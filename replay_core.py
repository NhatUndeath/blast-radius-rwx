"""Per-query replay of sqlglot's TPC-H / TPC-DS executor tests (tests/test_executor.py).

`test_execute_tpch` / `test_execute_tpcds` run each fixture query through sqlglot's Python executor
(parse in the parent, pickle to a worker, execute, pickle back) and compare with DuckDB's answer for
`transpile(sql, write="duckdb")`. Every query is independent, so a change that only touches the code
paths of a few queries can be checked by re-running just those queries with the patched sources and
comparing with the pristine results recorded at build time (tools/build_replay.py).

Used in two places:
  * build time: `python replay_core.py record <kind> <i> <src>` (one fresh process per query, so lazy
    caches are rebuilt by every query) prints coverage + result hashes as JSON;
  * run time: the selector runs `python replay_core.py check <src>` with the patched sources served by
    an import hook; it prints "@@R same" or "@@R diff <why>".
"""
from __future__ import annotations

import ast
import csv
import gzip
import hashlib
import json
import os
import pickle
import sys

KINDS = {
    "tpch": ("optimizer/tpc-h/", "optimizer/tpc-h/tpc-h.sql", "TPCH_SCHEMA"),
    "tpcds": ("optimizer/tpc-ds/", "optimizer/tpc-ds/tpc-ds.sql", "TPCDS_SCHEMA"),
}


def _open(path):
    with open(path, "rb") as f:
        gz = f.read(2) == b"\x1f\x8b"
    return gzip.open(path, "rt", newline="") if gz else open(path, encoding="utf-8", newline="")


def load_table(src, kind, table, columns):
    from sqlglot.executor.table import Table

    path = os.path.join(src, "tests", "fixtures", KINDS[kind][0], f"{table}.csv.gz")
    reader = csv.reader(_open(path), delimiter="|")
    rows, ctypes = [], []
    next(reader)
    for row in reader:
        if not ctypes:
            for v in row:
                try:
                    ctypes.append(type(ast.literal_eval(v)))
                except (ValueError, SyntaxError):
                    ctypes.append(str)
        rows.append(tuple(None if (t is not str and v == "") else t(v) for t, v in zip(ctypes, row)))
    return Table(columns=columns, rows=rows)


def queries(src, kind):
    sys.path.insert(0, src)
    from tests.helpers import load_sql_fixture_pairs

    return list(load_sql_fixture_pairs(KINDS[kind][1]))


def schema(kind):
    import tests.helpers as h

    return getattr(h, KINDS[kind][2])


def _h(obj) -> str:
    return hashlib.sha256(repr(obj).encode()).hexdigest()[:24]


class _StopAfterPlan(Exception):
    pass


# phase switch for recording: "query" (parse, optimize, plan), "fp" (our fingerprint), "exec"
PHASE = ["query"]


def plan_fingerprint(plan) -> str:
    """Everything the Python executor consumes from a plan: every step's attributes, with
    expressions serialized by sqlglot's serde (types included) and steps referenced by id."""
    from sqlglot import exp, serde
    from sqlglot.planner import Step

    labels = {}

    def key(st):
        return (type(st).__name__, str(st.name), repr([str(p) for p in getattr(st, "projections", [])]))

    def visit(st):
        if id(st) in labels:
            return
        labels[id(st)] = f"{type(st).__name__}#{len(labels)}"
        for d in sorted(st.dependencies, key=key):
            visit(d)

    visit(plan.root)

    def enc(o):
        if isinstance(o, Step):
            return ("step", labels.get(id(o), "?"))
        if isinstance(o, exp.Expr):
            return ("expr", json.dumps(serde.dump(o), sort_keys=True, default=repr))
        if isinstance(o, dict):
            return ("dict", sorted((repr(enc(k)), repr(enc(v))) for k, v in o.items()))
        if isinstance(o, (list, tuple)):
            return (type(o).__name__, [enc(x) for x in o])
        if isinstance(o, (set, frozenset)):
            return ("set", sorted(repr(enc(x)) for x in o))
        if isinstance(o, (str, int, float, bool, type(None))):
            return o
        return ("obj", type(o).__name__)

    rows = []
    for st in sorted(plan.dag, key=lambda x: labels.get(id(x), "?")):
        attrs = {k: v for k, v in vars(st).items() if k not in ("dependents", "dependencies")}
        rows.append((labels.get(id(st), "?"), sorted((k, repr(enc(v))) for k, v in attrs.items()),
                     sorted(labels.get(id(d), "?") for d in st.dependencies)))
    rows.append(("expression", enc(plan.expression)))
    return _h(rows)


def run_query(src, kind, meta, sql, tables_cache, mode="full", timing=None):
    """What the test does for one query; returns comparable hashes (raises on errors).
    mode="plan" stops right before the Python executor runs the plan."""
    import time

    from sqlglot import find_tables, parse_one, transpile
    from sqlglot.executor import execute
    from sqlglot.executor.python import PythonExecutor

    expression = pickle.loads(pickle.dumps(parse_one(sql)))
    duck = transpile(sql, write="duckdb")[0]
    out = {"duckdb_sql": _h(duck), "duckdb_text": duck}
    if meta.get("execute"):
        sch = schema(kind)
        tables = {}
        for t in find_tables(expression):
            name = t.name
            if name not in tables_cache:
                tables_cache[name] = load_table(src, kind, name, sch[name])
            tables[name] = tables_cache[name]
        orig = PythonExecutor.execute

        def hooked(self, plan):
            if timing is not None:
                timing["plan_done"] = time.process_time()
            PHASE[0] = "fp"
            try:
                out["plan"] = plan_fingerprint(plan)
            finally:
                PHASE[0] = "exec"
            if mode == "plan":
                raise _StopAfterPlan
            return orig(self, plan)

        PythonExecutor.execute = hooked
        try:
            result = execute(expression, schema=sch, tables=tables)
            PHASE[0] = "query"
            result = pickle.loads(pickle.dumps(result))
            out["result"] = _h((list(result.columns), list(result.rows)))
        except _StopAfterPlan:
            pass
        finally:
            PythonExecutor.execute = orig
            PHASE[0] = "query"
    return out


# --------------------------------------------------------------------------- build-time recording
def _record(kind, i, src):
    import time

    mon = sys.monitoring
    tool = mon.COVERAGE_ID
    root = os.path.abspath(os.path.join(src, "sqlglot")) + os.sep
    lines: dict[str, set[int]] = {}
    exec_lines: dict[str, set[int]] = {}
    phase = ["setup"]
    setup_lines: dict[str, set[int]] = {}

    def on_line(code, line):
        f = code.co_filename
        if not os.path.abspath(f).startswith(root):
            return mon.DISABLE
        if phase[0] == "query" and PHASE[0] == "fp":
            return None  # our fingerprint code is not part of the test; keep the event enabled
        rel = os.path.relpath(os.path.abspath(f), src).replace(os.sep, "/")
        if phase[0] == "setup":
            target = setup_lines
        elif PHASE[0] == "exec":
            target = exec_lines
        else:
            target = lines
        target.setdefault(rel, set()).add(line)
        return mon.DISABLE

    mon.use_tool_id(tool, "replay")
    mon.register_callback(tool, mon.events.LINE, on_line)
    # one-line functions (lambdas) emit no LINE event when called: record their first line
    mon.register_callback(tool, mon.events.PY_START, lambda code, off: on_line(code, code.co_firstlineno))
    mon.set_events(tool, mon.events.LINE | mon.events.PY_START)
    sys.path.insert(0, src)
    qs = queries(src, kind)
    meta, sql, _ = qs[i]
    # tables used by this query are loaded first, as the test's setUpClass does
    from sqlglot import find_tables, parse_one

    sch = schema(kind)
    cache = {}
    if meta.get("execute"):
        for t in find_tables(parse_one(sql)):
            cache[t.name] = load_table(src, kind, t.name, sch[t.name])
    mon.restart_events()
    phase[0] = "query"
    t0 = time.process_time()
    timing = {}
    out = run_query(src, kind, meta, sql, cache, timing=timing)
    out["seconds"] = round(time.process_time() - t0, 3)
    out["plan_seconds"] = round(timing.get("plan_done", time.process_time()) - t0, 3)
    mon.set_events(tool, 0)
    out["lines"] = {f: sorted(v) for f, v in lines.items()}
    out["exec_lines"] = {f: sorted(v) for f, v in exec_lines.items()}
    out["setup_lines"] = {f: sorted(v) for f, v in setup_lines.items()}
    out["execute"] = bool(meta.get("execute"))
    out["tables"] = sorted(cache)
    print(json.dumps(out))


def _genmem(spec):
    """tests/test_generator.py::test_generator_memory, restricted to the dialects whose dialect or
    generator classes come from a patched module (all others are unchanged)."""
    import gc
    import tracemalloc

    from sqlglot.dialects.dialect import Dialect, Dialects

    patched = set(spec["modules"])
    affected = []
    candidates = spec.get("names")
    names = list(Dialects) if candidates is None else list(candidates)
    for name in names:
        try:
            cls = type(Dialect.get_or_raise(name))
            mods = {c.__module__ for k in (cls, cls.generator_class, cls.tokenizer_class, cls.parser_class)
                    for c in k.__mro__}
        except BaseException as e:  # noqa: BLE001
            return f"diff genmem {name}: {type(e).__name__}"
        if mods & patched:
            affected.append(name)
    if len(affected) > spec.get("max", 6):
        return f"costly genmem {len(affected)} dialects"
    for name in affected:
        try:
            dialect = Dialect.get_or_raise(name)
            for _ in range(100):
                dialect.generator()
            gc.collect()
            tracemalloc.start()
            try:
                before = tracemalloc.get_traced_memory()[0]
                for _ in range(1000):
                    dialect.generator()
                gc.collect()
                after = tracemalloc.get_traced_memory()[0]
            finally:
                tracemalloc.stop()
        except BaseException as e:  # noqa: BLE001
            return f"diff genmem {name}: {type(e).__name__}"
        if after - before >= 1024:
            return f"diff genmem {name}: memory"
    return "same"


# --------------------------------------------------------------------------- run-time check
_DUCK = {}


def duckdb_same(src, kind, old_sql, new_sql):
    """The test compares with DuckDB's answer to transpile(sql, write="duckdb"); a different SQL
    text is harmless if DuckDB returns the same columns and rows for it."""
    try:
        import duckdb
    except Exception:
        return False
    conn = _DUCK.get(kind)
    if conn is None:
        conn = duckdb.connect()
        directory = os.path.join(src, "tests", "fixtures", KINDS[kind][0])
        for table, columns in schema(kind).items():
            file_name = os.path.join(directory, f"{table}.csv.gz").replace(os.sep, "/")
            conn.execute(
                f"""
                CREATE VIEW {table} AS
                SELECT *
                FROM READ_CSV('{file_name}', delim='|', header=True, columns={columns})
                """
            )
        _DUCK[kind] = conn

    def run(q):
        cur = conn.execute(q)
        return [d[0] for d in cur.description], cur.fetchall()

    try:
        return run(old_sql) == run(new_sql)
    except Exception:
        return False


def _check(src):
    req = json.loads(sys.stdin.read())
    real_out = sys.stdout
    sys.stdout = open(os.devnull, "w")

    def say(msg):
        real_out.write("@@R " + msg + chr(10))

    try:
        if req.get("genmem"):
            verdict = _genmem(req["genmem"])
            if verdict != "same":
                say(verdict)
                return
        cache = {}
        for kind, items in req.get("queries", {}).items():
            qs = queries(src, kind)
            for item in items:
                i, expected = item[0], item[1]
                mode = item[2] if len(item) > 2 else "full"
                meta, sql, _ = qs[i]
                try:
                    got = run_query(src, kind, meta, sql, cache, mode=mode)
                except BaseException as e:  # noqa: BLE001
                    say(f"diff {kind} {i}: {type(e).__name__}")
                    return
                keys = ("duckdb_sql", "plan") if mode == "plan" else ("duckdb_sql", "plan", "result")
                for k in keys:
                    if expected.get(k) != got.get(k):
                        if k == "duckdb_sql" and expected.get("duckdb_text") and                                 duckdb_same(src, kind, expected["duckdb_text"], got["duckdb_text"]):
                            continue
                        say(f"diff {kind} {i}: {k}")
                        return
        say("same")
    finally:
        real_out.flush()


if __name__ == "__main__":
    if sys.argv[1] == "record":
        _record(sys.argv[2], int(sys.argv[3]), sys.argv[4])
    elif sys.argv[1] == "check":
        _check(sys.argv[2])
