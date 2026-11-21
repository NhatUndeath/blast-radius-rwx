"""Blast Radius selector.

For each /data/commits/<id>.patch print one JSON line {"commit": id, "workers": [[...], ...]}.

All maps are built from the pinned sqlglot commit only (allowed by the rules):
  cov_map.json.gz     per-test line coverage (tools/cov_plugin.py + tools/build_covmap.py)
  struct_map.json     classes (+bases) and intra-repo imports per file (tools/build_struct.py)
  fixture_map.json    fixture file -> tests that read it (tools/build_maps.py)
and the pinned source itself (SQLGLOT_SRC, default /opt/sqlglot) to parse the changed files.

Per changed file:
  tests/fixtures/**          -> tests that read the fixture
  *.py under sqlglot/ tests/ -> the patched file must compile (else: all tests / the test file);
      a line inside a function body -> tests that executed that statement
      a def/decorator line          -> tests that executed any line of that function
      a class-body line             -> tests that executed any line of that class or its subclasses
      a module-level line           -> tests that executed any line of the module or of modules importing it
      class/module-level edits are also import-checked on a patched copy in /tmp (fail -> all tests)
  docs / text files          -> nothing
  anything else / any doubt  -> all tests
Then the selection is split over 1..8 workers (LPT) keeping the cheapest worker count.
Any error falls back to running every test.
"""

from __future__ import annotations

import ast
import gzip
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
MAX_WORKERS = 8
WORKER_COST_MS = 2000
SRC = Path(os.environ.get("SQLGLOT_SRC", "/opt/sqlglot"))
DOC_SUFFIXES = (".md", ".rst", ".txt", ".png", ".svg", ".html", ".css")
CACHE_DECORATORS = ("cache", "lru_cache", "cached_property", "cachedmethod", "memoize")


def log(msg: str) -> None:
    print(msg, file=sys.stderr)


class RunAll(Exception):
    pass


def duration_ms(seconds: float) -> int:
    return int((float(seconds) * 1000) + 0.5)


# --------------------------------------------------------------------------- scheduling
def lpt(items, k):
    loads = [0] * k
    workers = [[] for _ in range(k)]
    for number, ms in items:
        i = loads.index(min(loads))
        workers[i].append(number)
        loads[i] += ms
    workers = [w for w in workers if w]
    if not workers:
        return 0, []
    return max(loads) + WORKER_COST_MS * len(workers), workers


def schedule(selected, dur):
    if not selected:
        return []
    items = sorted(((n, dur[n]) for n in selected), key=lambda x: (-x[1], x[0]))
    best_cost, best = None, None
    for k in range(1, min(MAX_WORKERS, len(items)) + 1):
        cost, workers = lpt(items, k)
        if best_cost is None or cost < best_cost:
            best_cost, best = cost, workers
    return best or []


# --------------------------------------------------------------------------- patch parsing
HUNK = re.compile(r"^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@")


class FilePatch:
    def __init__(self):
        self.old = None
        self.new = None
        self.hunks = []  # (old_start, old_len, [(tag, text)])
        self.binary = False
        self.moved = False
        self.deleted = False
        self.created = False

    @property
    def path(self):
        for p in (self.new, self.old):
            if p and p != "/dev/null":
                return p
        return None


def _strip_prefix(p: str) -> str:
    p = p.split("\t")[0].strip()
    if p.startswith('"') and p.endswith('"'):
        p = p[1:-1]
    if p.startswith(("a/", "b/")):
        p = p[2:]
    return p


def parse_patch(text: str) -> list[FilePatch]:
    files: list[FilePatch] = []
    cur = None
    lines = text.split("\n")
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("diff --git "):
            cur = FilePatch()
            files.append(cur)
            m = re.match(r"diff --git a/(\S+) b/(\S+)", line)
            if m:
                cur.old, cur.new = m.group(1), m.group(2)
            i += 1
            continue
        if line.startswith("--- ") and i + 1 < len(lines) and lines[i + 1].startswith("+++ "):
            if cur is None or cur.hunks:
                cur = FilePatch()
                files.append(cur)
            o, n = line[4:], lines[i + 1][4:]
            cur.old = "/dev/null" if o.strip() == "/dev/null" else _strip_prefix(o)
            cur.new = "/dev/null" if n.strip() == "/dev/null" else _strip_prefix(n)
            i += 2
            continue
        if cur is not None and line.startswith(("rename from ", "copy from ", "rename to ", "copy to ",
                                                "deleted file mode", "new file mode")):
            if line.startswith(("rename", "copy")):
                cur.moved = True
            elif line.startswith("deleted"):
                cur.deleted = True
            else:
                cur.created = True
            i += 1
            continue
        if line.startswith("Binary files") or line.startswith("GIT binary patch"):
            if cur is not None:
                cur.binary = True
            i += 1
            continue
        m = HUNK.match(line)
        if m and cur is not None:
            old_start = int(m.group(1))
            old_len = int(m.group(2)) if m.group(2) is not None else 1
            new_len = int(m.group(4)) if m.group(4) is not None else 1
            body = []
            i += 1
            o_left, n_left = old_len, new_len
            while i < len(lines) and (o_left > 0 or n_left > 0):
                l = lines[i]
                if l.startswith("\\"):
                    i += 1
                    continue
                tag = l[:1] if l else " "
                if tag == "-":
                    o_left -= 1
                elif tag == "+":
                    n_left -= 1
                elif tag == " ":
                    o_left -= 1
                    n_left -= 1
                else:
                    raise RunAll(f"bad hunk line {l[:20]!r}")
                body.append((tag, l[1:]))
                i += 1
            while i < len(lines) and lines[i].startswith("\\"):
                i += 1
            cur.hunks.append((old_start, old_len, body))
            continue
        i += 1
    return files


def changed_positions(fp: FilePatch):
    """removed: old line numbers removed/modified; inserts: old line numbers after which lines are added."""
    removed, inserts = set(), set()
    for old_start, _old_len, body in fp.hunks:
        ln = old_start if old_start > 0 else 0
        # old_start is the first old line of the hunk (or the line before, when old_len == 0)
        if _old_len == 0:
            ln = old_start + 1
        for tag, _ in body:
            if tag == " ":
                ln += 1
            elif tag == "-":
                removed.add(ln)
                ln += 1
            elif tag == "+":
                inserts.add(ln - 1)  # added after old line ln-1
    return removed, inserts


def apply_patch(old_text: str, fp: FilePatch) -> str:
    old = old_text.split("\n")
    out = []
    pos = 0  # 0-based index into old
    for old_start, old_len, body in fp.hunks:
        start = old_start - 1 if old_len > 0 else old_start
        if start < pos:
            raise RunAll("overlapping hunks")
        out.extend(old[pos:start])
        pos = start
        for tag, text in body:
            if tag in (" ", "-"):
                if pos >= len(old) or old[pos].rstrip("\r") != text.rstrip("\r"):
                    raise RunAll("patch does not apply")
                if tag == " ":
                    out.append(old[pos])
                pos += 1
            else:
                out.append(text)
    out.extend(old[pos:])
    return "\n".join(out)


# --------------------------------------------------------------------------- maps
class Maps:
    def __init__(self, tests):
        self.tests = tests
        self.by_id = {t["id"]: t["number"] for t in tests}
        self.all = {t["number"] for t in tests}
        self.by_file = {}
        for t in tests:
            self.by_file.setdefault(t["file"], set()).add(t["number"])
        cov = json.loads(gzip.decompress((HERE / "cov_map.json.gz").read_bytes()))
        # translate map test index -> tests.json number by id
        idx_to_num = [self.by_id.get(tid) for tid in cov["tests"]]
        self.unmapped_tests = {n for n in self.all if n not in set(idx_to_num)}
        self.sets = [frozenset(idx_to_num[i] for i in s if idx_to_num[i] is not None) for s in cov["sets"]]
        self.cov = {f: ({int(k): v for k, v in d["lines"].items()}, set(d["collect"]))
                    for f, d in cov["files"].items()}
        self.class_users = {k: {idx_to_num[i] for i in v if idx_to_num[i] is not None}
                            for k, v in cov.get("class_users", {}).items()}
        self.class_used_at_collect = cov.get("classes_used_at_collect", {})
        self.imp = {f: (d.get("import_mods", []), {int(k): v for k, v in d.get("import_lines", {}).items()})
                    for f, d in cov["files"].items() if d.get("import_lines")}
        # fixture -> tests that opened it while running (audit hook); read at collection -> unknown
        self.opened = {fx: {idx_to_num[i] for i in v if idx_to_num[i] is not None}
                       for fx, v in cov.get("fixtures_opened", {}).items()}
        self.opened_at_collect = set(cov.get("fixtures_opened_at_collect", ()))
        struct = json.loads((HERE / "struct_map.json").read_text("utf-8"))
        self.struct = struct["files"]
        self.struct_opaque = struct.get("opaque_tests", [])
        self.importers = {}
        for f, d in self.struct.items():
            for imp in d["imports"]:
                self.importers.setdefault(imp, set()).add(f)
        try:
            self.fixtures = json.loads((HERE / "fixture_map.json").read_text("utf-8"))["fixtures"]
        except Exception:
            self.fixtures = {}

    def lines_tests(self, f, lines):
        m = self.cov.get(f)
        out = set()
        if not m:
            return out
        lm = m[0]
        for ln in lines:
            si = lm.get(ln)
            if si is not None:
                out |= self.sets[si]
        return out

    def range_tests(self, f, start, end):
        m = self.cov.get(f)
        out = set()
        if not m:
            return out
        for ln, si in m[0].items():
            if start <= ln <= end:
                out |= self.sets[si]
        return out

    def file_tests(self, f):
        m = self.cov.get(f)
        out = set()
        if m:
            for si in set(m[0].values()):
                out |= self.sets[si]
        return out

    def family_tests(self, f):
        """Tests that use the module `f`: lines run in f, or in modules f imports that are private to
        it (imported by at most 3 modules), e.g. dialects/tsql.py -> parsers/tsql.py, generators/tsql.py."""
        out = self.file_tests(f)
        for imp in self.struct.get(f, {}).get("imports", ()):
            if imp.startswith("sqlglot/") and len(self.importers.get(imp, ())) <= 3:
                out |= self.file_tests(imp)
        return out

    def class_tests(self, f, qual):
        key = f"{f}::{qual}"
        out = set(self.class_users.get(key, ()))
        for m in self.class_used_at_collect.get(key, ()):
            out |= self.file_tests(m) if m else set()
        return out

    def import_mods(self, f, lines):
        d = self.imp.get(f)
        out = set()
        if d:
            mods, by_line = d
            for ln in lines:
                for i in by_line.get(ln, ()):
                    out.add(mods[i])
        return out

    def collected(self, f, lines):
        m = self.cov.get(f)
        return bool(m) and any(ln in m[1] for ln in lines)

    def subclass_ranges(self, qual):
        """(file, start, end) of all classes that (transitively) derive from the class `qual`
        (qualified name, e.g. "Snowflake" or "Snowflake.Tokenizer"), matched by name."""
        out = []
        seen = set()
        frontier = [qual]
        done = set()
        while frontier:
            q = frontier.pop()
            if q in done:
                continue
            done.add(q)
            nested = "." in q
            last = q.rsplit(".", 1)[-1]
            for ff, d in self.struct.items():
                for c in d["classes"]:
                    if nested:
                        hit = any(b == q or b.endswith("." + q) for b in c.get("bases_dotted", ()))
                    else:
                        hit = last in c["bases"]
                    if hit and (ff, c["start"]) not in seen:
                        seen.add((ff, c["start"]))
                        out.append((ff, c["start"], c["end"]))
                        frontier.append(c.get("qual", c["name"]))
        return out


# --------------------------------------------------------------------------- AST helpers
def scope_chain(tree, line):
    """Innermost-last list of (node, kind) of def/class nodes containing `line` (decorators included)."""
    chain = []

    def visit(node):
        for child in ast.iter_child_nodes(node):
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                start = min([child.lineno] + [d.lineno for d in child.decorator_list])
                if start <= line <= child.end_lineno:
                    chain.append(child)
                    visit(child)
                    return
            elif hasattr(child, "lineno") and child.lineno <= line <= (child.end_lineno or child.lineno):
                visit(child)
                return

    visit(tree)
    return chain


def innermost_stmt(fn, line):
    best = None
    for node in ast.walk(fn):
        if node is fn or not isinstance(node, ast.stmt):
            continue
        if node.lineno <= line <= (node.end_lineno or node.lineno):
            if best is None or (node.end_lineno - node.lineno) <= (best.end_lineno - best.lineno):
                best = node
    return best


def header_lines(stmt):
    body = getattr(stmt, "body", None)
    if isinstance(body, list) and body and isinstance(stmt, (ast.If, ast.For, ast.AsyncFor, ast.While,
                                                             ast.With, ast.AsyncWith, ast.Try)):
        end = max(stmt.lineno, body[0].lineno - 1)
        return range(stmt.lineno, end + 1)
    return range(stmt.lineno, (stmt.end_lineno or stmt.lineno) + 1)


def body_start(fn):
    return fn.body[0].lineno if fn.body else fn.end_lineno


def is_cached(fn):
    for d in fn.decorator_list:
        s = ast.unparse(d) if hasattr(ast, "unparse") else ""
        if any(c in s for c in CACHE_DECORATORS):
            return True
    return False


def same_code(a, b):
    """Code objects equal apart from line numbers / positions (comments, blank lines)."""
    if a.co_code != b.co_code or a.co_names != b.co_names or a.co_varnames != b.co_varnames:
        return False
    if a.co_freevars != b.co_freevars or a.co_cellvars != b.co_cellvars or a.co_flags != b.co_flags:
        return False
    if a.co_argcount != b.co_argcount or a.co_kwonlyargcount != b.co_kwonlyargcount or a.co_name != b.co_name:
        return False
    if a.co_exceptiontable != b.co_exceptiontable if hasattr(a, "co_exceptiontable") else False:
        return False
    if len(a.co_consts) != len(b.co_consts):
        return False
    for x, y in zip(a.co_consts, b.co_consts):
        if hasattr(x, "co_code") or hasattr(y, "co_code"):
            if not (hasattr(x, "co_code") and hasattr(y, "co_code") and same_code(x, y)):
                return False
        elif type(x) is not type(y) or x != y:
            if not (x != x and y != y):  # NaN constants
                return False
    return True


# --------------------------------------------------------------------------- per-file analysis
def module_name(rel):
    mod = rel[:-3].replace("/", ".")
    return mod[: -len(".__init__")] if mod.endswith(".__init__") else mod


def analyze_py(rel, fp, maps, import_checks):
    src_path = SRC / rel
    is_test_file = rel.startswith("tests/")
    if fp.old == "/dev/null" or fp.created:
        if src_path.exists():
            raise RunAll("new file shadows an existing one")
        # new file: nothing imports it at the pinned commit unless something enumerates the package
        if rel.split("/")[-1] in ("conftest.py", "__init__.py", "sitecustomize.py"):
            raise RunAll("new special python file")
        if rel.startswith("sqlglot/"):
            import_checks["__need__"] = True  # also adds the tests that enumerate / import packages
            added = [t for h in fp.hunks for tag, t in h[2] if tag == "+"]
            import_checks.setdefault("__patched__", {})[rel] = chr(10).join(added)
        return set()
    if not src_path.exists():
        raise RunAll(f"source missing for {rel}")
    old_text = src_path.read_text("utf-8")
    if fp.new == "/dev/null":
        raise RunAll("deleted python file")
    new_text = apply_patch(old_text, fp)
    try:
        new_code = compile(new_text, rel, "exec", dont_inherit=True)
    except (SyntaxError, ValueError):
        if is_test_file and maps.by_file.get(rel):
            return set(maps.by_file[rel])
        raise RunAll(f"syntax error in {rel}")
    tree = ast.parse(old_text)
    if same_code(compile(old_text, rel, "exec", dont_inherit=True), new_code) or             ast.dump(tree) == ast.dump(ast.parse(new_text)):
        return set()  # only comments / blank lines / formatting changed: same program
    removed, inserts = changed_positions(fp)
    nlines = old_text.count("\n") + 1
    selected = set()
    need_import_check = False

    def module_level():
        out = maps.family_tests(rel)
        for c in maps.struct.get(rel, {}).get("classes", ()):
            out |= maps.class_tests(rel, c.get("qual", c["name"]))
        for imp in maps.importers.get(rel, ()):
            out |= maps.family_tests(imp)
        if is_test_file:
            out |= maps.by_file.get(rel, set())
        return out

    def class_level(cls, chain):
        out = maps.range_tests(rel, min([cls.lineno] + [d.lineno for d in cls.decorator_list]), cls.end_lineno)
        out |= maps.family_tests(rel) if rel.startswith("sqlglot/") else set()
        classes = [n for n in chain if isinstance(n, ast.ClassDef)]
        quals = []
        prefix = ""
        for n in chain:
            if isinstance(n, ast.ClassDef):
                quals.append(prefix + n.name)
                prefix += n.name + "."
            else:
                prefix += n.name + ".<locals>."
        for q in quals:
            out |= maps.class_tests(rel, q)  # tests that instantiated it or a subclass (MRO)
            for ff, s, e in maps.subclass_ranges(q):
                out |= maps.range_tests(ff, s, e)
                if ff.startswith("sqlglot/"):
                    out |= maps.family_tests(ff)
        if is_test_file:
            pre = f"{rel}::{cls.name}::"
            out |= {maps.by_id[t] for t in maps.by_id if t.startswith(pre)}
        return out

    def handle_line(line, inserted):
        nonlocal need_import_check
        chain = scope_chain(tree, line) if 1 <= line <= nlines else []
        fns = [n for n in chain if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))]
        if not chain:
            need_import_check = True
            return module_level()
        node = chain[-1]
        if isinstance(node, ast.ClassDef):
            need_import_check = True
            return class_level(node, chain)
        fn = node
        out = set()
        if any(is_cached(f) for f in fns):
            need_import_check = True
            return module_level()
        if line < body_start(fn) or (inserted and line == fn.end_lineno and line == body_start(fn)):
            # decorator / signature / def line: anything using the function
            need_import_check = True
            out |= maps.range_tests(rel, body_start(fn), fn.end_lineno)
            idx = max((i for i, n in enumerate(chain[:-1]) if isinstance(n, ast.ClassDef)), default=None)
            if idx is not None:
                out |= class_level(chain[idx], chain[: idx + 1])  # renamed / new method changes dispatch
            if is_test_file:
                out |= _tests_in_fn(rel, chain, maps)
            return out
        stmt = innermost_stmt(fn, line)
        lines = list(header_lines(stmt)) if stmt is not None else [line]
        out = maps.lines_tests(rel, lines)
        if not out and stmt is not None:
            out = maps.lines_tests(rel, range(stmt.lineno, stmt.end_lineno + 1))
        if stmt is not None:
            # results computed while some module was being imported (e.g. SQL templates parsed at
            # import) are reused by every test of that module without re-running these lines
            mods = maps.import_mods(rel, range(stmt.lineno, stmt.end_lineno + 1))
            for m in mods:
                if m != rel:
                    out |= maps.file_tests(m)
            if mods:
                need_import_check = True  # the change runs during those imports: they may now fail
                import_checks.setdefault("__also__", set()).update(mods)
        if not out and maps.collected(rel, range(fn.lineno, fn.end_lineno + 1)):
            # runs at import / collection time only: static
            need_import_check = True
            out = module_level()
        if is_test_file:
            out |= _tests_in_fn(rel, chain, maps)
        return out

    for line in sorted(removed):
        selected |= handle_line(line, False)
    for after in sorted(inserts):
        # an insertion after old line `after`: look at both neighbours
        prev_line, next_line = after, after + 1
        sel = set()
        if prev_line >= 1:
            sel |= handle_line(prev_line, True)
        if next_line <= nlines:
            sel |= handle_line(next_line, True)
        selected |= sel
    if rel.startswith("sqlglot/"):
        import_checks.setdefault("__patched__", {})[rel] = new_text
        if need_import_check:
            import_checks["__need__"] = True
    return selected


def _tests_in_fn(rel, chain, maps):
    names = [n.name for n in chain]
    out = set()
    for i in range(len(names), 0, -1):
        tid = rel + "::" + "::".join(names[:i])
        if tid in maps.by_id:
            out.add(maps.by_id[tid])
            break
    return out


_CHILD = r"""
import importlib, importlib.abc, importlib.util, io, json, os, sys
src = sys.argv[1]
req = json.loads(sys.stdin.read())
patched = {name: (path, text) for name, path, text in req["patched"]}


class _Patched(importlib.abc.MetaPathFinder, importlib.abc.Loader):
    def find_spec(self, name, path=None, target=None):
        if name not in patched:
            return None
        p = patched[name][0]
        pkg = p.endswith("__init__.py")
        return importlib.util.spec_from_file_location(
            name, p, loader=self, submodule_search_locations=[os.path.dirname(p)] if pkg else None)

    def create_module(self, spec):
        return None

    def exec_module(self, module):
        p, text = patched[module.__name__]
        exec(compile(text, p, "exec"), module.__dict__)


sys.meta_path.insert(0, _Patched())
sys.path.insert(0, src)
real_out = sys.stdout
sys.stdout = io.StringIO()
failed = []
try:
    import sqlglot
    import pkgutil
    names = sorted(m.name for m in pkgutil.walk_packages(sqlglot.__path__, "sqlglot.")
                   if not m.name.endswith("__main__"))
except BaseException as e:
    failed = ["sqlglot"]
    names = []
for m in names:
    try:
        importlib.import_module(m)
    except BaseException as e:
        failed.append(m)
real_out.write("@@R " + json.dumps(failed) + chr(10))
real_out.flush()
"""


_PRISTINE_FAILS: list = []
_DEADLINE = [float("inf")]


def _run_import_child(patched: dict):
    req = {"patched": [[module_name(rel), (SRC / rel).as_posix(), text] for rel, text in patched.items()]}
    env = {k: v for k, v in os.environ.items() if not k.startswith("PYTHON")}
    try:
        r = subprocess.run([sys.executable, "-I", "-S", "-B", "-c", _CHILD, str(SRC)], input=json.dumps(req),
                           capture_output=True, text=True, encoding="utf-8", env=env,
                           timeout=max(5.0, min(20.0, _DEADLINE[0] - time.monotonic())))
    except subprocess.TimeoutExpired:
        return None
    for line in reversed((r.stdout or "").splitlines()):
        if line.startswith("@@R "):
            return set(json.loads(line[4:]))
    return None


def import_check(patched: dict, also: set = frozenset()) -> bool:
    """True if `import sqlglot` and every sqlglot module still import with the patch applied
    (fresh interpreter; patched sources served by an import hook). Modules that fail to import
    unpatched too (optional dependencies) are ignored."""
    fails = _run_import_child(patched)
    if fails is None:
        log("[selector] import check: no result (timeout / crash)")
        return False
    if fails:
        if not _PRISTINE_FAILS:
            _PRISTINE_FAILS.append(_run_import_child({}) or set())
        fails -= _PRISTINE_FAILS[0]
    log(f"[selector] import check: {sorted(fails)[:5] or 'ok'}")
    return not fails


def select(patch_text, maps):
    files = parse_patch(patch_text)
    if not files:
        raise RunAll("no files in patch")
    selected = set()
    import_checks = {}
    for fp in files:
        rel = fp.path
        if rel is None or fp.binary:
            raise RunAll("binary or unnamed file")
        if fp.moved or fp.deleted:
            raise RunAll("renamed / copied / deleted file")
        if rel.startswith("tests/fixtures/"):
            if rel in maps.opened and rel not in maps.opened_at_collect:
                selected |= maps.opened[rel]  # exact readers
                continue
            ids = maps.fixtures.get(rel)  # static (AST) map: broader
            if not ids:
                raise RunAll(f"unmapped fixture {rel}")
            for tid in ids:
                if tid not in maps.by_id:
                    raise RunAll("fixture map / tests.json mismatch")
                selected.add(maps.by_id[tid])
        elif rel.endswith(".py") and (rel.startswith("sqlglot/") or rel.startswith("tests/")):
            selected |= analyze_py(rel, fp, maps, import_checks)
        elif rel.endswith(DOC_SUFFIXES) or rel.startswith(("docs/", "posts/", "benchmarks/", "pdoc/")):
            continue
        else:
            raise RunAll(f"unhandled file {rel}")
    if import_checks.get("__need__"):
        # tests that run sqlglot out of process (e.g. `python -c "import sqlglot"`) see import-time changes
        for entry in maps.struct_opaque:
            if entry in maps.by_id:
                selected.add(maps.by_id[entry])
            else:
                selected |= maps.by_file.get(entry, set())
    if import_checks.get("__need__") and not import_check(import_checks["__patched__"],
                                                         import_checks.get("__also__", set())):
        raise RunAll("patched modules fail to import")
    if selected:
        # tests the coverage map knows nothing about (e.g. could not run when the map was built)
        selected |= {n for n in maps.unmapped_tests if n in maps.all}
    return selected


# --------------------------------------------------------------------------- main
def parse_args(argv):
    opts = {"data": Path(os.environ.get("BLAST_DATA", "/data")), "tests": None, "patches": []}
    i = 0
    while i < len(argv):
        a = argv[i]
        if a in ("--data", "--tests") and i + 1 < len(argv):
            opts[a[2:]] = Path(argv[i + 1])
            i += 2
        elif a == "--patch" and i + 1 < len(argv):
            opts["patches"].append(Path(argv[i + 1]))
            i += 2
        else:
            i += 1
    return opts


def main() -> None:
    opts = parse_args(sys.argv[1:])
    tests_path = opts["tests"] or opts["data"] / "tests.json"
    tests = json.loads(Path(tests_path).read_text("utf-8"))["tests"]
    dur = {t["number"]: duration_ms(t["seconds"]) for t in tests}
    all_numbers = set(dur)
    patches = opts["patches"] or sorted((opts["data"] / "commits").glob("*.patch"))
    try:
        if not (SRC / "sqlglot" / "__init__.py").is_file():
            raise RuntimeError(f"pinned sqlglot sources not found at {SRC}")
        maps = Maps(tests)
    except Exception as e:
        log(f"[selector] maps unavailable, running everything: {e!r}")
        maps = None
    out = []
    # the batch limit is 3 min (4.5 in the final); leave a wide margin for the run-all fallbacks
    deadline = time.monotonic() + float(os.environ.get("SELECTOR_BUDGET_SEC", "140"))
    _DEADLINE[0] = deadline
    for p in patches:
        commit = p.name[: -len(".patch")] if p.name.endswith(".patch") else p.stem
        try:
            if maps is None:
                raise RunAll("no maps")
            if time.monotonic() > deadline:
                raise RunAll("time budget used up")
            text = p.read_bytes().decode("utf-8", errors="replace").replace("\r\n", "\n")
            selected = select(text, maps)
            selected &= all_numbers
            workers = schedule(selected, dur)
            why = f"{len(selected)} tests"
        except Exception as e:
            why = f"run all ({e!r:.120})"
            try:
                workers = schedule(all_numbers, dur)
            except Exception:
                workers = [sorted(all_numbers)]
        sys.stdout.write(json.dumps({"commit": commit, "workers": workers}, separators=(",", ":")) + chr(10))
        sys.stdout.flush()
        log(f"[selector] {commit}: {why}, {len(workers)} workers")



if __name__ == "__main__":
    main()
