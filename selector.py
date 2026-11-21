"""Blast Radius selector.

For each /data/commits/<id>.patch print one JSON line {"commit": id, "workers": [[...], ...]}.

Rules (general, no per-patch answers):
  1. Find the files the patch changes.
  2. If every changed file is a test fixture we have a map for (built from the pinned sqlglot commit
     by tools/build_maps.py: fixture -> tests that read it), select only those tests.
  3. Otherwise run every test.
  4. Split the selection over 1..8 workers (longest test first onto the lightest worker) and keep the
     worker count with the lowest cost (largest load + 2 s per worker).
Any error falls back to running every test, so a commit is never left without a valid line.

Local use: python selector.py [--data DIR] [--tests tests.json] [--patch file.patch ...]
"""

from __future__ import annotations

import json
import os
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
MAX_WORKERS = 8
WORKER_COST_MS = 2000


def log(msg: str) -> None:
    print(msg, file=sys.stderr)


def duration_ms(seconds: float) -> int:
    return int((float(seconds) * 1000) + 0.5)


# --------------------------------------------------------------------------- scheduling
def lpt(items: list[tuple[int, int]], k: int) -> tuple[int, list[list[int]]]:
    """items: (number, ms) sorted by ms desc. Returns (cost, workers)."""
    loads = [0] * k
    workers: list[list[int]] = [[] for _ in range(k)]
    for number, ms in items:
        i = loads.index(min(loads))
        workers[i].append(number)
        loads[i] += ms
    workers = [w for w in workers if w]
    if not workers:
        return 0, []
    return max(loads) + WORKER_COST_MS * len(workers), workers


def schedule(selected: set[int], dur: dict[int, int]) -> list[list[int]]:
    if not selected:
        return []
    items = sorted(((n, dur[n]) for n in selected), key=lambda x: (-x[1], x[0]))
    best_cost, best = None, None
    for k in range(1, min(MAX_WORKERS, len(items)) + 1):
        cost, workers = lpt(items, k)
        if best_cost is None or cost < best_cost:
            best_cost, best = cost, workers
    return best or []


# --------------------------------------------------------------------------- patch analysis
DIFF_FILE = re.compile(r"^diff --git a/(\S+) b/(\S+)", re.M)
PLUS_FILE = re.compile(r"^\+\+\+ (?:b/)?(\S+)", re.M)
MINUS_FILE = re.compile(r"^--- (?:a/)?(\S+)", re.M)


def changed_files(patch: str) -> set[str]:
    files: set[str] = set()
    for a, b in DIFF_FILE.findall(patch):
        files.update((a, b))
    for f in PLUS_FILE.findall(patch) + MINUS_FILE.findall(patch):
        files.add(f)
    files.discard("/dev/null")
    return files


def load_map() -> dict:
    p = HERE / "fixture_map.json"
    try:
        return json.loads(p.read_text("utf-8"))
    except Exception as e:  # missing map => run everything
        log(f"[selector] no fixture map: {e!r}")
        return {}


def select(patch: str, tests: list[dict], fmap: dict) -> set[int]:
    all_numbers = {t["number"] for t in tests}
    files = changed_files(patch)
    if not files:
        return all_numbers
    by_id = {t["id"]: t["number"] for t in tests}
    fixtures = fmap.get("fixtures", {})
    chosen: set[int] = set()
    for f in files:
        ids = fixtures.get(f)
        if ids is None:          # not a mapped fixture: unknown blast radius
            return all_numbers
        for tid in ids:
            n = by_id.get(tid)
            if n is None:        # map and tests.json disagree: be safe
                return all_numbers
            chosen.add(n)
    if not chosen:
        return all_numbers
    return chosen


# --------------------------------------------------------------------------- main
def parse_args(argv: list[str]) -> dict:
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
    fmap = load_map()
    out = []
    for p in patches:
        commit = p.name[: -len(".patch")] if p.name.endswith(".patch") else p.stem
        try:
            text = p.read_bytes().decode("utf-8", errors="replace")
            selected = select(text, tests, fmap)
            workers = schedule(selected, dur)
        except Exception as e:
            log(f"[selector] {commit}: fallback ({e!r})")
            try:
                workers = schedule(all_numbers, dur)
            except Exception:
                workers = [sorted(all_numbers)]
        out.append(json.dumps({"commit": commit, "workers": workers}, separators=(",", ":")))
        log(f"[selector] {commit}: {sum(len(w) for w in workers)} tests on {len(workers)} workers")
    sys.stdout.write("".join(line + "\n" for line in out))
    sys.stdout.flush()


if __name__ == "__main__":
    main()
