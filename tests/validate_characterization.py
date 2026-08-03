#!/usr/bin/env python3
"""ADR-009 Phase 0 — characterization harness for `scripts/validate.py`.

WHAT THIS IS
------------
A **before/after** net for the ADR-009 migration. Capture a baseline immediately
before a phase, run the phase, capture again, diff. Any difference is either an
intended change you can name, or refactor damage.

    uv run python tests/validate_characterization.py --record /tmp/before.json
    ... perform ADR-009 Phase 1 ...
    uv run python tests/validate_characterization.py --record /tmp/after.json
    uv run python tests/validate_characterization.py --compare /tmp/before.json /tmp/after.json

WHY IT IS NOT A COMMITTED GOLDEN
--------------------------------
A checked-in snapshot of `passed` values would be stale within days. The repo is
mid-remediation, `validate.py` is deliberately RED on `main` (the 2026-08-03
`stage13_status` guard fires on 14 of 21 bundles), and the operator expects more
gates to go red as remediation lands. A permanent fixture would become a
maintenance tax that gets updated reflexively — which is how a test stops
asserting anything. This is a characterization harness in the refactoring sense:
a temporary net, taken minutes apart, over an otherwise-unchanged tree.

The *permanent* structural guarantees live in the two committed guards:
`tests/test_validate_registry_contract.py` (count + order) and
`tests/test_validate_flag_propagation.py` (runtime flags reach their checks).

EXECUTION MODEL
---------------
Checks run **in-process, sequentially, in registration order** — the same way
`run_checks` executes them. Two reasons, one of which had to be corrected:

* It is affordable. Per-check subprocesses would re-pay import and graph-build
  cost ~50 times; `build_graph_json()` alone runs 4× per suite at ~15 s. This is
  the load-bearing reason.
* It is faithful *to process-level state generally* — module globals, `sys.path`,
  the runtime flags in `validation._config` — so a defect that only manifests
  when checks share an interpreter is visible here.

⚠️ An earlier version of this paragraph justified the model by claiming the three
module-global caches (`_LEAN_NAME_INDEX_CACHE`, `_LEAN_SOURCE_CACHE`,
`_PHYSLIB_SOURCE_CACHE`) "are shared across checks in a real run". **Measured
2026-08-03: they are not.** All three are populated and consumed inside the call
tree of a single check — `prose_theorem_reference_coverage`, via
`_load_lean_name_index()` and `_resolve_prose_ref()` — and no other check reaches
them. The design is unchanged because the cost argument alone carries it; the
reason was wrong and is corrected rather than quietly dropped. Asserting a
property of the data without measuring it is the defect class this whole harness
exists to catch, so it does not get to sit uncorrected in the harness's own
rationale.

The contamination hazard that motivated "one subprocess per check" is confined
to the three checks that regenerate on-disk artifacts a later check reads — and
all three are quarantined below, so it cannot arise.

QUARANTINE
----------
Nine checks are structurally non-snapshottable: they shell out, execute
notebooks, or rewrite tracked artifacts, so run N+1 legitimately differs from
run N. Forcing them into a snapshot would produce a harness that cries wolf,
which is worse than one with a stated gap.

KNOWN INTERACTION: `graph_integrity` MOVES WHEN YOU EDIT `tests/`
------------------------------------------------------------------
`build_graph.extract_python_test_nodes()` mints one graph node per `def test_*`
in `tests/test_*.py`, plus VERIFIES edges from the names each test references.
So **adding a test changes `graph_integrity`'s `graph_size` and `orphan_nodes`
details** — and a refactor of this suite edits tests in nearly every commit.
Expect this comparison to report `graph_integrity` diffs that are not refactor
damage.

`graph_integrity` is deliberately NOT quarantined for it. It is one of the few
checks that would actually notice a mechanical refactor breaking artifact
resolution, and scrubbing the counts would discard that. Attribute instead —
the arithmetic closes exactly, every time it has been done:

    nodes   += one per new `def test_*`
    edges   += one per (test, resolvable-name) pair, deduped
    orphans += one per new test with no resolvable name,
               plus one per existing test that LOST its last edge

Worked example (2026-08-03, the `_registry` extraction): +5 nodes / +3 edges /
+2 orphans = 5 new tests in one new file contributing 4 edges, minus 1 edge from
retargeting `v.STRICT_MODE` to `cfg.STRICT_MODE` in an existing test.

⚠️ When attributing, diff against the tree the BASELINE was taken from, not
against `HEAD` — they diverge as soon as you commit mid-phase, and using HEAD
silently under-counts (it did, once, and briefly looked like unexplained drift).

Most of these edges are spurious anyway: the resolver matches a test's
`referenced_names` against Lean short names with no alias guard, so `v` (from
`import validate as v`) resolves to a Lean structure field. See ADR-009
§Deferred item 7 — filed, not fixed, because it changes what a gate measures.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys
import time
from pathlib import Path

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))


#: Checks excluded from capture, with the reason each is non-deterministic.
QUARANTINE: dict[str, str] = {
    "lean_build":                      "shells out to `lake build`; emits job counts and timings",
    "notebook_exec":                   "executes ~91 notebooks and mutates .notebook_exec_cache.json",
    "notebook_stored_outputs_current": "re-executes bundle notebooks; wall-clock bound",
    "paper_latex_compiles":            "shells out to pdflatex over 21 drafts (and skips by default)",
    "counts_fresh":                    "REGENERATES docs/counts.json — later checks read it",
    "tables_fresh":                    "REGENERATES papers/*/tables/*.tex",
    "claim_clusters_fresh":            "REGENERATES papers/claim_clusters.json",
    "tracked_hypotheses_fresh":        "compares against a renderer whose output tracks the registry",
    "bundle_figure_integrity":         "renders figures via kaleido; byte-compare is renderer-version sensitive",
    # Not non-deterministic, but it MUTATES tracked files: `check()` writes
    # `freshness_stale` into every papers/*/bundle_metadata.json. A capture must not
    # dirty the tree it is characterizing, and a later check reads that metadata.
    "bundle_source_freshness":         "WRITES freshness_stale into tracked bundle_metadata.json",
}

#: Substrings whose *values* legitimately vary run to run. Replaced by a stable
#: token so a snapshot compares structure and verdicts, not wall-clock noise.
_SCRUBBERS: tuple[tuple[re.Pattern, str], ...] = (
    (re.compile(re.escape(str(SK_ROOT))), "<REPO>"),
    (re.compile(r"\b\d{4}-\d{2}-\d{2}T[\d:+\-]+"), "<TS>"),
    (re.compile(r"\b\d{4}-\d{2}-\d{2}\b"), "<DATE>"),
    (re.compile(r"\b\d+(\.\d+)?\s*s\b"), "<DUR>"),
    (re.compile(r"\(\d+ jobs?\)"), "(<JOBS> jobs)"),
    (re.compile(r"\b[0-9a-f]{40}\b"), "<SHA40>"),
    (re.compile(r"\b[0-9a-f]{16}\b"), "<SHA16>"),
)


def _scrub(text: str | None) -> str:
    out = text or ""
    for rx, repl in _SCRUBBERS:
        out = rx.sub(repl, out)
    return out


def capture(only: list[str] | None = None, verbose: bool = True) -> dict:
    """Run every non-quarantined check and return a normalized result tree."""
    os.environ.setdefault("PYTHONHASHSEED", "0")
    import validate as v

    payload: dict = {"checks": {}, "quarantined": sorted(QUARANTINE)}
    for spec in v._CHECKS:
        if spec.name in QUARANTINE:
            continue
        if only and spec.name not in only:
            continue
        t0 = time.monotonic()
        try:
            r = spec.func()
            entry = {
                "passed": bool(r.passed),
                "error": _scrub(r.error),
                # Sorted so that an unsorted glob or set-iteration order cannot
                # register as a behavioural change. Detail ORDER is not part of
                # the contract; detail CONTENT is.
                "details": sorted(
                    [
                        {
                            "name": _scrub(d.name),
                            "passed": bool(d.passed),
                            "warning": bool(d.warning),
                            "message": _scrub(d.message),
                        }
                        for d in r.details
                    ],
                    key=lambda d: (d["name"], d["message"]),
                ),
            }
        except Exception as exc:  # a raising check is itself characterizable
            entry = {"passed": None, "error": f"{type(exc).__name__}: {_scrub(str(exc))}",
                     "details": []}
        payload["checks"][spec.name] = entry
        if verbose:
            dt = time.monotonic() - t0
            print(f"  {spec.name:38} {'ok' if entry['passed'] else 'FAIL':4}  {dt:7.2f}s",
                  file=sys.stderr, flush=True)
    return payload


class EmptyComparison(RuntimeError):
    """Raised when a comparison has nothing to compare.

    ⚠️ This exists because the first version of this harness DID NOT raise it, and
    reported `CHARACTERIZATION HELD — 0 checks identical` for two empty snapshots.
    That is absence-of-measurement rendered as success — the exact defect class
    this whole engagement exists to remove — reproduced inside the tool built to
    detect it. An empty comparison is UNVERIFIED, never "held".
    """


def compare(before: dict, after: dict) -> list[str]:
    """Return a list of human-readable differences. Empty == characterization held.

    Raises `EmptyComparison` if either snapshot is empty or they cover disjoint
    check sets — a silent pass there would be indistinguishable from agreement.
    """
    b, a = before["checks"], after["checks"]
    if not b or not a:
        raise EmptyComparison(
            f"nothing to compare: before={len(b)} check(s), after={len(a)} check(s). "
            "An empty snapshot is an UNVERIFIED result, not a passing one. "
            "(zsh note: `--only $VAR` does not word-split — use `--only ${=VAR}` "
            "or list the names literally.)")
    if not (set(b) & set(a)):
        raise EmptyComparison(
            f"snapshots cover disjoint check sets ({len(b)} vs {len(a)}, no overlap); "
            "there is no common ground to compare.")

    diffs: list[str] = []

    for name in sorted(set(b) - set(a)):
        diffs.append(f"{name}: DISAPPEARED from the registry")
    for name in sorted(set(a) - set(b)):
        diffs.append(f"{name}: APPEARED in the registry")

    for name in sorted(set(b) & set(a)):
        bb, aa = b[name], a[name]
        if bb["passed"] != aa["passed"]:
            diffs.append(f"{name}: verdict {bb['passed']} -> {aa['passed']}")
        if bb["error"] != aa["error"]:
            diffs.append(f"{name}: error {bb['error']!r} -> {aa['error']!r}")
        bd = {(d["name"], d["message"]): d for d in bb["details"]}
        ad = {(d["name"], d["message"]): d for d in aa["details"]}
        for k in sorted(set(bd) - set(ad)):
            diffs.append(f"{name}: detail LOST  {k[0]} | {k[1][:110]}")
        for k in sorted(set(ad) - set(bd)):
            diffs.append(f"{name}: detail NEW   {k[0]} | {k[1][:110]}")
        for k in sorted(set(bd) & set(ad)):
            if bd[k]["passed"] != ad[k]["passed"] or bd[k]["warning"] != ad[k]["warning"]:
                diffs.append(
                    f"{name}: detail FLAGS {k[0]} "
                    f"passed {bd[k]['passed']}->{ad[k]['passed']} "
                    f"warning {bd[k]['warning']}->{ad[k]['warning']}")
    return diffs


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--record", metavar="OUT.json", help="capture a snapshot")
    p.add_argument("--compare", nargs=2, metavar=("BEFORE.json", "AFTER.json"))
    p.add_argument("--only", nargs="*", help="restrict to these check names")
    a = p.parse_args(argv)

    if a.record:
        snap = capture(only=a.only)
        n = len(snap["checks"])
        if n == 0:
            # Refuse to write an empty snapshot. A zero-check capture that lands on
            # disk will later be compared against another one and report "held".
            print("ERROR: captured 0 checks — refusing to write an empty snapshot.\n"
                  "  If you passed --only, no name matched the registry.\n"
                  "  zsh does NOT word-split unquoted parameters: use `--only ${=VAR}`\n"
                  "  or list the check names literally.", file=sys.stderr)
            return 2
        Path(a.record).write_text(json.dumps(snap, indent=2, sort_keys=True))
        print(f"\nrecorded {n} check(s) -> {a.record} "
              f"({len(snap['quarantined'])} quarantined)", file=sys.stderr)
        return 0

    if a.compare:
        before = json.loads(Path(a.compare[0]).read_text())
        after = json.loads(Path(a.compare[1]).read_text())
        try:
            diffs = compare(before, after)
        except EmptyComparison as exc:
            print(f"CHARACTERIZATION UNVERIFIED — {exc}")
            return 2
        if not diffs:
            print(f"CHARACTERIZATION HELD — {len(after['checks'])} checks identical")
            return 0
        print(f"CHARACTERIZATION BROKEN — {len(diffs)} difference(s):\n")
        for d in diffs:
            print(f"  {d}")
        return 1

    p.print_help()
    return 2


if __name__ == "__main__":
    sys.exit(main())
