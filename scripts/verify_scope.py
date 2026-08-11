#!/usr/bin/env python3
"""Run the verification a change can actually fail — and nothing else.

WHY THIS EXISTS. The merge gate is two agreeing `pytest -m ''` runs plus
`validate.py --ci --no-memo` plus a clean `lake build`: about 45 minutes. That gate
certifies a MERGE CANDIDATE. It was being run after every fix round, including rounds
that touched only markdown, and across eleven rounds not one finding required it:
a crash caught by one unit test, a wrong test name caught by grep, a stale
`counts.tex` caught by `counts_fresh` in 30 seconds.

So: iterate under `--scope`, gate once under `--merge-gate`.

    uv run python scripts/verify_scope.py                 # scope from the working tree
    uv run python scripts/verify_scope.py --since HEAD~1  # scope from a commit range
    uv run python scripts/verify_scope.py --merge-gate    # the full gate, for the candidate

WHAT DECIDES SCOPE. Only what a change can be OBSERVED by:

  lean/**                  -> lake build, ExtractDeps, the Lean-side checks
  src/**, scripts/**       -> the fast suite + the checks owning the touched modules
  tests/**                 -> the touched test files
  docs/architecture/**     -> architecture_inventory_fresh
  docs/counts.*            -> counts_fresh
  papers/**                -> the bundle gates
  .claude/plugins/**       -> the plugin surface guards
  everything else (*.md)   -> nothing mechanical; say so rather than imply coverage

⚠️ A NARROWER RUN IS A NARROWER CLAIM. This prints exactly what it ran and what it
therefore does NOT certify. Quoting a scoped run as if it were the merge gate is the
same defect class this repository keeps finding in its own prose.
"""
from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent


def _changed(since: str | None) -> list[str]:
    if since:
        cmd = ["git", "diff", "--name-only", f"{since}..HEAD"]
    else:
        cmd = ["git", "status", "--porcelain"]
    out = subprocess.run(cmd, cwd=REPO, capture_output=True, text=True).stdout
    if since:
        return [l.strip() for l in out.splitlines() if l.strip()]
    return [l[3:].strip() for l in out.splitlines() if l.strip()]


def _plan(paths: list[str]) -> tuple[list[tuple[str, list[str]]], list[str]]:
    """(steps, not_certified) — steps are (label, argv)."""
    touched = {
        "lean": any(p.startswith("lean/") for p in paths),
        "code": any(p.startswith(("src/", "scripts/")) for p in paths),
        "tests": any(p.startswith("tests/") for p in paths),
        "arch": any(p.startswith("docs/architecture/") for p in paths),
        "counts": any(p.startswith("docs/counts.") for p in paths),
        "papers": any(p.startswith("papers/") for p in paths),
        "plugin": any(p.startswith(".claude/plugins/") for p in paths),
    }
    steps: list[tuple[str, list[str]]] = []
    if touched["code"] or touched["tests"]:
        steps.append(("fast suite (tests/, default markers)",
                      ["uv", "run", "python", "-m", "pytest", "tests/", "-q"]))
    if touched["plugin"]:
        steps.append(("plugin surface guards",
                      ["uv", "run", "python", "-m", "pytest",
                       ".claude/plugins/skeft-qa/tests", "-q"]))
    if touched["arch"] or touched["code"]:
        steps.append(("architecture_inventory_fresh",
                      ["uv", "run", "python", "scripts/validate.py",
                       "--check", "architecture_inventory_fresh"]))
    if touched["counts"] or touched["code"]:
        steps.append(("counts_fresh",
                      ["uv", "run", "python", "scripts/validate.py",
                       "--check", "counts_fresh", "--no-memo"]))
    if touched["papers"]:
        steps.append(("bundle gates",
                      ["uv", "run", "python", "scripts/validate.py",
                       "--check", "bundle_prose_em_dash_free",
                       "--check", "bundle_reader_facing_voice",
                       "--check", "bundle_todo_free_before_green"]))
    if touched["lean"]:
        steps.append(("lake build", ["lake", "build"]))
        steps.append(("Lean substrate checks",
                      ["uv", "run", "python", "scripts/validate.py",
                       "--check", "lean_zero_sorry",
                       "--check", "axiom_closure_allowlist", "--no-memo"]))

    not_certified = []
    if not touched["lean"]:
        not_certified.append("the Lean build and axiom closure (no lean/ change)")
    if not (touched["code"] or touched["tests"]):
        not_certified.append("the Python suite (no src/, scripts/ or tests/ change)")
    not_certified.append("the FULL `-m ''` suite and `--ci` floor — run --merge-gate for those")
    return steps, not_certified


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--since", help="scope from <commit>..HEAD instead of the working tree")
    ap.add_argument("--merge-gate", action="store_true",
                    help="the full gate: two agreeing -m '' runs, --ci --no-memo, lake build")
    args = ap.parse_args()

    if args.merge_gate:
        steps = [
            ("full suite, run A", ["uv", "run", "python", "-m", "pytest", "-m", "", "-q"]),
            ("full suite, run B", ["uv", "run", "python", "-m", "pytest", "-m", "", "-q"]),
            ("validate --ci --no-memo",
             ["uv", "run", "python", "scripts/validate.py", "--ci", "--no-memo"]),
            ("lake build", ["lake", "build"]),
        ]
        not_certified: list[str] = []
        print("MERGE GATE — the full certification.\n")
    else:
        paths = _changed(args.since)
        if not paths:
            print("no changes detected; nothing to verify.")
            return 0
        steps, not_certified = _plan(paths)
        print(f"SCOPED VERIFICATION — {len(paths)} path(s) changed.")
        for p in paths[:12]:
            print(f"    {p}")
        if len(paths) > 12:
            print(f"    … and {len(paths) - 12} more")
        if not steps:
            print("\n  Nothing mechanical observes this change.")
            print("  NOT CERTIFIED: everything. This says only that no gate applies.")
            return 0
        print()

    failed = []
    for label, argv in steps:
        cwd = REPO / "lean" if argv[0] == "lake" else REPO
        print(f"  ── {label}")
        r = subprocess.run(argv, cwd=cwd, capture_output=True, text=True)
        tail = [l for l in (r.stdout + r.stderr).splitlines() if l.strip()][-1:]
        print(f"     {tail[0][:150] if tail else '(no output)'}")
        if r.returncode != 0:
            failed.append(label)

    print()
    if failed:
        print(f"FAILED: {', '.join(failed)}")
    else:
        print("all scoped steps passed.")
    if not_certified:
        print("\n⚠️  NOT CERTIFIED by this run:")
        for n in not_certified:
            print(f"    - {n}")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
