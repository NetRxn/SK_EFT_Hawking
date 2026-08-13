#!/usr/bin/env python3
"""Run the verification a change can actually fail — and nothing else.

WHY THIS EXISTS. The merge gate is two agreeing `pytest -m ''` runs plus
`validate.py --ci --no-memo` plus a clean `lake build`: about 45 minutes. That gate
certifies a MERGE CANDIDATE. It was being run after every fix round, including rounds
that touched only markdown, and across the last five findings of that stretch, none required it:
a crash caught by one unit test, a wrong test name caught by grep, a stale
`counts.tex` caught by `counts_fresh` in 30 seconds.

So: iterate under `--scope`, gate once under `--merge-gate`.

    uv run python scripts/verify_scope.py                 # scope from the working tree
    uv run python scripts/verify_scope.py --since HEAD~1  # scope from a commit range
    uv run python scripts/verify_scope.py --merge-gate    # the full gate, for the candidate

WHAT DECIDES SCOPE — this table is DERIVED FROM `_plan()`, not written beside it:

  lean/**                  -> counts_fresh, lake build SKEFTHawking.ExtractDeps,
                              lean_zero_sorry + axiom_closure_allowlist
  src/**, scripts/**       -> fast suite, architecture_inventory_fresh, counts_fresh,
                              module_census_fresh (those trees ARE its inputs)
  tests/**                 -> fast suite, counts_fresh
  rust/**                  -> NOTHING mechanical. No test under tests/ imports
                              `sk_eft_rhmc` (nine scripts/ drivers do), and a rust change
                              needs the CLAUDE.md rebuild first, so this tool cannot
                              observe it. NOT CERTIFIED carries the rebuild command.
  pyproject.toml, uv.lock  -> fast suite (the environment every step runs in)
  notebooks/**             -> counts_fresh, notebook_exec + viz_consistency
  docs/architecture/**     -> architecture_inventory_fresh
  docs/counts.*            -> counts_fresh
  papers/**                -> counts_fresh, the three deterministic bundle gates
  .claude/plugins/**       -> plugin guards AND architecture_inventory_fresh, because
                              the census derives agents/hooks/commands from that tree
  everything else (*.md)   -> nothing mechanical; say so rather than imply coverage

`counts_fresh` appears against six trees because `counts.json` publishes a figure
derived from each: pytest_cases and test_files from tests/, python_modules from src/,
notebooks/, papers/, and the whole Lean block. Verified against `update_counts.py`'s
producers, not from memory.

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
        # `notebooks/` is read by notebook_exec; pyproject/uv.lock change the
        # environment every other step runs in.
        #
        # ⚠️ `rust/` gets NO step, deliberately. An earlier version added a
        # `-k "rhmc or stencil or dirac"` slice on the claim that sk_eft_rhmc is
        # "imported by src/vestigial/hs_rhmc.py and exercised by seven test files".
        # Both were false: the name appears there only inside docstrings, and ZERO
        # files under tests/ import the extension — the slice ran 157 green tests
        # having loaded none of it. That turned an honest "nothing observes this"
        # into a FALSE GREEN, which is worse than the disclaimer it replaced. A
        # rust/ change needs the rebuild from CLAUDE.md and has no automated
        # coverage; `not_certified` says exactly that.
        "rust": any(p.startswith("rust/") for p in paths),
        "notebooks": any(p.startswith("notebooks/") for p in paths),
        "env": any(p in ("pyproject.toml", "uv.lock") for p in paths),
    }
    # counts.json/tex are DERIVED FROM tests/ and lean/ — a change to either moves
    # \totaltests or a Lean count. Omitting counts_fresh here reproduced the exact
    # blocker of the commit before this tool: a stale committed counts.tex.
    counts_moved = any(touched[k] for k in
                       ("counts", "tests", "lean", "code", "notebooks", "papers"))
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
    if touched["code"]:
        steps.append(("module_census_fresh",
                      ["uv", "run", "python", "scripts/validate.py",
                       "--check", "module_census_fresh"]))
    if counts_moved:
        steps.append(("counts_fresh",
                      ["uv", "run", "python", "scripts/validate.py",
                       "--check", "counts_fresh", "--no-memo"]))
    if touched["env"]:
        steps.append(("fast suite (environment changed)",
                      ["uv", "run", "python", "-m", "pytest", "tests/", "-q"]))
    if touched["notebooks"]:
        steps.append(("notebook_exec / viz_consistency",
                      ["uv", "run", "python", "scripts/validate.py",
                       "--check", "notebook_exec", "--check", "viz_consistency"]))
    if touched["plugin"]:
        steps.append(("architecture_inventory_fresh (plugin feeds the census)",
                      ["uv", "run", "python", "scripts/validate.py",
                       "--check", "architecture_inventory_fresh"]))
    if touched["papers"]:
        steps.append(("bundle gates",
                      ["uv", "run", "python", "scripts/validate.py",
                       "--check", "bundle_prose_em_dash_free",
                       "--check", "bundle_reader_facing_voice",
                       "--check", "bundle_todo_free_before_green"]))
    if touched["lean"]:
        # NOT plain `lake build`: it leaves ExtractDeps.olean missing and breaks
        # graph_integrity + counts_fresh downstream (CLAUDE.md, Build & run).
        steps.append(("lake build + ExtractDeps",
                      ["lake", "build", "SKEFTHawking.ExtractDeps"]))
        steps.append(("Lean substrate checks",
                      ["uv", "run", "python", "scripts/validate.py",
                       "--check", "lean_zero_sorry",
                       "--check", "axiom_closure_allowlist", "--no-memo"]))

    not_certified = []
    if touched["rust"]:
        not_certified.append(
            "ANYTHING about the Rust extension — no test under tests/ imports "
            "sk_eft_rhmc, and this run did not rebuild it. Run "
            "`PYO3_USE_ABI3_FORWARD_COMPATIBILITY=1 uv pip install -e rust/ "
            "--force-reinstall --no-deps` and exercise it by hand")
    if not touched["lean"]:
        not_certified.append("the Lean build and axiom closure (no lean/ change)")
    if not any(lbl.startswith("fast suite") for lbl, _ in steps):
        not_certified.append("the Python suite (nothing here runs it)")
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
            # ⚠️ EXPECTED NON-ZERO. `readiness_submission_gate` is red BY DESIGN until
            # the bundles reach submission, so `--ci` exits 1 on a healthy branch. The
            # condition is "SUBSTRATE clean, and readiness_submission_gate the only
            # failure" — see the `expect` handling below. Treating the exit code alone
            # as the verdict made this gate report FAILED on a tree that met every
            # merge condition, which is a gate that cries wolf.
            ("validate --ci --no-memo",
             ["uv", "run", "python", "scripts/validate.py", "--ci", "--no-memo"],
             "✓ SUBSTRATE: clean"),
            # ⚠️ `--ci` SKIPS four checks by design (_config.CI_SKIP): counts_fresh,
            # tables_fresh, claim_clusters_fresh, notebook_exec. counts_fresh being
            # among them is precisely why a stale committed counts.tex survived five
            # commits. A gate that inherits that blind spot is not a gate, so run them
            # explicitly here — this is the difference between --ci and CERTIFIED.
            ("the four CI_SKIP checks --ci cannot run",
             ["uv", "run", "python", "scripts/validate.py",
              "--check", "counts_fresh", "--check", "tables_fresh",
              "--check", "claim_clusters_fresh", "--check", "notebook_exec",
              "--no-memo"]),
            ("lake build + ExtractDeps",
             ["lake", "build", "SKEFTHawking.ExtractDeps"]),
        ]
        not_certified = [
            "that regenerating checks left the WORKING TREE clean — counts_fresh and "
            "tables_fresh rewrite in place and then pass, so check `git status` yourself",
        ]
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
            # ⚠️ DO NOT return here without printing `not_certified`. This early exit
            # discarded it, so a rust-only change — the case the rust/ disclosure was
            # WRITTEN FOR — printed the generic line and dropped the rebuild command.
            print("\n  Nothing mechanical observes this change.")
            print("  NOT CERTIFIED: everything. This says only that no gate applies.")
            for n in not_certified:
                print(f"    - {n}")
            return 0
        print()

    if not args.merge_gate:
        # SCOPED MODE ONLY. The gate's two full runs are byte-identical BY DESIGN — that
        # is what "two agreeing runs" means — so de-duplicating there silently deleted
        # run B while the docstring and --help still promised two. A tool whose critical
        # failure is under-reporting must not quietly do less than it says.
        seen_argv = set()
        steps = [(l, a) for l, a in steps
                 if not (tuple(a) in seen_argv or seen_argv.add(tuple(a)))]

    failed = []
    for step in steps:
        label, argv = step[0], step[1]
        # A step may declare a SUBSTRING that means success regardless of exit code.
        # Only `--ci` uses it, and only because its red-by-design paper-corpus gate
        # makes the exit code a false signal on a healthy branch.
        expect = step[2] if len(step) > 2 else None
        cwd = REPO / "lean" if argv[0] == "lake" else REPO
        print(f"  ── {label}")
        r = subprocess.run(argv, cwd=cwd, capture_output=True, text=True)
        out = r.stdout + r.stderr
        lines = [l for l in out.splitlines() if l.strip()]
        if expect:
            ok = expect in out
            shown = next((l for l in lines if expect in l), lines[-1] if lines else "")
            print(f"     {shown.strip()[:150]}")
        else:
            ok = r.returncode == 0
            print(f"     {lines[-1][:150] if lines else '(no output)'}")
        if not ok:
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
