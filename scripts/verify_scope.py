#!/usr/bin/env python3
"""Run the verification a change can actually fail — and nothing else.

WHY THIS EXISTS. The merge gate is a full `pytest -m ''` run plus
`validate.py --ci --no-memo` plus the four checks `--ci` skips plus a clean `lake build`,
plus a working-tree check: roughly 25-30 minutes since the duplicate full run was dropped
on 2026-08-13 (see the step list for why a repeat could not detect what it was for). That gate
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
                              module_census_fresh (those trees ARE its inputs — .py AND .sh)
  tests/**                 -> fast suite, counts_fresh
  rust/**                  -> NOTHING mechanical. No test under tests/ imports
                              `sk_eft_rhmc` (nine scripts/ drivers do), and a rust change
                              needs the CLAUDE.md rebuild first, so this tool cannot
                              observe it. NOT CERTIFIED carries the rebuild command.
  pyproject.toml, uv.lock  -> fast suite (the environment every step runs in)
  notebooks/**             -> counts_fresh, module_census_fresh (the census walks it
                              since D3), notebook_exec + viz_consistency
  docs/architecture/**     -> architecture_inventory_fresh
  docs/counts.*            -> counts_fresh
  papers/**                -> counts_fresh, the deterministic bundle gates,
                              review_verify_is_one_command + spelled_out_census_figures
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
        # ⚠️ The census walks notebooks/ since D3, so a notebook edit can make it stale.
        # `touched["code"]` keys on the src/ and scripts/ prefixes and does NOT cover
        # this — the same unwidened-probe gap D5 found in the sync Edge.
        steps.append(("module_census_fresh (the census walks notebooks/)",
                      ["uv", "run", "python", "scripts/validate.py",
                       "--check", "module_census_fresh"]))
        steps.append(("notebook_exec / viz_consistency",
                      ["uv", "run", "python", "scripts/validate.py",
                       "--check", "notebook_exec", "--check", "viz_consistency"]))
    if touched["plugin"]:
        steps.append(("architecture_inventory_fresh (plugin feeds the census)",
                      ["uv", "run", "python", "scripts/validate.py",
                       "--check", "architecture_inventory_fresh"]))
    if touched["papers"]:
        # ⚠️ `review_verify_is_one_command` belongs here because review DOCUMENTS live
        # under `papers/AutomatedReviews/`, so editing one is a `papers/**` change. A
        # broken `Verify:` line strands the finding it belongs to — `close_finding` runs
        # that line verbatim and refuses any other command — and the whole point of
        # catching it under `--scope` is that the author is still holding the document.
        steps.append(("bundle gates",
                      ["uv", "run", "python", "scripts/validate.py",
                       "--check", "bundle_prose_em_dash_free",
                       "--check", "bundle_reader_facing_voice",
                       "--check", "bundle_todo_free_before_green",
                       "--check", "review_verify_is_one_command",
                       # ⚠️ `seed_residue_absent` belongs here for the same reason and a
                       # sharper one: the fastest way to dirty `papers/AutomatedReviews/`
                       # is a killed production-seeded mutation, and the author holding a
                       # `papers/**` diff is exactly who can tell a seed from a finding.
                       # Under `--scope` this is the cheapest place the residue surfaces.
                       "--check", "seed_residue_absent",
                       "--check", "spelled_out_census_figures"]))
    if touched["lean"]:
        # NOT plain `lake build`: it leaves ExtractDeps.olean missing and breaks
        # graph_integrity + counts_fresh downstream (CLAUDE.md, Build & run).
        steps.append(("lake build + ExtractDeps",
                      ["lake", "build", "SKEFTHawking.ExtractDeps"]))
        steps.append(("Lean substrate checks",
                      ["uv", "run", "python", "scripts/validate.py",
                       "--check", "lean_zero_sorry",
                       "--check", "axiom_closure_allowlist",
                       # Statement-level, not proof-level. A Lean edit can rename a
                       # theorem into or out of the existential population, or weaken a
                       # statement to `∃ x, True` — neither of which the two checks
                       # above can see, since both judge PROOFS.
                       "--check", "vacuous_statement_audit",
                       "--check", "existential_witness_disclosure", "--no-memo"]))

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


def _tree_state() -> list[str]:
    """`git status --porcelain` lines — the working tree as the gate sees it.

    Compared before and after the gate's steps. Untracked files count: a check that
    WRITES a new artifact and then reports it fresh is the same defect as one that
    rewrites a tracked file.
    """
    r = subprocess.run(["git", "status", "--porcelain"], cwd=REPO,
                       capture_output=True, text=True)
    return [l for l in r.stdout.splitlines() if l.strip()]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--since", help="scope from <commit>..HEAD instead of the working tree")
    ap.add_argument("--merge-gate", action="store_true",
                    help="the full gate: two agreeing -m '' runs, --ci --no-memo, lake build")
    args = ap.parse_args()

    if args.merge_gate:
        steps = [
            # ⚠️ ONE full run, not two (2026-08-13). The gate ran this command TWICE,
            # byte-identical, for "two agreeing runs" — roughly half its ~45 minutes.
            #
            # A repeat cannot buy what a repeat is normally for. Order-dependence needs a
            # DIFFERENT order; no `pytest-randomly` / `pytest-random-order` is installed or
            # declared, so both runs collected the same tests in the same order and the
            # second could only re-observe the first. `c289ac8e`, which introduced this
            # file, carried the pair forward as inherited practice while optimizing how
            # OFTEN the gate runs; it never asked what the duplicate detected. No record
            # of the two runs ever disagreeing exists in docs/.
            #
            # The one real property two sequential runs could signal — a suite that
            # MUTATES the tree, live here because `counts_fresh` and `tables_fresh`
            # rewrite in place — is now measured directly by the working-tree check
            # below, in milliseconds instead of a quarter hour, and is asserted rather
            # than left to the reader (it used to sit in `not_certified` as "check
            # `git status` yourself").
            ("full suite", ["uv", "run", "python", "-m", "pytest", "-m", "", "-q"]),
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
        not_certified = []
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

    # De-duplicate identical commands. This used to be SCOPED-MODE-ONLY, carved out
    # because the gate's two byte-identical full runs were load-bearing "by design" and
    # de-duplicating silently deleted run B while the docstring still promised two. The
    # gate now declares ONE run, so the carve-out has nothing left to protect and the
    # rule applies uniformly. The lesson it encoded still holds and now lives at the
    # step list: a tool whose critical failure is under-reporting must never quietly do
    # less than it says — which is why removing run B came with the docstring, the
    # `not_certified` block and this guard in the same commit.
    seen_argv = set()
    steps = [s for s in steps
             if not (tuple(s[1]) in seen_argv or seen_argv.add(tuple(s[1])))]

    # ⚠️ Snapshot the working tree BEFORE any step. `counts_fresh` and `tables_fresh`
    # regenerate in place and then pass, so a gate that ignores this reports green on a
    # tree the run itself dirtied — the committed-stale-`counts.tex` shape.
    tree_before = _tree_state()

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

    # The property the duplicate full run was reaching for, measured directly.
    print("  ── working tree unchanged by this run")
    dirtied = sorted(set(_tree_state()) - set(tree_before))
    if dirtied:
        failed.append("working tree unchanged by this run")
        print(f"     {len(dirtied)} path(s) DIRTIED by the run itself: "
              f"{', '.join(p[3:] or p for p in dirtied[:6])}"
              f"{' …' if len(dirtied) > 6 else ''}")
        print("     A step rewrote a tracked file or left a new one behind, and then "
              "passed. Commit the regenerated artifact, or fix the step that writes "
              "on read.")
    else:
        print("     clean — no tracked file was rewritten by the run")

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
