#!/usr/bin/env python3
"""
Aristotle submission CLI (SAFE, partial-submission process — ADR-006).

Canonical Aristotle CLI. Thin wrapper over the engine in
src/core/aristotle_submit.py (SafeAristotleRunner). It implements the safe
process; the dangerous full-project process is archived + disabled at
scripts/archive/submit_to_aristotle.py. See
docs/adrs/ADR-006-aristotle-submission-rewrite.md.

Subcommands:
    sorries  [targets...]                 List current sorry gaps (Lean primitive).
    stage     <targets...>                Stage the minimal import-closure project.
    submit    <targets...> --yes-i-authorize   Stage + submit (ASYNC, no --wait).
    status                                List recorded submissions + status.
    retrieve  <job_id>                    Download + extract a completed run.
    graft     <retrieved_dir> <targets...> [--apply]
                                          Review (and with --apply: verify-then-graft).
    verify    <targets...>                Run the verification gauntlet only.

A "target" is a module (SKEFTHawking.Foo), a path, a *.lean name, or a bare leaf.

Examples:
    uv run python scripts/submit_to_aristotle.py sorries
    uv run python scripts/submit_to_aristotle.py stage SingularConnSquareCloseNC
    uv run python scripts/submit_to_aristotle.py submit SingularConnSquareCloseNC --yes-i-authorize
    uv run python scripts/submit_to_aristotle.py retrieve <job_id>
    uv run python scripts/submit_to_aristotle.py graft docs/aristotle_results/run_*/extracted SingularConnSquareCloseNC --apply
"""

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from src.core import aristotle_submit as A  # noqa: E402

DEFAULT_PROMPT = (
    "Fill in the remaining sorry(s) in the target file(s) of this Lean project. "
    "Use the helper lemmas already proved in the project and the PROVIDED SOLUTION "
    "hints in the theorem docstrings. Do not modify other files."
)


def cmd_sorries(args) -> None:
    targets = getattr(args, "targets", None)
    if targets:
        modules = A.transitive_import_closure(targets)
        scope = f"closure of {targets} ({len(modules)} modules)"
    else:
        modules = {r["module"] for r in A._load_lean_deps()}
        scope = f"all modules ({len(modules)})"
    sd = A.sorry_decls_in_modules(modules)
    stale = A.lean_deps_stale_for(modules)
    print(f"Sorry gaps (Lean primitive: sorryAx in kernel axiom closure) — {scope}:")
    if sd:
        for m, decls in sorted(sd.items()):
            print(f"  {m}: {decls}")
    else:
        print("  (none in the cached lean_deps.json view)")
    if stale:
        print(f"\n[!] {len(stale)} module(s) are NEWER than lean_deps.json — the cached view "
              f"may under-report.\n    Refresh: `cd lean && lake build SKEFTHawking.ExtractDeps`. "
              f"Stale e.g.: {stale[:5]}")


def cmd_stage(args) -> None:
    staged = A.stage_minimal_project(args.targets)
    print(f"Staged minimal project: {staged.root}")
    print(f"  targets : {staged.targets}")
    print(f"  closure : {len(staged.closure)} modules (hash {staged.closure_hash})")
    stale = A.lean_deps_stale_for(set(staged.closure))
    if stale:
        print(f"  note    : {len(stale)} closure module(s) newer than lean_deps.json")
    dup = A.find_duplicate_submission(staged.closure_hash)
    if dup:
        print(f"  [!] identical closure already submitted as job {dup['job_id']} "
              f"(status {dup['status']})")
    print("\nReview the staged project, then:")
    print(f"  submit {' '.join(args.targets)} --yes-i-authorize")


def cmd_submit(args) -> None:
    staged = A.stage_minimal_project(args.targets)
    if not args.yes_i_authorize:
        print("Refusing to submit: pass --yes-i-authorize (ADR-006 Stage-4 human-in-the-loop gate).")
        print(f"Staged at {staged.root}; closure {len(staged.closure)} modules (hash {staged.closure_hash}).")
        raise SystemExit(2)
    man = A.submit_async(staged, args.prompt, authorized=True, force=args.force)
    print(f"Submitted (ASYNC — did not wait). job_id = {man.job_id}")
    print(f"  manifest : {man.path()}")
    print(f"  closure  : {man.closure_modules} modules")
    print(f"\nAristotle runs server-side (~hours-day). Retrieve when ready:")
    print(f"  retrieve {man.job_id}")


def cmd_status(args) -> None:
    import json
    md = A.MANIFESTS_DIR
    rows = []
    if md.exists():
        for f in sorted(md.glob("*.json")):
            try:
                rows.append(json.loads(f.read_text()))
            except (json.JSONDecodeError, OSError):
                continue
    if not rows:
        print("No submissions recorded.")
        return
    print(f"{'job_id':38s} {'status':10s} targets")
    for m in rows:
        status = m.get("status") or "(legacy)"   # archived-process manifests have no status
        targets = m.get("targets") if m.get("targets") is not None else "(full-project, archived)"
        print(f"  {m.get('job_id',''):36s} {status:10s} {targets}")


def cmd_retrieve(args) -> None:
    out = A.retrieve(args.job_id)
    print(f"Retrieved + extracted to: {out}")
    print("Review, then graft:")
    print(f"  graft {out} <targets...> --apply")


def cmd_graft(args) -> None:
    root = Path(args.retrieved)
    plan = A.plan_graft(root, args.targets)
    print(f"Graft plan: target diffs={list(plan.diffs)} | "
          f"other_files_changed={plan.other_files_changed} | safe={plan.safe}")
    for m, d in plan.diffs.items():
        print(f"\n----- diff: {m} (ours -> aristotle) -----\n{d}")
    if not args.apply:
        print("\n(plan only — pass --apply to verify-then-graft with auto-revert on gauntlet failure)")
        return
    res = A.graft_and_verify(root, args.targets)
    if res.gauntlet:
        g = res.gauntlet
        print(f"\ngauntlet: build={g.build_ok} zero_sorry={g.zero_sorry} "
              f"kernel_pure={g.kernel_pure} validate={g.validate_ok} tests={g.tests_ok}")
        for d in g.details:
            print(f"    - {d}")
    print(f"\nResult: grafted={res.grafted} reverted={res.reverted}\n  {res.note}")
    if res.grafted:
        print("\nNEXT — register attribution (ADR-006 D4): add to ARISTOTLE_THEOREMS + bump the "
              "322 asserts (constants.py:1372, validate.py:1172), then update_counts.py / ATTRIBUTION.md.")


def cmd_verify(args) -> None:
    g = A.run_verification_gauntlet(args.targets)
    print(f"Verification gauntlet: passed={g.passed}")
    print(f"  build={g.build_ok} zero_sorry={g.zero_sorry} kernel_pure={g.kernel_pure} "
          f"validate={g.validate_ok} tests={g.tests_ok}")
    for d in g.details:
        print(f"    - {d}")


def main() -> None:
    p = argparse.ArgumentParser(
        description="Aristotle submission CLI (safe partial-submission process; ADR-006).")
    p.add_argument("--dry-run", action="store_true",
                   help="Alias for `sorries` with no targets (list current sorry gaps).")
    sub = p.add_subparsers(dest="cmd")

    s = sub.add_parser("sorries", help="List current sorry gaps (Lean primitive + staleness).")
    s.add_argument("targets", nargs="*")
    s.set_defaults(func=cmd_sorries)

    s = sub.add_parser("stage", help="Stage the minimal import-closure project for target(s).")
    s.add_argument("targets", nargs="+")
    s.set_defaults(func=cmd_stage)

    s = sub.add_parser("submit", help="Stage + submit (async). Requires --yes-i-authorize.")
    s.add_argument("targets", nargs="+")
    s.add_argument("--prompt", default=DEFAULT_PROMPT)
    s.add_argument("--yes-i-authorize", action="store_true",
                   help="Required: explicit Stage-4 authorization to submit.")
    s.add_argument("--force", action="store_true", help="Resubmit even if an identical closure is open.")
    s.set_defaults(func=cmd_submit)

    s = sub.add_parser("status", help="List recorded submissions + status.")
    s.set_defaults(func=cmd_status)

    s = sub.add_parser("retrieve", help="Download + extract a completed run.")
    s.add_argument("job_id")
    s.set_defaults(func=cmd_retrieve)

    s = sub.add_parser("graft", help="Review (and with --apply: verify-then-graft) a retrieved run.")
    s.add_argument("retrieved", help="Path to the extracted run directory.")
    s.add_argument("targets", nargs="+")
    s.add_argument("--apply", action="store_true",
                   help="Apply target-file graft + run the gauntlet (auto-reverts on failure).")
    s.set_defaults(func=cmd_graft)

    s = sub.add_parser("verify", help="Run the verification gauntlet for target(s).")
    s.add_argument("targets", nargs="+")
    s.set_defaults(func=cmd_verify)

    args = p.parse_args()
    if args.cmd is None:
        if args.dry_run:
            args.targets = []
            cmd_sorries(args)
        else:
            p.print_help()
        return
    args.func(args)


if __name__ == "__main__":
    main()
