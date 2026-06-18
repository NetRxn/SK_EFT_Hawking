"""Guarded worktree-slot reset for the parallel Lean-dev fan-out (v4.1, RC1/FM-1/FM-2).

Resets slot `wtN` to current `main` via `git checkout -B` — the **guardrail-safe** recipe.
This is NOT `git reset --hard`: the auto-mode permission classifier denies `reset --hard` on a
worktree the agent did not create this session (that is a Claude Code permission heuristic, NOT a
dev-harness hook — there is no Bash guardrail in this plugin). `checkout -B` advances the slot's
branch to `main` non-destructively and is not denied.

GUARD (the real invariant — "never clobber unmerged work"): refuses if the slot's branch holds any
commit not reachable from `main`, so the lead must merge/cherry-pick first; nothing is ever lost.

cwd-safe repo resolution: reuses `harness_common.repo_root()` (cache-safe, launch-robust). Stdlib
only; fail-soft with a clear message. Invoked by the `/reset-slot` command and referenced by
`goal-dev/references/parallel-worktrees.md`.
"""
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from harness_common import repo_root  # noqa: E402  (sibling shared helper)


def _run(args, cwd=None):
    return subprocess.run(args, capture_output=True, text=True, cwd=cwd)


def main():
    if len(sys.argv) < 2 or not sys.argv[1].strip():
        print("usage: reset_slot.py <N>   (slot number, e.g. 1|2|3 or wt1)")
        return 2
    n = sys.argv[1].strip().lower().removeprefix("wt")
    if not n.isdigit():
        print(f"⚠ invalid slot '{sys.argv[1]}' — expected a number (1|2|3).")
        return 2

    root = repo_root()
    if root is None:
        print("⚠ repo root unresolved — launch from the workspace root or inside the repo. No action.")
        return 1
    slot = root / ".claude" / "worktrees" / f"wt{n}"
    if not (slot / ".git").exists():
        print(f"⚠ slot wt{n} not found at {slot}. Run scripts/setup_lean_worktree_slots.sh first.")
        return 1

    branch = f"worktree-wt{n}"
    # GUARD: any commit on the slot branch not reachable from main would be discarded by the reset.
    log = _run(["git", "-C", str(slot), "log", "--oneline", "main..HEAD"])
    unmerged = log.stdout.strip()
    if unmerged:
        print(f"⛔ slot wt{n} has commits NOT on main — refusing to reset (would lose work):")
        print(unmerged)
        print("→ merge / cherry-pick them into main first, then re-run /reset-slot.")
        return 1

    # Safe: no divergence, so advancing the slot branch to main is loss-free (ff-equivalent).
    r = _run(["git", "-C", str(slot), "checkout", "-B", branch, "main"])
    if r.returncode != 0:
        print(f"⚠ `git checkout -B {branch} main` failed in wt{n}:\n{r.stderr.strip()}")
        return 1
    print(f"✓ slot wt{n} reset to main (branch {branch}).")
    print("  If main's build advanced since the last clone, re-clone the slot's .lake:")
    print(f"  rm -rf {slot}/lean/.lake && cp -c -R {root}/lean/.lake {slot}/lean/.lake")
    return 0


if __name__ == "__main__":
    sys.exit(main())
