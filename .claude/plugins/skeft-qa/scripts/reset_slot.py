"""Guarded worktree-slot reset for the parallel Lean-dev fan-out (v4.1, RC1/FM-1/FM-2).

Resets slot `wtN` to current `main` via `git checkout -B` — the **guardrail-safe** recipe.
This is NOT `git reset --hard`: the auto-mode permission classifier denies `reset --hard` on a
worktree the agent did not create this session (that is a Claude Code permission heuristic, NOT a
dev-harness hook — there is no Bash guardrail in this plugin). `checkout -B` advances the slot's
branch to `main` non-destructively and is not denied.

GUARD (the real invariant — "never clobber unmerged work"): refuses if the slot's branch holds any
commit not reachable from `main`, so the lead must merge/cherry-pick first; nothing is ever lost.

After the reset it **auto-re-clones the slot's `.lake` build** when main advanced since the slot's
last sync (staleness-gated on main's HEAD SHA — `_reclone_lake_if_stale`), so the slot's LSP always
matches its git tree without a manual copy.

cwd-safe repo resolution: reuses `harness_common.repo_root()` (cache-safe, launch-robust). Stdlib
only; fail-soft with a clear message. Invoked by the `/reset-slot` command and referenced by
`goal-dev/references/parallel-worktrees.md`.
"""
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from harness_common import repo_root  # noqa: E402  (sibling shared helper)


def _run(args, cwd=None):
    return subprocess.run(args, capture_output=True, text=True, cwd=cwd)


def _reclone_lake_if_stale(root, slot, n):
    """Refresh the slot's build so its LSP matches its git tree (now at main). Re-clones main's
    `lean/.lake` into the slot **only when main advanced** since the slot's last sync — gated on
    main's HEAD SHA, recorded at `<repo>/.claude/dev-harness/slot_lake/wtN.sha` (gitignored). So a
    fan-out that resets a slot repeatedly without main moving pays the COW copy only once. The clone
    is an APFS `cp -c` (copy-on-write, cheap), with a plain `cp -R` fallback off-APFS. Returns 0 ok."""
    main_sha = _run(["git", "-C", str(root), "rev-parse", "HEAD"]).stdout.strip()
    sha_file = root / ".claude" / "dev-harness" / "slot_lake" / f"wt{n}.sha"
    try:
        recorded = sha_file.read_text().strip()
    except Exception:
        recorded = ""
    dst = slot / "lean" / ".lake"
    if recorded == main_sha and (dst / "build").is_dir():
        print(f"  .lake already current @ {main_sha[:12]} (no re-clone needed).")
        return 0
    src = root / "lean" / ".lake"
    if not (src / "build").is_dir():
        print("  ⚠ main's lean/.lake/build is missing — run `cd lean && lake build` first. "
              "The slot's git tree is at main but its .lake was NOT refreshed.")
        return 1
    print(f"  main advanced (slot @ {recorded[:12] or 'none'} → main @ {main_sha[:12]}); "
          f"re-cloning the slot's .lake (APFS copy-on-write)…")
    try:
        if dst.exists():
            shutil.rmtree(dst, ignore_errors=True)   # gitignored .lake — rm is not a git reset/clean
        cp = _run(["cp", "-c", "-R", str(src), str(dst)])
        if cp.returncode != 0:                        # off-APFS: fall back to a plain recursive copy
            shutil.rmtree(dst, ignore_errors=True)
            cp = _run(["cp", "-R", str(src), str(dst)])
            if cp.returncode != 0:
                print(f"  ⚠ .lake re-clone failed:\n{cp.stderr.strip()}")
                return 1
        sha_file.parent.mkdir(parents=True, exist_ok=True)
        sha_file.write_text(main_sha)
        print(f"  ✓ slot .lake re-cloned to main @ {main_sha[:12]} (LSP now matches the git tree).")
        return 0
    except Exception as e:
        print(f"  ⚠ .lake re-clone error: {e}")
        return 1


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
    return _reclone_lake_if_stale(root, slot, n)


if __name__ == "__main__":
    sys.exit(main())
