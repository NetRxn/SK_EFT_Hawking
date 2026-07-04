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
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from harness_common import repo_root, harness_dir, marker_path  # noqa: E402  (sibling helpers)


def _run(args, cwd=None):
    return subprocess.run(args, capture_output=True, text=True, cwd=cwd)


def _base_ref(root):
    """The primary worktree's branch — the base slots are cut from — resolved instead of hardcoding
    `main` (adversarial review #1). Fallback `main`."""
    r = _run(["git", "-C", str(root), "symbolic-ref", "--short", "HEAD"])
    b = r.stdout.strip() if r.returncode == 0 else ""
    return b or "main"


def _slotnum(x):
    """Coerce a slot entry (1 | '1' | 'wt1') to int, else None."""
    try:
        s = str(x).strip().lower()
        return int(s[2:] if s.startswith("wt") else s)
    except Exception:
        return None


def _load_marker(p):
    try:
        return json.loads(p.read_text())
    except Exception:
        return None


def _other_owners(root, n, cur_sid, cur_goal):
    """Markers of a DIFFERENT goal that currently list slot `n` in their `slots`. The isolation
    guard: a slot may be owned by at most one goal, so a claim by this goal must surface (and, on a
    clean claim, transfer away) any other goal's ownership. Same-goal / same-session markers are not
    conflicts. Returns [(path, marker)]. Fail-open -> []."""
    owners = []
    try:
        for mf in (harness_dir(root) / "managed").glob("*.json"):
            if cur_sid and mf.name == f"{cur_sid}.json":
                continue
            m = _load_marker(mf)
            if not m:
                continue
            other = m.get("slots")
            if not isinstance(other, list):   # string mis-parse would iterate chars (isolation breach)
                continue
            # A conflict is: this slot owned by a DIFFERENT goal. When THIS session's goal_id is unknown
            # (out-of-session ops reset), we cannot prove same-goal -> treat any other owner as a
            # conflict (safe default; --force is the escape). Adversarial review #4/#6.
            if n in [_slotnum(s) for s in other] and (cur_goal is None or m.get("goal_id") != cur_goal):
                owners.append((mf, m))
    except Exception:
        pass
    return owners


def _stamp_ownership(root, n):
    """Add slot `n` to THIS session's marker `slots` (idempotent) and REMOVE it from every other
    marker (exclusive transfer) so the slot-aware re-anchor stays isolated to one goal. Best-effort:
    no current marker (reset run outside a goal) -> silently skip. Returns a status string for the
    caller to print, or ''."""
    sid = os.environ.get("CLAUDE_SESSION_ID", "").strip()
    if not sid:
        return ""
    mp = marker_path(root, sid)
    cur = _load_marker(mp)
    if cur is None:
        return ""  # this session is not a managed goal — reset still fine, nothing to stamp
    # exclusive transfer: drop n from any other marker that had it
    cur_goal = cur.get("goal_id")
    for mf, m in _other_owners(root, n, sid, cur_goal):
        m["slots"] = [s for s in (m.get("slots") or []) if _slotnum(s) != n]
        try:
            mf.write_text(json.dumps(m, indent=2))
        except Exception:
            pass
    cur_slots = cur.get("slots")
    cur_slots = cur_slots if isinstance(cur_slots, list) else []   # ignore a mis-typed string
    slots = [s for s in cur_slots if _slotnum(s) is not None]
    if n not in [_slotnum(s) for s in slots]:
        slots.append(n)
    cur["slots"] = sorted({_slotnum(s) for s in slots})
    try:
        mp.write_text(json.dumps(cur, indent=2))
        return f"✓ slot wt{n} claimed by this goal (marker slots={cur['slots']})."
    except Exception as e:
        return f"⚠ could not stamp slot ownership ({e}); reset succeeded regardless."


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
    args = [a for a in sys.argv[1:] if a.strip()]
    force = "--force" in args
    pos = [a for a in args if not a.startswith("-")]
    if not pos:
        print("usage: reset_slot.py <N> [--force]   (slot number, e.g. 1|2|3 or wt1)")
        return 2
    n = pos[0].strip().lower().removeprefix("wt")
    if not n.isdigit():
        print(f"⚠ invalid slot '{pos[0]}' — expected a number (1|2|3).")
        return 2

    root = repo_root()
    if root is None:
        print("⚠ repo root unresolved — launch from the workspace root or inside the repo. No action.")
        return 1
    slot = root / ".claude" / "worktrees" / f"wt{n}"
    if not (slot / ".git").exists():
        print(f"⚠ slot wt{n} not found at {slot}. Run scripts/setup_lean_worktree_slots.sh first.")
        return 1

    # OWNERSHIP GUARD (escape hatch = --force): if another goal's marker still owns this slot, refuse
    # so a goal cannot silently reclaim a slot another goal is anchored on (cross-goal isolation). The
    # HARD work-loss protection remains the unmerged-commits guard below; this is the softer, ownership
    # layer. A stale marker that outlived its goal is cleared via --force (or /goal-end + gc).
    ni = int(n)
    cur_sid = os.environ.get("CLAUDE_SESSION_ID", "").strip()
    cur = _load_marker(marker_path(root, cur_sid)) if cur_sid else None
    cur_goal = (cur or {}).get("goal_id")
    others = _other_owners(root, ni, cur_sid, cur_goal)
    if others and not force:
        print(f"⛔ slot wt{n} is currently owned by another goal's marker — refusing to reclaim:")
        for _mf, m in others:
            print(f"   goal_id={m.get('goal_id')} (role={m.get('role')})")
        print("→ if that goal is finished/paused, run its /goal-end (or `--force` to reclaim now). "
              "Committed work on the slot is separately protected by the unmerged-commits guard.")
        return 1

    branch = f"worktree-wt{n}"
    base = _base_ref(root)
    # GUARD: any commit on the slot branch not reachable from base would be discarded by the reset.
    # REFUSE on a git ERROR too (rc != 0), not only on non-empty output — else a bad base ref returns
    # empty and the guard is silently defeated, risking real work loss (adversarial review #2).
    log = _run(["git", "-C", str(slot), "log", "--oneline", f"{base}..HEAD"])
    if log.returncode != 0:
        print(f"⛔ could not verify slot wt{n} is safe to reset "
              f"(`git log {base}..HEAD` failed: {log.stderr.strip()}) — refusing.")
        print(f"→ confirm `{base}` exists and the slot is on branch {branch}, then retry.")
        return 1
    unmerged = log.stdout.strip()
    if unmerged:
        print(f"⛔ slot wt{n} has commits NOT on {base} — refusing to reset (would lose work):")
        print(unmerged)
        print("→ merge / cherry-pick them into main first, then re-run /reset-slot.")
        return 1

    # Safe: no divergence, so advancing the slot branch to base is loss-free (ff-equivalent).
    r = _run(["git", "-C", str(slot), "checkout", "-B", branch, base])
    if r.returncode != 0:
        print(f"⚠ `git checkout -B {branch} {base}` failed in wt{n}:\n{r.stderr.strip()}")
        return 1
    print(f"✓ slot wt{n} reset to main (branch {branch}).")
    stamp = _stamp_ownership(root, ni)
    if stamp:
        print(stamp)
    return _reclone_lake_if_stale(root, slot, n)


if __name__ == "__main__":
    sys.exit(main())
