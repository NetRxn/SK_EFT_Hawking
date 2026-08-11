#!/usr/bin/env python3
"""L3 — the one foolproof mechanical-sync command. Regenerates stale
artifacts in dependency order off the L0 manifest, so the agent never
reconstructs a multi-script incantation.

  --fast : cheap derivations only (counts.tex/tables/index-autogen from the
           EXISTING counts.json). Safe in a commit gate.
  --full : everything — the heavy ExtractDeps/counts regen + the S1 citation
           chain. Use at /sync or /wave-close, NOT per commit (ExtractDeps is
           ~30 min). Excludes Aristotle (S4, user-gated).

Stdlib only. Exits nonzero if any regen command fails.
"""
from __future__ import annotations
import argparse
import subprocess
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
ROOT = SCRIPT_DIR.parent
sys.path.insert(0, str(SCRIPT_DIR))
import sync_manifest as sm  # noqa: E402
import harness_lock  # noqa: E402

# S1 citation chain (heavy / network) — ordered.
CITATION_CHAIN = [
    ["uv", "run", "python", "scripts/extract_missing_bibkeys.py"],
    ["uv", "run", "python", "scripts/back_fill_primary_sources.py", "--fetch"],
    ["uv", "run", "python", "scripts/promote_primary_sources.py"],
]


def _run(cmd: list[str]) -> bool:
    print(f"  $ {' '.join(cmd)}")
    return subprocess.run(cmd, cwd=str(ROOT)).returncode == 0


def _lock_name(output: str) -> str:
    # stable per-artifact lock name from the edge output label (e.g. "counts", "lean_deps")
    base = output.split()[0].rsplit("/", 1)[-1]
    return base.replace(".", "_").replace("+", "").strip("_") or "regen"


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Mechanical-sync engine (L3).")
    g = ap.add_mutually_exclusive_group()
    g.add_argument("--fast", action="store_true", help="cheap derivations only")
    g.add_argument("--full", action="store_true", help="heavy regen + citation chain")
    a = ap.parse_args(argv)
    fast = a.fast or not a.full  # default fast

    ok = True
    # Artifacts whose regeneration was SKIPPED because another process held the lock.
    # Tracked, not merely printed: a skip means this run proceeded on whatever was already
    # on disk, so "sync OK" would otherwise report success over work that did not happen.
    # The lock's own behaviour is correct — it reports contention honestly; the defect was
    # that callers discarded that signal (ARCHITECTURE_TODOs A1).
    skipped: list[str] = []
    # Dependency order: lean_deps/counts first (heavy), then cheap derivations. Each
    # shared-artifact regen is serialized by the regen concurrency lock (spec 12 / Task 7):
    # if another agent (parallel worktree / lead+worker) holds the lock, SKIP and proceed on
    # its fresh output rather than racing the same regen.
    for e in sm.EDGES:
        if fast and e.cost != "cheap":
            continue
        if e.is_stale():
            with harness_lock.regen_lock(_lock_name(e.output)) as got:
                if got:
                    ok = _run(e.regen_cmd) and ok
                else:
                    skipped.append(str(e.output))
                    print(f"  (skip {e.output}: another agent is regenerating it)")
    if a.full:
        print("citation chain (S1):")
        with harness_lock.regen_lock("citations") as got:
            if got:
                for cmd in CITATION_CHAIN:
                    ok = _run(cmd) and ok
                ok = _run(["uv", "run", "python", "scripts/validate.py",
                           "--check", "citation_primary_sources_present"]) and ok
            else:
                skipped.append("citation chain")
                print("  (skip citation chain: another agent is regenerating it)")

    # A skip is NOT a success. The exit code stays 0 — another process is doing the work and
    # failing the caller would be wrong — but the summary must never read "sync OK" when a
    # stale artifact was left in place, and it names what was skipped so the caller can re-run.
    if not ok:
        print("sync had failures")
        return 1
    if skipped:
        print(f"sync INCOMPLETE — {len(skipped)} artifact(s) left stale because another "
              f"process holds the lock: {', '.join(skipped)}")
        print("  re-run once it finishes; this run did NOT regenerate them")
        return 0
    print("sync OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
