#!/usr/bin/env python3
"""Regen concurrency lock (spec 12). A per-artifact file lock under
<repo>/.claude/dev-harness/locks/ that serializes shared-artifact regen so
two concurrent agents (parallel worktrees, lead+workers) can't trigger the
same regen process at once.

Semantics:
  - NON-BLOCKING with a short bounded wait (WAIT_SECONDS), then SKIP-IF-LOCKED:
    if the lock is still held after the wait, the caller does NOT run the regen
    (the holder is already producing the same artifact; the caller proceeds on
    that fresh output). `regen_lock(name)` yields True if acquired (run the
    regen), False if skipped (do not run).
  - STALE-SAFE: a lock whose PID is dead OR whose mtime is older than
    STALE_SECONDS is reclaimed, so a crashed agent never deadlocks the loop.
  - FAIL-OPEN: any lock-subsystem error -> log to stderr and yield True
    (proceed); the lock must never block real work.

Stdlib only; Python-3.9-safe (no `X | Y` runtime unions, no `match`).
"""
from __future__ import annotations
import contextlib
import json
import os
import sys
import time
from pathlib import Path
from typing import Iterator


def _repo_root() -> Path:
    # Prefer the Plan-1 Foundation resolver (spec A.3) when importable; else
    # derive <repo> from this file's location (<repo>/scripts/harness_lock.py).
    try:
        sys.path.insert(0, str(Path(__file__).resolve().parent))
        from harness_common import repo_root  # type: ignore
        r = repo_root()
        if r:
            return Path(r)
    except Exception:
        pass
    return Path(__file__).resolve().parent.parent


LOCKS_DIR = _repo_root() / ".claude" / "dev-harness" / "locks"
WAIT_SECONDS = 5.0      # short bounded wait before skip-if-locked
POLL_SECONDS = 0.25
STALE_SECONDS = 1800.0  # reclaim a lock abandoned > 30 min (>= the ExtractDeps ceiling)


def _pid_alive(pid: int) -> bool:
    if pid <= 0:
        return False
    try:
        os.kill(pid, 0)
    except OSError as e:
        # ESRCH -> no such process (dead). EPERM -> exists but not ours (alive).
        import errno
        return e.errno != errno.ESRCH
    return True


def _is_stale(lock_path: Path) -> bool:
    try:
        meta = json.loads(lock_path.read_text())
    except Exception:
        return True  # unreadable/garbage lock -> treat as stale (reclaimable)
    if (time.time() - lock_path.stat().st_mtime) > STALE_SECONDS:
        return True
    return not _pid_alive(int(meta.get("pid", -1)))


def _create_excl(lock_path: Path) -> bool:
    """One atomic O_EXCL create. True on success, False if it already exists."""
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    try:
        fd = os.open(str(lock_path), os.O_CREAT | os.O_EXCL | os.O_WRONLY)
        os.write(fd, json.dumps({"pid": os.getpid(), "ts": time.time()}).encode())
        os.close(fd)
        return True
    except FileExistsError:
        return False


def _acquire(lock_path: Path) -> bool:
    """Try to create the lock atomically; if it exists but is stale, reclaim it and
    re-attempt **exactly once** (BOUNDED — review D3: a single retry, NOT self-recursion,
    so a pathological reclaim race where another agent keeps re-taking the lock can't
    recurse unboundedly / blow the stack — the bounded outer wait in `regen_lock` is the
    only loop). Returns True on acquire, False otherwise. Separated out so tests can force
    an error (fail-open)."""
    if _create_excl(lock_path):
        return True
    if _is_stale(lock_path):
        try:
            lock_path.unlink()
        except FileNotFoundError:
            pass
        return _create_excl(lock_path)  # ONE bounded re-attempt after reclaiming; no recursion
    return False


@contextlib.contextmanager
def regen_lock(name: str) -> Iterator[bool]:
    """Context manager. Yields True if the caller acquired the lock (RUN the
    regen) or False if it should SKIP (holder is already regenerating). Bounded
    non-blocking wait, stale-safe, fail-open."""
    lock_path = LOCKS_DIR / (name + ".lock")
    acquired = False
    try:
        deadline = time.time() + WAIT_SECONDS
        acquired = _acquire(lock_path)
        while not acquired and time.time() < deadline:
            time.sleep(POLL_SECONDS)
            acquired = _acquire(lock_path)
    except Exception as e:  # FAIL-OPEN — never block real work on a lock bug
        print(f"(harness_lock: {name}: {e} — failing open, proceeding)", file=sys.stderr)
        yield True
        return
    try:
        yield acquired
    finally:
        if acquired:
            try:
                lock_path.unlink()
            except FileNotFoundError:
                pass


if __name__ == "__main__":
    # smoke: `python3 scripts/harness_lock.py counts` -> prints acquire result
    nm = sys.argv[1] if len(sys.argv) > 1 else "smoke"
    with regen_lock(nm) as ok:
        print(f"acquired={ok} lock={LOCKS_DIR / (nm + '.lock')}")
