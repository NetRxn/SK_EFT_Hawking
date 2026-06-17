# SK_EFT_Hawking/tests/test_harness_lock.py
"""Tests for the L1/L2/L3 regen concurrency lock (spec 12).
Run: cd SK_EFT_Hawking && uv run python -m pytest tests/test_harness_lock.py -q
scripts/ is not on sys.path — load via the helper (do NOT import at module level)."""
import importlib.util
import os
import sys
import time
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent.parent / "scripts"


def _load(mod):
    spec = importlib.util.spec_from_file_location(mod, SCRIPTS / f"{mod}.py")
    m = importlib.util.module_from_spec(spec)
    sys.modules[mod] = m            # register before exec (canonical importlib pattern)
    spec.loader.exec_module(m)
    return m


def test_second_acquirer_skips_while_first_holds(tmp_path, monkeypatch):
    m = _load("harness_lock")
    monkeypatch.setattr(m, "LOCKS_DIR", tmp_path)  # isolate from the real repo locks dir
    ran = []
    with m.regen_lock("counts") as got_first:
        assert got_first is True               # first acquirer holds the lock
        with m.regen_lock("counts") as got_second:
            # bounded wait elapses, lock still held -> skip-if-locked -> acquired == False
            assert got_second is False
            if got_second:
                ran.append("second")
    assert ran == []                            # the waiter must NOT have re-run the regen


def test_stale_lock_is_reclaimed(tmp_path, monkeypatch):
    m = _load("harness_lock")
    monkeypatch.setattr(m, "LOCKS_DIR", tmp_path)
    # Plant a lock that looks abandoned: a dead PID + an mtime older than the stale timeout.
    lf = tmp_path / "counts.lock"
    lf.write_text('{"pid": 999999, "ts": 1.0}')                 # PID unlikely to exist; ancient ts
    os.utime(lf, (1.0, 1.0))
    with m.regen_lock("counts") as got:
        assert got is True                       # the stale lock was reclaimed, not blocked on


def test_fail_open_on_lock_error(tmp_path, monkeypatch):
    """A lock-subsystem error must NOT block work: the context manager yields True (proceed)."""
    m = _load("harness_lock")
    monkeypatch.setattr(m, "LOCKS_DIR", tmp_path)
    def _boom(*a, **k):
        raise OSError("simulated lock-subsystem failure")
    monkeypatch.setattr(m, "_acquire", _boom)    # force the acquire path to raise
    with m.regen_lock("counts") as got:
        assert got is True                       # fail-open: proceed despite the error
