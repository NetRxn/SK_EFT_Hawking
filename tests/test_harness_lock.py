# SK_EFT_Hawking/tests/test_harness_lock.py
"""Tests for the L1/L2/L3 regen concurrency lock (spec 12).
Run: cd SK_EFT_Hawking && uv run python -m pytest tests/test_harness_lock.py -q
scripts/ is not on sys.path — load via the helper (do NOT import at module level)."""
import importlib.util
import os
import sys
import time
from pathlib import Path

import pytest

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


# --- A caller must not report success over a regen the lock made it skip (A1) ---------
#
# The lock itself was never the defect: it reports contention honestly. The defect lived
# one layer up, in callers that discarded the signal — `sync.py` printed a skip line and
# still summarised "sync OK", so a run that left a stale artifact on disk was
# indistinguishable from one that regenerated it. These two tests pin BOTH directions;
# a test that only asserted the INCOMPLETE path could pass while the branch was dead.

def _run_sync_with_one_stale_edge(tmp_path, monkeypatch, *, contended: bool):
    """Drive sync.main over a single stale cheap edge, optionally under lock contention.

    Returns sync's stdout. The edge's regen_cmd is `true`, so nothing in the repo is
    touched — what is under test is the SUMMARY, not the regeneration.
    """
    import contextlib as _ctx
    import io
    hl = _load("harness_lock")
    monkeypatch.setattr(hl, "LOCKS_DIR", tmp_path)
    monkeypatch.setattr(hl, "WAIT_SECONDS", 0.2)   # bounded wait; semantics unchanged
    sync = _load("sync")
    monkeypatch.setattr(sync, "harness_lock", hl)  # same isolated locks dir as the holder
    edge = sync.sm.Edge("docs/fake_artifact.json", "n/a", ["true"], lambda: True, "cheap")
    monkeypatch.setattr(sync.sm, "EDGES", [edge])

    cap = io.StringIO()
    if contended:
        with hl.regen_lock(sync._lock_name(edge.output)) as got:
            assert got is True, "the holder must actually hold the lock"
            with _ctx.redirect_stdout(cap):
                rc = sync.main(["--fast"])
    else:
        with _ctx.redirect_stdout(cap):
            rc = sync.main(["--fast"])
    return rc, cap.getvalue()


def test_sync_reports_incomplete_when_the_lock_made_it_skip(tmp_path, monkeypatch):
    rc, out = _run_sync_with_one_stale_edge(tmp_path, monkeypatch, contended=True)
    assert "sync INCOMPLETE" in out, f"a skipped regen was reported as success: {out!r}"
    assert "docs/fake_artifact.json" in out, "the stale artifact must be NAMED, not counted"
    assert "sync OK" not in out
    # Exit 0 is deliberate: another process is doing the work, so failing the caller
    # would be wrong. The summary, not the exit code, carries the incompleteness.
    assert rc == 0


def test_sync_reports_ok_when_it_actually_regenerated(tmp_path, monkeypatch):
    """The falsifier for the test above: same stale edge, no contention -> plain OK.
    Without this, a summary hard-wired to INCOMPLETE would pass the first test."""
    rc, out = _run_sync_with_one_stale_edge(tmp_path, monkeypatch, contended=False)
    assert "sync OK" in out and "sync INCOMPLETE" not in out
    assert rc == 0


def test_extract_lean_deps_warns_loudly_when_it_skips(tmp_path, monkeypatch, caplog):
    """The other A1 caller. A skip here means every downstream consumer — counts, atlas,
    graph, axiom closure — is computed from the PREVIOUS extraction. That was logged at
    INFO, i.e. invisible at the default level, so a skipped run looked like a fresh one.
    The level is the assertion: WARNING or louder, naming what the staleness affects."""
    import logging
    hl = _load("harness_lock")
    monkeypatch.setattr(hl, "LOCKS_DIR", tmp_path)
    monkeypatch.setattr(hl, "WAIT_SECONDS", 0.2)
    eld = _load("extract_lean_deps")
    # _run_extraction must NOT reach the real extraction on the taken-lock path.
    monkeypatch.setattr(eld, "_run_extraction_locked",
                        lambda: pytest.fail("ran the extraction despite contention"))

    with hl.regen_lock("lean_deps") as got:
        assert got is True
        with caplog.at_level(logging.WARNING, logger=eld.logger.name):
            eld._run_extraction()

    recs = [r for r in caplog.records if r.levelno >= logging.WARNING]
    assert recs, "a skipped extraction was logged below WARNING — invisible by default"
    msg = recs[0].getMessage()
    assert "STALE" in msg and "PREVIOUS extraction" in msg, msg
