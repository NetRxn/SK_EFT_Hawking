"""Regression tests for the blocking-closure guard.

Why this file exists
--------------------
D12 Stage-13 findings 8.1 recurred across FOUR consecutive review rounds
(2026-07-31 at 1823, 2022, 2103, 2220). Each round the guard was declared fixed;
each next round found the fix inert by a slightly different route:

  * 1823 — a one-key ledger record (`{"finding_id": X}`) closed a 🔴 BLOCKER,
    and the closing document set its own severity;
  * 2022 — the guard ran, but the line immediately after it overwrote the
    verdict, so a two-key record still closed a blocker;
  * 2103 — the guard was scoped to `status: fixed`, so the two-key bypass
    survived verbatim as `{"finding_id": X, "status": "accepted"}`;
  * 2220 — heading-parse closure was still executing at `build_graph.py`
    despite a comment saying it had been deleted.

The through-line is not any one bug. It is that **the guard was verified by
reading it rather than by attacking it**, so a defect that left the code looking
correct survived every reading. These tests attack it: each constructs a ledger
record of a historically-successful bypass shape and asserts a live blocking
finding STAYS open.

`test_ledger_is_restored` is not ceremony — these tests mutate a tracked file in
place, and an earlier version of this exercise left the repository dirty.
"""
from __future__ import annotations

import importlib
import json
from pathlib import Path

import pytest

import scripts.build_graph as BG

LEDGER = Path(__file__).resolve().parent.parent / "docs" / "review_finding_supersessions.json"


def _open_blocker_id() -> str:
    """Id of some live finding that is open AND blocking-severity."""
    for f in BG.extract_review_finding_nodes():
        m = f.get("meta", {})
        if m.get("status") == "open" and m.get("severity") in ("critical", "blocker"):
            return f["id"]
    pytest.skip("no open blocking finding in the corpus to attack")


@pytest.fixture
def ledger_sandbox():
    """Restore the ledger byte-for-byte no matter how the test exits."""
    original = LEDGER.read_text()

    def _apply(record: dict) -> str:
        data = json.loads(original)
        data["supersessions"].append(record)
        LEDGER.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n")
        importlib.reload(BG)
        target = record["finding_id"]
        return next(
            (f["meta"]["status"] for f in BG.extract_review_finding_nodes()
             if f["id"] == target),
            "MISSING",
        )

    yield _apply
    LEDGER.write_text(original)
    importlib.reload(BG)


def test_heading_parse_closure_is_gone():
    """Round 2220: a comment claimed this was deleted while it still executed.

    Asserted against the source text, not the behaviour, because the defect was
    precisely that the behaviour looked right from the outside.
    """
    src = (Path(__file__).resolve().parent.parent / "scripts" / "build_graph.py").read_text()
    assert src.count("status = 'fixed'") == 0, (
        "heading-parse closure is executing again — every finding must be born "
        "`open`, with the supersession ledger the sole channel that can transition it"
    )


@pytest.mark.parametrize("shape,record_extra", [
    ("one-key", {}),
    ("two-key-fixed", {"status": "fixed"}),
    ("two-key-accepted", {"status": "accepted"}),
    ("evidence-without-anchor", {"status": "fixed", "evidence": "x" * 120}),
    ("anchor-with-thin-evidence", {"status": "fixed", "evidence": "too short",
                                   "commit": "deadbeef"}),
    ("accepted-thin-evidence", {"status": "accepted", "evidence": "ok",
                                "closed_date": "2026-08-01"}),
])
def test_bypass_shape_cannot_close_a_blocker(ledger_sandbox, shape, record_extra):
    """Each shape closed a live 🔴 BLOCKER in some round of the 8.1 chain."""
    target = _open_blocker_id()
    status = ledger_sandbox({"finding_id": target, **record_extra})
    assert status == "open", (
        f"bypass shape {shape!r} closed a blocking finding: {target} -> {status}. "
        f"A blocking closure requires status in (fixed, accepted) AND >=40 chars of "
        f"evidence AND a commit/date anchor."
    )


def test_ledger_is_restored():
    """The sandbox must leave the tracked ledger byte-identical.

    Runs the fixture's full lifecycle manually, because the restore happens in
    teardown — a test that used the fixture normally could only observe the
    mutated state, never the restoration. (The first draft of this test asserted
    `... or True`, which is vacuous: the very defect class this file exists for,
    written into the file that tests for it.)
    """
    before = LEDGER.read_text()
    gen = ledger_sandbox.__wrapped__()
    apply = next(gen)
    apply({"finding_id": _open_blocker_id(), "status": "fixed"})
    assert LEDGER.read_text() != before, "sandbox did not actually mutate the ledger"
    with pytest.raises(StopIteration):
        next(gen)  # drives teardown
    assert LEDGER.read_text() == before, "sandbox left the tracked ledger modified"


def test_a_well_formed_record_DOES_close():
    """The guard must not be vacuously strict — a proper record has to work.

    Without this leg, deleting the ledger reader entirely would pass every test
    above. That is the mirror of the defect this file exists for.
    """
    original = LEDGER.read_text()
    try:
        target = _open_blocker_id()
        data = json.loads(original)
        data["supersessions"].append({
            "finding_id": target,
            "status": "fixed",
            "closed_date": "2026-08-01",
            "commit": "0123456789abcdef",
            "evidence": (
                "A well-formed closure: status fixed, a commit anchor, and evidence "
                "comfortably past the forty-character bar so the guard admits it."),
        })
        LEDGER.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n")
        importlib.reload(BG)
        status = next((f["meta"]["status"] for f in BG.extract_review_finding_nodes()
                       if f["id"] == target), "MISSING")
        assert status == "fixed", (
            f"a well-formed ledger record failed to close {target} (got {status!r}) — "
            f"the guard is vacuously strict and closure is impossible")
    finally:
        LEDGER.write_text(original)
        importlib.reload(BG)
