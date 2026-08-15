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
    """Restore the ledger byte-for-byte no matter how the test exits.

    ⚠️ "NO MATTER HOW" USED TO EXCLUDE `SIGKILL`, and the supersession ledger is the ONE
    channel that can close a finding — residue here does not merely dirty a file, it
    closes or reopens real blockers for every consumer that reads the tree afterwards.
    Since 2026-08-15 the restore is journalled to `.seed-journal/` before the ledger is
    touched, so a later process can complete it.
    """
    from scripts.seed_journal import journalled
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

    with journalled(LEDGER, reason="bypass-shaped supersession records must not close a "
                                   "blocking finding"):
        yield _apply
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
    from scripts.seed_journal import journalled
    original = LEDGER.read_text()
    with journalled(LEDGER, reason="a well-formed supersession record MUST close its "
                                   "finding — the guard must not be vacuously strict"):
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
    importlib.reload(BG)


class TestTheBarAppliesAtEverySeverity:
    """D12 13.2 — open across FOUR consecutive rounds and reproducing at HEAD.

    The bar was gated on `severity in ('critical','major','blocker')`. Below that line a
    two-key record — no evidence, no anchor — closed a finding. And `- **Severity:**` is
    declarable in the finding BODY, where the declared value beats the heading glyph, with
    `_SEVERITY_DECL_MAP` mapping `recommended -> minor`: so a 🔴 BLOCKER heading declaring
    `recommended` closed on `{"finding_id": X, "status": "fixed"}`.
    """

    def test_a_content_free_record_cannot_close(self):
        from scripts.build_graph import _closure_record_meets_bar
        assert _closure_record_meets_bar({"finding_id": "x", "status": "fixed"}) is False

    def test_an_accepted_two_key_record_cannot_close_either(self):
        """Round 10 keyed on `== 'fixed'` alone, so `accepted` walked straight through —
        `_eval_fix_propagation` partitions it out before the severity filter runs."""
        from scripts.build_graph import _closure_record_meets_bar
        assert _closure_record_meets_bar({"finding_id": "x", "status": "accepted"}) is False

    def test_evidence_without_an_anchor_does_not_close(self):
        from scripts.build_graph import _closure_record_meets_bar
        assert _closure_record_meets_bar(
            {"status": "fixed", "evidence": "y" * 60}) is False

    def test_an_anchor_without_evidence_does_not_close(self):
        from scripts.build_graph import _closure_record_meets_bar
        assert _closure_record_meets_bar(
            {"status": "fixed", "commit": "abc1234"}) is False

    def test_a_complete_record_closes(self):
        from scripts.build_graph import _closure_record_meets_bar
        assert _closure_record_meets_bar(
            {"status": "fixed", "evidence": "y" * 60, "commit": "abc1234"}) is True

    def test_the_bar_stays_schema_tolerant(self):
        """264 historical blocking closures use (date, evidence, ...) and 23 use
        commit/closed_by/closed_date. Requiring `commit` would reopen 264 well-formed
        closures — a guard firing on correct data gets switched off."""
        from scripts.build_graph import _closure_record_meets_bar
        for anchor in ("date", "closed_date", "applied_at"):
            assert _closure_record_meets_bar(
                {"status": "fixed", "evidence": "y" * 60, anchor: "2026-08-12"}) is True
        for alias in ("note", "rationale"):
            assert _closure_record_meets_bar(
                {"status": "fixed", alias: "y" * 60, "commit": "abc"}) is True

    def test_the_severity_scoping_is_gone_from_the_source(self):
        """Structural: the bypass was re-introduced twice by narrowing the guard rather
        than removing the class. Assert the scope test itself is absent."""
        import inspect
        from scripts import build_graph as BG
        src = inspect.getsource(BG)
        assert "severity in ('critical', 'major', 'blocker')" not in src


class TestVerifiedByIsRequiredWhenTheFindingDeclaresAVerify:
    """ADR-012 D6.2. Live ONLY because the extractor now parses a `Verify:` line — shipping
    this parameter without that producer would have been a leg that cannot fire."""

    def test_missing_verified_by_fails(self):
        from scripts.build_graph import _closure_record_meets_bar
        assert _closure_record_meets_bar(
            {"status": "fixed", "evidence": "y" * 60, "commit": "abc"},
            finding_has_verify=True) is False

    def test_a_passing_verified_by_succeeds(self):
        from scripts.build_graph import _closure_record_meets_bar
        assert _closure_record_meets_bar(
            {"status": "fixed", "evidence": "y" * 60, "commit": "abc",
             "verified_by": {"command": "pytest -q", "exit_code": 0,
                             "run_at": "2026-08-12"}},
            finding_has_verify=True) is True

    def test_a_recorded_nonzero_exit_does_not_close(self):
        from scripts.build_graph import _closure_record_meets_bar
        assert _closure_record_meets_bar(
            {"status": "fixed", "evidence": "y" * 60, "commit": "abc",
             "verified_by": {"command": "pytest -q", "exit_code": 1,
                             "run_at": "2026-08-12"}},
            finding_has_verify=True) is False

    def test_an_empty_command_does_not_close(self):
        """A verified_by asserting exit 0 for no command is an assertion about nothing."""
        from scripts.build_graph import _closure_record_meets_bar
        assert _closure_record_meets_bar(
            {"status": "fixed", "evidence": "y" * 60, "commit": "abc",
             "verified_by": {"command": "", "exit_code": 0}},
            finding_has_verify=True) is False

    def test_a_finding_without_a_verify_is_unaffected(self):
        from scripts.build_graph import _closure_record_meets_bar
        assert _closure_record_meets_bar(
            {"status": "fixed", "evidence": "y" * 60, "commit": "abc"}) is True
