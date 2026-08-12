"""The ledger writer.

Spec: `docs/superpowers/specs/2026-08-12-finding-closure-lifecycle-design.md` §4.
ADR:  `docs/adrs/ADR-012-finding-lifecycle-routing-and-closure.md` D14.

Every test here drives the REAL `close()` in `--dry-run`, so the tracked 645 KB ledger is
never touched by the suite. The one test that exercises the write path builds its own
ledger in `tmp_path` and repoints the module constant.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT))
sys.path.insert(0, str(PROJECT_ROOT / "scripts"))

import close_finding as cf  # noqa: E402

# A live finding that carries no ledger record. If this ever stops resolving, pick another
# from `build_graph.extract_review_finding_nodes()` — do NOT weaken the assertions.
DOC = "papers/AutomatedReviews/2026-05-01-1345-bundle-stage13/I1.md"
SECTION = "1.4"
FID = "review:2026-05-01-1345-bundle-stage13:I1:1.4"
EVIDENCE = ("Figure rebuilt from the module dependency edges; every label resolves by "
            "exact name in lean_deps.json.")


class TestTheHappyPath:
    def test_a_resolvable_finding_is_written(self):
        ok, msg = cf.close(doc=DOC, sections=[SECTION], status="fixed",
                           evidence=EVIDENCE, commit="b0f44815", dry_run=True)
        assert ok is True, msg
        assert FID in msg

    def test_the_minter_is_the_shared_one(self):
        """`close_finding` must mint with the function the EXTRACTOR uses. Two
        implementations is how 66 review:-scheme records came to name no node."""
        import build_graph as bg
        assert cf._bg.mint_finding_id is bg.mint_finding_id

    def test_several_sections_write_one_record_each(self):
        """Meets the need that produced hand-written `…:5.1+5.2+5.3` keys without breaking
        the one-id-per-record invariant the reader depends on."""
        ok, msg = cf.close(doc=DOC, sections=[SECTION, "1.5"], status="fixed",
                           evidence=EVIDENCE, commit="b0f44815", dry_run=True)
        assert ok is True, msg
        assert "2 record(s)" in msg


class TestTheRefusals:
    def test_an_unresolvable_id_is_refused_and_lists_what_exists(self):
        ok, msg = cf.close(doc=DOC, sections=["99.99"], status="fixed",
                           evidence="x" * 60, commit="deadbeef", dry_run=True)
        assert ok is False
        assert "no such finding" in msg.lower()
        # the caller must SEE the real section numbers, not be left guessing
        assert FID in msg

    def test_an_unknown_status_is_refused(self):
        ok, msg = cf.close(doc=DOC, sections=[SECTION], status="closed",
                           evidence="x" * 60, commit="abc", dry_run=True)
        assert ok is False and "status" in msg.lower()

    def test_thin_evidence_is_refused(self):
        ok, msg = cf.close(doc=DOC, sections=[SECTION], status="fixed",
                           evidence="fixed it", commit="b0f44815", dry_run=True)
        assert ok is False and "evidence" in msg.lower()

    def test_a_closure_with_no_anchor_is_refused(self):
        ok, msg = cf.close(doc=DOC, sections=[SECTION], status="fixed",
                           evidence="x" * 60, dry_run=True)
        assert ok is False and "anchor" in msg.lower()

    def test_a_failing_verify_command_is_refused(self):
        ok, msg = cf.close(doc=DOC, sections=[SECTION], status="fixed",
                           evidence="x" * 60, commit="b0f44815",
                           verify='python3 -c "raise SystemExit(1)"', dry_run=True)
        assert ok is False and "verify" in msg.lower()

    def test_a_passing_verify_command_is_accepted(self):
        ok, msg = cf.close(doc=DOC, sections=[SECTION], status="fixed",
                           evidence="x" * 60, commit="b0f44815",
                           verify='python3 -c "pass"', dry_run=True)
        assert ok is True, msg


class TestSerialization:
    def _ledger(self, tmp_path, records):
        p = tmp_path / "review_finding_supersessions.json"
        p.write_text(json.dumps({"supersessions": records}, indent=2) + "\n")
        return p

    def test_a_conflicting_existing_record_is_a_refusal_not_a_crash(
            self, tmp_path, monkeypatch):
        """⚠️ `_load_supersession_ledger` is LAST-WINS and does not say so. Appending a
        second record with a different status means one of the pair silently does nothing
        — the defect this script exists to remove, reintroduced by its own writer. And a
        raise mid-batch escapes AFTER earlier records were already written to a tracked
        file, so it must surface as a refusal.
        """
        p = self._ledger(tmp_path, [{"finding_id": FID, "status": "open",
                                     "evidence": "y" * 60, "date": "2026-01-01"}])
        monkeypatch.setattr(cf, "LEDGER", p)
        ok, msg = cf.close(doc=DOC, sections=[SECTION], status="fixed",
                           evidence="x" * 60, commit="abc1234")
        assert ok is False
        assert "already carries status='open'" in msg
        assert json.loads(p.read_text())["supersessions"][0]["status"] == "open"

    def test_writing_the_same_status_twice_is_idempotent(self, tmp_path, monkeypatch):
        p = self._ledger(tmp_path, [{"finding_id": FID, "status": "fixed",
                                     "evidence": "y" * 60, "date": "2026-01-01"}])
        monkeypatch.setattr(cf, "LEDGER", p)
        ok, _ = cf.close(doc=DOC, sections=[SECTION], status="fixed",
                         evidence="x" * 60, commit="abc1234")
        assert ok is True
        assert len(json.loads(p.read_text())["supersessions"]) == 1

    def test_a_record_round_trips_with_its_verified_by(self, tmp_path, monkeypatch):
        p = self._ledger(tmp_path, [])
        monkeypatch.setattr(cf, "LEDGER", p)
        ok, _ = cf.close(doc=DOC, sections=[SECTION], status="fixed",
                         evidence="x" * 60, commit="abc1234",
                         verify='python3 -c "pass"')
        assert ok is True
        rec = json.loads(p.read_text())["supersessions"][0]
        assert rec["finding_id"] == FID
        assert rec["verified_by"]["exit_code"] == 0
        assert rec["verified_by"]["command"] == 'python3 -c "pass"'
        # ⚠️ the RAW command must never land in verified_by's slot — Task 8's interface bug
        assert isinstance(rec["verified_by"], dict)

    def test_the_write_is_atomic(self, tmp_path, monkeypatch):
        """A crash mid-write leaves the ONLY closure channel malformed, and every reader
        is told to fail closed on that. Assert no temp file survives and the JSON parses."""
        p = self._ledger(tmp_path, [])
        monkeypatch.setattr(cf, "LEDGER", p)
        cf.close(doc=DOC, sections=[SECTION], status="fixed", evidence="x" * 60,
                 commit="abc1234")
        assert not list(tmp_path.glob("*.tmp")), "a temp file survived the write"
        json.loads(p.read_text())          # parses


class TestTheCLI:
    def test_main_returns_1_and_says_refused(self, capsys):
        rc = cf.main(["--doc", DOC, "--section", "99.99", "--status", "fixed",
                      "--evidence", "x" * 60, "--commit", "abc", "--dry-run"])
        assert rc == 1
        assert "✗ REFUSED — " in capsys.readouterr().out

    def test_main_returns_0_and_says_ok(self, capsys):
        rc = cf.main(["--doc", DOC, "--section", SECTION, "--status", "fixed",
                      "--evidence", EVIDENCE, "--commit", "abc", "--dry-run"])
        assert rc == 0
        assert "✓ " in capsys.readouterr().out
