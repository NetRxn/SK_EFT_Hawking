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

    def test_several_sections_are_each_accounted_for(self):
        """Meets the need that produced hand-written `…:5.1+5.2+5.3` keys without breaking
        the one-id-per-record invariant the reader depends on.

        ⚠️ Asserts that BOTH ids are named, not that both are written. Section 1.5 already
        carries a record from the ADR-012 pilot batch, and a message reading `2 record(s)`
        over a batch that writes one is a false count in the tool's own success line.
        """
        ok, msg = cf.close(doc=DOC, sections=[SECTION, "1.5"], status="fixed",
                           evidence=EVIDENCE, commit="b0f44815", dry_run=True)
        assert ok is True, msg
        assert f"{FID}" in msg
        assert "review:2026-05-01-1345-bundle-stage13:I1:1.5" in msg

    def test_an_already_recorded_finding_is_not_counted_as_written(self):
        """The count in the success line is the count actually written."""
        ok, msg = cf.close(doc=DOC, sections=["1.5"], status="fixed",
                           evidence=EVIDENCE, commit="b0f44815", dry_run=True)
        assert ok is True, msg
        assert "0 record(s)" in msg and "already recorded" in msg


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


VERIFY_DOC = "papers/AutomatedReviews/2026-08-12-0200-citation-integrity/D10.md"
VERIFY_SECTION = "1.1"


class TestTheDeclaredVerifyCommandIsAuthoritative:
    """⚠️ `verified_by` is the strongest evidence in the ledger — it is what makes the bar's
    Verify leg non-vacuous. A record carrying `exit_code: 0` reads to every consumer as *the
    declared check passed*, so a closer must not be able to satisfy it with `true`."""

    def test_an_unrelated_verify_command_is_REFUSED(self):
        ok, msg = cf.close(doc=VERIFY_DOC, sections=[VERIFY_SECTION], status="fixed",
                           evidence="x" * 60, commit="abc1234",
                           verify="true   # not the declared command", dry_run=True)
        assert ok is False
        assert "declares a verification command" in msg
        assert "check that never ran" in msg

    def test_the_declared_command_RUNS_when_no_verify_is_passed(self, monkeypatch):
        """Omitting --verify is not a way around the declared command."""
        seen = {}

        def _fake(cmd, **kw):
            seen["cmd"] = cmd
            return __import__("subprocess").CompletedProcess(cmd, 0, "", "")

        monkeypatch.setattr(cf.subprocess, "run", _fake)
        ok, _ = cf.close(doc=VERIFY_DOC, sections=[VERIFY_SECTION], status="fixed",
                         evidence="x" * 60, commit="abc1234", dry_run=True)
        assert ok is True
        assert "check_undefined_citations.py" in seen["cmd"]

    def test_the_declared_command_is_recorded_beside_what_ran(self, monkeypatch, tmp_path):
        p = tmp_path / "l.json"
        p.write_text(json.dumps({"supersessions": []}))
        monkeypatch.setattr(cf, "LEDGER", p)
        monkeypatch.setattr(
            cf.subprocess, "run",
            lambda cmd, **kw: __import__("subprocess").CompletedProcess(cmd, 0, "", ""))
        ok, _ = cf.close(doc=VERIFY_DOC, sections=[VERIFY_SECTION], status="fixed",
                         evidence="x" * 60, commit="abc1234")
        assert ok is True
        vb = json.loads(p.read_text())["supersessions"][0]["verified_by"]
        assert "check_undefined_citations.py" in vb["declared"]
        assert vb["exit_code"] == 0


class TestAMatchingRecordIsNotAutomaticallyIdempotent:
    """⚠️ The founding defect, regenerated inside the writer built to remove it: a prior
    `{"finding_id": X, "status": "fixed"}` with no evidence does NOT meet the closure bar,
    so the finding still reads `open`. Skipping the write because the status matches reports
    success over a finding that stays blocked."""

    def test_a_sub_bar_prior_record_is_REFUSED_not_reported_as_done(
            self, tmp_path, monkeypatch):
        p = tmp_path / "l.json"
        p.write_text(json.dumps(
            {"supersessions": [{"finding_id": FID, "status": "fixed"}]}))
        monkeypatch.setattr(cf, "LEDGER", p)
        ok, msg = cf.close(doc=DOC, sections=[SECTION], status="fixed",
                           evidence="x" * 60, commit="abc1234")
        assert ok is False
        assert "does NOT meet the closure bar" in msg
        assert "still reads `open`" in msg

    def test_an_above_bar_prior_record_IS_idempotent(self, tmp_path, monkeypatch):
        p = tmp_path / "l.json"
        p.write_text(json.dumps({"supersessions": [
            {"finding_id": FID, "status": "fixed", "evidence": "y" * 60,
             "date": "2026-01-01"}]}))
        monkeypatch.setattr(cf, "LEDGER", p)
        ok, msg = cf.close(doc=DOC, sections=[SECTION], status="fixed",
                           evidence="x" * 60, commit="abc1234")
        assert ok is True and "already recorded" in msg
        assert len(json.loads(p.read_text())["supersessions"]) == 1


class TestTheLifecycleIsCyclable:
    """`reopened` is in `VALID_STATUSES`, so it must be reachable. Before this, every prior
    record raised a conflict and reopening a finding was possible only by the hand edit the
    script exists to eliminate."""

    def _seed(self, tmp_path, monkeypatch, status):
        p = tmp_path / "l.json"
        p.write_text(json.dumps({"supersessions": [
            {"finding_id": FID, "status": status, "evidence": "y" * 60,
             "date": "2026-01-01"}]}))
        monkeypatch.setattr(cf, "LEDGER", p)
        return p

    def test_a_fixed_finding_can_be_reopened(self, tmp_path, monkeypatch):
        p = self._seed(tmp_path, monkeypatch, "fixed")
        ok, msg = cf.close(doc=DOC, sections=[SECTION], status="reopened",
                           evidence="x" * 60, commit="abc1234")
        assert ok is True, msg
        assert json.loads(p.read_text())["supersessions"][-1]["status"] == "reopened"

    def test_a_reopened_finding_can_be_closed_again(self, tmp_path, monkeypatch):
        p = self._seed(tmp_path, monkeypatch, "reopened")
        ok, msg = cf.close(doc=DOC, sections=[SECTION], status="fixed",
                           evidence="x" * 60, commit="abc1234")
        assert ok is True, msg
        assert json.loads(p.read_text())["supersessions"][-1]["status"] == "fixed"

    def test_a_reopened_record_reads_back_as_open(self):
        """⚠️ It lands in the unrecognised-token bucket, which is the right answer for the
        wrong reason — assert it deliberately, so widening `_KNOWN_STATUSES` later cannot
        silently make a reopened finding read closed."""
        import build_graph as bg
        assert "reopened" not in bg_known_statuses()


def bg_known_statuses():
    """The literal tuple as it appears in the extractor, read from source."""
    import re
    import build_graph as bg
    src = Path(bg.__file__).read_text(encoding="utf-8")
    m = re.search(r"_KNOWN_STATUSES = \(([^)]*)\)", src)
    return [t.strip().strip("'\"") for t in m.group(1).split(",") if t.strip()]


class TestDryRunPreviewsTheRefusals:
    """A preview that cannot show the thing it is previewing is not a preview. When the
    conflict scan lived inside the writer, `--dry-run` reported `would write 2 record(s)`
    for a batch the real invocation refused."""

    def test_a_conflict_is_visible_in_dry_run(self, tmp_path, monkeypatch):
        p = tmp_path / "l.json"
        p.write_text(json.dumps({"supersessions": [
            {"finding_id": FID, "status": "accepted", "evidence": "y" * 60,
             "date": "2026-01-01"}]}))
        monkeypatch.setattr(cf, "LEDGER", p)
        ok, msg = cf.close(doc=DOC, sections=[SECTION], status="fixed",
                           evidence="x" * 60, commit="abc1234", dry_run=True)
        assert ok is False
        assert "already carries status='accepted'" in msg


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
