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


class TestTheWriteIsDurableUnderConcurrency:
    """⚠️ Filed 2026-08-15 after a REAL loss, not a theoretical one. A closure for
    `…2026-07-31-1823…:D12:8.6` printed `✓ wrote 1 record(s)`, exited 0, and the record
    was absent from the ledger afterwards while an earlier one survived. Five workers were
    running. The re-read that `_write` already performed was reasoned to make the window
    "too small to matter"; `json.dump` of 645 KB is not instantaneous and the guess was
    wrong.
    """

    def _ledger(self, tmp_path, monkeypatch, records):
        p = tmp_path / "review_finding_supersessions.json"
        p.write_text(json.dumps({"supersessions": records}))
        monkeypatch.setattr(cf, "LEDGER", p)
        return p

    def test_the_lock_lives_beside_the_CURRENT_ledger(self, tmp_path, monkeypatch):
        """A module-level constant would keep locking the real `docs/` file, so the suite
        would serialise against live closures and leave a lockfile in the tree."""
        p = self._ledger(tmp_path, monkeypatch, [])
        assert cf._lock_path().parent == p.parent

    def test_a_lock_respecting_writer_is_SERIALISED_not_interleaved(
            self, tmp_path, monkeypatch):
        """The lock's actual guarantee: a second writer that takes it WAITS, so its read
        happens after the first write and neither snapshot is stale.

        Two `open()` calls get separate fds, so `flock` arbitrates between them even
        inside one process — which is what makes this testable without a subprocess.
        """
        p = self._ledger(tmp_path, monkeypatch, [])
        with cf._ledger_lock():
            p.write_text(json.dumps({"supersessions": [
                {"finding_id": "review:other:X:1.1", "status": "fixed",
                 "evidence": "z" * 60, "date": "2026-01-01"}]}))
            with pytest.raises(TimeoutError, match="held"):
                with cf._ledger_lock(timeout=0.2):
                    pass                       # a second holder must not get in
        # Released: the next writer reads the interloper's state and adds to it.
        ok, msg = cf.close(doc=DOC, sections=[SECTION], status="fixed",
                           evidence="x" * 60, commit="abc1234")
        assert ok is True, msg
        ids = [e["finding_id"] for e in json.loads(p.read_text())["supersessions"]]
        assert ids == ["review:other:X:1.1", FID], (
            f"a serialised writer lost a record: {ids}")

    def test_a_writer_that_IGNORES_the_lock_is_still_caught(
            self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — the 8.6 loss, reproduced deterministically.

        A lock only binds participants. This seeds the non-participant: a writer that
        replaces the file inside the locked window, clobbering the record just written.
        The lock cannot stop it; the read-back must still refuse to call it success.
        """
        p = self._ledger(tmp_path, monkeypatch, [])
        real_atomic = cf._atomic_write

        def _clobber(data):
            real_atomic(data)
            p.write_text(json.dumps({"supersessions": [
                {"finding_id": "review:other:X:1.1", "status": "fixed"}]}))

        monkeypatch.setattr(cf, "_atomic_write", _clobber)
        ok, msg = cf.close(doc=DOC, sections=[SECTION], status="fixed",
                           evidence="x" * 60, commit="abc1234")
        assert ok is False, "a clobbered closure reported SUCCESS — this is the 8.6 loss"
        assert "WRITE LOST" in msg and FID in msg

    def test_a_lost_write_is_RAISED_not_reported_as_success(
            self, tmp_path, monkeypatch):
        """The success line is printed from the in-memory plan, so without a read-back it
        asserts what the tool INTENDED rather than what the file holds. Seed a writer that
        drops the record entirely and require the tool to notice."""
        p = self._ledger(tmp_path, monkeypatch, [])
        monkeypatch.setattr(
            cf, "_atomic_write",
            lambda data: p.write_text(json.dumps({"supersessions": []})))
        ok, msg = cf.close(doc=DOC, sections=[SECTION], status="fixed",
                           evidence="x" * 60, commit="abc1234")
        assert ok is False, "a closure whose record never landed reported SUCCESS"
        assert "WRITE LOST" in msg and FID in msg


class TestAnInertOpenRecordDoesNotBlockClosure:
    """⚠️ Findings are BORN `open` (`build_graph.py` BIRTH-STATUS INVARIANT), so a ledger
    record restating `open` asserts nothing and changes no reader's answer. Refusing on it
    made the *presence of a record that does nothing* permanently unclosable through the
    sole writer — and the refusal's own advice, "amend the existing record", names an
    operation this tool does not offer.

    Seeded into a COPY OF THE PRODUCTION LEDGER, not a two-record fixture: the guard reads
    the real 645 KB record set, and a fixture-only mutation would prove the test works
    rather than that the writer can be blocked in production. Measured 2026-08-15 before
    the fix: 10 findings carried an inert `open` record and 5 were open BLOCKING findings
    on the 21 submission bundles.
    """

    def _production_ledger_plus(self, tmp_path, monkeypatch, seeded):
        real = json.loads(cf.LEDGER.read_text(encoding="utf-8"))
        assert len(real["supersessions"]) > 100, (
            "expected the production ledger; a tiny one means LEDGER was already repointed "
            "and this test is no longer production-seeded")
        real["supersessions"].append(seeded)
        p = tmp_path / "review_finding_supersessions.json"
        p.write_text(json.dumps(real))
        monkeypatch.setattr(cf, "LEDGER", p)
        return p

    def test_an_inert_open_prior_falls_through_to_the_write(self, tmp_path, monkeypatch):
        p = self._production_ledger_plus(
            tmp_path, monkeypatch,
            {"finding_id": FID, "status": "open", "evidence": "the original description"})
        ok, msg = cf.close(doc=DOC, sections=[SECTION], status="fixed",
                           evidence="x" * 60, commit="abc1234")
        assert ok is True, msg
        assert json.loads(p.read_text())["supersessions"][-1]["status"] == "fixed"

    def test_the_closure_records_that_it_walked_over_an_inert_record(
            self, tmp_path, monkeypatch):
        """Without the marker the ledger reads as if nothing preceded the closure, and the
        next reader cannot tell an inert prior from no prior at all."""
        p = self._production_ledger_plus(
            tmp_path, monkeypatch, {"finding_id": FID, "status": "open"})
        ok, msg = cf.close(doc=DOC, sections=[SECTION], status="fixed",
                           evidence="x" * 60, commit="abc1234")
        assert ok is True, msg
        assert json.loads(p.read_text())["supersessions"][-1]["supersedes_inert_open"] is True

    def test_a_SUB_BAR_prior_of_another_status_is_also_inert(
            self, tmp_path, monkeypatch):
        """A closure that does not meet the bar leaves the finding reading `open`, so it
        changes no reader's answer — inert for the same reason an `open` record is.

        ⚠️ Measured on a real stranding. `review:2026-08-14-l1-stage13:L1:3.2` carried a
        substantive `accepted` record that could NEVER meet the bar: the finding declared
        a Verify asserting one branch of a two-branch Expected while the decision took the
        other, so the declared command could not pass under the decision actually made, no
        record could carry a passing `verified_by`, and the finding read `open`
        permanently. The Verify was the defect; this guard turned it into a life sentence.
        """
        self._production_ledger_plus(
            tmp_path, monkeypatch,
            {"finding_id": FID, "status": "accepted"})   # no evidence -> below the bar
        ok, msg = cf.close(doc=DOC, sections=[SECTION], status="fixed",
                           evidence="x" * 60, commit="abc1234")
        assert ok is True, msg

    def test_an_accepted_prior_is_STILL_refused(self, tmp_path, monkeypatch):
        """The narrowness is the point. `fixed`↔`accepted` and the below-the-bar-`fixed`
        refusals are each load-bearing; widening the guard past `open` reopens both."""
        self._production_ledger_plus(
            tmp_path, monkeypatch,
            {"finding_id": FID, "status": "accepted", "evidence": "y" * 60,
             "date": "2026-01-01"})
        ok, msg = cf.close(doc=DOC, sections=[SECTION], status="fixed",
                           evidence="x" * 60, commit="abc1234")
        assert ok is False
        assert "refusing to append a conflicting" in msg

    def test_a_sub_bar_fixed_prior_is_STILL_refused(self, tmp_path, monkeypatch):
        self._production_ledger_plus(
            tmp_path, monkeypatch, {"finding_id": FID, "status": "fixed"})
        ok, msg = cf.close(doc=DOC, sections=[SECTION], status="fixed",
                           evidence="x" * 60, commit="abc1234")
        assert ok is False
        assert "does NOT meet the closure bar" in msg


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

        ⚠️ This test seeded `status: "open"` until 2026-08-15 — using the one status that
        is NOT a conflict as its stand-in for "a conflicting prior". Findings are born
        `open`, so that record asserted nothing, and the test was pinning a refusal that
        should never have fired (see `TestAnInertOpenRecordDoesNotBlockClosure`). The
        intent below is unchanged; only the fixture moved to a genuine conflict.
        """
        p = self._ledger(tmp_path, [{"finding_id": FID, "status": "accepted",
                                     "evidence": "y" * 60, "date": "2026-01-01"}])
        monkeypatch.setattr(cf, "LEDGER", p)
        ok, msg = cf.close(doc=DOC, sections=[SECTION], status="fixed",
                           evidence="x" * 60, commit="abc1234")
        assert ok is False
        assert "already carries status='accepted'" in msg
        assert json.loads(p.read_text())["supersessions"][0]["status"] == "accepted"

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


# ── ADR-012 — `accepted` records its verify, `fixed` still enforces it ────────
#
# `accepted` means a decision NOT to fix, so its declared verify normally encodes
# the state the decision declines to change and exits non-zero by construction.
# Gating on it made the status unreachable exactly when it was needed.

def test_accepted_is_reachable_when_its_own_verify_fails(monkeypatch):
    """The defect: `accepted` could only be recorded when the fix already passed."""
    import scripts.close_finding as cf

    nodes = {"review:x:y:1": {"id": "review:x:y:1", "meta": {"verify": "exit 1"}}}
    ok, verified_by, msg = cf._run_verifications(
        ["review:x:y:1"], nodes, None, "accepted")
    assert ok, f"accepted must not be gated on its own verify: {msg}"
    rec = verified_by["review:x:y:1"]
    assert rec["exit_code"] == 1, "the real outcome must be RECORDED, not swallowed"
    assert rec["enforced"] is False


def test_fixed_still_fails_closed_on_a_failing_verify():
    """The gate that matters is unchanged — a `fixed` closure still refuses."""
    import scripts.close_finding as cf

    nodes = {"review:x:y:1": {"id": "review:x:y:1", "meta": {"verify": "exit 1"}}}
    ok, _verified_by, msg = cf._run_verifications(
        ["review:x:y:1"], nodes, None, "fixed")
    assert not ok
    assert "verify command failed" in msg


def test_a_passing_verify_records_exit_zero_under_both_statuses():
    import scripts.close_finding as cf

    nodes = {"review:x:y:1": {"id": "review:x:y:1", "meta": {"verify": "true"}}}
    for status in ("fixed", "accepted"):
        ok, verified_by, _ = cf._run_verifications(
            ["review:x:y:1"], nodes, None, status)
        assert ok and verified_by["review:x:y:1"]["exit_code"] == 0


class TestOutOfRepoArtifactAnchor:
    """A finding whose artifact lives OUTSIDE this git repository cannot be anchored to
    a commit — no commit here can contain the change (D11 Stage-13 finding
    `2026-08-01-0009:D11:N3`). `Lit-Search/` is a workspace sibling, and Pipeline
    Invariant #11 makes a primary-source cache mandatory at every Stage 13, so the
    schema's commit-or-date bar forced either a fabricated SHA or no closure. A record
    shipped citing the very commit the finding says did NOT fix it.

    Every leg drives the REAL `close()` in `--dry-run`; the tracked ledger is untouched.
    """

    #: A live finding whose only Location is under `Lit-Search/`.
    OOR_DOC = "papers/AutomatedReviews/2026-07-31-1951-internal-adversarial/D11.md"
    OOR_SECTION = "1.1"
    OOR_ARTIFACT = ("Lit-Search/Phase-6C/primary-sources/"
                    "LjungstromMortberg2024.abstract.txt")
    OOR_EVIDENCE = ("Cache Caveat block rewritten so the carve-out states the scope the "
                    "evidence was gathered at; verified by reading the file.")

    def test_a_commit_anchor_on_an_OUT_OF_REPO_artifact_is_REFUSED(self):
        """FIRES ON THE SEEDED DEFECT. This is the exact call that produced the shipped
        bad record: `--commit a683b917` against a finding whose artifact this repo does
        not track."""
        ok, msg = cf.close(doc=self.OOR_DOC, sections=[self.OOR_SECTION],
                           status="fixed", evidence=self.OOR_EVIDENCE,
                           commit="a683b917", dry_run=True)
        assert ok is False, "a structurally impossible commit anchor was accepted"
        assert "does not track" in msg and "--artifact" in msg, msg

    def test_an_IN_REPO_finding_is_NOT_blocked_by_the_guard(self):
        """The other direction, and it is the load-bearing one: the guard is narrow, so
        an ordinary in-repo closure must still pass with a plain commit anchor. A guard
        that blocked those would stop every closure in the project."""
        ok, msg = cf.close(doc=DOC, sections=[SECTION], status="fixed",
                           evidence=EVIDENCE, commit="b0f44815", dry_run=True)
        assert ok is True, msg

    def test_the_artifact_anchor_is_accepted_without_a_commit(self):
        ok, msg = cf.close(doc=self.OOR_DOC, sections=[self.OOR_SECTION],
                           status="fixed", evidence=self.OOR_EVIDENCE,
                           artifact=[self.OOR_ARTIFACT], dry_run=True)
        assert ok is True, msg

    def test_an_artifact_anchor_that_names_nothing_is_REFUSED(self):
        """The option exists to replace an anchor that proves nothing; it must not become
        one."""
        ok, msg = cf.close(doc=self.OOR_DOC, sections=[self.OOR_SECTION],
                           status="fixed", evidence=self.OOR_EVIDENCE,
                           artifact=["Lit-Search/__no_such_dir__/nope.txt"],
                           dry_run=True)
        assert ok is False and "does not resolve" in msg, msg

    def test_the_recorded_path_is_the_ON_DISK_spelling(self):
        """Review documents quote `Phase-6C` where the directory is `Phase-6c`. Both
        resolve on APFS and neither does on Linux CI, so the record must carry the
        spelling that actually exists (D11 round-4 finding 1.2)."""
        rec, why = cf._artifact_anchor([self.OOR_ARTIFACT])
        assert rec is not None, why
        assert rec["artifact_path"].startswith("Lit-Search/Phase-6c/"), (
            f"the anchor recorded the TYPED spelling {rec['artifact_path']!r} rather "
            f"than the on-disk one — a path that resolves only on a case-insensitive "
            f"filesystem is not provenance anywhere else")
        assert len(rec["artifact_sha256"]) == 64

    def test_the_hash_actually_tracks_the_file(self, tmp_path, monkeypatch):
        """A digest that does not move with the bytes is decoration."""
        import src.core.workspace as _ws
        ws = tmp_path / "ws"
        (ws / "Lit-Search" / "p").mkdir(parents=True)
        f = ws / "Lit-Search" / "p" / "a.txt"
        f.write_text("one")
        monkeypatch.setattr(_ws, "find_workspace", lambda: ws)
        first, _ = cf._artifact_anchor(["Lit-Search/p/a.txt"])
        f.write_text("two")
        second, _ = cf._artifact_anchor(["Lit-Search/p/a.txt"])
        assert first["artifact_sha256"] != second["artifact_sha256"]

    def test_no_anchor_at_all_is_still_REFUSED(self):
        ok, msg = cf.close(doc=DOC, sections=[SECTION], status="fixed",
                           evidence=EVIDENCE, dry_run=True)
        assert ok is False and "no anchor" in msg, msg
