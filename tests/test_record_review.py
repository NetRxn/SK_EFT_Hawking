"""`scripts/record_review.py` — the writer transition 2 never had (ADR-011 Phase 2).

`END_TO_END_MAP.md` §8 records the defect this closes: no code path in the repository
wrote `"green"` to any `stage*_status`, so every green in the corpus was a hand edit and
the reviewer agents that would earn one had no write path to the field they gate on.

These tests assert the REFUSALS, because a writer that only writes is not the fix — the
value is in what it declines to record. Each refusal is asserted against the specific
measured failure it prevents.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

import record_review as rr  # noqa: E402


@pytest.fixture
def bundle(tmp_path, monkeypatch):
    """A bundle whose three reviewer stages are all `pending`."""
    papers = tmp_path / "papers"
    (papers / "D1").mkdir(parents=True)
    monkeypatch.setattr(rr, "PAPERS", papers)
    monkeypatch.setattr(rr, "REPO", tmp_path)

    def write(**over):
        blob = {"bundle_target": "D1", "stage9_status": "pending",
                "stage10_status": "pending", "stage13_status": "pending"}
        blob.update(over)
        (papers / "D1" / "bundle_metadata.json").write_text(json.dumps(blob, indent=2))
    write()
    (tmp_path / "review.md").write_text("a review")
    return write


def _read(tmp_path):
    return json.loads(
        (tmp_path / "papers" / "D1" / "bundle_metadata.json").read_text())


class TestTheHappyPath:
    def test_a_stage9_verdict_is_recorded_with_its_timestamp(self, tmp_path, bundle):
        ok, msg = rr.record("D1", 9, "green", "review.md", None)
        assert ok, msg
        md = _read(tmp_path)
        assert md["stage9_status"] == "green"
        assert md["last_stage9_review"].endswith("Z")

    def test_stage13_green_after_both_prerequisites(self, tmp_path, bundle):
        bundle(stage9_status="green", stage10_status="green")
        ok, msg = rr.record("D1", 13, "green", "review.md", "full-adversarial")
        assert ok, msg
        md = _read(tmp_path)
        assert md["stage13_status"] == "green"
        assert md["stage13_review_kind"] == "full-adversarial"
        assert md["stage13_review_doc"] == "review.md"

    def test_a_non_green_stage13_verdict_needs_no_prerequisites(self, tmp_path, bundle):
        """Recording RED is how a failing review gets recorded at all — gating it
        behind green prerequisites would make the bad news unrecordable."""
        ok, msg = rr.record("D1", 13, "red", "review.md", "full-adversarial")
        assert ok, msg
        assert _read(tmp_path)["stage13_status"] == "red"


class TestTheRefusals:
    def test_stage13_green_is_refused_while_a_prerequisite_is_unfinished(
            self, tmp_path, bundle):
        """The measured failure: five bundles held a Stage-13 verdict with Stage 9 or
        10 never run. D6's was `not_started`."""
        bundle(stage9_status="not_started", stage10_status="green")
        ok, msg = rr.record("D1", 13, "green", "review.md", "full-adversarial")
        assert not ok
        assert "stage9=not_started" in msg and "BUNDLE_LIFT_PROCEDURE" in msg

    def test_BOTH_prerequisites_are_checked_not_just_one(self, tmp_path, bundle):
        """Asserted separately in both directions: a writer testing only Stage 9
        would have let D9 through, and one testing only Stage 10 would have let D7."""
        bundle(stage9_status="green", stage10_status="pending")
        assert not rr.record("D1", 13, "green", "review.md", "full-adversarial")[0]
        bundle(stage9_status="pending", stage10_status="green")
        assert not rr.record("D1", 13, "green", "review.md", "full-adversarial")[0]

    def test_a_stage13_verdict_without_a_kind_is_refused(self, tmp_path, bundle):
        ok, msg = rr.record("D1", 13, "green", "review.md", None)
        assert not ok and "--kind is required" in msg

    def test_an_attribution_sweep_does_not_earn_a_green(self, tmp_path, bundle):
        """THE D9 CASE. `review_recorded` treats any referenced document as a review,
        so a 16-anchor sweep satisfied the same guard as a full adversarial pass."""
        bundle(stage9_status="green", stage10_status="green")
        ok, msg = rr.record("D1", 13, "green", "review.md", "attribution-sweep")
        assert not ok and "does not earn a Stage-13 green" in msg

    def test_a_narrower_kind_may_still_record_a_NON_green_verdict(
            self, tmp_path, bundle):
        """The kind rule gates promotion, not recording. A section-scoped review that
        finds a blocker must be able to say so."""
        ok, msg = rr.record("D1", 13, "red", "review.md", "section-scoped")
        assert ok, msg

    def test_a_doc_that_does_not_exist_is_refused(self, tmp_path, bundle):
        ok, msg = rr.record("D1", 9, "green", "nope.md", None)
        assert not ok and "does not exist" in msg

    def test_an_absent_bundle_is_refused_not_created(self, tmp_path, bundle):
        ok, msg = rr.record("NOPE", 9, "green", "review.md", None)
        assert not ok and "no bundle_metadata.json" in msg

    def test_a_refusal_writes_NOTHING(self, tmp_path, bundle):
        """The blob must be byte-identical after a refused write — a partial write
        would leave a timestamp implying a review that was rejected."""
        p = tmp_path / "papers" / "D1" / "bundle_metadata.json"
        before = p.read_bytes()
        assert not rr.record("D1", 13, "green", "review.md", None)[0]
        assert p.read_bytes() == before


class TestSerialization:
    def test_non_ascii_in_the_blob_survives_a_write(self, tmp_path, bundle):
        """TODO-D25. The apex `claims` strings carry `§` and `—`; the default
        `ensure_ascii` re-encodes every one, turning a one-field edit into a
        several-hundred-line diff."""
        bundle(apex_theorems=[{"name": "X", "claims": "§2.1 — the thing"}])
        assert rr.record("D1", 9, "green", "review.md", None)[0]
        raw = (tmp_path / "papers" / "D1" / "bundle_metadata.json").read_text()
        assert "§2.1 — the thing" in raw
        assert "\\u00a7" not in raw
