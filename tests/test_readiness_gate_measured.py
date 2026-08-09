"""A gate that could not read its draft is UNMEASURED, not merely outstanding.

⚠️ `GateState` has no cannot-measure value, and `state='open'` was carrying two
meanings: "measured, and genuinely outstanding" and "the evaluator read nothing".
`paper_aggregate_state` maps both to YELLOW, so at every consumer — including the
graph payload — a paper whose draft could not be opened was indistinguishable
from one with real work left.

Worse, `GraphIndex.paper_tex` returned `''` for missing, unreadable and
genuinely-empty alike, and three evaluators turned that into a positive claim
about a file they never opened: "no inline unit-bearing literals in body prose",
"the draft has no abstract block". A false statement about the draft, emitted as
the gate's own evidence.

This pins both halves: `paper_tex` returns None on failure, and every evaluator
that consumes it declares `measured=False` rather than inventing a verdict.
"""
from __future__ import annotations

import pathlib
import sys

import pytest

REPO = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "scripts"))

import readiness_gates as rg  # noqa: E402


class TestPaperTexDistinguishesUnreadableFromEmpty:
    def test_an_unreadable_draft_reads_None(self, monkeypatch, tmp_path):
        monkeypatch.setattr(rg, "PAPERS_DIR", tmp_path)
        idx = rg.GraphIndex.__new__(rg.GraphIndex)
        assert idx.paper_tex("NoSuchBundle") is None

    def test_a_real_draft_still_reads_its_text(self, monkeypatch, tmp_path):
        """The silent direction — None everywhere would pass the test above."""
        monkeypatch.setattr(rg, "PAPERS_DIR", tmp_path)
        d = tmp_path / "ZZ"
        d.mkdir()
        (d / "paper_draft.tex").write_text("\\begin{abstract}hi\\end{abstract}")
        idx = rg.GraphIndex.__new__(rg.GraphIndex)
        assert "abstract" in idx.paper_tex("ZZ")

    def test_an_EMPTY_draft_is_not_the_same_as_an_unreadable_one(
            self, monkeypatch, tmp_path):
        """The distinction the `''` return destroyed."""
        monkeypatch.setattr(rg, "PAPERS_DIR", tmp_path)
        d = tmp_path / "ZZ"
        d.mkdir()
        (d / "paper_draft.tex").write_text("")
        idx = rg.GraphIndex.__new__(rg.GraphIndex)
        assert idx.paper_tex("ZZ") == ""      # readable, and empty
        assert idx.paper_tex("Missing") is None


class TestGateResultCarriesMeasured:
    def test_default_is_measured(self):
        r = rg.GateResult(gate="g", paper="ZZ", priority=1)
        assert r.measured is True

    def test_unreadable_draft_helper_marks_it_unmeasured(self):
        r = rg.GateResult(gate="g", paper="ZZ", priority=1)
        out = rg._unreadable_draft(r)
        assert out.measured is False
        assert out.state == "open", "state contract is unchanged — measured is additive"
        assert "not readable" in out.notes

    def test_measured_reaches_the_graph_payload(self):
        """A consumer that cannot see the flag is a consumer the flag does not
        help; the payload is how the dashboard and graph read gates."""
        r = rg.GateResult(gate="g", paper="ZZ", priority=1)
        r.measured = False
        assert r.to_node_payload()["meta"]["measured"] is False

    def test_state_is_still_one_of_the_five(self):
        """⚠️ NOT a sixth GateState. ADR-009 §Deferred item 4 declined
        `UNEVALUATED` on the state axis because consumers break on a new value;
        this asserts the remedy stayed additive."""
        import typing
        assert set(typing.get_args(rg.GateState)) == {
            "open", "in-review", "passed", "blocked", "needs-recheck"}
