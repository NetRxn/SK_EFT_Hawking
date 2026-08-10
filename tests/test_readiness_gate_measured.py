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


class TestTheFlagIsReadable:
    """⚠️ A write-only field fixes nothing. Round 3 found `measured` set, emitted
    into the payload, and consulted by NO consumer — including
    `paper_aggregate_state`, the function the field's own docstring names as the
    thing it was added to fix. This pins that a reader exists and discriminates."""

    def _mk(self, paper, gate, measured):
        r = rg.GateResult(gate=gate, paper=paper, priority=1)
        r.measured = measured
        return r

    def test_unmeasured_gates_are_reportable(self):
        rs = [self._mk("ZZ", "g1", False), self._mk("ZZ", "g2", True),
              self._mk("YY", "g3", False)]
        assert rg.paper_unmeasured_gates(rs, "ZZ") == ["g1"]

    def test_a_fully_measured_paper_reports_none(self):
        """The silent direction."""
        rs = [self._mk("ZZ", "g1", True), self._mk("ZZ", "g2", True)]
        assert rg.paper_unmeasured_gates(rs, "ZZ") == []

    def test_the_colour_contract_is_unchanged(self):
        """`state` stays a three-value contract — a fourth colour would break
        `check_readiness_submission_gate` and the heatmap."""
        rs = [self._mk("ZZ", "g1", False)]
        rs[0].state = "open"
        assert rg.paper_aggregate_state(rs, "ZZ") == "yellow"


# ── The half the file's docstring CLAIMED and did not test ───────────────────

#: Every evaluator that reads the draft. Deleting an evaluator's
#: `if tex is None: return _unreadable_draft(r)` guard must fail a test HERE —
#: round 3 measured that three of these (`citation_integrity`,
#: `parameter_provenance`, `numerical_freshness`) survived deletion with the whole
#: suite green, and the other four were caught only incidentally, by unrelated
#: contract tests crashing on `TypeError: 'str' in None`. An incidental crash is
#: not a guard: it fires on the shape of the code, not on the property.
#:
#: `_eval_citation_integrity` was the worst — deleting its guard silently restores
#: the exact pre-fix defect, because its `if not tex:` swallows `None` and reports
#: `'paper_draft.tex is empty'` about a file it never opened, with `measured=True`.
DRAFT_READING_EVALUATORS = [
    "_eval_citation_integrity",
    "_eval_parameter_provenance",
    "_eval_lean_proof_substance",
    "_eval_assumption_disclosure",
    "_eval_narrative_grounding",
    "_eval_production_run_health",
    "_eval_numerical_freshness",
]


class TestEveryDraftReadingEvaluatorDeclaresUnmeasured:
    @pytest.fixture
    def unreadable(self, monkeypatch, tmp_path):
        """A GraphIndex whose `paper_tex` always reports the draft unreadable."""
        monkeypatch.setattr(rg, "PAPERS_DIR", tmp_path)
        # A real GraphIndex over an empty graph: the evaluators touch `by_type`,
        # `out_edges` and friends before they reach the draft, so a hand-stubbed
        # object tests the stub rather than the guard.
        idx = rg.GraphIndex({"nodes": [], "links": []})
        monkeypatch.setattr(type(idx), "paper_tex", lambda self, k: None,
                            raising=False)
        return idx

    @pytest.mark.parametrize("name", DRAFT_READING_EVALUATORS)
    def test_an_unreadable_draft_is_UNMEASURED(self, name, unreadable):
        fn = getattr(rg, name)
        r = fn({"id": "paper:ZZ", "meta": {"paper_key": "ZZ"}}, unreadable)
        assert r.measured is False, (
            f"{name} read nothing and reported measured=True — the gate is "
            f"indistinguishable from one that genuinely ran")
        assert r.state == "open", "the state contract is unchanged"

    @pytest.mark.parametrize("name", DRAFT_READING_EVALUATORS)
    def test_a_readable_draft_is_MEASURED(self, name, unreadable, monkeypatch):
        """The silent direction. Without this, `measured=False` everywhere passes
        the test above while carrying no information."""
        monkeypatch.setattr(type(unreadable), "paper_tex",
                            lambda self, k: "\\begin{abstract}x\\end{abstract}\n"
                                            "\\begin{document}body\\end{document}",
                            raising=False)
        fn = getattr(rg, name)
        r = fn({"id": "paper:ZZ", "meta": {"paper_key": "ZZ"}}, unreadable)
        assert r.measured is True, (
            f"{name} reported UNMEASURED on a draft it could read")


class TestTheReaderHasAProductionCaller:
    """⚠️ `paper_unmeasured_gates` was added to give `GateResult.measured` a reader,
    and for one commit its only caller was the test asserting it exists.

    ⚠️⚠️ **AND THE FIRST VERSION OF THIS CLASS WAS ITSELF VACUOUS.** It asserted
    `"paper_unmeasured_gates" in inspect.getsource(...)` — and the function body
    contains a COMMENT naming `paper_unmeasured_gates`, so the import and the call
    could both be deleted and these tests still passed. Mutation-proven by the
    closure reviewer and reproduced here before rewriting. It is the identical
    raw-source-includes-comments evasion that was CORRECTLY fixed in
    `test_ratchets_have_zero_headroom.py` in the very same commit, a hundred lines
    away — this branch's signature defect, committed inside the fix for it.

    So this asserts BEHAVIOUR, not source text: drive the real extractor with a
    gate that measured nothing and require the warning to reach the log."""

    def _drive(self, monkeypatch, caplog, measured: bool):
        import logging
        import build_graph

        r = rg.GateResult(gate="citation_integrity", paper="ZZ", priority=1)
        r.state, r.measured = "open", measured
        # ⚠️ Only the GATE INPUT is stubbed, and deliberately so. An earlier version
        # also tried to stub `extract_all_nodes_without_gates`, which DOES NOT EXIST —
        # `raising=False` silently created an unused attribute, so the test read as
        # isolated while running every real extractor anyway. A patch that patches
        # nothing is a comment with a syntax error. The real extractors do run here
        # (a couple of seconds); that is honest, and the stubbed evaluator discards
        # their output.
        import readiness_gates
        monkeypatch.setattr(readiness_gates, "evaluate_all_gates",
                            lambda _g: [r], raising=False)
        with caplog.at_level(logging.WARNING):
            build_graph.extract_readiness_gate_nodes()
        return caplog.text

    def test_an_unmeasured_gate_reaches_the_log(self, monkeypatch, caplog):
        text = self._drive(monkeypatch, caplog, measured=False)
        assert "UNMEASURED" in text and "ZZ" in text, (
            "the only reader of GateResult.measured produced no output for a gate "
            "that measured nothing — the field is write-only again")

    def test_a_measured_gate_is_SILENT(self, monkeypatch, caplog):
        """The direction that makes the test above mean something: a reader that
        warns unconditionally carries no information."""
        text = self._drive(monkeypatch, caplog, measured=True)
        assert "UNMEASURED" not in text

    def test_the_warning_does_not_change_the_state(self, monkeypatch, caplog):
        """The distinction is reported BESIDE the colour, never folded into it —
        `GateState` is a three-value contract read by other consumers."""
        import build_graph
        r = rg.GateResult(gate="g", paper="ZZ", priority=1)
        r.state, r.measured = "open", False
        assert r.to_node_payload()["meta"]["state"] == "open"
        assert r.to_node_payload()["meta"]["measured"] is False
