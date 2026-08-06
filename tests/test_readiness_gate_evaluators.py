"""Direct tests for the 11 readiness-gate evaluators — PR-review pass 2, R6-M8.

WHY THIS FILE EXISTS
--------------------
`scripts/readiness_gates.py` is **804 LOC containing 11 functions that decide
whether a paper may be submitted**, and reviewer R6 measured its direct test
coverage: `rg '_eval_' tests/` returned **exactly one hit, a docstring mention.**
The only test touching this module patched `GATES` to a toy that raises.

That is the branch's coverage mismatch in one file: 2,446 test LOC guard 537 LOC
of validation plumbing, while the code that gates submission had none.

WHAT IS ASSERTED HERE, AND WHY IT IS GENERIC
--------------------------------------------
Hand-writing eleven bespoke fixtures would test my reading of each evaluator as
much as the evaluator. Instead these assert the properties that must hold for
ALL of them, and that this audit has repeatedly found violated elsewhere:

1. **Absence must not be success.** An evaluator handed a paper with no
   supporting evidence in the graph must not return `passed`. A gate that passes
   because it found nothing to check is "absence of measurement rendered as
   success" — the defect this whole audit exists to close — sitting directly on
   the submission decision.
2. **Identity is preserved.** Each returns the gate name and paper key it was
   asked about; a mismatch silently attributes a verdict to the wrong paper.
3. **A crash is BLOCKED, not open.** `paper_aggregate_state` maps `open` to
   YELLOW and only `blocked` to RED, so an evaluator that raised used to render
   as a mild advisory.
4. **The roster is ratcheted** — a new gate cannot land without a test.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))
sys.path.insert(0, str(SK_ROOT))

import readiness_gates as rg  # noqa: E402


def _empty_graph(paper_id="paper:paper1_sk_eft"):
    """A graph containing ONE Paper node and nothing else — the 'no evidence'
    case every evaluator must refuse to pass."""
    return {"nodes": [{"id": paper_id, "type": "Paper", "name": "paper1_sk_eft",
                       "meta": {}}],
            "links": []}


def _paper_and_index(graph=None):
    graph = graph or _empty_graph()
    idx = rg.GraphIndex(graph)
    paper = next(p for p in idx.papers())
    return paper, idx


ALL_EVALUATORS = [(name, prio, fn) for name, prio, fn in rg.GATES]


class TestEveryEvaluatorHonoursTheContract:

    @pytest.mark.parametrize("name,prio,fn", ALL_EVALUATORS,
                             ids=[n for n, _, _ in ALL_EVALUATORS])
    def test_a_vacuous_PASS_is_LABELLED_as_vacuous(self, name, prio, fn):
        """⚠️ MEASURED, then narrowed — and the narrowing is the honest part.

        Given a paper with NO evidence in the graph at all, **9 of the 11 gates
        return `passed`**. My first draft asserted `state != "passed"`, i.e. that
        an empty population must never satisfy a submission gate. Reading the
        code before trusting my own test: it is DELIBERATE and explicit —

            if not param_ids:
                r.state = 'passed'
                r.notes = 'no parameter dependencies declared'

        — a considered decision (a paper that genuinely uses no parameters does
        pass ParameterProvenance), not an oversight. Asserting my preferred
        semantics would have imposed a redefinition of 11 submission gates that I
        had not validated, on a corpus where 61 papers are already red.

        So this asserts the property that IS defensible and is what makes the
        decision reviewable: **a vacuous pass must SAY it is vacuous.** A silent
        one is indistinguishable from a satisfied one.

        The residual risk is recorded as a finding, not silently pinned here:
        these gates cannot distinguish "this paper declares no parameters" from
        "the extraction failed to link them", so a paper missing from the graph
        reads as submission-ready. Tracked in
        `docs/audits/2026-08-05-pr-review-2/FINDINGS_REGISTER_PASS2.md`.
        """
        paper, idx = _paper_and_index()
        r = fn(paper, idx)
        if r.state == "passed":
            assert r.notes or r.evidence, (
                f"{name} PASSED a paper with no evidence in the graph and said "
                f"nothing about why. A vacuous pass that does not announce "
                f"itself is indistinguishable from a satisfied gate.")

    @pytest.mark.parametrize("name,prio,fn", ALL_EVALUATORS,
                             ids=[n for n, _, _ in ALL_EVALUATORS])
    def test_it_returns_a_well_formed_result_for_the_paper_it_was_asked_about(
            self, name, prio, fn):
        paper, idx = _paper_and_index()
        r = fn(paper, idx)
        assert isinstance(r, rg.GateResult)
        assert r.gate == name, f"{name} returned a result labelled {r.gate!r}"
        assert r.paper == "paper1_sk_eft", (
            f"{name} attributed its verdict to {r.paper!r}, not the paper passed in")
        assert r.priority == prio
        assert r.state in ("open", "passed", "blocked")

    @pytest.mark.parametrize("name,prio,fn", ALL_EVALUATORS,
                             ids=[n for n, _, _ in ALL_EVALUATORS])
    def test_a_blocked_result_says_why(self, name, prio, fn):
        """A gate that blocks without naming a blocker is unactionable."""
        paper, idx = _paper_and_index()
        r = fn(paper, idx)
        if r.state == "blocked":
            assert r.blockers or r.notes, (
                f"{name} BLOCKED with no blockers and no notes — the reader "
                f"cannot tell what to fix")


class TestCrashHandling:
    """`evaluate_all_gates` must map an evaluator exception to BLOCKED. `open`
    renders YELLOW and only `blocked` renders RED, so a crashing gate used to
    read as a mild advisory."""

    def test_a_raising_evaluator_becomes_blocked_not_open(self, monkeypatch):
        def boom(paper, idx):
            raise RuntimeError("seeded crash")

        monkeypatch.setattr(rg, "GATES", [("ExplodingGate", 1, boom)])
        results = rg.evaluate_all_gates(_empty_graph())
        assert len(results) == 1
        assert results[0].state == "blocked", (
            "a gate evaluator that RAISED did not render as blocked; it would "
            "show YELLOW (advisory) rather than RED on the readiness heatmap")
        assert results[0].blockers or results[0].notes


class TestGateRosterIsRatcheted:

    def test_all_eleven_gates_are_exercised(self):
        """A new gate cannot land untested: it is parametrized from `GATES`
        itself, so this asserts the roster size the reviewers measured."""
        assert len(ALL_EVALUATORS) == 11, (
            f"GATES now has {len(ALL_EVALUATORS)} entries, not 11. The contract "
            f"tests above parametrize from GATES so they cover it automatically "
            f"— update this count deliberately, and add targeted cases for the "
            f"new gate's actual blocking condition.")

    def test_the_priority_split_is_what_the_submission_gate_assumes(self):
        p1 = [n for n, prio, _ in ALL_EVALUATORS if prio == 1]
        p2 = [n for n, prio, _ in ALL_EVALUATORS if prio == 2]
        assert len(p1) == 8 and len(p2) == 3, (
            f"P1/P2 split changed to {len(p1)}/{len(p2)}. "
            f"`readiness_submission_gate` blocks on P1 only, so moving a gate "
            f"between tiers changes what can ship.")


class TestVacuousPassesAreCorroborated:
    """⚠️ Operator ruling, 2026-08-05: a vacuous pass is right when the paper
    genuinely *carries nothing the gate checks*, and wrong when "there's a
    predictable thing that should be working that's being skipped" — because this
    infrastructure exists so that **a referee's concern is never something the
    author is left to discover unaided.**

    Applying that: of the four gates with an explicit empty-population PASS,
    `CitationIntegrity` and `AssumptionDisclosure` already cross-check the paper's
    own `.tex` (so their empty case is corroborated *not applicable*).
    `ParameterProvenance` and `NarrativeGrounding` did not — their populations come
    from GRAPH edges, so empty meant either "nothing to check" or "extraction
    failed", and they passed either way.

    MEASURED after corroborating: **17 of 64 papers** (D1, D3, D4, D5, E1, E2, …)
    were passing `ParameterProvenance` vacuously while their drafts carry
    unit-bearing numerical literals; they now read NOT ESTABLISHED (`open`). **41**
    are genuinely not-applicable and still pass. Zero papers changed colour — the
    aggregate stayed 0 green / 3 yellow / 61 red and `readiness_verdicts_agree`
    still passes — so this is strictly more information, not a new alarm.

    ⚠️ My first measurement of this said **58**, and it was an artifact:
    `find_inline_numerical_literals` returns `(stripped_text, matches)` — a 2-tuple,
    always truthy — so the branch fired for every paper regardless of content. The
    test `test_a_draft_with_no_numbers_still_passes_as_NOT_APPLICABLE` caught it.
    """

    def _paper(self, key="paper1_sk_eft"):
        return {"id": f"paper:{key}", "type": "Paper", "name": key, "meta": {}}

    def _idx_with_tex(self, tex, monkeypatch):
        idx = rg.GraphIndex(_empty_graph())
        monkeypatch.setattr(type(idx), "paper_tex", lambda self, k: tex, raising=False)
        return idx

    def test_numbers_with_no_parameter_edges_is_NOT_ESTABLISHED(self, monkeypatch):
        """FIRES ON THE DEFECT: a draft carrying unit-bearing literals with zero
        parameter edges must not read as provenance-clean."""
        idx = self._idx_with_tex(r"The condensate density is $1.2 \times 10^{14}$ cm$^{-3}$ "
                                 r"and the temperature 50 nK.", monkeypatch)
        r = rg._eval_parameter_provenance(self._paper(), idx)
        assert r.state == "open", (
            f"a draft with unit-bearing numbers and NO parameter edges reported "
            f"{r.state!r} — the gate verified nothing and said so to nobody")
        assert "NOT ESTABLISHED" in r.notes

    def test_a_draft_with_no_numbers_still_passes_as_NOT_APPLICABLE(self, monkeypatch):
        """SILENT ON CORRECT DATA — the operator's "carries nothing the gate
        checks" case. A genuinely parameter-free paper must not be nagged."""
        idx = self._idx_with_tex("A purely formal note with no measured quantities.",
                                 monkeypatch)
        r = rg._eval_parameter_provenance(self._paper(), idx)
        assert r.state == "passed"
        assert "no inline unit-bearing literals" in r.notes

    def test_narrative_grounding_surfaces_an_unextracted_abstract(self, monkeypatch):
        """A draft WITH an abstract but zero ProseClaim nodes means prose
        extraction never ran for it — the gate examined nothing."""
        idx = self._idx_with_tex(r"\begin{abstract}We show a large effect.\end{abstract}",
                                 monkeypatch)
        r = rg._eval_narrative_grounding(self._paper(), idx)
        assert r.state == "open"
        assert "NOT ESTABLISHED" in r.notes

    def test_narrative_grounding_passes_when_there_is_no_abstract(self, monkeypatch):
        idx = self._idx_with_tex("No abstract block here.", monkeypatch)
        r = rg._eval_narrative_grounding(self._paper(), idx)
        assert r.state == "passed"

    def test_the_corroborated_gates_read_the_draft(self):
        """Structural backstop against the production source: both gates must
        actually consult `paper_tex`. A behavioural test using a stubbed index
        stays green even if the production call is removed."""
        src = (SK_ROOT / "scripts" / "readiness_gates.py").read_text()
        for fn in ("_eval_parameter_provenance", "_eval_narrative_grounding"):
            body = src.split(f"def {fn}", 1)[1].split("\ndef ", 1)[0]
            assert "paper_tex" in body, (
                f"{fn} no longer cross-checks the draft — its empty-population "
                f"PASS is uncorroborated again, and cannot tell 'not applicable' "
                f"from 'extraction failed'")
