"""The cannot-measure pattern in the READINESS layer — QA_QI_INFRASTRUCTURE_MAP §7.

`tests/test_cannot_measure_baseline.py` ratchets the population inside the 59
validation checks. It structurally cannot see these two, because neither returns a
`CheckResult` — and both were live instances of the same defect:

1. **`readiness_gates.evaluate_all_gates`** wrapped every evaluator in `try/except`
   and set `state='open'` on failure. `paper_aggregate_state` maps `open` to YELLOW
   and only `blocked` to RED, so an evaluator that CRASHED rendered as a mild
   advisory. Measured before the fix: 0 exceptions across 704 evaluations (64 papers
   × 11 gates) — so the repair is a no-op on the current tree and guards against a
   NEW evaluator bug, which is exactly when a silent downgrade does most damage.

2. **`bundle_readiness._blocked_p1_gates_by_paper`** returned `{}` on any exception,
   documented as *"callers treat that as 'no downgrade'"*. `{}` and "could not
   compute" are different facts sharing one value, so a failure inside
   `build_graph_json` or a new evaluator bug silently removed the P1-gate downgrade
   and a bundle could render 🟢 GREEN — through the error path of the function added
   to stop exactly that.

MUTATION-VERIFIED 2026-08-04, each independently:
  * restore `state='open'` in the evaluator handler   -> test_evaluator_crash_blocks FAILS
  * restore `return {}` in the downgrade helper       -> test_uncomputable_gates_return_none FAILS
  * drop the `blocked_p1 is None` branch in aggregate -> test_green_withheld_when_unverified FAILS
Clean negative control: unmutated tree, all pass.
"""
from __future__ import annotations

import sys
from pathlib import Path

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))

import bundle_readiness as br  # noqa: E402
import readiness_gates as rg  # noqa: E402


class TestEvaluatorCrashIsBlocking:

    def test_evaluator_crash_blocks(self, monkeypatch):
        """FIRES on a seeded defect — an evaluator that raises must BLOCK, not advise."""
        def _boom(paper, idx):
            raise RuntimeError("seeded evaluator defect")

        monkeypatch.setattr(rg, "GATES", [("Exploding", 1, _boom)])

        class _Idx:
            def papers(self):
                return [{"id": "paper:X", "meta": {}, "name": "X"}]

        monkeypatch.setattr(rg, "GraphIndex", lambda graph: _Idx())
        results = rg.evaluate_all_gates({"nodes": [], "links": []})

        assert len(results) == 1
        assert results[0].state == "blocked", (
            f"a crashed evaluator produced state={results[0].state!r}. "
            "`paper_aggregate_state` maps anything but 'blocked' to YELLOW, so the "
            "paper would read as a mild advisory rather than unverified."
        )
        assert rg.paper_aggregate_state(results, "X") == "red"

    def test_a_healthy_evaluator_is_untouched(self, monkeypatch):
        """SILENT on correct data — the handler must not colour normal results."""
        def _ok(paper, idx):
            return rg.GateResult(gate="Fine", paper="X", priority=1, state="passed")

        monkeypatch.setattr(rg, "GATES", [("Fine", 1, _ok)])

        class _Idx:
            def papers(self):
                return [{"id": "paper:X", "meta": {}, "name": "X"}]

        monkeypatch.setattr(rg, "GraphIndex", lambda graph: _Idx())
        results = rg.evaluate_all_gates({"nodes": [], "links": []})
        assert results[0].state == "passed"
        assert rg.paper_aggregate_state(results, "X") == "green"


class TestUncomputableGatesWithholdGreen:

    def test_uncomputable_gates_return_none(self, monkeypatch):
        """FIRES — an exception must yield None ("unknown"), never {} ("none blocked")."""
        import readiness_gates
        monkeypatch.setattr(readiness_gates, "evaluate_all_gates",
                            lambda g: (_ for _ in ()).throw(RuntimeError("graph down")))
        out = br._blocked_p1_gates_by_paper()
        assert out is None, (
            f"got {out!r}. `{{}}` means 'no P1 gate is blocked' and licenses GREEN; "
            "'could not compute' must be a distinct value or the downgrade vanishes."
        )

    def test_healthy_path_returns_a_mapping(self, monkeypatch):
        """SILENT — the normal path still returns a dict, so callers behave as before."""
        import readiness_gates
        monkeypatch.setattr(
            readiness_gates, "evaluate_all_gates",
            lambda g: [readiness_gates.GateResult(gate="G", paper="D1",
                                                  priority=1, state="blocked")])
        monkeypatch.setattr(br, "_blocked_p1_gates_by_paper",
                            br._blocked_p1_gates_by_paper)
        out = br._blocked_p1_gates_by_paper()
        assert isinstance(out, dict) and out.get("D1") == ["G"]

    def test_green_withheld_when_unverified(self, monkeypatch):
        """FIRES — a bundle with zero findings must NOT render GREEN while the P1
        gates are unknown. This is the false-GREEN the helper exists to prevent."""
        monkeypatch.setattr(br, "_blocked_p1_gates_by_paper", lambda: None)
        monkeypatch.setattr(br, "_VALID_BUNDLE_TARGETS", {"D1"})
        monkeypatch.setattr(br, "resolve_stage13_reviews",
                            lambda *, backfill: {"D1": {"date": "2026-01-01"}})

        agg = br.aggregate_by_bundle({}, {}, {"D1": {"date": "2026-01-01"}})

        assert agg["D1"]["readiness"] == "YELLOW", (
            f"bundle rendered {agg['D1']['readiness']} with the P1 gates unverified. "
            "Zero known blockers is not evidence of readiness when the gate "
            "computation failed."
        )
        assert "UNVERIFIED" in agg["D1"]["readiness_display"]


class TestStage13EvidenceKindWithholdsGreen:
    """ADR-011 Phase 2d — a RECORDED review is not necessarily a review of the right
    SCOPE.

    `review_recorded` is satisfied by ANY document referenced by
    `stage13_review_doc`, so a targeted attribution sweep counted exactly as a full
    fresh-context adversarial pass. That is how D9 — the portfolio's only GREEN —
    reached GREEN with its Stage 10 never run. Visible in production today: D1, D2
    and D3 all cite `docs/audits/stage13_attribution_sweep_2026-06-10.md`.

    Same shape as the two withholding rules above it: NOT MEASURED must not render as
    measured-and-fine.
    """

    def _agg(self, monkeypatch, rev, *, claims_review=True, tmp_path=None):
        monkeypatch.setattr(br, "_blocked_p1_gates_by_paper", lambda: {})
        monkeypatch.setattr(br, "_VALID_BUNDLE_TARGETS", {"D1"})
        monkeypatch.setattr(br, "resolve_stage13_reviews", lambda *, backfill: {"D1": rev})
        if tmp_path is not None:
            d = tmp_path / "D1"
            d.mkdir(parents=True, exist_ok=True)
            if claims_review:
                (d / "claims_review.json").write_text("{}")
            monkeypatch.setattr(br, "_bundle_metadata_path",
                                lambda b: tmp_path / b / "bundle_metadata.json")
        return br.aggregate_by_bundle({}, {}, {"D1": rev})["D1"]

    def test_a_full_adversarial_review_still_earns_green(self, monkeypatch, tmp_path):
        """SILENT ON CORRECT DATA — the rule must not make GREEN unreachable."""
        out = self._agg(monkeypatch,
                        {"date": "2026-01-01", "kind": "full-adversarial"},
                        tmp_path=tmp_path)
        assert out["readiness"] == "GREEN", out["readiness_display"]

    def test_an_attribution_sweep_does_not(self, monkeypatch, tmp_path):
        out = self._agg(monkeypatch,
                        {"date": "2026-01-01", "kind": "attribution-sweep"},
                        tmp_path=tmp_path)
        assert out["readiness"] == "YELLOW"
        assert "UNVERIFIED" in out["readiness_display"]
        assert "attribution-sweep" in out["readiness_display"], "name the evidence"

    def test_an_UNRECORDED_kind_does_not(self, monkeypatch, tmp_path):
        """THE D9 CASE, exactly. Absent is UNKNOWN, not sufficient — every bundle
        predating the field has no kind, and 'we never wrote it down' is not
        evidence that the review was thorough."""
        out = self._agg(monkeypatch, {"date": "2026-01-01"}, tmp_path=tmp_path)
        assert out["readiness"] == "YELLOW"
        assert "unrecorded" in out["readiness_display"]

    def test_a_missing_claims_review_withholds_green(self, monkeypatch, tmp_path):
        """Stage 10 leaves an artifact. No `claims_review.json` means Stage 10 did
        not run — measured 2026-08-01 on D6 and D9, both of which had none."""
        out = self._agg(monkeypatch,
                        {"date": "2026-01-01", "kind": "full-adversarial"},
                        claims_review=False, tmp_path=tmp_path)
        assert out["readiness"] == "YELLOW"
        assert "no claims_review.json" in out["readiness_display"]

    def test_the_kind_gate_matches_the_writers(self):
        """ONE rule, two enforcement points. `record_review.py` refuses to WRITE a
        green on insufficient evidence and this layer refuses to RENDER one; if the
        two sets drifted, a verdict the writer rejected could still show GREEN."""
        import record_review as rr
        assert br._KINDS_SUFFICIENT_FOR_GREEN == rr.KINDS_SUFFICIENT_FOR_GREEN
