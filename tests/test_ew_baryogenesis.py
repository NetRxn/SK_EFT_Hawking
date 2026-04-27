"""Phase 6c Wave 2: tests for the EW baryogenesis ↔ chirality wall bridge.

Mirrors ``lean/SKEFTHawking/EWBaryogenesisChiralityWall.lean``. Validates:
- sphaleron suppression structural form (positivity, ≤ 1 in broken phase)
- chirality-wall predicate at SM-no-ν_R (wall intact) + SM+3ν_R (wall cracks)
- compound EWBG viability under {wall intact, crossover} verdict
- numerical anchor: SM m_H / KLRS-threshold > 1.5
- structured SM verdict: doubly forbidden under H_KLRS
"""

from __future__ import annotations

import math

import pytest

from src.core.constants import EW_PARAMS, EWBG_PARAMS
from src.core.formulas import (
    chirality_wall_blocks_ewbg,
    ewbg_viable,
    sphaleron_suppression,
)
from src.ew_baryogenesis import (
    sm_ewbg_verdict,
    sm_no_nu_R_z16_anomaly,
    sm_with_3nu_R_z16_anomaly,
    sphaleron_decoupling_threshold,
    sphalerons_decoupled,
    wall_cracked,
    wall_intact,
)


# ════════════════════════════════════════════════════════════════════
# §1: Sphaleron suppression
# ════════════════════════════════════════════════════════════════════


class TestSphaleronSuppression:
    def test_positive(self):
        """Lean: sphaleronSuppression_pos."""
        assert sphaleron_suppression(100.0, 100.0) > 0
        assert sphaleron_suppression(0.0, 100.0) == pytest.approx(1.0)
        assert sphaleron_suppression(1000.0, 100.0) > 0  # exp(-10) ≈ 4.5e-5

    def test_le_one_in_broken_phase(self):
        """Lean: sphaleronSuppression_le_one (v/T ≥ 0)."""
        for v, T in [(50.0, 100.0), (100.0, 100.0), (200.0, 100.0)]:
            assert sphaleron_suppression(v, T) <= 1.0

    def test_decreases_with_v(self):
        """Larger v at fixed T → stronger suppression."""
        assert sphaleron_suppression(200.0, 100.0) < sphaleron_suppression(100.0, 100.0)

    def test_decoupling_threshold_one(self):
        """Cohen-Kaplan-Nelson: threshold = 1.0."""
        assert sphaleron_decoupling_threshold() == pytest.approx(1.0)

    def test_decoupling_predicate(self):
        """Lean: SphaleronsDecoupled."""
        # v=200, T=100 → v/T = 2 > 1, decoupled
        assert sphalerons_decoupled(200.0, 100.0)
        # v=50, T=100 → v/T = 0.5 < 1, not decoupled
        assert not sphalerons_decoupled(50.0, 100.0)

    def test_decoupling_at_threshold(self):
        """At v/T = 1, sphalerons are *not* strictly decoupled (strict >)."""
        assert not sphalerons_decoupled(100.0, 100.0)


# ════════════════════════════════════════════════════════════════════
# §2: Chirality-wall predicate
# ════════════════════════════════════════════════════════════════════


class TestChiralityWall:
    def test_sm_no_nu_R_wall_intact(self):
        """Lean: sm_no_nu_R_wall_intact (45 ≡ 13 mod 16, ≠ 0)."""
        a = sm_no_nu_R_z16_anomaly()
        assert a == 13
        assert wall_intact(a)
        assert not wall_cracked(a)
        assert chirality_wall_blocks_ewbg(a)

    def test_sm_with_3nu_R_wall_cracks(self):
        """Lean: sm_with_3nu_R_wall_cracks (48 ≡ 0 mod 16)."""
        a = sm_with_3nu_R_z16_anomaly()
        assert a == 0
        assert wall_cracked(a)
        assert not wall_intact(a)
        assert not chirality_wall_blocks_ewbg(a)

    def test_canonical_representative_45_eq_13(self):
        """45 mod 16 = 13 ≡ -3 (sm_no_nu_R_anomaly_eq_neg_three bridge)."""
        assert 45 % 16 == 13
        assert chirality_wall_blocks_ewbg(45) == chirality_wall_blocks_ewbg(13)

    def test_chirality_wall_decidable(self):
        """Wall is intact OR cracked, never both (wall_intact_or_cracked)."""
        for a in range(16):
            intact = wall_intact(a)
            cracked = wall_cracked(a)
            assert intact != cracked  # exactly one


# ════════════════════════════════════════════════════════════════════
# §3: Compound EWBG viability predicate
# ════════════════════════════════════════════════════════════════════


SM_BENCH = dict(E=0.01, mu_sq=7744.0, lam=0.13, c_T=0.4)


class TestEWBGViability:
    def test_intact_wall_blocks_ewbg(self):
        """Lean: ewbg_forbidden_if_wall_intact."""
        # SM-no-ν_R: wall intact → never viable, regardless of transition
        for E in [0.0, 0.01, 0.5]:
            params = {**SM_BENCH, 'E': E}
            assert not ewbg_viable(13, **params)

    def test_crossover_blocks_ewbg(self):
        """Lean: ewbg_forbidden_if_transition_crossover.
        With cracked wall (anomaly = 0) BUT crossover (E = 0):
        EWBG is still blocked.
        """
        crossover_params = {**SM_BENCH, 'E': 0.0}
        assert not ewbg_viable(0, **crossover_params)
        assert not ewbg_viable(48, **crossover_params)

    def test_first_order_strong_with_cracked_wall(self):
        """Wall cracks AND first-order strong → viable."""
        # Need E > threshold * lam * T_c
        # T_c = sqrt(7744 / 0.4) = sqrt(19360) ≈ 139.14
        # threshold * lam * T_c = 1.0 * 0.13 * 139.14 ≈ 18.09
        # So choose E > 18.09 to make it viable
        strong_first_order = {**SM_BENCH, 'E': 25.0}
        assert ewbg_viable(0, **strong_first_order)
        assert ewbg_viable(48, **strong_first_order)
        # But SM-no-ν_R wall still blocks
        assert not ewbg_viable(13, **strong_first_order)

    def test_strict_lo_sm_benchmark_not_strong_enough(self):
        """SM benchmark E=0.01 is first-order at LO but below sphaleron-
        decoupling threshold (E = 0.01 << λ·T_c ≈ 18). EWBG still fails."""
        # Even with cracked wall, the SM benchmark E=0.01 is too weak
        assert not ewbg_viable(0, **SM_BENCH)
        assert not ewbg_viable(48, **SM_BENCH)


# ════════════════════════════════════════════════════════════════════
# §4: Quantitative anchors (KLRS overshoot)
# ════════════════════════════════════════════════════════════════════


class TestKLRSOvershoot:
    def test_sm_m_h_exceeds_klrs_threshold(self):
        """Lean: sm_klrs_overshoot_ratio_gt_threshold.
        SM m_H = 125.20 GeV, KLRS threshold = 72.4 GeV.
        Ratio > 1.5.
        """
        m_h = EW_PARAMS['M_H_GEV']
        m_h_klrs = EWBG_PARAMS['KLRS_M_H_CROSSOVER_THRESHOLD_GEV']
        assert m_h > m_h_klrs
        assert m_h / m_h_klrs > 1.5

    def test_overshoot_ratio_exact(self):
        """The overshoot ratio = 125.20/72.4 ≈ 1.729."""
        ratio = EWBG_PARAMS['M_H_OVERSHOOT_RATIO']
        assert ratio == pytest.approx(125.20 / 72.4)
        assert ratio > 1.7

    def test_klrs_uncertainty_below_overshoot(self):
        """The KLRS uncertainty (1.7 GeV) is much smaller than the
        overshoot (125.20 - 72.4 = 52.8 GeV)."""
        sigma = EWBG_PARAMS['KLRS_M_H_CROSSOVER_UNCERTAINTY_GEV']
        overshoot = EW_PARAMS['M_H_GEV'] - EWBG_PARAMS['KLRS_M_H_CROSSOVER_THRESHOLD_GEV']
        assert overshoot > 30 * sigma  # SM is many sigma above threshold


# ════════════════════════════════════════════════════════════════════
# §5: SM EWBG verdict — the punchline
# ════════════════════════════════════════════════════════════════════


class TestSMEWBGVerdict:
    def test_sm_no_nu_R_blocked(self):
        """Lean: sm_no_nu_R_ewbg_blocked."""
        verdict = sm_ewbg_verdict(sm_full_is_crossover=True)
        assert verdict.sm_no_nu_R_wall_intact
        assert verdict.sm_no_nu_R_ewbg_blocked

    def test_sm_with_3nu_R_wall_cracks_but_klrs_blocks(self):
        """Lean: sm_with_3nu_R_ewbg_forbidden_under_klrs."""
        verdict = sm_ewbg_verdict(sm_full_is_crossover=True)
        assert verdict.sm_with_3nu_R_wall_cracks
        assert not verdict.sm_with_3nu_R_ewbg_under_klrs

    def test_doubly_forbidden(self):
        """Lean: sm_no_nu_R_ewbg_doubly_forbidden — the correctness-push
        punchline. SM-as-is fails BOTH conditions."""
        verdict = sm_ewbg_verdict(sm_full_is_crossover=True)
        assert verdict.doubly_forbidden()

    def test_overshoot_ratio_in_verdict(self):
        """Verdict surfaces the KLRS overshoot ratio."""
        verdict = sm_ewbg_verdict(sm_full_is_crossover=True)
        assert verdict.klrs_overshoot_ratio > 1.5

    def test_strict_lo_first_order_branch(self):
        """If we'd assumed the strict-LO first-order prediction,
        SM+3ν_R would still need transition strength to be viable.
        Here we only check the wall-cracked branch evaluates differently
        from H_KLRS branch."""
        v_klrs = sm_ewbg_verdict(sm_full_is_crossover=True)
        v_first_order = sm_ewbg_verdict(sm_full_is_crossover=False)
        # SM-no-ν_R blocking is independent of transition assumption
        assert v_klrs.sm_no_nu_R_ewbg_blocked == v_first_order.sm_no_nu_R_ewbg_blocked
        # SM+3ν_R differs: KLRS blocks, strict-LO does not (wall cracks)
        assert not v_klrs.sm_with_3nu_R_ewbg_under_klrs
        assert v_first_order.sm_with_3nu_R_ewbg_under_klrs

    def test_constants_consistency(self):
        """EWBG_PARAMS values match what the predicates expect."""
        assert EWBG_PARAMS['SM_Z16_ANOMALY_NO_NU_R'] == 13
        assert EWBG_PARAMS['SM_Z16_ANOMALY_WITH_3NU_R'] == 0
        assert EWBG_PARAMS['SPHALERON_DECOUPLING_THRESHOLD'] == 1.0
        assert EWBG_PARAMS['KLRS_M_H_CROSSOVER_THRESHOLD_GEV'] == 72.4
        assert EWBG_PARAMS['SM_M_H_GEV'] == 125.20
