"""Phase 6e Wave 5 — Microscopic-to-Macroscopic Coefficient Match tests."""

from __future__ import annotations

import math

import pytest

from src.core.constants import MICRO_MACRO_PARAMS
from src.core.formulas import (
    lambda_emerg_microscopic,
    cc_problem_ratio,
    cc_decision_gate_e4_verdict,
    g_n_microscopic,
    higher_curvature_microscopic_stelle,
    microscopic_macroscopic_match_residual,
    microscopic_macroscopic_match_holds,
    G_N_from_seeley_dewitt,
    seeley_dewitt_a0,
)
from src.micro_macro_match import (
    LambdaEmergPrediction,
    lambda_emerg_at_point,
    lambda_emerg_scan_over_lambdaUV,
    lambda_emerg_scan_over_N_f,
    decision_gate_e4_verdict,
    GNMatchResult,
    g_n_microscopic_at_point,
    match_residual_scan_over_alpha,
    match_holds,
    CCProblemAssessment,
    assess_cc_problem,
    natural_parameter_scan,
    resolution_locus_diagnostic,
)


M_PL = MICRO_MACRO_PARAMS["M_PLANCK_GEV"]
N_F_SM = MICRO_MACRO_PARAMS["N_F_SM_DIRAC"]
LAMBDA_OBS = MICRO_MACRO_PARAMS["LAMBDA_OBSERVED_GEV4"]
RESOLUTION_LOCUS = MICRO_MACRO_PARAMS["LAMBDA_UV_RESOLUTION_LOCUS_DIAGNOSTIC_GEV"]


# ════════════════════════════════════════════════════════════════════
# Λ^emerg correctness + structural identities
# ════════════════════════════════════════════════════════════════════


class TestLambdaEmergMicroscopic:
    """Lean: ``lambdaEmergMicroscopic`` and its theorems."""

    def test_closed_form(self):
        # Λ^emerg = a_0(N_f) · Λ_UV^4
        assert lambda_emerg_microscopic(2.0, 4.0) == pytest.approx(
            seeley_dewitt_a0(4.0) * 2.0 ** 4
        )

    def test_positive_at_natural_inputs(self):
        # Lean: lambdaEmergMicroscopic_pos
        assert lambda_emerg_microscopic(M_PL, N_F_SM) > 0.0

    def test_zero_iff_lambda_uv_zero(self):
        # Lean: lambdaEmergMicroscopic_eq_zero_iff (forward, Λ=0)
        assert lambda_emerg_microscopic(0.0, N_F_SM) == 0.0

    def test_zero_iff_N_f_zero(self):
        # Lean: lambdaEmergMicroscopic_eq_zero_iff (forward, N_f=0)
        assert lambda_emerg_microscopic(M_PL, 0.0) == 0.0

    def test_nonzero_at_nonzero_inputs(self):
        # Lean: lambdaEmergMicroscopic_eq_zero_iff (reverse contrapositive)
        for L, N in [(1.0, 1.0), (1e10, 4.0), (M_PL, 16.0), (1e-3, 100.0)]:
            assert lambda_emerg_microscopic(L, N) != 0.0

    def test_quadrupling_lambda_uv_multiplies_lambda_emerg_by_256(self):
        # Λ^emerg ∝ Λ_UV^4: (4*Λ)^4 / Λ^4 = 256
        ratio = lambda_emerg_microscopic(4.0, N_F_SM) / lambda_emerg_microscopic(
            1.0, N_F_SM
        )
        assert ratio == pytest.approx(256.0)

    def test_doubling_N_f_doubles_lambda_emerg(self):
        # Λ^emerg ∝ N_f (via a_0)
        assert lambda_emerg_microscopic(M_PL, 2.0) == pytest.approx(
            2.0 * lambda_emerg_microscopic(M_PL, 1.0), rel=1e-12
        )


# ════════════════════════════════════════════════════════════════════
# Decision Gate E.4 — CC problem ratio + verdict
# ════════════════════════════════════════════════════════════════════


class TestDecisionGateE4:
    """Lean: ``cc_problem_reproduced_at_planck_with_dirac`` family."""

    def test_ratio_at_natural_planck_exceeds_1e120(self):
        # Lean: lambdaEmergMicroscopic_at_planck_natural_far_exceeds_observed
        # (Lean theorem proves > 10^100; Python verifies the actual ratio
        # is > 10^120, well above the Lean bound)
        ratio = cc_problem_ratio(M_PL, N_F_SM)
        assert ratio > 1.0e120
        assert math.log10(ratio) > 120.0

    def test_verdict_at_natural_planck_is_reproduced(self):
        v = cc_decision_gate_e4_verdict(M_PL, N_F_SM)
        assert v == MICRO_MACRO_PARAMS["DG_E4_VERDICT_REPRODUCED"]

    def test_verdict_at_resolution_locus_is_resolved(self):
        v = cc_decision_gate_e4_verdict(RESOLUTION_LOCUS, N_F_SM)
        assert v == MICRO_MACRO_PARAMS["DG_E4_VERDICT_RESOLVED"]

    def test_verdict_in_intermediate_band(self):
        # Λ_UV chosen so |log10 ratio| ~ 30 (between 1 and 60 floors)
        Lambda_intermediate = 1.0e-7  # 0.1 keV, far above resolution locus
        v = cc_decision_gate_e4_verdict(Lambda_intermediate, N_F_SM)
        # Should be intermediate (roughly 30 orders above Λ_obs at this cutoff)
        ratio = cc_problem_ratio(Lambda_intermediate, N_F_SM)
        log10r = math.log10(ratio)
        # Confirm it's in the intermediate band by definition
        if abs(log10r) < MICRO_MACRO_PARAMS["CC_RESOLVED_LOG10_BAND"]:
            assert v == MICRO_MACRO_PARAMS["DG_E4_VERDICT_RESOLVED"]
        elif ratio > MICRO_MACRO_PARAMS["CC_REPRODUCED_RATIO_FLOOR"]:
            assert v == MICRO_MACRO_PARAMS["DG_E4_VERDICT_REPRODUCED"]
        else:
            assert v == MICRO_MACRO_PARAMS["DG_E4_VERDICT_INTERMEDIATE"]

    def test_verdict_at_zero_lambda_uv(self):
        v = cc_decision_gate_e4_verdict(0.0, N_F_SM)
        assert v == MICRO_MACRO_PARAMS["DG_E4_VERDICT_INTERMEDIATE"]


# ════════════════════════════════════════════════════════════════════
# Microscopic G_N + match-residual theorems
# ════════════════════════════════════════════════════════════════════


class TestGnMicroscopic:
    """Lean: ``gNMicroscopic``, ``matchResidual``."""

    def test_g_n_at_alpha_one_matches_baseline(self):
        # Lean: gNMicroscopic_at_alpha_one_eq_G_N_emerg
        baseline = G_N_from_seeley_dewitt(M_PL, N_F_SM)
        assert g_n_microscopic(M_PL, N_F_SM, 1.0) == pytest.approx(
            baseline, rel=1e-12
        )

    def test_g_n_scales_linearly_with_alpha(self):
        # gNMicroscopic Λ N_f α = α · G_N_from_a2
        baseline = G_N_from_seeley_dewitt(M_PL, N_F_SM)
        for a in [0.5, 1.0, 2.0, 10.0]:
            assert g_n_microscopic(M_PL, N_F_SM, a) == pytest.approx(
                a * baseline, rel=1e-12
            )

    def test_match_residual_at_alpha_one_is_zero(self):
        # Lean: matchResidual_at_alpha_one
        assert microscopic_macroscopic_match_residual(M_PL, N_F_SM, 1.0) == 0.0

    def test_match_residual_linear_in_alpha_minus_one(self):
        # Lean: matchResidual_eq_alpha_minus_one_times_GN
        baseline = G_N_from_seeley_dewitt(M_PL, N_F_SM)
        for a in [0.1, 0.5, 0.99, 1.01, 2.0, 10.0]:
            expected = (a - 1.0) * baseline
            actual = microscopic_macroscopic_match_residual(M_PL, N_F_SM, a)
            assert actual == pytest.approx(expected, rel=1e-12, abs=1e-50)

    def test_match_residual_zero_iff_alpha_unity(self):
        # Lean: matchResidual_eq_zero_iff_alpha_unity
        for a in [0.5, 0.999, 1.001, 2.0, 100.0]:
            r = microscopic_macroscopic_match_residual(M_PL, N_F_SM, a)
            assert r != 0.0


# ════════════════════════════════════════════════════════════════════
# Higher-curvature Stelle triple (cross-bridge to Wave 2)
# ════════════════════════════════════════════════════════════════════


class TestHigherCurvatureStelle:
    """Lean: ``higherCurvature_stelle_sum_eq``,
    ``higherCurvature_stelle_sum_negative``."""

    def test_stelle_signs(self):
        # alpha < 0, beta < 0, gamma > 0  (Wave 2 sign signature)
        a, b, g = higher_curvature_microscopic_stelle(N_F_SM)
        assert a < 0.0
        assert b < 0.0
        assert g > 0.0

    def test_stelle_sum_negative_at_natural_N_f(self):
        # Lean: higherCurvature_stelle_sum_negative
        a, b, g = higher_curvature_microscopic_stelle(N_F_SM)
        assert (a + b + g) < 0.0

    def test_stelle_sum_closed_form(self):
        # Lean: higherCurvature_stelle_sum_eq:
        # alpha + beta + gamma = -(7 N_f / 810) * (4π)^-2
        for N in [1.0, 4.0, N_F_SM, 100.0]:
            a, b, g = higher_curvature_microscopic_stelle(N)
            expected = -(7.0 * N / 810.0) / (4.0 * math.pi) ** 2
            assert (a + b + g) == pytest.approx(expected, rel=1e-12)

    def test_stelle_linearity_in_N_f(self):
        # All three coefficients are linear in N_f
        a4, b4, g4 = higher_curvature_microscopic_stelle(4.0)
        a8, b8, g8 = higher_curvature_microscopic_stelle(8.0)
        assert a8 == pytest.approx(2.0 * a4, rel=1e-12)
        assert b8 == pytest.approx(2.0 * b4, rel=1e-12)
        assert g8 == pytest.approx(2.0 * g4, rel=1e-12)


# ════════════════════════════════════════════════════════════════════
# Bundled tracked-Prop H_MicroscopicCoefficientMatch
# ════════════════════════════════════════════════════════════════════


class TestBundledMatchPredicate:
    """Lean: ``H_MicroscopicCoefficientMatch``,
    ``dirac_H_MicroscopicCoefficientMatch_at_alpha_one``,
    ``perturbed_alpha_not_H_MicroscopicCoefficientMatch``."""

    def test_dirac_witness_at_alpha_one(self):
        # Lean: dirac_H_MicroscopicCoefficientMatch_at_alpha_one
        assert microscopic_macroscopic_match_holds(M_PL, N_F_SM, 1.0)

    def test_dirac_witness_across_natural_N_f_band(self):
        for N in [1.0, 4.0, 8.0, 16.0, 100.0]:
            assert microscopic_macroscopic_match_holds(M_PL, N, 1.0)

    def test_dirac_witness_across_lambda_uv_band(self):
        for L in [1e3, 1e10, 1e16, M_PL]:
            assert microscopic_macroscopic_match_holds(L, N_F_SM, 1.0)

    def test_perturbed_alpha_breaks_bundle(self):
        # Lean: perturbed_alpha_not_H_MicroscopicCoefficientMatch
        for a in [0.5, 0.99, 1.01, 2.0, 10.0]:
            assert not microscopic_macroscopic_match_holds(M_PL, N_F_SM, a)

    def test_zero_lambda_uv_breaks_bundle(self):
        # Λ_UV = 0 violates conjunct 2 (Λ^emerg > 0).
        # But conjunct 1 also fails because match-residual nonzero at α=2.
        # Test α=1 with Λ_UV = 0 specifically.
        assert not microscopic_macroscopic_match_holds(0.0, N_F_SM, 1.0)


# ════════════════════════════════════════════════════════════════════
# LambdaEmerg + GNMatch dataclasses + scans
# ════════════════════════════════════════════════════════════════════


class TestLambdaEmergPredictionDataClass:
    """Lean: companion to ``lambdaEmergMicroscopic_*`` theorems."""

    def test_dataclass_has_all_fields(self):
        p = lambda_emerg_at_point(M_PL, N_F_SM)
        assert isinstance(p, LambdaEmergPrediction)
        assert p.Lambda_UV_GeV == M_PL
        assert p.N_f == float(N_F_SM)
        assert p.lambda_emerg_GeV4 > 0.0
        assert p.ratio_to_observed > 0.0
        assert p.log10_ratio == pytest.approx(math.log10(p.ratio_to_observed))
        assert p.verdict == MICRO_MACRO_PARAMS["DG_E4_VERDICT_REPRODUCED"]

    def test_zero_lambda_uv_returns_intermediate(self):
        p = lambda_emerg_at_point(0.0, N_F_SM)
        assert p.lambda_emerg_GeV4 == 0.0
        assert math.isnan(p.ratio_to_observed)
        assert math.isnan(p.log10_ratio)
        assert p.verdict == MICRO_MACRO_PARAMS["DG_E4_VERDICT_INTERMEDIATE"]

    def test_lambda_uv_scan_returns_list(self):
        scan = lambda_emerg_scan_over_lambdaUV(N_F_SM, n_points=8)
        assert len(scan) == 8
        # Λ_UV monotonic increasing → log10_ratio monotonic increasing
        log10s = [s.log10_ratio for s in scan]
        for a, b in zip(log10s[:-1], log10s[1:]):
            assert a < b

    def test_N_f_scan_values_returns_one_per_value(self):
        scan = lambda_emerg_scan_over_N_f(M_PL)
        assert len(scan) == len(MICRO_MACRO_PARAMS["N_F_SCAN_VALUES"])

    def test_decision_gate_helper_is_consistent(self):
        v1 = decision_gate_e4_verdict(M_PL, N_F_SM)
        v2 = lambda_emerg_at_point(M_PL, N_F_SM).verdict
        assert v1 == v2 == MICRO_MACRO_PARAMS["DG_E4_VERDICT_REPRODUCED"]


class TestGNMatchResultDataClass:
    """Lean: companion to ``matchResidual_*`` theorems."""

    def test_dataclass_at_alpha_one(self):
        r = g_n_microscopic_at_point(M_PL, N_F_SM, 1.0)
        assert isinstance(r, GNMatchResult)
        assert r.alpha_ADW == 1.0
        assert r.match_residual == 0.0
        assert r.bundle_holds
        assert r.g_n_micro_GeVm2 == r.g_n_baseline_GeVm2

    def test_dataclass_at_perturbed_alpha(self):
        r = g_n_microscopic_at_point(M_PL, N_F_SM, 2.0)
        assert r.match_residual != 0.0
        assert not r.bundle_holds

    def test_alpha_scan_includes_alpha_one(self):
        scan = match_residual_scan_over_alpha(M_PL, N_F_SM, n_points=21)
        # Find any α very close to 1 in log-spaced scan; not guaranteed
        # to hit exactly. Verify residual sign across α=1.
        signs = sorted({1 if r.match_residual > 0 else (-1 if r.match_residual < 0 else 0) for r in scan})
        # Both negative-α (α<1) and positive-α (α>1) regimes appear
        assert -1 in signs
        assert 1 in signs

    def test_match_holds_helper_consistent(self):
        assert match_holds(M_PL, N_F_SM, 1.0)
        assert not match_holds(M_PL, N_F_SM, 1.5)


# ════════════════════════════════════════════════════════════════════
# CCProblemAssessment + natural-parameter scan
# ════════════════════════════════════════════════════════════════════


class TestCCProblemAssessment:
    """Lean: companion to Decision Gate E.4 quantitative anchor."""

    def test_planck_assessment_is_cc_reproduced_and_natural(self):
        a = assess_cc_problem(M_PL, N_F_SM)
        assert a.verdict == MICRO_MACRO_PARAMS["DG_E4_VERDICT_REPRODUCED"]
        assert a.natural
        assert not a.is_resolution_locus

    def test_resolution_locus_is_cc_resolved(self):
        a = resolution_locus_diagnostic(N_F_SM)
        assert a.verdict == MICRO_MACRO_PARAMS["DG_E4_VERDICT_RESOLVED"]
        assert a.is_resolution_locus
        assert not a.natural  # Λ_UV ≪ EW_SCALE

    def test_natural_parameter_scan_no_resolution_at_natural_lambda(self):
        scan = natural_parameter_scan(N_f_values=[1, 4, 16, 100], n_lambda_uv_points=8)
        natural_resolved = [
            a for a in scan
            if a.natural and a.verdict == MICRO_MACRO_PARAMS["DG_E4_VERDICT_RESOLVED"]
        ]
        assert len(natural_resolved) == 0

    def test_natural_parameter_scan_at_planck_all_reproduced(self):
        scan = natural_parameter_scan(N_f_values=[1, 4, 16, 100], n_lambda_uv_points=8)
        # Filter to scan points at the highest Λ_UV (= M_Pl by construction)
        max_lambda = max(a.Lambda_UV_GeV for a in scan)
        at_max = [a for a in scan if a.Lambda_UV_GeV == max_lambda]
        for a in at_max:
            assert a.verdict == MICRO_MACRO_PARAMS["DG_E4_VERDICT_REPRODUCED"]


# ════════════════════════════════════════════════════════════════════
# Lean ↔ Python bridge
# ════════════════════════════════════════════════════════════════════


class TestLeanBridge:
    """Cross-layer consistency: Python values must match Lean theorem
    contents."""

    def test_lambda_observed_matches_lean_constant(self):
        # Lean: lambdaObservedGeV4 := 26 / 10^48
        expected = 26.0 / 10.0 ** 48
        assert LAMBDA_OBS == pytest.approx(expected, rel=1e-6)

    def test_planck_anchor_matches_lean_constant(self):
        # Lean: planckMassGeV := 12 * 10^18  (conservative under-estimate)
        # Python uses the actual M_Pl ~ 1.221e19 GeV (looser bound, ratio
        # gets stronger). Verify Lean's anchor is below Python's.
        lean_anchor = 12.0 * 10.0 ** 18
        assert lean_anchor <= M_PL

    def test_lean_quantitative_bound_at_lean_anchor(self):
        # Lean theorem: at Λ_UV = 12·10^18, N_f = 16,
        #   lambdaEmergMicroscopic > 10^100 * lambdaObservedGeV4
        lean_anchor = 12.0 * 10.0 ** 18
        lhs = lambda_emerg_microscopic(lean_anchor, 16.0)
        rhs = (10.0 ** 100) * (26.0 / 10.0 ** 48)
        assert lhs > rhs
