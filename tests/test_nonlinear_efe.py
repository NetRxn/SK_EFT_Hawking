"""Phase 6e Wave 4 — Nonlinear Einstein Field Equations from ADW.

Numerical companion tests for ``lean/SKEFTHawking/NonlinearEFE.lean``.

Coverage:

- Stress-energy comparisons (emergent vs matter; deviation channel)
- Trace-level EFE residual (linearity in α-1; vanishing at α=1)
- PPN-style observable ratios (deflection / precession / ringdown)
- Cross-channel structural prediction (precession_dev = 2/3 × deflection_dev)
- Higher-curvature correction at canonical backgrounds
- Bundled ``H_NonlinearEFEHolds`` predicate witness + falsifier
- Cross-bridges to Wave 1 (G_N) + Wave 2 (pulsar bound) + Wave 3 (diff inv)
"""

import math
import numpy as np
import pytest

from src.core.constants import NONLINEAR_EFE_PARAMS
from src.core import formulas
from src.nonlinear_efe import (
    BackgroundCurvature,
    schwarzschild_horizon_background,
    de_sitter_background,
    flrw_radiation_background,
    efe_residual_at_background,
    efe_residual_scan_over_alpha,
    efe_residual_at_dirac_balanced,
    StressEnergyComparison,
    compare_emergent_vs_matter,
    deviation_channel,
    deviation_detectable_at_floor,
    ObservableSignature,
    deflection_signature,
    precession_signature,
    ringdown_signature,
    deviation_below_observation_floor,
    cross_channel_signature_table,
)


# ────────────────────────────────────────────────────────────────────
# Stress-energy: emergent vs matter trace
# ────────────────────────────────────────────────────────────────────

class TestStressEnergyComparison:
    """Substantive content of ``T_emerg`` and the deviation channel."""

    def test_emergent_eq_matter_at_alpha_one(self):
        for rho in [0.1, 1.0, 1e3, 1e10]:
            assert (
                formulas.emergent_stress_energy_trace(rho, 1.0)
                == formulas.matter_stress_energy_trace(rho)
            )

    @pytest.mark.parametrize("alpha", [0.5, 0.99, 1.0, 1.01, 2.0, 5.0])
    def test_deviation_eq_alpha_minus_one_times_rho(self, alpha):
        rho = 3.7
        dev = formulas.emergent_minus_matter_stress_energy_trace(rho, alpha)
        assert dev == pytest.approx((alpha - 1.0) * rho, rel=1e-12)

    def test_emergent_pos_iff_alpha_pos(self):
        rho = 2.0
        # α > 0 ⇒ T_emerg > 0
        for alpha in [0.01, 0.5, 1.0, 10.0]:
            assert formulas.emergent_stress_energy_trace(rho, alpha) > 0
        # α < 0 ⇒ T_emerg < 0
        for alpha in [-0.01, -0.5, -2.0]:
            assert formulas.emergent_stress_energy_trace(rho, alpha) < 0
        # α = 0 ⇒ T_emerg = 0
        assert formulas.emergent_stress_energy_trace(rho, 0.0) == 0.0

    def test_compare_record_consistent(self):
        rec = compare_emergent_vs_matter(rho_ADW=2.0, alpha_ADW=1.5)
        assert rec.T_emerg == pytest.approx(3.0)
        assert rec.T_matter == pytest.approx(2.0)
        assert rec.deviation == pytest.approx(1.0)
        assert rec.deviation_relative == pytest.approx(0.5)

    def test_compare_record_zero_density(self):
        rec = compare_emergent_vs_matter(rho_ADW=0.0, alpha_ADW=2.0)
        assert rec.T_emerg == 0.0
        assert rec.deviation == 0.0
        assert rec.deviation_relative is None  # undefined for ρ = 0

    def test_deviation_detectable_at_floor(self):
        # 5e-3 = default floor
        assert deviation_detectable_at_floor(rho_ADW=1.0, alpha_ADW=1.01)
        assert not deviation_detectable_at_floor(rho_ADW=1.0, alpha_ADW=1.0001)
        assert not deviation_detectable_at_floor(rho_ADW=0.0, alpha_ADW=10.0)


# ────────────────────────────────────────────────────────────────────
# Trace-level EFE residual
# ────────────────────────────────────────────────────────────────────

class TestEFEResidual:
    """Lean ↔ Python bridge for the Wave-4 Decision-Gate biconditional."""

    def test_residual_vanishes_at_alpha_one(self):
        for G_N in [1e-38, 1.0, 1e10]:
            for rho in [0.0, 1.0, 1e10]:
                assert formulas.efe_residual_trace(G_N, rho, 1.0) == 0.0

    @pytest.mark.parametrize("alpha", [0.5, 1.5, 2.0, 5.0])
    def test_residual_linear_in_alpha_minus_one(self, alpha):
        G_N, rho = 1.0, 1.0
        expected = 8.0 * math.pi * G_N * rho * (alpha - 1.0)
        assert formulas.efe_residual_trace(G_N, rho, alpha) == pytest.approx(
            expected, rel=1e-12
        )

    def test_residual_vanishes_at_zero_density(self):
        for alpha in [0.5, 1.0, 1.5, 2.0]:
            assert formulas.efe_residual_trace(1.0, 0.0, alpha) == 0.0

    def test_residual_at_dirac_balanced_calibration(self):
        # Cross-bridge: at the Wave-1 G_N_from_seeley_dewitt and α=1,
        # residual is identically zero (Lean theorem
        # efeResidualTrace_at_dirac_calibration_vanishes).
        assert (
            formulas.efe_residual_at_dirac_calibration(
                Lambda_UV=1e16, N_f=15, rho_ADW=1.0
            )
            == 0.0
        )

    def test_residual_scan_linearity(self):
        alpha_values = np.array([0.5, 0.75, 1.0, 1.25, 1.5])
        scan = efe_residual_scan_over_alpha(
            G_N=1.0, rho_ADW=1.0, alpha_values=alpha_values,
        )
        # Each (α, residual) pair: residual / (α - 1) must be constant
        # (= 8π) — directly tests the linear-in-(α-1) claim.
        slopes = [
            r / (a - 1.0) if a != 1.0 else None for a, r in scan
        ]
        # All non-None slopes equal 8π
        for s in slopes:
            if s is not None:
                assert s == pytest.approx(8.0 * math.pi, rel=1e-12)


# ────────────────────────────────────────────────────────────────────
# Background-curvature data
# ────────────────────────────────────────────────────────────────────

class TestBackgroundCurvatures:
    """Three canonical backgrounds with different curvature signatures."""

    def test_schwarzschild_vacuum(self):
        bg = schwarzschild_horizon_background()
        assert bg.R == 0.0
        assert bg.Ricci_sq == 0.0
        assert bg.Riemann_sq > 0.0  # vacuum but Kretschmann ≠ 0

    def test_de_sitter_curvature_invariants(self):
        bg = de_sitter_background()
        # de Sitter at H=1: R = 12, R² = 144, R_μν² = 36, R_μνρσ² = 24
        assert bg.R == 12.0
        assert bg.R_sq == 144.0
        assert bg.Ricci_sq == 36.0
        assert bg.Riemann_sq == 24.0
        # Sanity: R² = R · R → 144 = 12 · 12
        assert bg.R_sq == bg.R ** 2

    def test_flrw_radiation_traceless(self):
        bg = flrw_radiation_background()
        # Radiation: traceless T → R = 0
        assert bg.R == 0.0
        assert bg.R_sq == 0.0
        assert bg.Ricci_sq == 12.0
        assert bg.Riemann_sq == 12.0

    @pytest.mark.parametrize(
        "bg_factory",
        [
            schwarzschild_horizon_background,
            de_sitter_background,
            flrw_radiation_background,
        ],
    )
    def test_residual_at_background_matches_residual_alone(self, bg_factory):
        bg = bg_factory()
        # The residual at any background equals the residual computed
        # from (G_N, ρ, α) alone; bg is documentation
        assert (
            efe_residual_at_background(bg, G_N=1.0, rho_ADW=1.0,
                                          alpha_ADW=1.0)
            == 0.0
        )
        assert efe_residual_at_background(
            bg, G_N=1.0, rho_ADW=1.0, alpha_ADW=2.0
        ) == pytest.approx(8.0 * math.pi, rel=1e-12)


# ────────────────────────────────────────────────────────────────────
# Higher-curvature correction at backgrounds
# ────────────────────────────────────────────────────────────────────

class TestHigherCurvatureCorrection:
    """Wave 4 ↔ Wave 2 cross-bridge for higher-curvature term."""

    @pytest.mark.parametrize("N_f", [1, 6, 15, 24, 27])
    def test_correction_below_pulsar_at_de_sitter(self, N_f):
        bg = de_sitter_background()
        correction = formulas.higher_curvature_correction_at_background(
            N_f, bg.R_sq, bg.Ricci_sq, bg.Riemann_sq,
        )
        # Wave 2 main result: each coefficient < 10^59 (pulsar bound).
        # The aggregate correction at de Sitter is an O(1) combination
        # of the three coefficients with O(100) curvature inputs;
        # bound: |correction| ≤ (R² + Ricci² + Riemann²) · 1e59 = O(1e62).
        bound = (bg.R_sq + bg.Ricci_sq + bg.Riemann_sq) * 1.0e59
        assert abs(correction) < bound
        # Substantive: the correction is also non-zero
        assert correction != 0.0

    def test_correction_zero_at_vacuum_no_kretschmann(self):
        # All zero curvature → zero correction
        assert (
            formulas.higher_curvature_correction_at_background(
                15, 0.0, 0.0, 0.0
            )
            == 0.0
        )

    def test_correction_linear_in_N_f(self):
        # Wave 1 coefficients are linear in N_f; aggregate inherits
        bg = de_sitter_background()
        c_at_1 = formulas.higher_curvature_correction_at_background(
            1, bg.R_sq, bg.Ricci_sq, bg.Riemann_sq,
        )
        c_at_24 = formulas.higher_curvature_correction_at_background(
            24, bg.R_sq, bg.Ricci_sq, bg.Riemann_sq,
        )
        assert c_at_24 == pytest.approx(24.0 * c_at_1, rel=1e-12)


# ────────────────────────────────────────────────────────────────────
# Observable signatures
# ────────────────────────────────────────────────────────────────────

class TestObservableSignatures:
    """PPN-style multi-channel predictions."""

    def test_deflection_at_alpha_one_eq_GR(self):
        sig = deflection_signature(1.0)
        assert sig.ratio == 1.0
        assert sig.deviation == 0.0
        assert sig.detectable is False

    def test_precession_at_alpha_one_eq_GR(self):
        sig = precession_signature(1.0)
        assert sig.ratio == pytest.approx(1.0, rel=1e-12)
        assert sig.deviation == pytest.approx(0.0, abs=1e-12)
        assert sig.detectable is False

    def test_ringdown_at_alpha_one_eq_GR(self):
        sig = ringdown_signature(1.0)
        assert sig.ratio == 1.0
        assert sig.detectable is False

    @pytest.mark.parametrize("alpha", [0.5, 0.9, 1.0, 1.1, 1.5, 2.0])
    def test_precession_eq_2alpha_plus_1_div_3(self, alpha):
        # PPN combination: (2 + 2γ - β)/3 with γ=α, β=1 ⇒ (2α + 1)/3
        expected = (2.0 * alpha + 1.0) / 3.0
        assert formulas.precession_ratio(alpha) == pytest.approx(
            expected, rel=1e-12
        )

    @pytest.mark.parametrize("alpha", [0.5, 1.5, 2.0, 5.0])
    def test_precession_dev_eq_two_thirds_deflection_dev(self, alpha):
        """Cross-channel structural claim — Wave 4 anchor."""
        defl = formulas.deflection_ratio(alpha) - 1.0
        prec = formulas.precession_ratio(alpha) - 1.0
        assert prec == pytest.approx((2.0 / 3.0) * defl, rel=1e-12)

    def test_deflection_deviation_above_VLBI_floor(self):
        # 5% α-deviation greatly exceeds the 3e-4 VLBI floor
        sig = deflection_signature(1.05)
        assert sig.detectable

    def test_deflection_deviation_below_VLBI_floor(self):
        # 1e-5 α-deviation is below VLBI's 3e-4 floor
        sig = deflection_signature(1.0 + 1e-5)
        assert not sig.detectable

    def test_precession_deviation_floor(self):
        # MESSENGER 1e-4: at α=1.001, deviation = 2(α-1)/3 ≈ 6.7e-4
        sig = precession_signature(1.001)
        assert sig.detectable
        sig2 = precession_signature(1.0 + 1e-5)
        assert not sig2.detectable

    def test_cross_channel_signature_table(self):
        sigs = cross_channel_signature_table(1.05)
        assert len(sigs) == 3
        names = {s.channel for s in sigs}
        assert names == {"deflection", "precession", "ringdown"}
        # All three deviations consistent with α=1.05 prediction
        defl = next(s for s in sigs if s.channel == "deflection")
        prec = next(s for s in sigs if s.channel == "precession")
        ring = next(s for s in sigs if s.channel == "ringdown")
        assert defl.deviation == pytest.approx(0.05)
        assert prec.deviation == pytest.approx((2.0 / 3.0) * 0.05, rel=1e-12)
        assert ring.deviation == pytest.approx(0.05)

    def test_deviation_below_observation_floor_at_calib(self):
        # At α = 1 exactly, all three channels are below observation floors
        d = deviation_below_observation_floor(1.0)
        assert all(d.values())


# ────────────────────────────────────────────────────────────────────
# Bundled H_NonlinearEFEHolds predicate
# ────────────────────────────────────────────────────────────────────

class TestNonlinearEFEHoldsBundle:
    """Lean ↔ Python bridge for the Wave-4 tracked-Prop bundle."""

    def test_holds_at_calibration(self):
        assert formulas.nonlinear_efe_holds(
            Lambda_UV=1e16, N_f=15, rho_ADW=1.0, alpha_ADW=1.0
        )

    def test_fails_off_calibration(self):
        # α_ADW = 1.5 fails the residual conjunct
        assert not formulas.nonlinear_efe_holds(
            Lambda_UV=1e16, N_f=15, rho_ADW=1.0, alpha_ADW=1.5
        )

    @pytest.mark.parametrize("N_f", [1, 6, 15, 24, 27])
    def test_holds_across_SM_N_f_at_calib(self, N_f):
        # All SM-relevant N_f satisfy the bundle at α = 1
        assert formulas.nonlinear_efe_holds(
            Lambda_UV=1e16, N_f=N_f, rho_ADW=1.0, alpha_ADW=1.0
        )

    def test_holds_within_tolerance(self):
        # Within the EFE_RESIDUAL_TOLERANCE (1e-12), bundle holds
        tol = NONLINEAR_EFE_PARAMS['EFE_RESIDUAL_TOLERANCE']
        assert formulas.nonlinear_efe_holds(
            Lambda_UV=1e16, N_f=15, rho_ADW=1.0, alpha_ADW=1.0 + 0.1 * tol
        )
        # Outside tolerance, bundle fails
        assert not formulas.nonlinear_efe_holds(
            Lambda_UV=1e16, N_f=15, rho_ADW=1.0, alpha_ADW=1.0 + 100.0 * tol
        )


# ────────────────────────────────────────────────────────────────────
# Cross-module consistency
# ────────────────────────────────────────────────────────────────────

class TestCrossModuleConsistency:
    """Wave 4 connects to Waves 1, 2, 3 by name."""

    def test_dirac_balanced_matches_wave1_G_N(self):
        # G_N at the dirac-balanced calibration equals the Wave 1
        # heat-kernel-derived Newton constant
        from src.core.formulas import G_N_from_seeley_dewitt
        G_N = G_N_from_seeley_dewitt(1e16, 15)
        # Using G_N directly in the residual formula at α=1 should give 0
        assert formulas.efe_residual_trace(G_N, 1.0, 1.0) == 0.0

    def test_higher_curvature_at_de_sitter_matches_wave2_table(self):
        # At de Sitter, the correction is the sum of three Wave 2 coefs
        # times their respective curvature invariants
        bg = de_sitter_background()
        N_f = 24
        from src.core.formulas import (
            higher_curvature_R_sq_coefficient,
            higher_curvature_Ricci_sq_coefficient,
            higher_curvature_Riemann_sq_coefficient,
        )
        expected = (
            higher_curvature_R_sq_coefficient(N_f) * bg.R_sq
            + higher_curvature_Ricci_sq_coefficient(N_f) * bg.Ricci_sq
            + higher_curvature_Riemann_sq_coefficient(N_f) * bg.Riemann_sq
        )
        actual = formulas.higher_curvature_correction_at_background(
            N_f, bg.R_sq, bg.Ricci_sq, bg.Riemann_sq,
        )
        assert actual == expected

    def test_diff_invariance_holds_across_canonical_bgs(self):
        # Wave 3 path-(b) diff invariance must hold at all three
        # canonical backgrounds for the Christensen-Duff Dirac bundle
        from src.core.formulas import diff_invariance_holds_order_by_order
        for bg in [
            schwarzschild_horizon_background(),
            de_sitter_background(),
            flrw_radiation_background(),
        ]:
            assert diff_invariance_holds_order_by_order(
                15, bg.R, bg.R_sq, bg.Ricci_sq, bg.Riemann_sq,
            )


# ────────────────────────────────────────────────────────────────────
# Constant integrity
# ────────────────────────────────────────────────────────────────────

class TestConstantsIntegrity:
    """NONLINEAR_EFE_PARAMS values consistent with literature."""

    def test_alpha_calibration_eq_one(self):
        assert NONLINEAR_EFE_PARAMS['ALPHA_ADW_CALIBRATED'] == 1.0

    def test_alpha_natural_band_brackets_unity(self):
        assert NONLINEAR_EFE_PARAMS['ALPHA_ADW_NATURAL_MIN'] < 1.0
        assert NONLINEAR_EFE_PARAMS['ALPHA_ADW_NATURAL_MAX'] > 1.0

    def test_observation_floors_positive(self):
        for key in [
            'DEFLECTION_OBS_RELATIVE_PRECISION',
            'PERIHELION_OBS_RELATIVE_PRECISION',
            'RINGDOWN_OBS_RELATIVE_PRECISION',
        ]:
            assert NONLINEAR_EFE_PARAMS[key] > 0.0

    def test_de_sitter_R_sq_eq_R_squared(self):
        # Sanity: R² = R · R for de Sitter
        R = NONLINEAR_EFE_PARAMS['DE_SITTER_R_AT_UNIT_H']
        R_sq = NONLINEAR_EFE_PARAMS['DE_SITTER_R_SQ_AT_UNIT_H']
        assert R_sq == pytest.approx(R ** 2)

    def test_benchmark_backgrounds_complete(self):
        bgs = NONLINEAR_EFE_PARAMS['BENCHMARK_BACKGROUNDS']
        assert "Schwarzschild" in bgs
        assert "de_Sitter" in bgs
        assert "FLRW_radiation" in bgs
