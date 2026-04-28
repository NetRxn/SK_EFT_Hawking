"""Phase 6e Wave 6 — Einstein-Cartan Extension test suite.

Validates the Wave 6 microscopic torsion-amplitude prediction, the
Decision-Gate-style observational bound passage, and the calibration
biconditional residual ↔ α_EC = 1 against the Lean module
``lean/SKEFTHawking/EinsteinCartanExtension.lean``.
"""

from __future__ import annotations

import math

import numpy as np
import pytest

from src.core.constants import EINSTEIN_CARTAN_PARAMS, MICRO_MACRO_PARAMS
from src.core.formulas import (
    torsion_amplitude_ec,
    torsion_amplitude_at_cosmological_background,
    torsion_observational_bound_satisfied,
    ec_match_residual,
    einstein_cartan_extension_holds,
    G_N_from_seeley_dewitt,
    seeley_dewitt_a0,
)
from src.einstein_cartan import (
    TorsionPrediction,
    torsion_amplitude_at_point,
    torsion_scan_over_alpha,
    torsion_scan_over_lambda_uv,
    BoundVerdict,
    torsion_below_kostelecky,
    torsion_below_hughes_drever,
    torsion_observational_verdict,
    ECResidualResult,
    ec_residual_at_point,
    ec_match_holds,
)


M_PL = 1.221e19  # GeV
N_F_SM = 16
ALPHA_CAL = 1.0


# ────────────────────────────────────────────────────────────────────
# §1. Closed-form torsion amplitude
# ────────────────────────────────────────────────────────────────────


class TestTorsionAmplitudeClosedForm:
    """Closed-form ``torsion_amplitude_ec`` matches Lean's
    ``α_EC · G_N_from_a2 · n_spin`` definition."""

    def test_formula_matches_g_n_times_n_spin(self):
        """`torsion_amplitude_ec(α=1) = G_N_from_a2 · n_spin` (calibration form)."""
        n_s = 1.0e-39
        amp = torsion_amplitude_ec(M_PL, N_F_SM, 1.0, n_s)
        expected = G_N_from_seeley_dewitt(M_PL, N_F_SM) * n_s
        assert math.isclose(amp, expected, rel_tol=1e-12)

    def test_formula_linear_in_alpha(self):
        """At fixed (Λ, N_f, n_spin), `|T_EC|` is linear in α_EC."""
        n_s = 1.0e-39
        amp_1 = torsion_amplitude_ec(M_PL, N_F_SM, 1.0, n_s)
        amp_2 = torsion_amplitude_ec(M_PL, N_F_SM, 2.0, n_s)
        amp_3 = torsion_amplitude_ec(M_PL, N_F_SM, 3.0, n_s)
        assert math.isclose(amp_2, 2.0 * amp_1, rel_tol=1e-12)
        assert math.isclose(amp_3, 3.0 * amp_1, rel_tol=1e-12)

    def test_formula_linear_in_n_spin(self):
        """At fixed (Λ, N_f, α_EC), `|T_EC|` is linear in n_spin."""
        amp_1 = torsion_amplitude_ec(M_PL, N_F_SM, 1.0, 1.0e-39)
        amp_2 = torsion_amplitude_ec(M_PL, N_F_SM, 1.0, 2.0e-39)
        assert math.isclose(amp_2, 2.0 * amp_1, rel_tol=1e-12)

    def test_formula_inverse_lambda_squared(self):
        """At fixed (N_f, α_EC, n_spin), `|T_EC| ∝ 1/Λ²`."""
        n_s = 1.0e-39
        amp_a = torsion_amplitude_ec(1.0e15, N_F_SM, 1.0, n_s)
        amp_b = torsion_amplitude_ec(1.0e16, N_F_SM, 1.0, n_s)
        # Ratio = (10^15/10^16)² = 0.01 → amp_b/amp_a = 0.01
        assert math.isclose(amp_b / amp_a, 0.01, rel_tol=1e-10)

    def test_formula_inverse_n_f(self):
        """At fixed (Λ, α_EC, n_spin), `|T_EC| ∝ 1/N_f`."""
        n_s = 1.0e-39
        amp_8 = torsion_amplitude_ec(M_PL, 8.0, 1.0, n_s)
        amp_16 = torsion_amplitude_ec(M_PL, 16.0, 1.0, n_s)
        assert math.isclose(amp_16, 0.5 * amp_8, rel_tol=1e-12)

    def test_formula_zero_at_zero_n_spin(self):
        """`|T_EC| = 0` when spin density vanishes."""
        amp = torsion_amplitude_ec(M_PL, N_F_SM, 1.0, 0.0)
        assert amp == 0.0

    def test_formula_zero_at_zero_alpha(self):
        """`|T_EC| = 0` when α_EC = 0."""
        amp = torsion_amplitude_ec(M_PL, N_F_SM, 0.0, 1.0e-39)
        assert amp == 0.0


# ────────────────────────────────────────────────────────────────────
# §2. Cosmological-bath specialisation
# ────────────────────────────────────────────────────────────────────


class TestCosmologicalBackground:
    """`torsion_amplitude_at_cosmological_background` uses the canonical
    ``COSMOLOGICAL_SPIN_DENSITY_GEV3`` n_s and matches the general formula."""

    def test_specialisation_matches_general(self):
        """At the canonical cosmological n_s, specialised matches general."""
        n_s = EINSTEIN_CARTAN_PARAMS['COSMOLOGICAL_SPIN_DENSITY_GEV3']
        amp_general = torsion_amplitude_ec(M_PL, N_F_SM, 1.0, n_s)
        amp_cosmic = torsion_amplitude_at_cosmological_background(
            M_PL, N_F_SM, 1.0
        )
        assert math.isclose(amp_general, amp_cosmic, rel_tol=1e-12)

    def test_natural_prediction_order_of_magnitude(self):
        """At natural params (M_Pl, 16, 1), prediction is ~ 2×10⁻⁷⁷ GeV."""
        amp = torsion_amplitude_at_cosmological_background(M_PL, N_F_SM, 1.0)
        assert 1.0e-77 < amp < 1.0e-76

    def test_natural_prediction_strictly_positive(self):
        """Wave 6 substantive non-vanishing-prediction guarantee."""
        amp = torsion_amplitude_at_cosmological_background(M_PL, N_F_SM, 1.0)
        assert amp > 0.0


# ────────────────────────────────────────────────────────────────────
# §3. Decision-Gate-style observational bound (Kostelecky)
# ────────────────────────────────────────────────────────────────────


class TestKosteleckyBound:
    """Wave 6 correctness-push: at natural params, prediction is
    ~83 orders of magnitude below the Kostelecky bound."""

    def test_bound_value_matches_provenance(self):
        """`TORSION_BOUND_KOSTELECKY_GEV = 1×10⁻³¹` GeV (PRL 100, 111102)."""
        bound = EINSTEIN_CARTAN_PARAMS['TORSION_BOUND_KOSTELECKY_GEV']
        assert math.isclose(bound, 1.0e-31, rel_tol=1e-12)

    def test_natural_satisfies_kostelecky(self):
        """Wave 6 main correctness-push numerical."""
        assert torsion_observational_bound_satisfied(
            M_PL, N_F_SM, 1.0, channel='kostelecky'
        )

    def test_natural_satisfies_hughes_drever(self):
        """Wave 6 cross-channel chained-bound numerical."""
        assert torsion_observational_bound_satisfied(
            M_PL, N_F_SM, 1.0, channel='hughes_drever'
        )

    def test_natural_log10_margin_below_kostelecky(self):
        """Margin ≃ 45 orders of magnitude below Kostelecky."""
        bound = EINSTEIN_CARTAN_PARAMS['TORSION_BOUND_KOSTELECKY_GEV']
        amp = torsion_amplitude_at_cosmological_background(M_PL, N_F_SM, 1.0)
        margin = math.log10(bound / amp)
        # Predicted ~ 2.05e-77; bound = 1e-31. log10(1e-31 / 2.05e-77) ≃ 45.7
        assert 45.0 < margin < 46.5

    def test_kostelecky_strictly_tighter_than_hughes_drever(self):
        """Lean theorem `torsionBoundKostelecky_lt_hughesDrever`."""
        b_K = EINSTEIN_CARTAN_PARAMS['TORSION_BOUND_KOSTELECKY_GEV']
        b_HD = EINSTEIN_CARTAN_PARAMS['TORSION_BOUND_HUGHES_DREVER_GEV']
        assert b_K < b_HD

    @pytest.mark.parametrize("alpha_ec", [0.1, 0.5, 1.0, 2.0, 5.0, 10.0])
    def test_kostelecky_satisfied_across_natural_alpha_band(self, alpha_ec):
        """Across the natural α_EC band [0.1, 10], Kostelecky bound holds."""
        assert torsion_observational_bound_satisfied(
            M_PL, N_F_SM, alpha_ec, channel='kostelecky'
        )

    @pytest.mark.parametrize("lambda_uv", [1.0e3, 1.0e10, 1.0e16, 1.0e19])
    def test_kostelecky_satisfied_across_lambda_uv_grid(self, lambda_uv):
        """Across Λ_UV from TeV to M_Pl, Kostelecky bound holds at α=1."""
        assert torsion_observational_bound_satisfied(
            lambda_uv, N_F_SM, 1.0, channel='kostelecky'
        )

    def test_invalid_channel_raises(self):
        """Misspecified channel raises KeyError."""
        with pytest.raises(KeyError):
            torsion_observational_bound_satisfied(
                M_PL, N_F_SM, 1.0, channel='made_up_channel'
            )


# ────────────────────────────────────────────────────────────────────
# §4. EC match residual + Decision-Gate-style biconditional
# ────────────────────────────────────────────────────────────────────


class TestECResidual:
    """Wave 6 expression of Decision Gate E.2: residual = 0 ↔ α_EC = 1."""

    def test_residual_at_calibration_zero(self):
        """ecResidual at α_EC = 1 is exactly 0."""
        n_s = 1.0e-39
        residual = ec_match_residual(M_PL, N_F_SM, 1.0, n_s)
        assert residual == 0.0

    @pytest.mark.parametrize("alpha_ec", [0.5, 1.5, 2.0, 0.99, 1.01])
    def test_residual_off_calibration_nonzero(self, alpha_ec):
        """ecResidual at α_EC ≠ 1 is non-zero (under positive n_spin)."""
        n_s = 1.0e-39
        residual = ec_match_residual(M_PL, N_F_SM, alpha_ec, n_s)
        assert residual != 0.0

    def test_residual_linear_deviation_channel(self):
        """ecResidual = (α_EC - 1) · G_N_from_a2 · n_spin (substantive linear form)."""
        n_s = 1.0e-39
        for alpha_ec in [0.5, 1.5, 2.0]:
            residual = ec_match_residual(M_PL, N_F_SM, alpha_ec, n_s)
            expected = (
                (alpha_ec - 1.0)
                * G_N_from_seeley_dewitt(M_PL, N_F_SM)
                * n_s
            )
            assert math.isclose(residual, expected, rel_tol=1e-12)

    def test_residual_proportional_to_alpha_minus_one(self):
        """Residual at α=2 is exactly (-1)x residual at α=0."""
        n_s = 1.0e-39
        r_2 = ec_match_residual(M_PL, N_F_SM, 2.0, n_s)
        r_0 = ec_match_residual(M_PL, N_F_SM, 0.0, n_s)
        assert math.isclose(r_2, -r_0, rel_tol=1e-12)


# ────────────────────────────────────────────────────────────────────
# §5. Bundled tracked-Prop predicate
# ────────────────────────────────────────────────────────────────────


class TestEinsteinCartanBundle:
    """`einstein_cartan_extension_holds` mirrors Lean's
    ``H_EinsteinCartanExtensionHolds`` 3-conjunct bundle."""

    def test_dirac_witness_at_alpha_one(self):
        """At natural params + α_EC = 1, bundle holds (Lean Dirac witness)."""
        assert einstein_cartan_extension_holds(M_PL, N_F_SM, 1.0)

    @pytest.mark.parametrize("alpha_ec", [0.5, 1.5, 2.0, 0.99, 1.01])
    def test_perturbed_alpha_falsifier(self, alpha_ec):
        """Any α_EC ≠ 1 violates the bundle (Lean perturbed-α falsifier)."""
        assert not einstein_cartan_extension_holds(M_PL, N_F_SM, alpha_ec)

    def test_at_alpha_one_extreme_lambda_uv(self):
        """Bundle holds at any natural Λ_UV under α_EC = 1."""
        for lam in [1.0e3, 1.0e10, 1.0e15, 1.0e19]:
            assert einstein_cartan_extension_holds(lam, N_F_SM, 1.0)


# ────────────────────────────────────────────────────────────────────
# §6. Subpackage dataclasses
# ────────────────────────────────────────────────────────────────────


class TestTorsionPredictionDataclass:
    """`TorsionPrediction` matches `torsion_amplitude_ec` numerics."""

    def test_dataclass_fields(self):
        pred = torsion_amplitude_at_point(M_PL, N_F_SM, 1.0)
        assert isinstance(pred, TorsionPrediction)
        assert pred.lambda_uv_gev == M_PL
        assert pred.n_f == N_F_SM
        assert pred.alpha_ec == 1.0
        assert pred.n_spin_gev3 == \
            EINSTEIN_CARTAN_PARAMS['COSMOLOGICAL_SPIN_DENSITY_GEV3']
        assert pred.amplitude_gev > 0.0

    def test_scan_over_alpha_returns_list(self):
        scan = torsion_scan_over_alpha(M_PL, N_F_SM)
        n_pts = EINSTEIN_CARTAN_PARAMS['ALPHA_SCAN_POINTS']
        assert len(scan) == n_pts
        assert all(isinstance(p, TorsionPrediction) for p in scan)

    def test_scan_over_alpha_monotone(self):
        """Amplitude is monotone-increasing in α_EC."""
        alphas = [0.1, 0.5, 1.0, 2.0, 10.0]
        scan = torsion_scan_over_alpha(M_PL, N_F_SM, alpha_values=alphas)
        amps = [p.amplitude_gev for p in scan]
        assert amps == sorted(amps)

    def test_scan_over_lambda_uv_returns_list(self):
        scan = torsion_scan_over_lambda_uv(N_F_SM, alpha_ec=1.0)
        n_pts = EINSTEIN_CARTAN_PARAMS['LAMBDA_UV_SCAN_POINTS']
        assert len(scan) == n_pts
        assert all(isinstance(p, TorsionPrediction) for p in scan)

    def test_scan_over_lambda_uv_decreasing(self):
        """Amplitude decreases as Λ_UV increases (1/Λ² scaling)."""
        lams = [1.0e10, 1.0e13, 1.0e16, 1.0e19]
        scan = torsion_scan_over_lambda_uv(
            N_F_SM, alpha_ec=1.0, lambda_uv_values=lams
        )
        amps = [p.amplitude_gev for p in scan]
        # Decreasing
        for i in range(1, len(amps)):
            assert amps[i] < amps[i - 1]


class TestBoundVerdictDataclass:
    """`BoundVerdict` matches Decision-Gate-style verdict logic."""

    def test_natural_verdict_below_bound(self):
        v = torsion_observational_verdict(M_PL, N_F_SM, 1.0)
        assert isinstance(v, BoundVerdict)
        assert v.kostelecky_satisfied is True
        assert v.hughes_drever_satisfied is True
        assert (
            v.verdict_label
            == EINSTEIN_CARTAN_PARAMS['TORSION_VERDICT_BOUND_SATISFIED']
        )

    def test_torsion_below_kostelecky_at_natural(self):
        assert torsion_below_kostelecky(M_PL, N_F_SM, 1.0)

    def test_torsion_below_hughes_drever_at_natural(self):
        assert torsion_below_hughes_drever(M_PL, N_F_SM, 1.0)

    def test_log10_margin_positive_at_natural(self):
        v = torsion_observational_verdict(M_PL, N_F_SM, 1.0)
        assert v.log10_margin_kostelecky > 0


class TestECResidualResultDataclass:
    """`ECResidualResult` matches `ec_match_residual` + bundle."""

    def test_at_alpha_one_holds(self):
        r = ec_residual_at_point(M_PL, N_F_SM, 1.0)
        assert isinstance(r, ECResidualResult)
        assert r.residual_gev == 0.0
        assert r.alpha_ec == 1.0
        assert r.match_holds is True

    def test_off_calibration_fails_match(self):
        r = ec_residual_at_point(M_PL, N_F_SM, 1.5)
        assert r.residual_gev != 0.0
        assert r.match_holds is False

    def test_ec_match_holds_helper(self):
        assert ec_match_holds(M_PL, N_F_SM, 1.0)
        assert not ec_match_holds(M_PL, N_F_SM, 2.0)


# ────────────────────────────────────────────────────────────────────
# §7. Cross-Lean consistency
# ────────────────────────────────────────────────────────────────────


class TestLeanBridge:
    """Numerical computations match the Lean module's quantitative claims."""

    def test_lean_quantitative_anchor_inequality(self):
        """Lean: `torsionAtCosmologicalBackground M_Pl 16 1 < 1/10^31`.

        Verify the Python equivalent at higher precision.
        """
        amp = torsion_amplitude_at_cosmological_background(M_PL, N_F_SM, 1.0)
        bound = EINSTEIN_CARTAN_PARAMS['TORSION_BOUND_KOSTELECKY_GEV']
        # Lean proves amp < 1/10^31 = 1e-31; numerical amp ≃ 2.05e-77.
        assert amp < bound
        # And specifically < 10^-76 (much tighter than Lean's bound).
        assert amp < 1.0e-76

    def test_lean_alpha_unity_biconditional(self):
        """Lean: `ecResidual = 0 ↔ α_EC = 1` under positive (Λ, N_f, n_spin)."""
        n_s = 1.0e-39
        # Forward: residual = 0 ⇒ α = 1.
        # Numerically, only α exactly = 1 makes residual exactly 0.
        residuals_off = [
            ec_match_residual(M_PL, N_F_SM, a, n_s)
            for a in [0.5, 0.99, 1.01, 1.5]
        ]
        assert all(r != 0.0 for r in residuals_off)
        # Reverse: α = 1 ⇒ residual = 0.
        assert ec_match_residual(M_PL, N_F_SM, 1.0, n_s) == 0.0

    def test_lean_cross_bridge_at_alpha_one(self):
        """Lean: `torsionAmplitude(α=1) = G_N_from_a2 · n_spin`."""
        n_s = 1.0e-39
        amp = torsion_amplitude_ec(M_PL, N_F_SM, 1.0, n_s)
        g_n = G_N_from_seeley_dewitt(M_PL, N_F_SM)
        assert math.isclose(amp, g_n * n_s, rel_tol=1e-12)

    def test_lean_a0_consistency_with_wave_5(self):
        """Wave 6 inherits Wave 5's a_0(N_f=16) closed form."""
        # Wave 5: a_0(16) = 4·16/(4π)² = 64/(16π²) = 4/π².
        a0 = seeley_dewitt_a0(N_F_SM)
        expected = 4.0 / math.pi ** 2
        assert math.isclose(a0, expected, rel_tol=1e-12)
