"""Gravitational-wave propagation and numerical-window tests.

The adopted susceptibility endpoints exceed the GW170817 speed cap.
The compatible interval surrounds unity inside the adopted range.
Exact rational and high-precision references check the numerical
interval and speed-deviation computations.
"""

from __future__ import annotations

import math

from decimal import Decimal, localcontext
from fractions import Fraction

import numpy as np
import pytest

from src.core.constants import GW_PARAMS
from src.core.formulas import (
    c_GW_deviation_from_c,
    c_GW_from_chi_vest,
    c_GW_natural_range,
    dispersion_correction_from_GammaH,
    ligo_constraint_check,
)
from src.gravitational_waves import (
    GW170817Verdict,
    c_GW_at_natural_anchor,
    c_GW_grid,
    c_GW_natural_window_violation_factor,
    chi_vest_window_compatible_with_ligo,
    dispersion_correction_grid,
    leading_dispersion_correction,
    ligo_compatibility_check,
    ligo_falsification_summary,
)


# =====================================================================
# c_GW core formulas
# =====================================================================
class TestCGWCore:
    """c_GW = c · √χ_vest under the assumed normalized scalar law."""

    def test_c_GW_at_chi_one_equals_c(self):
        """Lean: GravitationalWaves.c_GW_at_chi_one"""
        c = GW_PARAMS["C_LIGHT_M_S"]
        assert c_GW_from_chi_vest(1.0, c) == pytest.approx(c, rel=1e-15)

    def test_c_GW_at_chi_default_equals_c(self):
        c = GW_PARAMS["C_LIGHT_M_S"]
        assert c_GW_from_chi_vest(GW_PARAMS["CHI_VEST_DEFAULT"], c) == pytest.approx(c, rel=1e-15)

    def test_c_GW_pos_for_chi_pos(self):
        """Lean: GravitationalWaves.c_GW_pos"""
        c = 1.0
        for chi in [1e-3, 0.1, 0.5, 1.0, 2.0, 10.0, 100.0]:
            assert c_GW_from_chi_vest(chi, c) > 0

    def test_c_GW_at_natural_anchor_helper(self):
        c = GW_PARAMS["C_LIGHT_M_S"]
        assert c_GW_at_natural_anchor() == pytest.approx(c, rel=1e-15)

    def test_c_GW_zero_at_chi_zero(self):
        assert c_GW_from_chi_vest(0.0, 1.0) == pytest.approx(0.0, abs=1e-15)

    @pytest.mark.parametrize("chi", [
        math.nextafter(0.0, 1.0), 1e-300, 1e-18, 1e-16,
        np.float32(1e-8), np.longdouble("1e-18"), 0.1, 1.0, 10.0,
    ])
    def test_speed_preserves_small_positive_susceptibilities(self, chi):
        """Avoid losing chi in 1 + (chi - 1), including normal callers' scalars."""
        with localcontext() as context:
            context.prec = 100
            numerator, denominator = chi.as_integer_ratio()
            reference = float((Decimal(numerator) / Decimal(denominator)).sqrt())
        actual = c_GW_from_chi_vest(chi, 1.0)
        assert actual > 0.0
        assert abs(actual - reference) <= math.ulp(reference)

    def test_speed_retains_wide_scalar_until_final_return(self):
        chi = np.longdouble("1e-18")
        speed = np.longdouble("1.000000000000000001")
        with localcontext() as context:
            context.prec = 100
            chi_num, chi_den = chi.as_integer_ratio()
            speed_num, speed_den = speed.as_integer_ratio()
            reference = float(
                (Decimal(chi_num) / Decimal(chi_den)).sqrt()
                * Decimal(speed_num) / Decimal(speed_den)
            )
        assert abs(c_GW_from_chi_vest(chi, speed) - reference) <= math.ulp(reference)

    def test_negative_susceptibility_returns_nan(self):
        with np.errstate(invalid="ignore"):
            assert math.isnan(c_GW_from_chi_vest(-1e-18, 1.0))

    def test_grid_preserves_small_positive_speeds(self):
        chi_values, speeds, _ = c_GW_grid(1e-18, 1e-16, 3)
        with localcontext() as context:
            context.prec = 100
            c_num, c_den = GW_PARAMS["C_LIGHT_M_S"].as_integer_ratio()
            exact_speed = Decimal(c_num) / Decimal(c_den)
            for chi, actual in zip(chi_values, speeds, strict=True):
                numerator, denominator = chi.as_integer_ratio()
                reference = float(
                    (Decimal(numerator) / Decimal(denominator)).sqrt() * exact_speed
                )
                assert actual > 0.0
                assert abs(actual - reference) <= math.ulp(reference)


class TestCGWDeviation:
    """Δc/c (χ_vest) = √χ_vest − 1."""

    def test_deviation_zero_at_chi_one(self):
        """Lean: GravitationalWaves.c_GW_deviation_zero_iff_chi_one (forward direction)"""
        assert c_GW_deviation_from_c(1.0) == pytest.approx(0.0, abs=1e-15)

    def test_deviation_negative_below_one(self):
        for chi in [0.01, 0.1, 0.5, 0.9]:
            assert c_GW_deviation_from_c(chi) < 0

    def test_deviation_positive_above_one(self):
        for chi in [1.1, 2.0, 10.0, 100.0]:
            assert c_GW_deviation_from_c(chi) > 0

    def test_deviation_strict_monotone(self):
        """Lean: GravitationalWaves.c_GW_deviation_strict_mono"""
        chis = np.geomspace(0.01, 100, 51)
        deviations = np.array([c_GW_deviation_from_c(c) for c in chis])
        assert np.all(np.diff(deviations) > 0), "Δc/c should be strictly increasing in χ"

    def test_deviation_at_one_tenth(self):
        """Lean: natural_lower_violates_ligo numerical anchor"""
        # √(0.1) ≈ 0.31623 → Δ ≈ −0.68377
        assert c_GW_deviation_from_c(0.1) == pytest.approx(np.sqrt(0.1) - 1.0, rel=1e-15)
        assert c_GW_deviation_from_c(0.1) < -0.5  # well below −0.5

    def test_deviation_at_ten(self):
        """Lean: natural_upper_violates_ligo numerical anchor"""
        # √(10) ≈ 3.16228 → Δ ≈ 2.16228
        assert c_GW_deviation_from_c(10.0) == pytest.approx(np.sqrt(10.0) - 1.0, rel=1e-15)
        assert c_GW_deviation_from_c(10.0) > 1.0  # well above 1.0


# =====================================================================
# GW170817 correctness-push
# =====================================================================
class TestLigoConstraint:
    """LigoSatisfied = |Δc/c| ≤ 3e-15."""

    def test_ligo_satisfied_at_chi_one(self):
        """Lean: GravitationalWaves.ligo_satisfied_at_chi_one"""
        assert ligo_constraint_check(c_GW_deviation_from_c(1.0))

    def test_ligo_satisfied_within_cap(self):
        # Δ slightly inside cap should pass
        cap = GW_PARAMS["C_GW_TWO_SIDED_CAP"]
        assert ligo_constraint_check(0.5 * cap)
        assert ligo_constraint_check(-0.5 * cap)
        assert ligo_constraint_check(cap)
        assert ligo_constraint_check(-cap)

    def test_ligo_fails_outside_cap(self):
        cap = GW_PARAMS["C_GW_TWO_SIDED_CAP"]
        assert not ligo_constraint_check(2.0 * cap)
        assert not ligo_constraint_check(-2.0 * cap)
        assert not ligo_constraint_check(1e-10)

    def test_ligo_compatibility_check_struct(self):
        verdict = ligo_compatibility_check(1.0)
        assert isinstance(verdict, GW170817Verdict)
        assert verdict.ligo_satisfied
        assert verdict.deviation == pytest.approx(0.0, abs=1e-15)
        assert verdict.violation_factor == pytest.approx(0.0, abs=1e-15)

    def test_ligo_window_brackets_unity(self):
        """Lean: c_GW_match_iff_chi_close_to_one — window contains 1."""
        cap = GW_PARAMS["C_GW_TWO_SIDED_CAP"]
        chi_lo, chi_hi = chi_vest_window_compatible_with_ligo(cap)
        assert chi_lo < 1.0 < chi_hi
        # window is symmetric around 1 to leading order
        assert (1.0 - chi_lo) == pytest.approx(chi_hi - 1.0, rel=1e-3)

    def test_ligo_window_endpoints_match_exact_default_cap(self):
        """Rounded endpoints agree with the exact cap's rational preimage."""
        cap = Fraction.from_float(GW_PARAMS["C_GW_TWO_SIDED_CAP"])
        chi_lo, chi_hi = chi_vest_window_compatible_with_ligo()
        assert chi_lo == float((1 - cap) ** 2)
        assert chi_hi == float((1 + cap) ** 2)


# =====================================================================
# Natural-range falsification (LOAD-BEARING)
# =====================================================================
class TestNaturalRangeFalsification:
    """Both adopted susceptibility endpoints exceed the GW170817 speed cap."""

    def test_natural_lower_violates_ligo(self):
        """Lean: natural_lower_violates_ligo"""
        chi_lo = GW_PARAMS["CHI_VEST_NATURAL_LOWER"]
        verdict = ligo_compatibility_check(chi_lo)
        assert not verdict.ligo_satisfied
        # |Δc/c| should be ~0.68, way above 3e-15
        assert abs(verdict.deviation) > 0.5

    def test_natural_upper_violates_ligo(self):
        """Lean: natural_upper_violates_ligo"""
        chi_hi = GW_PARAMS["CHI_VEST_NATURAL_UPPER"]
        verdict = ligo_compatibility_check(chi_hi)
        assert not verdict.ligo_satisfied
        # |Δc/c| should be ~2.16, way above 3e-15
        assert abs(verdict.deviation) > 1.0

    def test_natural_range_violation_factor_above_1e14(self):
        """Wave 2 main finding: ratio > 10^14."""
        delta_lo, delta_hi, ratio = c_GW_natural_window_violation_factor()
        assert ratio > 1e14
        # Specific values from Stage 2 numerics
        assert delta_lo == pytest.approx(np.sqrt(0.1) - 1.0, rel=1e-15)
        assert delta_hi == pytest.approx(np.sqrt(10.0) - 1.0, rel=1e-15)

    def test_falsification_summary_natural_range_incompatible(self):
        """Lean: vestigial_natural_range_violates_ligo"""
        summary = ligo_falsification_summary()
        assert summary["natural_range_compatible"] is False
        assert summary["violation_ratio_lower"] > 1e14
        assert summary["violation_ratio_upper"] > 1e14

    def test_falsification_summary_keys_complete(self):
        summary = ligo_falsification_summary()
        expected_keys = {
            "chi_vest_lower", "chi_vest_upper",
            "delta_lower", "delta_upper", "cap",
            "ligo_compatible_window",
            "violation_ratio_lower", "violation_ratio_upper",
            "natural_range_compatible",
        }
        assert expected_keys <= set(summary.keys())

    def test_natural_range_helper_matches_formula(self):
        """c_GW_natural_range from formulas.py matches summary."""
        delta_min, delta_max = c_GW_natural_range(
            GW_PARAMS["CHI_VEST_NATURAL_LOWER"],
            GW_PARAMS["CHI_VEST_NATURAL_UPPER"],
        )
        delta_lo, delta_hi, _ = c_GW_natural_window_violation_factor()
        assert delta_min == pytest.approx(delta_lo, rel=1e-15)
        assert delta_max == pytest.approx(delta_hi, rel=1e-15)


# =====================================================================
# Parameter-grid scans
# =====================================================================
class TestCGWGrid:
    """χ_vest grid scans for figure generation."""

    def test_c_GW_grid_default(self):
        chi_grid, c_GW_values, deviations = c_GW_grid()
        assert chi_grid.shape == (51,)
        assert c_GW_values.shape == (51,)
        assert deviations.shape == (51,)

    def test_c_GW_grid_endpoints(self):
        chi_grid, _, deviations = c_GW_grid()
        assert chi_grid[0] == pytest.approx(GW_PARAMS["CHI_VEST_NATURAL_LOWER"])
        assert chi_grid[-1] == pytest.approx(GW_PARAMS["CHI_VEST_NATURAL_UPPER"])
        assert deviations[0] < 0
        assert deviations[-1] > 0

    def test_c_GW_grid_monotone(self):
        _, c_GW_values, deviations = c_GW_grid()
        assert np.all(np.diff(c_GW_values) > 0)
        assert np.all(np.diff(deviations) > 0)

    def test_c_GW_grid_geometric_sampling(self):
        """χ_vest grid is geometric (log-spaced)."""
        chi_grid, _, _ = c_GW_grid(n_points=11)
        # Geometric sampling: log(chi_grid) is arithmetic
        diffs = np.diff(np.log(chi_grid))
        assert np.allclose(diffs, diffs[0], rtol=1e-12)

    def test_c_GW_grid_custom_endpoints(self):
        chi_grid, _, _ = c_GW_grid(0.5, 2.0, n_points=21)
        assert chi_grid[0] == pytest.approx(0.5)
        assert chi_grid[-1] == pytest.approx(2.0)


# =====================================================================
# Illustrative numerical product correction (physical matching open)
# =====================================================================
class TestDispersionCorrection:
    """Illustrative real-product ansatz: delta = gamma * omega."""

    def test_dispersion_zero_at_no_dissipation(self):
        """Lean: dispersion_correction_zero_at_no_dissipation"""
        for omega in [10.0, 100.0, 1e3, 1e4]:
            assert dispersion_correction_from_GammaH(omega, 0.0) == 0.0

    def test_dispersion_linear_in_gamma(self):
        """Lean: dispersion_correction_linear_in_gamma"""
        omega = 100.0
        gamma1 = 1e-30
        gamma2 = 2e-30
        d1 = dispersion_correction_from_GammaH(omega, gamma1)
        d2 = dispersion_correction_from_GammaH(omega, gamma2)
        d_sum = dispersion_correction_from_GammaH(omega, gamma1 + gamma2)
        assert d_sum == pytest.approx(d1 + d2, rel=1e-15)

    def test_dispersion_at_default_gamma(self):
        omega = GW_PARAMS["GW170817_PEAK_FREQ_HZ"]
        result = leading_dispersion_correction(omega)
        # Placeholder gamma=1e-30, numerical probe=100 gives delta=1e-28.
        # Physical frequency convention and unit normalization remain unmatched.
        assert result == pytest.approx(1e-30 * 100.0, rel=1e-15)

    def test_dispersion_grid_shape(self):
        freqs, corrections = dispersion_correction_grid()
        assert freqs.shape == (41,)
        assert corrections.shape == (41,)

    def test_dispersion_grid_endpoints(self):
        freqs, _ = dispersion_correction_grid()
        assert freqs[0] == pytest.approx(GW_PARAMS["GW_FREQ_HZ_LOWER"])
        assert freqs[-1] == pytest.approx(GW_PARAMS["GW_FREQ_HZ_UPPER"])

    def test_dispersion_grid_monotone(self):
        _, corrections = dispersion_correction_grid()
        # Linear in ω with positive γ → strictly increasing
        assert np.all(np.diff(corrections) > 0)

    def test_dispersion_well_below_ligo_at_default(self):
        """Default γ_H → dispersion correction ≪ LIGO cap."""
        omega = GW_PARAMS["GW170817_PEAK_FREQ_HZ"]
        result = leading_dispersion_correction(omega)
        assert abs(result) < GW_PARAMS["C_GW_TWO_SIDED_CAP"]


# =====================================================================
# Lean cross-check: tracked-hypothesis bundle
# =====================================================================
class TestVestigialModeIsGravitonBundle:
    """Cross-checks for the Lean H_VestigialModeIsGraviton bundle."""

    def test_anchor_satisfies_bundle(self):
        """Lean: H_VestigialModeIsGraviton_at_one"""
        verdict = ligo_compatibility_check(1.0)
        assert verdict.ligo_satisfied
        assert verdict.chi_vest > 0
        c = GW_PARAMS["C_LIGHT_M_S"]
        assert c_GW_from_chi_vest(verdict.chi_vest, c) > 0

    def test_natural_lower_falsifies_bundle(self):
        """Lean: H_VestigialModeIsGraviton_fails_at_natural_lower"""
        verdict = ligo_compatibility_check(GW_PARAMS["CHI_VEST_NATURAL_LOWER"])
        # Bundle requires LigoSatisfied — this fails
        assert not verdict.ligo_satisfied

    def test_natural_upper_falsifies_bundle(self):
        """Lean: H_VestigialModeIsGraviton_fails_at_natural_upper"""
        verdict = ligo_compatibility_check(GW_PARAMS["CHI_VEST_NATURAL_UPPER"])
        assert not verdict.ligo_satisfied

    def test_zero_falsifies_bundle(self):
        """Lean: H_VestigialModeIsGraviton_fails_at_zero (positivity)"""
        # χ_vest = 0 fails the positivity predicate
        chi = 0.0
        assert chi <= 0  # P1 fails

    def test_compatible_window_width_consistent_with_lean(self):
        """Exact real width is 4*tol; rounded endpoints approximate the preimage."""
        cap = GW_PARAMS["C_GW_TWO_SIDED_CAP"]
        chi_lo, chi_hi = chi_vest_window_compatible_with_ligo(cap)
        # Quantized endpoints carry a known rounding budget around exact 4·tol.
        exact_width = 4 * Fraction.from_float(cap)
        width = Fraction.from_float(chi_hi) - Fraction.from_float(chi_lo)
        budget = (Fraction.from_float(math.ulp(chi_lo)) +
                  Fraction.from_float(math.ulp(chi_hi))) / 2
        assert abs(width - exact_width) <= budget


# =====================================================================
# Integration: matches Wave 1 cross-references
# =====================================================================
class TestWave1Integration:
    """Wave 2 cross-checks against Wave 1 LinearizedEFE constants."""

    def test_c_light_natural_units_consistent(self):
        c = GW_PARAMS["C_LIGHT_M_S"]
        # Should match SI constant exactly (defined value)
        assert c == 299792458.0

    def test_chi_vest_natural_range_matches_alpha_ADW_convention(self):
        """Adopted windows match numerically without identifying their coefficients."""
        from src.core.constants import GRAV_PARAMS
        assert GW_PARAMS["CHI_VEST_NATURAL_LOWER"] == GRAV_PARAMS["ALPHA_ADW_LOWER"]
        assert GW_PARAMS["CHI_VEST_NATURAL_UPPER"] == GRAV_PARAMS["ALPHA_ADW_UPPER"]

    def test_falsification_factor_documented(self):
        """Wave 2 main finding: ratio is in 10^14 — 10^15 range."""
        _, _, ratio = c_GW_natural_window_violation_factor()
        # Documented in paper25 — between 1e14 and 1e16
        assert 1e14 < ratio < 1e16


# =====================================================================
# Strengthening-pass tests (post-Wave-2 audit, 2026-04-25)
# =====================================================================
class TestStrengtheningPass:
    """Cross-checks for the Wave 2 strengthening-pass theorems."""

    def test_quarter_susceptibility_violates_cap_and_strict_half_bound(self):
        """At χ=1/4, both the speed cap and strict half-deviation bound fail."""
        deviation = c_GW_deviation_from_c(0.25)
        assert deviation == pytest.approx(-0.5, rel=1e-15)
        # The bundle's P3' is |Δ| < 1/2 (strict). At χ=1/4, |Δ| = 1/2 exactly.
        assert abs(deviation) >= 0.5  # P3' fails
        assert not ligo_constraint_check(deviation)

    def test_natural_endpoints_fail_and_compatible_window_is_inside_range(self):
        """Both adopted endpoints fail while the compatible interval contains unity."""
        chi_lo = GW_PARAMS["CHI_VEST_NATURAL_LOWER"]
        chi_hi = GW_PARAMS["CHI_VEST_NATURAL_UPPER"]
        cap = GW_PARAMS["C_GW_TWO_SIDED_CAP"]

        verdict_lo = ligo_compatibility_check(chi_lo)
        verdict_hi = ligo_compatibility_check(chi_hi)

        # Both endpoints fail LIGO
        assert not verdict_lo.ligo_satisfied
        assert not verdict_hi.ligo_satisfied

        # The GW170817-compatible window
        chi_lig_lo, chi_lig_hi = chi_vest_window_compatible_with_ligo(cap)
        # Endpoint exclusion coexists with intersection at the natural anchor.
        assert chi_lo < chi_lig_lo < 1.0 < chi_lig_hi < chi_hi
        assert chi_lo < chi_lig_lo or chi_lo > chi_lig_hi
        assert chi_hi < chi_lig_lo or chi_hi > chi_lig_hi

    def test_dispersion_within_ligo_iff_biconditional(self):
        """Lean: dispersion_within_ligo_iff. |γ·ω| ≤ tol ↔ |γ| ≤ tol/ω."""
        from src.core.constants import GW_PARAMS
        tol = GW_PARAMS["C_GW_TWO_SIDED_CAP"]
        omega = GW_PARAMS["GW170817_PEAK_FREQ_HZ"]
        threshold = tol / omega

        # Boundary: γ at threshold passes
        gamma_at_threshold = threshold
        result_at = dispersion_correction_from_GammaH(omega, gamma_at_threshold)
        assert abs(result_at) == pytest.approx(tol, rel=1e-12)

        # Just below: passes
        gamma_below = 0.5 * threshold
        result_below = dispersion_correction_from_GammaH(omega, gamma_below)
        assert abs(result_below) <= tol

        # Just above: fails
        gamma_above = 2.0 * threshold
        result_above = dispersion_correction_from_GammaH(omega, gamma_above)
        assert abs(result_above) > tol

    def test_vestigial_dispersion_below_ligo_at_inspiral_peak(self):
        """Lean: vestigial_dispersion_below_ligo_at_inspiral_peak.
        The chosen placeholder gamma=1e-30 makes the numerical product
        gamma*100 smaller than the cap. This tests neither a derived physical
        coefficient nor a matched 100 Hz correction or total deviation."""
        from src.core.constants import GW_PARAMS
        gamma = GW_PARAMS["GAMMA_H_VESTIGIAL_DEFAULT"]  # 1e-30
        omega = GW_PARAMS["GW170817_PEAK_FREQ_HZ"]      # 100
        tol = GW_PARAMS["C_GW_TWO_SIDED_CAP"]           # 3e-15

        result = dispersion_correction_from_GammaH(omega, gamma)
        # 1e-30 * 100 = 1e-28 ≪ 3e-15
        assert abs(result) <= tol
        # Verify the 13-orders-of-magnitude headroom
        assert abs(result) < 1e-25  # 3 orders of margin to demonstrate "well below"

    def test_p1_does_not_imply_p3prime(self):
        """P1 (positivity) does not imply P3' (sub-half-deviation).
        At chi=1/4 P1 holds while P3' and P2 fail. Conversely P3' implies
        sqrt(chi)>1/2 and hence P1; this is no two-way independence."""
        # P1 at χ=1/4: 0 < 1/4 ✓
        assert 1.0/4.0 > 0
        # P3' at χ=1/4: |sqrt(1/4) - 1| = 1/2, NOT < 1/2 ✗
        deviation = c_GW_deviation_from_c(0.25)
        assert not (abs(deviation) < 0.5)  # P3' fails

    def test_natural_endpoints_excluded_while_window_contains_unity(self):
        """The finite window is inside the adopted range and includes unity."""
        cap = GW_PARAMS["C_GW_TWO_SIDED_CAP"]
        chi_lo, chi_hi = chi_vest_window_compatible_with_ligo(cap)

        # Width of GW170817-compatible window
        ligo_window_width = chi_hi - chi_lo

        # Natural range
        natural_lo = GW_PARAMS["CHI_VEST_NATURAL_LOWER"]
        natural_hi = GW_PARAMS["CHI_VEST_NATURAL_UPPER"]
        natural_width = natural_hi - natural_lo

        # The interval widths differ by more than fourteen orders of magnitude.
        # ratio = natural / ligo ~ 9.9 / 1.2e-14 ~ 8e14
        ratio = natural_width / ligo_window_width
        assert ratio > 1e14
        # And the natural endpoints are outside the LIGO window
        assert natural_lo < chi_lo  # 0.1 < ~1
        assert natural_hi > chi_hi  # 10 > ~1
        assert natural_lo < chi_lo < 1.0 < chi_hi < natural_hi


class TestWindowNumericalPrecision:
    @pytest.mark.parametrize("cap", [
        0.0, 1e-18, 3e-15, 0.1, 0.5, math.nextafter(1.0, 0.0), 1.0, 2.0,
    ])
    def test_window_endpoints_against_exact_preimage(self, cap):
        tolerance = Fraction.from_float(cap)
        expected = (max(Fraction(0), 1 - tolerance) ** 2,
                    (1 + tolerance) ** 2)
        actual = chi_vest_window_compatible_with_ligo(cap)
        for value, reference in zip(actual, expected, strict=True):
            # One output ulp covers the squared term's intermediate rounding.
            assert abs(Fraction.from_float(value) - reference) <= Fraction.from_float(
                math.ulp(float(reference))
            )

    @pytest.mark.parametrize("cap", [-1.0, float("nan"), float("inf")])
    def test_invalid_caps_are_rejected(self, cap):
        with pytest.raises(ValueError, match="finite.*nonnegative"):
            chi_vest_window_compatible_with_ligo(cap)

    @pytest.mark.parametrize("chi", [
        math.nextafter(1.0, 0.0), math.nextafter(1.0, math.inf),
        0.999999999999994, 1.000000000000006,
        np.float32(1.0000001), np.float32(0.99999994),
        np.longdouble(1) + 4 * np.finfo(np.longdouble).eps,
    ])
    def test_near_unity_deviation_matches_high_precision_reference(self, chi):
        with localcontext() as context:
            context.prec = 80
            numerator, denominator = chi.as_integer_ratio()
            exact_chi = Decimal(numerator) / Decimal(denominator)
            reference = float(exact_chi.sqrt() - 1)
        assert c_GW_deviation_from_c(chi) == pytest.approx(
            reference, rel=3e-16, abs=0.0
        )

    def test_infinite_and_nan_deviation_behavior_is_preserved(self):
        assert math.isinf(c_GW_deviation_from_c(math.inf))
        assert math.isnan(c_GW_deviation_from_c(math.nan))

    def test_d3_width_ratio_uses_the_exact_algebraic_width(self):
        from papers.D3.tables import _chi_window_ratio

        cap = GW_PARAMS["C_GW_TWO_SIDED_CAP"]
        natural = (GW_PARAMS["CHI_VEST_NATURAL_UPPER"]
                   - GW_PARAMS["CHI_VEST_NATURAL_LOWER"])
        assert _chi_window_ratio() == pytest.approx(
            natural / (4 * cap), rel=3e-16, abs=0.0
        )


class TestL1HeadlineNumerics:
    """Independent references for the current L1 abstract and figure caption.

    The Abbott fixture is source-qualified, not a PDF parser: ApJL 848 L13
    (2017), DOI 10.3847/2041-8213/aa920c, printed p.6, Sec.4.1, Eq.(1).
    The adopted susceptibility range is a model input, not an observation.
    """

    def test_conservative_cap_encloses_source_asymmetric_interval(self):
        # Catch a wrong sign, exponent, or use of the tighter positive arm.
        from src.core.provenance import PARAMETER_PROVENANCE

        source_lower, source_upper = Decimal('-3e-15'), Decimal('7e-16')
        for arm, reference in [('LOWER', source_lower), ('UPPER', source_upper)]:
            record = PARAMETER_PROVENANCE[f'GW.C_GW_DEVIATION_{arm}_BOUND']
            assert record['value'] == float(reference)
            assert record['doi'] == '10.3847/2041-8213/aa920c'
            assert 'Eq. (1)' in record['source']
        cap = max(abs(source_lower), abs(source_upper))
        assert GW_PARAMS['C_GW_DEVIATION_LOWER_BOUND'] == float(source_lower)
        assert GW_PARAMS['C_GW_DEVIATION_UPPER_BOUND'] == float(source_upper)
        assert GW_PARAMS['C_GW_TWO_SIDED_CAP'] == float(cap)
        for delta in (source_lower, Decimal(0), source_upper, cap):
            assert ligo_constraint_check(float(delta))
        assert not ligo_constraint_check(float(2 * cap))
        assert not ligo_constraint_check(float(-2 * cap))

    def test_adopted_endpoints_have_projected_not_measured_provenance(self):
        from src.core.provenance import PARAMETER_PROVENANCE

        for suffix, reference in [('LOWER', Decimal('0.1')), ('UPPER', Decimal('10'))]:
            key = f'CHI_VEST_NATURAL_{suffix}'
            record = PARAMETER_PROVENANCE[f'GW.{key}']
            assert GW_PARAMS[key] == float(reference)
            assert record['value'] == float(reference)
            assert record['tier'] == 'PROJECTED'

    def test_decimal_interval_width_and_fourteen_order_confinement(self):
        from papers.D3.tables import _chi_window_ratio

        # Exact declared decimals: avoid inferring the width by subtracting
        # rounded binary endpoints near unity (a different numerical object).
        tau = Fraction('3e-15')
        lower, upper = (1 - tau) ** 2, (1 + tau) ** 2
        width = upper - lower
        adopted_width = Fraction('10') - Fraction('0.1')
        assert width == Fraction('1.2e-14') == 4 * tau
        assert adopted_width == Fraction('9.9')
        ratio = adopted_width / width
        assert ratio > 10**14
        with localcontext() as context:
            context.prec = 80
            assert (Decimal(ratio.numerator) / Decimal(ratio.denominator)).log10() > 14
        assert _chi_window_ratio() == pytest.approx(float(ratio), rel=3e-16, abs=0)
        actual_lower, actual_upper = chi_vest_window_compatible_with_ligo()
        for actual, reference in [(actual_lower, lower), (actual_upper, upper)]:
            assert abs(Fraction.from_float(actual) - reference) <= Fraction.from_float(
                math.ulp(float(reference))
            ) / 2
        rounded_width = Fraction.from_float(actual_upper) - Fraction.from_float(actual_lower)
        rounding_budget = sum(Fraction.from_float(math.ulp(x)) / 2
                              for x in (actual_lower, actual_upper))
        assert abs(rounded_width - width) <= rounding_budget
        assert Fraction('0.1') < lower < 1 < upper < Fraction('10')

    @pytest.mark.parametrize('chi_text,caption_display,factor_display', [
        ('0.1', '-0.68', '2.28E+14'),
        ('10', '2.16', '7.21E+14'),
    ])
    def test_endpoint_deviation_rounding_and_violation_factor(
        self, chi_text, caption_display, factor_display,
    ):
        # Catch incorrect endpoint arithmetic, sign, cap or display rounding.
        with localcontext() as context:
            context.prec = 80
            reference = Decimal(chi_text).sqrt() - 1
            factor = abs(reference) / Decimal('3e-15')
            assert reference.quantize(Decimal('0.01')) == Decimal(caption_display)
            assert factor.quantize(Decimal('1e12')) == Decimal(factor_display)
        verdict = ligo_compatibility_check(float(chi_text))
        assert verdict.deviation == pytest.approx(float(reference), rel=3e-16, abs=0)
        assert verdict.violation_factor == pytest.approx(float(factor), rel=3e-16, abs=0)
        assert not verdict.ligo_satisfied
        assert verdict.violation_factor > 1e14
        assert f'{verdict.deviation:.2f}' == caption_display
        summary = ligo_falsification_summary()
        suffix = 'lower' if chi_text == '0.1' else 'upper'
        assert summary[f'delta_{suffix}'] == pytest.approx(float(reference), rel=3e-16, abs=0)
        assert summary[f'violation_ratio_{suffix}'] == pytest.approx(float(factor), rel=3e-16, abs=0)

    def test_unity_is_zero_deviation_anchor_with_other_compatible_points(self):
        assert GW_PARAMS['CHI_VEST_DEFAULT'] == 1.0
        assert c_GW_deviation_from_c(1.0) == 0.0
        assert c_GW_at_natural_anchor() == 299792458.0
        # Two non-unity interior witnesses rule out a singleton interpretation.
        with localcontext() as context:
            context.prec = 80
            tau = Decimal('3e-15')
            for chi in (math.nextafter(1.0, 0.0), math.nextafter(1.0, math.inf)):
                reference = Decimal.from_float(chi).sqrt() - 1
                assert 0 < abs(reference) < tau
                verdict = ligo_compatibility_check(chi)
                assert verdict.ligo_satisfied
                assert verdict.deviation == pytest.approx(float(reference), rel=3e-16, abs=0)


class TestL1FigureScientificInputs:
    """Plotly data and numeric labels; PNG custody/render acceptance is separate."""

    def test_curve_cap_band_adopted_rectangle_and_anchor(self):
        from src.core.visualizations import fig_c_GW_vs_ligo_constraint

        figure = fig_c_GW_vs_ligo_constraint()
        assert len(figure.data) == 3
        curve, band, anchor = figure.data
        assert len(curve.x) == len(curve.y) > 0
        x_lower, x_upper = min(curve.x), max(curve.x)
        assert 0 < x_lower < 0.1 < 1.0 < 10.0 < x_upper
        with localcontext() as context:
            context.prec = 80
            for chi, delta in zip(curve.x, curve.y, strict=True):
                reference = Decimal.from_float(float(chi)).sqrt() - 1
                assert delta == pytest.approx(float(reference), rel=4e-16, abs=0)
        assert tuple(band.x) == (x_lower, x_upper, x_upper, x_lower)
        assert tuple(band.y) == (3e-15, 3e-15, -3e-15, -3e-15)
        assert band.fill == 'toself'
        rectangle, = [shape for shape in figure.layout.shapes if shape.type == 'rect']
        assert (rectangle.x0, rectangle.x1) == (0.1, 10.0)
        assert rectangle.y0 <= min(curve.y)
        assert rectangle.y1 >= max(curve.y)
        zero, = [shape for shape in figure.layout.shapes if shape.type == 'line']
        assert (zero.x0, zero.x1, zero.y0, zero.y1) == (x_lower, x_upper, 0.0, 0.0)
        assert tuple(anchor.x) == (1.0,)
        assert tuple(anchor.y) == (0.0,)
        assert anchor.marker.symbol == 'star'
        assert figure.layout.xaxis.type == 'log'
        assert tuple(figure.layout.xaxis.range) == pytest.approx(
            (math.log10(x_lower), math.log10(x_upper)), rel=3e-16, abs=0
        )

    def test_endpoint_callouts_and_unresolved_width_at_declared_scale(self):
        from src.core.visualizations import fig_c_GW_vs_ligo_constraint

        figure = fig_c_GW_vs_ligo_constraint()
        range_label, = [a for a in figure.layout.annotations if not a.showarrow]
        assert '0.1' in range_label.text and '10' in range_label.text
        assert range_label.x == 0
        callouts = sorted((a for a in figure.layout.annotations if a.showarrow), key=lambda a: a.x)
        assert len(callouts) == 2
        with localcontext() as context:
            context.prec = 80
            for annotation, chi_text in zip(callouts, ('0.1', '10'), strict=True):
                chi = Decimal(chi_text)
                delta = chi.sqrt() - 1
                factor = abs(delta) / Decimal('3e-15')
                assert annotation.x == float(chi.log10())
                assert annotation.y == pytest.approx(float(delta), rel=3e-16, abs=0)
                assert f'χ={chi_text}' in annotation.text
                assert f'{delta:.3f}' in annotation.text
                assert f'{float(factor):.1e}' in annotation.text
            tau = Decimal('3e-15')
            lower, upper = (1 - tau)**2, (1 + tau)**2
            x_pixels = figure.layout.width - figure.layout.margin.l - figure.layout.margin.r
            y_pixels = figure.layout.height - figure.layout.margin.t - figure.layout.margin.b
            x_span = figure.layout.xaxis.range[1] - figure.layout.xaxis.range[0]
            y_span = figure.layout.yaxis.range[1] - figure.layout.yaxis.range[0]
            assert float(upper.log10() - lower.log10()) * x_pixels / x_span < 1
            assert float(2 * tau) * y_pixels / y_span < 1
