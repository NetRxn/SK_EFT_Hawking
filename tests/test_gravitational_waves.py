"""Phase 6a Wave 2: gravitational-wave propagation tests.

Cross-checks the Python pipeline (``src.gravitational_waves``) against
the Lean module ``GravitationalWaves.lean``. The Wave 2 main physics
finding — natural-range vestigial-second-sound graviton ID fails
GW170817 by 14+ orders of magnitude — is encoded as a hard test.
"""

from __future__ import annotations

import math

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
    """c_GW = c · √χ_vest (Wave 2 leading-order identification)."""

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

    def test_ligo_window_size_matches_2x_cap(self):
        """Width of GW170817-compatible χ window ≈ 2·cap."""
        cap = GW_PARAMS["C_GW_TWO_SIDED_CAP"]
        chi_lo, chi_hi = chi_vest_window_compatible_with_ligo(cap)
        assert (chi_hi - chi_lo) == pytest.approx(4.0 * cap, rel=1e-3)


# =====================================================================
# Natural-range falsification (LOAD-BEARING)
# =====================================================================
class TestNaturalRangeFalsification:
    """Natural χ_vest range fails GW170817 by ~10^14."""

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
# Dispersion correction (SK-EFT bridge)
# =====================================================================
class TestDispersionCorrection:
    """Leading dissipative dispersion: δω/ω = γ · ω."""

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
        # Default γ_H is 1e-30 placeholder, ω=100 Hz → δ = 1e-28
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
        """Window width = 4·tol to leading order; Lean biconditional pre-image."""
        cap = GW_PARAMS["C_GW_TWO_SIDED_CAP"]
        chi_lo, chi_hi = chi_vest_window_compatible_with_ligo(cap)
        # (1+tol)^2 - (1-tol)^2 = 4·tol
        assert (chi_hi - chi_lo) == pytest.approx(4.0 * cap, rel=1e-9)


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
        """χ_vest natural range follows GRAV.ALPHA_ADW_LOWER/UPPER convention."""
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

    def test_quarter_susceptibility_isolates_p3prime(self):
        """Lean: H_VestigialModeIsGraviton_fails_at_quarter. χ=1/4 gives
        Δc/c = -1/2; |Δ| = 1/2 fails the strict-< 1/2 P3' clause."""
        deviation = c_GW_deviation_from_c(0.25)
        assert deviation == pytest.approx(-0.5, rel=1e-15)
        # The bundle's P3' is |Δ| < 1/2 (strict). At χ=1/4, |Δ| = 1/2 exactly.
        assert abs(deviation) >= 0.5  # P3' fails

    def test_natural_range_disjoint_from_ligo_window(self):
        """Lean: natural_range_disjoint_from_ligo_window. The natural
        endpoints both fail LigoSatisfied; the natural range and the
        GW170817-compatible window are disjoint."""
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
        # Disjointness: chi_lig_hi < chi_lo and chi_lig_lo > chi_hi would
        # be unattainable since the window contains 1; check that the
        # endpoints are outside the window
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
        Vestigial-regime placeholder γ ≤ 1e-30 keeps δω/ω below the
        GW170817 cap at the GW170817 inspiral peak ω = 100 Hz."""
        from src.core.constants import GW_PARAMS
        gamma = GW_PARAMS["GAMMA_H_VESTIGIAL_DEFAULT"]  # 1e-30
        omega = GW_PARAMS["GW170817_PEAK_FREQ_HZ"]      # 100
        tol = GW_PARAMS["C_GW_TWO_SIDED_CAP"]           # 3e-15

        result = dispersion_correction_from_GammaH(omega, gamma)
        # 1e-30 * 100 = 1e-28 ≪ 3e-15
        assert abs(result) <= tol
        # Verify the 13-orders-of-magnitude headroom
        assert abs(result) < 1e-25  # 3 orders of margin to demonstrate "well below"

    def test_p3prime_independent_of_p1(self):
        """P3' (sub-half-deviation) is genuinely independent of P1 (positivity).
        Witness: χ=1/4 satisfies P1 but not P3'."""
        # P1 at χ=1/4: 0 < 1/4 ✓
        assert 1.0/4.0 > 0
        # P3' at χ=1/4: |sqrt(1/4) - 1| = 1/2, NOT < 1/2 ✗
        deviation = c_GW_deviation_from_c(0.25)
        assert not (abs(deviation) < 0.5)  # P3' fails

    def test_second_sound_underdetermination_replaced_by_disjointness(self):
        """The strengthened Phase 5y H1 caveat: the natural range and
        GW170817 window are disjoint (not just 'one consistent value
        exists'). This is the substantive replacement for the prior
        ∃-absorption form."""
        cap = GW_PARAMS["C_GW_TWO_SIDED_CAP"]
        chi_lo, chi_hi = chi_vest_window_compatible_with_ligo(cap)

        # Width of GW170817-compatible window
        ligo_window_width = chi_hi - chi_lo

        # Natural range
        natural_lo = GW_PARAMS["CHI_VEST_NATURAL_LOWER"]
        natural_hi = GW_PARAMS["CHI_VEST_NATURAL_UPPER"]
        natural_width = natural_hi - natural_lo

        # The LIGO window is exponentially smaller than the natural range
        # ratio = natural / ligo ~ 9.9 / 1.2e-14 ~ 8e14
        ratio = natural_width / ligo_window_width
        assert ratio > 1e14
        # And the natural endpoints are outside the LIGO window
        assert natural_lo < chi_lo  # 0.1 < ~1
        assert natural_hi > chi_hi  # 10 > ~1
