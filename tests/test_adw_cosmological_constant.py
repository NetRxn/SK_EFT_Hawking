"""Tests for src.dark_sector.adw_cosmological_constant (Phase 5x Wave 3).

Cross-checks the Python implementation against the Lean-proved
facts in ``CosmologicalConstant.lean``:

- T_dS_double_TGH: T_dS = 2 × T_GH exactly.
- T_dS_pos, T_GH_pos: both positive for H > 0.
- T_dS_gt_T_GH: T_dS is strictly larger than T_GH.
- quartic_CW_critical_point: for V(C)=-A·C²+B·C⁴ at C² = A/(2B),
  V(C) = -A²/(4B).
- quartic_CW_negative: the critical-point value is negative.
- lambda_magnitude_ratio: (T_p / T_o)⁴.
"""

from __future__ import annotations

import math

import pytest

from src.dark_sector.adw_cosmological_constant import (
    LAMBDA_RATIO_ADW_OBSERVED,
    T_ADW_PREDICTED_meV,
    T_OBSERVED_meV,
    CosmologicalConstantAssessment,
    KlinkhamerVolovikPrediction,
    adw_predicted_vs_observed_energy_ratio,
    assess_cosmological_constant_status,
    de_sitter_temperature_volovik,
    gibbons_hawking_temperature,
    klinkhamer_volovik_prediction,
    lambda_energy_density_meV4,
    lambda_magnitude_ratio,
    quartic_CW_critical_point,
    volovik_gh_ratio,
)


class TestDeSitterTemperatures:
    """Lean anchor: T_dS_double_TGH, T_dS_pos, T_GH_pos."""

    @pytest.mark.parametrize("H", [0.1, 1.0, 67.4, 1e18])
    def test_gibbons_hawking_formula(self, H):
        assert gibbons_hawking_temperature(H) == pytest.approx(H / (2.0 * math.pi))

    @pytest.mark.parametrize("H", [0.1, 1.0, 67.4, 1e18])
    def test_de_sitter_volovik_formula(self, H):
        assert de_sitter_temperature_volovik(H) == pytest.approx(H / math.pi)

    @pytest.mark.parametrize("H", [0.1, 1.0, 67.4, 1e18])
    def test_double_temperature_relation(self, H):
        """Lean T_dS_double_TGH: T_dS = 2 × T_GH exactly."""
        ratio = de_sitter_temperature_volovik(H) / gibbons_hawking_temperature(H)
        assert ratio == pytest.approx(2.0)

    def test_ratio_constant(self):
        """The T_dS/T_GH ratio is exactly 2, independent of H."""
        assert volovik_gh_ratio() == 2.0

    @pytest.mark.parametrize("H", [0.01, 1.0, 100.0])
    def test_both_positive(self, H):
        """Lean T_dS_pos, T_GH_pos: both > 0 for H > 0."""
        assert gibbons_hawking_temperature(H) > 0
        assert de_sitter_temperature_volovik(H) > 0

    @pytest.mark.parametrize("H", [0.01, 1.0, 100.0])
    def test_volovik_strictly_larger(self, H):
        """Lean T_dS_gt_T_GH: T_dS > T_GH for H > 0."""
        assert de_sitter_temperature_volovik(H) > gibbons_hawking_temperature(H)


class TestLambdaMagnitude:
    """Lean anchor: lambda_magnitude_ratio."""

    def test_canonical_adw_vs_observed(self):
        """(2.8/2.3)⁴ ≈ 2.196."""
        expected = (T_ADW_PREDICTED_meV / T_OBSERVED_meV) ** 4
        assert lambda_magnitude_ratio(
            T_ADW_PREDICTED_meV, T_OBSERVED_meV
        ) == pytest.approx(expected)

    def test_equal_inputs_give_one(self):
        """Lean lambda_magnitude_ratio_exact: identical inputs give 1."""
        assert lambda_magnitude_ratio(2.3, 2.3) == pytest.approx(1.0)
        assert lambda_magnitude_ratio(42.0, 42.0) == pytest.approx(1.0)

    def test_canonical_constant_matches(self):
        """Module-level constant equals the canonical ADW ratio."""
        assert LAMBDA_RATIO_ADW_OBSERVED == pytest.approx(
            adw_predicted_vs_observed_energy_ratio()
        )

    def test_ratio_in_expected_range(self):
        """W1b hook: 20% energy-scale accuracy gives a ρ ratio ~2.2."""
        ratio = adw_predicted_vs_observed_energy_ratio()
        assert 2.0 < ratio < 2.5

    def test_rejects_nonpositive_T_predicted(self):
        with pytest.raises(ValueError):
            lambda_magnitude_ratio(0.0, 2.3)
        with pytest.raises(ValueError):
            lambda_magnitude_ratio(-1.0, 2.3)

    def test_rejects_nonpositive_T_observed(self):
        with pytest.raises(ValueError):
            lambda_magnitude_ratio(2.8, 0.0)
        with pytest.raises(ValueError):
            lambda_magnitude_ratio(2.8, -1.0)

    def test_lambda_energy_density_quartic(self):
        """ρ_vac ≈ T⁴ for T > 0."""
        assert lambda_energy_density_meV4(2.3) == pytest.approx(2.3**4)
        assert lambda_energy_density_meV4(2.8) == pytest.approx(2.8**4)

    def test_lambda_energy_density_rejects_zero(self):
        with pytest.raises(ValueError):
            lambda_energy_density_meV4(0.0)


class TestQuarticCW:
    """Lean anchor: quartic_CW_critical_point, quartic_CW_negative."""

    def test_unit_coefficients(self):
        """For A=B=1: C₀² = 1/2, V₀ = -1/4."""
        C0, V0 = quartic_CW_critical_point(1.0, 1.0)
        assert C0**2 == pytest.approx(0.5)
        assert V0 == pytest.approx(-0.25)

    @pytest.mark.parametrize("A,B", [(1.0, 1.0), (2.0, 3.0), (0.1, 10.0)])
    def test_critical_point_identity(self, A, B):
        """Lean quartic_CW_critical_point: V(C) = -A²/(4B) at C² = A/(2B)."""
        C0, V0 = quartic_CW_critical_point(A, B)
        # Verify C0² = A/(2B)
        assert C0**2 == pytest.approx(A / (2.0 * B))
        # Verify V at C0 = -A·C0² + B·C0⁴
        V_direct = -A * C0**2 + B * C0**4
        assert V_direct == pytest.approx(V0)
        # Verify identity: V0 = -A²/(4B)
        assert V0 == pytest.approx(-(A**2) / (4.0 * B))

    @pytest.mark.parametrize("A,B", [(1.0, 1.0), (2.0, 3.0), (0.1, 10.0)])
    def test_critical_point_negative(self, A, B):
        """Lean quartic_CW_negative: V₀ < 0 for A, B > 0."""
        _, V0 = quartic_CW_critical_point(A, B)
        assert V0 < 0

    def test_rejects_nonpositive_A(self):
        with pytest.raises(ValueError):
            quartic_CW_critical_point(0.0, 1.0)
        with pytest.raises(ValueError):
            quartic_CW_critical_point(-1.0, 1.0)

    def test_rejects_nonpositive_B(self):
        with pytest.raises(ValueError):
            quartic_CW_critical_point(1.0, 0.0)
        with pytest.raises(ValueError):
            quartic_CW_critical_point(1.0, -1.0)


class TestKlinkhamerVolovikW1b:
    """⚡W1b corrected Klinkhamer-Volovik prediction.

    These tests enforce the W1b-corrected claim (KV does NOT explain
    DESI DR2 evolving-DE signal). If any of these flip, it indicates
    an unintended regression back to the pre-W1b claim.
    """

    def test_frozen_plateau(self):
        """W1b: (w₀, wₐ) = (-1, 0) at current epoch."""
        kv = klinkhamer_volovik_prediction()
        assert kv.w0 == -1.0
        assert kv.wa == 0.0

    def test_oscillation_is_planck_scale(self):
        """W1b: oscillations have period ~10⁻⁴⁴ s, not cosmological."""
        kv = klinkhamer_volovik_prediction()
        assert kv.oscillation_period_seconds <= 1e-40

    def test_w_effective_zero(self):
        """W1b: time-averaged w_eff = 0 (CDM-like), not evolving."""
        kv = klinkhamer_volovik_prediction()
        assert kv.w_effective_time_averaged == 0.0

    def test_desi_exclusion_significant(self):
        """W1b: DESI DR2 excludes at Pantheon+ ≥ 2σ, DESY5 ≥ 3σ."""
        kv = klinkhamer_volovik_prediction()
        assert kv.desi_dr2_exclusion_sigma_pantheon_plus >= 2.0
        assert kv.desi_dr2_exclusion_sigma_desy5 >= 3.0


class TestCosmologicalConstantAssessment:
    """Structured W1b-corrected status summary."""

    def test_kv_does_not_explain_desi(self):
        """⚡W1b: this MUST stay False; pre-W1b claim was True."""
        a = assess_cosmological_constant_status()
        assert a.kv_explains_desi is False

    def test_lambda_ratio_matches_canonical(self):
        a = assess_cosmological_constant_status()
        assert a.lambda_ratio_adw_observed == pytest.approx(
            adw_predicted_vs_observed_energy_ratio()
        )

    def test_accuracy_around_20_percent(self):
        """Surviving W1b hook: ~20% on the energy scale."""
        a = assess_cosmological_constant_status()
        assert 15.0 < a.lambda_accuracy_percent < 25.0

    def test_surviving_hooks_populated(self):
        """The assessment must list the W1b-corrected surviving hooks."""
        a = assess_cosmological_constant_status()
        assert len(a.surviving_hook_notes) >= 3
        combined = " ".join(a.surviving_hook_notes).lower()
        assert "planck" in combined or "oscillation" in combined
        assert "qcd" in combined
        assert "desi" in combined

    def test_assessment_types(self):
        a = assess_cosmological_constant_status()
        assert isinstance(a, CosmologicalConstantAssessment)
        assert isinstance(a.kv_prediction, KlinkhamerVolovikPrediction)
