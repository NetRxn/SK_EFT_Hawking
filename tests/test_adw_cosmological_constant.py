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

import json
import math
from dataclasses import FrozenInstanceError, asdict

import pytest

from src.dark_sector.adw_cosmological_constant import (
    LAMBDA_RATIO_ADW_OBSERVED,
    T_ADW_PREDICTED_meV,
    T_OBSERVED_meV,
    CosmologicalConstantAssessment,
    KlinkhamerVolovikBranch,
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

    def test_legacy_example_is_supplied_scale_arithmetic(self):
        """Legacy values exercise arithmetic, not a physical prediction."""
        expected = (T_ADW_PREDICTED_meV / T_OBSERVED_meV) ** 4
        assert lambda_magnitude_ratio(
            T_ADW_PREDICTED_meV, T_OBSERVED_meV
        ) == pytest.approx(expected)

    def test_equal_inputs_give_one(self):
        """Lean lambda_magnitude_ratio_exact: identical inputs give 1."""
        assert lambda_magnitude_ratio(2.3, 2.3) == pytest.approx(1.0)
        assert lambda_magnitude_ratio(42.0, 42.0) == pytest.approx(1.0)

    def test_canonical_constant_matches(self):
        """Legacy example constant is arithmetic, not a default prediction."""
        assert LAMBDA_RATIO_ADW_OBSERVED == pytest.approx(
            lambda_magnitude_ratio(T_ADW_PREDICTED_meV, T_OBSERVED_meV)
        )

    def test_default_helper_leaves_physical_prediction_uncomputed(self):
        assert adw_predicted_vs_observed_energy_ratio() is None

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
        """Supplied-scale fourth-power arithmetic, not a vacuum model."""
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


class TestKlinkhamerVolovikSourceScope:
    """Protect source model/regime, effective EoS, CPL and likelihood distinctions."""

    @pytest.mark.parametrize("branch", list(KlinkhamerVolovikBranch))
    def test_branch_selection_cannot_manufacture_a_model_fit(self, branch):
        kv = klinkhamer_volovik_prediction(branch=branch)
        assert kv.branch is branch
        assert kv.w0 is None and kv.wa is None
        assert kv.desi_fit_status == "not_computed"
        assert kv.desi_dr2_exclusion_sigma_pantheon_plus is None
        assert kv.desi_dr2_exclusion_sigma_desy5 is None
        assert kv.oscillation_period_seconds is None
        assert kv.clustering_status == "not_established"

    def test_equilibrium_effective_cdm_is_distinct_from_bare_field_and_de_cpl(self):
        kv = klinkhamer_volovik_prediction(
            branch=KlinkhamerVolovikBranch.DYNAMIC_2008_EQUILIBRIUM
        )
        assert kv.source_arxiv == "0806.2805v7"
        assert kv.bare_field_w == -1.0
        assert kv.w_effective_time_averaged == 0.0
        assert kv.w0 is None and kv.wa is None

    @pytest.mark.parametrize("branch", [
        KlinkhamerVolovikBranch.UNSELECTED,
        KlinkhamerVolovikBranch.DYNAMIC_2008_PERTURBED,
        KlinkhamerVolovikBranch.STEPWISE_2011_PLATEAU,
    ])
    def test_equilibrium_effective_number_does_not_leak_to_other_regimes(self, branch):
        assert klinkhamer_volovik_prediction(branch=branch).w_effective_time_averaged is None

    def test_plateau_scenario_is_not_silently_replaced_by_2008_equilibrium(self):
        kv = klinkhamer_volovik_prediction(
            branch=KlinkhamerVolovikBranch.STEPWISE_2011_PLATEAU
        )
        assert kv.source_arxiv == "1102.3152v4"
        assert kv.bare_field_w is None
        assert kv.w0 is None and kv.wa is None

    def test_legacy_no_argument_call_does_not_select_a_physical_model(self):
        kv = klinkhamer_volovik_prediction()
        assert kv.branch is KlinkhamerVolovikBranch.UNSELECTED
        assert kv.source_arxiv is None and kv.bare_field_w is None

    @pytest.mark.parametrize("constructor", [
        KlinkhamerVolovikPrediction, klinkhamer_volovik_prediction,
    ])
    @pytest.mark.parametrize("invalid", ["unqualified_frozen_plateau", None, 0])
    def test_invalid_branch_is_rejected(self, constructor, invalid):
        with pytest.raises(ValueError):
            constructor(branch=invalid)

    @pytest.mark.parametrize("supplied", [
        {"w0": -1.0}, {"wa": 0.0},
        {"desi_dr2_exclusion_sigma_pantheon_plus": 2.9},
        {"desi_dr2_exclusion_sigma_desy5": 4.4},
        {"desi_fit_status": "accepted"},
        {"oscillation_period_seconds": 1e-44},
        {"w_effective_time_averaged": 0.0},
    ])
    def test_constructor_cannot_promote_supplied_values_to_a_fit(self, supplied):
        with pytest.raises(TypeError):
            KlinkhamerVolovikPrediction(**supplied)

    def test_source_report_is_frozen(self):
        kv = klinkhamer_volovik_prediction()
        with pytest.raises(FrozenInstanceError):
            kv.w0 = -1.0


class TestCosmologicalConstantAssessment:
    """Unknown model-fit status must survive reporting and the actual consumer."""

    def test_uncomputed_is_not_reported_as_rejection_or_acceptance(self):
        a = assess_cosmological_constant_status()
        assert a.kv_explains_desi is None
        assert a.kv_desi_fit_status == "not_computed"
        encoded = asdict(a)
        assert encoded["kv_explains_desi"] is None
        assert encoded["kv_prediction"]["w0"] is None
        assert encoded["kv_prediction"]["desi_fit_status"] == "not_computed"

    def test_default_magnitude_is_explicitly_unknown(self):
        a = assess_cosmological_constant_status()
        assert a.lambda_ratio_adw_observed is None
        assert a.lambda_accuracy_percent is None
        assert a.magnitude_status == "not_computed"
        assert a.adw_prediction_meV is None
        assert asdict(a)["magnitude_inputs_meV"] is None

    def test_supplied_scales_do_not_become_a_physical_prediction(self):
        a = assess_cosmological_constant_status(magnitude_inputs_meV=(4.0, 2.0))
        assert a.lambda_ratio_adw_observed == pytest.approx(16.0)
        assert a.lambda_accuracy_percent == pytest.approx(100.0)
        assert a.magnitude_status == "supplied_input_comparison"
        assert a.adw_prediction_meV is None

    @pytest.mark.parametrize("branch", list(KlinkhamerVolovikBranch))
    def test_notes_do_not_reintroduce_exclusion_or_alternative_ranking(self, branch):
        notes = " ".join(assess_cosmological_constant_status(branch=branch).surviving_hook_notes).lower()
        assert "not computed" in notes
        assert "independent provenance" in notes
        assert "2.9" not in notes and "4.4" not in notes
        assert "strongest" not in notes

    @pytest.mark.parametrize("branch", list(KlinkhamerVolovikBranch))
    def test_actual_synthesis_preserves_unknown_and_unrelated_reports(self, branch):
        from src.dark_sector.synthesis import phase5x_upstream_wave_reports

        default = phase5x_upstream_wave_reports()
        selected = phase5x_upstream_wave_reports(kv_branch=branch)
        assert selected.keys() == default.keys()
        for key in default.keys() - {"cosmological_constant"}:
            assert selected[key] == default[key]
        cc = selected["cosmological_constant"]
        assert cc.kv_prediction.branch is branch
        assert cc.kv_desi_fit_status == "not_computed"
        assert cc.kv_explains_desi is None
        assert cc.kv_prediction.w0 is None and cc.kv_prediction.wa is None
        assert default["cosmological_constant"].kv_prediction.branch is KlinkhamerVolovikBranch.UNSELECTED

    def test_assessment_types(self):
        a = assess_cosmological_constant_status()
        assert isinstance(a, CosmologicalConstantAssessment)
        assert isinstance(a.kv_prediction, KlinkhamerVolovikPrediction)


class TestADWMagnitudeInputContract:
    @pytest.mark.parametrize("inputs,ratio,deviation", [((4.0, 2.0), 16.0, 100.0), ((2.0, 4.0), 0.0625, 50.0)])
    def test_explicit_comparison_is_not_tuned_to_old_accuracy_band(self, inputs, ratio, deviation):
        a = assess_cosmological_constant_status(magnitude_inputs_meV=inputs)
        assert a.magnitude_inputs_meV == inputs
        assert a.lambda_ratio_adw_observed == pytest.approx(ratio)
        assert a.lambda_accuracy_percent == pytest.approx(deviation)
        assert a.magnitude_status == "supplied_input_comparison"
        assert asdict(a)["adw_prediction_meV"] is None

    def test_partial_inputs_are_not_completed_from_legacy_constants(self):
        with pytest.raises(ValueError):
            adw_predicted_vs_observed_energy_ratio(candidate_scale_meV=4.0)
        with pytest.raises(ValueError):
            adw_predicted_vs_observed_energy_ratio(reference_scale_meV=2.0)

    @pytest.mark.parametrize("bad", [0.0, -1.0, float("nan"), float("inf")])
    @pytest.mark.parametrize("reference_bad", [False, True])
    def test_report_rejects_invalid_scale_on_either_side(self, bad, reference_bad):
        inputs = (2.0, bad) if reference_bad else (bad, 2.0)
        with pytest.raises(ValueError):
            assess_cosmological_constant_status(magnitude_inputs_meV=inputs)

    def test_fourth_power_metric_prefix_covariance(self):
        # 1000 meV = 1 eV; this is a prefix conversion, not J/m^3.
        assert lambda_energy_density_meV4(1000.0) * 1e-12 == pytest.approx(1.0)
        assert lambda_energy_density_meV4(1.0) * 1e-12 == pytest.approx(1e-12, abs=0.0)

    def test_constructor_cannot_inject_an_independent_prediction(self):
        with pytest.raises(TypeError):
            CosmologicalConstantAssessment(
                kv_prediction=klinkhamer_volovik_prediction(), surviving_hook_notes=(),
                adw_prediction_meV=2.8,
            )

    @pytest.mark.parametrize("branch", list(KlinkhamerVolovikBranch))
    def test_actual_synthesis_preserves_kv_and_unrelated_reports(self, branch):
        from src.dark_sector.synthesis import phase5x_upstream_wave_reports

        default = phase5x_upstream_wave_reports(kv_branch=branch)
        supplied = phase5x_upstream_wave_reports(kv_branch=branch, adw_magnitude_inputs_meV=(4.0, 2.0))
        assert supplied.keys() == default.keys()
        for key in default.keys() - {"cosmological_constant"}:
            assert supplied[key] == default[key]
        a, b = supplied["cosmological_constant"], default["cosmological_constant"]
        assert a.kv_prediction == b.kv_prediction
        assert a.kv_desi_fit_status == b.kv_desi_fit_status
        assert a.kv_explains_desi is None
        assert b.lambda_ratio_adw_observed is None
        assert a.lambda_ratio_adw_observed == pytest.approx(16.0)
        assert a.adw_prediction_meV is None and b.adw_prediction_meV is None


class TestADWImmutableInputRecord:
    @staticmethod
    def _report(entrypoint, inputs):
        if entrypoint == "constructor":
            return CosmologicalConstantAssessment(
                kv_prediction=klinkhamer_volovik_prediction(),
                surviving_hook_notes=(), magnitude_inputs_meV=inputs,
            )
        if entrypoint == "factory":
            return assess_cosmological_constant_status(magnitude_inputs_meV=inputs)
        from src.dark_sector.synthesis import phase5x_upstream_wave_reports

        return phase5x_upstream_wave_reports(
            adw_magnitude_inputs_meV=inputs,
        )["cosmological_constant"]

    @pytest.mark.parametrize("entrypoint", ["constructor", "factory", "synthesis"])
    def test_mutable_caller_pair_is_rejected(self, entrypoint):
        inputs = [4.0, 2.0]
        with pytest.raises(ValueError, match="two-element tuple"):
            self._report(entrypoint, inputs)
        inputs[0] = 2.0
        # No successful record retains this caller-owned list.
        with pytest.raises(ValueError, match="two-element tuple"):
            self._report(entrypoint, inputs)

    @pytest.mark.parametrize("entrypoint", ["constructor", "factory", "synthesis"])
    @pytest.mark.parametrize("inputs", [
        (), (4.0,), (4.0, 2.0, 1.0), "42", {"candidate": 4.0, "reference": 2.0},
        (None, None), (None, 2.0), (4.0, None), (True, 2.0), (4.0, "2"),
        ([4.0], 2.0), (4.0, [2.0]),
    ])
    def test_malformed_explicit_pair_rejected_before_arithmetic(self, entrypoint, inputs):
        with pytest.raises(ValueError):
            self._report(entrypoint, inputs)

    @pytest.mark.parametrize("entrypoint", ["constructor", "factory", "synthesis"])
    def test_nonbuiltin_numeric_scalars_are_not_silently_adopted(self, entrypoint):
        class ExternalFloat(float):
            pass

        with pytest.raises(ValueError, match="builtin int or float"):
            self._report(entrypoint, (ExternalFloat(4.0), 2.0))

    @pytest.mark.parametrize("entrypoint", ["constructor", "factory", "synthesis"])
    @pytest.mark.parametrize("bad", [0.0, -1.0, float("nan"), float("inf")])
    @pytest.mark.parametrize("reference_bad", [False, True])
    def test_finite_positive_validation_at_each_entry(self, entrypoint, bad, reference_bad):
        inputs = (2.0, bad) if reference_bad else (bad, 2.0)
        with pytest.raises(ValueError, match="finite and positive"):
            self._report(entrypoint, inputs)

    @pytest.mark.parametrize("entrypoint", ["constructor", "factory", "synthesis"])
    @pytest.mark.parametrize("inputs,ratio,deviation", [
        ((4, 2), 16.0, 100.0), ((2, 4), 0.0625, 50.0),
    ])
    def test_canonical_snapshot_serializes_with_consistent_results(self, entrypoint, inputs, ratio, deviation):
        report = self._report(entrypoint, inputs)
        assert type(report.magnitude_inputs_meV) is tuple
        assert all(type(value) is float for value in report.magnitude_inputs_meV)
        assert report.magnitude_inputs_meV == inputs
        assert report.magnitude_status == "supplied_input_comparison"
        assert report.lambda_ratio_adw_observed == pytest.approx(ratio)
        assert report.lambda_accuracy_percent == pytest.approx(deviation)
        encoded = json.loads(json.dumps(asdict(report)))
        assert encoded["magnitude_inputs_meV"] == list(inputs)
        assert encoded["lambda_ratio_adw_observed"] == pytest.approx(ratio)
        assert encoded["lambda_accuracy_percent"] == pytest.approx(deviation)
        assert encoded["adw_prediction_meV"] is None
        with pytest.raises(FrozenInstanceError):
            report.magnitude_inputs_meV = (8.0, 2.0)
        with pytest.raises(FrozenInstanceError):
            report.adw_prediction_meV = 2.8
        assert json.loads(json.dumps(asdict(report))) == encoded

    @pytest.mark.parametrize("entrypoint", ["constructor", "factory", "synthesis"])
    def test_omitted_sentinel_is_distinct_from_explicit_none_elements(self, entrypoint):
        report = self._report(entrypoint, None)
        assert report.magnitude_inputs_meV is None
        assert report.magnitude_status == "not_computed"
        assert report.lambda_ratio_adw_observed is None
        assert report.lambda_accuracy_percent is None
        assert report.adw_prediction_meV is None
        with pytest.raises(ValueError):
            self._report(entrypoint, (None, None))

    def test_actual_exported_crossconnection_has_qualified_physical_scope(self):
        from src.dark_sector.synthesis import (
            CROSS_CONNECTION_MATRIX, assess_dark_sector_synthesis,
        )

        matches = [c for c in CROSS_CONNECTION_MATRIX if c.connection_id == "ADW_CC_x_SFDM"]
        assert len(matches) == 1
        connection = matches[0]
        assert connection.waves == ("W3", "W5")
        assert connection.strength == "Conceptual"
        assert connection.lean_backing == "memo-only (W5 not yet shipped)"
        assert "candidate vacuum response" in connection.summary.lower()
        assert "nonzero ADW vacuum magnitude" in connection.summary
        assert "any quantitative connection are uncomputed" in connection.summary
        assert "T⁴" not in connection.summary
        assessment = assess_dark_sector_synthesis()
        assert assessment.cross_connection_count == len(CROSS_CONNECTION_MATRIX)
        assert assessment.lean_backed_connection_count == sum(
            not c.lean_backing.startswith("memo-only") for c in CROSS_CONNECTION_MATRIX
        )
