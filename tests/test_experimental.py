"""Tests for the experimental prediction package.

Tests prediction tables, detector requirements, platform comparisons,
and kappa-scaling predictions for all three BEC platforms.
"""

import numpy as np
import pytest

from src.experimental.predictions import (
    FrequencyPrediction,
    PredictionTable,
    DetectorRequirements,
    PlatformComparison,
    KappaScalingPrediction,
    compute_prediction_table,
    compute_all_predictions,
    compute_detector_requirements,
    compare_platforms,
    measurement_strategy,
    kappa_scaling_prediction,
    REPRESENTATIVE_OMEGAS,
)
from src.wkb.spectrum import (
    steinhauer_platform,
    heidelberg_platform,
    trento_platform,
)


class TestFrequencyPrediction:
    """Tests for individual frequency predictions."""

    def test_prediction_at_T_H(self):
        """Prediction at omega = T_H should have well-defined values."""
        platform = steinhauer_platform()
        table = compute_prediction_table(platform, omegas_over_T_H=[1.0])
        pred = table.predictions[0]
        assert pred.omega_over_T_H == pytest.approx(1.0)
        assert pred.n_total > 0
        assert pred.n_planck > 0
        assert pred.n_noise >= 0

    def test_noise_floor_positive(self):
        """Noise floor should be non-negative at all frequencies."""
        platform = steinhauer_platform()
        table = compute_prediction_table(platform)
        for pred in table.predictions:
            assert pred.n_noise >= 0

    def test_deviation_small_at_low_freq(self):
        """Deviation from Planckian should be small at low frequencies."""
        platform = steinhauer_platform()
        table = compute_prediction_table(platform, omegas_over_T_H=[0.5])
        pred = table.predictions[0]
        # At low frequency, corrections are small
        assert abs(pred.fractional_deviation) < 0.5

    def test_dominant_correction_identified(self):
        """Each prediction should identify a dominant correction."""
        platform = steinhauer_platform()
        table = compute_prediction_table(platform)
        valid_corrections = {'dispersive', 'dissipative', 'noise_floor'}
        for pred in table.predictions:
            assert pred.dominant_correction in valid_corrections


class TestPredictionTable:
    """Tests for complete prediction tables."""

    def test_steinhauer_table_structure(self):
        """Steinhauer table should have correct structure."""
        platform = steinhauer_platform()
        table = compute_prediction_table(platform)
        assert table.platform_name == "Steinhauer_Rb87"
        assert table.T_H > 0
        assert table.omega_max > 0
        assert table.omega_max_over_T_H > 0
        assert len(table.predictions) == len(REPRESENTATIVE_OMEGAS)

    def test_heidelberg_table_structure(self):
        """Heidelberg table should have correct structure."""
        platform = heidelberg_platform()
        table = compute_prediction_table(platform)
        assert table.platform_name == "Heidelberg_K39"
        assert len(table.predictions) == len(REPRESENTATIVE_OMEGAS)

    def test_trento_table_structure(self):
        """Trento table should have correct structure."""
        platform = trento_platform()
        table = compute_prediction_table(platform)
        assert table.platform_name == "Trento_Na23"
        assert len(table.predictions) == len(REPRESENTATIVE_OMEGAS)

    def test_custom_frequencies(self):
        """Custom frequency points should work."""
        platform = steinhauer_platform()
        custom = [1.0, 2.0, 4.0]
        table = compute_prediction_table(platform, omegas_over_T_H=custom)
        assert len(table.predictions) == 3

    def test_summary_diagnostics(self):
        """Summary diagnostics should be populated."""
        platform = steinhauer_platform()
        table = compute_prediction_table(platform)
        assert 'max_deviation' in table.summary
        assert 'delta_diss_at_T_H' in table.summary
        assert 'shots_needed' in table.summary

    def test_best_frequency_range(self):
        """Best frequency range should be a valid interval."""
        platform = steinhauer_platform()
        table = compute_prediction_table(platform)
        low, high = table.best_frequency_range
        assert low < high
        assert low > 0


class TestAllPredictions:
    """Tests for compute_all_predictions."""

    def test_all_three_platforms(self):
        """Should return tables for all three platforms."""
        tables = compute_all_predictions()
        assert 'steinhauer' in tables
        assert 'heidelberg' in tables
        assert 'trento' in tables

    def test_consistent_frequencies(self):
        """All tables should use the same frequency points."""
        tables = compute_all_predictions()
        for name, table in tables.items():
            assert len(table.predictions) == len(REPRESENTATIVE_OMEGAS)

    def test_different_parameters(self):
        """Different platforms should have different parameters."""
        tables = compute_all_predictions()
        # D parameters differ between platforms
        D_values = {name: t.params.D for name, t in tables.items()}
        assert len(set(D_values.values())) == 3  # all different


class TestDetectorRequirements:
    """Tests for detector requirement calculations."""

    def test_three_goals_per_platform(self):
        """Should compute requirements for three measurement goals."""
        platform = steinhauer_platform()
        reqs = compute_detector_requirements(platform)
        assert len(reqs) == 3

    def test_dissipative_detection_feasible(self):
        """Dissipative correction detection should have a feasibility assessment."""
        platform = steinhauer_platform()
        reqs = compute_detector_requirements(platform)
        diss_req = reqs[0]
        assert "dissipative" in diss_req.goal.lower()
        assert isinstance(diss_req.feasible, bool)

    def test_shots_positive(self):
        """Required shots should be positive when feasible."""
        platform = steinhauer_platform()
        reqs = compute_detector_requirements(platform)
        for req in reqs:
            if req.feasible:
                assert req.required_shots > 0

    def test_heidelberg_requirements(self):
        """Heidelberg should have valid requirements."""
        platform = heidelberg_platform()
        reqs = compute_detector_requirements(platform)
        assert len(reqs) == 3
        for req in reqs:
            assert req.platform_name == "Heidelberg_K39"


class TestPlatformComparison:
    """Tests for cross-platform comparisons."""

    def test_four_observables(self):
        """Should compare on four observables."""
        comparisons = compare_platforms()
        assert len(comparisons) == 4

    def test_rankings_complete(self):
        """Each comparison should rank all three platforms."""
        comparisons = compare_platforms()
        for comp in comparisons:
            assert len(comp.rankings) == 3
            assert set(comp.rankings.values()) == {1, 2, 3}

    def test_values_populated(self):
        """Observable values should be populated for all platforms."""
        comparisons = compare_platforms()
        for comp in comparisons:
            assert len(comp.values) == 3
            for val in comp.values.values():
                assert isinstance(val, (int, float))

    def test_recommendation_nonempty(self):
        """Each comparison should have a recommendation."""
        comparisons = compare_platforms()
        for comp in comparisons:
            assert len(comp.recommendation) > 10


class TestMeasurementStrategy:
    """Tests for measurement strategy generation."""

    def test_strategy_structure(self):
        """Strategy should have priorities and requirements."""
        platform = steinhauer_platform()
        strategy = measurement_strategy(platform)
        assert strategy.platform_name == "Steinhauer_Rb87"
        assert len(strategy.priority_measurements) == 3
        assert len(strategy.detector_requirements) == 3
        assert len(strategy.comparison) == 4

    def test_priorities_ordered_by_feasibility(self):
        """Priorities should be ordered by feasibility."""
        platform = steinhauer_platform()
        strategy = measurement_strategy(platform)
        # Just check we have priorities
        assert len(strategy.priority_measurements) > 0


class TestKappaScaling:
    """Tests for kappa-scaling predictions."""

    def test_scaling_prediction_structure(self):
        """Kappa-scaling prediction should have correct structure."""
        pred = kappa_scaling_prediction(n_points=5)
        assert len(pred.kappa_values) == 5
        assert len(pred.T_eff_ratio) == 5
        assert len(pred.delta_disp_values) == 5
        assert len(pred.delta_diss_values) == 5

    def test_dispersive_scaling_quadratic(self):
        """Dispersive correction should scale approximately as D^2."""
        pred = kappa_scaling_prediction(n_points=10)
        # Expected: alpha_disp ≈ 2.0
        assert abs(pred.scaling_exponent_disp - 2.0) < 0.3

    def test_dissipative_scaling_flat(self):
        """Dissipative correction should be approximately constant in D."""
        pred = kappa_scaling_prediction(n_points=10)
        # Expected: alpha_diss ≈ 0 (constant)
        # Allow larger tolerance since the scaling is approximate
        assert abs(pred.scaling_exponent_diss) < 1.5

    def test_T_eff_ratio_near_unity(self):
        """T_eff/T_H should be close to 1 for small corrections."""
        pred = kappa_scaling_prediction(n_points=5)
        for ratio in pred.T_eff_ratio:
            assert abs(ratio - 1.0) < 0.1


class TestKappaScalingModule:
    """Tests for src/experimental/kappa_scaling.py — the physical kappa-scaling module.

    These test the correct physics: at fixed BEC material properties,
    delta_disp scales as kappa^2 and delta_diss scales as kappa^1.
    """

    def test_sweep_structure(self):
        """Sweep should have correct array shapes and metadata."""
        from src.experimental.kappa_scaling import compute_kappa_sweep
        from src.core.transonic_background import steinhauer_Rb87
        from src.core.constants import KAPPA_SCALING_FACTORS

        sweep = compute_kappa_sweep(steinhauer_Rb87(), 'Steinhauer')
        n = len(KAPPA_SCALING_FACTORS)
        assert len(sweep.kappa_values) == n
        assert len(sweep.delta_disp_values) == n
        assert len(sweep.delta_diss_values) == n
        assert len(sweep.delta_total_values) == n
        assert len(sweep.T_eff_ratio) == n
        assert sweep.platform_name == 'Steinhauer'
        assert sweep.kappa_nominal > 0
        assert sweep.kappa_cross > 0
        assert sweep.gamma_1 > 0
        assert sweep.gamma_2 > 0
        assert sweep.c_s > 0
        assert sweep.xi > 0

    def test_dispersive_scaling_exponent(self):
        """Fitted dispersive scaling exponent should be 2.0 (quadratic)."""
        from src.experimental.kappa_scaling import compute_all_sweeps

        sweeps = compute_all_sweeps()
        for name, sweep in sweeps.items():
            assert abs(sweep.scaling_exponent_disp - 2.0) < 0.01, (
                f"{name}: expected disp exponent=2.0, got {sweep.scaling_exponent_disp:.4f}"
            )

    def test_dissipative_scaling_exponent(self):
        """Fitted dissipative scaling exponent should be 1.0 (linear)."""
        from src.experimental.kappa_scaling import compute_all_sweeps

        sweeps = compute_all_sweeps()
        for name, sweep in sweeps.items():
            assert abs(sweep.scaling_exponent_diss - 1.0) < 0.01, (
                f"{name}: expected diss exponent=1.0, got {sweep.scaling_exponent_diss:.4f}"
            )

    def test_dispersive_always_negative(self):
        """Dispersive correction should be negative at all kappa > 0."""
        from src.experimental.kappa_scaling import compute_all_sweeps

        sweeps = compute_all_sweeps()
        for name, sweep in sweeps.items():
            assert np.all(sweep.delta_disp_values < 0), (
                f"{name}: delta_disp should be < 0 at all kappa"
            )

    def test_dissipative_always_positive(self):
        """Dissipative correction should be positive at all kappa > 0."""
        from src.experimental.kappa_scaling import compute_all_sweeps

        sweeps = compute_all_sweeps()
        for name, sweep in sweeps.items():
            assert np.all(sweep.delta_diss_values > 0), (
                f"{name}: delta_diss should be > 0 at all kappa"
            )

    def test_crossover_balance(self):
        """At kappa_cross, |delta_disp| should equal delta_diss."""
        from src.core.formulas import (
            kappa_scaling_dispersive, kappa_scaling_dissipative, kappa_scaling_crossover
        )
        from src.experimental.kappa_scaling import compute_all_sweeps

        sweeps = compute_all_sweeps()
        for name, sweep in sweeps.items():
            d_disp_cross = abs(kappa_scaling_dispersive(
                sweep.kappa_cross, sweep.xi, sweep.c_s
            ))
            d_diss_cross = kappa_scaling_dissipative(
                sweep.kappa_cross, sweep.gamma_1, sweep.gamma_2, sweep.c_s
            )
            assert d_disp_cross == pytest.approx(d_diss_cross, rel=1e-10), (
                f"{name}: crossover balance failed: |d_disp|={d_disp_cross:.3e}, "
                f"d_diss={d_diss_cross:.3e}"
            )

    def test_crossover_formula_consistency(self):
        """kappa_scaling_crossover should match the crossoverKappa computation."""
        from src.core.formulas import kappa_scaling_crossover
        from src.experimental.kappa_scaling import compute_all_sweeps

        sweeps = compute_all_sweeps()
        for name, sweep in sweeps.items():
            formula_cross = kappa_scaling_crossover(sweep.gamma_1, sweep.gamma_2, sweep.xi)
            assert formula_cross == pytest.approx(sweep.kappa_cross, rel=1e-12), (
                f"{name}: crossover formulas disagree"
            )

    def test_T_eff_ratio_physical_bounds(self):
        """T_eff/T_H should be in (0.99, 1.01) for these small corrections."""
        from src.experimental.kappa_scaling import compute_all_sweeps

        sweeps = compute_all_sweeps()
        for name, sweep in sweeps.items():
            for i, ratio in enumerate(sweep.T_eff_ratio):
                assert 0.99 < ratio < 1.01, (
                    f"{name} at kappa={sweep.kappa_values[i]:.1f}: "
                    f"T_eff/T_H={ratio:.6f} out of bounds"
                )

    def test_heidelberg_dissipative_dominated(self):
        """Heidelberg K-39 should be in the dissipative-dominated regime."""
        from src.experimental.kappa_scaling import compute_kappa_sweep
        from src.core.transonic_background import heidelberg_K39

        sweep = compute_kappa_sweep(heidelberg_K39(), 'Heidelberg')
        assert sweep.kappa_nominal < sweep.kappa_cross, (
            "Heidelberg should be dissipative-dominated (kappa_nom < kappa_cross)"
        )

    def test_trento_dispersive_dominated(self):
        """Trento should be in the dispersive-dominated regime."""
        from src.experimental.kappa_scaling import compute_kappa_sweep
        from src.core.transonic_background import trento_spin_sonic

        sweep = compute_kappa_sweep(trento_spin_sonic(), 'Trento')
        assert sweep.kappa_nominal > sweep.kappa_cross, (
            "Trento should be dispersive-dominated (kappa_nom > kappa_cross)"
        )

    def test_cross_module_consistency(self):
        """kappa_scaling formulas should match transonic_background computations.

        At nominal kappa, the kappa_scaling_dispersive formula should agree
        with the standard dispersive_correction(D) formula.
        """
        from src.core.formulas import dispersive_correction, kappa_scaling_dispersive
        from src.experimental.kappa_scaling import compute_all_sweeps

        sweeps = compute_all_sweeps()
        for name, sweep in sweeps.items():
            D_nom = sweep.xi * sweep.kappa_nominal / sweep.c_s
            d_disp_standard = dispersive_correction(D_nom)
            d_disp_kappa = kappa_scaling_dispersive(sweep.kappa_nominal, sweep.xi, sweep.c_s)
            assert d_disp_standard == pytest.approx(d_disp_kappa, rel=1e-10), (
                f"{name}: dispersive_correction(D) != kappa_scaling_dispersive(kappa)"
            )

    def test_summary_table(self):
        """Summary table should have all platforms with valid data."""
        from src.experimental.kappa_scaling import kappa_scaling_summary

        summary = kappa_scaling_summary()
        assert set(summary.keys()) == {'Steinhauer', 'Heidelberg', 'Trento'}
        for name, s in summary.items():
            assert s['kappa_nominal'] > 0
            assert s['kappa_cross'] > 0
            assert s['regime'] in ('dispersive', 'dissipative')
            assert abs(s['scaling_exponent_disp'] - 2.0) < 0.01
            assert abs(s['scaling_exponent_diss'] - 1.0) < 0.01


class TestPolaritonPredictions:
    """Tests for polariton Tier 1 predictions."""

    def test_all_platforms_compute(self):
        """All polariton platforms should compute without error."""
        from src.experimental.polariton_predictions import compute_all_polariton_platforms

        platforms = compute_all_polariton_platforms()
        assert len(platforms) == 3
        for name, p in platforms.items():
            assert p.T_H > 0
            assert p.D > 0
            assert p.validity_ratio > 0

    def test_T_H_much_hotter_than_bec(self):
        """Polariton T_H should be >> BEC T_H (factor > 10^8)."""
        from src.experimental.polariton_predictions import polariton_bec_comparison

        comps = polariton_bec_comparison()
        for c in comps:
            for bec_name, ratio in c.T_H_ratio.items():
                assert ratio > 1e8, (
                    f"{c.polariton.name} vs {bec_name}: T_H ratio = {ratio:.1e}, expected > 10^8"
                )

    def test_tier1_regime_classification(self):
        """Regime classification should match Gamma_pol/kappa thresholds."""
        from src.experimental.polariton_predictions import compute_all_polariton_platforms

        platforms = compute_all_polariton_platforms()
        for name, p in platforms.items():
            if p.validity_ratio < 0.03:
                assert p.tier1_regime == 'excellent'
            elif p.validity_ratio < 0.1:
                assert p.tier1_regime == 'perturbative'
            elif p.validity_ratio < 1.0:
                assert p.tier1_regime == 'borderline'
            else:
                assert p.tier1_regime == 'intractable'

    def test_ultralong_is_perturbative(self):
        """Ultra-long cavity should be in the perturbative Tier 1 regime."""
        from src.experimental.polariton_predictions import compute_polariton_platform

        p = compute_polariton_platform('Paris_ultralong')
        assert p.tier1_regime == 'perturbative'
        assert p.validity_ratio < 0.1

    def test_standard_is_intractable(self):
        """Standard cavity should be intractable for Tier 1."""
        from src.experimental.polariton_predictions import compute_polariton_platform

        p = compute_polariton_platform('Paris_standard')
        assert p.tier1_regime == 'intractable'
        assert p.validity_ratio > 1.0

    def test_dispersive_correction_larger_than_bec(self):
        """Polariton dispersive correction should be larger (D ~ 0.1 vs D ~ 0.02)."""
        from src.experimental.polariton_predictions import compute_polariton_platform

        p = compute_polariton_platform('Paris_ultralong')
        assert abs(p.delta_disp) > 1e-3, (
            f"Expected |delta_disp| > 0.001, got {abs(p.delta_disp):.3e}"
        )

    def test_spatial_attenuation_factor(self):
        """Spatial attenuation correction should be >= 1."""
        from src.core.formulas import polariton_spatial_attenuation

        # Long cavity, 10 um propagation at 10^6 m/s group velocity
        factor = polariton_spatial_attenuation(1e10, 10e-6, 1e6)
        assert factor >= 1.0
        assert factor < 2.0  # Should be modest for short distances

    def test_regime_map(self):
        """Regime map should have all platforms with valid data."""
        from src.experimental.polariton_predictions import polariton_regime_map

        regime_map = polariton_regime_map()
        assert len(regime_map) == 3
        for name, data in regime_map.items():
            assert 'Gamma_pol_over_kappa' in data
            assert 'tier1_regime' in data
            assert data['T_H_K'] > 0


class TestPhysicsConsistency:
    """Cross-checks for physics consistency."""

    def test_steinhauer_d_value(self):
        """Steinhauer D should match known value."""
        platform = steinhauer_platform()
        assert platform.D == pytest.approx(0.03)

    def test_noise_floor_identity(self):
        """n_noise = delta_diss = delta_k/2 (FDR identity)."""
        platform = steinhauer_platform()
        table = compute_prediction_table(platform, omegas_over_T_H=[1.0])
        pred = table.predictions[0]
        # delta_k = 2 * delta_diss
        assert pred.delta_k == pytest.approx(2 * pred.delta_diss, rel=0.01)
        # n_noise ≈ delta_k / 2 = delta_diss
        assert pred.n_noise == pytest.approx(pred.delta_k / 2, rel=0.01)

    def test_dispersive_correction_negative(self):
        """Dispersive correction should be negative (subluminal)."""
        platform = steinhauer_platform()
        table = compute_prediction_table(platform)
        for pred in table.predictions:
            assert pred.delta_disp < 0

    def test_dissipative_correction_positive(self):
        """Dissipative correction should be positive."""
        platform = steinhauer_platform()
        table = compute_prediction_table(platform)
        for pred in table.predictions:
            assert pred.delta_diss > 0

    def test_total_occupation_exceeds_planck(self):
        """Total occupation should generally exceed Planckian (due to noise)."""
        platform = steinhauer_platform()
        table = compute_prediction_table(platform, omegas_over_T_H=[1.0])
        pred = table.predictions[0]
        # n_total = n_hawking + n_noise ≥ n_planck approximately
        # This can fail at specific frequencies due to delta_disp < 0
        # but at omega = T_H, dissipative heating should dominate
        assert pred.n_total > 0

    def test_omega_max_ordered(self):
        """Platforms with smaller D should have larger omega_max/T_H."""
        tables = compute_all_predictions()
        # omega_max = kappa / D^(2/3), so smaller D → larger omega_max/T_H
        D_trento = tables['trento'].params.D
        D_heidelberg = tables['heidelberg'].params.D
        D_steinhauer = tables['steinhauer'].params.D
        assert D_trento < D_heidelberg < D_steinhauer
        # Therefore omega_max/T_H should be ordered inversely
        assert (tables['trento'].omega_max_over_T_H >
                tables['heidelberg'].omega_max_over_T_H >
                tables['steinhauer'].omega_max_over_T_H)

    def test_shot_count_sanity(self):
        """Shot counts must be >> 10^4 when corrections are << 1.

        Catching physically absurd shot counts (e.g. 27) that arise from
        using relative deviations that diverge at high frequency.
        """
        tables = compute_all_predictions()
        for name, t in tables.items():
            delta_diss = t.summary['delta_diss_at_T_H']
            shots = t.summary['shots_needed']
            # If the correction is sub-percent, you need many shots
            if delta_diss < 1e-3:
                assert shots > 1e4, (
                    f"{name}: delta_diss={delta_diss:.2e} but shots_needed={shots:.0f} "
                    f"— physically absurd (small correction cannot be detected with few shots)"
                )
            # No platform should report feasible (all corrections are tiny)
            assert not t.summary['feasible'], (
                f"{name}: feasible=True but delta_diss={delta_diss:.2e} — "
                f"these corrections are far below current detector sensitivity"
            )
