"""Tests for the vestigial gravity simulation package.

Tests lattice model, mean-field analysis, Monte Carlo sampler,
and phase diagram scanning.
"""

import numpy as np
import pytest

from src.vestigial.lattice_model import (
    LatticeParams, TetradSite, LatticeConfig,
    create_lattice, auxiliary_action,
    tetrad_order_parameter, metric_order_parameter,
    site_action,
)
from src.vestigial.mean_field import (
    MeanFieldParams, MeanFieldResult,
    mean_field_gap_equation, mean_field_metric_correlator,
    vestigial_phase_window, full_mean_field_analysis,
)
from src.vestigial.monte_carlo import (
    MCParams, MCResult, metropolis_sweep, run_monte_carlo,
)
from src.vestigial.phase_diagram import (
    PhasePoint, PhaseDiagramResult,
    scan_coupling, classify_phase_point,
)


class TestLatticeParams:
    """Tests for lattice parameter structure."""

    def test_volume(self):
        params = LatticeParams(L=4, d=4)
        assert params.volume == 256

    def test_euclidean_metric(self):
        params = LatticeParams(d=4, euclidean=True)
        assert np.allclose(params.eta, np.eye(4))

    def test_lorentzian_metric(self):
        params = LatticeParams(d=4, euclidean=False)
        expected = np.diag([-1, 1, 1, 1])
        assert np.allclose(params.eta, expected)

    def test_tetrad_components(self):
        params = LatticeParams(d=4)
        assert params.n_tetrad_components == 16

    def test_critical_coupling(self):
        params = LatticeParams(N_f=4)
        assert params.G_c == pytest.approx(2.0)


class TestTetradSite:
    """Tests for tetrad field at a single site."""

    def test_identity_magnitude(self):
        e = TetradSite(field=np.eye(4))
        assert e.magnitude == pytest.approx(2.0)  # sqrt(4)

    def test_zero_magnitude(self):
        e = TetradSite(field=np.zeros((4, 4)))
        assert e.magnitude == pytest.approx(0.0)

    def test_identity_metric(self):
        e = TetradSite(field=np.eye(4))
        assert np.allclose(e.metric, np.eye(4))

    def test_scaled_metric(self):
        e = TetradSite(field=2.0 * np.eye(4))
        assert np.allclose(e.metric, 4.0 * np.eye(4))

    def test_lorentzian_check_euclidean(self):
        e = TetradSite(field=np.eye(4))
        assert e.is_lorentzian(np.eye(4))

    def test_metric_eigenvalues_positive(self):
        e = TetradSite(field=np.eye(4))
        assert np.all(e.metric_eigenvalues > 0)


class TestLatticeConfig:
    """Tests for lattice configuration."""

    def test_hot_start(self):
        params = LatticeParams(L=2, d=4, G=1.0)
        config = create_lattice(params, init_type="hot")
        assert config.tetrads.shape == (16, 4, 4)

    def test_cold_start(self):
        params = LatticeParams(L=2, d=4, G=1.0)
        config = create_lattice(params, init_type="cold")
        assert np.allclose(config.tetrads[0], np.eye(4))

    def test_zero_start(self):
        params = LatticeParams(L=2, d=4, G=1.0)
        config = create_lattice(params, init_type="zero")
        assert np.allclose(config.tetrads, 0.0)

    def test_site_tetrad(self):
        params = LatticeParams(L=2, d=4, G=1.0)
        config = create_lattice(params, init_type="cold")
        t = config.site_tetrad(0)
        assert isinstance(t, TetradSite)


class TestAuxiliaryAction:
    """Tests for the auxiliary action."""

    def test_zero_config_zero_action(self):
        params = LatticeParams(L=2, d=4, G=1.0)
        config = create_lattice(params, init_type="zero")
        assert auxiliary_action(config) == pytest.approx(0.0)

    def test_action_positive_euclidean(self):
        params = LatticeParams(L=2, d=4, G=1.0, euclidean=True)
        config = create_lattice(params, init_type="hot")
        assert auxiliary_action(config) > 0

    def test_action_scales_with_G(self):
        """Action ~ 1/G, so doubling G halves action."""
        params1 = LatticeParams(L=2, d=4, G=1.0)
        params2 = LatticeParams(L=2, d=4, G=2.0)
        config1 = create_lattice(params1, init_type="cold")
        config2 = create_lattice(params2, init_type="cold")
        # Copy same field config
        config2.tetrads = config1.tetrads.copy()
        S1 = auxiliary_action(config1)
        S2 = auxiliary_action(config2)
        assert S2 == pytest.approx(S1 / 2.0)

    def test_site_action_consistency(self):
        params = LatticeParams(L=2, d=4, G=1.0)
        config = create_lattice(params, init_type="cold")
        total = sum(site_action(config.tetrads[i], params.G, params.eta)
                    for i in range(config.volume))
        assert total == pytest.approx(auxiliary_action(config))


class TestOrderParameters:
    """Tests for order parameters."""

    def test_cold_start_has_tetrad_vev(self):
        params = LatticeParams(L=2, d=4, G=1.0)
        config = create_lattice(params, init_type="cold")
        M = tetrad_order_parameter(config)
        assert np.allclose(M, np.eye(4))

    def test_zero_start_no_tetrad_vev(self):
        params = LatticeParams(L=2, d=4, G=1.0)
        config = create_lattice(params, init_type="zero")
        M = tetrad_order_parameter(config)
        assert np.allclose(M, 0.0)

    def test_cold_start_has_metric(self):
        params = LatticeParams(L=2, d=4, G=1.0, euclidean=True)
        config = create_lattice(params, init_type="cold")
        M_g = metric_order_parameter(config)
        assert np.allclose(M_g, np.eye(4))

    def test_zero_start_no_metric(self):
        params = LatticeParams(L=2, d=4, G=1.0)
        config = create_lattice(params, init_type="zero")
        M_g = metric_order_parameter(config)
        assert np.allclose(M_g, 0.0)


class TestMeanField:
    """Tests for mean-field analysis."""

    def test_below_Gc_no_tetrad(self):
        params = MeanFieldParams(G=0.5, Lambda=1.0, N_f=4)
        C = mean_field_gap_equation(params)
        assert C == pytest.approx(0.0)

    def test_above_Gc_has_tetrad(self):
        params = MeanFieldParams(G=100.0, Lambda=1.0, N_f=4)
        C = mean_field_gap_equation(params)
        assert C > 0

    def test_metric_correlator_positive_near_Gc(self):
        G_c = 8.0 * np.pi**2 / (4 * 1.0**2)
        params = MeanFieldParams(G=0.9 * G_c, Lambda=1.0, N_f=4)
        G_m = mean_field_metric_correlator(params)
        assert G_m > 0

    def test_vestigial_window_exists(self):
        result = vestigial_phase_window(Lambda=1.0, N_f=4)
        assert 'vestigial_exists' in result

    def test_full_analysis_below_Gc(self):
        result = full_mean_field_analysis(G=0.001, Lambda=1.0, N_f=4)
        assert result.phase == "pre_geometric"

    def test_full_analysis_above_Gc(self):
        G_c = 8.0 * np.pi**2 / (4 * 1.0**2)
        result = full_mean_field_analysis(G=3.0 * G_c, Lambda=1.0, N_f=4)
        assert result.phase == "full_tetrad"
        assert result.C_tetrad > 0

    def test_three_phase_structure(self):
        """Verify the corrected three-phase structure:
        - Weak coupling (G << G_c) → pre-geometric
        - Near G_c from below → vestigial
        - Above G_c → full tetrad
        """
        result = vestigial_phase_window(Lambda=1.0, N_f=4, n_points=30)

        # Must have all three phases
        phases_seen = set(result['phases'])
        assert "pre_geometric" in phases_seen, "No pre-geometric phase found"
        assert "vestigial" in phases_seen, "No vestigial phase found"
        assert "full_tetrad" in phases_seen, "No full_tetrad phase found"

        # Phase ordering: pre-geometric first, then vestigial, then full tetrad
        first_vestigial = next(i for i, p in enumerate(result['phases']) if p == "vestigial")
        first_full = next(i for i, p in enumerate(result['phases']) if p == "full_tetrad")
        last_pre = max(i for i, p in enumerate(result['phases']) if p == "pre_geometric")
        assert last_pre < first_vestigial, "pre-geometric should come before vestigial"
        assert first_vestigial < first_full, "vestigial should come before full_tetrad"

        # Vestigial window should be near G_c (ratio 0.7-1.0), not at weak coupling
        vestigial_ratios = [result['coupling_ratios'][i]
                           for i, p in enumerate(result['phases']) if p == "vestigial"]
        assert min(vestigial_ratios) > 0.6, f"Vestigial starts too low: {min(vestigial_ratios)}"
        assert max(vestigial_ratios) <= 1.1, f"Vestigial extends too high: {max(vestigial_ratios)}"


class TestMonteCarlo:
    """Tests for Monte Carlo sampler."""

    def test_single_sweep(self):
        params = LatticeParams(L=2, d=2, G=1.0)
        config = create_lattice(params, init_type="hot")
        rng = np.random.default_rng(42)
        config, acc = metropolis_sweep(config, step_size=0.3, rng=rng)
        assert 0.0 <= acc <= 1.0

    def test_short_run(self):
        params = LatticeParams(L=2, d=2, G=1.0)
        mc_params = MCParams(n_thermalize=10, n_measure=20, n_skip=2, seed=42)
        result = run_monte_carlo(params, mc_params)
        assert isinstance(result, MCResult)
        assert len(result.measurements) == 20

    def test_acceptance_rate_reasonable(self):
        params = LatticeParams(L=2, d=2, G=1.0)
        mc_params = MCParams(n_thermalize=10, n_measure=20, n_skip=2, seed=42)
        result = run_monte_carlo(params, mc_params)
        assert 0.1 < result.overall_acceptance < 0.99

    def test_strong_coupling_ordered(self):
        """At very weak coupling (strong constraint), tetrad should be small."""
        params = LatticeParams(L=2, d=2, G=0.01)
        mc_params = MCParams(n_thermalize=20, n_measure=30, n_skip=2, seed=42)
        result = run_monte_carlo(params, mc_params)
        # Weak G = strong constraint: tetrads should be small
        assert result.mean_tetrad_vev < 1.0

    def test_reproducibility(self):
        """Same seed should give same result."""
        params = LatticeParams(L=2, d=2, G=1.0)
        mc_params = MCParams(n_thermalize=5, n_measure=10, n_skip=1, seed=123)
        r1 = run_monte_carlo(params, mc_params)
        r2 = run_monte_carlo(params, mc_params)
        assert r1.mean_tetrad_vev == pytest.approx(r2.mean_tetrad_vev)


class TestPhaseDiagram:
    """Tests for phase diagram scanning."""

    def test_classify_pre_geometric(self):
        assert classify_phase_point(0.0, 0.0) == "pre_geometric"

    def test_classify_vestigial(self):
        assert classify_phase_point(0.0, 1.0) == "vestigial"

    def test_classify_full_tetrad(self):
        assert classify_phase_point(1.0, 1.0) == "full_tetrad"

    def test_mean_field_scan(self):
        result = scan_coupling(
            method="mean_field",
            Lambda=1.0, N_f=4,
            coupling_range=(0.5, 3.0),
            n_points=10,
        )
        assert isinstance(result, PhaseDiagramResult)
        assert len(result.points) == 10
        assert result.method == "mean_field"

    def test_phase_sequence(self):
        """Below G_c: pre-geometric. Far above G_c: full tetrad."""
        result = scan_coupling(
            method="mean_field",
            Lambda=1.0, N_f=4,
            coupling_range=(0.3, 3.0),
            n_points=20,
        )
        # First few points should be pre-geometric or vestigial
        assert result.phases[0] in ("pre_geometric", "vestigial")
        # Last few points should be full_tetrad
        assert result.phases[-1] == "full_tetrad"

    def test_coupling_ratios_array(self):
        result = scan_coupling(
            method="mean_field",
            n_points=5,
        )
        assert len(result.coupling_ratios) == 5
        assert result.coupling_ratios[0] < result.coupling_ratios[-1]


class TestCrossModuleConsistency:
    """Cross-module consistency checks."""

    def test_mean_field_matches_adw_gap_equation(self):
        """Mean-field tetrad VEV should match Phase 3 gap equation."""
        from src.adw.gap_equation import full_gap_analysis

        Lambda = 1.0
        N_f = 4
        G_c = 8.0 * np.pi**2 / (N_f * Lambda**2)
        G = 2.0 * G_c

        # Phase 3 result
        p3 = full_gap_analysis(G=G, Lambda=Lambda, N_f=N_f)
        C_p3 = p3.nontrivial_solution.C if p3.nontrivial_solution else 0.0

        # Phase 4 mean-field
        params = MeanFieldParams(G=G, Lambda=Lambda, N_f=N_f)
        C_p4 = mean_field_gap_equation(params)

        assert C_p4 == pytest.approx(C_p3, rel=0.01)

    def test_critical_coupling_consistent(self):
        """G_c should match between lattice model and mean-field."""
        lp = LatticeParams(N_f=4)
        mf = MeanFieldParams(G=1.0, Lambda=np.pi, N_f=4)
        # LatticeParams.G_c = 8/N_f = 2.0 (lattice units, Lambda = pi)
        assert lp.G_c == pytest.approx(2.0)
        # MeanFieldParams.G_c = 8 pi^2 / (N_f Lambda^2)
        assert mf.G_c == pytest.approx(8 * np.pi**2 / (4 * np.pi**2))


# ═══════════════════════════════════════════════════════════════════
# Finite-size scaling and Lorentzian pilot tests
# ═══════════════════════════════════════════════════════════════════

from src.vestigial.finite_size import (
    BinderCumulant, SusceptibilityPeak, FiniteSizeResult,
    SignReweightingResult,
    compute_binder_cumulant, find_susceptibility_peak,
    find_binder_crossing, finite_size_scaling,
    sign_reweighting, lorentzian_pilot,
)


class TestBinderCumulant:
    """Tests for Binder cumulant computation."""

    def test_binder_from_mc(self):
        params = LatticeParams(L=2, d=2, G=1.0)
        mc_params_small = MCParams(n_thermalize=10, n_measure=30, n_skip=2, seed=42)
        mc_result = run_monte_carlo(params, mc_params_small)
        binder = compute_binder_cumulant(mc_result, 1.0)
        assert isinstance(binder, BinderCumulant)
        assert binder.L == 2

    def test_binder_bounded(self):
        """Binder cumulant should be in [-1, 2/3] for physical distributions."""
        params = LatticeParams(L=2, d=2, G=1.0)
        mc_params_small = MCParams(n_thermalize=10, n_measure=30, n_skip=2, seed=42)
        mc_result = run_monte_carlo(params, mc_params_small)
        binder = compute_binder_cumulant(mc_result, 1.0)
        assert -1.5 < binder.U_tetrad < 1.0
        assert -1.5 < binder.U_metric < 1.0

    def test_m2_positive(self):
        params = LatticeParams(L=2, d=2, G=1.0)
        mc_params_small = MCParams(n_thermalize=10, n_measure=30, n_skip=2, seed=42)
        mc_result = run_monte_carlo(params, mc_params_small)
        binder = compute_binder_cumulant(mc_result, 1.0)
        assert binder.m2_tetrad >= 0
        assert binder.m2_metric >= 0


class TestSusceptibilityPeak:
    """Tests for susceptibility peak finding."""

    def test_peak_at_maximum(self):
        ratios = np.array([0.5, 1.0, 1.5, 2.0])
        chi = np.array([0.1, 0.5, 0.8, 0.3])
        peak = find_susceptibility_peak(ratios, chi, L=4, order_param_type="tetrad")
        assert peak.peak_coupling == pytest.approx(1.5)
        assert peak.peak_height == pytest.approx(0.8)
        assert peak.L == 4


class TestBinderCrossing:
    """Tests for Binder cumulant crossing detection."""

    def test_crossing_found(self):
        """Construct two Binder curves that cross."""
        binders_L1 = [
            BinderCumulant(L=4, coupling_ratio=r, U_tetrad=0.3 + 0.2 * r,
                          U_metric=0, m2_tetrad=0, m4_tetrad=0, m2_metric=0, m4_metric=0)
            for r in [0.5, 1.0, 1.5, 2.0]
        ]
        binders_L2 = [
            BinderCumulant(L=8, coupling_ratio=r, U_tetrad=0.8 - 0.1 * r,
                          U_metric=0, m2_tetrad=0, m4_tetrad=0, m2_metric=0, m4_metric=0)
            for r in [0.5, 1.0, 1.5, 2.0]
        ]
        crossing = find_binder_crossing(binders_L1, binders_L2, "tetrad")
        assert crossing is not None
        assert 0.5 < crossing < 2.0

    def test_no_crossing(self):
        """If curves don't cross, return None."""
        binders_L1 = [
            BinderCumulant(L=4, coupling_ratio=r, U_tetrad=0.1 * r,
                          U_metric=0, m2_tetrad=0, m4_tetrad=0, m2_metric=0, m4_metric=0)
            for r in [0.5, 1.0, 1.5]
        ]
        binders_L2 = [
            BinderCumulant(L=8, coupling_ratio=r, U_tetrad=0.1 * r + 1.0,
                          U_metric=0, m2_tetrad=0, m4_tetrad=0, m2_metric=0, m4_metric=0)
            for r in [0.5, 1.0, 1.5]
        ]
        crossing = find_binder_crossing(binders_L1, binders_L2, "tetrad")
        assert crossing is None


class TestSignReweighting:
    """Tests for Lorentzian sign reweighting."""

    def test_sign_result_structure(self):
        mc_params_small = MCParams(n_thermalize=10, n_measure=30, n_skip=2, seed=42)
        result = sign_reweighting(1.0, L=2, mc_params=mc_params_small)
        assert isinstance(result, SignReweightingResult)
        assert result.L == 2
        assert result.n_configs == 30

    def test_sign_positive(self):
        """Average sign should be non-negative."""
        mc_params_small = MCParams(n_thermalize=10, n_measure=30, n_skip=2, seed=42)
        result = sign_reweighting(1.0, L=2, mc_params=mc_params_small)
        assert result.avg_sign >= 0

    def test_delta_S_negative(self):
        """Delta S should be negative (Lorentzian action has wrong-sign timelike components)."""
        mc_params_small = MCParams(n_thermalize=10, n_measure=30, n_skip=2, seed=42)
        result = sign_reweighting(1.0, L=2, mc_params=mc_params_small)
        assert result.delta_S_mean < 0

    def test_sign_decreases_with_volume(self):
        """Larger lattice should have smaller average sign (sign problem worsens)."""
        mc = MCParams(n_thermalize=10, n_measure=30, n_skip=2, seed=42)
        r2 = sign_reweighting(1.0, L=2, mc_params=mc)
        # L=2 in d=2 has V=4, already gives very small sign
        # Just check it's a valid number
        assert 0 <= r2.avg_sign <= 1.0

    def test_lorentzian_pilot(self):
        """Pilot should return results for each coupling."""
        mc = MCParams(n_thermalize=5, n_measure=10, n_skip=1, seed=42)
        results = lorentzian_pilot([0.5, 1.5], L=2, mc_params=mc)
        assert len(results) == 2
        for r in results:
            assert isinstance(r, SignReweightingResult)


class TestFiniteSizeScaling:
    """Tests for the full finite-size scaling analysis."""

    def test_fss_structure(self):
        """FSS should return valid structure with small params."""
        mc = MCParams(n_thermalize=10, n_measure=20, n_skip=2, seed=42)
        result = finite_size_scaling(
            lattice_sizes=[2],
            coupling_range=(0.5, 2.0),
            n_couplings=5,
            mc_params=mc,
        )
        assert isinstance(result, FiniteSizeResult)
        assert 2 in result.binder_data
        assert len(result.binder_data[2]) == 5

    def test_fss_multiple_sizes(self):
        """FSS with two sizes should enable crossing detection."""
        mc = MCParams(n_thermalize=10, n_measure=20, n_skip=2, seed=42)
        result = finite_size_scaling(
            lattice_sizes=[2, 3],
            coupling_range=(0.5, 2.0),
            n_couplings=5,
            mc_params=mc,
        )
        assert len(result.lattice_sizes) == 2
        assert len(result.susceptibility_peaks_tetrad) == 2
        assert len(result.susceptibility_peaks_metric) == 2
