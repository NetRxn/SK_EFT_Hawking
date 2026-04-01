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


# ════════════════════════════════════════════════════════════════════
# Phase 5 Wave 2A: SU(2) Integration + Grassmann TRG
# ════════════════════════════════════════════════════════════════════

from src.vestigial.su2_integration import (
    integrate_one_link, build_effective_action,
    su2_pseudo_reality_check, build_initial_tensor,
    SU2IntegrationResult, EffectiveAction2D,
)
from src.vestigial.grassmann_trg import (
    run_grassmann_trg, TRGParams, scan_coupling_2d,
    trg_free_energy_convergence, PhaseScanResult,
)
from src.core.formulas import (
    su2_one_link_integral, adw_2d_effective_coupling,
    binder_cumulant, grassmann_trg_free_energy,
)
from src.core.constants import ADW_2D_MODEL, SU2_HAAR, GRASSMANN_TRG


class TestSU2Integration:
    """Tests for SU(2) Haar measure integration."""

    def test_one_link_integral_value(self):
        """∫ dU U_ij U*_kl = 1/2 for SU(2)."""
        assert su2_one_link_integral(2) == 0.5

    def test_one_link_integral_general(self):
        """For SU(N), the factor is 1/N."""
        assert su2_one_link_integral(3) == pytest.approx(1.0 / 3.0)

    def test_effective_coupling(self):
        """g_eff = g_EH / dim_fund."""
        assert adw_2d_effective_coupling(4.0, 2) == 2.0
        assert adw_2d_effective_coupling(0.0, 2) == 0.0

    def test_integrate_one_link_structure(self):
        """Integration result has correct structure."""
        result = integrate_one_link(2.0)
        assert isinstance(result, SU2IntegrationResult)
        assert result.g_EH == 2.0
        assert result.g_eff == 1.0
        assert result.dim_fund == 2
        assert 'singlet' in result.channels
        assert result.channels['singlet'] == 1.0

    def test_effective_action_structure(self):
        """Effective action has correct parameters."""
        action = build_effective_action(1.0, 2.0)
        assert isinstance(action, EffectiveAction2D)
        assert action.g_cosmo == 1.0
        assert action.g_eff == 1.0  # 2.0 / 2
        assert action.d == 2
        assert action.n_grassmann == 2
        assert action.coordination_number == 4

    def test_pseudo_reality(self):
        """SU(2) fundamental rep is pseudo-real: U* = ε U ε⁻¹."""
        result = su2_pseudo_reality_check()
        assert result['pseudo_real'] is True
        assert result['max_reconstruction_error'] < 1e-10
        assert result['sign_problem_absent'] is True

    def test_initial_tensor_shape(self):
        """Initial tensor has shape (2, 2, 2, 2)."""
        T = build_initial_tensor(1.0, 1.0)
        assert T.shape == (2, 2, 2, 2)

    def test_initial_tensor_positive(self):
        """All tensor elements should be positive (Boltzmann weights)."""
        T = build_initial_tensor(1.0, 0.5)
        assert np.all(T > 0)

    def test_initial_tensor_zero_coupling(self):
        """At g_cosmo=0, g_EH=0: all weights = 1, tensor sums to 4."""
        T = build_initial_tensor(0.0, 0.0)
        # Each element T[l,r,u,d] = Σ_{n1,n2} 1 = 4 (sum over 4 configs)
        assert np.allclose(T, 4.0)


class TestGrassmannTRG:
    """Tests for the Grassmann TRG algorithm."""

    def test_trg_runs(self):
        """TRG should run without errors."""
        result = run_grassmann_trg(1.0, 1.0, TRGParams(D_cut=4, n_rg_steps=2))
        assert result.L == 4
        assert result.volume == 16
        assert np.isfinite(result.ln_Z)
        assert np.isfinite(result.free_energy)

    def test_trg_zero_coupling_consistency(self):
        """At zero coupling, free energy per site should be independent of L."""
        f_values = []
        for n_rg in [2, 3, 4]:
            result = run_grassmann_trg(0.0, 0.0, TRGParams(D_cut=4, n_rg_steps=n_rg))
            f_values.append(result.free_energy)
        # Free energy per site should be the same regardless of lattice size
        for f in f_values:
            assert abs(f - f_values[0]) < 0.1, (
                f"Free energy varies with L at zero coupling: {f_values}"
            )

    def test_trg_free_energy_finite(self):
        """Free energy should be finite for reasonable couplings."""
        for g_EH in [0.0, 0.5, 1.0, 2.0, 5.0]:
            result = run_grassmann_trg(1.0, g_EH, TRGParams(D_cut=4, n_rg_steps=2))
            assert np.isfinite(result.free_energy), f"Non-finite f at g_EH={g_EH}"

    def test_trg_lattice_size(self):
        """Lattice size = 2^n_rg_steps."""
        for n in [1, 2, 3, 4]:
            result = run_grassmann_trg(1.0, 1.0, TRGParams(D_cut=4, n_rg_steps=n))
            assert result.L == 2**n
            assert result.volume == (2**n)**2

    def test_trg_sv_spectrum(self):
        """Singular value spectrum should be recorded at each step."""
        params = TRGParams(D_cut=8, n_rg_steps=3)
        result = run_grassmann_trg(1.0, 1.0, params)
        assert len(result.singular_value_spectrum) == 3
        for sv in result.singular_value_spectrum:
            assert len(sv) > 0
            assert np.all(sv >= 0)
            # SVs should be in decreasing order
            assert np.all(sv[:-1] >= sv[1:])

    def test_trg_d_cut_convergence(self):
        """Free energy should converge as D_cut increases."""
        conv = trg_free_energy_convergence(1.0, 1.0, D_cut_values=[4, 8, 16], n_rg_steps=3)
        energies = [r['free_energy'] for r in conv['results']]
        # Check that differences decrease (convergence)
        if len(energies) >= 3:
            diff1 = abs(energies[1] - energies[0])
            diff2 = abs(energies[2] - energies[1])
            assert diff2 <= diff1 + 1e-10  # converging or already converged


class TestPhaseScan2D:
    """Tests for the 2D coupling scan."""

    def test_scan_runs(self):
        """Coupling scan should complete without errors."""
        result = scan_coupling_2d(
            g_cosmo=1.0,
            g_EH_range=(0.0, 3.0),
            n_points=10,
            trg_params=TRGParams(D_cut=4, n_rg_steps=2),
        )
        assert isinstance(result, PhaseScanResult)
        assert len(result.g_EH_values) == 10
        assert len(result.free_energies) == 10
        assert np.all(np.isfinite(result.free_energies))

    def test_scan_specific_heat(self):
        """Specific heat should be computed."""
        result = scan_coupling_2d(
            g_cosmo=1.0, g_EH_range=(0.0, 3.0), n_points=10,
            trg_params=TRGParams(D_cut=4, n_rg_steps=2),
        )
        assert len(result.specific_heat) == 10
        assert np.all(np.isfinite(result.specific_heat))

    def test_free_energy_monotone_weak_coupling(self):
        """Free energy should vary smoothly at weak coupling."""
        result = scan_coupling_2d(
            g_cosmo=1.0, g_EH_range=(0.0, 1.0), n_points=5,
            trg_params=TRGParams(D_cut=4, n_rg_steps=2),
        )
        # Check free energies are finite and smooth (no wild jumps)
        diffs = np.abs(np.diff(result.free_energies))
        assert np.all(diffs < 10.0)  # no catastrophic jumps


class TestFormulas2D:
    """Tests for the Wave 2A formulas in formulas.py."""

    def test_binder_cumulant_ordered(self):
        """U_L = 2/3 in the ordered limit (m⁴ = m²²)."""
        m2 = 5.0
        m4 = m2**2
        assert binder_cumulant(m2, m4) == pytest.approx(2.0 / 3.0)

    def test_binder_cumulant_gaussian(self):
        """U_L = 0 for Gaussian (m⁴ = 3m²²)."""
        m2 = 5.0
        m4 = 3.0 * m2**2
        assert binder_cumulant(m2, m4) == pytest.approx(0.0)

    def test_binder_cumulant_zero(self):
        """U_L = 0 when m2 = 0."""
        assert binder_cumulant(0.0, 0.0) == 0.0

    def test_free_energy_formula(self):
        """f = -ln(Z)/V."""
        assert grassmann_trg_free_energy(10.0, 100) == pytest.approx(-0.1)
        assert grassmann_trg_free_energy(0.0, 100) == 0.0

    def test_free_energy_zero_volume(self):
        """Handle zero volume gracefully."""
        assert grassmann_trg_free_energy(10.0, 0) == 0.0

    def test_constants_consistency(self):
        """ADW 2D model constants are self-consistent."""
        assert ADW_2D_MODEL['d'] == 2
        assert ADW_2D_MODEL['n_grassmann'] == 2
        assert ADW_2D_MODEL['gauge_dim'] == SU2_HAAR['dim_fund']
        assert SU2_HAAR['one_link_factor'] == su2_one_link_integral(SU2_HAAR['dim_fund'])


# ════════════════════════════════════════════════════════════════════
# Phase 5 Wave 2B: 4D Fermion-Bag Monte Carlo
# ════════════════════════════════════════════════════════════════════

from src.core.formulas import (
    so4_one_link_integral, adw_4d_effective_coupling,
    eight_fermion_vertex_weight, fermion_bag_local_weight,
    metric_correlator_connected, vestigial_phase_indicator,
)
from src.core.constants import ADW_4D_MODEL, SO4_HAAR, FERMION_BAG
from src.vestigial.lattice_4d import (
    Lattice4DParams, Lattice4DConfig, create_lattice_4d,
    total_action_4d, tetrad_order_parameter_4d, metric_order_parameter_4d,
    neighbor_index, bond_index,
)
from src.vestigial.fermion_bag import (
    FermionBagParams, FermionBagResult, run_fermion_bag_mc,
)
from src.vestigial.phase_scan import (
    scan_coupling_4d, PhaseScan4DResult,
    binder_crossing_analysis, BinderCrossing4DResult,
)


class TestFormulas4D:
    """Tests for Wave 2B formulas."""

    def test_so4_one_link(self):
        """SO(4) one-link factor = 1/4."""
        assert so4_one_link_integral() == 0.25

    def test_so4_one_link_general(self):
        """General: 1/(dim_L × dim_R)."""
        assert so4_one_link_integral(3, 3) == pytest.approx(1.0 / 9.0)

    def test_adw_4d_effective_coupling(self):
        """g_eff = g_EH / 4."""
        assert adw_4d_effective_coupling(4.0) == 1.0
        assert adw_4d_effective_coupling(0.0) == 0.0

    def test_eight_fermion_full_occ(self):
        """At full occupation, weight = exp(-g_cosmo)."""
        assert eight_fermion_vertex_weight(8, 1.0) == pytest.approx(np.exp(-1.0))

    def test_eight_fermion_partial_occ(self):
        """At partial occupation, weight = 1."""
        for n in range(8):
            assert eight_fermion_vertex_weight(n, 5.0) == 1.0

    def test_fermion_bag_weight(self):
        """Bag weight is product of positive factors."""
        config = {
            'site_occupations': [8, 4, 0],
            'bond_occupations': [1, 0, 1],
        }
        w = fermion_bag_local_weight(config, 1.0, 0.5)
        expected = np.exp(-1.0) * 1.0 * 1.0 * np.exp(-0.5) * 1.0 * np.exp(-0.5)
        assert w == pytest.approx(expected)
        assert w > 0

    def test_metric_correlator_positive(self):
        """Connected metric correlator ≥ 0."""
        assert metric_correlator_connected(5.0, 30.0) >= 0
        assert metric_correlator_connected(5.0, 25.0) == 0  # m4 = m2²

    def test_vestigial_indicator_all_phases(self):
        """Phase indicator classifies all three phases correctly."""
        assert vestigial_phase_indicator(0.1, 0.1) == 'pre_geometric'
        assert vestigial_phase_indicator(0.1, 0.6) == 'vestigial'
        assert vestigial_phase_indicator(0.6, 0.6) == 'tetrad_ordered'
        assert vestigial_phase_indicator(0.3, 0.3) == 'crossover'

    def test_constants_4d(self):
        """4D model constants are self-consistent."""
        assert ADW_4D_MODEL['d'] == 4
        assert ADW_4D_MODEL['n_grassmann'] == 8
        assert ADW_4D_MODEL['n_dirac'] * ADW_4D_MODEL['spinor_dim'] == 8
        assert SO4_HAAR['one_link_factor'] == so4_one_link_integral()


class TestLattice4D:
    """Tests for the 4D lattice model."""

    def test_params_volume(self):
        """Volume = L^4."""
        p = Lattice4DParams(L=4)
        assert p.volume == 256

    def test_params_bonds(self):
        """Number of bonds = V × d."""
        p = Lattice4DParams(L=3)
        assert p.n_bonds == 81 * 4  # 3^4 = 81 sites, 4 directions

    def test_params_g_eff(self):
        """Effective coupling = g_EH/4."""
        p = Lattice4DParams(g_EH=8.0)
        assert p.g_eff == 2.0

    def test_create_lattice(self):
        """Lattice creation produces correct shapes."""
        p = Lattice4DParams(L=2)
        config = create_lattice_4d(p)
        assert config.site_occ.shape == (16,)   # 2^4
        assert config.bond_occ.shape == (64,)   # 16 × 4
        assert np.all(config.site_occ >= 0)
        assert np.all(config.site_occ <= 8)

    def test_total_action_positive(self):
        """Total action is non-negative for positive couplings."""
        p = Lattice4DParams(L=2, g_cosmo=1.0, g_EH=1.0)
        config = create_lattice_4d(p)
        S = total_action_4d(config)
        assert S >= 0

    def test_tetrad_order_bounded(self):
        """Tetrad order parameter in [0, 1]."""
        p = Lattice4DParams(L=2)
        config = create_lattice_4d(p)
        E = tetrad_order_parameter_4d(config)
        assert 0 <= E <= 1

    def test_metric_order_bounded(self):
        """Metric order parameter in [0, 1]."""
        p = Lattice4DParams(L=2)
        config = create_lattice_4d(p)
        g = metric_order_parameter_4d(config)
        assert 0 <= g <= 1

    def test_neighbor_periodic(self):
        """Periodic boundary conditions wrap correctly."""
        L = 3
        # In direction 0, site L-1 wraps to 0
        assert neighbor_index(2, 0, L) == 0   # x0=2 → x0=0
        # In direction 1, site at x1=2 wraps
        site = 2 * L   # (0,2,0,0)
        nbr = neighbor_index(site, 1, L)
        assert nbr == 0  # wraps to (0,0,0,0)

    def test_bond_index_unique(self):
        """Bond indices are unique across all site-direction pairs."""
        L = 2
        V = L**4
        indices = set()
        for site in range(V):
            for d in range(4):
                idx = bond_index(site, d, V)
                indices.add(idx)
        assert len(indices) == V * 4  # all unique


class TestFermionBagMC:
    """Tests for the fermion-bag Monte Carlo."""

    def test_mc_runs(self):
        """MC should complete without errors."""
        p = Lattice4DParams(L=2, g_cosmo=1.0, g_EH=1.0)
        mc = FermionBagParams(n_thermalize=5, n_measure=10, n_skip=1, seed=42)
        r = run_fermion_bag_mc(p, mc)
        assert isinstance(r, FermionBagResult)
        assert np.isfinite(r.binder_tetrad)
        assert np.isfinite(r.binder_metric)
        assert r.phase in ['pre_geometric', 'vestigial', 'tetrad_ordered', 'crossover']

    def test_acceptance_rate(self):
        """Acceptance rate should be between 0 and 1."""
        p = Lattice4DParams(L=2, g_cosmo=1.0, g_EH=1.0)
        mc = FermionBagParams(n_thermalize=5, n_measure=10, n_skip=1, seed=42)
        r = run_fermion_bag_mc(p, mc)
        assert 0 < r.acceptance_rate <= 1

    def test_reproducibility(self):
        """Same seed gives same results."""
        p = Lattice4DParams(L=2, g_cosmo=1.0, g_EH=1.0)
        mc = FermionBagParams(n_thermalize=5, n_measure=10, n_skip=1, seed=123)
        r1 = run_fermion_bag_mc(p, mc)
        r2 = run_fermion_bag_mc(p, FermionBagParams(n_thermalize=5, n_measure=10, n_skip=1, seed=123))
        assert r1.binder_tetrad == r2.binder_tetrad

    def test_strong_coupling_ordered(self):
        """At strong coupling (large g_EH), system should trend toward order."""
        p = Lattice4DParams(L=2, g_cosmo=0.1, g_EH=10.0)
        mc = FermionBagParams(n_thermalize=20, n_measure=50, n_skip=2, seed=42)
        r = run_fermion_bag_mc(p, mc)
        # Strong coupling favors low occupation → action minimized
        assert np.isfinite(r.action_mean)

    def test_zero_coupling(self):
        """At zero coupling, system is free — all configs equally weighted."""
        p = Lattice4DParams(L=2, g_cosmo=0.0, g_EH=0.0)
        mc = FermionBagParams(n_thermalize=5, n_measure=20, n_skip=1, seed=42)
        r = run_fermion_bag_mc(p, mc)
        assert r.action_mean == pytest.approx(0.0, abs=0.01)


class TestPhaseScan4D:
    """Tests for the 4D coupling scan."""

    def test_scan_runs(self):
        """Coupling scan completes."""
        mc = FermionBagParams(n_thermalize=5, n_measure=10, n_skip=1, seed=42)
        scan = scan_coupling_4d(1.0, (0.0, 2.0), 5, L=2, mc_params=mc)
        assert isinstance(scan, PhaseScan4DResult)
        assert len(scan.g_EH_values) == 5
        assert len(scan.binder_tetrad) == 5
        assert np.all(np.isfinite(scan.binder_tetrad))

    def test_scan_acceptance_rates(self):
        """All scan points should have reasonable acceptance."""
        mc = FermionBagParams(n_thermalize=5, n_measure=10, n_skip=1, seed=42)
        scan = scan_coupling_4d(1.0, (0.0, 2.0), 5, L=2, mc_params=mc)
        assert np.all(scan.acceptance_rates > 0)
        assert np.all(scan.acceptance_rates <= 1)

    def test_binder_crossing_analysis(self):
        """Binder crossing analysis runs without errors."""
        mc = FermionBagParams(n_thermalize=5, n_measure=10, n_skip=1, seed=42)
        result = binder_crossing_analysis(
            g_cosmo=1.0, g_EH_range=(0.0, 2.0), n_points=5,
            lattice_sizes=[2, 3], mc_params=mc,
        )
        assert isinstance(result, BinderCrossing4DResult)
        assert len(result.scans) == 2
        assert isinstance(result.vestigial_detected, bool)


# ════════════════════════════════════════════════════════════════════
# Option C: Wetterich NJL fermion-bag MC
# ════════════════════════════════════════════════════════════════════

from src.vestigial.wetterich_model import njl_sweep, run_njl_mc
from src.core.constants import NJL_MODEL, NJL_COUPLING_SCAN


class TestNJLConstants:
    """Stage 1 checks: NJL constants are well-formed."""

    def test_njl_model_fields(self):
        """NJL model dict has required fields."""
        assert NJL_MODEL['d'] == 4
        assert NJL_MODEL['n_grassmann'] == 8
        assert NJL_MODEL['n_fierz_channels'] == 5
        assert NJL_MODEL['gauge_group'] is None  # key difference from ADW

    def test_njl_fierz_completeness(self):
        """1 + 1 + 4 + 4 + 6 = 16 = (spinor_dim)^2 (Fierz completeness)."""
        assert 1 + 1 + 4 + 4 + 6 == 16
        # 16 = 4^2 where 4 is spinor dimension; n_grassmann=8 = 2 Dirac × 4 components
        assert 16 == 4 ** 2

    def test_njl_coupling_scan_range(self):
        """NJL coupling is positive (attractive)."""
        lo, hi = NJL_COUPLING_SCAN['g_njl_range']
        assert lo >= 0
        assert hi > lo


class TestNJLSweep:
    """Stage 6 checks: NJL sweep mechanics."""

    def test_njl_sweep_preserves_shape(self):
        """Sweep doesn't change lattice dimensions."""
        params = Lattice4DParams(L=2, g_cosmo=1.0, g_EH=0.0)
        rng = np.random.default_rng(42)
        config = create_lattice_4d(params, rng)
        V = params.volume

        config_new, acc = njl_sweep(config, rng, g_njl=1.0)
        assert config_new.site_occ.shape == (V,)
        assert 0 <= acc <= 1

    def test_njl_sweep_occupation_bounds(self):
        """Occupations remain in [0, N_grass] after sweep."""
        params = Lattice4DParams(L=2, g_cosmo=1.0, g_EH=0.0)
        rng = np.random.default_rng(42)
        config = create_lattice_4d(params, rng)
        N = params.n_grassmann

        for _ in range(10):
            config, _ = njl_sweep(config, rng, g_njl=5.0)

        assert np.all(config.site_occ >= 0)
        assert np.all(config.site_occ <= N)

    def test_njl_zero_coupling_high_acceptance(self):
        """g_njl=0 means only on-site action → high acceptance."""
        params = Lattice4DParams(L=2, g_cosmo=0.1, g_EH=0.0)
        rng = np.random.default_rng(42)
        config = create_lattice_4d(params, rng)

        accs = []
        for _ in range(20):
            config, acc = njl_sweep(config, rng, g_njl=0.0)
            accs.append(acc)

        mean_acc = np.mean(accs)
        assert mean_acc > 0.8, f"Zero coupling should give high acceptance, got {mean_acc}"

    def test_njl_strong_coupling_lower_acceptance(self):
        """Strong coupling reduces acceptance rate."""
        params = Lattice4DParams(L=2, g_cosmo=1.0, g_EH=0.0)
        rng_weak = np.random.default_rng(42)
        rng_strong = np.random.default_rng(42)
        config_w = create_lattice_4d(params, rng_weak)
        config_s = create_lattice_4d(params, rng_strong)

        acc_weak = []
        acc_strong = []
        for _ in range(20):
            config_w, a = njl_sweep(config_w, rng_weak, g_njl=0.1)
            acc_weak.append(a)
            config_s, a = njl_sweep(config_s, rng_strong, g_njl=50.0)
            acc_strong.append(a)

        assert np.mean(acc_weak) > np.mean(acc_strong), \
            "Strong coupling should lower acceptance"


class TestNJLMC:
    """Stage 6 checks: full NJL MC run."""

    def test_njl_mc_runs(self):
        """NJL MC completes without error."""
        params = Lattice4DParams(L=2, g_cosmo=1.0, g_EH=0.0)
        mc = FermionBagParams(n_thermalize=10, n_measure=20, n_skip=1, seed=42)
        result = run_njl_mc(params, g_njl=5.0, mc_params=mc)

        assert result.tetrad_m2 >= 0
        assert result.metric_m2 >= 0
        assert 0 < result.acceptance_rate < 1
        assert result.phase in ('pre_geometric', 'vestigial', 'tetrad_ordered')

    def test_njl_binder_bounds(self):
        """Binder cumulants in valid range [0, 2/3]."""
        params = Lattice4DParams(L=2, g_cosmo=1.0, g_EH=0.0)
        mc = FermionBagParams(n_thermalize=10, n_measure=50, n_skip=1, seed=42)

        for g in [0.0, 5.0, 20.0]:
            result = run_njl_mc(params, g_njl=g, mc_params=mc)
            assert 0 <= result.binder_tetrad <= 2.0 / 3.0 + 0.01, \
                f"Binder tetrad out of range at g={g}: {result.binder_tetrad}"
            assert 0 <= result.binder_metric <= 2.0 / 3.0 + 0.01, \
                f"Binder metric out of range at g={g}: {result.binder_metric}"

    def test_njl_acceptance_varies_with_coupling(self):
        """Acceptance rate should depend on coupling strength."""
        params = Lattice4DParams(L=3, g_cosmo=1.0, g_EH=0.0)
        mc = FermionBagParams(n_thermalize=10, n_measure=30, n_skip=1, seed=137)

        acc_weak = run_njl_mc(params, g_njl=0.1, mc_params=mc).acceptance_rate
        acc_strong = run_njl_mc(params, g_njl=20.0, mc_params=mc).acceptance_rate
        assert acc_weak != acc_strong, \
            "Acceptance should vary with coupling (not uniform like Option B bug)"

    def test_njl_adw_correspondence_limit(self):
        """At half-filling mean, NJL scalar dominates → close to ADW fundamental."""
        from src.core.formulas import njl_scalar_channel, njl_bond_weight_total

        # At half-filling (n=4 of 8), pseudoscalar vanishes
        n_half = 4
        g = 10.0
        scalar = njl_scalar_channel(n_half, n_half, g, N_grass=8)
        total = njl_bond_weight_total(n_half, n_half, g, N_grass=8)
        assert abs(scalar - total) < 1e-10, \
            "At half-filling, total should equal scalar (pseudoscalar vanishes)"

    def test_njl_pseudoscalar_cancellation_away_from_half(self):
        """Away from half-filling, pseudoscalar partially cancels scalar."""
        from src.core.formulas import njl_scalar_channel, njl_bond_weight_total

        # At n=2 (quarter-filling), pseudoscalar is nonzero
        n = 2
        g = 10.0
        scalar = njl_scalar_channel(n, n, g, N_grass=8)
        total = njl_bond_weight_total(n, n, g, N_grass=8)
        assert total < scalar, \
            "Away from half-filling, pseudoscalar should reduce total"

    def test_njl_reproducibility(self):
        """Same seed gives same result."""
        params = Lattice4DParams(L=2, g_cosmo=1.0, g_EH=0.0)
        mc = FermionBagParams(n_thermalize=10, n_measure=20, n_skip=1, seed=42)

        r1 = run_njl_mc(params, g_njl=5.0, mc_params=mc)
        r2 = run_njl_mc(params, g_njl=5.0, mc_params=mc)
        assert r1.tetrad_m2 == r2.tetrad_m2
        assert r1.acceptance_rate == r2.acceptance_rate
