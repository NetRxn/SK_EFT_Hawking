"""Phase 6a Wave 1 tests: emergent G_N + linearized Einstein equations."""

from __future__ import annotations

import math

import numpy as np
import pytest

from src.core.constants import GRAV_PARAMS
from src.core.formulas import (
    G_N_emergent,
    G_N_emergent_at_coupling,
    G_N_emergent_matches_observed,
    G_N_sakharov,
    acceleration_flrw,
    alpha_ADW_linear_ansatz,
    conservation_flrw_rate,
    friedmann_consistency_residual,
    hubble_squared_flrw,
    linearized_einstein_de_donder,
    planck_mass_emergent_gev,
    trace_reverse_perturbation,
)
from src.emergent_gravity import (
    G_N_emerg_at_coupling_grid,
    G_N_emerg_grid,
    G_N_emerg_match_grid,
    G_N_emerg_match_locus_lambda,
    G_N_emerg_planck_anchor_alpha,
    VergelesPositivityCheck,
    deDonder_gauge_residual,
    linearized_einstein_de_donder_array,
    minkowski_metric,
    minkowski_trace,
    natural_parameter_grid,
    sakharov_baseline_consistency,
    trace_reversed_perturbation_array,
    vergeles_alpha_natural_range,
)


class TestSakharovInducedGravity:
    """Section 4 of LinearizedEFE.lean."""

    def test_sakharov_positive(self):
        g_n = G_N_sakharov(1.0e16, 15)
        assert g_n > 0

    def test_sakharov_inverse_lambda_squared(self):
        # G_N_sakharov ∝ 1/Λ²
        g_low = G_N_sakharov(1.0e15, 15)
        g_high = G_N_sakharov(1.0e16, 15)
        assert g_low > g_high
        # Ratio = (10)² = 100
        assert g_low / g_high == pytest.approx(100.0, rel=1e-9)

    def test_sakharov_inverse_n_f(self):
        # G_N_sakharov ∝ 1/N_f
        g_low = G_N_sakharov(1.0e16, 15)
        g_high = G_N_sakharov(1.0e16, 30)
        assert g_low / g_high == pytest.approx(2.0, rel=1e-9)

    def test_sakharov_planck_value(self):
        # At Λ = M_P with N_f = 45 (3 generations × 15 Weyl), Sakharov G_N
        # should land within 16% of observed G_N (Lean: ratio = 0.838)
        m_p = GRAV_PARAMS["M_PLANCK_GEV"]
        g_n = G_N_sakharov(m_p, 45)
        ratio = g_n / GRAV_PARAMS["G_N_OBS_GEV_M2"]
        assert 0.8 <= ratio <= 0.9

    def test_sakharov_invalid_inputs(self):
        with pytest.raises(ValueError):
            G_N_sakharov(0.0, 15)
        with pytest.raises(ValueError):
            G_N_sakharov(1.0e16, 0.0)
        with pytest.raises(ValueError):
            G_N_sakharov(-1.0, 15)


class TestG_N_Emergent:
    """Section 5 of LinearizedEFE.lean: ADW emergent G_N."""

    def test_at_alpha_one_equals_sakharov(self):
        # G_N_emerg(Λ, N_f, 1) = G_N_sakharov(Λ, N_f)
        g_emerg = G_N_emergent(1.0e16, 15, alpha_adw=1.0)
        g_sak = G_N_sakharov(1.0e16, 15)
        assert g_emerg == pytest.approx(g_sak, rel=1e-12)

    def test_emerg_positive_iff_alpha_positive(self):
        # Lean: G_N_emerg_sign
        assert G_N_emergent(1.0e16, 15, alpha_adw=2.0) > 0
        assert G_N_emergent(1.0e16, 15, alpha_adw=0.5) > 0
        # alpha = 0 gives zero
        assert G_N_emergent(1.0e16, 15, alpha_adw=0.0) == 0.0

    def test_match_observed_returns_bool(self):
        # Lean: G_N_emerg_match_locus
        result = G_N_emergent_matches_observed(1.0e16, 15, 1.0)
        assert isinstance(result, bool)

    def test_match_at_planck_anchor_with_alpha_star(self):
        # At Λ = M_P, α* = N_f / (12π) gives exact match.
        # The relative error is float-precision (~1e-6), driven by the
        # M_P_GEV constant being accurate to 7 significant figures.
        m_p = GRAV_PARAMS["M_PLANCK_GEV"]
        g_n_obs = GRAV_PARAMS["G_N_OBS_GEV_M2"]
        for n_f in [15, 16, 45, 48]:
            alpha_star = n_f / (12.0 * math.pi)
            g_n = G_N_emergent(m_p, n_f, alpha_star)
            assert abs(g_n - g_n_obs) / g_n_obs < 1e-5

    def test_planck_mass_emergent(self):
        # M_P^emerg = √(N_f Λ² / (12π α_ADW))
        m_p_emerg = planck_mass_emergent_gev(1.0e19, 15, 1.0)
        # Should be ~ M_P scale
        assert 1.0e18 < m_p_emerg < 1.0e20


class TestG_N_MatchLocus:
    """Closed-form Λ-locus from Lean theorem G_N_emerg_match_locus."""

    def test_planck_anchor_alpha(self):
        # Lean: G_N_emerg_match_at_planck_anchor
        # At Λ = M_P, the matching α is N_f/(12π).
        for n_f, expected in [
            (15, 0.3979),
            (16, 0.4244),
            (45, 1.1937),
            (48, 1.2732),
        ]:
            alpha = G_N_emerg_planck_anchor_alpha(n_f)
            assert alpha == pytest.approx(expected, rel=1e-3)

    def test_match_locus_lambda_at_alpha_one(self):
        # At α_ADW = 1, the matching Λ should be close to M_P for natural N_f
        m_p = GRAV_PARAMS["M_PLANCK_GEV"]
        for n_f in [15, 45]:
            lam = G_N_emerg_match_locus_lambda(n_f, 1.0)
            ratio = lam / m_p
            # Should land within an order of magnitude of M_P
            assert 0.1 < ratio < 10.0

    def test_match_locus_consistent_with_grid(self):
        # The closed-form locus should hit the match grid exactly.
        n_f = 45
        alpha = 1.0
        lam_locus = G_N_emerg_match_locus_lambda(n_f, alpha)
        # Verify by direct evaluation
        g_n = G_N_emergent(lam_locus, n_f, alpha)
        assert abs(g_n - GRAV_PARAMS["G_N_OBS_GEV_M2"]) / GRAV_PARAMS["G_N_OBS_GEV_M2"] < 1e-9

    def test_invalid_inputs(self):
        with pytest.raises(ValueError):
            G_N_emerg_match_locus_lambda(-1.0, 1.0)
        with pytest.raises(ValueError):
            G_N_emerg_match_locus_lambda(15, 0.0)
        with pytest.raises(ValueError):
            G_N_emerg_planck_anchor_alpha(-1.0)


class TestLinearizedEFE:
    """Sections 1-3 of LinearizedEFE.lean: metric, trace, linearized Einstein."""

    def test_minkowski_metric_signature(self):
        eta = minkowski_metric()
        assert eta[0, 0] == -1.0
        assert eta[1, 1] == 1.0
        assert eta[2, 2] == 1.0
        assert eta[3, 3] == 1.0
        # Off-diagonal zero
        for i in range(4):
            for j in range(4):
                if i != j:
                    assert eta[i, j] == 0.0

    def test_minkowski_trace_signature(self):
        # tr_η h = -h₀₀ + h₁₁ + h₂₂ + h₃₃ (Lean: trace_h_eq)
        h = np.array([
            [10.0, 0.0, 0.0, 0.0],
            [0.0, 1.0, 0.0, 0.0],
            [0.0, 0.0, 2.0, 0.0],
            [0.0, 0.0, 0.0, 3.0],
        ])
        assert minkowski_trace(h) == pytest.approx(-10.0 + 1.0 + 2.0 + 3.0)

    def test_minkowski_trace_eta_self(self):
        # tr(η) = 4 (Lean: trace_eta_self)
        eta = minkowski_metric()
        assert minkowski_trace(eta) == pytest.approx(4.0)

    def test_trace_reverse_involutive(self):
        # h̄̄ = h (Lean: trace_reverse_involutive)
        h = np.array([
            [0.1, 0.02, 0.0, 0.0],
            [0.02, 0.05, 0.0, 0.0],
            [0.0, 0.0, 0.05, 0.01],
            [0.0, 0.0, 0.01, 0.05],
        ])
        h_bar = trace_reversed_perturbation_array(h)
        h_back = trace_reversed_perturbation_array(h_bar)
        assert np.allclose(h, h_back, atol=1e-15)

    def test_trace_reverse_negates_trace(self):
        # tr(h̄) = -tr(h) (Lean: trace_reverse_negates_trace)
        h = np.array([
            [0.1, 0.0, 0.0, 0.0],
            [0.0, 0.05, 0.0, 0.0],
            [0.0, 0.0, 0.05, 0.0],
            [0.0, 0.0, 0.0, 0.05],
        ])
        tr_h = minkowski_trace(h)
        h_bar = trace_reversed_perturbation_array(h)
        tr_h_bar = minkowski_trace(h_bar)
        assert tr_h_bar == pytest.approx(-tr_h, abs=1e-15)

    def test_linearized_einstein_zero_at_zero(self):
        # Lean: linEinstein_zero_at_zero
        zero = np.zeros((4, 4))
        G = linearized_einstein_de_donder_array(2.5, zero)
        assert np.allclose(G, np.zeros((4, 4)))

    def test_linearized_einstein_linear(self):
        # Lean: linEinstein_linear — linearity in h̄
        h1 = np.diag([0.1, 0.2, 0.3, 0.4])
        h2 = np.diag([0.5, 0.6, 0.7, 0.8])
        k_sq = 1.5
        G_sum = linearized_einstein_de_donder_array(k_sq, h1 + h2)
        G_split = (
            linearized_einstein_de_donder_array(k_sq, h1)
            + linearized_einstein_de_donder_array(k_sq, h2)
        )
        assert np.allclose(G_sum, G_split, atol=1e-15)

    def test_linearized_einstein_symm_inherits(self):
        # G^(1) is symmetric if h̄ is
        h_bar = np.array([
            [0.1, 0.05, 0.0, 0.0],
            [0.05, 0.2, 0.0, 0.0],
            [0.0, 0.0, 0.3, 0.07],
            [0.0, 0.0, 0.07, 0.4],
        ])
        G = linearized_einstein_de_donder_array(2.0, h_bar)
        assert np.allclose(G, G.T, atol=1e-15)

    def test_de_donder_residual_zero_for_constant_h(self):
        # If h̄ is constant in spacetime, k_μ h̄^μν = 0 for k_μ = 0.
        h = np.eye(4) * 0.1
        h_bar = trace_reversed_perturbation_array(h)
        residual = deDonder_gauge_residual(np.zeros(4), h_bar)
        assert np.allclose(residual, np.zeros(4))

    def test_de_donder_residual_pure_temporal(self):
        # k_μ = (k_0, 0, 0, 0); k^μ = (-k_0, 0, 0, 0)
        # residual_ν = k^μ h̄_μν = -k_0 h̄_0ν
        k0 = 0.5
        k = np.array([k0, 0.0, 0.0, 0.0])
        h_bar = np.array([
            [1.0, 0.5, 0.3, 0.1],
            [0.5, 0.0, 0.0, 0.0],
            [0.3, 0.0, 0.0, 0.0],
            [0.1, 0.0, 0.0, 0.0],
        ])
        residual = deDonder_gauge_residual(k, h_bar)
        expected = -k0 * h_bar[0, :]
        assert np.allclose(residual, expected)


class TestVergelesUnitarity:
    """Tracked-hypothesis sanity checks."""

    def test_sakharov_baseline_consistency(self):
        # At α_ADW = 1, G_N_emerg = G_N_sakharov
        ok = sakharov_baseline_consistency(1.0e16, 15)
        assert ok is True

    def test_natural_range_alpha_one(self):
        chk = vergeles_alpha_natural_range(1.0)
        assert isinstance(chk, VergelesPositivityCheck)
        assert chk.alpha_in_natural_range
        assert chk.alpha_positive
        assert chk.sakharov_baseline_match
        assert chk.alpha_adw == 1.0

    def test_natural_range_low_edge(self):
        chk = vergeles_alpha_natural_range(0.1)
        assert chk.alpha_in_natural_range
        assert chk.alpha_positive

    def test_natural_range_above_high_edge(self):
        # Outside natural range
        chk = vergeles_alpha_natural_range(20.0)
        assert not chk.alpha_in_natural_range
        assert chk.alpha_positive  # but still positive

    def test_natural_range_negative_alpha(self):
        # Wrong-sign emergent gravity
        chk = vergeles_alpha_natural_range(-1.0)
        assert not chk.alpha_in_natural_range
        assert not chk.alpha_positive


class TestParameterGrid:
    """natural_parameter_grid integration."""

    def test_grid_shapes(self):
        grid = natural_parameter_grid(n_lambda=10, n_alpha=8)
        assert grid["lambda_uv"].shape == (10,)
        assert grid["alpha_adw"].shape == (8,)
        assert grid["g_n_grid"].shape == (10, 8)
        assert grid["match_grid"].shape == (10, 8)
        assert grid["locus_lambda"].shape == (8,)

    def test_grid_match_locus_consistent(self):
        # The locus_lambda values must reproduce match=True at each alpha
        grid = natural_parameter_grid(n_lambda=20, n_alpha=10)
        n_f = grid["n_f"]
        for j, alpha in enumerate(grid["alpha_adw"]):
            lam_match = grid["locus_lambda"][j]
            g_n = G_N_emergent(lam_match, n_f, alpha)
            ratio = g_n / GRAV_PARAMS["G_N_OBS_GEV_M2"]
            assert abs(ratio - 1.0) < 1e-9

    def test_grid_match_count_nonzero(self):
        # At least some cells in the grid should match observed G_N
        grid = natural_parameter_grid(n_lambda=80, n_alpha=60)
        assert grid["match_grid"].sum() > 0

    def test_planck_anchor_in_natural_range(self):
        # For SM N_f, the Planck-anchor α* should be inside natural range
        for n_f in [15, 16, 45, 48]:
            alpha_star = G_N_emerg_planck_anchor_alpha(n_f)
            assert GRAV_PARAMS["ALPHA_ADW_LOWER"] <= alpha_star <= GRAV_PARAMS["ALPHA_ADW_UPPER"]


class TestAlphaADWLinearAnsatz:
    """Phase 6a Wave 1 deep-research integration: linear ansatz for α_ADW."""

    def test_at_two_equals_half(self):
        # Lean: alphaADW_linear_at_two
        assert alpha_ADW_linear_ansatz(2.0) == pytest.approx(0.5)

    def test_at_hundred_close_to_one(self):
        # Lean: alphaADW_linear_at_hundred
        assert alpha_ADW_linear_ansatz(100.0) == pytest.approx(0.99)

    def test_positivity_in_broken_phase(self):
        # Lean: alphaADW_linear_positivity (∀ x > 1, α(x) > 0)
        for x in [1.001, 1.5, 2.0, 5.0, 100.0]:
            assert alpha_ADW_linear_ansatz(x) > 0

    def test_critical_collapse_limit(self):
        # Lean: alphaADW_linear_critical_collapse — as x → 1⁺, α → 0
        for x in [1.001, 1.0001, 1.00001]:
            val = alpha_ADW_linear_ansatz(x)
            assert val > 0
            assert val < 0.001

    def test_deep_gap_limit(self):
        # Lean: alphaADW_linear_deep_gap — as x → ∞, α → 1
        for x in [10.0, 100.0, 1000.0, 10000.0]:
            val = alpha_ADW_linear_ansatz(x)
            assert val < 1.0
            assert val > 1.0 - 1.0 / x - 1e-15

    def test_invalid_input(self):
        with pytest.raises(ValueError):
            alpha_ADW_linear_ansatz(0.0)
        with pytest.raises(ValueError):
            alpha_ADW_linear_ansatz(-1.0)


class TestG_N_EmergentAtCoupling:
    """G/G_c-parameterized emergent G_N from deep-research integration."""

    def test_at_two_equals_half_sakharov(self):
        # Lean: G_N_emerg_at_two_with_linear_ansatz
        m_p = GRAV_PARAMS["M_PLANCK_GEV"]
        n_f = 15
        g_n_at_two = G_N_emergent_at_coupling(m_p, n_f, 2.0)
        g_n_sak = G_N_sakharov(m_p, n_f)
        assert g_n_at_two == pytest.approx(0.5 * g_n_sak)

    def test_at_two_with_n_f_45_close_to_observed(self):
        # At Λ = M_P, N_f = 45, G/G_c = 2, the natural anchor:
        # G_N_emerg = 0.5 · G_N_sakharov = 0.5 · 0.838 · G_N_obs ≈ 0.419 G_N_obs
        m_p = GRAV_PARAMS["M_PLANCK_GEV"]
        g_n = G_N_emergent_at_coupling(m_p, 45, 2.0)
        ratio = g_n / GRAV_PARAMS["G_N_OBS_GEV_M2"]
        assert 0.4 <= ratio <= 0.45

    def test_grid_shape(self):
        lam = np.array([1.0e16, 1.0e17, 1.0e18])
        gc = np.array([1.5, 2.0, 5.0])
        grid = G_N_emerg_at_coupling_grid(lam, n_f=15, g_over_g_c_range=gc)
        assert grid.shape == (3, 3)

    def test_grid_default_anchor(self):
        # Default G/G_c = 2 anchor
        lam = np.array([1.0e16, 1.0e19])
        grid = G_N_emerg_at_coupling_grid(lam, n_f=15)
        assert grid.shape == (2, 1)
        # Larger Λ → smaller G_N (∝ 1/Λ²)
        assert grid[0, 0] > grid[1, 0]


# ════════════════════════════════════════════════════════════════════
# Phase 6a Wave 4: FLRW dynamics
# ════════════════════════════════════════════════════════════════════


class TestFLRWFriedmann:
    """FLRW formulas in src.core.formulas."""

    def test_hubble_squared_flat_dust(self):
        # H² = (8πG/3) ρ for flat dust
        rho = 1.0e-26
        g_n = 6.6743e-11
        h_sq = hubble_squared_flrw(rho, g_n)
        expected = (8.0 * math.pi * g_n / 3.0) * rho
        assert h_sq == pytest.approx(expected)

    def test_hubble_squared_with_curvature(self):
        # H² = (8πG/3)ρ - k/a²
        rho = 1.0e-26
        g_n = 6.6743e-11
        h_sq_open = hubble_squared_flrw(rho, g_n, k=-1.0, a=1.0)
        h_sq_flat = hubble_squared_flrw(rho, g_n, k=0.0, a=1.0)
        assert h_sq_open > h_sq_flat

    def test_acceleration_lambda_positive(self):
        # ä/a > 0 for cosmological constant (p = -ρ)
        rho = 1.0e-26
        p = -rho
        a_ddot = acceleration_flrw(rho, p, 6.6743e-11)
        assert a_ddot > 0

    def test_acceleration_dust_negative(self):
        # ä/a < 0 for dust (p = 0, ρ + 3p = ρ > 0)
        rho = 1.0e-26
        a_ddot = acceleration_flrw(rho, 0.0, 6.6743e-11)
        assert a_ddot < 0

    def test_conservation_dust(self):
        # ρ̇ = -3H ρ for dust (w = 0)
        rho = 1.0e-26
        H = 2.193e-18
        rho_dot = conservation_flrw_rate(rho, 0.0, H)
        assert rho_dot == pytest.approx(-3.0 * H * rho)

    def test_conservation_lambda(self):
        # ρ̇ = 0 for cosmological constant (p = -ρ)
        rho = 1.0e-26
        H = 2.193e-18
        rho_dot = conservation_flrw_rate(rho, -rho, H)
        assert rho_dot == pytest.approx(0.0, abs=1e-50)

    def test_friedmann_consistency_residual_lambda(self):
        # For a pure cosmological constant: Ḣ = 0, H² = (8πG/3) ρ_Λ
        rho = 1.0e-26
        p = -rho
        g_n = 6.6743e-11
        H_sq = (8.0 * math.pi * g_n / 3.0) * rho
        H = math.sqrt(H_sq)
        H_dot = 0.0
        residual = friedmann_consistency_residual(rho, p, H, H_dot, g_n)
        assert residual < 1e-50
