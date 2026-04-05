"""Tests for the tetrad gap equation formulas (Phase 5d Wave 1).

Validates:
1. Gap integral properties: positivity, monotonicity, limits
2. Critical coupling: matches V_eff, correct scaling
3. Gap operator: fixed-point structure, trivial/nontrivial solutions
4. Cross-consistency: integral formulation matches V_eff formulation
"""

import numpy as np
import pytest

from src.core.formulas import (
    adw_critical_coupling,
    tetrad_critical_coupling_integral,
    tetrad_density_of_states,
    tetrad_gap_integral,
    tetrad_gap_operator,
    tetrad_gap_solution,
)


# ══════════════════════════════════════════════════════
# Gap integral properties
# ══════════════════════════════════════════════════════


class TestGapIntegral:
    """Tests for I(Δ) = ∫₀^Λ ρ(p)/(p²+Δ²) dp."""

    def test_I0_formula(self):
        """I(0) = c₄·Λ²/2 = Λ²/(8π²)."""
        Lambda = 3.0
        I0 = tetrad_gap_integral(0, Lambda)
        expected = Lambda**2 / (8 * np.pi**2)
        assert abs(I0 - expected) < 1e-12

    def test_I0_positive(self):
        """I(0) > 0 for any Λ > 0."""
        for Lambda in [0.1, 1.0, np.pi, 10.0]:
            assert tetrad_gap_integral(0, Lambda) > 0

    def test_positive(self):
        """I(Δ) > 0 for Δ ≥ 0 and Λ > 0."""
        Lambda = np.pi
        for Delta in [0, 0.1, 0.5, 1.0, 2.0]:
            assert tetrad_gap_integral(Delta, Lambda) > 0

    def test_strictly_decreasing(self):
        """I(Δ₁) > I(Δ₂) when 0 ≤ Δ₁ < Δ₂."""
        Lambda = np.pi
        deltas = [0, 0.1, 0.5, 1.0, 2.0, 5.0]
        values = [tetrad_gap_integral(d, Lambda) for d in deltas]
        for i in range(len(values) - 1):
            assert values[i] > values[i + 1], (
                f"I({deltas[i]}) = {values[i]} should be > I({deltas[i+1]}) = {values[i+1]}"
            )

    def test_tends_to_zero(self):
        """I(Δ) → 0 as Δ → ∞."""
        Lambda = np.pi
        I_large = tetrad_gap_integral(1000, Lambda)
        assert I_large < 1e-4, f"I(1000) = {I_large} should be near zero"

    def test_upper_bound(self):
        """I(Δ) ≤ I(0) for all Δ ≥ 0."""
        Lambda = np.pi
        I0 = tetrad_gap_integral(0, Lambda)
        for Delta in [0.01, 0.1, 1.0, 5.0]:
            assert tetrad_gap_integral(Delta, Lambda) <= I0 + 1e-12

    def test_continuity_at_zero(self):
        """I(ε) → I(0) as ε → 0⁺."""
        Lambda = np.pi
        I0 = tetrad_gap_integral(0, Lambda)
        I_eps = tetrad_gap_integral(1e-8, Lambda)
        assert abs(I_eps - I0) < 1e-6, f"|I(ε) - I(0)| = {abs(I_eps - I0)} too large"


# ══════════════════════════════════════════════════════
# Critical coupling
# ══════════════════════════════════════════════════════


class TestCriticalCoupling:
    """Tests for G_c = 1/(N_f · I(0)) = 8π²/(N_f · Λ²)."""

    def test_matches_veff(self):
        """G_c from integral formulation matches V_eff formulation."""
        for Lambda in [1.0, np.pi, 5.0]:
            for N_f in [1, 2, 4]:
                Gc_int = tetrad_critical_coupling_integral(Lambda, N_f)
                Gc_veff = adw_critical_coupling(Lambda, N_f)
                assert abs(Gc_int - Gc_veff) < 1e-10, (
                    f"G_c mismatch at Λ={Lambda}, N_f={N_f}: "
                    f"integral={Gc_int}, V_eff={Gc_veff}"
                )

    def test_positive(self):
        """G_c > 0 for Λ > 0 and N_f > 0."""
        assert tetrad_critical_coupling_integral(np.pi, 2) > 0

    def test_explicit_formula(self):
        """G_c = 8π²/(N_f · Λ²) numerically."""
        Lambda = 2.0
        N_f = 3
        Gc = tetrad_critical_coupling_integral(Lambda, N_f)
        expected = 8 * np.pi**2 / (N_f * Lambda**2)
        assert abs(Gc - expected) < 1e-10

    def test_scaling_with_Lambda(self):
        """G_c ∝ 1/Λ². Doubling Λ divides G_c by 4."""
        N_f = 2
        Gc1 = tetrad_critical_coupling_integral(1.0, N_f)
        Gc2 = tetrad_critical_coupling_integral(2.0, N_f)
        assert abs(Gc1 / Gc2 - 4.0) < 1e-10

    def test_scaling_with_Nf(self):
        """G_c ∝ 1/N_f. Doubling N_f halves G_c."""
        Lambda = np.pi
        Gc1 = tetrad_critical_coupling_integral(Lambda, 1)
        Gc2 = tetrad_critical_coupling_integral(Lambda, 2)
        assert abs(Gc1 / Gc2 - 2.0) < 1e-10


# ══════════════════════════════════════════════════════
# Gap operator and solutions
# ══════════════════════════════════════════════════════


class TestGapOperator:
    """Tests for the gap operator f_G(Δ) = G·N_f·Δ·I(Δ)."""

    def test_trivial_fixed_point(self):
        """f_G(0) = 0 for any G."""
        assert tetrad_gap_operator(0, 5.0, np.pi, 2) == 0

    def test_nonneg(self):
        """f_G(Δ) ≥ 0 for Δ ≥ 0, G > 0."""
        assert tetrad_gap_operator(1.0, 5.0, np.pi, 2) > 0

    def test_subcritical_contraction(self):
        """For G < G_c: f_G(Δ)/Δ < 1 for all Δ > 0 (contraction)."""
        Lambda = np.pi
        N_f = 2
        Gc = tetrad_critical_coupling_integral(Lambda, N_f)
        G = 0.5 * Gc
        for Delta in [0.01, 0.1, 0.5, 1.0, 2.0]:
            ratio = tetrad_gap_operator(Delta, G, Lambda, N_f) / Delta
            assert ratio < 1.0, f"f_G(Δ)/Δ = {ratio} should be < 1 subcritically"

    def test_supercritical_expansion_at_origin(self):
        """For G > G_c: f_G(Δ)/Δ > 1 near Δ = 0 (expansion)."""
        Lambda = np.pi
        N_f = 2
        Gc = tetrad_critical_coupling_integral(Lambda, N_f)
        G = 2.0 * Gc
        Delta_small = 0.001
        ratio = tetrad_gap_operator(Delta_small, G, Lambda, N_f) / Delta_small
        assert ratio > 1.0, f"f_G(Δ)/Δ = {ratio} should be > 1 supercritically near 0"


class TestGapSolution:
    """Tests for the gap equation solver."""

    def test_subcritical_returns_zero(self):
        """For G < G_c, only trivial solution Δ = 0."""
        Lambda = np.pi
        N_f = 2
        Gc = tetrad_critical_coupling_integral(Lambda, N_f)
        assert tetrad_gap_solution(0.5 * Gc, Lambda, N_f) == 0.0

    def test_supercritical_returns_positive(self):
        """For G > G_c, nontrivial Δ* > 0."""
        Lambda = np.pi
        N_f = 2
        Gc = tetrad_critical_coupling_integral(Lambda, N_f)
        Delta_star = tetrad_gap_solution(2 * Gc, Lambda, N_f)
        assert Delta_star > 0, f"Δ* should be > 0 for G = 2·G_c"

    def test_fixed_point_equation(self):
        """Solution satisfies Δ* = f_G(Δ*)."""
        Lambda = np.pi
        N_f = 2
        Gc = tetrad_critical_coupling_integral(Lambda, N_f)
        G = 3.0 * Gc
        Delta_star = tetrad_gap_solution(G, Lambda, N_f)
        f_Delta = tetrad_gap_operator(Delta_star, G, Lambda, N_f)
        assert abs(Delta_star - f_Delta) / Delta_star < 1e-8, (
            f"Δ* = {Delta_star}, f_G(Δ*) = {f_Delta}"
        )

    def test_monotone_in_G(self):
        """Δ*(G) is increasing in G for G > G_c."""
        Lambda = np.pi
        N_f = 2
        Gc = tetrad_critical_coupling_integral(Lambda, N_f)
        G_values = [1.5 * Gc, 2.0 * Gc, 3.0 * Gc, 5.0 * Gc]
        solutions = [tetrad_gap_solution(G, Lambda, N_f) for G in G_values]
        for i in range(len(solutions) - 1):
            assert solutions[i] < solutions[i + 1], (
                f"Δ*({G_values[i]:.2f}) = {solutions[i]:.4f} should be < "
                f"Δ*({G_values[i+1]:.2f}) = {solutions[i+1]:.4f}"
            )

    def test_bounded_by_Lambda(self):
        """Gap solution Δ* ≤ Λ (bounded by cutoff)."""
        Lambda = np.pi
        N_f = 2
        Gc = tetrad_critical_coupling_integral(Lambda, N_f)
        for mult in [1.5, 2, 5, 10]:
            Delta_star = tetrad_gap_solution(mult * Gc, Lambda, N_f)
            assert Delta_star <= Lambda + 1e-10, (
                f"Δ* = {Delta_star} should be ≤ Λ = {Lambda} for G = {mult}·G_c"
            )
        # At moderate coupling, strict bound holds
        Delta_moderate = tetrad_gap_solution(1.5 * Gc, Lambda, N_f)
        assert Delta_moderate < 0.95 * Lambda, (
            f"Δ*(1.5·G_c) = {Delta_moderate} should be well below Λ"
        )

    def test_critical_point_zero(self):
        """At G = G_c, solution is exactly 0 (bifurcation point)."""
        Lambda = np.pi
        N_f = 2
        Gc = tetrad_critical_coupling_integral(Lambda, N_f)
        assert tetrad_gap_solution(Gc, Lambda, N_f) == 0.0


# ══════════════════════════════════════════════════════
# Density of states
# ══════════════════════════════════════════════════════


class TestDensityOfStates:
    """Tests for ρ(p) = c₄ · p³."""

    def test_nonneg(self):
        """ρ(p) ≥ 0 for p ≥ 0."""
        for p in [0, 0.1, 1.0, 10.0]:
            assert tetrad_density_of_states(p) >= 0

    def test_zero_at_origin(self):
        """ρ(0) = 0."""
        assert tetrad_density_of_states(0) == 0

    def test_c4_coefficient(self):
        """c₄ = 1/(4π²)."""
        rho_1 = tetrad_density_of_states(1.0)
        expected = 1 / (4 * np.pi**2)
        assert abs(rho_1 - expected) < 1e-12

    def test_cubic_scaling(self):
        """ρ(2p) = 8·ρ(p) (cubic in p)."""
        p = 1.5
        assert abs(tetrad_density_of_states(2 * p) / tetrad_density_of_states(p) - 8.0) < 1e-10
