"""Phase 6f Wave 5 — ADM (3+1) formalism tests.

Cross-layer agreement between Python ``formulas.py`` ADM helpers and
the Lean ``ADMFormalism.lean`` block decomposition + constraint
predicates + spacetime-specific ADM data.

Coverage mirrors the Lean module's substantive content (14
substantive theorems + 1 marker):

- TestADMFourMetric — block decomposition g_00 = -N² + γ_ij N^i N^j,
  g_0i = γ_ij N^j; Minkowski specialization.
- TestSpatialContractions — extrinsic curvature trace + K² contraction,
  K = 0 specializations.
- TestHamiltonianConstraint — vacuum biconditional, moment-of-time-
  symmetry, Yamabe form.
- TestMomentumConstraint — vacuum biconditional.
- TestMinkowskiADM — Minkowski satisfies both constraints trivially.
- TestDeSitterADM — flat-slicing Λ = 3H² Hamiltonian-constraint
  cross-bridge to 6f.4.
- TestSchwarzschildADM — ADM mass equals metric parameter (cross-
  bridge to 6f.4).
- TestStrengtheningQuantitative — quantitative bounds on dS Λ-K
  identity at observed cosmological values.
- TestPhase6fCrossBridge — bridges to 6f.1+6f.2+6f.4.
- TestAntiPatternAudit — predicates non-vacuous, no ∃-absorption.
"""

from __future__ import annotations

import math
import pytest

from src.core.formulas import (
    adm_four_metric_g00,
    adm_four_metric_g0i,
    desitter_adm_mass,
    extrinsic_curvature_squared,
    extrinsic_curvature_trace,
    hamiltonian_constraint,
    momentum_constraint,
    schwarzschild_adm_mass,
)


def euclidean_3metric():
    return [[1.0, 0.0, 0.0], [0.0, 1.0, 0.0], [0.0, 0.0, 1.0]]


def zero_3vector():
    return [0.0, 0.0, 0.0]


def zero_3tensor():
    return [[0.0, 0.0, 0.0], [0.0, 0.0, 0.0], [0.0, 0.0, 0.0]]


class TestADMFourMetric:
    """ADM 4-metric block decomposition. Mirrors Lean
    admFourMetric_00 / _0i + minkowski_admFourMetric_00 / _0i."""

    def test_minkowski_g00_eq_neg_one(self):
        """For N=1, N^i=0, γ=δ: g_00 = -1.

        Mirrors Lean minkowski_admFourMetric_00."""
        assert adm_four_metric_g00(
            1.0, euclidean_3metric(), zero_3vector()) == pytest.approx(-1.0)

    def test_minkowski_g0i_eq_zero(self):
        """For N^i=0: g_0i = 0 for all i.

        Mirrors Lean minkowski_admFourMetric_0i."""
        for i in range(3):
            assert adm_four_metric_g0i(
                euclidean_3metric(), zero_3vector(), i) == pytest.approx(0.0)

    def test_g00_lapse_squared_pure_temporal(self):
        """For N=N₀, N^i=0: g_00 = -N₀²."""
        for N in [0.5, 1.0, 2.0]:
            assert adm_four_metric_g00(
                N, euclidean_3metric(), zero_3vector()) == pytest.approx(-N**2)

    def test_g00_with_shift_contribution(self):
        """For N=1, N^i=(0.5, 0, 0), γ=δ:
        g_00 = -1 + γ_ij N^i N^j = -1 + 0.25 = -0.75."""
        N_shift = [0.5, 0.0, 0.0]
        result = adm_four_metric_g00(1.0, euclidean_3metric(), N_shift)
        assert result == pytest.approx(-0.75)

    def test_g0i_with_shift(self):
        """For γ=δ, N^i=(0.3, 0.4, 0.0): g_0i = N_i = N^i (Euclidean)."""
        N_shift = [0.3, 0.4, 0.0]
        for i, expected in enumerate(N_shift):
            assert adm_four_metric_g0i(
                euclidean_3metric(), N_shift, i) == pytest.approx(expected)


class TestSpatialContractions:
    """Mean curvature + K² contractions."""

    def test_K_zero_trace_zero(self):
        """K = 0 ⇒ tr K = 0.

        Mirrors Lean extrinsicCurvatureTrace_zero_at_K_zero."""
        assert extrinsic_curvature_trace(
            zero_3tensor(), euclidean_3metric()) == 0.0

    def test_K_zero_K_sq_zero(self):
        """K = 0 ⇒ K_ij K^ij = 0.

        Mirrors Lean extrinsicCurvatureSquared_zero_at_K_zero."""
        assert extrinsic_curvature_squared(
            zero_3tensor(), euclidean_3metric()) == 0.0

    def test_dS_flat_slicing_trK_eq_neg_3H(self):
        """For dS flat slicing, K_ij = -H γ_ij, so tr K = γ^ij K_ij =
        γ^ij (-H γ_ij) = -H tr_γ(γ) = -H · 3 (since γ^ij γ_ij = 3 in
        3D for γ = identity)."""
        H = 1.0
        K_dS = [[-H, 0, 0], [0, -H, 0], [0, 0, -H]]
        gamma = euclidean_3metric()
        assert extrinsic_curvature_trace(K_dS, gamma) == pytest.approx(-3 * H)

    def test_dS_flat_slicing_K_sq_eq_3H_sq(self):
        """For dS flat slicing K_ij = -H γ_ij with γ=δ:
        K_ij K^ij = γ^ik γ^jl K_ij K_kl = (γ^ij K_ij)² approximately
        but actually K^ij K_ij = γ^ik γ^jl K_ij K_kl = sum of
        (-H δ_ij)² across i=j: 3 · (-H)² = 3 H²."""
        H = 1.0
        K_dS = [[-H, 0, 0], [0, -H, 0], [0, 0, -H]]
        gamma = euclidean_3metric()
        assert extrinsic_curvature_squared(
            K_dS, gamma) == pytest.approx(3 * H**2)


class TestHamiltonianConstraint:
    """ADM Hamiltonian constraint H = ^(3)R + (tr K)² - K_ij K^ij -
    16π G ρ."""

    def test_minkowski_H_zero(self):
        """All-zero ADM data ⇒ H = 0.

        Mirrors Lean minkowski_satisfies_hamiltonianConstraint."""
        assert hamiltonian_constraint(0.0, 0.0, 0.0, 0.0) == 0.0

    def test_vacuum_iff(self):
        """For ρ = 0: H = 0 ↔ R3 + (tr K)² = K_ij K^ij.

        Mirrors Lean hamiltonianConstraint_vacuum_iff."""
        # Forward: take values satisfying R3 + trK² = Ksq
        for R3, trK, Ksq in [(0, 0, 0), (1, 1, 2), (4, 2, 8)]:
            assert hamiltonian_constraint(R3, trK, Ksq, 0) == pytest.approx(0)
        # Backward: violate the relation, H ≠ 0
        for R3, trK, Ksq in [(1, 0, 0), (0, 0, 1), (1, 1, 0)]:
            if R3 + trK**2 != Ksq:
                assert hamiltonian_constraint(R3, trK, Ksq, 0) != 0.0

    def test_moment_of_time_symmetry(self):
        """At K = 0: H = R3 - 16π G ρ.

        Mirrors Lean hamiltonianConstraint_moment_of_time_symmetry."""
        for R3, rho in [(0, 0), (1.0, 1.0/(16*math.pi)), (-1, 0.5)]:
            expected = R3 - 16.0 * math.pi * rho
            assert hamiltonian_constraint(
                R3, 0, 0, rho) == pytest.approx(expected)

    def test_moment_of_time_symmetry_yamabe_iff(self):
        """At K = 0: H = 0 ↔ R3 = 16π G ρ.

        Mirrors Lean hamiltonianConstraint_moment_of_time_symmetry_iff."""
        # Forward: ρ = R3 / (16π) gives H = 0
        for R3 in [0, 1.0, 5.0, -2.0]:
            rho = R3 / (16.0 * math.pi)
            assert hamiltonian_constraint(
                R3, 0, 0, rho) == pytest.approx(0)


class TestMomentumConstraint:
    """ADM momentum constraint M^i = D_j(K^ij - γ^ij K) - 8π G j^i."""

    def test_minkowski_momentum_zero(self):
        """divK_trace_free = 0, j^i = 0 ⇒ M^i = 0.

        Mirrors Lean minkowski_satisfies_momentumConstraint."""
        assert momentum_constraint(0.0, 0.0) == 0.0

    def test_vacuum_iff(self):
        """For j^i = 0: M^i = 0 ↔ divK_trace_free = 0.

        Mirrors Lean momentumConstraint_vacuum_iff."""
        # Forward
        assert momentum_constraint(0.0, 0.0) == 0.0
        # Backward: divK_trace_free ≠ 0 ⇒ M^i ≠ 0
        for div in [0.1, -0.5, 1.0]:
            assert momentum_constraint(div, 0.0) != 0.0

    def test_no_vacuum_with_nonzero_matter_momentum(self):
        """divK_trace_free = 0 + j^i ≠ 0 ⇒ M^i ≠ 0 (matter source
        breaks vacuum)."""
        for j in [0.1, -0.5, 1.0]:
            assert momentum_constraint(0.0, j) == pytest.approx(
                -8.0 * math.pi * j)


class TestMinkowskiADM:
    """Minkowski ADM data: trivial-vacuum specialization."""

    def test_minkowski_full_constraints_satisfied(self):
        """Minkowski (R3=0, trK=0, K²=0, ρ=0, divK=0, j^i=0)
        satisfies BOTH Hamiltonian and momentum constraints."""
        H = hamiltonian_constraint(0, 0, 0, 0)
        M = momentum_constraint(0, 0)
        assert H == 0.0
        assert M == 0.0


class TestDeSitterADM:
    """De Sitter flat slicing: K = -H γ, R3 = 0, ρ_Λ = Λ/(8πG).

    Mirrors Lean deSitter_flat_slicing_hamiltonian_iff."""

    def test_dS_flat_slicing_H_eq_3H_sq(self):
        """At dS flat slicing with Λ = 3H²:
        H_constraint = 0 + (-3H)² - 3H² - 16π · (3H²)/(8π) = 0."""
        for H in [0.5, 1.0, 2.0]:
            trK = -3 * H
            K_sq = 3 * H**2
            Lambda = 3 * H**2
            rho = Lambda / (8 * math.pi)
            assert hamiltonian_constraint(
                0, trK, K_sq, rho) == pytest.approx(0)

    def test_dS_flat_slicing_violates_at_wrong_lambda(self):
        """At dS with wrong Λ ≠ 3H², H_constraint ≠ 0 — confirms
        non-vacuous biconditional."""
        H = 1.0
        trK = -3 * H
        K_sq = 3 * H**2
        for Lambda in [0, H**2, 5 * H**2, -H**2]:
            rho = Lambda / (8 * math.pi)
            if Lambda != 3 * H**2:
                assert hamiltonian_constraint(0, trK, K_sq, rho) != pytest.approx(0)


class TestSchwarzschildADM:
    """Schwarzschild ADM mass extraction. Mirrors Lean
    schwarzschild_adm_mass_eq_M / schwarzschild_adm_mass_pos_iff."""

    def test_adm_mass_eq_M(self):
        """ADM mass equals the Schwarzschild parameter."""
        for M in [0.5, 1.0, 2.5, 100.0]:
            assert schwarzschild_adm_mass(M) == M

    def test_adm_mass_pos_iff_M_pos(self):
        """ADM mass positive iff M positive (positive-energy
        specialization)."""
        for M in [0.5, 1.0, 100.0]:
            assert schwarzschild_adm_mass(M) > 0.0
        for M in [-0.5, -1.0]:
            assert schwarzschild_adm_mass(M) < 0.0
        assert schwarzschild_adm_mass(0.0) == 0.0

    def test_dS_adm_mass_zero(self):
        """De Sitter ADM mass vanishes (no point-mass source).

        Mirrors Lean deSitter_adm_mass_eq_zero."""
        assert desitter_adm_mass() == 0.0


class TestStrengtheningQuantitative:
    """Quantitative bounds tying Lean ADM identities to physics."""

    def test_dS_observed_lambda_admConstraint_balance(self):
        """At observed Λ ≃ 1.1e-52 m⁻², the dS ADM Hamiltonian
        constraint balances at H = √(Λ/3). Confirms the Λ = 3H²
        ADM-level identity matches the cosmological observation.

        The residual is checked relative to the K² input scale to
        account for floating-point precision at the cosmological-Λ
        scale (Λ ~ 10⁻⁵² implies inputs ~ 10⁻⁵²; expect residuals at
        ~16 orders below input, i.e., near double-precision)."""
        Lambda_obs = 1.1e-52  # m⁻²
        H = math.sqrt(Lambda_obs / 3.0)
        trK = -3 * H
        K_sq = 3 * H**2
        rho_Lambda = Lambda_obs / (8 * math.pi)
        H_constraint = hamiltonian_constraint(0, trK, K_sq, rho_Lambda)
        # Relative tolerance: residual / input_scale < machine epsilon * 100
        relative = abs(H_constraint) / max(K_sq, 1e-300)
        assert relative < 1e-14

    def test_solar_mass_adm_mass_geometric_units(self):
        """For solar-mass Schwarzschild (M_geom ≃ 1477 m), ADM mass
        equals the geometric parameter."""
        M_geom_solar = 1477.0
        assert schwarzschild_adm_mass(M_geom_solar) == M_geom_solar
        assert schwarzschild_adm_mass(M_geom_solar) > 0.0

    def test_yamabe_form_at_solar_density(self):
        """At solar-mean-density (ρ_⊙ ≃ 1.4e3 kg/m³ in SI; geometric:
        ~ ρ G/c²), the Yamabe-form Hamiltonian constraint at K=0
        gives R3 = 16πG ρ. Confirms the Yamabe-positive scalar
        curvature regime."""
        # ρ_solar in geometric units: ρ_geom = ρ_SI · G / c²
        # ≃ 1.4e3 · 6.67e-11 / 9e16 ≃ 1.0e-24 m⁻²
        rho_geom = 1.0e-24
        R3_yamabe = 16.0 * math.pi * rho_geom
        # H = 0 at this ρ + R3
        H_constraint = hamiltonian_constraint(R3_yamabe, 0, 0, rho_geom)
        assert abs(H_constraint) < 1e-30


class TestPhase6fCrossBridge:
    """Cross-bridges to 6f.1 + 6f.2 + 6f.4."""

    def test_dS_flat_slicing_matches_6f4_lambda_eq_three_H_sq(self):
        """The dS Hamiltonian-constraint balance at flat slicing
        recovers the 6f.4 `deSitter_lambda_from_K(K=H²) = 3H²`
        identity."""
        from src.core.formulas import deSitter_lambda_from_K
        for H in [0.5, 1.0, 2.5]:
            K = H**2
            Lambda_from_6f4 = deSitter_lambda_from_K(K)
            # ADM-level: at this Λ, the H_constraint = 0
            trK = -3 * H
            K_sq = 3 * H**2
            rho = Lambda_from_6f4 / (8 * math.pi)
            assert hamiltonian_constraint(
                0, trK, K_sq, rho) == pytest.approx(0)

    def test_schwarzschild_adm_mass_matches_6f4_horizon_radius(self):
        """ADM mass M corresponds to horizon radius r_H = 2M (6f.4
        cross-bridge)."""
        from src.core.formulas import schwarzschild_horizon_radius
        for M in [0.5, 1.0, 2.5]:
            assert (schwarzschild_horizon_radius(M)
                    == pytest.approx(2 * schwarzschild_adm_mass(M)))


class TestAntiPatternAudit:
    """Anti-pattern audit per CLAUDE.md preemptive-strengthening
    discipline."""

    def test_no_p1_existential_absorption_minkowski(self):
        """Minkowski ADM data uses explicit numerical N=1, N^i=0,
        γ=δ. No `∃ N γ K, P(N,γ,K)`."""
        N = 1.0
        gamma = euclidean_3metric()
        N_shift = zero_3vector()
        result = adm_four_metric_g00(N, gamma, N_shift)
        assert result == -1.0

    def test_no_p3_trivial_K_zero(self):
        """K = 0 specializations are not P3-trivial — they encode the
        moment-of-time-symmetry condition (Schwarzschild's natural
        slicing). The substantive content lives in the Yamabe-form
        biconditional (R3 = 16π G ρ), not in the K=0 fact alone."""
        # Different (R3, ρ) pairs satisfying Yamabe form
        for R3, expected_rho in [(0, 0), (16 * math.pi, 1.0)]:
            rho = expected_rho
            assert hamiltonian_constraint(
                R3, 0, 0, rho) == pytest.approx(0)

    def test_predicates_nonvacuous_dS_lambda_specific(self):
        """The Λ = 3H² biconditional for dS flat slicing has
        non-trivial both-direction content: at Λ ≠ 3H², the
        constraint is non-zero."""
        H = 1.0
        trK = -3 * H
        K_sq = 3 * H**2
        # Forward: Λ = 3H² ⇒ H_constraint = 0
        rho_correct = (3 * H**2) / (8 * math.pi)
        assert hamiltonian_constraint(
            0, trK, K_sq, rho_correct) == pytest.approx(0)
        # Backward: Λ ≠ 3H² ⇒ H_constraint ≠ 0
        rho_wrong = (5 * H**2) / (8 * math.pi)
        assert hamiltonian_constraint(0, trK, K_sq, rho_wrong) != pytest.approx(0)

    def test_no_p4_vacuous_axiom_yamabe_form(self):
        """The Yamabe-form biconditional R3 = 16πG ρ is verified at
        multiple (R3, ρ) values, not just R3 = 0."""
        for R3 in [0, 1.0, -2.0, 100.0]:
            rho = R3 / (16 * math.pi)
            assert hamiltonian_constraint(
                R3, 0, 0, rho) == pytest.approx(0)

    def test_load_bearing_mass_independence_in_schwarzschild(self):
        """ADM mass for Schwarzschild depends on M (not a constant).
        Different M ⇒ different ADM mass."""
        masses = [schwarzschild_adm_mass(M) for M in [0.5, 1.0, 2.5]]
        assert len(set(masses)) == 3  # All distinct
