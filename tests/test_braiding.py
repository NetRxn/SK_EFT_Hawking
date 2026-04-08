"""
Tests for Ising and Fibonacci braiding data (Phase 5e).

Corresponds to IsingBraiding.lean, QCyc16.lean, QCyc5.lean, QSqrt3.lean, QLevel3.lean.
"""

import numpy as np
import pytest
from src.core.formulas import (
    ising_r_matrix, ising_twist, ising_f_symbol,
    fibonacci_r_matrix, fibonacci_twist,
    trefoil_jones_ising,
    su2k_s_matrix_entry, su2k_fusion_rule,
    mtc_s_matrix, mtc_quantum_dimensions, mtc_total_quantum_dimension,
    interferometric_visibility, thermal_hall_conductance,
    topological_entanglement_entropy, quasiparticle_charge,
    ground_state_degeneracy, distinguishing_observables_table,
)


class TestIsingRMatrix:
    def test_R_ss_1(self):
        """R^{σσ}_1 = e^{-iπ/8}."""
        R = ising_r_matrix(1, 1, 0)
        assert abs(R - np.exp(-1j * np.pi / 8)) < 1e-14

    def test_R_ss_psi(self):
        """R^{σσ}_ψ = e^{3iπ/8}."""
        R = ising_r_matrix(1, 1, 2)
        assert abs(R - np.exp(3j * np.pi / 8)) < 1e-14

    def test_R_sigma_psi(self):
        """R^{σψ}_σ = -i."""
        assert abs(ising_r_matrix(1, 2, 1) - (-1j)) < 1e-14

    def test_R_psi_psi(self):
        """R^{ψψ}_1 = -1."""
        assert abs(ising_r_matrix(2, 2, 0) - (-1)) < 1e-14

    def test_R_unitarity(self):
        """|R| = 1 for all non-trivial entries."""
        for (a, b, c) in [(1,1,0), (1,1,2), (1,2,1), (2,1,1), (2,2,0)]:
            assert abs(abs(ising_r_matrix(a, b, c)) - 1.0) < 1e-14


class TestIsingTwist:
    def test_theta_1(self):
        assert ising_twist(0) == 1.0

    def test_theta_sigma(self):
        assert abs(ising_twist(1) - np.exp(1j * np.pi / 8)) < 1e-14

    def test_theta_psi(self):
        assert ising_twist(2) == -1.0


class TestIsingHexagon:
    def test_hexagon_I(self):
        """(1/√2)(1 + R^{σψ}_σ) = (R^{σσ}_1)²."""
        lhs = (1 + ising_r_matrix(1, 2, 1)) / np.sqrt(2)
        rhs = ising_r_matrix(1, 1, 0) ** 2
        assert abs(lhs - rhs) < 1e-13

    def test_hexagon_II(self):
        """(1/√2)(1 - R^{σψ}_σ) = R^{σσ}_1 · R^{σσ}_ψ."""
        lhs = (1 - ising_r_matrix(1, 2, 1)) / np.sqrt(2)
        rhs = ising_r_matrix(1, 1, 0) * ising_r_matrix(1, 1, 2)
        assert abs(lhs - rhs) < 1e-13

    def test_hexagon_III(self):
        """(1/√2)(1 + R^{σψ}_σ) = -(R^{σσ}_ψ)²."""
        lhs = (1 + ising_r_matrix(1, 2, 1)) / np.sqrt(2)
        rhs = -(ising_r_matrix(1, 1, 2) ** 2)
        assert abs(lhs - rhs) < 1e-13


class TestIsingRibbon:
    def test_ribbon_ss_1(self):
        """(R^{σσ}_1)² = 1/(θ_σ)²."""
        lhs = ising_r_matrix(1, 1, 0) ** 2
        rhs = 1.0 / ising_twist(1) ** 2
        assert abs(lhs - rhs) < 1e-13

    def test_ribbon_ss_psi(self):
        """(R^{σσ}_ψ)² = θ_ψ/(θ_σ)²."""
        lhs = ising_r_matrix(1, 1, 2) ** 2
        rhs = ising_twist(2) / ising_twist(1) ** 2
        assert abs(lhs - rhs) < 1e-13

    def test_ribbon_pp_1(self):
        """(R^{ψψ}_1)² = 1."""
        assert abs(ising_r_matrix(2, 2, 0) ** 2 - 1.0) < 1e-14


class TestTrefoil:
    def test_trefoil_equals_neg_one(self):
        """Jones polynomial of trefoil at q=i equals -1."""
        result = trefoil_jones_ising()
        assert abs(result - (-1.0)) < 1e-12

    def test_trefoil_is_real(self):
        """Trefoil invariant should be real."""
        result = trefoil_jones_ising()
        assert abs(result.imag) < 1e-12


class TestFibonacciRMatrix:
    def test_R1_eq_Rtau_sq(self):
        """R₁ = Rτ² (critical identity)."""
        R1 = fibonacci_r_matrix(0)
        Rtau = fibonacci_r_matrix(1)
        assert abs(R1 - Rtau ** 2) < 1e-13

    def test_hexagon_E1(self):
        """R₁² = φ⁻¹ + Rτ."""
        phi_inv = (np.sqrt(5) - 1) / 2
        R1 = fibonacci_r_matrix(0)
        Rtau = fibonacci_r_matrix(1)
        assert abs(R1 ** 2 - (phi_inv + Rtau)) < 1e-13

    def test_hexagon_E3(self):
        """Rτ² + φ⁻¹·Rτ + 1 = 0."""
        phi_inv = (np.sqrt(5) - 1) / 2
        Rtau = fibonacci_r_matrix(1)
        assert abs(Rtau ** 2 + phi_inv * Rtau + 1) < 1e-13

    def test_twist_consistency(self):
        """θτ · R₁ = 1 (from Rτ⁻² = θτ and R₁ = Rτ²)."""
        theta = fibonacci_twist()
        R1 = fibonacci_r_matrix(0)
        assert abs(theta * R1 - 1.0) < 1e-13


class TestSU2kSMatrix:
    def test_k3_unitarity_diagonal(self):
        """SU(2)₃ S-matrix row norms = 1."""
        k = 3
        for i in range(k + 1):
            norm = sum(su2k_s_matrix_entry(k, i, j) ** 2 for j in range(k + 1))
            assert abs(norm - 1.0) < 1e-12, f"Row {i} norm = {norm}"

    def test_k3_unitarity_offdiag(self):
        """SU(2)₃ S-matrix row orthogonality."""
        k = 3
        for i in range(k + 1):
            for j in range(i + 1, k + 1):
                dot = sum(su2k_s_matrix_entry(k, i, l) * su2k_s_matrix_entry(k, j, l)
                          for l in range(k + 1))
                assert abs(dot) < 1e-12, f"Rows {i},{j} dot = {dot}"

    def test_k4_unitarity_diagonal(self):
        """SU(2)₄ S-matrix row norms = 1."""
        k = 4
        for i in range(k + 1):
            norm = sum(su2k_s_matrix_entry(k, i, j) ** 2 for j in range(k + 1))
            assert abs(norm - 1.0) < 1e-12, f"Row {i} norm = {norm}"


# ════════════════════════════════════════════════════════════════════
# Phase 5o W3: Experimental predictions from verified MTC data
# ════════════════════════════════════════════════════════════════════

class TestMTCSMatrix:
    def test_ising_s_matrix_unitary(self):
        S = mtc_s_matrix('ising')
        assert np.allclose(S @ S.T, np.eye(3))

    def test_fibonacci_s_matrix_unitary(self):
        S = mtc_s_matrix('fibonacci')
        assert np.allclose(S @ S.T, np.eye(2))

    def test_ising_s_matrix_symmetric(self):
        S = mtc_s_matrix('ising')
        assert np.allclose(S, S.T)

    def test_ising_s_sigma_sigma_zero(self):
        """S_{σσ} = 0 — root of even-odd effect."""
        S = mtc_s_matrix('ising')
        assert abs(S[1, 1]) < 1e-14


class TestQuantumDimensions:
    def test_ising_D_squared(self):
        D = mtc_total_quantum_dimension('ising')
        assert abs(D**2 - 4.0) < 1e-12

    def test_fibonacci_D_squared(self):
        phi = (1 + np.sqrt(5)) / 2
        D = mtc_total_quantum_dimension('fibonacci')
        assert abs(D**2 - (2 + phi)) < 1e-12


class TestInterferometricVisibility:
    def test_ising_even_odd_effect(self):
        """M_{σ,σ} = 0: complete suppression for odd parity."""
        assert abs(interferometric_visibility('ising', 1, 1)) < 1e-14

    def test_ising_vacuum_full(self):
        """M_{σ,1} = +1: full visibility for vacuum target."""
        assert abs(interferometric_visibility('ising', 1, 0) - 1.0) < 1e-12

    def test_ising_fermion_pi_shifted(self):
        """M_{σ,ψ} = -1: full visibility, π-shifted."""
        assert abs(interferometric_visibility('ising', 1, 2) - (-1.0)) < 1e-12

    def test_fibonacci_nonzero(self):
        """M_{τ,τ} = -1/φ² ≈ -0.382: reduced but nonzero."""
        phi = (1 + np.sqrt(5)) / 2
        M = interferometric_visibility('fibonacci', 1, 1)
        assert abs(M - (-1/phi**2)) < 1e-12

    def test_fibonacci_visibility_magnitude(self):
        """|M_{τ,τ}| ≈ 0.382."""
        assert abs(abs(interferometric_visibility('fibonacci', 1, 1)) - 0.381966) < 1e-5


class TestThermalHall:
    def test_ising_central_charge(self):
        """c_top = 1/2 for Ising."""
        result = thermal_hall_conductance('ising')
        assert abs(result['c_top'] - 0.5) < 1e-10

    def test_fibonacci_central_charge(self):
        """c_top = 14/5 for Fibonacci."""
        result = thermal_hall_conductance('fibonacci')
        assert abs(result['c_top'] - 2.8) < 1e-10

    def test_kappa_0_positive(self):
        result = thermal_hall_conductance('ising')
        assert result['kappa_0'] > 0

    def test_nu52_prediction(self):
        """ν=5/2 prediction: 2 + 0.5 = 2.5κ₀ (Banerjee 2018)."""
        result = thermal_hall_conductance('ising')
        total_with_landau = 2 + result['c_top']
        assert abs(total_with_landau - 2.5) < 1e-10


class TestTEE:
    def test_ising_tee(self):
        assert abs(topological_entanglement_entropy('ising') - np.log(2)) < 1e-12

    def test_fibonacci_tee(self):
        phi = (1 + np.sqrt(5)) / 2
        expected = np.log(np.sqrt(2 + phi))
        assert abs(topological_entanglement_entropy('fibonacci') - expected) < 1e-12

    def test_ising_greater_than_fibonacci(self):
        """Ising TEE > Fibonacci TEE (D_ising=2 > D_fib≈1.9)."""
        assert topological_entanglement_entropy('ising') > topological_entanglement_entropy('fibonacci')


class TestQuasiparticleCharge:
    def test_ising_charge(self):
        assert quasiparticle_charge('ising')['charge_fraction'] == 0.25

    def test_fibonacci_charge(self):
        assert quasiparticle_charge('fibonacci')['charge_fraction'] == 0.2


class TestGSD:
    def test_ising_gsd(self):
        assert ground_state_degeneracy('ising') == 3

    def test_fibonacci_gsd(self):
        assert ground_state_degeneracy('fibonacci') == 2


class TestDistinguishingTable:
    def test_table_has_5_observables(self):
        table = distinguishing_observables_table()
        assert len(table) == 5

    def test_table_ranked(self):
        table = distinguishing_observables_table()
        ranks = [row['rank'] for row in table]
        assert ranks == [1, 2, 3, 4, 5]
