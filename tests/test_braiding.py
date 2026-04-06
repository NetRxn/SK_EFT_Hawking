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
