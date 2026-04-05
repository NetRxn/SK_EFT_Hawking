"""Tests for SU(2)_k fusion categories (Phase 5c Wave 3).

Tests the truncated Clebsch-Gordan fusion rules, quantum dimensions,
global dimensions, S-matrix, and Verlinde formula for k=1,2,3.

Lean: SU2kFusion.lean
"""

import math

import numpy as np
import pytest

from src.core.formulas import (
    su2k_fusion_rule,
    su2k_global_dim_sq,
    su2k_quantum_dim,
    su2k_s_matrix_entry,
    su2k_verlinde,
)

PHI = (1 + math.sqrt(5)) / 2  # golden ratio


class TestFusionRulesK1:
    """SU(2)_1: Z/2 group fusion (semion). 2 simple objects."""

    def test_unit_fusion(self):
        """V_0 tensor V_j = V_j for all j."""
        for j in range(2):
            for m in range(2):
                expected = 1 if j == m else 0
                assert su2k_fusion_rule(1, 0, j, m) == expected

    def test_v1_squared(self):
        """V_1 tensor V_1 = V_0 (Z/2 fusion)."""
        assert su2k_fusion_rule(1, 1, 1, 0) == 1
        assert su2k_fusion_rule(1, 1, 1, 1) == 0

    def test_all_coefficients(self):
        """Complete 2x2x2 fusion table."""
        # N_{00}^0=1, N_{00}^1=0, N_{01}^0=0, N_{01}^1=1
        # N_{10}^0=0, N_{10}^1=1, N_{11}^0=1, N_{11}^1=0
        expected = {
            (0, 0, 0): 1, (0, 0, 1): 0, (0, 1, 0): 0, (0, 1, 1): 1,
            (1, 0, 0): 0, (1, 0, 1): 1, (1, 1, 0): 1, (1, 1, 1): 0,
        }
        for (i, j, m), val in expected.items():
            assert su2k_fusion_rule(1, i, j, m) == val, f"N_{{{i}{j}}}^{m}"


class TestFusionRulesK2:
    """SU(2)_2: Ising fusion rules. 3 simple objects (1, sigma, psi)."""

    def test_sigma_squared(self):
        """sigma tensor sigma = 1 + psi (the defining Ising relation)."""
        assert su2k_fusion_rule(2, 1, 1, 0) == 1  # contains V_0
        assert su2k_fusion_rule(2, 1, 1, 1) == 0  # no V_1
        assert su2k_fusion_rule(2, 1, 1, 2) == 1  # contains V_2

    def test_psi_squared(self):
        """psi tensor psi = 1."""
        assert su2k_fusion_rule(2, 2, 2, 0) == 1
        assert su2k_fusion_rule(2, 2, 2, 1) == 0
        assert su2k_fusion_rule(2, 2, 2, 2) == 0

    def test_sigma_psi(self):
        """sigma tensor psi = sigma."""
        assert su2k_fusion_rule(2, 1, 2, 0) == 0
        assert su2k_fusion_rule(2, 1, 2, 1) == 1
        assert su2k_fusion_rule(2, 1, 2, 2) == 0

    def test_commutativity(self):
        """N_{ij}^m = N_{ji}^m for all i,j,m."""
        for i in range(3):
            for j in range(3):
                for m in range(3):
                    assert su2k_fusion_rule(2, i, j, m) == su2k_fusion_rule(2, j, i, m)

    def test_associativity(self):
        """sum_m N_{ij}^m * N_{mk}^n = sum_m N_{jk}^m * N_{im}^n."""
        for i in range(3):
            for j in range(3):
                for k_idx in range(3):
                    for n in range(3):
                        lhs = sum(
                            su2k_fusion_rule(2, i, j, m) * su2k_fusion_rule(2, m, k_idx, n)
                            for m in range(3)
                        )
                        rhs = sum(
                            su2k_fusion_rule(2, j, k_idx, m) * su2k_fusion_rule(2, i, m, n)
                            for m in range(3)
                        )
                        assert lhs == rhs, f"Assoc fail: i={i},j={j},k={k_idx},n={n}"


class TestFusionRulesK3:
    """SU(2)_3: 4 simple objects (contains Fibonacci subcategory)."""

    def test_fibonacci_relation(self):
        """V_2 tensor V_2 = V_0 + V_2 (tau tensor tau = 1 + tau)."""
        assert su2k_fusion_rule(3, 2, 2, 0) == 1
        assert su2k_fusion_rule(3, 2, 2, 1) == 0
        assert su2k_fusion_rule(3, 2, 2, 2) == 1
        assert su2k_fusion_rule(3, 2, 2, 3) == 0

    def test_v1_squared(self):
        """V_1 tensor V_1 = V_0 + V_2."""
        assert su2k_fusion_rule(3, 1, 1, 0) == 1
        assert su2k_fusion_rule(3, 1, 1, 1) == 0
        assert su2k_fusion_rule(3, 1, 1, 2) == 1
        assert su2k_fusion_rule(3, 1, 1, 3) == 0

    def test_charge_conjugation(self):
        """V_3 tensor V_j = V_{3-j} (charge conjugation)."""
        assert su2k_fusion_rule(3, 3, 0, 3) == 1
        assert su2k_fusion_rule(3, 3, 1, 2) == 1
        assert su2k_fusion_rule(3, 3, 2, 1) == 1
        assert su2k_fusion_rule(3, 3, 3, 0) == 1

    def test_associativity(self):
        """Full associativity check for k=3."""
        for i in range(4):
            for j in range(4):
                for k_idx in range(4):
                    for n in range(4):
                        lhs = sum(
                            su2k_fusion_rule(3, i, j, m) * su2k_fusion_rule(3, m, k_idx, n)
                            for m in range(4)
                        )
                        rhs = sum(
                            su2k_fusion_rule(3, j, k_idx, m) * su2k_fusion_rule(3, i, m, n)
                            for m in range(4)
                        )
                        assert lhs == rhs


class TestQuantumDimensions:
    """Tests for quantum dimensions d_j."""

    def test_k1_dims(self):
        """k=1: d_0=1, d_1=1."""
        assert su2k_quantum_dim(1, 0) == pytest.approx(1.0, abs=1e-12)
        assert su2k_quantum_dim(1, 1) == pytest.approx(1.0, abs=1e-12)

    def test_k2_dims(self):
        """k=2: d_0=1, d_1=sqrt(2), d_2=1."""
        assert su2k_quantum_dim(2, 0) == pytest.approx(1.0, abs=1e-12)
        assert su2k_quantum_dim(2, 1) == pytest.approx(math.sqrt(2), abs=1e-12)
        assert su2k_quantum_dim(2, 2) == pytest.approx(1.0, abs=1e-12)

    def test_k3_dims(self):
        """k=3: d_0=1, d_1=phi, d_2=phi, d_3=1."""
        assert su2k_quantum_dim(3, 0) == pytest.approx(1.0, abs=1e-12)
        assert su2k_quantum_dim(3, 1) == pytest.approx(PHI, abs=1e-12)
        assert su2k_quantum_dim(3, 2) == pytest.approx(PHI, abs=1e-12)
        assert su2k_quantum_dim(3, 3) == pytest.approx(1.0, abs=1e-12)

    def test_dimension_consistency(self):
        """d_i * d_j = sum_m N_{ij}^m * d_m (fusion ring homomorphism)."""
        for k in [1, 2, 3]:
            for i in range(k + 1):
                for j in range(k + 1):
                    lhs = su2k_quantum_dim(k, i) * su2k_quantum_dim(k, j)
                    rhs = sum(
                        su2k_fusion_rule(k, i, j, m) * su2k_quantum_dim(k, m)
                        for m in range(k + 1)
                    )
                    assert lhs == pytest.approx(rhs, abs=1e-10), \
                        f"k={k}, i={i}, j={j}: {lhs} != {rhs}"


class TestGlobalDimension:
    """Tests for global dimension D^2 = sum d_j^2."""

    def test_k1(self):
        """D^2 = 2 for k=1."""
        assert su2k_global_dim_sq(1) == pytest.approx(2.0, abs=1e-12)

    def test_k2(self):
        """D^2 = 4 for k=2."""
        assert su2k_global_dim_sq(2) == pytest.approx(4.0, abs=1e-12)

    def test_k3(self):
        """D^2 = 5 + sqrt(5) for k=3."""
        assert su2k_global_dim_sq(3) == pytest.approx(5 + math.sqrt(5), abs=1e-10)

    def test_matches_sum(self):
        """D^2 = sum_{j=0}^{k} d_j^2 for k=1,2,3."""
        for k in [1, 2, 3]:
            from_formula = su2k_global_dim_sq(k)
            from_sum = sum(su2k_quantum_dim(k, j) ** 2 for j in range(k + 1))
            assert from_formula == pytest.approx(from_sum, abs=1e-10)


class TestSMatrix:
    """Tests for the S-matrix."""

    def test_unitarity_k1(self):
        """S*S^T = I for k=1 (2x2)."""
        S = np.array([[su2k_s_matrix_entry(1, i, j) for j in range(2)] for i in range(2)])
        np.testing.assert_allclose(S @ S.T, np.eye(2), atol=1e-12)

    def test_unitarity_k2(self):
        """S*S^T = I for k=2 (3x3)."""
        S = np.array([[su2k_s_matrix_entry(2, i, j) for j in range(3)] for i in range(3)])
        np.testing.assert_allclose(S @ S.T, np.eye(3), atol=1e-12)

    def test_unitarity_k3(self):
        """S*S^T = I for k=3 (4x4)."""
        S = np.array([[su2k_s_matrix_entry(3, i, j) for j in range(4)] for i in range(4)])
        np.testing.assert_allclose(S @ S.T, np.eye(4), atol=1e-12)

    def test_symmetry(self):
        """S_{ij} = S_{ji} for all k."""
        for k in [1, 2, 3]:
            for i in range(k + 1):
                for j in range(k + 1):
                    assert su2k_s_matrix_entry(k, i, j) == pytest.approx(
                        su2k_s_matrix_entry(k, j, i), abs=1e-14
                    )

    def test_nondegeneracy(self):
        """det(S) != 0 for k=1,2,3 (modularity condition)."""
        for k in [1, 2, 3]:
            S = np.array([
                [su2k_s_matrix_entry(k, i, j) for j in range(k + 1)]
                for i in range(k + 1)
            ])
            assert abs(np.linalg.det(S)) > 0.5  # |det| = 1 for unitary S


class TestVerlinde:
    """Tests for the Verlinde formula: N_{ij}^m from S-matrix."""

    def test_verlinde_matches_fusion_k1(self):
        """Verlinde formula reproduces fusion rules for k=1."""
        for i in range(2):
            for j in range(2):
                for m in range(2):
                    v = su2k_verlinde(1, i, j, m)
                    f = su2k_fusion_rule(1, i, j, m)
                    assert round(v) == f, f"k=1: N_{{{i}{j}}}^{m}: Verlinde={v}, fusion={f}"

    def test_verlinde_matches_fusion_k2(self):
        """Verlinde formula reproduces fusion rules for k=2."""
        for i in range(3):
            for j in range(3):
                for m in range(3):
                    v = su2k_verlinde(2, i, j, m)
                    f = su2k_fusion_rule(2, i, j, m)
                    assert round(v) == f, f"k=2: N_{{{i}{j}}}^{m}: Verlinde={v}, fusion={f}"

    def test_verlinde_matches_fusion_k3(self):
        """Verlinde formula reproduces fusion rules for k=3."""
        for i in range(4):
            for j in range(4):
                for m in range(4):
                    v = su2k_verlinde(3, i, j, m)
                    f = su2k_fusion_rule(3, i, j, m)
                    assert round(v) == f, f"k=3: N_{{{i}{j}}}^{m}: Verlinde={v}, fusion={f}"

    def test_verlinde_nonneg_integer(self):
        """All Verlinde coefficients are non-negative integers."""
        for k in [1, 2, 3]:
            for i in range(k + 1):
                for j in range(k + 1):
                    for m in range(k + 1):
                        v = su2k_verlinde(k, i, j, m)
                        assert v >= -0.01, f"Negative: k={k}, ({i},{j},{m}): {v}"
                        assert abs(v - round(v)) < 0.01, f"Non-integer: k={k}, ({i},{j},{m}): {v}"
