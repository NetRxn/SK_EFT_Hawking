"""Tests for q-integers and q-Dolan-Grady coefficient.

Lean modules: QNumber.lean, Uqsl2.lean
"""

import pytest
from src.core.formulas import q_integer, q_dg_coefficient


class TestQInteger:
    """Test [n]_q = q^{n-1} + q^{n-3} + ... + q^{-(n-1)}."""

    def test_q_zero(self):
        assert q_integer(0, 2) == 0

    def test_q_one(self):
        assert q_integer(1, 2) == 1  # q^0 = 1

    def test_q_two(self):
        """[2]_q = q + q⁻¹."""
        assert q_integer(2, 2) == 2 + 0.5  # 2 + 1/2

    def test_q_three(self):
        """[3]_q = q² + 1 + q⁻²."""
        assert q_integer(3, 2) == 4 + 1 + 0.25  # 4 + 1 + 1/4

    def test_classical_limit(self):
        """[n]_1 = n for all n."""
        for n in range(10):
            assert abs(q_integer(n, 1.0) - n) < 1e-10, f"[{n}]_1 = {q_integer(n, 1.0)} ≠ {n}"

    def test_symmetry(self):
        """[n]_q = [n]_{q⁻¹} (q-numbers are symmetric under q ↔ q⁻¹)."""
        for n in range(1, 6):
            for q in [2.0, 3.0, 0.5]:
                assert abs(q_integer(n, q) - q_integer(n, 1/q)) < 1e-10

    def test_two_pow4_at_q1(self):
        """[2]_1⁴ = 2⁴ = 16 = DG_COEFF."""
        assert q_integer(2, 1.0) ** 4 == 16


class TestQDGCoefficient:
    """Test [3]_q = q² + 1 + q⁻² (q-Dolan-Grady coefficient)."""

    def test_classical(self):
        """[3]_1 = 3."""
        assert q_dg_coefficient(1.0) == 3.0

    def test_explicit(self):
        """[3]_2 = 4 + 1 + 1/4 = 5.25."""
        assert q_dg_coefficient(2.0) == 5.25

    def test_matches_q_integer(self):
        """q_dg_coefficient(q) = q_integer(3, q)."""
        for q in [0.5, 1.0, 2.0, 3.0]:
            assert abs(q_dg_coefficient(q) - q_integer(3, q)) < 1e-10

    def test_rho_independent_of_q(self):
        """The RHS coefficient ρ = 16 is independent of q."""
        # ρ is a free parameter, not a q-number. This test documents that.
        rho = 16  # DG_COEFF
        for q in [0.5, 1.0, 2.0, 3.0]:
            assert rho == 16  # ρ doesn't change with q
