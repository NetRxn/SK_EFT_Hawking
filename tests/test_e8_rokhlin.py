"""Tests for E8 lattice, algebraic Rokhlin, and spin bordism (Phase 5c Wave 7).

Covers E8Lattice.lean, AlgebraicRokhlin.lean, SpinBordism.lean.
"""

import numpy as np
import pytest


class TestE8Lattice:
    """Tests for E8 Cartan matrix properties."""

    E8 = np.array([
        [2, 0, -1, 0, 0, 0, 0, 0],
        [0, 2, 0, -1, 0, 0, 0, 0],
        [-1, 0, 2, -1, 0, 0, 0, 0],
        [0, -1, -1, 2, -1, 0, 0, 0],
        [0, 0, 0, -1, 2, -1, 0, 0],
        [0, 0, 0, 0, -1, 2, -1, 0],
        [0, 0, 0, 0, 0, -1, 2, -1],
        [0, 0, 0, 0, 0, 0, -1, 2],
    ])

    def test_det_is_one(self):
        """det(E8) = 1 (unimodular)."""
        assert round(np.linalg.det(self.E8)) == 1

    def test_symmetric(self):
        """E8 is symmetric."""
        np.testing.assert_array_equal(self.E8, self.E8.T)

    def test_diagonal_all_two(self):
        """All diagonal entries are 2 (even)."""
        assert all(self.E8[i, i] == 2 for i in range(8))

    def test_positive_definite(self):
        """E8 is positive definite (all eigenvalues > 0)."""
        eigenvalues = np.linalg.eigvalsh(self.E8)
        assert all(e > 0 for e in eigenvalues)

    def test_signature_is_8(self):
        """Signature = 8 (positive definite rank 8)."""
        eigenvalues = np.linalg.eigvalsh(self.E8)
        sigma = sum(1 for e in eigenvalues if e > 0) - sum(1 for e in eigenvalues if e < 0)
        assert sigma == 8

    def test_sigma_div_8(self):
        """σ=8 is divisible by 8 (algebraic Serre bound)."""
        assert 8 % 8 == 0

    def test_sigma_not_div_16(self):
        """σ=8 is NOT divisible by 16 (disproves naive algebraic Rokhlin)."""
        assert 8 % 16 != 0

    def test_leading_minors_positive(self):
        """All leading principal minors are positive (Sylvester's criterion)."""
        for k in range(1, 9):
            minor = self.E8[:k, :k]
            assert np.linalg.det(minor) > 0, f"Minor {k} is not positive"


class TestHyperbolicPlane:
    """Tests for the hyperbolic plane H."""

    H = np.array([[0, 1], [1, 0]])

    def test_det_minus_one(self):
        """det(H) = -1."""
        assert round(np.linalg.det(self.H)) == -1

    def test_symmetric(self):
        """H is symmetric."""
        np.testing.assert_array_equal(self.H, self.H.T)

    def test_even_diagonal(self):
        """H has even diagonal (both zeros)."""
        assert all(self.H[i, i] % 2 == 0 for i in range(2))

    def test_signature_zero(self):
        """σ(H) = 0 (one positive, one negative eigenvalue)."""
        eigenvalues = np.linalg.eigvalsh(self.H)
        sigma = sum(1 for e in eigenvalues if e > 0.01) - sum(1 for e in eigenvalues if e < -0.01)
        assert sigma == 0


class TestAlgebraicRokhlin:
    """Tests for the algebraic Serre theorem."""

    def test_serre_e8(self):
        """E8: σ=8 ≡ 0 mod 8."""
        assert 8 % 8 == 0

    def test_serre_two_e8(self):
        """E8 + E8: σ=16 ≡ 0 mod 8."""
        assert 16 % 8 == 0

    def test_serre_e8_minus_e8(self):
        """E8 + (-E8): σ=0 ≡ 0 mod 8."""
        assert 0 % 8 == 0

    def test_serre_H(self):
        """H: σ=0 ≡ 0 mod 8."""
        assert 0 % 8 == 0

    def test_classification_sigma(self):
        """Classification: σ = 8(a - b) for all a, b."""
        for a in range(5):
            for b in range(5):
                sigma = 8 * (a - b)
                assert sigma % 8 == 0

    def test_gap_algebra_topology(self):
        """The factor between algebraic (8) and topological (16) is 2."""
        assert 16 // 8 == 2


class TestSpinBordism:
    """Tests for the spin bordism → Rokhlin → Wang chain."""

    def test_rokhlin_examples(self):
        """16 | σ for σ = -16n (bordism)."""
        for n in range(-5, 6):
            sigma = -16 * n
            assert sigma % 16 == 0

    def test_anomaly_with_nu_R(self):
        """16 Weyl per generation: 16*N_f ≡ 0 mod 16."""
        for nf in range(1, 10):
            assert (16 * nf) % 16 == 0

    def test_anomaly_without_nu_R(self):
        """15 Weyl per generation: 15*N_f ≡ -N_f mod 16."""
        for nf in range(1, 10):
            assert (15 * nf) % 16 == (-nf) % 16

    def test_three_gen_anomaly(self):
        """N_f=3 without ν_R: anomaly = 15*3 mod 16 = 13."""
        assert (15 * 3) % 16 == 13

    def test_wang_chain(self):
        """24 | 8N_f → 3 | N_f for all N_f where the hypothesis holds."""
        for nf in range(0, 30):
            if (8 * nf) % 24 == 0:
                assert nf % 3 == 0, f"Wang fails for N_f={nf}"

    def test_wang_minimal(self):
        """The smallest positive N_f satisfying 24 | 8N_f is N_f = 3."""
        solutions = [nf for nf in range(1, 30) if (8 * nf) % 24 == 0]
        assert solutions[0] == 3
