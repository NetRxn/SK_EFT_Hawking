"""
Tests for FK Gapped Interface and Modularity Theorem (Phase 5s).

Cross-validates the Lean formalization against independent Python computation.
"""

import pytest
import numpy as np


class TestFKHamiltonian:
    """Tests for the Fidkowski-Kitaev 16×16 Hamiltonian."""

    @pytest.fixture
    def H(self):
        """Build the FK Hamiltonian from the two components."""
        # W1: diagonal, eigenvalue -2(2-N)^2 + 2 where N = popcount(k)
        diag = np.zeros(16, dtype=int)
        for k in range(16):
            N = bin(k).count('1')
            diag[k] = -2 * (2 - N) ** 2 + 2
        W1 = np.diag(diag)

        # W2: anti-diagonal with sign (-1)^{b1+b3}
        W2 = np.zeros((16, 16), dtype=int)
        for k in range(16):
            b1 = (k >> 3) & 1  # bit 3 (MSB in 4-bit)
            b3 = (k >> 1) & 1  # bit 1
            sign = (-1) ** (b1 + b3)
            W2[k, 15 - k] = sign

        return W1 + W2

    def test_symmetric(self, H):
        assert np.array_equal(H, H.T)

    def test_trace_zero(self, H):
        assert np.trace(H) == 0

    def test_frobenius_norm(self, H):
        assert np.trace(H @ H) == 112

    def test_eigenvalues(self, H):
        evals = sorted(np.linalg.eigvalsh(H))
        expected = sorted([-7, -5] + [-1]*4 + [1]*7 + [3]*3)
        np.testing.assert_array_almost_equal(evals, expected)

    def test_ground_state_unique(self, H):
        evals = np.linalg.eigvalsh(H)
        assert np.sum(np.abs(evals - (-7)) < 0.01) == 1

    def test_spectral_gap(self, H):
        evals = sorted(np.linalg.eigvalsh(H))
        assert evals[0] == pytest.approx(-7)
        assert evals[1] == pytest.approx(-5)
        assert evals[1] - evals[0] == pytest.approx(2)

    def test_ground_state_eigenvector(self, H):
        v = np.zeros(16, dtype=int)
        v[0] = 1
        v[15] = -1
        result = H @ v
        expected = -7 * v
        np.testing.assert_array_equal(result, expected)

    def test_parity_commutation(self, H):
        parity = np.diag([(-1)**bin(k).count('1') for k in range(16)])
        commutator = H @ parity - parity @ H
        assert np.all(commutator == 0)

    def test_characteristic_polynomial(self, H):
        """Verify char poly = (x+7)(x+5)(x+1)^4(x-1)^7(x-3)^3."""
        coeffs = np.poly(H)
        # Check by evaluating at eigenvalues
        for lam in [-7, -5, -1, 1, 3]:
            val = np.polyval(coeffs, lam)
            assert abs(val) < 1e-6, f"char poly({lam}) = {val} ≠ 0"

    def test_multiplicities(self):
        """Verify eigenvalue multiplicities sum to 16."""
        assert 1 + 1 + 4 + 7 + 3 == 16

    def test_multiplicity_trace(self):
        """Cross-validate: sum(lambda_i * m_i) = 0."""
        assert (-7)*1 + (-5)*1 + (-1)*4 + 1*7 + 3*3 == 0

    def test_multiplicity_frobenius(self):
        """Cross-validate: sum(lambda_i^2 * m_i) = 112."""
        assert (-7)**2*1 + (-5)**2*1 + (-1)**2*4 + 1**2*7 + 3**2*3 == 112


class TestModularityTheorem:
    """Tests for the general det(S)≠0 → Z₂ trivial theorem."""

    def test_proportional_rows_singular(self):
        """Any matrix with proportional rows has det = 0."""
        for n in [3, 4, 5]:
            A = np.random.randint(0, 10, (n, n)).astype(float)
            c = 2.5
            A[1] = c * A[0]  # Make row 1 proportional to row 0
            assert abs(np.linalg.det(A)) < 1e-10

    def test_invertible_no_proportional(self):
        """An invertible matrix has no proportional rows."""
        A = np.eye(5)
        assert abs(np.linalg.det(A)) > 0.5
        for i in range(5):
            for j in range(5):
                if i != j:
                    # Check rows i and j are NOT proportional
                    # (they're standard basis vectors, clearly independent)
                    cross = np.abs(A[i] * A[j]).sum()
                    if cross > 0:  # nonzero overlap
                        ratio = A[i] / np.where(A[j] != 0, A[j], 1)
                        assert not np.allclose(ratio * (A[j] != 0), ratio[0] * (A[j] != 0))

    def test_ising_s_matrix(self):
        """Ising S-matrix has det ≠ 0 → Muger trivial (general theorem)."""
        s2 = np.sqrt(2)
        S = np.array([
            [1, s2, 1],
            [s2, 0, -s2],
            [1, -s2, 1]
        ]) / 2
        assert abs(np.linalg.det(S)) > 0.1
        # No row proportional to row 0
        for i in [1, 2]:
            if np.allclose(S[0], 0):
                continue
            ratios = S[i] / np.where(np.abs(S[0]) > 1e-10, S[0], 1)
            valid = np.abs(S[0]) > 1e-10
            if valid.sum() >= 2:
                assert not np.allclose(ratios[valid], ratios[valid][0])

    def test_fibonacci_s_matrix(self):
        """Fibonacci S-matrix has det ≠ 0."""
        phi = (1 + np.sqrt(5)) / 2
        D2 = 2 + phi
        S = np.array([
            [1, phi],
            [phi, -1]
        ]) / np.sqrt(D2)
        assert abs(np.linalg.det(S)) > 0.1
