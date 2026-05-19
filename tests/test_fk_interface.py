"""Tests for FK Gapped Interface (Cayley calibration) and Modularity Theorem.

Phase 5s Wave 4 cross-layer parity check. Verifies the Python pipeline
matches the Lean formalisation `SKEFTHawking.FK` (FKGappedInterface.lean
— 12 theorems / 0 sorry / native_decide on 16×16 ℤ matrices).

Cross-validation strategy:
  1. Build W constructively from the 8 Majorana operators + the 14 signed
     Cayley quartets. Confirm the result is real-integer and symmetric.
  2. Compare entry-wise to the sparse `FK.W` Lean encoding (10 nonzero
     entries on the even-parity diagonal + corner off-diagonals).
  3. Verify minimal polynomial, traces, eigenvalue spectrum, ground-state
     vector, fermion-parity commutation, and Spin(7) multiplicity system.
"""

import numpy as np
import pytest

from src.core.formulas import (
    fk_cayley_quartets,
    fk_dimensional_ladder_evidence,
    fk_eigenvalues,
    fk_ground_state_vector,
    fk_hamiltonian,
    fk_hamiltonian_sparse,
    fk_majorana_operators,
    fk_minimal_polynomial_residual,
    fk_parity_matrix,
    fk_spectral_gap,
)


class TestMajoranaOperators:
    """Jordan-Wigner γ₁..γ₈ as 16×16 complex matrices."""

    @pytest.fixture(scope='class')
    def gammas(self):
        return fk_majorana_operators()

    def test_count(self, gammas):
        assert len(gammas) == 8

    def test_dimensions(self, gammas):
        for g in gammas:
            assert g.shape == (16, 16)

    def test_hermitian(self, gammas):
        for i, g in enumerate(gammas, start=1):
            assert np.allclose(g, g.conj().T), f"γ{i} not Hermitian"

    def test_clifford_anticommutation(self, gammas):
        """{γₐ, γ_b} = 2 δ_{ab} · I."""
        I16 = np.eye(16, dtype=complex)
        for a in range(8):
            for b in range(8):
                anticomm = gammas[a] @ gammas[b] + gammas[b] @ gammas[a]
                expected = 2 * I16 if a == b else np.zeros_like(I16)
                assert np.allclose(anticomm, expected), \
                    f"{{γ{a+1}, γ{b+1}}} ≠ 2 δ_ab I"

    def test_squared_identity(self, gammas):
        """γₐ² = I for each a."""
        I16 = np.eye(16, dtype=complex)
        for i, g in enumerate(gammas, start=1):
            assert np.allclose(g @ g, I16), f"γ{i}² ≠ I"


class TestCayleyQuartets:
    """The 14 signed quartets defining the Cayley 4-form on R⁸."""

    def test_count(self):
        assert len(fk_cayley_quartets()) == 14

    def test_strictly_increasing(self):
        for a, b, c, d, _ in fk_cayley_quartets():
            assert 1 <= a < b < c < d <= 8

    def test_signs_are_unit(self):
        for *_, sign in fk_cayley_quartets():
            assert sign in (+1, -1)

    def test_seven_self_dual_pairs(self):
        """Each quartet pairs with its complement in {1,...,8}; pair shares sign."""
        quartets = fk_cayley_quartets()
        signs = {tuple(sorted([a, b, c, d])): sign for a, b, c, d, sign in quartets}
        for q, sign in signs.items():
            complement = tuple(sorted(set(range(1, 9)) - set(q)))
            assert complement in signs, f"complement of {q} missing"
            assert signs[complement] == sign, \
                f"sign mismatch on Hodge pair {q} ↔ {complement}"


class TestFKHamiltonianConstructive:
    """W constructed from γ matrices + 14 Cayley quartets."""

    @pytest.fixture(scope='class')
    def W(self):
        return fk_hamiltonian()

    def test_integer_real(self, W):
        assert W.dtype == np.int64 or W.dtype == int

    def test_dimensions(self, W):
        assert W.shape == (16, 16)

    def test_symmetric(self, W):
        assert np.array_equal(W, W.T)

    def test_trace_zero(self, W):
        assert np.trace(W) == 0

    def test_frobenius_224(self, W):
        """tr(W²) = 14 × 16 = 224 (one I₁₆ per Cayley term, all cross-terms traceless)."""
        assert np.trace(W @ W) == 224

    def test_minimal_polynomial(self, W):
        """W³ + 12W² - 28W = 0 — the minimal polynomial of W."""
        residual = fk_minimal_polynomial_residual(W)
        assert np.array_equal(residual, np.zeros((16, 16), dtype=int))

    def test_eigenvalues_match_spectrum(self, W):
        evals = sorted(np.linalg.eigvalsh(W))
        expected = sorted([-14] + [0] * 8 + [2] * 7)
        np.testing.assert_array_almost_equal(evals, expected, decimal=10)

    def test_ground_state_unique(self, W):
        evals = np.linalg.eigvalsh(W)
        assert np.sum(np.abs(evals - (-14)) < 1e-8) == 1

    def test_spectral_gap_14(self, W):
        evals = sorted(np.linalg.eigvalsh(W))
        assert evals[0] == pytest.approx(-14)
        assert evals[1] == pytest.approx(0, abs=1e-8)
        assert evals[1] - evals[0] == pytest.approx(14)

    def test_ground_state_eigenvector(self, W):
        """W · gs_vec = -14 · gs_vec where gs_vec = e₀ - e₁₅."""
        v = fk_ground_state_vector()
        np.testing.assert_array_equal(W @ v, -14 * v)


class TestFKLeanSparseParity:
    """`fk_hamiltonian()` (constructive) must equal `fk_hamiltonian_sparse()` (Lean's W)."""

    def test_sparse_matches_constructive(self):
        W_full = fk_hamiltonian()
        W_lean = fk_hamiltonian_sparse()
        np.testing.assert_array_equal(W_full, W_lean)

    def test_sparse_has_ten_nonzero_entries(self):
        W = fk_hamiltonian_sparse()
        assert int((W != 0).sum()) == 10

    def test_sparse_diag_minus_six_at_extremes(self):
        W = fk_hamiltonian_sparse()
        assert W[0, 0] == -6
        assert W[15, 15] == -6

    def test_sparse_diag_plus_two_at_two_bit_indices(self):
        W = fk_hamiltonian_sparse()
        for idx in (3, 5, 6, 9, 10, 12):
            assert W[idx, idx] == 2, f"W[{idx},{idx}] expected 2"

    def test_sparse_corner_eight(self):
        W = fk_hamiltonian_sparse()
        assert W[0, 15] == 8
        assert W[15, 0] == 8

    def test_sparse_zero_on_odd_parity(self):
        """W·|n⟩ = 0 for any odd-parity Fock-basis state."""
        W = fk_hamiltonian_sparse()
        for n in range(16):
            if bin(n).count('1') % 2 == 1:
                e_n = np.zeros(16, dtype=int)
                e_n[n] = 1
                assert np.array_equal(W @ e_n, np.zeros(16, dtype=int)), \
                    f"odd-parity state |{n:04b}⟩ not annihilated"


class TestFKSpinSevenMultiplicities:
    """The {1, 8, 7} multiplicity system from the Spin(7) decomposition."""

    def test_multiplicities_sum_to_dimension(self):
        m1, m2, m3 = 1, 8, 7
        assert m1 + m2 + m3 == 16

    def test_eigenvalue_dict(self):
        spec = fk_eigenvalues()
        assert spec == {-14: 1, 0: 8, +2: 7}

    def test_trace_constraint(self):
        spec = fk_eigenvalues()
        weighted = sum(eigval * mult for eigval, mult in spec.items())
        assert weighted == 0

    def test_frobenius_constraint(self):
        spec = fk_eigenvalues()
        weighted = sum(eigval ** 2 * mult for eigval, mult in spec.items())
        assert weighted == 224

    def test_spectral_gap(self):
        assert fk_spectral_gap() == 14


class TestFermionParity:
    """Fermion-parity matrix Γ commutes with W (each quartic monomial degree 4)."""

    @pytest.fixture(scope='class')
    def parity(self):
        return fk_parity_matrix()

    def test_diagonal(self, parity):
        assert np.array_equal(parity, np.diag(np.diag(parity)))

    def test_squared_identity(self, parity):
        assert np.array_equal(parity @ parity, np.eye(16, dtype=int))

    def test_eight_plus_eight_split(self, parity):
        diag = np.diag(parity)
        assert int((diag == +1).sum()) == 8
        assert int((diag == -1).sum()) == 8

    def test_commutes_with_W(self, parity):
        W = fk_hamiltonian()
        assert np.array_equal(W @ parity, parity @ W)

    def test_ground_state_even_parity(self, parity):
        """The unique ground state |GS⟩ has Γ|GS⟩ = +|GS⟩ (Spin(7) singlet, even)."""
        v = fk_ground_state_vector()
        assert np.array_equal(parity @ v, v)


class TestDimensionalLadderEvidence:
    """Phase 5s Wave 4 bridge theorem evidence stack across 1+1D / 2+1D / 3+1D."""

    def test_three_dimensions_present(self):
        ladder = fk_dimensional_ladder_evidence()
        assert set(ladder.keys()) == {'1+1D', '2+1D', '3+1D'}

    def test_one_two_d_proved(self):
        ladder = fk_dimensional_ladder_evidence()
        assert ladder['1+1D']['status'] == 'PROVED'
        assert ladder['2+1D']['status'] == 'PROVED'

    def test_three_d_tracked_prop(self):
        """3+1D entry was AXIOMATIZED pre-2026-05-19; converted to
        TRACKED_PROP (`TPFConjecture`) on 2026-05-19 per Pipeline
        Invariant #15 (axioms are temporary scaffolding)."""
        ladder = fk_dimensional_ladder_evidence()
        assert ladder['3+1D']['status'] == 'TRACKED_PROP'

    def test_two_d_witness_is_fk_summary(self):
        ladder = fk_dimensional_ladder_evidence()
        assert 'fk_summary' in ladder['2+1D']['witness']

    def test_two_d_gap_matches_spectral_gap(self):
        ladder = fk_dimensional_ladder_evidence()
        assert ladder['2+1D']['gap'] == fk_spectral_gap()

    def test_three_d_witness_is_tpf_conjecture(self):
        """Witness updated from `gapped_interface_axiom` (pre-2026-05-19)
        to `TPFConjecture` (post-Tracked-Prop conversion)."""
        ladder = fk_dimensional_ladder_evidence()
        assert ladder['3+1D']['witness'] == 'TPFConjecture'


class TestModularityTheorem:
    """Tests for the general det(S)≠0 → Z₂ trivial theorem."""

    def test_proportional_rows_singular(self):
        """Any matrix with proportional rows has det = 0."""
        rng = np.random.default_rng(42)
        for n in [3, 4, 5]:
            A = rng.integers(0, 10, (n, n)).astype(float)
            A[1] = 2.5 * A[0]
            assert abs(np.linalg.det(A)) < 1e-8

    def test_invertible_implies_no_proportional_rows(self):
        """Identity is invertible → standard-basis rows are pairwise independent."""
        A = np.eye(5)
        assert abs(np.linalg.det(A)) > 0.5

    def test_ising_s_matrix_modular(self):
        """Ising MTC: det(S) ≠ 0 → Müger center is trivial."""
        s2 = np.sqrt(2)
        S = np.array([
            [1, s2, 1],
            [s2, 0, -s2],
            [1, -s2, 1],
        ]) / 2
        assert abs(np.linalg.det(S)) > 0.1

    def test_fibonacci_s_matrix_modular(self):
        """Fibonacci MTC: det(S) ≠ 0 → modular."""
        phi = (1 + np.sqrt(5)) / 2
        D2 = 2 + phi
        S = np.array([
            [1, phi],
            [phi, -1],
        ]) / np.sqrt(D2)
        assert abs(np.linalg.det(S)) > 0.1
