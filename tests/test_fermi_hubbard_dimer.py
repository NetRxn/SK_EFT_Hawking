"""Tests for Phase 5t Wave 2 Fermi-Hubbard dimer algebraic core.

Every test mirrors a Lean theorem in
``lean/SKEFTHawking/FermiHubbardDimer.lean``. Numerical cross-checks run
over a random parameter grid so the Python and Lean sides can't silently
drift apart.
"""

from __future__ import annotations

import numpy as np
import pytest

from src.fermi_hubbard.dimer import (
    BASIS_6,
    DOWN_UP,
    H_full,
    H_singlet,
    TRIPLET_MINUS,
    TRIPLET_PLUS,
    TRIPLET_ZERO_UNNORM,
    UP_DOWN,
    V_DMINUS,
    V_DPLUS,
    V_S,
    V_T0,
    block_match_Dminus,
    block_match_Dplus,
    block_match_s,
    bright_energies_U0,
    chiral_anticommutator_U0,
    chiral_op,
    dark_vec,
    singlet_determinant,
    singlet_trace,
)


rng = np.random.default_rng(seed=5723)


#: Deterministic sample grid covering physical sign choices.
PARAM_GRID = [
    (1.0, 0.0, 0.0),
    (1.0, 2.0, 0.0),
    (0.7, -1.3, 0.0),
    (1.0, 0.0, 3.0),
    (1.0, 2.0, 3.0),
    (0.0, 1.0, 1.0),
    (-0.5, 2.5, 4.0),
]


@pytest.fixture
def random_params():
    """Random (t, Δ, U) with |.| ≤ 3 — both signs, includes near-zero."""
    return rng.uniform(-3.0, 3.0, size=(40, 3))


class TestSingletHamiltonianStructure:
    """T1 + matrix shape basics."""

    def test_shape(self):
        H = H_singlet(1.0, 0.5, 0.2)
        assert H.shape == (3, 3)
        assert H.dtype == np.float64

    def test_H_singlet_is_symmetric_on_grid(self, random_params):
        # Lean T1: (H_singlet)ᵀ = H_singlet.
        for t, delta, U in random_params:
            H = H_singlet(float(t), float(delta), float(U))
            assert np.allclose(H, H.T, atol=1e-12)

    @pytest.mark.parametrize("t, delta, U", PARAM_GRID)
    def test_H_singlet_specific_entries(self, t, delta, U):
        # Verify matrix layout entry-by-entry.
        H = H_singlet(t, delta, U)
        assert H[0, 0] == pytest.approx(U)
        assert H[1, 1] == pytest.approx(U)
        assert H[2, 2] == pytest.approx(0.0)
        assert H[0, 1] == pytest.approx(delta)
        assert H[0, 2] == pytest.approx(-2.0 * t)
        assert H[1, 2] == pytest.approx(0.0)


class TestDarkState:
    """T2 + T3."""

    @pytest.mark.parametrize("t, delta", [(1.0, 2.0), (0.7, -1.3), (3.0, 0.5)])
    def test_dark_vec_in_kernel_U0(self, t, delta):
        # Lean T2: H_singlet(t, Δ, 0) · darkVec(t, Δ) = 0.
        H0 = H_singlet(t, delta, 0.0)
        v = dark_vec(t, delta)
        assert np.allclose(H0 @ v, np.zeros(3), atol=1e-12)

    def test_dark_vec_in_kernel_random_grid(self, random_params):
        for t, delta, _ in random_params:
            H0 = H_singlet(float(t), float(delta), 0.0)
            v = dark_vec(float(t), float(delta))
            assert np.allclose(H0 @ v, np.zeros(3), atol=1e-12)

    @pytest.mark.parametrize("t, delta",
                             [(1.0, 0.0), (0.0, 2.0), (0.3, -0.5)])
    def test_dark_vec_nonzero_when_params_nontrivial(self, t, delta):
        # Lean T3: darkVec ≠ 0 whenever (t, Δ) ≠ (0, 0).
        v = dark_vec(t, delta)
        assert np.any(v != 0.0)

    def test_dark_vec_zero_only_at_origin(self):
        v = dark_vec(0.0, 0.0)
        assert np.allclose(v, np.zeros(3))


class TestChiralSymmetry:
    """T4 + T5."""

    def test_chiral_op_involutory(self):
        # Lean T4: Γ · Γ = I.
        G = chiral_op()
        assert np.allclose(G @ G, np.eye(3))

    def test_chiral_op_diag_signature(self):
        G = chiral_op()
        assert np.array_equal(np.diag(G), np.array([1.0, -1.0, -1.0]))

    @pytest.mark.parametrize("t, delta",
                             [(1.0, 2.0), (0.7, -1.3), (2.5, 0.0),
                              (0.0, 1.5), (-0.5, 2.5)])
    def test_chiral_anticommutes_at_U0(self, t, delta):
        # Lean T5: {Γ, H_singlet(t, Δ, 0)} = 0.
        anti = chiral_anticommutator_U0(t, delta)
        assert np.allclose(anti, np.zeros((3, 3)), atol=1e-12)

    def test_chiral_breaks_at_U_nonzero(self):
        # Sanity: the anticommutator is NOT zero when U ≠ 0.
        H = H_singlet(1.0, 2.0, 1.5)
        G = chiral_op()
        anti = G @ H + H @ G
        assert not np.allclose(anti, np.zeros((3, 3)))


class TestDeterminantAndTrace:
    """T6 + T7."""

    @pytest.mark.parametrize("t, delta, U", PARAM_GRID)
    def test_det_matches_formula(self, t, delta, U):
        # Lean T6: det H₃ = -4 U t².
        H = H_singlet(t, delta, U)
        det_numerical = np.linalg.det(H)
        det_formula = singlet_determinant(t, delta, U)
        assert det_numerical == pytest.approx(det_formula, abs=1e-10)
        assert det_formula == pytest.approx(-4.0 * U * t**2)

    @pytest.mark.parametrize("t, delta", [(1.0, 2.0), (0.7, -1.3), (2.0, 0.5)])
    def test_det_zero_at_U0(self, t, delta):
        # Lean T6a: det H_singlet(t, Δ, 0) = 0.
        assert singlet_determinant(t, delta, 0.0) == pytest.approx(0.0)

    @pytest.mark.parametrize("t, delta, U", PARAM_GRID)
    def test_trace_matches_formula(self, t, delta, U):
        # Lean T7: tr H₃ = 2U.
        H = H_singlet(t, delta, U)
        assert np.trace(H) == pytest.approx(2.0 * U)
        assert singlet_trace(t, delta, U) == pytest.approx(2.0 * U)

    @pytest.mark.parametrize("t, delta", [(1.0, 2.0), (0.0, 1.0), (3.0, 0.0)])
    def test_trace_zero_at_U0(self, t, delta):
        assert singlet_trace(t, delta, 0.0) == pytest.approx(0.0)


class TestBrightEigenvalues:
    """Informal T4 — paired nonzero eigenvalues ±√(Δ²+4t²)."""

    @pytest.mark.parametrize("t, delta",
                             [(1.0, 2.0), (0.7, -1.3), (3.0, 0.5),
                              (0.0, 1.5), (2.0, 0.0)])
    def test_bright_energies_match_eigendecomposition(self, t, delta):
        H0 = H_singlet(t, delta, 0.0)
        eigs = np.sort(np.linalg.eigvalsh(H0))
        expected_low, expected_high = bright_energies_U0(t, delta)
        assert eigs[0] == pytest.approx(expected_low, abs=1e-10)
        assert eigs[1] == pytest.approx(0.0, abs=1e-10)
        assert eigs[2] == pytest.approx(expected_high, abs=1e-10)

    def test_bright_energies_paired(self):
        low, high = bright_energies_U0(1.0, 2.0)
        assert low == pytest.approx(-high)


class TestFullHamiltonianTriplet:
    """T10a + T10b + T10c."""

    def test_H_full_shape(self):
        H = H_full(1.0, 0.5, 0.2)
        assert H.shape == (6, 6)
        assert len(BASIS_6) == 6

    @pytest.mark.parametrize("t, delta, U", PARAM_GRID)
    def test_triplet_plus_is_zero_eigenvector(self, t, delta, U):
        # Lean T10a.
        H = H_full(t, delta, U)
        assert np.allclose(H @ TRIPLET_PLUS, np.zeros(6), atol=1e-12)

    @pytest.mark.parametrize("t, delta, U", PARAM_GRID)
    def test_triplet_zero_is_zero_eigenvector(self, t, delta, U):
        # Lean T10b. Unnormalized; Hv=0 ⟹ H(v/√2)=0.
        H = H_full(t, delta, U)
        assert np.allclose(H @ TRIPLET_ZERO_UNNORM, np.zeros(6), atol=1e-12)

    @pytest.mark.parametrize("t, delta, U", PARAM_GRID)
    def test_triplet_minus_is_zero_eigenvector(self, t, delta, U):
        # Lean T10c.
        H = H_full(t, delta, U)
        assert np.allclose(H @ TRIPLET_MINUS, np.zeros(6), atol=1e-12)

    def test_full_hamiltonian_is_symmetric(self, random_params):
        # Not in the Lean module yet, but a natural sanity check.
        for t, delta, U in random_params:
            H = H_full(float(t), float(delta), float(U))
            assert np.allclose(H, H.T, atol=1e-12)


class TestSymmetryAdaptedBasisEmbeddings:
    """Phase 5t W3: basis-change block-match + computational decomposition."""

    def test_basis_vector_components(self):
        # Sanity: the unnormalized basis vectors have the expected
        # components in the {|↑,↑⟩, |↑↓,0⟩, |↑,↓⟩, |↓,↑⟩, |0,↑↓⟩, |↓,↓⟩} site
        # ordering.
        np.testing.assert_array_equal(V_DPLUS, [0, 1, 0, 0, 1, 0])
        np.testing.assert_array_equal(V_DMINUS, [0, 1, 0, 0, -1, 0])
        np.testing.assert_array_equal(V_S, [0, 0, 1, -1, 0, 0])
        np.testing.assert_array_equal(V_T0, [0, 0, 1, 1, 0, 0])
        np.testing.assert_array_equal(UP_DOWN, [0, 0, 1, 0, 0, 0])
        np.testing.assert_array_equal(DOWN_UP, [0, 0, 0, 1, 0, 0])

    def test_symmetry_basis_are_mutually_orthogonal(self):
        # {D+, D-, s, t0} span the S_z = 0 subspace with distinct symmetries;
        # they must be pairwise orthogonal in the site basis.
        basis = [V_DPLUS, V_DMINUS, V_S, V_T0]
        for i, v in enumerate(basis):
            for j, w in enumerate(basis):
                if i != j:
                    assert np.dot(v, w) == 0.0, f"{i},{j} not orthogonal"

    @pytest.mark.parametrize("t, delta, U", PARAM_GRID)
    def test_H_full_acts_on_v_Dplus(self, t, delta, U):
        # Lean W3a: H_full · v_Dplus = U·v_Dplus + Δ·v_Dminus + (-2t)·v_s.
        H = H_full(t, delta, U)
        assert np.allclose(H @ V_DPLUS, block_match_Dplus(t, delta, U),
                            atol=1e-12)

    @pytest.mark.parametrize("t, delta, U", PARAM_GRID)
    def test_H_full_acts_on_v_Dminus(self, t, delta, U):
        # Lean W3b: H_full · v_Dminus = Δ·v_Dplus + U·v_Dminus.
        H = H_full(t, delta, U)
        assert np.allclose(H @ V_DMINUS, block_match_Dminus(t, delta, U),
                            atol=1e-12)

    @pytest.mark.parametrize("t, delta, U", PARAM_GRID)
    def test_H_full_acts_on_v_s(self, t, delta, U):
        # Lean W3c: H_full · v_s = (-2t)·v_Dplus.
        H = H_full(t, delta, U)
        assert np.allclose(H @ V_S, block_match_s(t, delta, U),
                            atol=1e-12)

    @pytest.mark.parametrize("t, delta, U", PARAM_GRID)
    def test_H_full_acts_on_v_t0_is_zero(self, t, delta, U):
        # Lean W3d: triplet t0 decouples at zero energy for all (t, Δ, U).
        H = H_full(t, delta, U)
        assert np.allclose(H @ V_T0, np.zeros(6), atol=1e-12)

    def test_H_full_acts_on_symmetry_basis_on_random_grid(self, random_params):
        # The four block-match identities on a broader random grid.
        for t, delta, U in random_params:
            t_, d_, U_ = float(t), float(delta), float(U)
            H = H_full(t_, d_, U_)
            assert np.allclose(H @ V_DPLUS, block_match_Dplus(t_, d_, U_),
                                atol=1e-12)
            assert np.allclose(H @ V_DMINUS, block_match_Dminus(t_, d_, U_),
                                atol=1e-12)
            assert np.allclose(H @ V_S, block_match_s(t_, d_, U_),
                                atol=1e-12)
            assert np.allclose(H @ V_T0, np.zeros(6), atol=1e-12)

    def test_updown_decomposition(self):
        # Lean W3e: 2·up_down = v_t0 + v_s.
        np.testing.assert_array_equal(2.0 * UP_DOWN, V_T0 + V_S)

    def test_downup_decomposition(self):
        # Lean W3f: 2·down_up = v_t0 - v_s.
        np.testing.assert_array_equal(2.0 * DOWN_UP, V_T0 - V_S)

    def test_block_match_singlet_rows_match_H_singlet(self, random_params):
        # The three block-match RHSs are exactly the (D+, D-, s) rows of
        # H_singlet re-expressed in the 6-dim site basis. Project the RHS
        # onto the {v_Dplus, v_Dminus, v_s} basis and compare to H_singlet
        # row-by-row.
        norm_Dplus = np.dot(V_DPLUS, V_DPLUS)  # = 2
        norm_Dminus = np.dot(V_DMINUS, V_DMINUS)  # = 2
        norm_s = np.dot(V_S, V_S)  # = 2
        for t, delta, U in random_params:
            t_, d_, U_ = float(t), float(delta), float(U)
            Hs = H_singlet(t_, d_, U_)
            # Row 0 (D+):
            rhs0 = block_match_Dplus(t_, d_, U_)
            assert np.isclose(np.dot(V_DPLUS, rhs0) / norm_Dplus, Hs[0, 0])
            assert np.isclose(np.dot(V_DMINUS, rhs0) / norm_Dminus, Hs[0, 1])
            assert np.isclose(np.dot(V_S, rhs0) / norm_s, Hs[0, 2])
            # Row 1 (D-):
            rhs1 = block_match_Dminus(t_, d_, U_)
            assert np.isclose(np.dot(V_DPLUS, rhs1) / norm_Dplus, Hs[1, 0])
            assert np.isclose(np.dot(V_DMINUS, rhs1) / norm_Dminus, Hs[1, 1])
            assert np.isclose(np.dot(V_S, rhs1) / norm_s, Hs[1, 2])
            # Row 2 (s):
            rhs2 = block_match_s(t_, d_, U_)
            assert np.isclose(np.dot(V_DPLUS, rhs2) / norm_Dplus, Hs[2, 0])
            assert np.isclose(np.dot(V_DMINUS, rhs2) / norm_Dminus, Hs[2, 1])
            assert np.isclose(np.dot(V_S, rhs2) / norm_s, Hs[2, 2])
