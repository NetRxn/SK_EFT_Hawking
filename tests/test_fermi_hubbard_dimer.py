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
    H_full,
    H_singlet,
    TRIPLET_MINUS,
    TRIPLET_PLUS,
    TRIPLET_ZERO_UNNORM,
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
