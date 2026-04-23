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
    bright_vec_minus,
    bright_vec_plus,
    charpoly_coeffs,
    chiral_anticommutator_U0,
    chiral_conjugation_U0,
    chiral_image_dark,
    chiral_image_minus,
    chiral_image_plus,
    chiral_op,
    chiral_proj_minus,
    chiral_proj_plus,
    bright_vec_minus_norm,
    bright_vec_plus_norm,
    E_minus,
    E_minus_char_residual,
    E_minus_eigenvector,
    E_plus,
    E_plus_char_residual,
    E_plus_eigenvector,
    J_leading_superexchange,
    J_superexchange,
    antisymmetric_doublon_vec,
    dark_state_theta_norm,
    dark_vec_norm,
    geometric_phase_loop_check,
    u_swap_action_on_kernel,
    u_swap_adapted,
    u_swap_singlet,
    dark_state_theta,
    dark_vec,
    gap_at_U0,
    singlet_determinant,
    singlet_trace,
    spectrum_U0,
    spectrum_symmetric_under_neg,
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


class TestU0SpectrumW4:
    """Phase 5t W4: θ-parametrized dark state + bright eigenvectors +
    charpoly + linear independence at U = 0."""

    @pytest.mark.parametrize("t, delta, theta", [
        (1.0, 0.5, 0.3),
        (1.0, 2.0, 1.2),
        (0.7, -1.3, 2.0),
        (2.0, 0.0, np.pi / 2),
        (0.0, 1.0, 0.0),
        (-0.5, 2.5, 1.5),
    ])
    def test_dark_state_theta_in_kernel_when_angle_matches(self, t, delta, theta):
        # Lean W4a: if Δ·sin θ = 2t·cos θ then H(U=0)·darkStateθ = 0.
        # We re-derive a matching θ analytically and check.
        # darkVec (unnormalized) is (0, 2t, Δ); matching angle tan θ = 2t/Δ
        # when Δ≠0. Use explicit (sin θ, cos θ) = (2t, Δ)/g normalization.
        g = np.sqrt(delta**2 + 4 * t**2)
        if g == 0:
            return
        sin_theta = 2 * t / g
        cos_theta = delta / g
        psi = np.array([0.0, sin_theta, cos_theta])
        assert np.isclose(delta * sin_theta, 2 * t * cos_theta, atol=1e-12)
        assert np.allclose(H_singlet(t, delta, 0.0) @ psi, np.zeros(3),
                            atol=1e-12)

    def test_darkStateθ_nonzero_regardless_of_theta(self):
        # Lean W4e'': darkStateθ is always nonzero (Pythagorean identity).
        rng = np.random.default_rng(seed=7)
        for _ in range(20):
            theta = rng.uniform(-10.0, 10.0)
            v = dark_state_theta(theta)
            # ||v||² = 0 + sin²θ + cos²θ = 1
            assert np.isclose(np.dot(v, v), 1.0, atol=1e-12)
            assert not np.allclose(v, np.zeros(3))

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
        (0.0, 1.0),
    ])
    def test_bright_vec_plus_is_positive_eigenvector(self, t, delta):
        # Lean W4b: H(U=0) · brightVecPlus = +gap · brightVecPlus.
        gap = gap_at_U0(t, delta)
        bv = bright_vec_plus(t, delta)
        H = H_singlet(t, delta, 0.0)
        assert np.allclose(H @ bv, gap * bv, atol=1e-12)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
        (0.0, 1.0),
    ])
    def test_bright_vec_minus_is_negative_eigenvector(self, t, delta):
        # Lean W4c: H(U=0) · brightVecMinus = -gap · brightVecMinus.
        gap = gap_at_U0(t, delta)
        bv = bright_vec_minus(t, delta)
        H = H_singlet(t, delta, 0.0)
        assert np.allclose(H @ bv, -gap * bv, atol=1e-12)

    def test_bright_vec_nonzero_when_params_nontrivial(self):
        # Lean W4e + W4e'.
        for t, delta in [(1.0, 0.0), (0.0, 1.0), (0.5, -0.5), (2.0, 3.0)]:
            assert not np.allclose(bright_vec_plus(t, delta), np.zeros(3))
            assert not np.allclose(bright_vec_minus(t, delta), np.zeros(3))

    def test_gap_at_U0_pos_when_params_nontrivial(self):
        # Lean W4d.
        for t, delta in [(1.0, 0.0), (0.0, 1.0), (0.5, -0.5), (2.0, 3.0)]:
            assert gap_at_U0(t, delta) > 0

    def test_gap_at_U0_sq_identity(self):
        # Lean W4d': gap² = Δ² + 4t².
        rng = np.random.default_rng(seed=11)
        for _ in range(20):
            t = rng.uniform(-3.0, 3.0)
            delta = rng.uniform(-3.0, 3.0)
            assert np.isclose(gap_at_U0(t, delta)**2, delta**2 + 4*t**2,
                              atol=1e-12)

    def test_eigenvalues_distinct_at_U0(self):
        # Lean W4i: {0, +gap, -gap} are pairwise distinct when (t,Δ) ≠ 0.
        for t, delta in [(1.0, 0.0), (0.0, 1.0), (0.5, -0.5), (2.0, 3.0)]:
            gap = gap_at_U0(t, delta)
            assert gap != 0.0
            assert gap != -gap  # since gap > 0

    @pytest.mark.parametrize("t, delta, U", PARAM_GRID)
    def test_charpoly_coeffs_match_np_poly(self, t, delta, U):
        # Lean W4f (charpoly_H_singlet): coefficients match np's characteristic poly.
        coeffs = charpoly_coeffs(t, delta, U)  # (c3, c2, c1, c0) = (1, -2U, U²-Δ²-4t², 4Ut²)
        # np.poly returns coefficients of (X - λ₁)(X - λ₂)... for given eigenvalues.
        # Use np.linalg.eigvalsh on H_singlet and compute np.poly, compare.
        H = H_singlet(t, delta, U)
        eigs = np.linalg.eigvalsh(H)
        np_coeffs = np.poly(eigs)  # [1, -sum(eigs), pair_sum, -prod(eigs)]
        assert np.allclose(np_coeffs, np.array(coeffs), atol=1e-9)

    def test_charpoly_U0_factors_correctly(self):
        # Lean W4g: at U=0, charpoly = λ · (λ² - (Δ²+4t²)).
        for t, delta in [(1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0)]:
            coeffs = charpoly_coeffs(t, delta, 0.0)
            assert coeffs == (1.0, 0.0, -(delta**2 + 4*t**2), 0.0)

    def test_spectrum_at_U0_is_0_plus_gap_minus_gap(self):
        # Lean W4h: the three eigenvalues at U=0 are exactly {0, +gap, -gap}.
        for t, delta in [(1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0),
                          (-0.5, 2.5)]:
            eigs = sorted(np.linalg.eigvalsh(H_singlet(t, delta, 0.0)))
            gap = gap_at_U0(t, delta)
            expected = sorted([-gap, 0.0, gap])
            assert np.allclose(eigs, expected, atol=1e-12)

    def test_eigenvector_matrix_det_equals_2_times_g_root(self):
        # Lean W4j: det of eigenvector matrix = 2·(Δ²+4t²)·√(Δ²+4t²).
        for t, delta in [(1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0),
                          (-0.5, 2.5)]:
            g = delta**2 + 4 * t**2
            sqrt_g = np.sqrt(g)
            M = np.array([
                [0.0, 2*t, delta],
                [sqrt_g, delta, -2*t],
                [-sqrt_g, delta, -2*t],
            ])
            det = np.linalg.det(M)
            assert np.isclose(det, 2 * g * sqrt_g, atol=1e-9)

    def test_eigenvectors_linearly_independent_at_U0(self):
        # Lean W4k: the 3 eigenvectors are linearly independent when (t,Δ) ≠ 0.
        for t, delta in [(1.0, 0.0), (0.0, 1.0), (0.5, -0.5), (2.0, 3.0),
                          (-0.5, 2.5)]:
            dv = dark_vec(t, delta)
            bp = bright_vec_plus(t, delta)
            bm = bright_vec_minus(t, delta)
            M = np.array([dv, bp, bm])
            # All three are rows of a 3x3 matrix with nonzero det ⇒ independent
            assert abs(np.linalg.det(M)) > 1e-9

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
        (0.0, 1.0), (3.0, -2.0),
    ])
    def test_dark_brightPlus_orthogonal(self, t, delta):
        # Lean W4l.
        assert np.isclose(np.dot(dark_vec(t, delta),
                                   bright_vec_plus(t, delta)), 0.0,
                          atol=1e-12)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
        (0.0, 1.0), (3.0, -2.0),
    ])
    def test_dark_brightMinus_orthogonal(self, t, delta):
        # Lean W4m.
        assert np.isclose(np.dot(dark_vec(t, delta),
                                   bright_vec_minus(t, delta)), 0.0,
                          atol=1e-12)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
        (0.0, 1.0), (3.0, -2.0),
    ])
    def test_brightPlus_brightMinus_orthogonal(self, t, delta):
        # Lean W4n: inner product is -g + Δ² + 4t² = 0.
        assert np.isclose(np.dot(bright_vec_plus(t, delta),
                                   bright_vec_minus(t, delta)), 0.0,
                          atol=1e-12)

    def test_three_eigenvectors_pairwise_orthogonal_on_random_grid(self):
        # All three orthogonality theorems simultaneously on a wider grid.
        rng_local = np.random.default_rng(seed=19)
        for _ in range(15):
            t = rng_local.uniform(-3.0, 3.0)
            delta = rng_local.uniform(-3.0, 3.0)
            dv = dark_vec(t, delta)
            bp = bright_vec_plus(t, delta)
            bm = bright_vec_minus(t, delta)
            assert np.isclose(np.dot(dv, bp), 0.0, atol=1e-12)
            assert np.isclose(np.dot(dv, bm), 0.0, atol=1e-12)
            assert np.isclose(np.dot(bp, bm), 0.0, atol=1e-12)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
        (0.0, 1.0),
    ])
    def test_spectrum_membership_matches_three_eigenvalues(self, t, delta):
        # Lean W4p: μ ∈ spectrum ℝ H_singlet(t,Δ,0) ↔ μ ∈ {0, +gap, -gap}.
        # Python cross-check: the eigvalsh of the matrix equals exactly the
        # predicted three-element set (up to floating-point tolerance).
        gap = gap_at_U0(t, delta)
        eigs = set(np.round(np.linalg.eigvalsh(H_singlet(t, delta, 0.0)),
                              decimals=10))
        expected = set(np.round([0.0, gap, -gap], decimals=10))
        assert eigs == expected

    def test_charpoly_roots_multiset_at_U0(self):
        # Lean W4o: roots multiset = {0, +gap, -gap}.
        # Python cross-check: np.roots on the cubic coefficients should
        # give exactly these three values.
        for t, delta in [(1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5)]:
            coeffs = charpoly_coeffs(t, delta, 0.0)
            # np.roots wants highest-degree coeff first; charpoly_coeffs
            # already returns (c3, c2, c1, c0).
            roots = sorted(np.roots(coeffs))
            gap = gap_at_U0(t, delta)
            expected = sorted([-gap, 0.0, gap])
            assert np.allclose(roots, expected, atol=1e-9)


class TestChiralPinningW5:
    """Phase 5t W5 chiral conjugation + BDI spectrum pairing +
    zero-mode pinning. Each test mirrors a Lean theorem in
    ``FermiHubbardDimer.lean`` Section 10."""

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
        (0.0, 1.0), (3.0, -2.0),
    ])
    def test_chiralOp_conjugation_neg_deterministic(self, t, delta):
        # Lean W5a: Γ · H · Γ = -H at U=0.
        H = H_singlet(t, delta, 0.0)
        assert np.allclose(chiral_conjugation_U0(t, delta), -H, atol=1e-12)

    def test_chiralOp_conjugation_neg_random(self):
        # Lean W5a on a wider random (t,Δ) grid.
        rng_local = np.random.default_rng(seed=5705)
        for _ in range(25):
            t = rng_local.uniform(-3.0, 3.0)
            delta = rng_local.uniform(-3.0, 3.0)
            H = H_singlet(t, delta, 0.0)
            assert np.allclose(chiral_conjugation_U0(t, delta), -H,
                               atol=1e-12)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
    ])
    def test_chiral_maps_eigenvector_bright_plus(self, t, delta):
        # Lean W5b applied to the +gap eigenvector:
        # H v_+ = +gap · v_+ ⟹ H (Γ v_+) = -gap · (Γ v_+).
        H = H_singlet(t, delta, 0.0)
        gap = gap_at_U0(t, delta)
        vp = bright_vec_plus(t, delta)
        gamma_vp = chiral_op() @ vp
        lhs = H @ gamma_vp
        rhs = -gap * gamma_vp
        assert np.allclose(lhs, rhs, atol=1e-12)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
    ])
    def test_chiral_maps_eigenvector_bright_minus(self, t, delta):
        # Lean W5b applied to the -gap eigenvector:
        # H v_- = -gap · v_- ⟹ H (Γ v_-) = +gap · (Γ v_-).
        H = H_singlet(t, delta, 0.0)
        gap = gap_at_U0(t, delta)
        vm = bright_vec_minus(t, delta)
        gamma_vm = chiral_op() @ vm
        lhs = H @ gamma_vm
        rhs = gap * gamma_vm
        assert np.allclose(lhs, rhs, atol=1e-12)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
        (0.0, 1.0), (3.0, -2.0),
    ])
    def test_spectrum_pairing_U0(self, t, delta):
        # Lean W5c: μ ∈ spec ↔ -μ ∈ spec.
        assert spectrum_symmetric_under_neg(t, delta)

    def test_spectrum_pairing_U0_random(self):
        rng_local = np.random.default_rng(seed=5712)
        for _ in range(20):
            t = rng_local.uniform(-3.0, 3.0)
            delta = rng_local.uniform(-3.0, 3.0)
            assert spectrum_symmetric_under_neg(t, delta)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0),
        (0.0, 1.0), (3.0, -2.0),
    ])
    def test_zero_mem_spectrum_U0(self, t, delta):
        # Lean W5d: 0 is always in the spectrum.
        eigs = np.linalg.eigvalsh(H_singlet(t, delta, 0.0))
        assert np.min(np.abs(eigs)) < 1e-10

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
        (0.0, 1.0), (3.0, -2.0),
    ])
    def test_darkVec_in_chiral_minus_eigenspace(self, t, delta):
        # Lean W5e: Γ · darkVec = -darkVec.
        dv = dark_vec(t, delta)
        assert np.allclose(chiral_image_dark(t, delta), -dv, atol=1e-12)

    def test_darkVec_in_chiral_minus_eigenspace_random(self):
        rng_local = np.random.default_rng(seed=5729)
        for _ in range(20):
            t = rng_local.uniform(-3.0, 3.0)
            delta = rng_local.uniform(-3.0, 3.0)
            dv = dark_vec(t, delta)
            assert np.allclose(chiral_image_dark(t, delta), -dv,
                               atol=1e-12)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
    ])
    def test_zero_mode_pinned_bundle(self, t, delta):
        # Lean W5f bundled: dark vec is (i) kernel-vector, (ii) -1 eigenvector
        # of Γ, (iii) nonzero (for nontrivial params).
        dv = dark_vec(t, delta)
        H = H_singlet(t, delta, 0.0)
        assert np.allclose(H @ dv, 0.0, atol=1e-12)
        assert np.allclose(chiral_image_dark(t, delta), -dv, atol=1e-12)
        assert np.linalg.norm(dv) > 1e-9

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
        (0.0, 1.0), (3.0, -2.0),
    ])
    def test_brightVecPlus_chiral_image(self, t, delta):
        # Lean W5g: Γ · brightVecPlus = -brightVecMinus.
        assert np.allclose(chiral_image_plus(t, delta),
                           -bright_vec_minus(t, delta), atol=1e-12)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
        (0.0, 1.0), (3.0, -2.0),
    ])
    def test_brightVecMinus_chiral_image(self, t, delta):
        # Lean W5g': Γ · brightVecMinus = -brightVecPlus.
        assert np.allclose(chiral_image_minus(t, delta),
                           -bright_vec_plus(t, delta), atol=1e-12)

    def test_chiral_op_squared_is_identity(self):
        # Consistency with Lean W2 T4 (Γ² = I).
        G = chiral_op()
        assert np.allclose(G @ G, np.eye(3))

    def test_chiral_twice_preserves_brightVecPlus(self):
        # Γ²·brightVecPlus = brightVecPlus (follows from W5g + W5g' + T4).
        for t, delta in [(1.0, 2.0), (0.7, -1.3), (-0.5, 2.5)]:
            vp = bright_vec_plus(t, delta)
            G = chiral_op()
            assert np.allclose(G @ (G @ vp), vp, atol=1e-12)

    def test_anti_unitary_TR_trivial_on_real_H(self):
        # Lean W5h paper-framing marker. On real-valued H, complex
        # conjugation acts as identity; the anti-unitary time-reversal
        # of BDI collapses to the identity action.
        for (t, delta, U) in PARAM_GRID:
            H = H_singlet(t, delta, U)
            # np.conj on a real array is identity.
            assert np.allclose(np.conj(H), H, atol=1e-12)

    def test_spectrum_exact_at_U0(self):
        # Lean W4p restated: spectrum_U0 should match eigvalsh exactly.
        for (t, delta, U) in PARAM_GRID:
            if abs(U) > 1e-12:
                continue  # skip U != 0 cases
            predicted = sorted(spectrum_U0(t, delta))
            actual = sorted(np.linalg.eigvalsh(H_singlet(t, delta, 0.0)))
            assert np.allclose(predicted, actual, atol=1e-10)


class TestChiralStrengthW5Round2:
    """Phase 5t W5 round-2 strengthening: chiral ker invariance, Γ
    nonzero preservation, multiset-level spectrum pairing, projector
    algebra, zero-mode uniqueness up to scalar.

    Each test mirrors a Lean theorem in ``FermiHubbardDimer.lean``
    Section 11."""

    # --- W5i: zero_mode_space_is_chiral_invariant ---

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
        (0.0, 1.0),
    ])
    def test_zero_mode_space_chiral_invariant_on_darkVec(self, t, delta):
        # Lean W5i: if H·v = 0, then H·(Γv) = 0. Test with v = darkVec.
        H = H_singlet(t, delta, 0.0)
        dv = dark_vec(t, delta)
        # Precondition:
        assert np.allclose(H @ dv, 0.0, atol=1e-12)
        # Corollary (W5i):
        assert np.allclose(H @ (chiral_op() @ dv), 0.0, atol=1e-12)

    def test_zero_mode_space_chiral_invariant_random_kernel(self):
        # Arbitrary v in ker(H) (random scalar multiple of darkVec).
        rng_local = np.random.default_rng(seed=800)
        for _ in range(15):
            t = rng_local.uniform(-3.0, 3.0)
            delta = rng_local.uniform(-3.0, 3.0)
            c = rng_local.uniform(-5.0, 5.0)
            dv = dark_vec(t, delta)
            v = c * dv  # arbitrary zero mode
            H = H_singlet(t, delta, 0.0)
            assert np.allclose(H @ v, 0.0, atol=1e-12)
            assert np.allclose(H @ (chiral_op() @ v), 0.0, atol=1e-12)

    # --- W5j: chiral_preserves_nonzero ---

    @pytest.mark.parametrize("v", [
        [1.0, 0.0, 0.0], [0.0, 1.0, 0.0], [0.0, 0.0, 1.0],
        [1.0, 1.0, 1.0], [1.3, -0.7, 2.0], [-0.5, 2.1, -3.1],
    ])
    def test_chiral_preserves_nonzero(self, v):
        # Lean W5j: v ≠ 0 ⟹ Γv ≠ 0.
        v_arr = np.array(v, dtype=float)
        assert np.linalg.norm(v_arr) > 0
        assert np.linalg.norm(chiral_op() @ v_arr) > 0

    def test_chiral_is_its_own_inverse(self):
        # Injectivity route: Γ(Γv) = v for all v (W2 T4 applied twice).
        rng_local = np.random.default_rng(seed=801)
        for _ in range(15):
            v = rng_local.uniform(-3.0, 3.0, size=3)
            G = chiral_op()
            assert np.allclose(G @ (G @ v), v)

    # --- W5k: multiset-level spectrum pairing ---

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
        (0.0, 1.0), (3.0, -2.0),
    ])
    def test_roots_multiset_symmetric_under_neg(self, t, delta):
        # Lean W5k: (charpoly.roots).map Neg.neg = charpoly.roots.
        # Python cross-check: the sorted roots list equals its sorted
        # negation (as a multiset).
        coeffs = (1.0, 0.0, -(delta**2 + 4.0 * t**2), 0.0)  # U=0 charpoly
        roots = sorted(np.roots(coeffs).real)
        neg_roots = sorted((-np.array(roots)).tolist())
        assert np.allclose(roots, neg_roots, atol=1e-10)

    # --- W5l/m: P±² = P± (idempotent projectors) ---

    def test_chiralProjPlus_idempotent(self):
        P = chiral_proj_plus()
        assert np.allclose(P @ P, P)

    def test_chiralProjMinus_idempotent(self):
        P = chiral_proj_minus()
        assert np.allclose(P @ P, P)

    # --- W5n/n': P+·P- = P-·P+ = 0 (orthogonal projectors) ---

    def test_chiralProjPlus_chiralProjMinus_orthogonal(self):
        Pplus = chiral_proj_plus()
        Pminus = chiral_proj_minus()
        assert np.allclose(Pplus @ Pminus, 0.0)
        assert np.allclose(Pminus @ Pplus, 0.0)

    # --- W5o: P+ + P- = 1 (complete projectors) ---

    def test_chiralProj_complete(self):
        Pplus = chiral_proj_plus()
        Pminus = chiral_proj_minus()
        assert np.allclose(Pplus + Pminus, np.eye(3))

    # --- W5o1/o2: Γ acts as ±1 on ±1 eigenspaces ---

    def test_chiralOp_acts_as_plus_one_on_Pplus_range(self):
        # Lean W5o1: Γ · P_+ = P_+.
        assert np.allclose(chiral_op() @ chiral_proj_plus(),
                           chiral_proj_plus())

    def test_chiralOp_acts_as_minus_one_on_Pminus_range(self):
        # Lean W5o2: Γ · P_- = -P_-.
        assert np.allclose(chiral_op() @ chiral_proj_minus(),
                           -chiral_proj_minus())

    def test_projectors_match_chiralOp_eigendecomposition(self):
        # Consistency: the eigenvalues of Γ are {+1, -1, -1}, and
        # the projectors onto the +1 / -1 eigenspaces match P_±.
        G = chiral_op()
        w, V = np.linalg.eigh(G)  # eigenvalues ascending
        # w ≈ [-1, -1, +1]; columns of V are eigenvectors.
        # Reconstruct P_+ = outer(v_+, v_+), where v_+ is the +1 eigenvec.
        # Assume +1 eigenvalue is last in ascending order.
        v_plus = V[:, 2].reshape(3, 1)
        P_plus_reconstructed = v_plus @ v_plus.T
        assert np.allclose(P_plus_reconstructed, chiral_proj_plus())

    # --- W5p: zero-mode uniqueness up to scalar ---

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
        (0.0, 1.0), (3.0, -2.0),
    ])
    def test_zero_mode_unique_up_to_scalar_via_nullspace_rank(self, t, delta):
        # Lean W5p: the kernel of H_singlet(t, Δ, 0) is 1-dim when
        # (t, Δ) ≠ (0, 0). Cross-check: numpy's null-space rank should
        # be 1 for H_singlet at U=0.
        H = H_singlet(t, delta, 0.0)
        U, sv, Vh = np.linalg.svd(H)
        # Number of singular values close to zero (= nullspace dim):
        null_dim = int(np.sum(sv < 1e-10))
        assert null_dim == 1

    def test_any_kernel_vector_is_darkvec_multiple(self):
        # Extract a nullspace basis vector via SVD, verify it's a scalar
        # multiple of darkVec (up to sign and normalization).
        rng_local = np.random.default_rng(seed=803)
        for _ in range(12):
            t = rng_local.uniform(-3.0, 3.0)
            delta = rng_local.uniform(-3.0, 3.0)
            if abs(t) < 1e-6 and abs(delta) < 1e-6:
                continue  # skip trivial
            H = H_singlet(t, delta, 0.0)
            U, sv, Vh = np.linalg.svd(H)
            # Last row of Vh is the null-space basis vector.
            v_null = Vh[-1]
            dv = dark_vec(t, delta)
            dv_normalized = dv / np.linalg.norm(dv)
            # v_null should be ±dv_normalized (up to sign).
            dot = np.abs(np.dot(v_null, dv_normalized))
            assert np.isclose(dot, 1.0, atol=1e-10)

    def test_explicit_kernel_span_darkvec(self):
        # Construct a random scalar multiple c·darkVec, apply H, verify 0.
        # Then apply W5p conceptually: any such kernel vector IS a scalar
        # multiple of darkVec (the decomposition exists).
        rng_local = np.random.default_rng(seed=804)
        for _ in range(10):
            t = rng_local.uniform(-3.0, 3.0)
            delta = rng_local.uniform(-3.0, 3.0)
            if abs(t) < 1e-6 and abs(delta) < 1e-6:
                continue
            c = rng_local.uniform(-5.0, 5.0)
            dv = dark_vec(t, delta)
            v = c * dv
            # Sanity: in kernel
            assert np.allclose(H_singlet(t, delta, 0.0) @ v, 0.0,
                               atol=1e-12)
            # W5p: v should recover the scalar (up to sign / normalization).
            # Since v = c·dv, the ratio v[2]/dv[2] = c when Δ ≠ 0
            if abs(delta) > 1e-6:
                assert np.isclose(v[2] / dv[2], c, atol=1e-10)


class TestNormalizedEigenvectorsW6A:
    """Phase 5t W6A: EuclideanSpace-typed normalized eigenvectors."""

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
        (0.0, 1.0), (3.0, -2.0),
    ])
    def test_dark_vec_norm_unit(self, t, delta):
        # Lean W6A-U1: ‖darkVecNorm‖ = 1.
        assert np.isclose(np.linalg.norm(dark_vec_norm(t, delta)), 1.0)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
    ])
    def test_bright_vec_plus_norm_unit(self, t, delta):
        # Lean W6A-U2.
        assert np.isclose(np.linalg.norm(bright_vec_plus_norm(t, delta)),
                          1.0)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
    ])
    def test_bright_vec_minus_norm_unit(self, t, delta):
        # Lean W6A-U3.
        assert np.isclose(np.linalg.norm(bright_vec_minus_norm(t, delta)),
                          1.0)

    def test_orthonormal_triple(self):
        # Lean W6A-O1: the three normalized eigenvectors form an
        # orthonormal family.
        rng_local = np.random.default_rng(seed=600)
        for _ in range(15):
            t = rng_local.uniform(-3.0, 3.0)
            delta = rng_local.uniform(-3.0, 3.0)
            if abs(t) < 1e-6 and abs(delta) < 1e-6:
                continue
            dn = dark_vec_norm(t, delta)
            bpn = bright_vec_plus_norm(t, delta)
            bmn = bright_vec_minus_norm(t, delta)
            # All unit norm
            assert np.isclose(np.linalg.norm(dn), 1.0)
            assert np.isclose(np.linalg.norm(bpn), 1.0)
            assert np.isclose(np.linalg.norm(bmn), 1.0)
            # Pairwise orthogonal
            assert np.isclose(np.dot(dn, bpn), 0.0, atol=1e-12)
            assert np.isclose(np.dot(dn, bmn), 0.0, atol=1e-12)
            assert np.isclose(np.dot(bpn, bmn), 0.0, atol=1e-12)

    def test_eigenvector_matrix_is_orthogonal(self):
        # Lean W6B-U1/U2: the matrix with columns (or rows) the three
        # normalized eigenvectors is orthogonal (unitary for real case).
        rng_local = np.random.default_rng(seed=601)
        for _ in range(15):
            t = rng_local.uniform(-3.0, 3.0)
            delta = rng_local.uniform(-3.0, 3.0)
            if abs(t) < 1e-6 and abs(delta) < 1e-6:
                continue
            dn = dark_vec_norm(t, delta)
            bpn = bright_vec_plus_norm(t, delta)
            bmn = bright_vec_minus_norm(t, delta)
            M = np.column_stack([dn, bpn, bmn])
            assert np.allclose(M @ M.T, np.eye(3), atol=1e-12)
            assert np.allclose(M.T @ M, np.eye(3), atol=1e-12)


class TestGeometricSWAPW6C:
    """Phase 5t W6C: geometric SWAP operator + action on eigenvectors."""

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
        (0.0, 1.0), (3.0, -2.0),
    ])
    def test_U_SWAP_darkVec_sign_flip(self, t, delta):
        # Lean W6C-A1: U_SWAP · darkVec = -darkVec.
        U = u_swap_singlet(t, delta)
        dv = np.array([0.0, 2*t, delta])
        assert np.allclose(U @ dv, -dv, atol=1e-12)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
        (0.0, 1.0), (3.0, -2.0),
    ])
    def test_U_SWAP_brightVecPlus_identity(self, t, delta):
        # Lean W6C-A2: U_SWAP · brightVecPlus = brightVecPlus.
        U = u_swap_singlet(t, delta)
        g = np.sqrt(delta**2 + 4*t**2)
        vp = np.array([g, delta, -2*t])
        assert np.allclose(U @ vp, vp, atol=1e-12)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
        (0.0, 1.0), (3.0, -2.0),
    ])
    def test_U_SWAP_brightVecMinus_identity(self, t, delta):
        # Lean W6C-A3.
        U = u_swap_singlet(t, delta)
        g = np.sqrt(delta**2 + 4*t**2)
        vm = np.array([-g, delta, -2*t])
        assert np.allclose(U @ vm, vm, atol=1e-12)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
    ])
    def test_U_SWAP_symmetric(self, t, delta):
        # Lean W6C-S1.
        U = u_swap_singlet(t, delta)
        assert np.allclose(U.T, U, atol=1e-12)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
    ])
    def test_U_SWAP_involution(self, t, delta):
        # Lean W6C-S2: U · U = I.
        U = u_swap_singlet(t, delta)
        assert np.allclose(U @ U, np.eye(3), atol=1e-12)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
    ])
    def test_U_SWAP_orthogonal(self, t, delta):
        # Lean W6C-S3: U · Uᵀ = I (unitarity in real case).
        U = u_swap_singlet(t, delta)
        assert np.allclose(U @ U.T, np.eye(3), atol=1e-12)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
    ])
    def test_U_SWAP_det_minus_one(self, t, delta):
        # Lean W6C-D1: det U = -1.
        U = u_swap_singlet(t, delta)
        assert np.isclose(np.linalg.det(U), -1.0, atol=1e-10)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
    ])
    def test_U_SWAP_trace_one(self, t, delta):
        # Lean W6C-T1: tr U = +1.
        U = u_swap_singlet(t, delta)
        assert np.isclose(np.trace(U), 1.0, atol=1e-10)

    def test_U_SWAP_eigenvalues_random(self):
        # Eigenvalues are {-1, +1, +1}: one -1 and two +1s.
        rng_local = np.random.default_rng(seed=700)
        for _ in range(15):
            t = rng_local.uniform(-3.0, 3.0)
            delta = rng_local.uniform(-3.0, 3.0)
            if abs(t) < 1e-6 and abs(delta) < 1e-6:
                continue
            U = u_swap_singlet(t, delta)
            eigs = sorted(np.linalg.eigvalsh(U + np.zeros((3,3))))
            # eigs are real since U is symmetric
            expected = sorted([-1.0, 1.0, 1.0])
            assert np.allclose(eigs, expected, atol=1e-10)

    def test_U_SWAP_reflection_identity(self):
        # Householder: U = I - 2 · P_darkNorm where P = |d⟩⟨d|
        rng_local = np.random.default_rng(seed=701)
        for _ in range(10):
            t = rng_local.uniform(-3.0, 3.0)
            delta = rng_local.uniform(-3.0, 3.0)
            if abs(t) < 1e-6 and abs(delta) < 1e-6:
                continue
            dn = dark_vec_norm(t, delta)
            P = np.outer(dn, dn)
            U_direct = u_swap_singlet(t, delta)
            U_reconstructed = np.eye(3) - 2 * P
            assert np.allclose(U_direct, U_reconstructed, atol=1e-12)


class TestGeometricSWAPW6Round2:
    """Phase 5t W6 round-2 strengthening: scalar-multiple eigenvector
    actions (W6C-A1s/A2s/A3s), unitary-group membership (W6C-U1), and
    kernel action (W6C-K1).

    These cross-check the Lean theorems that generalize W6C-A1/A2/A3
    from explicit eigenvectors to scalar multiples, and combine W5p
    zero-mode uniqueness with the sign-flip to give the strongest
    kernel-action statement.
    """

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
        (0.0, 1.0), (3.0, -2.0),
    ])
    def test_U_SWAP_smul_darkVec(self, t, delta):
        # Lean W6C-A1s: U · (c • darkVec) = -(c • darkVec) for any c.
        U = u_swap_singlet(t, delta)
        dv = np.array([0.0, 2*t, delta])
        rng_local = np.random.default_rng(seed=710)
        for _ in range(5):
            c = rng_local.uniform(-5.0, 5.0)
            v = c * dv
            assert np.allclose(U @ v, -v, atol=1e-12)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
        (0.0, 1.0), (3.0, -2.0),
    ])
    def test_U_SWAP_smul_brightVecPlus(self, t, delta):
        # Lean W6C-A2s: U · (c • brightVecPlus) = c • brightVecPlus.
        U = u_swap_singlet(t, delta)
        g = np.sqrt(delta**2 + 4*t**2)
        vp = np.array([g, delta, -2*t])
        rng_local = np.random.default_rng(seed=711)
        for _ in range(5):
            c = rng_local.uniform(-5.0, 5.0)
            v = c * vp
            assert np.allclose(U @ v, v, atol=1e-12)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
        (0.0, 1.0), (3.0, -2.0),
    ])
    def test_U_SWAP_smul_brightVecMinus(self, t, delta):
        # Lean W6C-A3s.
        U = u_swap_singlet(t, delta)
        g = np.sqrt(delta**2 + 4*t**2)
        vm = np.array([-g, delta, -2*t])
        rng_local = np.random.default_rng(seed=712)
        for _ in range(5):
            c = rng_local.uniform(-5.0, 5.0)
            v = c * vm
            assert np.allclose(U @ v, v, atol=1e-12)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
    ])
    def test_U_SWAP_mem_unitaryGroup_transpose_identity(self, t, delta):
        # Lean W6C-U1 unpacks to the orthogonality identity Uᵀ · U = I
        # over ℝ (TrivialStar makes conjTranspose = transpose).
        U = u_swap_singlet(t, delta)
        assert np.allclose(U.T @ U, np.eye(3), atol=1e-12)

    def test_U_SWAP_on_kernel_random_scalars(self):
        # Lean W6C-K1: for any v with H · v = 0, U · v = -v. Here we
        # sample v = c · darkVec (which spans ker(H) by W5p) for random c.
        rng_local = np.random.default_rng(seed=713)
        for _ in range(20):
            t = rng_local.uniform(-3.0, 3.0)
            delta = rng_local.uniform(-3.0, 3.0)
            if abs(t) < 1e-6 and abs(delta) < 1e-6:
                continue
            c = rng_local.uniform(-5.0, 5.0)
            H = H_singlet(t, delta, 0.0)
            dv = np.array([0.0, 2*t, delta])
            v = c * dv
            # Cross-check: v is truly in the kernel
            assert np.allclose(H @ v, 0.0, atol=1e-12)
            # W6C-K1 claim
            result = u_swap_action_on_kernel(t, delta, v)
            assert np.allclose(result, -v, atol=1e-12)

    def test_U_SWAP_on_kernel_via_nullspace_projection(self):
        # Stronger cross-check: extract the true kernel via SVD, verify
        # SWAP acts as -1 on every vector in that kernel. This is the
        # W6C-K1 statement without relying on the explicit darkVec form.
        rng_local = np.random.default_rng(seed=714)
        for _ in range(10):
            t = rng_local.uniform(-3.0, 3.0)
            delta = rng_local.uniform(-3.0, 3.0)
            if abs(t) < 1e-6 and abs(delta) < 1e-6:
                continue
            H = H_singlet(t, delta, 0.0)
            U = u_swap_singlet(t, delta)
            # SVD kernel extraction: singular values near zero identify
            # the nullspace direction
            _, s, Vh = np.linalg.svd(H)
            # kernel is the right singular vector with smallest sv
            kernel_dir = Vh[-1]  # smallest sv is last
            # Make sure this is truly in the kernel
            assert s[-1] < 1e-10
            assert np.allclose(H @ kernel_dir, 0.0, atol=1e-10)
            # U_SWAP acts as -1 on it
            assert np.allclose(U @ kernel_dir, -kernel_dir, atol=1e-10)

    def test_U_SWAP_unitary_determinant_product(self):
        # Sanity: W6C-U1 membership implies |det U| = 1. Since det U = -1
        # (W6C-D1), the member is in the unitary group but NOT SO(3) —
        # it's a reflection, not a rotation.
        rng_local = np.random.default_rng(seed=715)
        for _ in range(10):
            t = rng_local.uniform(-3.0, 3.0)
            delta = rng_local.uniform(-3.0, 3.0)
            if abs(t) < 1e-6 and abs(delta) < 1e-6:
                continue
            U = u_swap_singlet(t, delta)
            # Unitary: |det| = 1
            assert np.isclose(abs(np.linalg.det(U)), 1.0, atol=1e-10)
            # Reflection, not rotation: det = -1
            assert np.isclose(np.linalg.det(U), -1.0, atol=1e-10)


class TestDirectExchangeSuperexchangeW7:
    """Phase 5t W7: direct-exchange vs superexchange scaling.

    Tests the Lean W7 real-analysis theorems characterising the upper
    eigenvalue ``E_plus(t, U) = (U + sqrt(U² + 16·t²))/2`` of the
    2×2 symmetric sector of the Fermi-Hubbard dimer at zero detuning.
    """

    # --- W7a: direct-exchange value at U = 0 ---

    @pytest.mark.parametrize("t", [0.0, 0.5, 1.0, 2.0, -1.0, -2.5, 3.7])
    def test_E_plus_value_at_zero(self, t):
        # Lean W7a: E_plus(t, 0) = 2·|t|.
        assert np.isclose(E_plus(t, 0.0), 2.0 * abs(t), atol=1e-12)

    @pytest.mark.parametrize("t", [0.5, 1.0, 2.0, -1.5, 3.0])
    def test_J_superexchange_at_zero(self, t):
        # Lean W7g: J(t, 0) = 2·|t|.
        assert np.isclose(J_superexchange(t, 0.0), 2.0 * abs(t), atol=1e-12)

    # --- W7b/c: Vieta identities ---

    @pytest.mark.parametrize("t, U", [
        (0.0, 0.0), (1.0, 0.0), (0.0, 1.0), (1.0, 2.0),
        (0.5, -1.0), (-2.0, 3.0), (1.5, -0.7), (3.0, 10.0),
    ])
    def test_vieta_trace(self, t, U):
        # Lean W7b: E_plus + E_minus = U.
        assert np.isclose(E_plus(t, U) + E_minus(t, U), U, atol=1e-12)

    @pytest.mark.parametrize("t, U", [
        (0.0, 0.0), (1.0, 0.0), (0.0, 1.0), (1.0, 2.0),
        (0.5, -1.0), (-2.0, 3.0), (1.5, -0.7), (3.0, 10.0),
    ])
    def test_vieta_product(self, t, U):
        # Lean W7c: E_plus · E_minus = -4·t².
        assert np.isclose(E_plus(t, U) * E_minus(t, U), -4.0 * t**2, atol=1e-10)

    # --- W7d: derivative at U = 0 is 1/2 ---

    @pytest.mark.parametrize("t", [0.5, 1.0, 2.0, -1.5, 3.0, -0.7])
    def test_E_plus_deriv_at_zero(self, t):
        # Lean W7d: (d/dU) E_plus(t, U) at U=0 is 1/2, for t ≠ 0.
        # Numerical derivative via central differences.
        h = 1e-6
        deriv = (E_plus(t, h) - E_plus(t, -h)) / (2.0 * h)
        assert np.isclose(deriv, 0.5, atol=1e-8)

    # --- W7e: sqrt lower bound ---

    @pytest.mark.parametrize("t, U", [
        (0.5, 0.0), (1.0, 2.0), (2.0, 1.0), (-1.5, -3.0), (0.3, 0.0),
    ])
    def test_sqrt_lower_bound_abs_t(self, t, U):
        # Lean W7e: sqrt(U² + 16·t²) ≥ 4·|t|.
        lhs = 4.0 * abs(t)
        rhs = float(np.sqrt(U**2 + 16.0 * t**2))
        assert lhs <= rhs + 1e-12

    # --- W7f: monotonicity on U ≥ 0 ---

    @pytest.mark.parametrize("t", [0.0, 0.5, 1.0, -1.5, 2.0])
    def test_E_plus_monotone_nonneg(self, t):
        # Lean W7f: E_plus is monotone non-decreasing in U on U ≥ 0.
        Us = np.linspace(0.0, 10.0, 50)
        values = [E_plus(t, U) for U in Us]
        # Every consecutive pair must be non-decreasing
        for i in range(len(values) - 1):
            assert values[i] <= values[i + 1] + 1e-12

    # --- W7h: √(1+x) ≤ 1 + x/2 for x ≥ 0 ---

    @pytest.mark.parametrize("x", [0.0, 0.1, 0.5, 1.0, 2.0, 5.0, 100.0])
    def test_sqrt_one_add_le(self, x):
        # Lean W7h: √(1+x) ≤ 1 + x/2 for x ≥ 0.
        assert float(np.sqrt(1.0 + x)) <= 1.0 + x / 2.0 + 1e-12

    # --- W7i: superexchange approximation bound ---

    @pytest.mark.parametrize("t, U_factor", [
        (1.0, 1.0), (1.0, 2.0), (0.5, 3.0), (-1.5, 5.0), (2.0, 10.0),
        (0.7, 1.5), (-0.3, 20.0),
    ])
    def test_J_superexchange_bound(self, t, U_factor):
        # Lean W7i: for U ≥ 4|t|, t ≠ 0, |J(t,U) - 4t²/U| ≤ 16t⁴/U³.
        U = 4.0 * abs(t) * U_factor  # ensures U ≥ 4|t| > 0
        if U == 0.0:
            pytest.skip("trivial case")
        J_actual = J_superexchange(t, U)
        J_leading = J_leading_superexchange(t, U)
        bound = 16.0 * t**4 / U**3
        err = abs(J_actual - J_leading)
        assert err <= bound + 1e-12, f"err={err}, bound={bound}, (t,U)={(t,U)}"

    def test_J_superexchange_bound_asymptotic_tightness(self):
        # Numerical: at U = 4|t|, the bound is close to tight — the
        # leading-order correction is ~ 16·t⁴/U³, i.e., the bound is
        # asymptotically sharp up to a multiplicative constant.
        # At larger U/t, the bound loosens further.
        rng_local = np.random.default_rng(seed=720)
        for _ in range(15):
            t = rng_local.uniform(0.3, 3.0)
            U = 4.0 * t * rng_local.uniform(1.0, 50.0)
            err = abs(J_superexchange(t, U) - J_leading_superexchange(t, U))
            bound = 16.0 * t**4 / U**3
            assert err <= bound + 1e-12
            # For strict inequality check (no trivial zero): err > 0 unless t == 0
            if t != 0:
                # Err should be strictly positive (leading term isn't exact)
                assert err > 0

    # --- Scaling signature tests ---

    def test_direct_exchange_scales_linear_in_U(self):
        # At U = 0, the Taylor expansion E_plus(t, U) ≈ 2|t| + U/2 holds.
        # So E_plus(t, U) - 2|t| ≈ U/2 for small U.
        for t in [0.5, 1.0, 2.0, -1.5]:
            for U in [1e-4, 1e-3, 1e-2]:
                expected = 2.0 * abs(t) + U / 2.0
                # Error should be O(U²/|t|)
                tol = U**2 / abs(t) * 2.0
                assert abs(E_plus(t, U) - expected) <= tol + 1e-14

    def test_superexchange_scales_quadratic_in_t_inverse_in_U(self):
        # At large U, J(t, U) ≈ 4·t²/U. The ratio J/(4t²/U) should → 1.
        t = 1.0
        ratios = []
        for U in [50.0, 500.0, 5000.0]:
            ratios.append(J_superexchange(t, U) / J_leading_superexchange(t, U))
        # The ratios should increase toward 1 as U → ∞
        for r in ratios:
            assert 0.9 < r < 1.0 + 1e-10  # below 1 since J < 4t²/U for U > 0
        # Each successive U should give a ratio closer to 1 (monotone convergence)
        for i in range(len(ratios) - 1):
            assert ratios[i] < ratios[i + 1] + 1e-10


class TestW7Round2Strengthening:
    """Phase 5t W7 round-2: matrix bridge + Lipschitz strengthening.

    Cross-checks Lean W7j-W7q: characteristic equations, charpoly
    factorization at Δ=0, explicit eigenvectors (E_plus, E_minus,
    antisymmetric doublon U), E_minus value at zero, and the global
    1-Lipschitz bound for E_plus.
    """

    # --- W7j/k: characteristic equations ---

    @pytest.mark.parametrize("t, U", [
        (0.0, 0.0), (0.5, 0.0), (0.0, 1.0), (1.0, 2.0),
        (0.5, -1.0), (-2.0, 3.0), (1.5, -0.7), (3.0, 10.0),
        (0.3, -5.0), (2.5, 7.5),
    ])
    def test_E_plus_char_eq(self, t, U):
        # Lean W7j: E_plus² - U·E_plus - 4·t² = 0.
        assert abs(E_plus_char_residual(t, U)) < 1e-10

    @pytest.mark.parametrize("t, U", [
        (0.0, 0.0), (0.5, 0.0), (0.0, 1.0), (1.0, 2.0),
        (0.5, -1.0), (-2.0, 3.0), (1.5, -0.7), (3.0, 10.0),
        (0.3, -5.0), (2.5, 7.5),
    ])
    def test_E_minus_char_eq(self, t, U):
        # Lean W7k: E_minus² - U·E_minus - 4·t² = 0.
        assert abs(E_minus_char_residual(t, U)) < 1e-10

    # --- W7l: charpoly factorization at Δ=0 ---

    @pytest.mark.parametrize("t, U", [
        (0.5, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
        (1.5, 3.5), (-1.0, -2.0),
    ])
    def test_charpoly_Delta0_factored_roots(self, t, U):
        # Lean W7l: at Δ=0, charpoly(H) factors as (X-U)(X²-UX-4t²).
        # Numerical check: roots of charpoly (eigenvalues of H) are
        # {U, E_plus(t, U), E_minus(t, U)}.
        H = H_singlet(t, 0.0, U)
        eigs = sorted(np.linalg.eigvalsh(H))
        expected = sorted([U, E_plus(t, U), E_minus(t, U)])
        assert np.allclose(eigs, expected, atol=1e-10)

    # --- W7m/n: E_plus, E_minus eigenvectors ---

    @pytest.mark.parametrize("t, U", [
        (0.5, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
        (1.5, 3.5), (-1.0, -2.0),
    ])
    def test_E_plus_eigenvector(self, t, U):
        # Lean W7m: H · [E_plus, 0, -2t] = E_plus · [E_plus, 0, -2t].
        H = H_singlet(t, 0.0, U)
        v = E_plus_eigenvector(t, U)
        Hv = H @ v
        expected = E_plus(t, U) * v
        assert np.allclose(Hv, expected, atol=1e-10)

    @pytest.mark.parametrize("t, U", [
        (0.5, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
        (1.5, 3.5), (-1.0, -2.0),
    ])
    def test_E_minus_eigenvector(self, t, U):
        # Lean W7n.
        H = H_singlet(t, 0.0, U)
        v = E_minus_eigenvector(t, U)
        Hv = H @ v
        expected = E_minus(t, U) * v
        assert np.allclose(Hv, expected, atol=1e-10)

    # --- W7o: antisymmetric doublon eigenvector at eigenvalue U ---

    @pytest.mark.parametrize("t, U", [
        (0.0, 0.0), (0.5, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0),
        (-0.5, 2.5), (1.5, 3.5), (3.0, -10.0),
    ])
    def test_antisymmetric_doublon_eigenvector(self, t, U):
        # Lean W7o: H · [0, 1, 0] = U · [0, 1, 0] at Δ=0.
        H = H_singlet(t, 0.0, U)
        v = antisymmetric_doublon_vec()
        Hv = H @ v
        expected = U * v
        assert np.allclose(Hv, expected, atol=1e-12)

    # --- W7p: E_minus at U=0 is -2|t| ---

    @pytest.mark.parametrize("t", [0.0, 0.5, 1.0, 2.0, -1.0, -2.5, 3.7])
    def test_E_minus_value_at_zero(self, t):
        # Lean W7p: E_minus(t, 0) = -2·|t|.
        assert np.isclose(E_minus(t, 0.0), -2.0 * abs(t), atol=1e-12)

    # --- W7q: global 1-Lipschitz bound for E_plus ---

    @pytest.mark.parametrize("t", [0.0, 0.5, 1.0, -1.5, 2.0, -3.0])
    def test_E_plus_lipschitz_grid(self, t):
        # Lean W7q: |E_plus(t, U₁) - E_plus(t, U₂)| ≤ |U₁ - U₂|.
        Us = np.linspace(-10.0, 10.0, 30)
        for i in range(len(Us)):
            for j in range(i + 1, len(Us)):
                U1, U2 = Us[i], Us[j]
                lhs = abs(E_plus(t, U1) - E_plus(t, U2))
                rhs = abs(U1 - U2)
                assert lhs <= rhs + 1e-12

    def test_E_plus_lipschitz_random(self):
        # Random sampling: Lipschitz bound holds for any (t, U₁, U₂).
        rng_local = np.random.default_rng(seed=730)
        for _ in range(50):
            t = rng_local.uniform(-5.0, 5.0)
            U1 = rng_local.uniform(-20.0, 20.0)
            U2 = rng_local.uniform(-20.0, 20.0)
            lhs = abs(E_plus(t, U1) - E_plus(t, U2))
            rhs = abs(U1 - U2)
            assert lhs <= rhs + 1e-12

    def test_E_plus_lipschitz_tight_in_limit(self):
        # The bound is tight in the large-U limit (E_plus ≈ U, so
        # |E_plus(U₁) - E_plus(U₂)| → |U₁ - U₂|).
        t = 1.0
        U1, U2 = 1000.0, 1100.0
        lhs = abs(E_plus(t, U1) - E_plus(t, U2))
        rhs = abs(U1 - U2)
        # At large U, E_plus(U) ≈ U + 2t²/U, so difference ≈ |U₁ - U₂|
        # with small correction.
        assert 0.99 < lhs / rhs <= 1.0 + 1e-10

    # --- Vieta + char eq cross-checks ---

    @pytest.mark.parametrize("t, U", [
        (0.5, 0.0), (1.0, 2.0), (-0.7, 3.1), (2.0, -1.5),
    ])
    def test_eigenvectors_span_H_singlet(self, t, U):
        # All three eigenvectors [U, E_plus, E_minus] together span ℝ³
        # and reconstruct H_singlet(t, 0, U). Verified by showing
        # determinant of the matrix they form is nonzero (so linearly
        # independent for generic (t, U)).
        v_antisym = antisymmetric_doublon_vec()
        v_plus = E_plus_eigenvector(t, U)
        v_minus = E_minus_eigenvector(t, U)
        M = np.column_stack([v_antisym, v_plus, v_minus])
        # Linearly independent iff det ≠ 0.
        if abs(t) > 1e-6:  # skip degenerate t = 0 where E_plus = E_minus = 0
            assert abs(np.linalg.det(M)) > 1e-8


class TestW6Deferred6x6Lift:
    """Phase 5t W6-deferred: 6×6 block-diagonal lift of U_SWAP_singlet
    to the symmetry-adapted basis (singlet ⊕ triplet).

    Tests Lean W6D-S1/S2/S3/U1/A1/A2: unitarity properties of
    ``u_swap_adapted``, and block-structure preservation (singlet
    block inherits U_SWAP_singlet action; triplet block is identity).
    """

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
        (0.3, -1.0),
    ])
    def test_U_SWAP_adapted_symmetric(self, t, delta):
        # Lean W6D-S1: (U_SWAP_adapted)ᵀ = U_SWAP_adapted.
        U = u_swap_adapted(t, delta)
        assert np.allclose(U.T, U, atol=1e-12)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
        (0.3, -1.0),
    ])
    def test_U_SWAP_adapted_involution(self, t, delta):
        # Lean W6D-S2: U · U = I (6×6).
        U = u_swap_adapted(t, delta)
        assert np.allclose(U @ U, np.eye(6), atol=1e-12)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
        (0.3, -1.0),
    ])
    def test_U_SWAP_adapted_orthogonal(self, t, delta):
        # Lean W6D-S3: U · Uᵀ = I (unitarity witness in 6×6).
        U = u_swap_adapted(t, delta)
        assert np.allclose(U @ U.T, np.eye(6), atol=1e-12)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
    ])
    def test_U_SWAP_adapted_on_inl_matches_singlet(self, t, delta):
        # Lean W6D-A1: for any singlet-embedded v, U_SWAP_adapted · (v, 0) =
        # (U_SWAP_singlet · v, 0).
        rng_local = np.random.default_rng(seed=740)
        for _ in range(5):
            v = rng_local.uniform(-3.0, 3.0, size=3)
            v_embedded = np.concatenate([v, np.zeros(3)])
            U6 = u_swap_adapted(t, delta)
            U3 = u_swap_singlet(t, delta)
            expected = np.concatenate([U3 @ v, np.zeros(3)])
            assert np.allclose(U6 @ v_embedded, expected, atol=1e-12)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
    ])
    def test_U_SWAP_adapted_on_inr_is_identity(self, t, delta):
        # Lean W6D-A2: for any triplet-embedded w, U_SWAP_adapted · (0, w) = (0, w).
        rng_local = np.random.default_rng(seed=741)
        for _ in range(5):
            w = rng_local.uniform(-3.0, 3.0, size=3)
            w_embedded = np.concatenate([np.zeros(3), w])
            U6 = u_swap_adapted(t, delta)
            assert np.allclose(U6 @ w_embedded, w_embedded, atol=1e-12)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
    ])
    def test_U_SWAP_adapted_eigenvalues(self, t, delta):
        # Expected eigenvalues: {-1, +1, +1} (from singlet) + {+1, +1, +1}
        # (from triplet identity) = {-1, +1, +1, +1, +1, +1}.
        U6 = u_swap_adapted(t, delta)
        eigs = sorted(np.linalg.eigvalsh(U6))
        expected = sorted([-1.0, 1.0, 1.0, 1.0, 1.0, 1.0])
        assert np.allclose(eigs, expected, atol=1e-10)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
    ])
    def test_U_SWAP_adapted_det_minus_one(self, t, delta):
        # Det = (det U_SWAP_singlet) · (det I) = (-1) · 1 = -1.
        U6 = u_swap_adapted(t, delta)
        assert np.isclose(np.linalg.det(U6), -1.0, atol=1e-10)

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
    ])
    def test_U_SWAP_adapted_trace(self, t, delta):
        # Trace = tr(U_SWAP_singlet) + tr(I₃) = 1 + 3 = 4.
        U6 = u_swap_adapted(t, delta)
        assert np.isclose(np.trace(U6), 4.0, atol=1e-10)


class TestGeometricPhaseW8:
    """Phase 5t W8 Target A: minimal geometric-phase theorem.

    Cross-checks Lean W8a/b/c/d/e — the θ-parameterized dark state
    sign-flip under π-shift (Berry phase), 2π periodicity,
    normalization, and dynamical-phase vanishing.
    """

    @pytest.mark.parametrize("theta", [
        0.0, 0.1, np.pi / 4, np.pi / 2, 1.0, 2.5, -0.3, -np.pi, 10.0,
    ])
    def test_darkStateθ_add_pi_sign_flip(self, theta):
        # Lean W8a: darkStateθ(θ + π) = -darkStateθ(θ).
        start = dark_state_theta_norm(theta)
        after_pi = dark_state_theta_norm(theta + np.pi)
        assert np.allclose(after_pi, -start, atol=1e-12)

    @pytest.mark.parametrize("theta", [
        0.0, 0.1, np.pi / 4, np.pi / 2, 1.0, 2.5, -0.3, -np.pi, 10.0,
    ])
    def test_darkStateθ_add_two_pi(self, theta):
        # Lean W8b: darkStateθ(θ + 2π) = darkStateθ(θ).
        start = dark_state_theta_norm(theta)
        after_2pi = dark_state_theta_norm(theta + 2.0 * np.pi)
        assert np.allclose(after_2pi, start, atol=1e-12)

    @pytest.mark.parametrize("theta", [
        0.0, 0.1, np.pi / 4, np.pi / 2, 1.0, 2.5, -0.3, -np.pi, 10.0,
    ])
    def test_darkStateθ_dotProduct_self(self, theta):
        # Lean W8c: dot(darkStateθ θ, darkStateθ θ) = sin²(θ) + cos²(θ) = 1.
        v = dark_state_theta_norm(theta)
        assert np.isclose(np.dot(v, v), 1.0, atol=1e-12)

    @pytest.mark.parametrize("theta", [
        0.0, 0.1, np.pi / 4, np.pi / 2, 1.0, 2.5, -np.pi / 3,
    ])
    def test_darkStateθ_in_kernel_under_angle_condition(self, theta):
        # Lean W4a cross-check: darkStateθ(θ) ∈ ker(H) under the angle
        # condition Δ·sin(θ) = 2t·cos(θ). Construct (t, Δ) from θ so
        # the condition holds automatically (take t = sin(θ)/2, Δ = cos(θ)).
        t = np.sin(theta) / 2.0
        delta = np.cos(theta)
        H = H_singlet(t, delta, 0.0)
        v = dark_state_theta_norm(theta)
        Hv = H @ v
        assert np.allclose(Hv, 0.0, atol=1e-12)

    @pytest.mark.parametrize("theta", [
        0.1, np.pi / 4, np.pi / 2, 1.0, 2.5, -np.pi / 3,
    ])
    def test_dynamical_phase_vanishes(self, theta):
        # Lean W8d: ⟨darkStateθ, H · darkStateθ⟩ = 0 under angle condition.
        t = np.sin(theta) / 2.0
        delta = np.cos(theta)
        H = H_singlet(t, delta, 0.0)
        v = dark_state_theta_norm(theta)
        expectation = float(v @ (H @ v))
        assert np.isclose(expectation, 0.0, atol=1e-12)

    def test_geometric_phase_loop_check_bundled(self):
        # Lean W8e bundled: sign flip + zero dynamical phase.
        rng_local = np.random.default_rng(seed=750)
        for _ in range(20):
            theta = rng_local.uniform(-10.0, 10.0)
            witness = geometric_phase_loop_check(theta)
            assert witness["sign_flip_err"] < 1e-12
            assert witness["periodicity_err"] < 1e-12
            assert witness["unit_norm_err"] < 1e-12

    def test_geometric_phase_berry_via_two_pi_sweeps(self):
        # Two π-sweeps = one 2π-sweep = identity (sign flip squared).
        # This is the "Berry phase squared = 1" sanity check.
        rng_local = np.random.default_rng(seed=751)
        for _ in range(10):
            theta = rng_local.uniform(-5.0, 5.0)
            v_start = dark_state_theta_norm(theta)
            v_after_first_pi = dark_state_theta_norm(theta + np.pi)
            v_after_second_pi = dark_state_theta_norm(theta + 2.0 * np.pi)
            # First π: sign flip.
            assert np.allclose(v_after_first_pi, -v_start, atol=1e-12)
            # Second π (total 2π): back to start.
            assert np.allclose(v_after_second_pi, v_start, atol=1e-12)
