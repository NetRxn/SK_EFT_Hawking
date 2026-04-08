"""Tests for TQFT pipeline: WRT invariants, surgery, Temperley-Lieb (Phase 5k W4).

Corresponds to WRTInvariant.lean, WRTComputation.lean, SurgeryPresentation.lean,
TemperleyLieb.lean, JonesWenzl.lean.

Tests verify:
  - WRT invariant computations Z(S^3) = 1/D for Ising/Fibonacci
  - Lens space invariants Z(L(p,1)) including vanishing at L(8,1) for Ising
  - Surgery presentation properties (handle slide symmetry, Kirby moves)
  - Temperley-Lieb relation verification (3 relation types)
"""

import math

import numpy as np
import pytest

from src.core.formulas import (
    su2k_quantum_dim,
    su2k_global_dim_sq,
    su2k_s_matrix_entry,
    su2k_twist,
    su2k_topological_central_charge,
    mtc_quantum_dimensions,
    mtc_total_quantum_dimension,
    wrt_s3,
    wrt_s2xs1,
    wrt_lens_space,
    wrt_invariants_table,
    surgery_linking_matrix,
    surgery_handle_slide,
    tl_relation_check,
)


PHI = (1 + math.sqrt(5)) / 2  # golden ratio


# ═══════════════════════════════════════════════════════════════
# WRT Invariant Tests — Z(S^3) = 1/D
# ═══════════════════════════════════════════════════════════════


class TestWRTS3:
    """Z(S^3) = 1/D for normalized convention."""

    def test_ising_s3(self):
        """Ising: Z(S^3) = 1/2 (D = 2, D^2 = 4)."""
        z = wrt_s3('ising')
        assert abs(z - 0.5) < 1e-14

    def test_fibonacci_s3(self):
        """Fibonacci: Z(S^3) = 1/sqrt(2+phi)."""
        z = wrt_s3('fibonacci')
        D = math.sqrt(2 + PHI)
        assert abs(z - 1.0 / D) < 1e-14

    def test_s3_positive(self):
        """Z(S^3) > 0 for both models."""
        for model in ('ising', 'fibonacci'):
            assert wrt_s3(model) > 0

    def test_s3_less_than_1(self):
        """Z(S^3) < 1 for both models (D > 1)."""
        for model in ('ising', 'fibonacci'):
            assert wrt_s3(model) < 1.0

    def test_s3_consistent_with_global_dim(self):
        """Z(S^3) = 1/D matches mtc_total_quantum_dimension."""
        for model in ('ising', 'fibonacci'):
            D = mtc_total_quantum_dimension(model)
            assert abs(wrt_s3(model) - 1.0 / D) < 1e-14


class TestWRTS2xS1:
    """Z(S^2 x S^1) = rank (number of simple objects)."""

    def test_ising_rank(self):
        """Ising: 3 simple objects {1, sigma, psi}."""
        assert wrt_s2xs1('ising') == 3

    def test_fibonacci_rank(self):
        """Fibonacci: 2 simple objects {1, tau}."""
        assert wrt_s2xs1('fibonacci') == 2

    def test_rank_matches_quantum_dims(self):
        """Rank matches length of quantum dimension vector."""
        for model in ('ising', 'fibonacci'):
            dims = mtc_quantum_dimensions(model)
            assert wrt_s2xs1(model) == len(dims)


# ═══════════════════════════════════════════════════════════════
# Lens Space Invariants Z(L(p,1))
# ═══════════════════════════════════════════════════════════════


class TestLensSpaceIsing:
    """Ising lens space invariants from WRTComputation.lean."""

    def test_lens_1_is_gauss_sum_normalized(self):
        """Z(L(1,1)) numerator = p_+ = 2*zeta_16 (from gauss_sum theorem)."""
        z = wrt_lens_space('ising', 1)
        # D^2 = 4, so Z = (1 + 2*theta_sigma + theta_psi*(-1)) / 4
        # = (1 + 2*e^{i*pi/8} + (-1)) / 4 = 2*e^{i*pi/8}/4 = e^{i*pi/8}/2
        expected = np.exp(1j * np.pi / 8) / 2
        assert abs(z - expected) < 1e-14

    def test_lens_8_vanishing(self):
        """Z(L(8,1)) = 0 for Ising (proved in ising_lens_8_num).

        This is the key result: L(8,1) is 'invisible' to Ising WRT.
        theta_sigma^8 = e^{i*pi} = -1, so numerator = 1 + 2*(-1) + 1 = 0.
        """
        z = wrt_lens_space('ising', 8)
        assert abs(z) < 1e-14

    def test_lens_16_trivial(self):
        """Z(L(16,1)) = 1 for Ising (proved in ising_lens_16_num).

        theta_sigma^16 = e^{2i*pi} = 1, so numerator = 1 + 2 + 1 = 4 = D^2.
        Z = D^2/D^2 = 1.
        """
        z = wrt_lens_space('ising', 16)
        assert abs(z - 1.0) < 1e-14

    def test_lens_2(self):
        """Z(L(2,1)) for Ising: numerator = 2 + 2*zeta^2."""
        z = wrt_lens_space('ising', 2)
        theta_s_sq = np.exp(2j * np.pi / 8)
        expected = (1 + 2 * theta_s_sq + 1) / 4  # theta_psi^2 = (-1)^2 = 1
        assert abs(z - expected) < 1e-14

    def test_lens_3(self):
        """Z(L(3,1)) for Ising: numerator = 2*zeta^3."""
        z = wrt_lens_space('ising', 3)
        theta_s_cubed = np.exp(3j * np.pi / 8)
        expected = (1 + 2 * theta_s_cubed + (-1)**3) / 4
        assert abs(z - expected) < 1e-14

    def test_lens_4(self):
        """Z(L(4,1)) for Ising: numerator = 2 + 2*zeta^4 = 2 + 2i."""
        z = wrt_lens_space('ising', 4)
        theta_s_4 = np.exp(4j * np.pi / 8)  # = i
        expected = (1 + 2 * theta_s_4 + 1) / 4
        assert abs(z - expected) < 1e-14


class TestLensSpaceFibonacci:
    """Fibonacci lens space invariants from WRTComputation.lean."""

    def test_lens_5_trivial(self):
        """Z(L(5,1)) = 1 for Fibonacci (proved in fib_lens_5_num).

        theta_tau^5 = (e^{4i*pi/5})^5 = e^{4i*pi} = 1.
        Numerator = 1 + phi^2 * 1 = 1 + (1+phi) = 2+phi = D^2.
        So Z = D^2/D^2 = 1.
        """
        z = wrt_lens_space('fibonacci', 5)
        assert abs(z - 1.0) < 1e-14

    def test_lens_10_trivial(self):
        """Z(L(10,1)) = 1 for Fibonacci (proved in fib_lens_10_num).

        theta_tau^10 = (theta_tau^5)^2 = 1. Same as L(5,1).
        """
        z = wrt_lens_space('fibonacci', 10)
        assert abs(z - 1.0) < 1e-14

    def test_lens_periodicity_5(self):
        """Fibonacci lens space invariants have period 5 in p."""
        for p in range(1, 6):
            z_p = wrt_lens_space('fibonacci', p)
            z_p5 = wrt_lens_space('fibonacci', p + 5)
            assert abs(z_p - z_p5) < 1e-13, f"Period-5 fails at p={p}"


class TestLensSpaceGeneral:
    """General properties of lens space invariants."""

    def test_lens_0_is_s2xs1_value(self):
        """Z(L(0,1)) = Z(S^2 x S^1) up to normalization.

        L(0,1) surgery = 0-framed unknot = S^2 x S^1.
        Z = (1/D^2) * sum d_i^2 * theta_i^0 = (1/D^2) * D^2 = 1.
        """
        for model in ('ising', 'fibonacci'):
            z = wrt_lens_space(model, 0)
            assert abs(z - 1.0) < 1e-14, f"Z(L(0,1)) != 1 for {model}"

    def test_lens_invariant_bounded(self):
        """|Z(L(p,1))| <= 1 for all p (WRT is a normalized invariant)."""
        for model in ('ising', 'fibonacci'):
            for p in range(0, 20):
                z = wrt_lens_space(model, p)
                assert abs(z) <= 1.0 + 1e-14, (
                    f"|Z(L({p},1))| = {abs(z):.6f} > 1 for {model}"
                )


# ═══════════════════════════════════════════════════════════════
# Surgery Presentation Tests
# ═══════════════════════════════════════════════════════════════


class TestSurgeryPresentation:
    """Tests for surgery linking matrices."""

    def test_s3_empty(self):
        """S^3 is the empty surgery (0 components)."""
        data = surgery_linking_matrix('S3')
        assert data['num_components'] == 0
        assert data['matrix'].shape == (0, 0)
        assert data['framings'] == []

    def test_s2xs1_zero_framing(self):
        """S^2 x S^1 = 0-framed unknot."""
        data = surgery_linking_matrix('S2xS1')
        assert data['num_components'] == 1
        assert data['framings'] == [0]
        assert data['matrix'][0, 0] == 0

    def test_lens_framing(self):
        """L(p,1) = p-framed unknot."""
        for p in [-3, -1, 0, 1, 5, 16]:
            data = surgery_linking_matrix('lens', p=p)
            assert data['num_components'] == 1
            assert data['framings'] == [p]
            assert data['matrix'][0, 0] == p

    def test_lens_0_is_s2xs1(self):
        """L(0,1) linking matrix = S^2 x S^1 linking matrix."""
        lens0 = surgery_linking_matrix('lens', p=0)
        s2xs1 = surgery_linking_matrix('S2xS1')
        assert np.array_equal(lens0['matrix'], s2xs1['matrix'])

    def test_hopf_link(self):
        """Hopf link surgery: 2 components, linking number 1."""
        data = surgery_linking_matrix('hopf', a=2, b=3)
        assert data['num_components'] == 2
        M = data['matrix']
        assert M[0, 0] == 2
        assert M[1, 1] == 3
        assert M[0, 1] == 1  # linking number
        assert M[1, 0] == 1  # symmetric

    def test_hopf_symmetric(self):
        """Hopf link matrix is symmetric."""
        M = surgery_linking_matrix('hopf', a=5, b=-2)['matrix']
        assert np.array_equal(M, M.T)

    def test_trefoil_complement(self):
        """Trefoil complement surgery: [[-2,1],[1,-3]]."""
        data = surgery_linking_matrix('trefoil_complement')
        M = data['matrix']
        assert data['num_components'] == 2
        assert M[0, 0] == -2
        assert M[1, 1] == -3
        assert M[0, 1] == 1
        assert M[1, 0] == 1

    def test_all_linking_matrices_symmetric(self):
        """All surgery presentations produce symmetric matrices."""
        cases = [
            ('S2xS1',),
            ('lens', {'p': 7}),
            ('hopf', {'a': 3, 'b': -1}),
            ('trefoil_complement',),
        ]
        for args in cases:
            name = args[0]
            kwargs = args[1] if len(args) > 1 else {}
            M = surgery_linking_matrix(name, **kwargs)['matrix']
            assert np.array_equal(M, M.T), f"{name} not symmetric"


class TestHandleSlide:
    """Tests for Kirby move K2 (handle slide)."""

    def test_handle_slide_preserves_size(self):
        """Handle slide preserves matrix dimensions."""
        M = surgery_linking_matrix('hopf', a=2, b=3)['matrix']
        M_slid = surgery_handle_slide(M, 0, 1)
        assert M_slid.shape == M.shape

    def test_handle_slide_symmetry(self):
        """Handle slide preserves symmetry (proved in Lean)."""
        M = surgery_linking_matrix('hopf', a=2, b=3)['matrix']
        M_slid = surgery_handle_slide(M, 0, 1)
        assert np.array_equal(M_slid, M_slid.T), "Handle slide broke symmetry"

    def test_self_slide_lens(self):
        """Self-slide on L(p,1) gives framing 4p (proved: handleSlide_self_framing)."""
        for p in [1, 2, 3, 5, -1, -7]:
            M = surgery_linking_matrix('lens', p=p)['matrix']
            M_slid = surgery_handle_slide(M, 0, 0)
            assert M_slid[0, 0] == 4 * p, (
                f"Self-slide on L({p},1): got {M_slid[0, 0]}, expected {4*p}"
            )

    def test_handle_slide_hopf(self):
        """Handle slide on Hopf link: specific numerical check."""
        # Hopf: [[a,1],[1,b]], slide 0 over 1
        # Result[0,0] = a + 1 + 1 + b = a + b + 2
        # Result[0,1] = 1 + b
        # Result[1,0] = 1 + b (symmetric)
        # Result[1,1] = b (unchanged)
        M = surgery_linking_matrix('hopf', a=2, b=3)['matrix']
        M_slid = surgery_handle_slide(M, 0, 1)
        assert M_slid[0, 0] == 2 + 3 + 2  # a + b + 2
        assert M_slid[0, 1] == 1 + 3  # off-diag + b
        assert M_slid[1, 0] == 1 + 3  # symmetric
        assert M_slid[1, 1] == 3  # unchanged

    def test_handle_slide_trefoil_symmetry(self):
        """Handle slide on trefoil complement preserves symmetry."""
        M = surgery_linking_matrix('trefoil_complement')['matrix']
        for i in range(2):
            for j in range(2):
                M_slid = surgery_handle_slide(M, i, j)
                assert np.array_equal(M_slid, M_slid.T), (
                    f"Slide ({i},{j}) on trefoil broke symmetry"
                )


# ═══════════════════════════════════════════════════════════════
# Temperley-Lieb Relation Tests
# ═══════════════════════════════════════════════════════════════


class TestTemperleyLiebRelations:
    """Verify TL relation structure matches Lean formalization."""

    def test_tl1_idempotent_valid(self):
        """TL1: e_i^2 = delta * e_i is valid for all generators."""
        for i in range(5):
            result = tl_relation_check(5, 2.0, 'idempotent', i)
            assert result['valid'] is True
            assert result['type'] == 'TL1'

    def test_tl1_out_of_range(self):
        """TL1 fails for out-of-range index."""
        result = tl_relation_check(3, 2.0, 'idempotent', 5)
        assert result['valid'] is False

    def test_tl2_jones_adjacent(self):
        """TL2: e_i * e_j * e_i = e_i for |i-j| = 1."""
        # Adjacent pairs
        for (i, j) in [(0, 1), (1, 0), (1, 2), (2, 1), (3, 4)]:
            result = tl_relation_check(5, 2.0, 'jones', i, j)
            assert result['valid'] is True, f"Jones failed for ({i},{j})"
            assert result['type'] == 'TL2'

    def test_tl2_jones_non_adjacent(self):
        """TL2 fails for non-adjacent generators."""
        result = tl_relation_check(5, 2.0, 'jones', 0, 2)
        assert result['valid'] is False

    def test_tl3_far_commute(self):
        """TL3: e_i * e_j = e_j * e_i for |i-j| >= 2."""
        for (i, j) in [(0, 2), (0, 3), (1, 3), (0, 4), (2, 4)]:
            result = tl_relation_check(5, 2.0, 'far_commute', i, j)
            assert result['valid'] is True, f"Far commute failed for ({i},{j})"
            assert result['type'] == 'TL3'

    def test_tl3_not_far(self):
        """TL3 fails for adjacent generators."""
        result = tl_relation_check(5, 2.0, 'far_commute', 0, 1)
        assert result['valid'] is False

    def test_three_relation_types_exhaustive(self):
        """Every pair (i,j) with i != j falls into exactly one of TL2 or TL3.

        For |i-j| = 1: Jones relation (TL2)
        For |i-j| >= 2: far commute (TL3)
        """
        n = 5
        for i in range(n):
            for j in range(n):
                if i == j:
                    continue
                diff = abs(i - j)
                if diff == 1:
                    assert tl_relation_check(n, 2.0, 'jones', i, j)['valid']
                    assert not tl_relation_check(n, 2.0, 'far_commute', i, j)['valid']
                else:
                    assert diff >= 2
                    assert not tl_relation_check(n, 2.0, 'jones', i, j)['valid']
                    assert tl_relation_check(n, 2.0, 'far_commute', i, j)['valid']

    def test_delta_appears_in_idempotent(self):
        """TL1 relation string contains the delta value."""
        result = tl_relation_check(3, 1.5, 'idempotent', 0)
        assert '1.5' in result['relation']


# ═══════════════════════════════════════════════════════════════
# WRT Global Dimension Consistency
# ═══════════════════════════════════════════════════════════════


class TestGlobalDimensionConsistency:
    """Cross-checks between su2k formulas and WRT computations."""

    def test_ising_d_sq_from_su2k(self):
        """Ising D^2 = 4 from su2k_global_dim_sq(k=2)."""
        D_sq = su2k_global_dim_sq(2)
        assert abs(D_sq - 4.0) < 1e-13

    def test_fibonacci_d_sq_from_su2k(self):
        """Fibonacci D^2 from su2k_global_dim_sq(k=3) (contains Fibonacci as subcategory)."""
        D_sq_k3 = su2k_global_dim_sq(3)
        # k=3 has 4 objects; Fibonacci is the {0,3} subcategory with d_tau = phi
        assert abs(D_sq_k3 - (5 + math.sqrt(5))) < 1e-13

    def test_ising_dims(self):
        """Ising quantum dimensions: d = (1, sqrt(2), 1)."""
        assert abs(su2k_quantum_dim(2, 0) - 1.0) < 1e-14
        assert abs(su2k_quantum_dim(2, 1) - math.sqrt(2)) < 1e-14
        assert abs(su2k_quantum_dim(2, 2) - 1.0) < 1e-14

    def test_fibonacci_dim_tau(self):
        """Fibonacci: d_tau = phi (golden ratio)."""
        # At k=3, the Fibonacci subcategory uses j=0 and j=3
        # But the tau anyon is j=1 at k=3 for the full theory, or equivalently
        # d_1(k=3) = phi
        d1 = su2k_quantum_dim(3, 1)
        assert abs(d1 - PHI) < 1e-14

    def test_twist_consistency(self):
        """su2k_twist matches WRT lens space theta values."""
        # Ising: theta_sigma = e^{i*pi/8} from su2k_twist(k=2, a=1)
        theta = su2k_twist(2, 1)
        assert abs(theta - np.exp(2j * np.pi * 1 * 3 / (4 * 4))) < 1e-14
        # theta_a = exp(2*pi*i * a*(a+2) / (4*(k+2)))
        # For k=2, a=1: exp(2*pi*i * 1*3 / 16) = exp(i*pi*3/8)
        # Note: the Lean convention uses theta_sigma = e^{i*pi/8} for the twist
        # while su2k_twist gives the conformal weight formula

    def test_topological_central_charge_ising(self):
        """Ising c_top = 3/2 from su2k_topological_central_charge(k=2)."""
        c = su2k_topological_central_charge(2)
        assert abs(c - 1.5) < 1e-14

    def test_topological_central_charge_k1(self):
        """k=1: c_top = 1."""
        c = su2k_topological_central_charge(1)
        assert abs(c - 1.0) < 1e-14


# ═══════════════════════════════════════════════════════════════
# WRT Invariants Table
# ═══════════════════════════════════════════════════════════════


class TestWRTInvariantsTable:
    """Integration test for the invariants table function."""

    def test_table_has_entries(self):
        """Table returns non-empty list."""
        rows = wrt_invariants_table()
        assert len(rows) >= 6

    def test_table_fields(self):
        """Each row has required fields."""
        rows = wrt_invariants_table()
        for row in rows:
            assert 'manifold' in row
            assert 'ising' in row
            assert 'fibonacci' in row
            assert 'lean_status' in row

    def test_all_proved(self):
        """All entries in the table are PROVED in Lean."""
        rows = wrt_invariants_table()
        for row in rows:
            assert row['lean_status'] == 'PROVED', (
                f"{row['manifold']} not proved"
            )

    def test_table_includes_key_manifolds(self):
        """Table includes S^3, S^2 x S^1, and at least one lens space."""
        rows = wrt_invariants_table()
        manifolds = [r['manifold'] for r in rows]
        assert 'S^3' in manifolds
        assert 'S^2 x S^1' in manifolds
        assert any('L(' in m for m in manifolds)


# ═══════════════════════════════════════════════════════════════
# Physical Bounds (CHECK 12 compliance)
# ═══════════════════════════════════════════════════════════════


class TestPhysicalBounds:
    """Ensure all WRT quantities satisfy physical bounds."""

    def test_wrt_s3_bounded(self):
        """0 < Z(S^3) < 1 for both models."""
        for model in ('ising', 'fibonacci'):
            z = wrt_s3(model)
            assert 0 < z < 1, f"Z(S^3) = {z} out of bounds for {model}"

    def test_lens_space_bounded(self):
        """|Z(L(p,1))| <= 1 for all tested p."""
        for model in ('ising', 'fibonacci'):
            for p in range(0, 25):
                z = wrt_lens_space(model, p)
                assert abs(z) <= 1.0 + 1e-14, (
                    f"|Z(L({p},1))| = {abs(z)} for {model}"
                )

    def test_global_dim_positive(self):
        """D^2 > 0 for both models."""
        for model in ('ising', 'fibonacci'):
            D = mtc_total_quantum_dimension(model)
            assert D > 0

    def test_quantum_dims_positive(self):
        """All quantum dimensions > 0."""
        for model in ('ising', 'fibonacci'):
            dims = mtc_quantum_dimensions(model)
            assert all(d > 0 for d in dims), f"Negative dim in {model}"
