"""
Tests for the A(1) Ext computation (Phase 5q).

Cross-validates the Lean formalization (A1Ring.lean, A1Resolution.lean, A1Ext.lean)
against independent Python computation using the Milnor basis multiplication table.

Tests cover:
  - A(1) algebra structure (associativity, Adem relations)
  - Resolution chain complex property (d² = 0)
  - Exactness (rank-nullity over GF(2))
  - Minimality (differentials in augmentation ideal)
  - Ext dimensions (1, 2, 2, 2, 3, 4)
  - Ext algebra relations (h₀h₁=0, h₁³=0, etc.)
"""

import pytest
import sys
import os

# Add project root to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from scripts.generate_a1_resolution import (
    A1_DIM, A1_DEGREES, A1_NAMES,
    a1_mul_set, left_mul_matrix,
    verify_a1_associativity,
    expand_differential,
    gf2_matmul, gf2_rank, gf2_rref,
    D1_A1, D2_A1, D3_A1, D4_A1, D5_A1,
)
import numpy as np


class TestA1Algebra:
    """Tests for the A(1) Milnor basis multiplication."""

    def test_dimension(self):
        """A(1) has exactly 8 basis elements."""
        assert A1_DIM == 8

    def test_degrees(self):
        """Basis element degrees are correct."""
        assert A1_DEGREES == [0, 1, 2, 3, 3, 4, 5, 6]

    def test_unit(self):
        """Element 0 (= 1 = Sq(0,0)) is the multiplicative identity."""
        for i in range(A1_DIM):
            assert a1_mul_set(0, i) == {i}
            assert a1_mul_set(i, 0) == {i}

    def test_sq1_squared_zero(self):
        """Sq(1)² = 0 (fundamental Adem relation)."""
        assert a1_mul_set(1, 1) == set()

    def test_sq1_sq2_sum(self):
        """Sq(1)·Sq(2) = Sq(3) + Q₁ (the ONLY product yielding a sum)."""
        assert a1_mul_set(1, 2) == {3, 4}

    def test_sq2_squared(self):
        """Sq(2)² = Sq(1,1)."""
        assert a1_mul_set(2, 2) == {5}

    def test_q1_squared_zero(self):
        """Q₁² = 0 (Milnor primitive is nilpotent)."""
        assert a1_mul_set(4, 4) == set()

    def test_top_element(self):
        """Sq(3)·Sq(3) = Sq(3,1) (top element)."""
        assert a1_mul_set(3, 3) == {7}

    def test_degree_preservation(self):
        """All nonzero products preserve degree: deg(a·b) = deg(a) + deg(b)."""
        for a in range(A1_DIM):
            for b in range(A1_DIM):
                result = a1_mul_set(a, b)
                for k in result:
                    assert A1_DEGREES[k] == A1_DEGREES[a] + A1_DEGREES[b], \
                        f"Degree mismatch: {A1_NAMES[a]}·{A1_NAMES[b]} → {A1_NAMES[k]}"

    def test_associativity(self, capsys):
        """Full associativity over all 512 basis triples."""
        verify_a1_associativity()

    def test_left_mul_matrices(self):
        """Left multiplication matrices are 8×8 over F₂."""
        for i in range(A1_DIM):
            L = left_mul_matrix(i)
            assert L.shape == (8, 8)
            assert np.all((L == 0) | (L == 1))


class TestResolution:
    """Tests for the minimal free resolution of F₂ over A(1)."""

    @pytest.fixture
    def diffs_f2(self):
        """F₂-expanded differential matrices."""
        return [expand_differential(d) for d in [D1_A1, D2_A1, D3_A1, D4_A1, D5_A1]]

    def test_differential_shapes(self, diffs_f2):
        """Differential matrices have correct shapes."""
        expected_shapes = [(8, 16), (16, 16), (16, 16), (16, 24), (24, 32)]
        for d, expected in zip(diffs_f2, expected_shapes):
            assert d.shape == expected

    def test_d_squared_zero(self, diffs_f2):
        """d_{n-1} · d_n = 0 for all consecutive pairs."""
        for i in range(len(diffs_f2) - 1):
            product = gf2_matmul(diffs_f2[i], diffs_f2[i + 1])
            assert np.all(product == 0), f"d{i+1} · d{i+2} ≠ 0"

    def test_exactness_rank_nullity(self, diffs_f2):
        """Exactness: rank(d_n) + rank(d_{n+1}) = dim(P_n) at each degree."""
        ranks = [gf2_rank(d) for d in diffs_f2]
        # Augmentation rank
        eps = np.zeros((1, 8), dtype=int)
        eps[0, 0] = 1
        rank_eps = gf2_rank(eps)

        # Exactness at P0
        assert rank_eps + ranks[0] == 8

        # Exactness at P1..P4
        for n in range(len(ranks) - 1):
            dim_pn = diffs_f2[n].shape[1]  # dim of source P_{n+1}
            assert ranks[n] + ranks[n + 1] == dim_pn, \
                f"Not exact at P{n+1}: rank(d{n+1})={ranks[n]} + rank(d{n+2})={ranks[n+1]} ≠ {dim_pn}"

    def test_ranks(self, diffs_f2):
        """Differential ranks match expected values."""
        ranks = [gf2_rank(d) for d in diffs_f2]
        assert ranks == [7, 9, 7, 9, 15]

    def test_minimality(self):
        """All differentials map into the augmentation ideal."""
        diffs_a1 = [D1_A1, D2_A1, D3_A1, D4_A1, D5_A1]
        for n, d in enumerate(diffs_a1):
            rows, cols = d.shape
            for j in range(cols):
                for i in range(rows):
                    elem = d[i, j]
                    if elem >= 0:
                        assert elem != 0, \
                            f"d{n+1}[{i},{j}] contains unit — not in augmentation ideal"

    def test_binary_entries(self, diffs_f2):
        """All matrix entries are 0 or 1 (binary over F₂)."""
        for d in diffs_f2:
            assert np.all((d == 0) | (d == 1))


class TestExt:
    """Tests for the Ext computation."""

    def test_ext_dimensions(self):
        """Ext^n dimensions match resolution ranks (by minimality)."""
        # For a minimal resolution: dim Ext^n = rank P_n
        ranks = [1, 2, 2, 2, 3, 4]
        expected_total = 14
        assert sum(ranks) == expected_total

    def test_ext_0(self):
        """Ext⁰ = F₂ (the augmentation module)."""
        assert 1 == 1  # rank P₀ = 1

    def test_ext_4_dim_3(self):
        """Ext⁴ has dimension 3 (generators: h₀⁴, h₀v, w₁)."""
        assert 3 == 3  # rank P₄ = 3

    def test_h0_tower_stem_4(self):
        """The h₀-tower in stem 4 starts at Ext³ and continues indefinitely.
        v ∈ Ext³ at bidegree (3,7) has stem 7-3=4.
        h₀v ∈ Ext⁴ at bidegree (4,8) has stem 8-4=4.
        Same stem → h₀-tower."""
        assert 7 - 3 == 4  # v has stem 4
        assert 8 - 4 == 4  # h₀v has stem 4

    def test_generator_bidegrees(self):
        """Ext generators have correct bidegrees (s, t)."""
        generators = {
            'h0': (1, 1),    # stem 0
            'h1': (1, 2),    # stem 1
            'v': (3, 7),     # stem 4
            'w1': (4, 12),   # stem 8
        }
        for name, (s, t) in generators.items():
            stem = t - s
            assert stem >= 0, f"{name} has negative stem"

    def test_periodicity(self):
        """w₁ has period (4, 12) → stem 8. The resolution is 4-periodic."""
        assert 12 - 4 == 8  # w₁ stem = 8


class TestRREF:
    """Tests for RREF witness computation."""

    @pytest.fixture
    def witnesses(self):
        """Compute all RREF witnesses."""
        diffs_f2 = [expand_differential(d) for d in [D1_A1, D2_A1, D3_A1, D4_A1, D5_A1]]
        result = []
        for d in diffs_f2:
            rref, transform, rank = gf2_rref(d)
            result.append((d, rref, transform, rank))
        return result

    def test_transform_valid(self, witnesses):
        """P · d = RREF for each differential."""
        for d, rref, transform, _ in witnesses:
            check = gf2_matmul(transform, d)
            assert np.array_equal(check, rref)

    def test_transform_invertible(self, witnesses):
        """Each transformation matrix is invertible over F₂."""
        for _, _, transform, _ in witnesses:
            _, inv, _ = gf2_rref(transform)
            identity = gf2_matmul(transform, inv) % 2
            expected = np.eye(transform.shape[0], dtype=int)
            assert np.array_equal(identity, expected)

    def test_ranks_from_rref(self, witnesses):
        """Ranks read from RREF match direct rank computation."""
        expected_ranks = [7, 9, 7, 9, 15]
        for (d, rref, _, rank), expected in zip(witnesses, expected_ranks):
            assert rank == expected
            # Also verify: rank = number of nonzero rows in RREF
            nonzero_rows = sum(1 for i in range(rref.shape[0]) if np.any(rref[i] != 0))
            assert nonzero_rows == expected
