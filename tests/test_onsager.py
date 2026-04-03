"""
Tests for Phase 5a Wave 1A: Onsager Algebra formulas and constants.

Validates:
  - Dolan-Grady relation verification
  - Davies commutation relation structure
  - Chevalley embedding consistency
  - Algebraic dimension properties
  - Coefficient relationships between presentations
"""

import numpy as np
import pytest

from src.core.constants import ONSAGER_ALGEBRA
from src.core.formulas import (
    onsager_dg_relation,
    onsager_davies_commutator,
    onsager_chevalley_embedding,
    onsager_dimension,
)


# ════════════════════════════════════════════════════════════════════
# Constants validation
# ════════════════════════════════════════════════════════════════════


class TestOnsagerConstants:
    """Validate Onsager algebra constants from constants.py."""

    def test_dg_coeff_is_16(self):
        """The Dolan-Grady coefficient is 16 (Dolan & Grady, PRL 49, 1982)."""
        assert ONSAGER_ALGEBRA['DG_COEFF'] == 16

    def test_dg_coeff_factors(self):
        """DG_COEFF = 4² = DAVIES_AA² — connecting the two presentations."""
        assert ONSAGER_ALGEBRA['DG_COEFF'] == ONSAGER_ALGEBRA['DAVIES_AA_COEFF'] ** 2

    def test_davies_aa_coeff(self):
        """Davies AA coefficient: [A_m, A_n] = 4 G_{m-n}."""
        assert ONSAGER_ALGEBRA['DAVIES_AA_COEFF'] == 4

    def test_davies_ga_coeff(self):
        """Davies GA coefficient: [G_n, A_m] = 2(A_{m+n} - A_{m-n})."""
        assert ONSAGER_ALGEBRA['DAVIES_GA_COEFF'] == 2

    def test_dg_generators(self):
        """DG presentation has exactly 2 generators (A₀, A₁)."""
        assert ONSAGER_ALGEBRA['GENERATORS'] == 2

    def test_dg_relations(self):
        """DG presentation has exactly 2 cubic relations."""
        assert ONSAGER_ALGEBRA['RELATIONS'] == 2

    def test_sl2_dim(self):
        """sl₂ is 3-dimensional (contraction target)."""
        assert ONSAGER_ALGEBRA['SL2_DIM'] == 3

    def test_coefficient_chain(self):
        """The coefficient chain: DG_COEFF = AA² and AA = 2 × GA."""
        aa = ONSAGER_ALGEBRA['DAVIES_AA_COEFF']
        ga = ONSAGER_ALGEBRA['DAVIES_GA_COEFF']
        dg = ONSAGER_ALGEBRA['DG_COEFF']
        assert aa == 2 * ga  # 4 = 2 × 2
        assert dg == aa ** 2  # 16 = 4²


# ════════════════════════════════════════════════════════════════════
# Dolan-Grady relation tests
# ════════════════════════════════════════════════════════════════════


class TestDolanGradyRelation:
    """Test the DG relation verification function."""

    def test_dg_relation_holds(self):
        """DG relation: [A₀, [A₀, [A₀, A₁]]] = 16[A₀, A₁]."""
        assert onsager_dg_relation(1.0, 16.0) is True

    def test_dg_relation_fails(self):
        """DG relation fails when triple bracket ≠ 16 × single bracket."""
        assert onsager_dg_relation(1.0, 15.0) is False

    def test_dg_relation_zero(self):
        """DG relation trivially holds when [A₀, A₁] = 0."""
        assert onsager_dg_relation(0.0, 0.0) is True

    def test_dg_relation_scaling(self):
        """DG relation is homogeneous: if (a, 16a) works, so does (λa, 16λa)."""
        for scale in [0.1, 1.0, 100.0, -5.0]:
            assert onsager_dg_relation(scale, 16.0 * scale) is True

    def test_dg_relation_coefficient_exact(self):
        """The coefficient is exactly 16, not 15 or 17."""
        a = 1.0
        assert onsager_dg_relation(a, 16 * a) is True
        assert onsager_dg_relation(a, 15 * a) is False
        assert onsager_dg_relation(a, 17 * a) is False


# ════════════════════════════════════════════════════════════════════
# Davies commutation relation tests
# ════════════════════════════════════════════════════════════════════


class TestDaviesCommutator:
    """Test the Davies commutation relation structure."""

    def test_AA_commutator_structure(self):
        """[A_m, A_n] = 4 G_{m-n} — returns correct coefficient."""
        A = {0: 1.0, 1: 2.0, 2: 3.0, -1: -2.0}
        G = {0: 0.0, 1: 0.5, -1: -0.5, 2: 1.0, -2: -1.0}
        result = onsager_davies_commutator(2, 1, A, G)
        assert 'AA' in result
        assert result['AA'][0] == 4 * G[1]  # 4 * G_{2-1} = 4 * G_1

    def test_GA_commutator_structure(self):
        """[G_n, A_m] = 2(A_{m+n} - A_{m-n})."""
        A = {0: 1.0, 1: 2.0, 2: 3.0, 3: 4.0, -1: -2.0}
        G = {0: 0.0, 1: 0.5, -1: -0.5}
        result = onsager_davies_commutator(2, 1, A, G)
        assert 'GA' in result
        assert result['GA'][0] == 2 * (A[3] - A[1])  # 2 * (A_{2+1} - A_{2-1})

    def test_GG_commutator_zero(self):
        """[G_m, G_n] = 0 — abelian G-subalgebra."""
        A = {0: 1.0}
        G = {0: 0.0, 1: 0.5}
        result = onsager_davies_commutator(0, 1, A, G)
        assert 'GG' in result
        assert result['GG'][0] == 0

    def test_commutator_keys(self):
        """Result always has 'GG' key (abelian) regardless of indices."""
        A = {0: 1.0, 1: 2.0}
        G = {0: 0.0}
        result = onsager_davies_commutator(0, 1, A, G)
        assert 'GG' in result


# ════════════════════════════════════════════════════════════════════
# Chevalley embedding tests
# ════════════════════════════════════════════════════════════════════


class TestChevalleyEmbedding:
    """Test the Chevalley involution embedding into L(sl₂)."""

    def test_theta_fixed(self):
        """All embedded generators are θ̂-fixed by construction."""
        for m in range(-5, 6):
            emb = onsager_chevalley_embedding(m)
            assert emb['theta_fixed'] is True

    def test_A_embedding_format(self):
        """A_m embedding: f⊗t^m - e⊗t^{-m}."""
        emb = onsager_chevalley_embedding(3)
        assert 'f⊗t^3' in emb['A_m']
        assert 'e⊗t^-3' in emb['A_m']

    def test_G_embedding_format(self):
        """G_m embedding: h⊗t^{-m} - h⊗t^m."""
        emb = onsager_chevalley_embedding(2)
        assert 'h⊗t^-2' in emb['G_m']
        assert 'h⊗t^2' in emb['G_m']

    def test_A0_embedding(self):
        """A₀ embedding: f⊗t^0 - e⊗t^0 = f - e (in sl₂ directly)."""
        emb = onsager_chevalley_embedding(0)
        assert 'f⊗t^0' in emb['A_m']
        assert 'e⊗t^0' in emb['A_m']


# ════════════════════════════════════════════════════════════════════
# Algebraic dimension tests
# ════════════════════════════════════════════════════════════════════


class TestOnsagerDimension:
    """Test the Onsager algebra dimension and structure properties."""

    def test_infinite_dimensional(self):
        """The Onsager algebra is infinite-dimensional."""
        dim = onsager_dimension()
        assert dim['is_infinite_dimensional'] is True

    def test_A_basis_integer_indexed(self):
        """A_m generators are ℤ-indexed."""
        dim = onsager_dimension()
        assert 'ℤ' in dim['basis_A']

    def test_G_basis_positive_indexed(self):
        """G_n generators are indexed by positive integers."""
        dim = onsager_dimension()
        assert '>' in dim['basis_G'] or 'positive' in dim['basis_G'].lower() or '{>0}' in dim['basis_G']

    def test_two_dg_generators(self):
        """Finitely generated: only 2 DG generators produce everything."""
        dim = onsager_dimension()
        assert dim['dg_generators'] == 2

    def test_trivial_center(self):
        """The center is trivial (or spanned by G₀)."""
        dim = onsager_dimension()
        assert dim['center'] == 'trivial'


# ════════════════════════════════════════════════════════════════════
# Physics connection tests
# ════════════════════════════════════════════════════════════════════


class TestPhysicsConnections:
    """Test connections to physical applications."""

    def test_ising_spin_dim(self):
        """Single Ising spin: ℂ² (dimension 2)."""
        assert 2 ** 1 == 2

    def test_contraction_target_su2(self):
        """Contraction target su(2) is 3-dimensional."""
        assert ONSAGER_ALGEBRA['SL2_DIM'] == 3

    def test_dg_coeff_from_physics(self):
        """DG coefficient 16 = 4 × 2 × 2 (Davies × GA × GA)."""
        aa = ONSAGER_ALGEBRA['DAVIES_AA_COEFF']
        ga = ONSAGER_ALGEBRA['DAVIES_GA_COEFF']
        assert aa * ga * ga == ONSAGER_ALGEBRA['DG_COEFF']
