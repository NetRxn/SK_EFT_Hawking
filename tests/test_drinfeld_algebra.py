"""Tests for Drinfeld double algebra and equivalence formulas.

Tests the D(G) algebra operations (basis multiplication, antipode, coproduct)
and the Z(Vec_G) ≅ Rep(D(G)) equivalence properties for concrete groups.

Formulas from: src/core/formulas.py
Lean modules: DrinfeldDoubleRing.lean, DrinfeldEquivalence.lean
"""

import pytest
import numpy as np
from src.core.formulas import (
    drinfeld_double_dim,
    drinfeld_double_simples_abelian,
    drinfeld_double_simples,
    drinfeld_double_basis_mul,
    drinfeld_double_antipode,
    drinfeld_coproduct_summands,
)


# ════════════════════════════════════════════════════════════════════
# Helper: concrete group elements for Z/2 and S₃
# ════════════════════════════════════════════════════════════════════

class Z2:
    """Z/2 = {0, 1} with addition mod 2."""
    elements = [0, 1]

    @staticmethod
    def mul(a, b):
        return (a + b) % 2

    @staticmethod
    def inv(a):
        return a  # every element is its own inverse in Z/2

    @staticmethod
    def conjugate(g, x):
        return x  # Z/2 is abelian


class IntMod:
    """Integers mod n as a group under addition."""
    def __init__(self, n):
        self.n = n
        self.elements = list(range(n))

    def mul(self, a, b):
        return (a + b) % self.n

    def inv(self, a):
        return (-a) % self.n

    def conjugate(self, g, x):
        return x  # abelian


# ════════════════════════════════════════════════════════════════════
# Test: D(G) dimensions
# ════════════════════════════════════════════════════════════════════

class TestDrinfeldDoubleDim:
    """Test dim D(G) = |G|²."""

    def test_z2(self):
        assert drinfeld_double_dim(2) == 4

    def test_z3(self):
        assert drinfeld_double_dim(3) == 9

    def test_s3(self):
        assert drinfeld_double_dim(6) == 36

    def test_trivial(self):
        assert drinfeld_double_dim(1) == 1

    def test_z5(self):
        assert drinfeld_double_dim(5) == 25


# ════════════════════════════════════════════════════════════════════
# Test: Simple module counts
# ════════════════════════════════════════════════════════════════════

class TestSimpleCounts:
    """Test simple D(G)-module counts."""

    def test_z2_abelian(self):
        """Z/2: 4 simples (toric code anyons)."""
        assert drinfeld_double_simples_abelian(2) == 4

    def test_z3_abelian(self):
        """Z/3: 9 simples."""
        assert drinfeld_double_simples_abelian(3) == 9

    def test_s3_general(self):
        """S₃: 3 classes, irreps [1, 3, 2] per centralizer → 8 simples."""
        # {e}: centralizer = S₃, 3 irreps (triv, sign, std)
        # {(12),(13),(23)}: centralizer = Z/2, each has 2 irreps
        #   but there are 3 elements in 1 class, centralizer = ⟨(12)⟩ ≅ Z/2
        # {(123),(132)}: centralizer = Z/3, 3 irreps
        # Total: 3 + 2 + 3 = 8
        assert drinfeld_double_simples(3, [3, 2, 3]) == 8

    def test_s3_global_dim(self):
        """S₃: D² = Σ d_a² = 1+1+4+9+9+4+4+4 = 36 = |S₃|²."""
        quantum_dims_sq = [1, 1, 4, 9, 9, 4, 4, 4]
        assert sum(quantum_dims_sq) == 36
        assert sum(quantum_dims_sq) == drinfeld_double_dim(6)


# ════════════════════════════════════════════════════════════════════
# Test: Basis multiplication
# ════════════════════════════════════════════════════════════════════

class TestBasisMultiplication:
    """Test (δ_a ⊗ g1) · (δ_b ⊗ g2) = δ_{a, g1·b·g1⁻¹} · (δ_a ⊗ g1·g2)."""

    def test_z2_identity_mul(self):
        """(δ_0 ⊗ 0) · (δ_0 ⊗ 0) = δ_0 ⊗ 0 (unit * unit = unit)."""
        result = drinfeld_double_basis_mul(0, 0, 0, 0, Z2.mul, Z2.conjugate)
        assert result == (0, 0)

    def test_z2_nonzero_product(self):
        """(δ_0 ⊗ 1) · (δ_0 ⊗ 1) = δ_0 ⊗ 0."""
        result = drinfeld_double_basis_mul(0, 0, 1, 1, Z2.mul, Z2.conjugate)
        assert result == (0, 0)  # g1*g2 = 1+1 = 0 mod 2

    def test_z2_zero_product(self):
        """(δ_0 ⊗ 0) · (δ_1 ⊗ 0) = 0 (a=0 ≠ conj(0,1)=1)."""
        result = drinfeld_double_basis_mul(0, 1, 0, 0, Z2.mul, Z2.conjugate)
        assert result is None

    def test_z2_matching_grades(self):
        """(δ_1 ⊗ 0) · (δ_1 ⊗ 1) = δ_1 ⊗ 1."""
        result = drinfeld_double_basis_mul(1, 1, 0, 1, Z2.mul, Z2.conjugate)
        assert result == (1, 1)

    def test_abelian_conjugation_trivial(self):
        """For abelian G, conjugation is trivial: product is nonzero iff a == b."""
        z3 = IntMod(3)
        # a=1, b=1, g1=2, g2=1: conj(2,1) = 1 = a, so nonzero
        result = drinfeld_double_basis_mul(1, 1, 2, 1, z3.mul, z3.conjugate)
        assert result == (1, 0)  # g1*g2 = 2+1 = 0 mod 3

    def test_abelian_mismatch_zero(self):
        """For abelian G, a ≠ b gives zero."""
        z3 = IntMod(3)
        result = drinfeld_double_basis_mul(1, 2, 0, 0, z3.mul, z3.conjugate)
        assert result is None


# ════════════════════════════════════════════════════════════════════
# Test: Antipode
# ════════════════════════════════════════════════════════════════════

class TestAntipode:
    """Test S(δ_a ⊗ g) = δ_{g⁻¹·a⁻¹·g} ⊗ g⁻¹."""

    def test_z2_identity(self):
        """S(δ_0 ⊗ 0) = δ_0 ⊗ 0."""
        result = drinfeld_double_antipode(0, 0, Z2.inv, Z2.conjugate)
        assert result == (0, 0)

    def test_z2_nontrivial(self):
        """S(δ_1 ⊗ 1) = δ_1 ⊗ 1 (in Z/2, everything is self-inverse)."""
        result = drinfeld_double_antipode(1, 1, Z2.inv, Z2.conjugate)
        assert result == (1, 1)

    def test_involutive_z2(self):
        """S(S(x)) = x for all Z/2 basis elements."""
        for a in Z2.elements:
            for g in Z2.elements:
                s_once = drinfeld_double_antipode(a, g, Z2.inv, Z2.conjugate)
                s_twice = drinfeld_double_antipode(s_once[0], s_once[1], Z2.inv, Z2.conjugate)
                assert s_twice == (a, g), f"S²(δ_{a}⊗{g}) ≠ δ_{a}⊗{g}"

    def test_involutive_z3(self):
        """S(S(x)) = x for all Z/3 basis elements."""
        z3 = IntMod(3)
        for a in z3.elements:
            for g in z3.elements:
                s1 = drinfeld_double_antipode(a, g, z3.inv, z3.conjugate)
                s2 = drinfeld_double_antipode(s1[0], s1[1], z3.inv, z3.conjugate)
                assert s2 == (a, g)


# ════════════════════════════════════════════════════════════════════
# Test: Coproduct
# ════════════════════════════════════════════════════════════════════

class TestCoproduct:
    """Test Δ(δ_a ⊗ g) = Σ_{a1·a2=a} (δ_{a1} ⊗ g) ⊗ (δ_{a2} ⊗ g)."""

    def test_z2_identity(self):
        """Δ(δ_0 ⊗ 0): a1+a2=0 mod 2 → {(0,0), (1,1)}."""
        summands = drinfeld_coproduct_summands(0, 0, Z2.elements, Z2.mul)
        # a1+a2 = 0 mod 2: (0,0) and (1,1)
        assert len(summands) == 2

    def test_z2_one(self):
        """Δ(δ_1 ⊗ 0): a1+a2=1 mod 2 → {(0,1), (1,0)}."""
        summands = drinfeld_coproduct_summands(1, 0, Z2.elements, Z2.mul)
        assert len(summands) == 2

    def test_z3_summand_count(self):
        """For Z/3, each coproduct has exactly 3 summands."""
        z3 = IntMod(3)
        for a in z3.elements:
            summands = drinfeld_coproduct_summands(a, 0, z3.elements, z3.mul)
            assert len(summands) == 3

    def test_coproduct_preserves_g(self):
        """All summands have the same g component."""
        z3 = IntMod(3)
        summands = drinfeld_coproduct_summands(1, 2, z3.elements, z3.mul)
        for (a1, g1), (a2, g2) in summands:
            assert g1 == 2
            assert g2 == 2


# ════════════════════════════════════════════════════════════════════
# Test: Equivalence properties
# ════════════════════════════════════════════════════════════════════

class TestEquivalenceProperties:
    """Test Z(Vec_G) ≅ Rep(D(G)) consistency checks."""

    def test_z2_count_match(self):
        """Z/2: |Irr(Z(Vec_G))| = |Irr(Rep(D(G)))| = 4."""
        assert drinfeld_double_simples_abelian(2) == 4
        assert drinfeld_double_dim(2) == 4  # = |G|² for abelian

    def test_s3_global_dim_match(self):
        """S₃: D² = |G|² on both sides."""
        assert drinfeld_double_dim(6) == 36

    def test_abelian_simples_eq_dim(self):
        """For abelian G: #simples = dim D(G) = |G|²."""
        for n in [1, 2, 3, 4, 5, 7]:
            assert drinfeld_double_simples_abelian(n) == drinfeld_double_dim(n)

    def test_hopf_antipode_well_defined(self):
        """Antipode is well-defined on all basis elements."""
        z3 = IntMod(3)
        # S maps basis elements to basis elements
        for a in z3.elements:
            for g in z3.elements:
                result = drinfeld_double_antipode(a, g, z3.inv, z3.conjugate)
                assert result[0] in z3.elements
                assert result[1] in z3.elements
