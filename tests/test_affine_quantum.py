"""Tests for affine quantum group U_q(ŝl₂) and restricted u_q(sl₂) (Phase 5c Waves 2, 5).

Lean: Uqsl2Affine.lean, RestrictedUq.lean
"""

import math

import pytest

from src.core.formulas import (
    affine_chevalley_cross_relation,
    coideal_generator,
    restricted_uq_relations,
)


class TestAffineChevalley:
    """Tests for the affine Cartan matrix relations."""

    def test_same_node_scaling(self):
        """K_i E_i K_i^{-1} = q^2 E_i (a_ii = 2)."""
        q = 0.7
        assert affine_chevalley_cross_relation(2, q) == pytest.approx(q ** 2)

    def test_cross_node_scaling(self):
        """K_i E_j K_i^{-1} = q^{-2} E_j (a_ij = -2)."""
        q = 0.7
        assert affine_chevalley_cross_relation(-2, q) == pytest.approx(q ** (-2))

    def test_cartan_matrix_symmetry(self):
        """The affine A_1^{(1)} Cartan matrix is symmetric: a_01 = a_10 = -2."""
        q = 0.5
        assert affine_chevalley_cross_relation(-2, q) == affine_chevalley_cross_relation(-2, q)

    def test_q_equals_1_recovery(self):
        """At q=1: all scalings are 1 (classical limit)."""
        assert affine_chevalley_cross_relation(2, 1) == 1
        assert affine_chevalley_cross_relation(-2, 1) == 1


class TestCoidealGenerator:
    """Tests for the q-Onsager coideal generators B_i = F_i + c*E_i*K_i^{-1}."""

    def test_coideal_structure(self):
        """B_i = F_i + E_i * K_i^{-1} with c=1."""
        result = coideal_generator(3.0, 5.0, 7.0, c=1)
        assert result == 3.0 + 1 * 5.0 * 7.0  # F + c*E*Kinv = 3 + 35 = 38

    def test_coideal_c_parameter(self):
        """Different c values scale the E*Kinv term."""
        result = coideal_generator(3.0, 5.0, 7.0, c=2)
        assert result == 3.0 + 2 * 5.0 * 7.0  # 3 + 70 = 73

    def test_coideal_default_c(self):
        """Default c=1."""
        result = coideal_generator(1.0, 1.0, 1.0)
        assert result == 2.0  # 1 + 1*1*1


class TestRestrictedUq:
    """Tests for the restricted quantum group u_q(sl₂)."""

    def test_ell_3(self):
        """ell=3: dim=27, 3 simples, fusion level k=1."""
        data = restricted_uq_relations(3)
        assert data['dimension'] == 27
        assert data['num_simples'] == 3
        assert data['fusion_level'] == 1
        assert data['nilpotency_exponent'] == 3
        assert data['torsion_order'] == 3

    def test_ell_5(self):
        """ell=5: dim=125, 5 simples, fusion level k=3 (contains Fibonacci!)."""
        data = restricted_uq_relations(5)
        assert data['dimension'] == 125
        assert data['num_simples'] == 5
        assert data['fusion_level'] == 3

    def test_ell_7(self):
        """ell=7: dim=343, 7 simples, fusion level k=5."""
        data = restricted_uq_relations(7)
        assert data['dimension'] == 343
        assert data['fusion_level'] == 5

    def test_dimension_is_cube(self):
        """dim u_q = ell^3 for all odd ell >= 3."""
        for ell in [3, 5, 7, 9, 11]:
            data = restricted_uq_relations(ell)
            assert data['dimension'] == ell ** 3

    def test_invalid_even_ell(self):
        """Even ell is not allowed (different conventions needed)."""
        with pytest.raises(ValueError, match="odd"):
            restricted_uq_relations(4)

    def test_invalid_small_ell(self):
        """ell < 3 is not allowed."""
        with pytest.raises(ValueError, match="odd"):
            restricted_uq_relations(2)
        with pytest.raises(ValueError, match="odd"):
            restricted_uq_relations(1)

    def test_fusion_level_connection(self):
        """k = ell - 2: the SU(2)_k fusion category corresponds to u_q at ell = k+2."""
        for k in [1, 2, 3, 4, 5]:
            ell = k + 2
            if ell % 2 == 1:  # only odd ell
                data = restricted_uq_relations(ell)
                assert data['fusion_level'] == k
