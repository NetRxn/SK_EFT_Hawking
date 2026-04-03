"""
Tests for Phase 5a Wave 1B: Onsager Algebra Contraction to su(2).

Validates:
  - Inönü-Wigner contraction rescaling
  - Commutator vanishing at ε=0
  - su(2) recovery (3-dimensional target)
  - Coefficient consistency with Davies presentation
"""

import numpy as np
import pytest

from src.core.constants import ONSAGER_ALGEBRA
from src.core.formulas import onsager_contraction


class TestContractionRescaling:
    """Test the Inönü-Wigner contraction rescaling."""

    def test_rescaling_nonzero_epsilon(self):
        """At ε ≠ 0, rescaled generators are nonzero."""
        result = onsager_contraction(0.5, 1.0, 2.0)
        assert result['A0_rescaled'] == 0.5 * 1.0
        assert result['A1_rescaled'] == 0.5 * 2.0

    def test_rescaling_unit_epsilon(self):
        """At ε = 1, rescaled generators equal originals."""
        result = onsager_contraction(1.0, 3.0, 7.0)
        assert result['A0_rescaled'] == 3.0
        assert result['A1_rescaled'] == 7.0

    def test_commutator_coefficient_scales_quadratically(self):
        """[ε·A₀, ε·A₁] = ε²·4·G₁ — coefficient is ε²·4."""
        for eps in [0.1, 0.5, 1.0, 2.0]:
            result = onsager_contraction(eps, 1.0, 1.0)
            assert np.isclose(result['commutator_coeff'], eps ** 2 * 4)

    def test_commutator_coefficient_at_unit(self):
        """At ε = 1: commutator coefficient = 4 (Davies AA coefficient)."""
        result = onsager_contraction(1.0, 1.0, 1.0)
        assert result['commutator_coeff'] == ONSAGER_ALGEBRA['DAVIES_AA_COEFF']


class TestContractionLimit:
    """Test the ε → 0 limit behavior."""

    def test_zero_epsilon_generators_vanish(self):
        """At ε = 0, rescaled generators are zero."""
        result = onsager_contraction(0.0, 5.0, 10.0)
        assert result['A0_rescaled'] == 0.0
        assert result['A1_rescaled'] == 0.0

    def test_zero_epsilon_commutator_vanishes(self):
        """At ε = 0, commutator coefficient = 0² · 4 = 0."""
        result = onsager_contraction(0.0, 1.0, 1.0)
        assert result['commutator_coeff'] == 0.0

    def test_vanishes_flag_at_zero(self):
        """vanishes_at_zero is True when ε = 0."""
        result = onsager_contraction(0.0, 1.0, 1.0)
        assert result['vanishes_at_zero'] is True

    def test_vanishes_flag_at_nonzero(self):
        """vanishes_at_zero is False when ε ≠ 0."""
        result = onsager_contraction(0.5, 1.0, 1.0)
        assert result['vanishes_at_zero'] is False

    def test_small_epsilon_commutator_small(self):
        """For small ε, commutator coefficient is O(ε²) — very small."""
        result = onsager_contraction(1e-6, 1.0, 1.0)
        assert result['commutator_coeff'] < 1e-10


class TestSU2Recovery:
    """Test that the contraction target is su(2)."""

    def test_su2_dim_is_3(self):
        """Contraction target su(2) is 3-dimensional."""
        result = onsager_contraction(1.0, 1.0, 1.0)
        assert result['su2_dim'] == 3

    def test_su2_dim_matches_constants(self):
        """su(2) dimension matches SL2_DIM in constants."""
        result = onsager_contraction(1.0, 1.0, 1.0)
        assert result['su2_dim'] == ONSAGER_ALGEBRA['SL2_DIM']

    def test_su2_dim_independent_of_epsilon(self):
        """The target dimension doesn't depend on ε."""
        for eps in [0.0, 0.01, 1.0, 100.0]:
            result = onsager_contraction(eps, 1.0, 1.0)
            assert result['su2_dim'] == 3


class TestCoefficientConsistency:
    """Test coefficient relationships between contraction and Davies."""

    def test_commutator_uses_davies_aa(self):
        """Commutator coefficient at ε=1 equals DAVIES_AA_COEFF = 4."""
        result = onsager_contraction(1.0, 1.0, 1.0)
        assert result['commutator_coeff'] == 4

    def test_dg_from_contraction(self):
        """DG_COEFF = 16 = (DAVIES_AA)² = 4² — consistent with contraction."""
        aa = ONSAGER_ALGEBRA['DAVIES_AA_COEFF']
        dg = ONSAGER_ALGEBRA['DG_COEFF']
        assert dg == aa ** 2
