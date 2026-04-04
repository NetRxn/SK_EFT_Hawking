"""Tests for Rokhlin bridge: "16 convergence" and with/without ν_R constraints.

Lean module: RokhlinBridge.lean (14 theorems, 0 axioms, 0 sorry)
"""

import pytest
import math
from src.core.formulas import (
    rokhlin_sixteen_convergence,
    generation_constraints_with_without_nu_R,
)
from src.core.constants import SM_FERMION_DATA


class TestSixteenConvergence:
    """Test the four independent appearances of 16."""

    def test_all_sixteen(self):
        """All four contexts give 16."""
        info = rokhlin_sixteen_convergence()
        assert info['sm_weyl'] == 16
        assert info['z16_bordism'] == 16
        assert info['rokhlin_signature'] == 16
        assert info['kitaev_16fold'] == 16
        assert info['all_equal'] is True

    def test_bott_decomposition(self):
        """16 = 8 × 2 (Bott period × Pfaffian)."""
        info = rokhlin_sixteen_convergence()
        assert info['bott_decomposition']['period'] == 8
        assert info['bott_decomposition']['pfaffian'] == 2
        assert info['bott_decomposition']['product'] == 16

    def test_sm_weyl_matches_fermion_data(self):
        """SM Weyl count from constants matches the "16"."""
        total = sum(f['components'] for f in SM_FERMION_DATA.values())
        assert total == rokhlin_sixteen_convergence()['sm_weyl']


class TestWithWithoutNuR:
    """Test generation constraints with and without right-handed neutrinos."""

    def test_n3_with_nu_R(self):
        """N_f=3 with ν_R: passes both constraints."""
        r = generation_constraints_with_without_nu_R(3)
        assert r['with_nu_R']['all_ok'] is True

    def test_n3_without_nu_R(self):
        """N_f=3 without ν_R: fails Z₁₆ (3 is not divisible by 16)."""
        r = generation_constraints_with_without_nu_R(3)
        assert r['without_nu_R']['z16_ok'] is False
        assert r['without_nu_R']['all_ok'] is False

    def test_n48_without_nu_R(self):
        """N_f=48 without ν_R: passes both (lcm(16,3) = 48)."""
        r = generation_constraints_with_without_nu_R(48)
        assert r['without_nu_R']['z16_ok'] is True
        assert r['without_nu_R']['modular_ok'] is True
        assert r['without_nu_R']['all_ok'] is True

    def test_minimal_with_nu_R(self):
        """Minimal N_f with ν_R is 3."""
        r = generation_constraints_with_without_nu_R(1)
        assert r['minimal_with_nu_R'] == 3

    def test_minimal_without_nu_R(self):
        """Minimal N_f without ν_R is 48 = lcm(16, 3)."""
        r = generation_constraints_with_without_nu_R(1)
        assert r['minimal_without_nu_R'] == 48
        assert math.lcm(16, 3) == 48

    def test_z16_always_cancels_with_nu_R(self):
        """With ν_R, Z₁₆ anomaly cancels for ALL N_f."""
        for n in range(1, 100):
            r = generation_constraints_with_without_nu_R(n)
            assert r['with_nu_R']['z16_ok'] is True

    def test_only_mod3_pass_with_nu_R(self):
        """With ν_R, only multiples of 3 satisfy all constraints."""
        for n in range(1, 50):
            r = generation_constraints_with_without_nu_R(n)
            assert r['with_nu_R']['all_ok'] == (n % 3 == 0)

    def test_only_mod48_pass_without_nu_R(self):
        """Without ν_R, only multiples of 48 satisfy all constraints."""
        for n in range(1, 100):
            r = generation_constraints_with_without_nu_R(n)
            assert r['without_nu_R']['all_ok'] == (n % 48 == 0)

    def test_observed_n3_implies_nu_R(self):
        """N_f=3 observed → ν_R must exist (since 3 fails without ν_R)."""
        r = generation_constraints_with_without_nu_R(3)
        assert r['with_nu_R']['all_ok'] is True
        assert r['without_nu_R']['all_ok'] is False
