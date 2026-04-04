"""Tests for modular invariance constraint: c₋ ≡ 0 mod 24.

Validates the framing anomaly derivation from the Dedekind eta function's
T-transformation phase, and the connection to the generation constraint.

Lean module: ModularInvarianceConstraint.lean
"""

import pytest
import cmath
import math
from src.core.formulas import (
    modular_t_phase,
    dedekind_eta_origin_of_24,
    wang_bridge_central_charge,
    sm_generation_constraint,
)


class TestModularTPhase:
    """Test the T-transformation phase e^{2πi·c₋/24}."""

    def test_c_minus_24_invariant(self):
        """c₋ = 24: phase = e^{2πi} = 1 (modular invariant)."""
        result = modular_t_phase(24)
        assert result['is_modular_invariant'] is True
        assert result['satisfies_framing_anomaly'] is True

    def test_c_minus_48_invariant(self):
        """c₋ = 48: phase = e^{4πi} = 1."""
        result = modular_t_phase(48)
        assert result['is_modular_invariant'] is True

    def test_c_minus_8_not_invariant(self):
        """c₋ = 8 (one generation): phase ≠ 1 (NOT modular invariant)."""
        result = modular_t_phase(8)
        assert result['is_modular_invariant'] is False
        assert result['c_minus_mod_24'] == 8

    def test_c_minus_16_not_invariant(self):
        """c₋ = 16 (two generations): phase ≠ 1."""
        result = modular_t_phase(16)
        assert result['is_modular_invariant'] is False

    def test_c_minus_0_invariant(self):
        """c₋ = 0: trivially modular invariant."""
        result = modular_t_phase(0)
        assert result['is_modular_invariant'] is True

    def test_phase_is_root_of_unity(self):
        """Phase magnitude is always 1 (it's a root of unity)."""
        for c in range(50):
            result = modular_t_phase(c)
            assert abs(result['phase_magnitude'] - 1.0) < 1e-10

    def test_phase_period_24(self):
        """Phase repeats with period 24."""
        for c in range(50):
            p1 = modular_t_phase(c)['phase']
            p2 = modular_t_phase(c + 24)['phase']
            assert abs(p1 - p2) < 1e-10

    def test_sm_three_generations(self):
        """SM with 3 generations: c₋ = 24, modular invariant."""
        result = modular_t_phase(8 * 3)
        assert result['c_minus'] == 24
        assert result['is_modular_invariant'] is True

    def test_sm_one_generation_fails(self):
        """SM with 1 generation: c₋ = 8, NOT modular invariant."""
        result = modular_t_phase(8 * 1)
        assert result['is_modular_invariant'] is False


class TestFramingAnomalyConstraint:
    """Test 24 | c₋ as necessary and sufficient for modular invariance."""

    def test_divisible_by_24_iff_invariant(self):
        """c₋ % 24 == 0 ↔ modular invariant (for c₋ = 0..100)."""
        for c in range(101):
            result = modular_t_phase(c)
            assert result['satisfies_framing_anomaly'] == result['is_modular_invariant'], \
                f"c₋={c}: framing={result['satisfies_framing_anomaly']}, invariant={result['is_modular_invariant']}"

    def test_24_factorization(self):
        """24 = 8 × 3: the origin of the generation constraint."""
        assert 24 == 8 * 3
        assert math.gcd(8, 3) == 1  # coprime

    def test_constraint_sharpness(self):
        """24 | 8·3 but 24 ∤ 8·1 and 24 ∤ 8·2."""
        assert (8 * 3) % 24 == 0
        assert (8 * 1) % 24 != 0
        assert (8 * 2) % 24 != 0


class TestFullChain:
    """Test the complete chain: η → 24 → c₋ = 8N_f → 3 | N_f."""

    def test_chain_n3(self):
        """N_f=3: 16 Weyl → c₋=8 → c₋=24 → 24|24 → 3|3 ✓."""
        bridge = wang_bridge_central_charge(16)
        assert bridge['c_minus_per_gen'] == 8.0
        phase = modular_t_phase(8 * 3)
        assert phase['is_modular_invariant'] is True
        gen = sm_generation_constraint(3)
        assert gen['satisfies_generation_constraint'] is True

    def test_chain_n6(self):
        """N_f=6: c₋=48, 24|48, 3|6 ✓."""
        phase = modular_t_phase(8 * 6)
        assert phase['is_modular_invariant'] is True
        gen = sm_generation_constraint(6)
        assert gen['satisfies_generation_constraint'] is True

    def test_chain_n4_fails(self):
        """N_f=4: c₋=32, 24∤32, 3∤4 ✗."""
        phase = modular_t_phase(8 * 4)
        assert phase['is_modular_invariant'] is False
        gen = sm_generation_constraint(4)
        assert gen['satisfies_generation_constraint'] is False

    def test_only_multiples_of_3(self):
        """For N_f = 1..20, only multiples of 3 are modular invariant."""
        for n in range(1, 21):
            phase = modular_t_phase(8 * n)
            gen = sm_generation_constraint(n)
            assert phase['is_modular_invariant'] == gen['satisfies_generation_constraint'], \
                f"N_f={n}: modular={phase['is_modular_invariant']}, gen={gen['satisfies_generation_constraint']}"


class TestDedekindEtaOrigin:
    """Test the explanation of the "24" origin."""

    def test_zeta_minus_one(self):
        """ζ(-1) = -1/12 (Ramanujan summation)."""
        info = dedekind_eta_origin_of_24()
        assert info['zeta_minus_one'] == -1/12

    def test_factorization(self):
        """24 = 8 × 3."""
        info = dedekind_eta_origin_of_24()
        assert info['factorization_24']['8'] == 'c₋ per generation'
        assert info['factorization_24']['3'] == 'N_f constraint'
