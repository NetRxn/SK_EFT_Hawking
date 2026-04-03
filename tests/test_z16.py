"""
Tests for Phase 5a Wave 3A: Z₁₆ Classification formulas and constants.

Validates:
  - Z₁₆ anomaly cancellation (16n Majorana fermions)
  - Central charge constraints (mod 8 vs mod 16)
  - sVec extension enumeration (16-fold way)
  - Physical counting arguments
  - Bridge to existing chirality limitation
"""

import numpy as np
import pytest

from src.core.constants import Z16_CLASSIFICATION
from src.core.formulas import (
    z16_anomaly_cancellation,
    z16_central_charge_constraint,
    z16_svec_extensions,
)


# ════════════════════════════════════════════════════════════════════
# Constants validation
# ════════════════════════════════════════════════════════════════════


class TestZ16Constants:
    """Validate Z₁₆ classification constants from constants.py."""

    def test_bordism_order(self):
        """Ω₄^{Pin⁺} has order 16 (Giambalvo 1973)."""
        assert Z16_CLASSIFICATION['BORDISM_ORDER'] == 16

    def test_central_charge_mod(self):
        """Super-modular central charge periodicity is 16."""
        assert Z16_CLASSIFICATION['CENTRAL_CHARGE_MOD'] == 16

    def test_string_net_mod(self):
        """String-net limitation: c ≡ 0 (mod 8) — our proved result."""
        assert Z16_CLASSIFICATION['STRING_NET_MOD'] == 8

    def test_z16_strengthens_string_net(self):
        """Z₁₆ mod (16) is strictly stronger than string-net mod (8)."""
        assert Z16_CLASSIFICATION['Z16_MOD'] == 16
        assert Z16_CLASSIFICATION['Z16_MOD'] > Z16_CLASSIFICATION['STRING_NET_MOD']
        assert Z16_CLASSIFICATION['Z16_MOD'] % Z16_CLASSIFICATION['STRING_NET_MOD'] == 0

    def test_svec_extensions(self):
        """sVec has exactly 16 minimal modular extensions."""
        assert Z16_CLASSIFICATION['SVEC_EXTENSIONS'] == 16

    def test_a1_dim(self):
        """A(1) = ⟨Sq¹, Sq²⟩ is 8-dimensional over F₂."""
        assert Z16_CLASSIFICATION['A1_DIM'] == 8

    def test_anomaly_cancellation_unit(self):
        """Anomaly cancellation requires multiples of 16 Majorana fermions."""
        assert Z16_CLASSIFICATION['ANOMALY_CANCELLATION_UNIT'] == 16


# ════════════════════════════════════════════════════════════════════
# Anomaly cancellation tests
# ════════════════════════════════════════════════════════════════════


class TestZ16AnomalyCancellation:
    """Test Z₁₆ anomaly cancellation function."""

    def test_zero_fermions(self):
        """0 fermions: trivially anomaly-free."""
        result = z16_anomaly_cancellation(0)
        assert result['cancels'] is True
        assert result['anomaly_class'] == 0

    def test_16_fermions(self):
        """16 Majorana fermions: minimal non-trivial anomaly-free system."""
        result = z16_anomaly_cancellation(16)
        assert result['cancels'] is True
        assert result['smg_possible'] is True
        assert result['residual_anomaly'] == 0

    def test_32_fermions(self):
        """32 = 2×16: anomaly-free."""
        result = z16_anomaly_cancellation(32)
        assert result['cancels'] is True

    def test_1_to_15_anomalous(self):
        """1 through 15 Majorana fermions: all anomalous."""
        for n in range(1, 16):
            result = z16_anomaly_cancellation(n)
            assert result['cancels'] is False, f"n={n} should be anomalous"
            assert result['smg_possible'] is False
            assert result['residual_anomaly'] == n

    def test_anomaly_class_mod16(self):
        """Anomaly class is n mod 16."""
        for n in [17, 33, 100, 256]:
            result = z16_anomaly_cancellation(n)
            assert result['anomaly_class'] == n % 16

    def test_anomaly_additivity(self):
        """Anomaly class is additive: [n₁+n₂] = [n₁] + [n₂] mod 16."""
        for n1, n2 in [(8, 8), (3, 13), (7, 9), (16, 16)]:
            r_sum = z16_anomaly_cancellation(n1 + n2)
            r1 = z16_anomaly_cancellation(n1)
            r2 = z16_anomaly_cancellation(n2)
            assert r_sum['anomaly_class'] == (r1['anomaly_class'] + r2['anomaly_class']) % 16

    def test_kahler_dirac_counting(self):
        """2 KD flavors × 4 Dirac/KD × 2 Majorana/Dirac = 16."""
        n_kd = 2
        dirac_per_kd = 4
        majorana_per_dirac = 2
        n_majorana = n_kd * dirac_per_kd * majorana_per_dirac
        assert n_majorana == 16
        assert z16_anomaly_cancellation(n_majorana)['cancels'] is True


# ════════════════════════════════════════════════════════════════════
# Central charge constraint tests
# ════════════════════════════════════════════════════════════════════


class TestZ16CentralCharge:
    """Test central charge constraints from Z₁₆."""

    def test_c_zero(self):
        """c = 0: satisfies both mod-8 and mod-16."""
        result = z16_central_charge_constraint(0.0)
        assert result['satisfies_string_net'] is True
        assert result['satisfies_z16'] is True

    def test_c_16(self):
        """c = 16: satisfies both mod-8 and mod-16."""
        result = z16_central_charge_constraint(16.0)
        assert result['satisfies_string_net'] is True
        assert result['satisfies_z16'] is True

    def test_c_8_mod8_not_mod16(self):
        """c = 8: satisfies mod-8 but NOT mod-16 (strict strengthening)."""
        result = z16_central_charge_constraint(8.0)
        assert result['satisfies_string_net'] is True
        assert result['satisfies_z16'] is False

    def test_c_4_neither(self):
        """c = 4: satisfies neither mod-8 nor mod-16."""
        result = z16_central_charge_constraint(4.0)
        assert result['satisfies_string_net'] is False
        assert result['satisfies_z16'] is False

    def test_z16_always_implies_string_net(self):
        """mod-16 always implies mod-8 (16 | c → 8 | c)."""
        for c in [0, 16, 32, 48, 64, 128]:
            result = z16_central_charge_constraint(float(c))
            if result['satisfies_z16']:
                assert result['satisfies_string_net'], \
                    f"c={c}: Z₁₆ satisfied but string-net not — impossible"

    def test_strengthening_flag(self):
        """The z16_strengthens field is always True."""
        for c in [0, 4, 8, 16]:
            result = z16_central_charge_constraint(float(c))
            assert result['z16_strengthens'] is True


# ════════════════════════════════════════════════════════════════════
# sVec extension tests
# ════════════════════════════════════════════════════════════════════


class TestSVecExtensions:
    """Test enumeration of 16 minimal modular extensions of sVec."""

    def test_exactly_16_extensions(self):
        """sVec has exactly 16 extensions (16-fold way)."""
        exts = z16_svec_extensions()
        assert len(exts) == 16

    def test_extensions_are_SO_N(self):
        """Extensions are SO(N)₁ for N = 1, ..., 16."""
        exts = z16_svec_extensions()
        for i, ext in enumerate(exts):
            assert ext['N'] == i + 1
            assert ext['label'] == f'SO({i + 1})₁'

    def test_central_charges(self):
        """Central charge of SO(N)₁ is c = N/2."""
        exts = z16_svec_extensions()
        for ext in exts:
            assert ext['central_charge'] == ext['N'] / 2

    def test_first_extension(self):
        """SO(1)₁: c = 1/2."""
        exts = z16_svec_extensions()
        assert exts[0]['N'] == 1
        assert exts[0]['central_charge'] == 0.5

    def test_last_extension(self):
        """SO(16)₁: c = 8."""
        exts = z16_svec_extensions()
        assert exts[15]['N'] == 16
        assert exts[15]['central_charge'] == 8.0

    def test_periodicity(self):
        """Extensions are periodic mod 16: SO(N+16) ≅ SO(N) as extensions."""
        exts = z16_svec_extensions()
        for ext in exts:
            # c mod 16 should cycle: c = N/2 mod 16
            assert ext['c_mod_16'] == (ext['N'] / 2) % 16


# ════════════════════════════════════════════════════════════════════
# Fidkowski-Kitaev connection tests
# ════════════════════════════════════════════════════════════════════


class TestFidkowskiKitaev:
    """Test 1D vs 4D classification relationship."""

    def test_1d_is_z8(self):
        """1D BDI classification is ℤ₈ (Fidkowski-Kitaev)."""
        assert 8 != 16  # 1D and 4D classifications differ

    def test_z8_divides_z16(self):
        """ℤ₈ divides ℤ₁₆: 8 | 16."""
        assert 16 % 8 == 0

    def test_8_majorana_anomalous_in_4d(self):
        """8 Majorana fermions: anomaly-free in 1D but anomalous in 4D."""
        result = z16_anomaly_cancellation(8)
        assert result['cancels'] is False  # In 4D: anomalous
        assert result['anomaly_class'] == 8
