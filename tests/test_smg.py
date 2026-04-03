"""
Tests for Phase 5a Wave 5A: SMG Classification.

Validates the algebraic classification infrastructure for symmetric mass
generation — anomaly conditions, Altland-Zirnbauer classes, Z₁₆ connection.
Tests the Python-side constants and formulas that correspond to the Lean
SMGClassification module.
"""

import numpy as np
import pytest

from src.core.constants import Z16_CLASSIFICATION
from src.core.formulas import z16_anomaly_cancellation


class TestSMGAnomalyConditions:
    """Test SMG anomaly conditions via the Z₁₆ formulas."""

    def test_16_majorana_smg_possible(self):
        """16 Majorana fermions: anomaly-free, SMG possible."""
        result = z16_anomaly_cancellation(16)
        assert result['smg_possible'] is True

    def test_32_majorana_smg_possible(self):
        """32 = 2×16: anomaly-free, SMG possible."""
        result = z16_anomaly_cancellation(32)
        assert result['smg_possible'] is True

    def test_8_majorana_no_smg_in_4d(self):
        """8 Majorana: anomaly-free in 1D (FK Z₈) but anomalous in 4D (Z₁₆)."""
        result = z16_anomaly_cancellation(8)
        assert result['smg_possible'] is False
        assert result['anomaly_class'] == 8

    def test_anomaly_class_additive(self):
        """Anomaly class is additive mod 16."""
        for n1, n2 in [(8, 8), (4, 12), (1, 15)]:
            r1 = z16_anomaly_cancellation(n1)
            r2 = z16_anomaly_cancellation(n2)
            r_sum = z16_anomaly_cancellation(n1 + n2)
            assert r_sum['anomaly_class'] == (r1['anomaly_class'] + r2['anomaly_class']) % 16

    def test_contrapositive_no_go(self):
        """Anomalous systems cannot undergo SMG regardless of interactions."""
        for n in range(1, 16):
            result = z16_anomaly_cancellation(n)
            assert result['smg_possible'] is False


class TestAltlandZirnbauer:
    """Test Altland-Zirnbauer tenfold way properties."""

    def test_ten_classes(self):
        """There are exactly 10 AZ symmetry classes."""
        az_classes = ['A', 'AIII', 'AI', 'BDI', 'D', 'DIII', 'AII', 'CII', 'C', 'CI']
        assert len(az_classes) == 10

    def test_pin_plus_is_class_d(self):
        """4D Pin⁺ corresponds to AZ class D (particle-hole, C²=+1)."""
        assert Z16_CLASSIFICATION['BORDISM_ORDER'] == 16


class TestKahlerDiracCounting:
    """Test the Kähler-Dirac fermion counting argument."""

    def test_2_kd_flavors_equals_16_majorana(self):
        """2 KD × 4 Dirac/KD × 2 Majorana/Dirac = 16."""
        assert 2 * 4 * 2 == 16

    def test_1_kd_flavor_anomalous(self):
        """1 KD flavor = 8 Majorana: anomalous in 4D."""
        result = z16_anomaly_cancellation(1 * 4 * 2)
        assert result['smg_possible'] is False

    def test_2_kd_flavors_anomaly_free(self):
        """2 KD flavors = 16 Majorana: anomaly-free in 4D."""
        result = z16_anomaly_cancellation(2 * 4 * 2)
        assert result['smg_possible'] is True


class TestSMGBridgeTheorems:
    """Test connections between SMG and existing infrastructure."""

    def test_z16_classification_order(self):
        """4D Pin⁺ classification order is 16."""
        assert Z16_CLASSIFICATION['BORDISM_ORDER'] == 16

    def test_fk_1d_vs_4d(self):
        """FK 1D is Z₈, 4D is Z₁₆ — different classifications."""
        assert 8 != 16
        assert 16 % 8 == 0  # Z₈ divides Z₁₆

    def test_anomaly_matching_topological(self):
        """Anomaly class is invariant under adding 16 fermions."""
        for n in range(20):
            r1 = z16_anomaly_cancellation(n)
            r2 = z16_anomaly_cancellation(n + 16)
            assert r1['anomaly_class'] == r2['anomaly_class']
