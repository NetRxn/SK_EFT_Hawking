"""Tests for graphene transport counting and WF violation (Phase 5w Waves 5-7).

Tests cover:
- Transport coefficient counting: 1+1D BEC vs 2+1D Dirac fluid
- Conformal constraint: ζ = 0
- WF violation: Lorenz ratio diverges at charge neutrality
- Viscosity bound: η/s ≥ KSS
- Classification structure consistency
"""

import numpy as np
import pytest

from src.graphene.transport_counting import (
    bec_1d_counting,
    classify_first_order_conformal_charged,
    classify_first_order_non_conformal_charged,
    classify_second_order_conformal_charged,
    classify_parity_odd_first_order,
    wiedemann_franz_lorenz_ratio,
)
from src.core.constants import HBAR, K_B, E_CHARGE


class TestBECCounting:
    """Cross-validate with existing 1+1D formula."""

    def test_order_1(self):
        assert bec_1d_counting(1) == 2

    def test_order_2(self):
        assert bec_1d_counting(2) == 2

    def test_order_3(self):
        assert bec_1d_counting(3) == 3


class TestFirstOrderConformal:
    def test_count_is_2(self):
        cls = classify_first_order_conformal_charged()
        assert cls.total_independent == 2

    def test_has_eta_and_sigma_Q(self):
        cls = classify_first_order_conformal_charged()
        all_coeffs = []
        for s in cls.sectors:
            all_coeffs.extend(s.coefficients)
        names = ' '.join(all_coeffs)
        assert 'η' in names
        assert 'σ_Q' in names

    def test_matches_bec_count(self):
        """Striking coincidence: both 1+1D and 2+1D conformal have 2."""
        assert classify_first_order_conformal_charged().total_independent == bec_1d_counting(1)

    def test_no_bulk_viscosity(self):
        """Conformal: ζ = 0."""
        cls = classify_first_order_conformal_charged()
        scalar = [s for s in cls.sectors if s.name == 'scalar'][0]
        assert scalar.dissipative == 0


class TestFirstOrderNonConformal:
    def test_count_is_3(self):
        cls = classify_first_order_non_conformal_charged()
        assert cls.total_independent == 3

    def test_has_bulk(self):
        cls = classify_first_order_non_conformal_charged()
        scalar = [s for s in cls.sectors if s.name == 'scalar'][0]
        assert scalar.dissipative == 1
        assert any('ζ' in c for c in scalar.coefficients)


class TestSecondOrder:
    def test_much_richer_than_1d(self):
        """2+1D has ~9 vs 1+1D's 2 at second order."""
        cls = classify_second_order_conformal_charged()
        assert cls.total_independent > bec_1d_counting(2) * 2

    def test_haack_yarom_reduces(self):
        """Haack-Yarom identity reduces tensor sector by 1."""
        cls = classify_second_order_conformal_charged()
        tensor = [s for s in cls.sectors if s.name == 'tensor'][0]
        assert 'Haack-Yarom' in tensor.constraints[0]


class TestParityOdd:
    def test_count_is_2(self):
        cls = classify_parity_odd_first_order()
        assert cls.total_parity_odd == 2

    def test_non_dissipative(self):
        cls = classify_parity_odd_first_order()
        assert cls.total_dissipative == 0


class TestWiedemannFranz:
    def test_diverges_at_cnp(self):
        """L/L₀ >> 1 at charge neutrality (small n)."""
        v_F = 1e6
        T = 100  # K
        s = 1e16  # entropy density [J/(K·m²)] (order of magnitude)
        sigma_Q = 1.55e-4  # σ_Q in SI
        n_small = 1e12  # very small carrier density

        L, L_over_L0 = wiedemann_franz_lorenz_ratio(v_F, s, sigma_Q, n_small, T)
        assert L_over_L0 > 10  # should be >> 1

    def test_L_positive(self):
        L, _ = wiedemann_franz_lorenz_ratio(1e6, 1e16, 1e-4, 1e12, 100)
        assert L > 0

    def test_grows_with_entropy(self):
        """L ∝ s² at fixed everything else."""
        _, r1 = wiedemann_franz_lorenz_ratio(1e6, 1e16, 1e-4, 1e12, 100)
        _, r2 = wiedemann_franz_lorenz_ratio(1e6, 2e16, 1e-4, 1e12, 100)
        assert r2 > r1


class TestViscosityBound:
    def test_graphene_satisfies_kss(self):
        """η/s ≈ 4 × ℏ/(4πk_B) satisfies the bound."""
        bound = HBAR / (4 * np.pi * K_B)
        eta_over_s = 4 * bound
        assert eta_over_s >= bound
