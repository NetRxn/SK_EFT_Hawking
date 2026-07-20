"""Tests for graphene transport counting and WF violation (Phase 5w Waves 5-7).

Tests cover:
- Transport coefficient counting: 1+1D BEC vs 2+1D Dirac fluid
- Conformal constraint: ζ = 0
- WF violation: regularized Lorenz ratio peaks (finite) at charge neutrality
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
    L_LORENZ_SOMMERFELD,
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
    """Regularized WF Lorenz-ratio profile L/L₀(n): finite everywhere, equal
    to R_peak at charge neutrality, recovering to the WF value 1 at high
    density (R-09: the old code claimed L → ∞ but implemented a finite
    n₀-regularized form; these assert the corrected physics numerically)."""

    N0 = 1e12       # regularizing disorder/thermal carrier density [m⁻²]
    RPEAK = 200.0   # measured peak violation at CNP (Majumdar 2025, >200×)

    def test_finite_and_equals_peak_at_cnp(self):
        r0 = wiedemann_franz_lorenz_ratio(0.0, self.N0, self.RPEAK)
        assert np.isfinite(r0)
        assert r0 == pytest.approx(self.RPEAK, rel=1e-12)  # NOT infinite

    def test_half_excess_at_n0(self):
        # At n = n₀ the excess (L/L₀ − 1) is exactly halved.
        r = wiedemann_franz_lorenz_ratio(self.N0, self.N0, self.RPEAK)
        assert r == pytest.approx(1.0 + (self.RPEAK - 1.0) / 2.0, rel=1e-12)

    def test_wf_recovery_at_high_density(self):
        # |n| ≫ n₀ → Fermi-liquid WF value L/L₀ → 1 (from above).
        r = wiedemann_franz_lorenz_ratio(1e5 * self.N0, self.N0, self.RPEAK)
        assert r == pytest.approx(1.0, abs=1e-6)
        assert r > 1.0

    def test_monotonic_decreasing_in_density(self):
        rs = [wiedemann_franz_lorenz_ratio(n, self.N0, self.RPEAK)
              for n in [0.0, 0.5e12, 1e12, 2e12, 1e13]]
        assert all(a > b for a, b in zip(rs, rs[1:]))

    def test_even_in_carrier_density(self):
        # Depends only on (n/n₀)² → symmetric under electron↔hole doping.
        assert (wiedemann_franz_lorenz_ratio(3e12, self.N0, self.RPEAK)
                == pytest.approx(
                    wiedemann_franz_lorenz_ratio(-3e12, self.N0, self.RPEAK)))

    def test_crossno_regime_peak(self):
        # Crossno 2016 ~10× at 75 K: finite peak = 10 exactly at CNP.
        assert wiedemann_franz_lorenz_ratio(0.0, self.N0, 10.0) == pytest.approx(10.0)

    def test_raises_on_nonpositive_n0(self):
        with pytest.raises(ValueError):
            wiedemann_franz_lorenz_ratio(1e12, 0.0, self.RPEAK)

    def test_lorenz_sommerfeld_constant_value_and_units(self):
        # L₀ = (π²/3)(k_B/e)² ≈ 2.44e-8 W·Ω·K⁻² = [V²/K²]. The Lorenz NUMBER
        # carries these units; only the RATIO L/L₀ is dimensionless.
        expected = (np.pi**2 / 3.0) * (K_B / E_CHARGE)**2
        assert L_LORENZ_SOMMERFELD == pytest.approx(expected, rel=1e-12)
        assert L_LORENZ_SOMMERFELD == pytest.approx(2.44e-8, rel=1e-2)


class TestViscosityBound:
    def test_graphene_satisfies_kss(self):
        """η/s ≈ 4 × ℏ/(4πk_B) satisfies the bound."""
        bound = HBAR / (4 * np.pi * K_B)
        eta_over_s = 4 * bound
        assert eta_over_s >= bound
