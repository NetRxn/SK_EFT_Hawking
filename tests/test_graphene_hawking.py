"""Tests for graphene Hawking temperature predictions (Phase 5w Wave 3).

Tests cover:
- Surface gravity and adiabaticity parameter
- Dissipative correction negligibility (key finding: 11 orders below dispersive)
- Effective temperature with corrections
- EFT validity bounds (D < 1)
- Noise spectrum shape
- Cross-validation with existing BEC correction formulas
"""

import numpy as np
import pytest

from src.graphene.hawking_predictions import (
    graphene_surface_gravity,
    graphene_adiabaticity,
    graphene_damping_rate_horizon,
    graphene_hawking_prediction,
    graphene_noise_spectrum,
    all_platform_predictions,
)
from src.core.formulas import (
    hawking_temperature,
    dispersive_correction,
    first_order_correction,
)
from src.core.constants import GRAPHENE_PLATFORMS


class TestSurfaceGravity:
    def test_dean_positive(self):
        kappa = graphene_surface_gravity('Dean_bilayer_nozzle')
        assert kappa > 0

    def test_dean_order_of_magnitude(self):
        kappa = graphene_surface_gravity('Dean_bilayer_nozzle')
        assert 1e11 < kappa < 1e13


class TestAdiabaticity:
    def test_dean_perturbative(self):
        """Dean nozzle D < 1: EFT is valid."""
        D = graphene_adiabaticity('Dean_bilayer_nozzle')
        assert 0 < D < 1

    def test_monolayer_50nm_nonperturbative(self):
        """50nm monolayer D > 1: EFT breaks down."""
        D = graphene_adiabaticity('Monolayer_50nm')
        assert D > 1


class TestDampingRate:
    def test_positive(self):
        Gamma_H = graphene_damping_rate_horizon('Dean_bilayer_nozzle')
        assert Gamma_H > 0

    def test_much_smaller_than_kappa(self):
        """Γ_H << κ: dissipative correction is negligible."""
        Gamma_H = graphene_damping_rate_horizon('Dean_bilayer_nozzle')
        kappa = graphene_surface_gravity('Dean_bilayer_nozzle')
        assert Gamma_H / kappa < 1e-10


class TestHawkingPrediction:
    def test_dean_T_H_positive(self):
        pred = graphene_hawking_prediction('Dean_bilayer_nozzle')
        assert pred['T_H_K'] > 0

    def test_dean_T_eff_positive(self):
        pred = graphene_hawking_prediction('Dean_bilayer_nozzle')
        assert pred['T_eff_K'] > 0

    def test_dean_correction_small(self):
        """Total correction < 5% for Dean nozzle."""
        pred = graphene_hawking_prediction('Dean_bilayer_nozzle')
        assert abs(pred['correction_pct']) < 5.0

    def test_dissipative_negligible_vs_dispersive(self):
        """Key finding: δ_diss << δ_disp by 11 orders of magnitude."""
        pred = graphene_hawking_prediction('Dean_bilayer_nozzle')
        assert abs(pred['delta_diss']) < abs(pred['delta_disp']) * 1e-8

    def test_dispersive_correction_negative(self):
        """Dispersive correction is negative (cooling)."""
        pred = graphene_hawking_prediction('Dean_bilayer_nozzle')
        assert pred['delta_disp'] < 0

    def test_T_eff_less_than_T_H(self):
        """With negative dispersive correction, T_eff < T_H."""
        pred = graphene_hawking_prediction('Dean_bilayer_nozzle')
        assert pred['T_eff_K'] < pred['T_H_K']

    def test_monolayer_50nm_breaks_eft(self):
        """50nm monolayer: D > 1, T_eff goes negative (EFT invalid)."""
        pred = graphene_hawking_prediction('Monolayer_50nm')
        assert pred['D'] > 1
        assert pred['T_eff_K'] < 0  # EFT breakdown signal


class TestNoiseSpectrum:
    def test_returns_arrays(self):
        spec = graphene_noise_spectrum('Dean_bilayer_nozzle')
        assert 'omega' in spec
        assert 'n_hawking' in spec
        assert len(spec['omega']) == 200

    def test_hawking_occupation_decreasing(self):
        """n_Hawking decreases with frequency (thermal spectrum)."""
        spec = graphene_noise_spectrum('Dean_bilayer_nozzle')
        # Check monotonically decreasing after peak
        n = spec['n_hawking']
        peak_idx = np.argmax(n)
        assert np.all(np.diff(n[peak_idx:]) <= 0)

    def test_thermal_dominates_hawking(self):
        """At T_ambient >> T_H, thermal noise dominates Hawking signal."""
        spec = graphene_noise_spectrum('Dean_bilayer_nozzle')
        # Near ω_H, thermal occupation >> Hawking occupation
        mid = len(spec['omega']) // 2
        assert spec['n_thermal'][mid] > spec['n_hawking'][mid]


class TestAllPlatforms:
    def test_three_acoustic_platforms(self):
        """Three platforms (excluding p-n junction) produce predictions."""
        preds = all_platform_predictions()
        assert len(preds) == 3

    def test_all_have_required_keys(self):
        preds = all_platform_predictions()
        required = {'T_H_K', 'T_eff_K', 'delta_disp', 'delta_diss', 'D',
                     'Gamma_H_s1', 'kappa_s1'}
        for name, pred in preds.items():
            for key in required:
                assert key in pred, f"{name} missing {key}"


class TestCrossValidation:
    def test_T_H_matches_generic_formula(self):
        """T_H from graphene module matches generic hawking_temperature()."""
        pred = graphene_hawking_prediction('Dean_bilayer_nozzle')
        T_H_generic = hawking_temperature(pred['kappa_s1'])
        assert abs(pred['T_H_K'] - T_H_generic) / T_H_generic < 1e-10

    def test_delta_disp_matches_generic(self):
        """δ_disp from graphene module matches generic dispersive_correction()."""
        pred = graphene_hawking_prediction('Dean_bilayer_nozzle')
        delta_generic = dispersive_correction(pred['D'])
        assert abs(pred['delta_disp'] - delta_generic) < 1e-15

    def test_delta_diss_matches_generic(self):
        """δ_diss from graphene module matches generic first_order_correction()."""
        pred = graphene_hawking_prediction('Dean_bilayer_nozzle')
        delta_generic = first_order_correction(pred['Gamma_H_s1'], pred['kappa_s1'])
        assert abs(pred['delta_diss'] - delta_generic) < 1e-20
