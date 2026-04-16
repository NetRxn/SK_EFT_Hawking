"""Tests for graphene Hawking noise spectrum (Phase 5w Wave 4).

Tests cover:
- Spectrum computation and structure
- Detection protocol feasibility
- Physical consistency (Planck shape, thermal dominance)
- Cross-platform comparison
"""

import numpy as np
import pytest

from src.graphene.wkb_spectrum import (
    compute_graphene_spectrum,
    detection_protocol_summary,
)


class TestSpectrumComputation:
    def test_returns_correct_shape(self):
        spec = compute_graphene_spectrum('Dean_bilayer_nozzle', n_points=100)
        assert len(spec.omega) == 100
        assert len(spec.S_hawking) == 100
        assert len(spec.S_thermal) == 100

    def test_frequencies_positive(self):
        spec = compute_graphene_spectrum('Dean_bilayer_nozzle')
        assert np.all(spec.omega > 0)

    def test_hawking_occupation_positive(self):
        spec = compute_graphene_spectrum('Dean_bilayer_nozzle')
        assert np.all(spec.n_hawking > 0)

    def test_thermal_dominates(self):
        """T_ambient >> T_H means S_thermal >> S_hawking everywhere."""
        spec = compute_graphene_spectrum('Dean_bilayer_nozzle')
        assert np.all(spec.S_thermal > spec.S_hawking)

    def test_snr_positive(self):
        spec = compute_graphene_spectrum('Dean_bilayer_nozzle')
        assert np.all(spec.snr_per_bin > 0)

    def test_omega_H_in_GHz_range(self):
        """Characteristic Hawking frequency should be in GHz range."""
        spec = compute_graphene_spectrum('Dean_bilayer_nozzle')
        omega_H_GHz = spec.omega_H / (2 * np.pi * 1e9)
        assert 1 < omega_H_GHz < 500  # 1-500 GHz


class TestDetectionProtocol:
    def test_dean_eft_valid(self):
        proto = detection_protocol_summary('Dean_bilayer_nozzle')
        assert proto['eft_valid'] is True

    def test_dean_dispersive_dominates(self):
        proto = detection_protocol_summary('Dean_bilayer_nozzle')
        assert proto['corrections']['dominant'] == 'dispersive'

    def test_integration_time_finite(self):
        proto = detection_protocol_summary('Dean_bilayer_nozzle')
        assert proto['detection']['integration_time_cumulative_s'] < np.inf

    def test_integration_time_feasible(self):
        """Integration time should be < 1 hour for Dean nozzle."""
        proto = detection_protocol_summary('Dean_bilayer_nozzle')
        assert proto['detection']['feasible']

    def test_freq_window_reasonable(self):
        """Detection band should be in GHz range."""
        proto = detection_protocol_summary('Dean_bilayer_nozzle')
        band = proto['detection']['optimal_freq_band']
        assert 'GHz' in band

    def test_T_H_much_larger_than_BEC(self):
        proto = detection_protocol_summary('Dean_bilayer_nozzle')
        assert proto['comparison_to_BEC']['T_H_ratio'] > 1e8


class TestPhysicalConsistency:
    def test_hawking_decreasing_at_high_freq(self):
        """n_Hawking decreases at high frequency (Boltzmann suppression)."""
        spec = compute_graphene_spectrum('Dean_bilayer_nozzle')
        # At high ω, n_Hawking should decrease
        high_freq_half = spec.n_hawking[len(spec.n_hawking)//2:]
        assert high_freq_half[-1] < high_freq_half[0]

    def test_planck_approximation_at_low_freq(self):
        """At low ω, n_Hawking ≈ n_Planck (corrections small for Dean)."""
        spec = compute_graphene_spectrum('Dean_bilayer_nozzle')
        # First few bins: Hawking should be within 10% of Planck
        ratio = spec.n_hawking[:5] / spec.n_planck[:5]
        assert np.all(np.abs(ratio - 1.0) < 0.1)

    def test_S_thermal_flat(self):
        """Johnson-Nyquist noise is frequency-independent (white noise)."""
        spec = compute_graphene_spectrum('Dean_bilayer_nozzle')
        assert np.all(np.abs(spec.S_thermal - spec.S_thermal[0]) < 1e-30)


class TestMonolayerComparison:
    def test_monolayer_100nm_higher_TH(self):
        """Monolayer 100nm has higher T_H than Dean bilayer."""
        spec_dean = compute_graphene_spectrum('Dean_bilayer_nozzle')
        spec_mono = compute_graphene_spectrum('Monolayer_100nm')
        assert spec_mono.T_H_K > spec_dean.T_H_K

    def test_monolayer_50nm_eft_breakdown(self):
        """50nm monolayer: D > 1, EFT invalid."""
        spec = compute_graphene_spectrum('Monolayer_50nm')
        assert spec.D > 1
