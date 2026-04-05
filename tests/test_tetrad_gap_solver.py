"""Tests for the tetrad gap solver and observables (Phase 5d Wave 2).

Validates:
1. Gap curve computation and phase diagram
2. Cross-validation between integral and V_eff G_c
3. Vladimirov-Diakonov comparison (G_c is O(1) in lattice units)
4. Binder cumulant limits
5. Observable sanity checks
"""

import numpy as np
import pytest

from src.adw.tetrad_gap_solver import (
    compute_gap_curve,
    compute_phase_diagram,
    cross_validate_Gc,
    gap_vs_vladimirov_diakonov,
)
from src.adw.tetrad_observables import (
    binder_cumulant,
    metric_order_parameter,
    susceptibility_from_correlator,
)


# ══════════════════════════════════════════════════════
# Gap curve
# ══════════════════════════════════════════════════════


class TestGapCurve:
    """Tests for the Δ*(G) curve computation."""

    def test_basic_curve(self):
        """Curve computes without error."""
        result = compute_gap_curve(np.pi, N_f=2, n_points=50)
        assert len(result.G_values) == 50
        assert len(result.Delta_values) == 50
        assert result.G_c > 0

    def test_subcritical_zero(self):
        """Below G_c, all Δ = 0."""
        result = compute_gap_curve(np.pi, N_f=2, G_max_ratio=0.99, n_points=20)
        assert np.all(result.Delta_values == 0)

    def test_supercritical_positive(self):
        """Above G_c, Δ > 0."""
        result = compute_gap_curve(np.pi, N_f=2, G_min_ratio=1.5, G_max_ratio=5, n_points=20)
        assert np.all(result.Delta_values > 0)

    def test_monotone(self):
        """Δ*(G) is monotonically increasing in the supercritical regime."""
        result = compute_gap_curve(np.pi, N_f=2, G_min_ratio=1.2, G_max_ratio=5, n_points=50)
        for i in range(len(result.Delta_values) - 1):
            assert result.Delta_values[i] <= result.Delta_values[i + 1] + 1e-10


# ══════════════════════════════════════════════════════
# Cross-validation
# ══════════════════════════════════════════════════════


class TestCrossValidation:
    """Tests that integral and V_eff formulations agree."""

    def test_Gc_match(self):
        """G_c from both formulations must match exactly."""
        cv = cross_validate_Gc()
        assert cv['match']
        assert abs(cv['ratio'] - 1.0) < 1e-10

    def test_Gc_match_various_params(self):
        """G_c matches for various Λ and N_f."""
        for Lambda in [1.0, np.pi, 10.0]:
            for N_f in [1, 2, 4]:
                cv = cross_validate_Gc(Lambda, N_f)
                assert cv['match'], f"G_c mismatch at Λ={Lambda}, N_f={N_f}"


# ══════════════════════════════════════════════════════
# Vladimirov-Diakonov comparison
# ══════════════════════════════════════════════════════


class TestVladDiakonov:
    """Tests for comparison with VD 2D lattice results."""

    def test_Gc_order_one(self):
        """G_c should be O(1) in lattice units (not fine-tuned)."""
        vd = gap_vs_vladimirov_diakonov(np.pi, N_f=2)
        assert vd['is_order_one'], (
            f"G_c·Λ² = {vd['G_c_lattice_units']:.2f} should be O(1)"
        )

    def test_explicit_value(self):
        """G_c·Λ² = 8π²/N_f for lattice cutoff."""
        vd = gap_vs_vladimirov_diakonov(np.pi, N_f=2)
        expected = 8 * np.pi**2 / 2  # 8π²/N_f
        assert abs(vd['G_c_lattice_units'] - expected) < 1e-8


# ══════════════════════════════════════════════════════
# Binder cumulant
# ══════════════════════════════════════════════════════


class TestBinderCumulant:
    """Tests for the Binder cumulant U₄."""

    def test_ordered_limit(self):
        """In the ordered phase (sharp peak), U₄ → 2/3."""
        O_ordered = np.ones(10000) + 0.001 * np.random.randn(10000)
        U4 = binder_cumulant(O_ordered)
        assert abs(U4 - 2/3) < 0.01

    def test_disordered_limit(self):
        """In the disordered phase (Gaussian), U₄ → 0."""
        np.random.seed(42)
        O_disordered = np.random.randn(100000)
        U4 = binder_cumulant(O_disordered)
        assert abs(U4) < 0.05

    def test_zero_input(self):
        """All-zero input returns 0."""
        assert binder_cumulant(np.zeros(100)) == 0.0

    def test_range(self):
        """U₄ ∈ [0, 2/3] for physical inputs."""
        np.random.seed(123)
        for _ in range(10):
            O = np.abs(np.random.randn(1000))
            U4 = binder_cumulant(O)
            assert -0.1 <= U4 <= 2/3 + 0.01


# ══════════════════════════════════════════════════════
# Metric order parameter
# ══════════════════════════════════════════════════════


class TestMetricOrderParameter:
    """Tests for the vestigial metric order parameter."""

    def test_zero_when_uncorrelated(self):
        """O_met = 0 when E^a E^b is uncorrelated."""
        n = 1000
        # Random independent tetrad configs: ⟨EE⟩ = ⟨E⟩⟨E⟩
        np.random.seed(42)
        tetrad_avg = np.random.randn(4) * 0.1
        tetrad_sq = np.array([
            np.outer(tetrad_avg, tetrad_avg) + 0.001 * np.random.randn(4, 4)
            for _ in range(n)
        ])
        O_met = metric_order_parameter(tetrad_sq, tetrad_avg)
        assert abs(O_met) < 0.1, f"O_met = {O_met} should be ~0 for uncorrelated"

    def test_nonzero_when_correlated(self):
        """O_met ≠ 0 when connected correlator is nonzero."""
        n = 1000
        np.random.seed(42)
        tetrad_avg = np.zeros(4)
        # Large connected correlator
        tetrad_sq = np.array([
            np.diag([1.0, 0.5, 0.5, 0.5]) + 0.01 * np.random.randn(4, 4)
            for _ in range(n)
        ])
        O_met = metric_order_parameter(tetrad_sq, tetrad_avg)
        assert abs(O_met) > 0.1, f"O_met = {O_met} should be nonzero"


# ══════════════════════════════════════════════════════
# Susceptibility from correlator
# ══════════════════════════════════════════════════════


class TestSusceptibility:
    """Tests for χ = V·Σ C(r)."""

    def test_positive_for_positive_correlator(self):
        """χ > 0 when C(r) > 0."""
        L = 4
        C = np.array([1.0, 0.5, 0.25])  # Decaying correlator
        chi = susceptibility_from_correlator(C, L)
        assert chi > 0

    def test_scaling_with_volume(self):
        """χ scales with V = L⁴."""
        C = np.array([1.0, 0.5, 0.25])
        chi4 = susceptibility_from_correlator(C, L=4)
        chi8 = susceptibility_from_correlator(C, L=8)
        assert abs(chi8 / chi4 - 8**4 / 4**4) < 0.01
