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
    """Threshold coefficient comparison only, not full-model equivalence."""

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


class TestGapCurveNumericalContract:
    def test_zero_singleton_and_constant_ranges_are_valid(self):
        single = compute_gap_curve(1.0, G_min_ratio=0, G_max_ratio=10, n_points=1)
        assert single.G_values.tolist() == [0.0]
        assert single.Delta_values.tolist() == [0.0]
        constant = compute_gap_curve(1.0, G_min_ratio=2, G_max_ratio=2, n_points=3)
        assert np.all(constant.G_values == constant.G_values[0])
        assert np.all(constant.Delta_values == constant.Delta_values[0])
        assert constant.Delta_values[0] > 0

    def test_wrapper_reaches_true_above_cutoff_witness(self):
        ratio = 1 / (1 - 4 * np.log(5 / 4))
        result = compute_gap_curve(1.0, N_f=2, G_min_ratio=ratio, G_max_ratio=ratio, n_points=1)
        assert result.Delta_values[0] == pytest.approx(2, rel=2e-10)
        full = compute_gap_curve(np.pi, G_min_ratio=0, G_max_ratio=10, n_points=12)
        assert full.Delta_values[0] == 0
        assert full.Delta_values[-1] > full.Lambda

    @pytest.mark.parametrize("kwargs", [
        {"n_points": 0}, {"n_points": True}, {"n_points": 1.5},
        {"G_min_ratio": -1}, {"G_max_ratio": np.inf},
        {"G_min_ratio": 3, "G_max_ratio": 2}, {"G_min_ratio": True},
    ])
    def test_invalid_curve_domains(self, kwargs):
        with pytest.raises(ValueError):
            compute_gap_curve(1.0, **kwargs)

    def test_canonical_refusal_is_not_replaced_with_zero(self, monkeypatch):
        import src.adw.tetrad_gap_solver as solver
        def refused(*args, **kwargs):
            raise ArithmeticError("controlled canonical refusal")
        monkeypatch.setattr(solver, "tetrad_gap_solution", refused)
        with pytest.raises(ArithmeticError, match="controlled canonical refusal"):
            solver.compute_gap_curve(1.0, n_points=1)


class TestGapCurveOriginalScalarAdmission:
    @pytest.mark.parametrize("sign", [1, -1])
    def test_original_rational_ratio_is_refused_not_replaced_by_zero(self, sign):
        from fractions import Fraction
        epsilon = Fraction(sign, 10**400)
        # Small cutoff gives a large finite Gc; the exact endpoint product
        # can be representable even though epsilon itself is not binary64.
        with pytest.raises(ValueError):
            compute_gap_curve(1e-150, G_min_ratio=epsilon, G_max_ratio=epsilon, n_points=1)

    def test_actual_wrapper_preserves_true_zeros_and_positive_subnormal_ratio(self):
        from fractions import Fraction
        for zero in (0.0, -0.0, Fraction(0, 1)):
            result = compute_gap_curve(1.0, G_min_ratio=zero, G_max_ratio=zero, n_points=1)
            assert result.G_values.tolist() == [0.0]
            assert result.Delta_values.tolist() == [0.0]
        smallest = np.nextafter(0.0, 1.0)
        result = compute_gap_curve(1e-150, G_min_ratio=smallest, G_max_ratio=smallest, n_points=1)
        assert np.isfinite(result.G_values[0]) and result.G_values[0] > 0
        assert result.Delta_values[0] == 0  # Genuine subcritical root, not zeroed input.
