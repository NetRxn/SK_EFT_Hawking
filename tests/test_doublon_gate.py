"""Phase 5t Wave 9 — Tests for the doublon-gate experimental module.

Cross-checks ``src.experimental.doublon_gate`` against the
Lean-verified dimer core and the W6/W7 scalar claims. Every test
mirrors a Lean theorem or a structural invariant of the pipeline.
"""

from __future__ import annotations

import numpy as np
import pytest

from src.experimental.doublon_gate import (
    DimerSpectrum,
    bench_superexchange_bound,
    dimer_spectrum_at_U0,
    exact_diagonalize,
    gate_6x6_unitarity_witness,
    scaling_comparison_curves,
    swap_action_on_singlet,
)


class TestExactDiagonalization:
    @pytest.mark.parametrize("t, delta, U", [
        (1.0, 0.0, 0.0), (1.0, 2.0, 0.0), (0.7, -1.3, 2.0),
        (2.0, 1.0, -1.5), (-0.5, 2.5, 3.0), (1.5, 0.0, 5.0),
    ])
    def test_ED_returns_six_eigenvalues_full(self, t, delta, U):
        result = exact_diagonalize(t, delta, U)
        assert isinstance(result, DimerSpectrum)
        assert len(result.eigenvalues_6x6) == 6
        assert len(result.eigenvalues_3x3) == 3

    @pytest.mark.parametrize("t, delta, U", [
        (1.0, 0.0, 0.0), (1.0, 2.0, 0.0), (0.7, -1.3, 2.0),
        (2.0, 1.0, -1.5), (-0.5, 2.5, 3.0), (1.5, 0.0, 5.0),
    ])
    def test_ED_eigenvalues_ascending(self, t, delta, U):
        result = exact_diagonalize(t, delta, U)
        for i in range(len(result.eigenvalues_3x3) - 1):
            assert result.eigenvalues_3x3[i] <= result.eigenvalues_3x3[i + 1]
        for i in range(len(result.eigenvalues_6x6) - 1):
            assert result.eigenvalues_6x6[i] <= result.eigenvalues_6x6[i + 1]

    @pytest.mark.parametrize("t, delta, U", [
        (1.0, 0.0, 0.0), (0.7, -1.3, 2.0), (-0.5, 2.5, 3.0), (1.5, 0.0, 5.0),
    ])
    def test_ED_6x6_contains_three_zeros_and_3x3_block(self, t, delta, U):
        # H_full has three zero eigenvalues from the triplet states
        # (Lean T10a, T10b, T10c); the other three come from the 3×3
        # singlet block. So sorted 6×6 eigenvalues = sorted(3×3) ∪ {0, 0, 0}.
        result = exact_diagonalize(t, delta, U)
        combined = sorted(
            list(result.eigenvalues_3x3) + [0.0, 0.0, 0.0]
        )
        assert np.allclose(sorted(result.eigenvalues_6x6), combined, atol=1e-10)


class TestU0Spectrum:
    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.5, 1.3), (-2.0, 3.0), (1.5, -0.7),
    ])
    def test_U0_spectrum_matches_W4p(self, t, delta):
        # Lean W4p: spectrum at U=0 is {0, +gap, -gap} where
        # gap = √(delta² + 4·t²).
        gap = np.sqrt(delta**2 + 4.0 * t**2)
        expected = sorted([0.0, gap, -gap])
        actual = dimer_spectrum_at_U0(t, delta)
        assert np.allclose(actual, expected, atol=1e-10)


class TestScalingComparisonCurves:
    def test_scaling_curves_direct_exchange_meets_zero(self):
        # At U=0, E_plus = 2|t| (Lean W7a) and direct-exchange
        # approximation is exact: direct_linear(U=0) = 2|t|.
        t = 1.0
        curves = scaling_comparison_curves(t, np.array([0.0]))
        assert np.isclose(curves["E_plus"][0], 2.0 * abs(t))
        assert np.isclose(curves["direct_linear"][0], 2.0 * abs(t))

    def test_scaling_curves_E_plus_consistent(self):
        # E_plus curve matches closed-form: (U + √(U²+16t²))/2.
        t = 1.5
        Us = np.linspace(-5.0, 20.0, 50)
        curves = scaling_comparison_curves(t, Us)
        expected = (Us + np.sqrt(Us**2 + 16 * t**2)) / 2
        assert np.allclose(curves["E_plus"], expected)

    def test_scaling_curves_J_nan_at_zero(self):
        # J_leading = 4t²/U is undefined at U=0; scaling function uses nan.
        t = 1.0
        curves = scaling_comparison_curves(t, np.array([0.0, 1.0, 2.0]))
        assert np.isnan(curves["J_leading"][0])
        assert np.isclose(curves["J_leading"][1], 4.0 * t**2 / 1.0)
        assert np.isclose(curves["J_leading"][2], 4.0 * t**2 / 2.0)

    def test_scaling_curves_J_approaches_J_leading_at_large_U(self):
        # At large U, J(t, U) → 4t²/U (W7i).
        t = 1.0
        Us = np.array([100.0, 1000.0, 10000.0])
        curves = scaling_comparison_curves(t, Us)
        # Error should decrease as 1/U²
        for U, J, J_lead in zip(Us, curves["J"], curves["J_leading"]):
            # bound: |J - J_leading| ≤ 16 t⁴/U³
            assert abs(J - J_lead) <= 16.0 * t**4 / U**3 + 1e-12


class TestSwapActionOnSinglet:
    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
    ])
    def test_swap_action_sign_flip_on_dark(self, t, delta):
        result = swap_action_on_singlet(t, delta)
        assert np.allclose(
            result["U_times_dark"], -result["dark"], atol=1e-12
        )

    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
    ])
    def test_swap_action_identity_on_bright(self, t, delta):
        result = swap_action_on_singlet(t, delta)
        assert np.allclose(
            result["U_times_bright_plus"],
            result["bright_plus"], atol=1e-12,
        )
        assert np.allclose(
            result["U_times_bright_minus"],
            result["bright_minus"], atol=1e-12,
        )


class TestGate6x6Unitarity:
    @pytest.mark.parametrize("t, delta", [
        (1.0, 0.0), (1.0, 2.0), (0.7, -1.3), (2.0, 1.0), (-0.5, 2.5),
    ])
    def test_6x6_unitarity(self, t, delta):
        witness = gate_6x6_unitarity_witness(t, delta)
        assert witness["involution_err"] < 1e-10
        assert witness["orthogonal_err"] < 1e-10
        assert witness["det_minus_one_err"] < 1e-10


class TestSuperexchangeBoundBenchmark:
    def test_bench_superexchange_bound_respects_W7i(self):
        # Lean W7i: |J - 4t²/U| ≤ 16 t⁴ / U³ for U ≥ 4|t|, t ≠ 0.
        t = 1.0
        factors = np.linspace(1.0, 100.0, 50)
        result = bench_superexchange_bound(t, factors)
        for res, bound in zip(result["residual"], result["bound"]):
            assert res <= bound + 1e-12

    def test_bench_superexchange_bound_tightness(self):
        # At U = 4|t| (factor = 1), the residual is comparable to (but
        # still below) the bound — bound is asymptotically tight.
        t = 1.0
        result = bench_superexchange_bound(t, np.array([1.0]))
        # residual must be non-trivial (not zero) but below bound
        assert result["residual"][0] > 0
        assert result["residual"][0] < result["bound"][0]

    def test_bench_superexchange_bound_zero_t(self):
        # At t=0, both residual and bound are trivially zero.
        result = bench_superexchange_bound(0.0, np.array([1.0, 2.0]))
        assert np.allclose(result["residual"], 0.0)
        assert np.allclose(result["bound"], 0.0)
