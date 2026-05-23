"""Phase 6t Wave 8 Stage 6 — Solovay-Kitaev compiler smoke tests.

Numerical sanity checks on the Lean-verified quantitative Solovay-Kitaev
length-bound + the Dawson-Nielsen exponent. These tests verify the
PYTHON-SIDE mirror of constants declared in:

  - lean/SKEFTHawking/FKLW/SolovayKitaevLengthBound.lean
    (skLengthConst, skLengthExponent, skLengthBaseCase, skBalancedDecompCost)
  - lean/SKEFTHawking/FKLW/SolovayKitaevQuantitative.lean
    (solovayKitaev_dawson_nielsen_quantitative_fibonacci headline)
  - lean/SKEFTHawking/FKLW/FibonacciEpsilonNet.lean (ε₀-net ε₀ = 1/8388608)

The Wave 7 reference-compiler native-extraction smoke test (running
`lake env lean --run scripts/SKCompilerCLI.lean` and asserting braid-word
outputs match the worked-example corpus) is GATED on the deferred
Wave 7 closeout (constructive F,G extraction + closed-form SU(2) exp).
Until that ships, this file exercises only the polylogarithmic length
formula and Dawson-Nielsen exponent properties.
"""

import math

import numpy as np
import pytest

from src.core.visualizations import (
    SK_BALANCED_DECOMP_COST,
    SK_LENGTH_BASE_CASE,
    SK_LENGTH_CONST,
    SK_LENGTH_EXPONENT,
    fig_fibonacci_braid_word_t_gate_example,
    fig_sk_length_bound_curve,
)


class TestDawsonNielsenExponent:
    """SolovayKitaevLengthBound.skLengthExponent = log 5 / log(3/2)."""

    def test_dawson_nielsen_exponent_value(self):
        """skLengthExponent = log 5 / log(3/2) ≈ 3.9694."""
        expected = math.log(5) / math.log(3 / 2)
        assert math.isclose(SK_LENGTH_EXPONENT, expected, rel_tol=1e-12)

    def test_dawson_nielsen_exponent_in_open_interval_3_4(self):
        """Lean: three_lt_skLengthExponent ∧ skLengthExponent_lt_four."""
        assert 3.0 < SK_LENGTH_EXPONENT < 4.0

    def test_dawson_nielsen_exponent_approx_3_97(self):
        """Numerical value mirrors the Lean docstring '≈ 3.97'."""
        assert math.isclose(SK_LENGTH_EXPONENT, 3.9694, abs_tol=1e-3)


class TestSolovayKitaevLengthConstants:
    """SolovayKitaevLengthBound.lean artifact constants."""

    def test_sk_length_const_positive(self):
        """Lean: skLengthConst_pos."""
        assert SK_LENGTH_CONST > 0
        assert SK_LENGTH_CONST == 1000.0

    def test_sk_length_base_case_positive(self):
        assert SK_LENGTH_BASE_CASE > 0
        assert SK_LENGTH_BASE_CASE == 100.0

    def test_sk_balanced_decomp_cost_positive(self):
        assert SK_BALANCED_DECOMP_COST > 0
        assert SK_BALANCED_DECOMP_COST == 100.0


class TestSkLengthBoundFormula:
    """L(ε) := skLengthConst · (log(1/ε))^skLengthExponent.

    The Lean headline ``solovayKitaev_dawson_nielsen_quantitative_fibonacci``
    asserts this as the polylogarithmic length bound on the level-
    ``skLevel_polylog ε`` braid-word output of the Solovay-Kitaev compiler.
    These tests verify the formula is well-defined and monotonic over the
    physical precision range ε ∈ (0, 1].
    """

    def _length(self, eps: float) -> float:
        return SK_LENGTH_CONST * (math.log(1.0 / eps)) ** SK_LENGTH_EXPONENT

    def test_length_at_eps_1eM6(self):
        """At ε = 1e-6, length is finite + positive + matches ≈ 3.36e7."""
        length = self._length(1e-6)
        assert length > 0
        assert math.isfinite(length)
        # log(1e6)^3.9694 ≈ 13.816^3.9694 ≈ 33600 → L ≈ 3.36e7
        assert 3.0e7 < length < 4.0e7

    def test_length_monotone_decreasing_in_epsilon(self):
        """L(ε) is strictly decreasing in ε for ε ∈ (0, e⁻¹)."""
        eps_grid = np.logspace(-12, -1, 50)
        lengths = [self._length(e) for e in eps_grid]
        for i in range(len(lengths) - 1):
            assert lengths[i] > lengths[i + 1], (
                f"L({eps_grid[i]:.2e}) = {lengths[i]:.2e} should be > "
                f"L({eps_grid[i + 1]:.2e}) = {lengths[i + 1]:.2e}"
            )

    def test_length_dominates_linear_log_at_small_eps(self):
        """L(ε) > c·log(1/ε) for ε small enough (since exponent > 1)."""
        for eps in [1e-3, 1e-6, 1e-9, 1e-12]:
            log_inv = math.log(1.0 / eps)
            length = self._length(eps)
            assert length > SK_LENGTH_CONST * log_inv

    def test_length_dominated_by_quartic_log(self):
        """L(ε) ≤ skLengthConst · (log(1/ε))^4 since exponent < 4."""
        for eps in [1e-3, 1e-6, 1e-9, 1e-12]:
            log_inv = math.log(1.0 / eps)
            length = self._length(eps)
            quartic = SK_LENGTH_CONST * log_inv**4
            assert length <= quartic


class TestEpsilonNetGroundFloor:
    """FibonacciEpsilonNet.lean: ε₀ = 1/8388608 = 1/(8·1024²)."""

    EPSILON_ZERO = 1.0 / 8388608.0  # = 1.1920928955078125e-7

    def test_epsilon_zero_definition(self):
        """ε₀ = 1/(8·K_compose²) with K_compose = 1024."""
        K_compose = 1024.0
        expected = 1.0 / (8.0 * K_compose**2)
        assert math.isclose(self.EPSILON_ZERO, expected, rel_tol=1e-15)

    def test_epsilon_zero_in_physical_range(self):
        """ε₀ is a small positive precision (≈ 1.2e-7)."""
        assert 1e-8 < self.EPSILON_ZERO < 1e-6


class TestSKFigures:
    """Stage 8 figure generators are well-formed."""

    def test_fig_sk_length_bound_curve_renders(self):
        fig = fig_sk_length_bound_curve()
        assert fig is not None
        assert len(fig.data) >= 3  # Dawson-Nielsen + 2 reference curves

    def test_fig_sk_length_bound_curve_axis_logarithmic(self):
        fig = fig_sk_length_bound_curve()
        layout = fig.layout
        # The xaxis is log-precision; yaxis log-length.
        assert layout.xaxis.type == "log"
        assert layout.yaxis.type == "log"

    def test_fig_fibonacci_braid_word_t_gate_example_renders(self):
        fig = fig_fibonacci_braid_word_t_gate_example()
        assert fig is not None
        # 3 strand baselines + 8 letters × 2 arcs each = 19 traces
        assert len(fig.data) == 19


# ─────────────────────────────────────────────────────────────────────────────
# Wave 7 native-extraction reference-compiler smoke test (DEFERRED).
#
# The roadmap (§3.Wave 8 Stage 6) prescribes invocation of
# `lake env lean --run scripts/SKCompilerCLI.lean` on a worked-example corpus
# (T-gate, H-gate, S-gate, π-rotations + stress-test) and asserting:
#   - error bound ‖ρ_Fib(output) - target‖ < ε numerically
#   - length(output) ≤ skLengthConst · (log(1/ε))^skLengthExponent
#
# This test is GATED on the Wave 7 native-extraction closeout, which in turn
# requires:
#   (1) constructive (F, G) extraction (no Classical.choose) in
#       SU2BalancedCommutator.balanced_commutator_general_axis_lie_traceless
#   (2) closed-form SU(2) exponential exp(iθ·n̂·σ̄) = cos(θ)·I + i·sin(θ)·n̂·σ̄
#       to make `expIsu2 F` computable
# Both items are deferred (cf. memory: project_phase6t_path_a_active_2026_05_22).
# ─────────────────────────────────────────────────────────────────────────────


@pytest.mark.slow
@pytest.mark.skip(
    reason=(
        "Wave 7 native-extraction smoke test gated on constructive (F, G) "
        "extraction + closed-form SU(2) exp; not yet shipped. See roadmap "
        "§17.2 #5."
    )
)
def test_sk_compiler_native_corpus_smoke():
    """Wave 8 Stage 6 reference-compiler corpus smoke test (DEFERRED).

    When unblocked, runs ``lake env lean --run scripts/SKCompilerCLI.lean``
    on the T/H/S/π-rotation worked-example corpus and asserts output braid
    words satisfy both error and length bounds. See roadmap §3.Wave 8
    Stage 6 for the full specification.
    """
    raise NotImplementedError
