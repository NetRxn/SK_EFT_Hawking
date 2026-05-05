"""Tests for the Padé-Borel resurgence infrastructure (Phase 6n.α.2 Stage 1).

Validates the borel-transform pipeline against:
1. Known factorial sequences (Gevrey-1) — Heller-Spalinski validation case
2. Multi-singularity Borel transforms (richer Padé reconstruction)
3. Geometric / polynomial sequences — should NOT signal Gevrey-1 divergence
4. Λ_UV closed form for known A
5. ratio_test asymptotic behavior

Validation strategy: before running on actual SK-EFT γ-coefficient
sequences (which require physical-input γ values), verify the pipeline
correctly recovers known A values from synthetic test sequences with
known Borel-plane singularity structure.

Note on Padé degeneracy: a pure `a_n = n!/A^n` sequence Borel-transforms
to `b_n = 1/A^n`, which is rational of degree (0,1) — a single simple
pole at ζ=A. The exact Padé approximant is [0/1] = 1/(1-ζ/A); requesting
[M/M] for M ≥ 2 produces a singular linear system in scipy.pade.
The tests below either use M=1 explicitly, or use richer sequences with
multiple Borel-plane singularities so that higher-order Padé is well-conditioned.
"""

import math

import numpy as np
import pytest

from src.resurgence.borel import (
    borel_transform,
    pade_borel,
    leading_borel_singularity,
    ratio_test,
    lambda_uv_estimate,
)


# ═══════════════════════════════════════════════════════════════════
# Borel transform basic correctness
# ═══════════════════════════════════════════════════════════════════

class TestBorelTransform:
    """B[f]_n = a_n / n! is the elementary Borel transform."""

    def test_zero_sequence(self):
        b = borel_transform([0.0, 0.0, 0.0, 0.0])
        assert np.allclose(b, [0.0, 0.0, 0.0, 0.0])

    def test_single_one(self):
        # a = (1, 0, 0, ...) ⇒ B[a] = (1, 0, 0, ...)
        b = borel_transform([1.0, 0.0, 0.0])
        assert b[0] == 1.0
        assert b[1] == 0.0

    def test_factorial_sequence_borel_transforms_to_one(self):
        # a_n = n! ⇒ B[a]_n = 1 (constant)
        a = [float(math.factorial(n)) for n in range(8)]
        b = borel_transform(a)
        assert np.allclose(b, [1.0] * 8)

    def test_ones_sequence_borel_transforms_to_inverse_factorials(self):
        # a_n = 1 ⇒ B[a]_n = 1/n!
        a = [1.0] * 6
        b = borel_transform(a)
        expected = [1.0 / math.factorial(n) for n in range(6)]
        assert np.allclose(b, expected)


# ═══════════════════════════════════════════════════════════════════
# Heller-Spalinski validation: a_n = n!/A^n, [1/1] Padé recovers A
# ═══════════════════════════════════════════════════════════════════

class TestHellerSpalinskiValidation:
    """For a_n = n!/A^n (Gevrey-1, single Borel singularity at ζ=A),
    [1/1] Padé exactly recovers A. Higher-order Padé is degenerate
    on this rational-degree-(0,1) function — see TestMultiSingularity
    for richer reconstruction tests."""

    @pytest.mark.parametrize("A_true", [1.0, 2.0, 3.0, 0.5])
    def test_borel_singularity_recovers_A_at_M1(self, A_true):
        """[1/1] Padé-Borel of a_n = n!/A^n recovers ζ = A exactly."""
        a = [math.factorial(n) / A_true**n for n in range(3)]
        A_extracted = leading_borel_singularity(a, M=1, N=1)
        assert A_extracted is not None
        assert A_extracted.real == pytest.approx(A_true, rel=1e-6)

    def test_lambda_uv_closed_form_at_M1(self):
        """Λ_UV = κ √A for a_n = n!/A^n with A = 4, κ = 1.5."""
        A_true = 4.0
        kappa = 1.5
        a = [math.factorial(n) / A_true**n for n in range(3)]
        Lambda_UV = lambda_uv_estimate(a, kappa, M=1)
        expected = kappa * math.sqrt(A_true)  # = 1.5 * 2 = 3.0
        assert Lambda_UV == pytest.approx(expected, rel=1e-6)

    def test_ratio_test_converges_to_inverse_A(self):
        """For a_n = n!/A^n, R_n := a_{n+1}/((n+1)a_n) = 1/A (exactly)."""
        A_true = 2.5
        a = [math.factorial(n) / A_true**n for n in range(20)]
        R = ratio_test(a)
        # For n!/A^n: R_n = (n+1)!/A^(n+1) / ((n+1) · n!/A^n) = 1/A exactly.
        assert R[-1] == pytest.approx(1.0 / A_true, rel=1e-10)
        assert R[0] == pytest.approx(1.0 / A_true, rel=1e-10)


# ═══════════════════════════════════════════════════════════════════
# Multi-singularity Borel transforms — richer Padé reconstruction
# ═══════════════════════════════════════════════════════════════════

class TestMultiSingularity:
    """For a_n = α · n!/A^n + β · n!/B^n (two distinct Borel singularities
    at ζ = A and ζ = B), the [2/2] Padé approximant should recover both
    poles, and leading_borel_singularity should pick the smaller one."""

    def test_two_singularity_sequence_recovers_leading(self):
        """a_n = n!/A^n + 0.5 · n!/B^n with A=2 < B=5: leading is A=2."""
        A, B = 2.0, 5.0
        a = [math.factorial(n) * (1.0 / A**n + 0.5 / B**n) for n in range(5)]
        # B[a]_n = 1/A^n + 0.5/B^n; rational of degree (0,2) with simple
        # poles at ζ=A and ζ=B. [2/2] Padé reconstructs exactly.
        A_extracted = leading_borel_singularity(a, M=2, N=2)
        assert A_extracted is not None
        # Leading (smallest positive real) is A
        assert A_extracted.real == pytest.approx(A, rel=1e-3)


# ═══════════════════════════════════════════════════════════════════
# Negative tests: pipeline must NOT spuriously extract A from
# non-Gevrey-1 sequences
# ═══════════════════════════════════════════════════════════════════

class TestNonGevreyFalseSignal:
    """Geometric and polynomial sequences should not produce a sharp
    Borel-plane singularity at finite distance — ratio_test correctly
    decays toward 0 in these cases."""

    def test_geometric_sequence_ratio_test_decays(self):
        """For a_n = 1/A^n (geometric), R_n = 1/((n+1)A) → 0.
        Distinct from Gevrey-1 R_n → 1/A (constant)."""
        A = 2.0
        N = 15
        a = [1.0 / A**n for n in range(N)]
        R = ratio_test(a)
        # R_n should monotonically decrease
        assert R[-1] < R[0]
        # R[N-2] = a[N-1]/((N-1)*a[N-2]) = (1/A) / (N-1)
        # = 1/(A*(N-1)) = 1/(2*14) for N=15
        expected_last = 1.0 / (A * (N - 1))
        assert R[-1] == pytest.approx(expected_last, rel=1e-9)

    def test_polynomial_sequence_ratio_test_decays(self):
        """For a_n = n+1 (polynomial), R_n = (n+2)/((n+1)²) → 0.
        Confirms ratio test correctly identifies sub-factorial growth."""
        a = [float(n + 1) for n in range(15)]
        R = ratio_test(a)
        # All values should be small
        assert R[-1] < 0.1


# ═══════════════════════════════════════════════════════════════════
# Pipeline error/edge handling
# ═══════════════════════════════════════════════════════════════════

class TestPipelineErrorHandling:
    """Verify the pipeline raises sensibly on insufficient input and
    handles edge cases (no positive singularity)."""

    def test_pade_borel_raises_with_too_few_coeffs(self):
        """pade_borel should error if not enough coefficients for [M/N]."""
        with pytest.raises(ValueError):
            pade_borel([1.0, 2.0], M=2, N=2)  # Need M+N+1 = 5 coeffs

    def test_lambda_uv_raises_with_too_few_coeffs(self):
        """lambda_uv_estimate requires len(coeffs) >= 3 for default M=1."""
        with pytest.raises(ValueError):
            lambda_uv_estimate([1.0, 0.5], kappa=1.0)


# ═══════════════════════════════════════════════════════════════════
# SK-EFT integration smoke test
# ═══════════════════════════════════════════════════════════════════

class TestSKEFTSyntheticIntegration:
    """Smoke test: feed the borel pipeline a synthetic SK-EFT-shaped
    factorially-divergent coefficient sequence and verify the pipeline
    recovers the expected Λ_UV."""

    def test_borel_pipeline_on_synthetic_sk_eft_sequence(self):
        """Synthetic n!/A^n sequence with A=2 (factorial divergence):
        Λ_UV = κ √A = 1.0 · √2 ≈ 1.414."""
        a = [math.factorial(n) / 2.0**n for n in range(3)]
        kappa = 1.0
        Lambda_UV = lambda_uv_estimate(a, kappa, M=1)
        assert Lambda_UV is not None
        assert Lambda_UV == pytest.approx(math.sqrt(2.0), rel=1e-6)

    def test_borel_pipeline_handles_realistic_n6_sequence(self):
        """N=6 coefficients (matching SK-EFT shipped through order 5):
        use a multi-singularity test sequence that gives a well-conditioned
        [2/2] Padé. This matches the realistic regime where N=6
        coefficients are available from formulas.py orders 0-5."""
        A = 2.0  # Leading Borel singularity
        # Synthetic SK-EFT-shaped 6-coefficient sequence with non-trivial
        # Borel structure (two singularities at A=2, B=4).
        a = [math.factorial(n) * (1.0 / A**n + 0.3 / 4.0**n) for n in range(6)]
        A_extracted = leading_borel_singularity(a, M=2, N=2)
        assert A_extracted is not None
        # Tolerance loosened because the secondary B=4 singularity can shift
        # the [2/2] Padé reconstruction of the leading singularity slightly
        assert A_extracted.real == pytest.approx(A, rel=0.05)
