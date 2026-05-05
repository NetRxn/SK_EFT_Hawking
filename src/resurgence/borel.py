"""Phase 6n.α (G2 Resurgence) — Borel-Écalle resurgence numerical
infrastructure.

Implements the Padé-Borel pipeline from the Resurgence DR §5 for
extracting the Borel action `A` (location of the leading Borel-plane
singularity) from a finite truncation of a Gevrey-1 perturbative
series. The Borel action determines the substrate UV cutoff via
Λ_UV = κ √A in the SK-EFT gradient expansion (where the dimensionless
expansion variable is g = (ω/κ)²).

Pipeline:

    1. ratio_test(coeffs) → R_n = a_{n+1} / ((n+1) a_n)
       At large n, R_n → 1/A for Gevrey-1 sequences (a_n ~ Γ(n+β)/A^n).
       For geometric sequences (a_n ~ 1/A^n), R_n → 1/((n+1)A) → 0
       — distinguishes factorial vs geometric divergence.

    2. borel_transform(coeffs) → b_n = a_n / n!
       Has finite radius of convergence equal to |A| for Gevrey-1
       coefficient sequences.

    3. pade_borel(coeffs, M, N) → diagonal Padé approximant of the
       truncated Borel transform. Closest pole near the positive
       real axis gives ζ = A.

    4. leading_borel_singularity(coeffs, M) → extracts A from the
       Padé approximant.

    5. lambda_uv_estimate(coeffs, kappa) → Λ_UV = κ √A.

References:
- Aniceto-Başar-Schiappa, Phys. Rep. 809 (2019) 1 (arXiv:1802.10441)
- Heller-Spalinski, PRL 115 (2015) 072501 (arXiv:1503.07514)
- Caliceti-Meyer-Hermann-Ribeca-Surzhykov-Jentschura, Phys. Rep. 446 (2007) 1
- Mera-Pedersen-Nikolić, PRL 115 (2015) 143001 (arXiv:1502.06743)
- Resurgence DR §5: Lit-Search/_Exploratory/Resurgence Theory and
  Schwinger-Keldysh EFT.md
"""

import math
from typing import Optional

import numpy as np
from scipy.interpolate import pade


def borel_transform(coeffs):
    """Borel transform: b_n = a_n / n!

    Args:
        coeffs: sequence of perturbative coefficients [a_0, a_1, a_2, ...]

    Returns:
        numpy array of borel-transformed coefficients [a_0/0!, a_1/1!, ...]

    Note: For a Gevrey-1 sequence with a_n ~ n! / A^n, the Borel
    transform has finite radius of convergence equal to |A|. Polynomial
    sequences (n^k growth) Borel-transform to entire functions.
    """
    return np.array([c / math.factorial(n) for n, c in enumerate(coeffs)],
                    dtype=float)


def pade_borel(coeffs, M: int, N: Optional[int] = None):
    """[M/N] Padé approximant of the truncated Borel transform.

    Args:
        coeffs: perturbative coefficient sequence
        M: numerator degree
        N: denominator degree (default M)

    Returns:
        (p, q) numpy.poly1d objects — numerator p, denominator q
        such that B[f]_truncated(ζ) ≈ p(ζ) / q(ζ).

    Requires len(coeffs) >= M + N + 1.
    """
    if N is None:
        N = M
    needed = M + N + 1
    if len(coeffs) < needed:
        raise ValueError(
            f"pade_borel requires len(coeffs) >= {needed}, got {len(coeffs)}"
        )
    b = borel_transform(coeffs[:needed])
    p, q = pade(b, N, M)
    return p, q


def leading_borel_singularity(coeffs, M: int, N: Optional[int] = None,
                              imag_tol: float = 1e-3) -> Optional[complex]:
    """Locate the closest positive-real-axis pole of the [M/N] Padé-Borel.

    Args:
        coeffs: perturbative coefficient sequence
        M: numerator Padé degree
        N: denominator Padé degree (default M)
        imag_tol: tolerance for "essentially real" classification

    Returns:
        Complex number A (essentially real, positive part) or None if
        no positive-real-axis singularity is found.
    """
    if N is None:
        N = M
    _p, q = pade_borel(coeffs, M, N)
    roots = np.roots(q.coeffs)
    # Filter to positive real (within imag_tol) and pick closest to origin
    candidates = [r for r in roots if r.real > 0 and abs(r.imag) < imag_tol]
    if not candidates:
        return None
    return min(candidates, key=lambda z: z.real)


def ratio_test(coeffs):
    """Cheap diagnostic for factorial vs geometric divergence.

    Computes R_n := a_{n+1} / ((n+1) * a_n) for n = 0, 1, ..., len-2.

    Asymptotic behavior:
    - Gevrey-1 (factorial): R_n → 1/A as n → ∞
      (because a_n ~ Γ(n+β)/A^n → a_{n+1}/((n+1)a_n) ~ 1/A · Γ(n+β+1)/((n+1)Γ(n+β)) → 1/A)
    - Geometric (a_n ~ C/A^n): R_n → 1/((n+1)A) → 0
    - Polynomial (a_n ~ n^k): R_n → ((n+1)/n)^k / (n+1) → 0

    Args:
        coeffs: perturbative coefficient sequence

    Returns:
        numpy array of R_n values (skipping n where a_n = 0).

    Note: R_n converging to a non-zero positive constant is the
    signature of Gevrey-1 divergence; convergence to 0 indicates
    sub-factorial growth.
    """
    out = []
    for n in range(len(coeffs) - 1):
        if coeffs[n] == 0:
            continue
        out.append(coeffs[n + 1] / ((n + 1) * coeffs[n]))
    return np.array(out, dtype=float)


def lambda_uv_estimate(coeffs, kappa: float, M: Optional[int] = None) -> Optional[float]:
    """Closed-form Λ_UV = κ √A from leading Borel singularity.

    Per Resurgence DR §5: in the SK-EFT gradient expansion the
    dimensionless variable is g = (ω/κ)², so the Borel action A
    (dimensionless in g) gives a UV cutoff Λ_UV = κ √A.

    The non-perturbative correction is then
        δ_NP(ω) ~ S_1 exp(-A · κ²/ω²) = S_1 exp(-(Λ_UV/ω)² · A)
    — exponentially suppressed at frequencies ω ≪ Λ_UV.

    Args:
        coeffs: perturbative coefficient sequence
        kappa: surface gravity κ [s⁻¹]
        M: Padé numerator degree (default len//2 - 1)

    Returns:
        Λ_UV estimate [s⁻¹], or None if no leading Borel singularity
        could be extracted.
    """
    if M is None:
        M = (len(coeffs) - 1) // 2
        if M < 1:
            raise ValueError(
                f"lambda_uv_estimate requires len(coeffs) >= 3 for M=1, "
                f"got {len(coeffs)}"
            )
    A = leading_borel_singularity(coeffs, M)
    if A is None:
        return None
    return kappa * math.sqrt(A.real)
