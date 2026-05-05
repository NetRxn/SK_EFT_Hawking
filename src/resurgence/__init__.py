"""Phase 6n.α (G2 Resurgence) — Borel-Écalle resurgence infrastructure
for the SK-EFT gradient expansion.

Provides Padé-Borel reconstruction tools for extracting the Borel
action `A` (and hence the substrate UV cutoff Λ_UV = κ √A) from a
finite truncation of the SK-EFT gradient-expansion coefficient
sequence. The tools work on any Gevrey-1 sequence (factorially
divergent at large n) and degrade gracefully on geometrically
convergent sequences (linear-response Grozdanov-Kovtun-Starinets-Tadić
arXiv:1904.01018 case).

Usage:

    from src.resurgence.borel import (
        borel_transform, pade_borel, leading_borel_singularity,
        ratio_test, lambda_uv_estimate,
    )

    # Heller-Spalinski-style validation: a_n = n! / A^n
    coeffs = [factorial(n) / 2.0**n for n in range(10)]
    A_extracted = leading_borel_singularity(coeffs, M=4).real
    # Should recover A ≈ 2.0

References:
- Aniceto-Başar-Schiappa Phys. Rep. 809 (2019) 1, arXiv:1802.10441
- Heller-Spalinski PRL 115 (2015) 072501, arXiv:1503.07514
- Mera-Pedersen-Nikolić PRL 115 (2015) 143001, arXiv:1502.06743
- Resurgence DR §5: Lit-Search/_Exploratory/Resurgence Theory and
  Schwinger-Keldysh EFT.md
"""

from src.resurgence.borel import (
    borel_transform,
    pade_borel,
    leading_borel_singularity,
    ratio_test,
    lambda_uv_estimate,
)

__all__ = [
    'borel_transform',
    'pade_borel',
    'leading_borel_singularity',
    'ratio_test',
    'lambda_uv_estimate',
]
