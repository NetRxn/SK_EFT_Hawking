"""Phase 6e Wave 1: Seeley-DeWitt coefficient evaluator.

Mirrors ``lean/SKEFTHawking/HeatKernelExpansion.lean``:

  a_0(N_f) = 4 N_f / (4π)²
  a_2(N_f, R) = - (N_f / 12) · R / (4π)²
  a_4(N_f, R, Ricci, Riem) = N_f / (4π)² · [
      -5 R²/(12·180)
    + +7 R_μν²/(12·180)
    + -12 R_μνρσ²/(12·180)
  ]

References: Vassilevich, Phys. Rep. 388, 279 (2003), Eqs. (4.37)–(4.42);
Christensen-Duff, Nucl. Phys. B154, 301 (1979).
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np

from src.core.constants import HEAT_KERNEL_PARAMS
from src.core.formulas import (
    seeley_dewitt_a0,
    seeley_dewitt_a2_R_coefficient,
    seeley_dewitt_a4_basis,
)


@dataclass(frozen=True)
class SeeleyDeWittCoefficients:
    """Bundle of leading Dirac heat-kernel coefficients in 4D vacuum.

    All densities are local (per-point); for the integrated effective
    action they multiply ``√g d⁴x`` plus the proper-time weighting
    that produces the Λ⁴/Λ²/log(Λ) divergence structure.
    """

    N_f: float
    a0: float
    a2_R_coef: float
    a4_R_sq: float
    a4_Ricci_sq: float
    a4_Riemann_sq: float

    def asdict(self) -> dict[str, float]:
        return {
            "N_f": self.N_f,
            "a0": self.a0,
            "a2_R_coef": self.a2_R_coef,
            "a4_R_sq": self.a4_R_sq,
            "a4_Ricci_sq": self.a4_Ricci_sq,
            "a4_Riemann_sq": self.a4_Riemann_sq,
        }


def seeley_dewitt_coefficients(N_f: float) -> SeeleyDeWittCoefficients:
    """Compute the Christensen-Duff Dirac heat-kernel coefficients."""
    if N_f <= 0:
        raise ValueError(f"N_f must be positive, got {N_f}")
    a4 = seeley_dewitt_a4_basis(N_f)
    return SeeleyDeWittCoefficients(
        N_f=float(N_f),
        a0=seeley_dewitt_a0(N_f),
        a2_R_coef=seeley_dewitt_a2_R_coefficient(N_f),
        a4_R_sq=a4["R_sq"],
        a4_Ricci_sq=a4["Ricci_sq"],
        a4_Riemann_sq=a4["Riemann_sq"],
    )


def asymptotic_consistency_residual(N_f: float) -> float:
    """Residual of the closed-form coefficient algebra.

    The Seeley-DeWitt expansion ties ``a_0``, ``a_2``, and the ``a_4``
    triple by a single overall factor ``N_f / (4π)²``. Compute the
    coefficient-side ratio that should equal ``-12 / (180 · 12)``
    (the Riemann² rational) and report the residual against the
    canonical value. Used as a sanity check that the formula module
    has not silently drifted.
    """
    coefs = seeley_dewitt_coefficients(N_f)
    canonical_riemann = -12.0 / (12.0 * 180.0)
    overall = HEAT_KERNEL_PARAMS["FOUR_PI_SQ"] * coefs.a4_Riemann_sq / N_f
    return float(overall - canonical_riemann)
