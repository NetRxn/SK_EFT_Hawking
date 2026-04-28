"""3-scalar curvature basis evaluators for Phase 6e Wave 2.

Implements Stelle's ``{R², C², 𝒢}`` basis for the local higher-curvature
effective Lagrangian, derived from Wave 1's Christensen-Duff Dirac a_4
coefficients via a 3×3 linear-system solve.

All functions mirror Lean theorems in
``lean/SKEFTHawking/HigherCurvatureStructure.lean``.  Numerical values
agree to machine precision; sign-definite α, β, γ for positive N_f.
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import Tuple


@dataclass(frozen=True)
class StelleBasisCoefficients:
    """Coefficients ``(α, β, γ)`` of ``{R², C², 𝒢}`` basis at fixed N_f.

    All carry the implicit ``(4π)⁻²`` heat-kernel normalization (matched
    to the Wave 1 ``a4_R_sq_coef`` convention).

    Mirrors ``a4_alpha N_f``, ``a4_beta N_f``, ``a4_gamma N_f`` in
    ``HigherCurvatureStructure.lean``.

    Sign-definite for ``N_f > 0``:
    - ``alpha < 0``  (R² coefficient)
    - ``beta < 0``   (C²  coefficient)
    - ``gamma > 0``  (Gauss-Bonnet topological coefficient)
    """
    N_f: float
    alpha: float
    beta: float
    gamma: float


def stelle_basis_coefficients(N_f: float) -> StelleBasisCoefficients:
    """Compute ``(α, β, γ)`` for fermion count ``N_f``.

    Closed form (per ``(4π)²``):
        α(N_f) = -N_f / 324
        β(N_f) = -41 N_f / 4320
        γ(N_f) = 17 N_f / 4320

    Lean: HigherCurvatureStructure.a4_alpha,
          HigherCurvatureStructure.a4_beta,
          HigherCurvatureStructure.a4_gamma
    """
    from src.core.constants import HEAT_KERNEL_PARAMS  # FOUR_PI_SQ lives here
    inv_4pi_sq = 1.0 / HEAT_KERNEL_PARAMS['FOUR_PI_SQ']
    return StelleBasisCoefficients(
        N_f=float(N_f),
        alpha=float(N_f) * (-1.0 / 324.0) * inv_4pi_sq,
        beta=float(N_f) * (-41.0 / 4320.0) * inv_4pi_sq,
        gamma=float(N_f) * (17.0 / 4320.0) * inv_4pi_sq,
    )


def gauss_bonnet_4D(R_sq: float, Ricci_sq: float, Riemann_sq: float) -> float:
    """Gauss-Bonnet 4D Euler density: 𝒢 = R² − 4 R_μν² + R_μνρσ².

    Topological at integrated level on closed 4-manifolds; locally a
    non-trivial scalar.

    Lean: HigherCurvatureStructure.gaussBonnet4D
    """
    return float(R_sq) - 4.0 * float(Ricci_sq) + float(Riemann_sq)


def weyl_squared_4D(R_sq: float, Ricci_sq: float, Riemann_sq: float) -> float:
    """Weyl-squared in 4D from trace decomposition:
    C² = R_μνρσ² − 2 R_μν² + (1/3) R².

    Vanishes iff conformally flat (de Sitter, FLRW with K = 0, etc.).

    Lean: HigherCurvatureStructure.weylSquared4D
    """
    return (float(Riemann_sq) - 2.0 * float(Ricci_sq)
            + (1.0 / 3.0) * float(R_sq))


def a4_density(N_f: float, R_sq: float, Ricci_sq: float,
               Riemann_sq: float) -> float:
    """a_4 density in the original ``{R², R_μν², R_μνρσ²}`` basis using
    Wave 1 Christensen-Duff coefficients.

    Lean: HigherCurvatureStructure.a4_density
    """
    from src.core.formulas import (
        higher_curvature_R_sq_coefficient,
        higher_curvature_Ricci_sq_coefficient,
        higher_curvature_Riemann_sq_coefficient,
    )
    return (higher_curvature_R_sq_coefficient(N_f) * float(R_sq)
            + higher_curvature_Ricci_sq_coefficient(N_f) * float(Ricci_sq)
            + higher_curvature_Riemann_sq_coefficient(N_f)
              * float(Riemann_sq))


def a4_density_in_RC2GB_basis(N_f: float, R_sq: float, Ricci_sq: float,
                                Riemann_sq: float) -> float:
    """a_4 density in Stelle's ``{R², C², 𝒢}`` basis using ``(α, β, γ)``.

    By the basis-change identity (Lean theorem
    ``a4_density_eq_a4_density_in_RC2GB_basis``), this equals
    ``a4_density(N_f, R_sq, Ricci_sq, Riemann_sq)`` for all inputs.

    Lean: HigherCurvatureStructure.a4_density_in_RC2GB_basis
    """
    coefs = stelle_basis_coefficients(N_f)
    C_sq = weyl_squared_4D(R_sq, Ricci_sq, Riemann_sq)
    GB = gauss_bonnet_4D(R_sq, Ricci_sq, Riemann_sq)
    return (coefs.alpha * float(R_sq)
            + coefs.beta * C_sq
            + coefs.gamma * GB)


def basis_change_residual(N_f: float, R_sq: float, Ricci_sq: float,
                            Riemann_sq: float) -> float:
    """Residual ``a4_density - a4_density_in_RC2GB_basis``.

    Should be zero to machine precision for all inputs (basis-change
    identity, Lean theorem ``a4_density_eq_a4_density_in_RC2GB_basis``).
    """
    return abs(a4_density(N_f, R_sq, Ricci_sq, Riemann_sq)
               - a4_density_in_RC2GB_basis(N_f, R_sq, Ricci_sq, Riemann_sq))
