"""Gauss-Bonnet + Weyl-squared sanity checks for Wave 2.

Verifies the canonical 4D differential-geometry identities at
representative backgrounds (de Sitter, Schwarzschild vacuum,
generic).  Mirrors the Lean theorems
``weylSquared4D_eq_zero_iff_conformally_flat`` and
``gaussBonnet_minus_weyl_eq_R_minus_Ricci_combination``.
"""

from __future__ import annotations

from src.higher_curvature.curvature_basis import (
    gauss_bonnet_4D, weyl_squared_4D,
)


def gauss_bonnet_combination_check(R_sq: float, Ricci_sq: float,
                                     Riemann_sq: float,
                                     tol: float = 1e-12) -> bool:
    """Verify the algebraic identity 𝒢 − C² = (2/3) R² − 2 R_μν².

    This is the engine for the Wave 2 basis change.  Mirrors Lean
    theorem ``gaussBonnet_minus_weyl_eq_R_minus_Ricci_combination``.
    Returns True iff the identity holds to within ``tol``.
    """
    lhs = (gauss_bonnet_4D(R_sq, Ricci_sq, Riemann_sq)
           - weyl_squared_4D(R_sq, Ricci_sq, Riemann_sq))
    rhs = (2.0 / 3.0) * float(R_sq) - 2.0 * float(Ricci_sq)
    return abs(lhs - rhs) <= tol


def weyl_squared_de_sitter_zero(H: float, tol: float = 1e-9) -> bool:
    """Verify Weyl² = 0 on de Sitter at Hubble parameter H.

    For de Sitter (4D, Lorentzian → Euclidean continuation):
    - R     = 12 H²
    - R²    = 144 H⁴
    - R_μν² = 36 H⁴
    - R_μνρσ² = 24 H⁴

    Therefore C² = 24 − 72 + 48 = 0 H⁴ (conformally flat).

    Mirrors the right-hand side of Lean theorem
    ``weylSquared4D_eq_zero_iff_conformally_flat`` evaluated at
    ``Riem = 2 Ricci - R/3`` for de Sitter.
    """
    H4 = float(H) ** 4
    R_sq = 144.0 * H4
    Ricci_sq = 36.0 * H4
    Riemann_sq = 24.0 * H4
    return abs(weyl_squared_4D(R_sq, Ricci_sq, Riemann_sq)) <= tol


def weyl_squared_schwarzschild_vacuum(M: float, r: float,
                                        tol: float = 1e-9) -> bool:
    """For Schwarzschild vacuum at radius r, verify Weyl² = Riemann².

    In any vacuum solution (Ricci-flat), R = R_μν = 0 so:
        C² = R_μνρσ² − 2·0 + (1/3)·0 = R_μνρσ²

    For Schwarzschild: R_μνρσ² = 48 M² / r⁶.  Returns True iff this
    matches numerically.
    """
    Riemann_sq = 48.0 * float(M) ** 2 / (float(r) ** 6)
    C_sq = weyl_squared_4D(0.0, 0.0, Riemann_sq)
    return abs(C_sq - Riemann_sq) <= tol
