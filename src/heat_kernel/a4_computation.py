"""Phase 6e Wave 1: a_4 higher-curvature basis with Gauss-Bonnet check.

The Christensen-Duff Dirac a_4 density in 4D vacuum:

    a_4(x) = N_f / (4π)² · [
        -5/(12·180) · R²
      + +7/(12·180) · R_μν R^μν
      + -12/(12·180) · R_μνρσ R^μνρσ
    ]

The Gauss-Bonnet combination ``𝒢 = R² − 4 R_μν² + R_μνρσ²`` is
topological in 4D — locally non-zero, but its integral is the Euler
characteristic up to a fixed factor of 32π². The local algebra here
checks the consistency of the rational coefficient triple.
"""

from __future__ import annotations

from src.core.constants import HEAT_KERNEL_PARAMS
from src.core.formulas import gauss_bonnet_density, seeley_dewitt_a4_basis


def a4_basis(N_f: float) -> dict[str, float]:
    """Re-export of the canonical a_4 coefficient basis."""
    return seeley_dewitt_a4_basis(N_f)


def gauss_bonnet_combination(N_f: float) -> float:
    """Evaluate ``c_R² − 4 c_Ricci² + c_Riem²`` from the Dirac a_4
    coefficients. Lean theorem
    ``a4_gauss_bonnet_combination`` says this equals
    ``N_f · (−45 / (12·180)) / (4π)² = −N_f / (48 (4π)²)``.
    """
    coefs = a4_basis(N_f)
    return gauss_bonnet_density(
        coefs["R_sq"], coefs["Ricci_sq"], coefs["Riemann_sq"]
    )


def higher_curvature_dirac_signs(N_f: float) -> dict[str, str]:
    """Return the sign of each a_4 coefficient.

    For positive ``N_f``:
      - ``R²`` coefficient is negative
      - ``Ricci²`` coefficient is positive
      - ``Riemann²`` coefficient is negative

    Useful as a fast structural check + as a Lean cross-bridge target
    (see ``a4_R_sq_coef_neg``, ``a4_Ricci_sq_coef_pos``,
    ``a4_Riemann_sq_coef_neg``).
    """
    if N_f <= 0:
        raise ValueError(f"N_f must be positive, got {N_f}")
    coefs = a4_basis(N_f)
    sign = {
        "R_sq": "neg" if coefs["R_sq"] < 0 else "pos",
        "Ricci_sq": "neg" if coefs["Ricci_sq"] < 0 else "pos",
        "Riemann_sq": "neg" if coefs["Riemann_sq"] < 0 else "pos",
    }
    return sign


def coefficient_overall_factor() -> float:
    """The shared ``1/(4π)²`` normalization. Used by tests + the
    cross-check that all a_n coefficients factor through it.
    """
    return 1.0 / HEAT_KERNEL_PARAMS["FOUR_PI_SQ"]
