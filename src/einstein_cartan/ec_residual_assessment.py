"""Wave 6 expression of Decision Gate E.2: EC residual = 0 ↔ α_EC = 1.

The EC match residual

    residual(Λ_UV, N_f, α_EC, n_spin)
        = torsion_amplitude_ec(Λ_UV, N_f, α_EC, n_spin)
          - torsion_amplitude_ec(Λ_UV, N_f, 1, n_spin)
        = (α_EC - 1) · G_N_sakharov(Λ_UV, N_f) · n_spin

vanishes iff ``α_EC = 1`` under positive ``(Λ_UV, N_f, n_spin)``.  This
is the Wave 6 expression of Decision Gate E.2 (the Wave 1 closure
``a2_matches_GNemerg_iff_alpha_ADW_unity`` lifted to the EC sector).

Lean: ``EinsteinCartanExtension.ecResidual``,
      ``EinsteinCartanExtension.ecResidual_eq_zero_iff_alpha_unity``
"""

from __future__ import annotations

from dataclasses import dataclass

from src.core.constants import EINSTEIN_CARTAN_PARAMS
from src.core.formulas import (
    ec_match_residual,
    einstein_cartan_extension_holds,
)


@dataclass(frozen=True)
class ECResidualResult:
    """EC residual + bundled tracked-Prop predicate at a (Λ_UV, N_f, α_EC) point.

    Attributes
    ----------
    residual_gev : float
        Closed-form EC residual (units: GeV², from ``G_N · n_spin``).
    alpha_ec : float
        Einstein-Cartan rescaling coefficient.
    match_holds : bool
        Whether ``H_EinsteinCartanExtensionHolds`` is satisfied.
    """

    residual_gev: float
    alpha_ec: float
    match_holds: bool


def ec_residual_at_point(
    lambda_uv_gev: float,
    n_f: float,
    alpha_ec: float,
    n_spin_gev3: float | None = None,
) -> ECResidualResult:
    """Evaluate the EC residual + bundled match predicate at one point."""
    if n_spin_gev3 is None:
        n_spin_gev3 = EINSTEIN_CARTAN_PARAMS['COSMOLOGICAL_SPIN_DENSITY_GEV3']
    residual = ec_match_residual(lambda_uv_gev, n_f, alpha_ec, n_spin_gev3)
    holds = einstein_cartan_extension_holds(
        lambda_uv_gev, n_f, alpha_ec, n_spin=n_spin_gev3
    )
    return ECResidualResult(
        residual_gev=float(residual),
        alpha_ec=float(alpha_ec),
        match_holds=bool(holds),
    )


def ec_match_holds(
    lambda_uv_gev: float,
    n_f: float,
    alpha_ec: float,
    n_spin_gev3: float | None = None,
) -> bool:
    """Convenience: True iff ``H_EinsteinCartanExtensionHolds`` at this point."""
    return ec_residual_at_point(
        lambda_uv_gev, n_f, alpha_ec, n_spin_gev3
    ).match_holds
