"""Wave 6 observational-bound assessment vs Kostelecky / Hughes-Drever.

The Wave 6 correctness-push compares the microscopic torsion-amplitude
prediction at the cosmological background against the tightest published
torsion observational bounds:

- ``TORSION_BOUND_KOSTELECKY_GEV = 1×10⁻³¹ GeV`` (PRL 100, 111102 (2008))
- ``TORSION_BOUND_HUGHES_DREVER_GEV = 1×10⁻²⁹ GeV`` (PRD 64, 084014 (2001))

At the natural microscopic point ``(Λ_UV, N_f, α_EC) = (M_Pl, 16, 1)``
the prediction sits ~83 orders of magnitude below Kostelecky — i.e.
trivially satisfied at all natural parameter points.

Lean: ``EinsteinCartanExtension.torsionBoundKostelecky``,
      ``torsionBoundHughesDrever``,
      ``torsionAtCosmologicalBackground_at_planck_natural_below_kostelecky``,
      ``below_kostelecky_implies_below_hughes_drever``
"""

from __future__ import annotations

from dataclasses import dataclass

from src.core.constants import EINSTEIN_CARTAN_PARAMS
from src.core.formulas import torsion_amplitude_at_cosmological_background


@dataclass(frozen=True)
class BoundVerdict:
    """Aggregated verdict at a (Λ_UV, N_f, α_EC) point against published bounds.

    Attributes
    ----------
    amplitude_gev : float
        Predicted ``|T_EC|`` at the cosmological background.
    kostelecky_satisfied : bool
        Whether the prediction sits below the Kostelecky bound.
    hughes_drever_satisfied : bool
        Whether the prediction sits below the Hughes-Drever bound.
    log10_margin_kostelecky : float
        ``log10(bound / prediction)`` — orders of magnitude of headroom
        below the Kostelecky bound (negative ⇒ violated).
    verdict_label : str
        ``'torsion_below_bound'`` or ``'torsion_above_bound'`` from
        ``EINSTEIN_CARTAN_PARAMS``.
    """

    amplitude_gev: float
    kostelecky_satisfied: bool
    hughes_drever_satisfied: bool
    log10_margin_kostelecky: float
    verdict_label: str


def torsion_below_kostelecky(
    lambda_uv_gev: float,
    n_f: float,
    alpha_ec: float = 1.0,
) -> bool:
    """True iff predicted ``|T_EC|`` (cosmological bath) < Kostelecky bound."""
    bound = EINSTEIN_CARTAN_PARAMS['TORSION_BOUND_KOSTELECKY_GEV']
    pred = torsion_amplitude_at_cosmological_background(
        lambda_uv_gev, n_f, alpha_ec
    )
    return abs(pred) < bound


def torsion_below_hughes_drever(
    lambda_uv_gev: float,
    n_f: float,
    alpha_ec: float = 1.0,
) -> bool:
    """True iff predicted ``|T_EC|`` (cosmological bath) < Hughes-Drever bound."""
    bound = EINSTEIN_CARTAN_PARAMS['TORSION_BOUND_HUGHES_DREVER_GEV']
    pred = torsion_amplitude_at_cosmological_background(
        lambda_uv_gev, n_f, alpha_ec
    )
    return abs(pred) < bound


def torsion_observational_verdict(
    lambda_uv_gev: float,
    n_f: float,
    alpha_ec: float = 1.0,
) -> BoundVerdict:
    """Aggregate Decision-Gate-style verdict at the cosmological background."""
    import math

    bound_K = EINSTEIN_CARTAN_PARAMS['TORSION_BOUND_KOSTELECKY_GEV']
    bound_HD = EINSTEIN_CARTAN_PARAMS['TORSION_BOUND_HUGHES_DREVER_GEV']
    pred = torsion_amplitude_at_cosmological_background(
        lambda_uv_gev, n_f, alpha_ec
    )
    pred_abs = abs(pred)
    ksat = pred_abs < bound_K
    hdsat = pred_abs < bound_HD
    margin = math.log10(bound_K / pred_abs) if pred_abs > 0 else float('inf')
    label = (
        EINSTEIN_CARTAN_PARAMS['TORSION_VERDICT_BOUND_SATISFIED']
        if ksat
        else EINSTEIN_CARTAN_PARAMS['TORSION_VERDICT_BOUND_VIOLATED']
    )
    return BoundVerdict(
        amplitude_gev=pred,
        kostelecky_satisfied=ksat,
        hughes_drever_satisfied=hdsat,
        log10_margin_kostelecky=margin,
        verdict_label=label,
    )
