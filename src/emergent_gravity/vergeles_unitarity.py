"""Vergeles unitarity sanity check for ADW NG-mode → linearized Einstein.

Phase 6a Wave 1 tracked-hypothesis numerics. The Vergeles unitarity
proof (PRD 112, 054509 (2025)) establishes positivity of the ADW
NG-mode two-point function. The ADW-specific α_ADW coefficient that
appears in ``G_N^emerg = α_ADW · 12π / (N_f · Λ²)`` requires extracting
this two-point function and projecting onto the spin-2 sector — a
calculation pending deep research return
(``Lit-Search/Tasks/submitted/Phase6a_W1_vergeles_GN_coefficient.md``).

This module records the numerical checks that *can* be performed
without the deep-research result:

1. **Sakharov baseline consistency.** Confirms that at α_ADW = 1 the
   Sakharov-Adler one-loop result is reproduced.
2. **Natural-range check.** Confirms that the natural α_ADW range
   ``[0.1, 10]`` covers the values needed for SM N_f to match the
   observed G_N at natural Λ_UV.
3. **Positivity check.** Confirms ``α_ADW > 0`` (no wrong-sign gravity
   under Vergeles positivity).
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np

from src.core.constants import GRAV_PARAMS
from src.core.formulas import G_N_emergent, G_N_sakharov


@dataclass(frozen=True)
class VergelesPositivityCheck:
    """Verdict of the Vergeles positivity / natural-range check at a point.

    Attributes
    ----------
    alpha_adw : float
        Tested ADW coefficient.
    alpha_in_natural_range : bool
        ``ALPHA_ADW_LOWER ≤ α_ADW ≤ ALPHA_ADW_UPPER``.
    alpha_positive : bool
        ``α_ADW > 0`` (no wrong-sign emergent gravity).
    sakharov_baseline_match : bool
        At α_ADW = 1, ``G_N^emerg = G_N^Sakharov`` (within 1e-12).
    """

    alpha_adw: float
    alpha_in_natural_range: bool
    alpha_positive: bool
    sakharov_baseline_match: bool


def sakharov_baseline_consistency(
    lambda_uv_gev: float,
    n_f: float | int,
    rtol: float = 1e-12,
) -> bool:
    """At α_ADW = 1, ``G_N_emerg = G_N_sakharov`` to floating-point precision.

    Numerical mirror of ``LinearizedEFE.G_N_emerg_at_alpha_one``.

    Parameters
    ----------
    lambda_uv_gev : float
        UV cutoff in GeV.
    n_f : int or float
        Weyl species count.
    rtol : float, default=1e-12
        Relative tolerance.

    Returns
    -------
    bool
        True iff the equality holds within rtol.
    """
    g_emerg_one = G_N_emergent(lambda_uv_gev, n_f, alpha_adw=1.0)
    g_sak = G_N_sakharov(lambda_uv_gev, n_f)
    return bool(abs(g_emerg_one - g_sak) <= rtol * abs(g_sak))


def vergeles_alpha_natural_range(alpha_adw: float) -> VergelesPositivityCheck:
    """Bundle the three Vergeles-derived sanity checks at one point.

    Parameters
    ----------
    alpha_adw : float
        ADW coefficient to test.

    Returns
    -------
    VergelesPositivityCheck
        Structured verdict.
    """
    natural_low = GRAV_PARAMS["ALPHA_ADW_LOWER"]
    natural_high = GRAV_PARAMS["ALPHA_ADW_UPPER"]

    in_range = bool(natural_low <= alpha_adw <= natural_high)
    positive = bool(alpha_adw > 0)
    # Exercise the Sakharov-Adler consistency at fiducial Λ_UV/N_f
    fid_lam = GRAV_PARAMS["LAMBDA_UV_GUT_GEV"]
    fid_nf = GRAV_PARAMS["N_F_DEFAULT"]
    sak_match = sakharov_baseline_consistency(fid_lam, fid_nf)

    return VergelesPositivityCheck(
        alpha_adw=float(alpha_adw),
        alpha_in_natural_range=in_range,
        alpha_positive=positive,
        sakharov_baseline_match=sak_match,
    )


def planck_anchor_natural_alpha_for_nf(n_f: float | int) -> tuple[float, bool]:
    """At Λ = M_P^obs the matching α_ADW is N_f/(12π); is it natural?

    Returns ``(α*, in_natural_range)``. The ``in_natural_range`` flag is
    True iff ``α* ∈ [ALPHA_ADW_LOWER, ALPHA_ADW_UPPER]``.

    Parameters
    ----------
    n_f : int or float
        Weyl species count.

    Returns
    -------
    tuple[float, bool]
        Matching α_ADW and natural-range flag.
    """
    alpha_star = float(n_f / (12.0 * np.pi))
    in_range = bool(
        GRAV_PARAMS["ALPHA_ADW_LOWER"]
        <= alpha_star
        <= GRAV_PARAMS["ALPHA_ADW_UPPER"]
    )
    return alpha_star, in_range
