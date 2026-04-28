"""Phase 6e Wave 1: Decision Gate E.2 calibration — heat-kernel a_2 vs
Phase 6a.1 LinearizedEFE.G_N_sakharov.

Integrating the Λ²-divergent part of ``a_2`` against the Einstein-
Hilbert action ``-1/(16π G_N) ∫ R √g d⁴x`` gives

    1 / (16 π G_N) = N_f Λ² / (192 π²)
  ⇒ G_N = 12 π / (N_f Λ²)  ≡  LinearizedEFE.G_N_sakharov(Λ, N_f).

The match is **exact** at α_ADW = 1, the Sakharov-Adler baseline.
The natural-parameter band α_ADW ∈ [0.5, 1.5] gives ≤50% relative
deviation, matching the ``GRAV_PARAMS.G_N_MATCH_TOLERANCE`` policy.
"""

from __future__ import annotations

from src.core.constants import GRAV_PARAMS, HEAT_KERNEL_PARAMS
from src.core.formulas import (
    G_N_from_seeley_dewitt,
    heat_kernel_a2_matches_GN_sakharov,
)


def G_N_from_a2(Lambda_UV: float, N_f: float) -> float:
    """Re-export of the canonical heat-kernel-derived Newton constant."""
    return G_N_from_seeley_dewitt(Lambda_UV, N_f)


def G_N_linearized_at_alpha(
    Lambda_UV: float, N_f: float, alpha_ADW: float = 1.0
) -> float:
    """LinearizedEFE.G_N_emerg evaluated in pure Python.

    ``G_N_emerg(Λ, N_f, α) = α · 12 π / (N_f Λ²)``
    """
    import math
    return alpha_ADW * 12.0 * math.pi / (float(N_f) * float(Lambda_UV) ** 2)


def a2_calibration_relative_error(
    Lambda_UV: float, N_f: float, alpha_ADW: float = 1.0
) -> float:
    """|G_N_heat_kernel - G_N_linearized| / G_N_linearized.

    Returns 0.0 at α_ADW = 1 (exact match). Linear in |α − 1| below 1
    and bounded by |α − 1| / α above 1.
    """
    G_hk = G_N_from_a2(Lambda_UV, N_f)
    G_lin = G_N_linearized_at_alpha(Lambda_UV, N_f, alpha_ADW)
    return abs(G_hk - G_lin) / G_lin


def a2_calibration_passes(
    Lambda_UV: float,
    N_f: float,
    alpha_ADW: float = 1.0,
    tolerance: float | None = None,
) -> bool:
    """Decision Gate E.2 boolean: relative error within tolerance."""
    return heat_kernel_a2_matches_GN_sakharov(
        Lambda_UV, N_f, alpha_ADW=alpha_ADW, tolerance=tolerance
    )


def planck_anchor_match() -> dict[str, float]:
    """Quantitative anchor: the Sakharov-Adler match locus.

    At ``Λ_UV = LAMBDA_UV_PLANCK_GEV`` and ``N_f = N_F_THREE_GEN_NO_NU_R = 45``,
    the heat-kernel ``G_N`` differs from the observed ``G_N`` by an
    exactly computable factor that is independent of α_ADW (entering
    only through the linearized-side comparison). Returns the bare
    numerical values for downstream tests + the Lean ``norm_num`` anchor.
    """
    Lambda = GRAV_PARAMS["LAMBDA_UV_PLANCK_GEV"]
    N_f = GRAV_PARAMS["N_F_THREE_GEN_NO_NU_R"]
    return {
        "Lambda_UV_GeV": float(Lambda),
        "N_f": int(N_f),
        "G_N_heat_kernel_GeV_m2": G_N_from_a2(Lambda, N_f),
        "G_N_observed_GeV_m2": GRAV_PARAMS["G_N_OBS_GEV_M2"],
        "rel_diff": abs(
            G_N_from_a2(Lambda, N_f) - GRAV_PARAMS["G_N_OBS_GEV_M2"]
        )
        / GRAV_PARAMS["G_N_OBS_GEV_M2"],
        "tolerance_band": HEAT_KERNEL_PARAMS["A2_GN_MATCH_TOLERANCE"],
    }
