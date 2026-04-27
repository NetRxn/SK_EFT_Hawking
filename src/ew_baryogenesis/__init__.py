"""Phase 6c Wave 2: EW Baryogenesis ↔ Chirality Wall bridge.

Numerical companion to ``lean/SKEFTHawking/EWBaryogenesisChiralityWall.lean``.
Two-pillar EWBG verdict: chirality-wall (Z₁₆ anomaly cancellation, Phase 5e/5p)
AND phase-transition viability (Phase 5z.3) — both must hold for EWBG.

Conclusion (under H_KLRS): SM-as-is is doubly forbidden — wall intact AND
transition crossover. Baryogenesis must dispatch to leptogenesis or BSM.
"""

from src.ew_baryogenesis.sphaleron_computation import (
    sphaleron_suppression,
    sphalerons_decoupled,
    sphaleron_decoupling_threshold,
)
from src.ew_baryogenesis.bridge_check import (
    wall_intact,
    wall_cracked,
    sm_no_nu_R_z16_anomaly,
    sm_with_3nu_R_z16_anomaly,
    ewbg_viable,
    sm_ewbg_verdict,
)

__all__ = [
    "sphaleron_suppression",
    "sphalerons_decoupled",
    "sphaleron_decoupling_threshold",
    "wall_intact",
    "wall_cracked",
    "sm_no_nu_R_z16_anomaly",
    "sm_with_3nu_R_z16_anomaly",
    "ewbg_viable",
    "sm_ewbg_verdict",
]
