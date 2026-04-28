"""Phase 6e Wave 4: Nonlinear Einstein Field Equations from ADW.

Numerical companion to ``lean/SKEFTHawking/NonlinearEFE.lean``.

At the trace level of the variational EFE
``δS/δe^a_μ = 0  →  R + α_HC · 𝒜₄ + 8π G_N · T = 0``,
the Wave-1 Christensen-Duff Dirac calibration absorbs the Einstein +
matter trace into the Sakharov-Adler baseline at ``α_ADW = 1``, so the
trace-level residual is the deviation
``8π G_N · ρ_ADW · (α_ADW − 1)``.

The Wave 4 **load-bearing correctness-push** is a Decision-Gate-style
biconditional: under positive Newton constant and non-zero matter
source, this residual vanishes iff ``α_ADW = 1``.

Submodules:

- ``efe_solver`` — trace-level EFE residual evaluator at
  representative-background scans (Schwarzschild, de Sitter,
  FLRW radiation)
- ``T_emerg_vs_matter`` — emergent vs bare-matter stress-energy trace
  comparator with linear-in-(α-1) deviation channel
- ``observable_prediction`` — PPN-style observable ratios (deflection,
  perihelion precession, ringdown frequency) under the ADW α_ADW
  rescaling, plus VLBI / MESSENGER / GWTC-3 floor checks
"""

from src.nonlinear_efe.efe_solver import (
    BackgroundCurvature,
    schwarzschild_horizon_background,
    de_sitter_background,
    flrw_radiation_background,
    efe_residual_at_background,
    efe_residual_scan_over_alpha,
    efe_residual_at_dirac_balanced,
)
from src.nonlinear_efe.T_emerg_vs_matter import (
    StressEnergyComparison,
    compare_emergent_vs_matter,
    deviation_channel,
    deviation_detectable_at_floor,
)
from src.nonlinear_efe.observable_prediction import (
    ObservableSignature,
    deflection_signature,
    precession_signature,
    ringdown_signature,
    deviation_below_observation_floor,
    cross_channel_signature_table,
)

__all__ = [
    "BackgroundCurvature",
    "schwarzschild_horizon_background",
    "de_sitter_background",
    "flrw_radiation_background",
    "efe_residual_at_background",
    "efe_residual_scan_over_alpha",
    "efe_residual_at_dirac_balanced",
    "StressEnergyComparison",
    "compare_emergent_vs_matter",
    "deviation_channel",
    "deviation_detectable_at_floor",
    "ObservableSignature",
    "deflection_signature",
    "precession_signature",
    "ringdown_signature",
    "deviation_below_observation_floor",
    "cross_channel_signature_table",
]
