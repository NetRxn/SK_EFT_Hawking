"""Phase 6e Wave 6: Einstein-Cartan Extension (torsion from spin current).

Numerical companion to ``lean/SKEFTHawking/EinsteinCartanExtension.lean``.

Extends the ADW emergent-gravity programme to Einstein-Cartan with
non-zero torsion sourced by the fermion spin current — the structural
consequence of working with tetrads ``e^a_μ`` rather than the metric
``g_μν``.  Hehl-style EC theory (Hehl-Heyde-Kerlick-Nester, Rev. Mod.
Phys. 48, 393 (1976)) gives the algebraic Cartan torsion equation
``T^a_{μν} ∝ G_N · S^a_{μν}``; the Wave 6 scalar amplitude is

  ``|T_EC|(Λ_UV, N_f, α_EC, n_spin)
       = α_EC · 12π/(N_f · Λ_UV²) · n_spin``.

The Wave 6 **correctness-push** is a quantitative observational-bound
theorem: at the natural microscopic point ``(Λ_UV, N_f, α_EC) =
(M_Pl, 16, 1)`` and the cosmological-bath spin density
``n_s ≃ 1.3×10⁻³⁹ GeV³``, the predicted torsion amplitude
``|T_EC| ≃ 1.3×10⁻¹¹⁴ GeV`` sits ~83 orders of magnitude below the
tightest published Kostelecky-Russell-Tasson cosmic-axial-torsion
bound ``T < 10⁻³¹ GeV`` (PRL 100, 111102 (2008)).

Submodules:

- ``torsion_amplitude`` — ``|T_EC|`` evaluator + scans over
  ``(Λ_UV, N_f, α_EC, n_spin)``.
- ``observational_bounds`` — Decision-Gate-style verdict against
  Kostelecky / Hughes-Drever published bounds.
- ``ec_residual_assessment`` — Wave 6 expression of Decision Gate E.2
  (calibration channel: residual = 0 ↔ α_EC = 1).
"""

from src.einstein_cartan.torsion_amplitude import (
    TorsionPrediction,
    torsion_amplitude_at_point,
    torsion_scan_over_alpha,
    torsion_scan_over_lambda_uv,
)
from src.einstein_cartan.observational_bounds import (
    BoundVerdict,
    torsion_below_kostelecky,
    torsion_below_hughes_drever,
    torsion_observational_verdict,
)
from src.einstein_cartan.ec_residual_assessment import (
    ECResidualResult,
    ec_residual_at_point,
    ec_match_holds,
)

__all__ = [
    "TorsionPrediction",
    "torsion_amplitude_at_point",
    "torsion_scan_over_alpha",
    "torsion_scan_over_lambda_uv",
    "BoundVerdict",
    "torsion_below_kostelecky",
    "torsion_below_hughes_drever",
    "torsion_observational_verdict",
    "ECResidualResult",
    "ec_residual_at_point",
    "ec_match_holds",
]
