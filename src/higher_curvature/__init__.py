"""Phase 6e Wave 2: Higher-curvature structure from Wave 1 a_4.

Numerical companion to ``lean/SKEFTHawking/HigherCurvatureStructure.lean``.

Takes the three Christensen-Duff a_4 Dirac coefficients of Wave 1 and
assembles them into the canonical Stelle ``{R², C², 𝒢}`` basis with
coefficients ``(α, β, γ)``.  In 4D the Gauss-Bonnet density 𝒢 is
topological, so only ``{R², C²}`` survives in the local Lagrangian.

Submodules:

- ``curvature_basis`` — 3-scalar curvature evaluator + Stelle
  ``{R², C², 𝒢}`` decomposition + sign-definite ``α(N_f), β(N_f),
  γ(N_f)`` for the SM-like fermion content
- ``gauss_bonnet_check`` — verifies the Gauss-Bonnet density vanishes
  at *integrated* level on test backgrounds (closed manifolds), and
  the Weyl decomposition C² = Riem² − 2 Ricci² + R²/3 holds
  algebraically
- ``observational_bound_check`` — compares microscopic predictions to
  LIGO / pulsar / Eöt-Wash short-range-gravity / Cassini observational
  bounds on dimensionless higher-curvature couplings (Calmet et al.,
  Berti et al.)

Correctness-push: for SM-relevant fermion counts (N_f ∈ [24, 27]) the
Wave 1 Dirac a_4 coefficients are O(10⁻³) — far below the tightest
observational ceiling (Hulse-Taylor binary pulsar, |β| ≲ 10⁵⁹).  No
tension with observation.
"""

from src.higher_curvature.curvature_basis import (
    StelleBasisCoefficients,
    stelle_basis_coefficients,
    a4_density,
    a4_density_in_RC2GB_basis,
    weyl_squared_4D,
    gauss_bonnet_4D,
)
from src.higher_curvature.gauss_bonnet_check import (
    gauss_bonnet_combination_check,
    weyl_squared_de_sitter_zero,
    weyl_squared_schwarzschild_vacuum,
)
from src.higher_curvature.observational_bound_check import (
    HC_OBS_BOUNDS,
    largest_predicted_coefficient,
    predictions_below_bound,
    pulsar_correctness_push_passes,
)

__all__ = [
    "StelleBasisCoefficients",
    "stelle_basis_coefficients",
    "a4_density",
    "a4_density_in_RC2GB_basis",
    "weyl_squared_4D",
    "gauss_bonnet_4D",
    "gauss_bonnet_combination_check",
    "weyl_squared_de_sitter_zero",
    "weyl_squared_schwarzschild_vacuum",
    "HC_OBS_BOUNDS",
    "largest_predicted_coefficient",
    "predictions_below_bound",
    "pulsar_correctness_push_passes",
]
