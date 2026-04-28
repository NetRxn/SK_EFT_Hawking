"""Phase 6e Wave 1: Seeley-DeWitt heat-kernel expansion of the Dirac
fermion-determinant on a 4D Riemannian background.

Numerical companion to ``lean/SKEFTHawking/HeatKernelExpansion.lean``.
Re-exports the canonical formulas from ``src.core.formulas`` and
provides higher-level evaluators / cross-check routines:

- ``seeley_dewitt`` — leading coefficient evaluator + asymptotic
  consistency check at fiducial parameters
- ``a2_computation`` — analytical ``a_2`` derivation cross-checked
  against Phase 6a.1 ``LinearizedEFE.G_N_sakharov``
- ``a4_computation`` — higher-curvature basis decomposition with
  Gauss-Bonnet topological identity sanity check

The Decision Gate E.2 calibration anchor:

  G_N^Sakharov = 12 π / (N_f Λ²) at α_ADW = 1
  ⇕  (heat-kernel a_2 integration matches linearized 6a.1)
  ⇒ ADW mean-field gravity emergence is self-consistent.
"""

from src.heat_kernel.seeley_dewitt import (
    SeeleyDeWittCoefficients,
    seeley_dewitt_coefficients,
)
from src.heat_kernel.a2_computation import (
    G_N_from_a2,
    a2_calibration_relative_error,
    a2_calibration_passes,
)
from src.heat_kernel.a4_computation import (
    a4_basis,
    gauss_bonnet_combination,
    higher_curvature_dirac_signs,
)

__all__ = [
    "SeeleyDeWittCoefficients",
    "seeley_dewitt_coefficients",
    "G_N_from_a2",
    "a2_calibration_relative_error",
    "a2_calibration_passes",
    "a4_basis",
    "gauss_bonnet_combination",
    "higher_curvature_dirac_signs",
]
