"""Phase 5z Wave 1: Scalar-rung interpretation of the Higgs bilinear.

Numerical companions to ``lean/SKEFTHawking/ScalarRungInterpretation.lean``.
All physics formulas are imported from ``src.core.formulas``; this package
adds parameter-scan utilities and the Anderson-Higgs mass-matrix wrapper.
"""

from src.scalar_rung.higgs_prediction import (
    higgs_mass_scan,
    quantitative_match_grid,
)
from src.scalar_rung.ew_mass_matrix import (
    anderson_higgs_w_z_masses,
    cos_theta_w_consistency,
)

__all__ = [
    "higgs_mass_scan",
    "quantitative_match_grid",
    "anderson_higgs_w_z_masses",
    "cos_theta_w_consistency",
]
