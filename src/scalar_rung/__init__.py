"""Phase 5z Waves 1 + 1b: Scalar-rung interpretation of the Higgs bilinear.

Numerical companions to ``lean/SKEFTHawking/ScalarRungInterpretation.lean``
(Wave 1) and ``lean/SKEFTHawking/BHLGaugeEmbedding.lean`` (Wave 1b).
All physics formulas are imported from ``src.core.formulas``; this package
adds parameter-scan utilities, the Anderson-Higgs mass-matrix wrapper,
and BHL-class quantitative-scope numerics.
"""

from src.scalar_rung.higgs_prediction import (
    higgs_mass_scan,
    quantitative_match_grid,
)
from src.scalar_rung.ew_mass_matrix import (
    anderson_higgs_w_z_masses,
    cos_theta_w_consistency,
)
from src.scalar_rung.bhl_embedding import (
    bhl_minimal_prediction,
    bhl_gap_against_pdg,
    bilocal_correction_required,
    bilocal_correction_scan,
    bhl_pagels_stokar_vev_check,
)

__all__ = [
    "higgs_mass_scan",
    "quantitative_match_grid",
    "anderson_higgs_w_z_masses",
    "cos_theta_w_consistency",
    "bhl_minimal_prediction",
    "bhl_gap_against_pdg",
    "bilocal_correction_required",
    "bilocal_correction_scan",
    "bhl_pagels_stokar_vev_check",
]
