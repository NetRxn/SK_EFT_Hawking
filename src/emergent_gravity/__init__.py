"""Phase 6a Wave 1: emergent G_N + linearized Einstein equations.

Numerical companion to ``lean/SKEFTHawking/LinearizedEFE.lean``. All
core physics formulas are imported from ``src.core.formulas``; this
package adds parameter-scan utilities (Λ_UV, N_f, α_ADW), the locus-of-
match computation, and the Vergeles unitarity sanity check.

Wave 4 (FLRW dynamics) re-uses ``G_N_emergent`` plus dedicated FLRW
helpers in ``src.emergent_gravity.flrw_solver``.
"""

from src.emergent_gravity.G_N_emerg import (
    G_N_emerg_at_coupling_grid,
    G_N_emerg_grid,
    G_N_emerg_match_grid,
    G_N_emerg_match_locus_lambda,
    G_N_emerg_planck_anchor_alpha,
    natural_parameter_grid,
)
from src.emergent_gravity.linearized_efe import (
    deDonder_gauge_residual,
    linearized_einstein_de_donder_array,
    minkowski_metric,
    minkowski_trace,
    trace_reversed_perturbation_array,
)
from src.emergent_gravity.vergeles_unitarity import (
    VergelesPositivityCheck,
    sakharov_baseline_consistency,
    vergeles_alpha_natural_range,
)

__all__ = [
    # G_N scans
    "G_N_emerg_at_coupling_grid",
    "G_N_emerg_grid",
    "G_N_emerg_match_grid",
    "G_N_emerg_match_locus_lambda",
    "G_N_emerg_planck_anchor_alpha",
    "natural_parameter_grid",
    # Linearized EFE numerics
    "deDonder_gauge_residual",
    "linearized_einstein_de_donder_array",
    "minkowski_metric",
    "minkowski_trace",
    "trace_reversed_perturbation_array",
    # Vergeles sanity
    "VergelesPositivityCheck",
    "sakharov_baseline_consistency",
    "vergeles_alpha_natural_range",
]
