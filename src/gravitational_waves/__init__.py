"""Phase 6a Wave 2: gravitational waves from vestigial-phase susceptibility.

Numerical companion to ``lean/SKEFTHawking/GravitationalWaves.lean``. All
core formulas live in ``src.core.formulas``; this package provides
parameter-scan utilities, the GW170817 falsification analysis over the
natural χ_vest range, and the SK-EFT dispersion-correction probe.

The Wave 2 main physics finding is the **quantitative falsification** of
the Volovik vestigial-second-sound graviton identification under
GW170817: the natural susceptibility range gives Δc/c ∈ [-0.68, +2.16],
exceeding the LIGO bound (3e-15) by 14+ orders of magnitude. This
package computes that explicitly and produces the falsification figure.
"""

from src.gravitational_waves.c_GW_computation import (
    c_GW_at_natural_anchor,
    c_GW_grid,
    c_GW_natural_window_violation_factor,
)
from src.gravitational_waves.dispersion_relation import (
    dispersion_correction_grid,
    leading_dispersion_correction,
)
from src.gravitational_waves.ligo_constraint_check import (
    GW170817Verdict,
    chi_vest_window_compatible_with_ligo,
    ligo_compatibility_check,
    ligo_falsification_summary,
)

__all__ = [
    # c_GW scans
    "c_GW_at_natural_anchor",
    "c_GW_grid",
    "c_GW_natural_window_violation_factor",
    # Dispersion
    "dispersion_correction_grid",
    "leading_dispersion_correction",
    # LIGO check
    "GW170817Verdict",
    "chi_vest_window_compatible_with_ligo",
    "ligo_compatibility_check",
    "ligo_falsification_summary",
]
