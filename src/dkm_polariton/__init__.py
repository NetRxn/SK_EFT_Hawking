"""Legacy photon-equivalent arithmetic exports.

The scalar comparison proxy and API names are retained. These exports
do not certify mode occupation, a hard cutoff, F3 or physical uniqueness.
"""

from src.dkm_polariton.polariton_occupation_bound import (
    mode_occupation_per_pulse,
    is_below_dkm_f3_threshold,
    DKM_F3_THRESHOLD_OCCUPATION,
    penn_tmd_occupation_at_switching_threshold,
    paris_lkb_occupation_at_typical_pump,
)

__all__ = [
    "mode_occupation_per_pulse",
    "is_below_dkm_f3_threshold",
    "DKM_F3_THRESHOLD_OCCUPATION",
    "penn_tmd_occupation_at_switching_threshold",
    "paris_lkb_occupation_at_typical_pump",
]
