"""
Phase 6v Wave 6v.3: DKM F3 polariton occupancy bound.

Polariton-platform companion to the Phase 6q DKM transport bootstrap
substrate. Computes the per-pulse photon count for ultrafast-polariton
platforms (Penn TMD nanocavity Wang et al. 2026, Paris-LKB Falque 2025)
and confirms it sits well below the n_threshold ≈ 10⁶ regime that
breaks DKM F3 (operator-growth) on continuum-bosonic platforms via
Yin-Lucas / Kuwahara-Saito Lieb-Robinson-for-bosons.

This module's substantive output is the empirical resolution of the
Phase 6q open question (left in `project_phase6q_complete_2026_05_23`
memory): **polariton takes the POSITIVE-uniqueness branch of the
Phase 6q bimodal outcome** under any device-operating pump-energy
constraint matched to the experimental switching threshold.
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
