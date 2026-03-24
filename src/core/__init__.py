"""Core shared infrastructure for the SK-EFT Hawking project.

Contains the transonic background solver, Aristotle API interface,
visualization utilities, physical constants (single source of truth),
and Lean-verified formulas used by both Phase 1 and Phase 2 analyses.
"""

from src.core.transonic_background import (
    BECParameters,
    TransonicBackground,
    solve_transonic_background,
    compute_dissipative_correction,
    steinhauer_Rb87,
    heidelberg_K39,
    trento_spin_sonic,
)
from src.core.constants import (
    HBAR,
    K_B,
    ATOMS,
    EXPERIMENTS,
    COLORS,
    ARISTOTLE_THEOREMS,
    TOTAL_THEOREMS,
    get_bec_parameters,
    get_all_experiments,
)
from src.core.formulas import (
    count_coefficients,
    enumerate_monomials,
    damping_rate,
    dispersive_correction,
    first_order_correction,
    second_order_correction,
    effective_temperature_ratio,
    turning_point_shift,
    beliaev_damping_rate,
    beliaev_transport_coefficients,
)
from src.core.aristotle_interface import (
    AristotleRunner,
    AristotleResult,
    SorryGap,
    SORRY_GAPS,
    PROJECT_ROOT,
    LEAN_DIR,
)

__all__ = [
    # Transonic background
    "BECParameters",
    "TransonicBackground",
    "solve_transonic_background",
    "compute_dissipative_correction",
    "steinhauer_Rb87",
    "heidelberg_K39",
    "trento_spin_sonic",
    # Aristotle
    "AristotleRunner",
    "AristotleResult",
    "SorryGap",
    "SORRY_GAPS",
    "PROJECT_ROOT",
    "LEAN_DIR",
]
