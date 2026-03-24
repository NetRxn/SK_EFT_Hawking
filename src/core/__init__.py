"""Core shared infrastructure for the SK-EFT Hawking project.

Contains the transonic background solver, Aristotle API interface,
and visualization utilities used by both Phase 1 and Phase 2 analyses.
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
