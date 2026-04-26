"""Phase 5z Wave 3: Electroweak phase transition on the scalar rung.

Numerical companions to ``lean/SKEFTHawking/EWPhaseTransition.lean``.
Per Phase 5z O.2 verdict (Scenario A 3/5): Wave 3 proceeds with direct
SU(2)-indexed finite-T potential built on the BHL Higgs-doublet
identification (Wave 1b).
"""

from src.ew_phase_transition.potential import (
    finite_t_potential,
    thermal_mass_sq,
    critical_temperature,
    latent_heat,
)
from src.ew_phase_transition.order_classifier import (
    is_first_order_ew,
    is_crossover_ew,
    transition_order_grid,
)
from src.ew_phase_transition.baryogenesis_compatibility import (
    is_baryogenesis_viable,
    sphaleron_decoupling_threshold,
)

__all__ = [
    "finite_t_potential",
    "thermal_mass_sq",
    "critical_temperature",
    "latent_heat",
    "is_first_order_ew",
    "is_crossover_ew",
    "transition_order_grid",
    "is_baryogenesis_viable",
    "sphaleron_decoupling_threshold",
]
