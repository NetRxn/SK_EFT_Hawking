"""Phase 6b Wave 3 — Vestigial slow-roll inflation (preliminary Stage 3a numerics).

Status: pre-Gate-B.3 reconnaissance. No Lean theorems yet; this subpackage
produces the (n_s, r) parameter scan that informs the Gate B.3 user-authorization
decision per `docs/roadmaps/Phase6b_Roadmap.md` §239.

Vestigial-phase potential (from `VestigialEOS.lean`):
    V(τ) = ρ_vest(τ) = f_0 · (1 - τ²) · (5τ² - 1)

with τ ∈ [0,1] the vestigial-phase order parameter. The potential has:
    - V(0) = -f_0  (anti-de-Sitter-like minimum, NOT inflationary)
    - V(1/√5) = 0
    - V(√(3/5)) = 4f_0/5  (local maximum — hilltop)
    - V(1) = 0

Slow-roll inflation requires V > 0, restricting τ ∈ (1/√5, 1) ≈ (0.447, 1).
"""

from .slow_roll import (
    vestigial_potential,
    vestigial_potential_derivative,
    vestigial_potential_second_derivative,
    slow_roll_epsilon,
    slow_roll_eta,
)
from .ns_r_prediction import (
    n_s_vestigial,
    r_vestigial,
    e_folds_vestigial,
    scan_microscopic_grid,
)
from .planck_bicep_check import (
    PlanckBICEPRegion,
    is_admissible,
)

__all__ = [
    "vestigial_potential",
    "vestigial_potential_derivative",
    "vestigial_potential_second_derivative",
    "slow_roll_epsilon",
    "slow_roll_eta",
    "n_s_vestigial",
    "r_vestigial",
    "e_folds_vestigial",
    "scan_microscopic_grid",
    "PlanckBICEPRegion",
    "is_admissible",
]
