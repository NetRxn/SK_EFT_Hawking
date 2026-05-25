"""Phase 6q DKM transport bootstrap — graphene MIR numerical companion.

Wave 2b numerical Python companion to the Lean substrate at
``lean/SKEFTHawking/DKMBootstrap/``. Computes the Chowdhury-Hartnoll-
Hebbar-Khondaker (CHHK) MIR-style geometric constant
``(d·β_d/(4π))^(1/(d+1))`` and confronts it with measured graphene
Dirac-fluid mean-free-path data (Crossno 2016).

Public API:
    graphene_mir_bound_constant() — float MIR constant for d=2 graphene.
    graphene_mir_constraint(ell, a) — checks ℓ/a ≥ MIR constant.
    crossno_graphene_satisfies_chhk_bound() — verification on Crossno data.

All canonical formulas live in ``src.core.formulas``; this module only
specializes them to graphene and adds the experimental-data confrontation.
"""

from src.dkm_bootstrap.graphene_mir import (
    graphene_mir_bound_constant,
    graphene_mir_constraint,
    crossno_graphene_satisfies_chhk_bound,
    CROSSNO_GRAPHENE_MEAN_FREE_PATH_M,
    CROSSNO_GRAPHENE_MEAN_FREE_PATH_RANGE_M,
    GRAPHENE_LATTICE_SPACING_M,
)

__all__ = [
    "graphene_mir_bound_constant",
    "graphene_mir_constraint",
    "crossno_graphene_satisfies_chhk_bound",
    "CROSSNO_GRAPHENE_MEAN_FREE_PATH_M",
    "CROSSNO_GRAPHENE_MEAN_FREE_PATH_RANGE_M",
    "GRAPHENE_LATTICE_SPACING_M",
]
