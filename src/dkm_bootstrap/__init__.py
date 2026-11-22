"""Adopted DKM scalar and fitted-length comparison exports.

Legacy names/keys describe arithmetic. A true comparison verifies no
material CHHK applicability or collective-length identification.
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
