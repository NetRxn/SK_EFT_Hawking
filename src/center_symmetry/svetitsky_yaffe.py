"""Svetitsky-Yaffe universality lookup — Phase 6d Wave 1.

Mirrors `lean/SKEFTHawking/CenterSymmetryConfinement.lean` §4.

Per Svetitsky-Yaffe (1982): D-dim SU(N) finite-T deconfinement
shares its universality class with the (D−1)-dim Z_N spin model.

Critical exponent ν values (correlation length) are anchored to
literature: Pelissetto-Vicari, Phys. Rep. 368, 549 (2002);
Kos-Poland-Simmons-Duffin, JHEP 03 (2016) 069 (3D Ising bootstrap).
"""

from __future__ import annotations

from enum import Enum

from .polyakov_loop import CenterZN


class UniversalityClass(Enum):
    """Universality classes for Svetitsky-Yaffe deconfinement transitions.

    Aligned with the Lean `UniversalityClass` inductive type.
    """

    ISING = "Ising"                          # 3D Ising (Z_2 spin model)
    THREE_STATE_POTTS = "three_state_Potts"  # 3D 3-state Potts (Z_3)
    XY = "XY"                                 # 3D XY (U(1) spin model)
    OTHER = "other"


def svetitsky_yaffe_class(z: CenterZN) -> UniversalityClass:
    """The Svetitsky-Yaffe map: Z_N center → 3D universality class
    of the finite-temperature 4D-gauge-theory deconfinement transition.

    Mirrors `svetitskyYaffeClass` Lean function.
    """
    if z.N == 2:
        return UniversalityClass.ISING
    if z.N == 3:
        return UniversalityClass.THREE_STATE_POTTS
    return UniversalityClass.OTHER


#: Critical exponent ν (correlation length) by universality class.
#: Literature values:
#:   - 3D Ising: ν ≈ 0.6299 (Pelissetto-Vicari; KPSD bootstrap)
#:   - 3D 3-state Potts: ν ≈ 0.5 (mean-field-like; weakly first order)
#:   - 3D XY: ν ≈ 0.6717 (lattice).
_CRITICAL_NU: dict[UniversalityClass, float] = {
    UniversalityClass.ISING: 0.6299,
    UniversalityClass.THREE_STATE_POTTS: 0.5,
    UniversalityClass.XY: 0.6717,
    UniversalityClass.OTHER: 0.0,
}


def critical_exponent_nu(uc: UniversalityClass) -> float:
    """The correlation-length critical exponent ν for a universality class.

    Mirrors the Lean `critical_exponent_nu` function. Used downstream to
    distinguish deconfinement transitions of different center-symmetry
    types (Ising vs Potts ν differ by ~0.13 — quantitatively
    distinguishable in lattice scaling fits).
    """
    return _CRITICAL_NU[uc]
