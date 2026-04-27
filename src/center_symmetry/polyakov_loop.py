"""Polyakov loop and Z_N center action — Phase 6d Wave 1.

Mirrors `lean/SKEFTHawking/CenterSymmetryConfinement.lean` §1–§3.

The Polyakov loop is a complex-valued order parameter. Confinement
holds iff `P = 0`, equivalently iff the Z_N 1-form center symmetry is
unbroken. The center symmetry acts on `P` by multiplication by
ζ_N = exp(2πi/N).
"""

from __future__ import annotations

import math
from dataclasses import dataclass


@dataclass(frozen=True)
class CenterZN:
    """The cyclic center Z_N for a non-Abelian gauge theory.

    For SU(N), the center is exactly Z_N. The constraint `N ≥ 2` is
    load-bearing — Z_1 is trivial, only N ≥ 2 yields a non-trivial
    center symmetry whose breaking corresponds to deconfinement.
    """

    N: int

    def __post_init__(self) -> None:
        if self.N < 2:
            raise ValueError(f"CenterZN requires N >= 2, got N={self.N}")


#: Z_2 center (SU(2) gauge theory).
Z2 = CenterZN(N=2)
#: Z_3 center (SU(3) gauge theory; QCD).
Z3 = CenterZN(N=3)


def center_phase(z: CenterZN) -> complex:
    """The fundamental phase ζ_N = exp(2πi/N) generating Z_N ⊂ ℂ*.

    Mirrors `centerPhase` in the Lean module. Used by `center_action`
    as the multiplicative generator of the center symmetry.
    """
    return complex(math.cos(2 * math.pi / z.N), math.sin(2 * math.pi / z.N))


def center_action(z: CenterZN, polyakov: complex) -> complex:
    """The Z_N center action on the Polyakov loop: P → ζ_N · P.

    Mirrors `centerAction` in the Lean module.
    """
    return center_phase(z) * polyakov


def confining(polyakov: complex, atol: float = 1e-12) -> bool:
    """Whether a Polyakov-loop value is in the confining phase.

    Mirrors `Confining` Lean predicate. Returns True iff `P = 0` (within
    `atol` for numerical safety). The `atol` defaults to 1e-12 and is
    essentially exact-equality for the analytical/structural use cases
    this module supports.
    """
    return abs(polyakov) <= atol


def polyakov_magnitude(polyakov: complex) -> float:
    """The real-valued order parameter |P|.

    Mirrors `polyakovMagnitude` in the Lean module. Confining ⟺ |P| = 0.
    """
    return abs(polyakov)
