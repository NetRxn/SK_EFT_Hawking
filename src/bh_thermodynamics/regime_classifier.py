"""Regime classification for emergent-gravity ADW black holes.

Mirrors the Lean module's `Regime` inductive type, `BHData` and
`ADWParams` structures, `M_c` default function, and `classify`
decidable function. Wave 5.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

import numpy as np


class Regime(Enum):
    """Regime classification per `M ⋛ M_c`.

    - `SCHWARZSCHILD`: `M > M_c` — heating-as-evaporates (`dT_H/dM < 0`,
      `C(M) < 0`). Classical Hawking regime.
    - `BOUNDARY`: `M = M_c` — `dT_H/dM = 0`, T_H attains its maximum.
    - `ADW_EXTREMALITY`: `M < M_c` — cooling-toward-extremality
      (`dT_H/dM > 0`, `C(M) > 0`). The Wave 5 substrate-driven regime
      below the critical mass.
    """

    SCHWARZSCHILD = "Schwarzschild"
    BOUNDARY = "Boundary"
    ADW_EXTREMALITY = "ADWExtremality"


@dataclass(frozen=True)
class ADWParams:
    """ADW substrate parameters.

    Mirrors `lean/SKEFTHawking/BHThermodynamicsFourLaws.lean::ADWParams`.

    Parameters
    ----------
    alpha_ADW : float
        Wave 1 emergent-gravity coefficient; tracked-hypothesis.
    lambda_UV : float
        Sakharov-Adler UV cutoff (natural units; same units as M).
    N_f : float
        Fermion-flavor count (real for Lean compatibility).
    chi_vest : float
        Wave 2 vestigial-phase susceptibility.
    """

    alpha_ADW: float
    lambda_UV: float
    N_f: float
    chi_vest: float

    def __post_init__(self):
        if self.alpha_ADW <= 0:
            raise ValueError(f"alpha_ADW must be > 0, got {self.alpha_ADW}")
        if self.lambda_UV <= 0:
            raise ValueError(f"lambda_UV must be > 0, got {self.lambda_UV}")
        if self.N_f <= 0:
            raise ValueError(f"N_f must be > 0, got {self.N_f}")
        if self.chi_vest <= 0:
            raise ValueError(f"chi_vest must be > 0, got {self.chi_vest}")


@dataclass(frozen=True)
class BHData:
    """Black-hole observables for the four-laws bundle.

    Mirrors `lean/SKEFTHawking/BHThermodynamicsFourLaws.lean::BHData`.
    """

    M: float
    Q: float
    J: float
    A: float
    r_h: float
    T_H: float
    kappa: float

    def __post_init__(self):
        if self.M <= 0:
            raise ValueError(f"BHData.M must be > 0, got {self.M}")
        if self.A <= 0:
            raise ValueError(f"BHData.A must be > 0, got {self.A}")
        if self.r_h <= 0:
            raise ValueError(f"BHData.r_h must be > 0, got {self.r_h}")


def M_c_default(p: ADWParams) -> float:
    """Default critical-mass scaling: `M_c = (N_f * Λ_UV) / (12π * α_ADW)`.

    Mirrors `lean/SKEFTHawking/BHThermodynamicsFourLaws.lean::M_c`.

    This is the Wave 5 deep-research §3 dimensional ansatz; not pinned
    by any published primary source. Substrate-specific corrections live
    in the tracked-hypothesis bundle `H_RegimePartition`.

    Parameters
    ----------
    p : ADWParams
        Substrate parameters.

    Returns
    -------
    float
        Critical mass `M_c` in same units as `Λ_UV`.
    """
    return p.N_f * p.lambda_UV / (12.0 * np.pi * p.alpha_ADW)


def classify(b: BHData, p: ADWParams) -> Regime:
    """Decidable regime classifier `Regime` ← BHData × ADWParams.

    Mirrors `lean/SKEFTHawking/BHThermodynamicsFourLaws.lean::classify`.

    Parameters
    ----------
    b : BHData
        Black-hole observables (uses `b.M` for comparison against `M_c`).
    p : ADWParams
        Substrate parameters (determines `M_c`).

    Returns
    -------
    Regime
        SCHWARZSCHILD if M > M_c, ADW_EXTREMALITY if M < M_c, else BOUNDARY.
    """
    M_c = M_c_default(p)
    if b.M > M_c:
        return Regime.SCHWARZSCHILD
    elif b.M < M_c:
        return Regime.ADW_EXTREMALITY
    else:
        return Regime.BOUNDARY
