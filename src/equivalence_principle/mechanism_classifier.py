"""EP-violation classifier — Phase 6c Wave 3.

Mirrors `lean/SKEFTHawking/EquivalencePrinciple.lean`. Provides the
mechanism × EP-level matrix as a pure-Python dictionary lookup, plus
named numerical constants for the MICROSCOPE bound, STEP target, and
the two vestigial-phase η scales.

EP levels (in order of strength):
- WEP: Weak EP. Violation parameter η = (a_1 - a_2)/½(a_1 + a_2).
       MICROSCOPE bound (Touboul et al., PRL 119, 231101, 2017): η < 1e-15.
- EEP: Einstein EP = WEP + LLI + LPI.
- SEP: Strong EP = EEP + universal grav-self-energy coupling
       (Nordtvedt parameter η_N).

Mechanism × EP profile:
- vestigial differential coupling (η = 1 maximal, ruled out): violates WEP.
- vestigial relics STEP-class (η ~ 1e-18, sub-MICROSCOPE):       violates WEP.
- FangGu torsion DM (kinematic failure, w_FG = 1/3):             does NOT violate.
- fracton subdiffusion (universal):                              does NOT violate.
- SFDM Thomas-Fermi (single-field uniform):                      does NOT violate.
- hidden-sector ℤ₁₆ singlet (SM-singlet, decoupled):             does NOT violate.

Numerical constants come from the published primary sources and are
referenced in the docstrings + per-entry comments.
"""

from __future__ import annotations

from enum import Enum
from typing import Optional


class EPLevel(Enum):
    """Three levels of the Equivalence Principle.

    Ordered (by `numerical_order`) from weakest to strongest:
    WEP < EEP < SEP. A WEP-violator implies EEP- and SEP-violation.
    """

    WEP = "WEP"
    EEP = "EEP"
    SEP = "SEP"

    @property
    def numerical_order(self) -> int:
        return {EPLevel.WEP: 0, EPLevel.EEP: 1, EPLevel.SEP: 2}[self]


class EPMechanism(Enum):
    """The six Phase 5x DM-related mechanisms classified for EP-violation."""

    vestigialDifferentialCoupling = "vestigialDifferentialCoupling"
    vestigialReliscSTEPClass = "vestigialReliscSTEPClass"
    fangGuTorsionTrace = "fangGuTorsionTrace"
    fractonSubdiffusion = "fractonSubdiffusion"
    sfdmThomasFermi = "sfdmThomasFermi"
    hiddenSectorZ16Singlet = "hiddenSectorZ16Singlet"


# === Numerical constants (load-bearing for paper34 + figure) ===

#: MICROSCOPE bound on WEP-violation parameter η. Touboul et al.,
#: PRL 119, 231101 (2017). Current best terrestrial/satellite constraint.
MICROSCOPE_BOUND: float = 1e-15

#: STEP-class satellite mission target sensitivity. Next-generation
#: EP-violation test (Phase 6 vestigial relics anchor; W8 hook line 3).
STEP_TARGET: float = 1e-18

#: Vestigial-phase EP-violation parameter (maximal). Per
#: `VestigialGravity.ep_violation`: Δ_EP = 1 in vestigial phase
#: (metric ≠ 0, tetrad VEV = 0 → fermions and bosons couple to
#: different gravitational fields). Already ruled out at any current
#: η-precision.
VESTIGIAL_PHASE_ETA_MAX: float = 1.0

#: Vestigial-relics EP-violation parameter. Per W8 §5 ranking line 3:
#: residual differential coupling from vestigial-phase defect remnants
#: in the full-tetrad phase, η ~ 10⁻¹⁸ (STEP-detectable).
VESTIGIAL_RELICS_ETA: float = 1e-18


# === Per-mechanism violation-level assignment ===
#
# `None` ⇒ mechanism satisfies all three EP levels.
# `EPLevel.WEP` ⇒ violates WEP (and hence EEP, SEP).
# `EPLevel.EEP` ⇒ violates EEP and SEP, satisfies WEP.
# `EPLevel.SEP` ⇒ violates SEP only.

_VIOLATION_LEVEL: dict[EPMechanism, Optional[EPLevel]] = {
    EPMechanism.vestigialDifferentialCoupling: EPLevel.WEP,
    EPMechanism.vestigialReliscSTEPClass: EPLevel.WEP,
    EPMechanism.fangGuTorsionTrace: None,
    EPMechanism.fractonSubdiffusion: None,
    EPMechanism.sfdmThomasFermi: None,
    EPMechanism.hiddenSectorZ16Singlet: None,
}


def violation_level(m: EPMechanism) -> Optional[EPLevel]:
    """Return the weakest EP level violated by `m`, or `None` if none.

    Mirrors `EquivalencePrinciple.violationLevel` in Lean.
    """
    return _VIOLATION_LEVEL[m]


def violates_at(m: EPMechanism, level: EPLevel) -> bool:
    """Return True iff mechanism `m` violates EP at level `level`.

    A WEP-violator violates WEP, EEP, and SEP (since WEP ⊂ EEP ⊂ SEP
    in implication strength). Mirrors `EquivalencePrinciple.violatesAt`.
    """
    weakest = violation_level(m)
    if weakest is None:
        return False
    return weakest.numerical_order <= level.numerical_order


def satisfies_at(m: EPMechanism, level: EPLevel) -> bool:
    """Return True iff mechanism `m` satisfies EP at level `level`."""
    return not violates_at(m, level)


# === The 6×3 EP-violation matrix (mechanisms × WEP/EEP/SEP) ===
#
# Used to render `fig_ep_violation_matrix` in `visualizations.py`.
# Cell value is "violates" or "satisfies".

EP_VIOLATION_MATRIX: dict[EPMechanism, dict[EPLevel, bool]] = {
    m: {L: violates_at(m, L) for L in EPLevel} for m in EPMechanism
}
