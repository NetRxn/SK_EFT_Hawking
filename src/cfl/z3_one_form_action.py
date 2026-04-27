"""Emergent ℤ_3 one-form action and the correctness-push — Phase 6d Wave 3.

Mirrors `lean/SKEFTHawking/CFLChiralLagrangian.lean` §2, §3.

THE Phase 6d.3 correctness-push: the CFL emergent ℤ_3 one-form symmetry
generator (Hirono-Tanizaki) equals the QCD center ℤ_3 generator from
Phase 6d Wave 1 (CenterSymmetryConfinement).

Both are `exp(2πi/3)` — the substantive content is the IDENTIFICATION
across two derivations: (a) the bare gauge center symmetry, (b) the
emergent diquark-sector one-form symmetry.
"""

from __future__ import annotations

import math

from src.center_symmetry import Z3, center_phase

#: Emergent ℤ_3 one-form symmetry generator (Hirono-Tanizaki).
#: Defined independently from `center_phase(Z3)` — the equality is
#: a substantive identification, not a definitional alias.
EMERGENT_Z3_PHASE: complex = complex(
    math.cos(2 * math.pi / 3), math.sin(2 * math.pi / 3)
)

#: QCD center ℤ_3 generator from Phase 6d Wave 1.
QCD_CENTER_Z3_PHASE: complex = center_phase(Z3)


def cfl_emergent_z3_matches_qcd_center_z3(atol: float = 1e-10) -> bool:
    """**THE correctness-push:** does the CFL emergent ℤ_3 one-form
    generator equal the QCD center ℤ_3 generator?

    Mirrors Lean `CFL_emergent_Z3_matches_QCD_center_Z3`. Returns True
    iff `|EMERGENT_Z3_PHASE − QCD_CENTER_Z3_PHASE| < atol`.

    Within float precision, both compute to `cos(2π/3) + i·sin(2π/3)`
    — they ARE equal.
    """
    return abs(EMERGENT_Z3_PHASE - QCD_CENTER_Z3_PHASE) < atol


def emergent_z3_action(phi: complex) -> complex:
    """The action of emergent ℤ_3 on a CFL diquark: Φ → ω · Φ.

    Mirrors Lean `emergentZ3Action`.
    """
    return EMERGENT_Z3_PHASE * phi


def emergent_z3_pow_3(atol: float = 1e-10) -> bool:
    """Numerical check: ω³ = 1 (cube root of unity).

    Mirrors Lean `emergentZ3_pow_3`.
    """
    return abs(EMERGENT_Z3_PHASE**3 - 1.0) < atol
