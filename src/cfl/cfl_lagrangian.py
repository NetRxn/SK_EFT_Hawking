"""CFL chiral Lagrangian skeleton — Phase 6d Wave 3.

Mirrors `lean/SKEFTHawking/CFLChiralLagrangian.lean` §1, §4.

The CFL phase is characterized by a non-zero diquark VEV `Φ`. The
kinetic term is the canonical `(1/2)|∂Φ|²`; the mass term is
proportional to `m_q · |Φ|²`, vanishing in the chiral limit.
"""

from __future__ import annotations


def is_cfl_phase(phi: complex, atol: float = 1e-12) -> bool:
    """Whether the diquark VEV characterizes a CFL phase (non-zero |Φ|).

    Mirrors Lean `isCFLPhase`. Returns True iff `|Φ| > atol`.
    """
    return abs(phi) > atol


def diquark_magnitude(phi: complex) -> float:
    """The diquark magnitude `|Φ|`. Mirrors Lean `diquarkMagnitude`."""
    return abs(phi)


def cfl_kinetic_term(d_phi_norm: float) -> float:
    """CFL kinetic term `(1/2) |∂Φ|²`. Mirrors Lean `cflKineticTerm`."""
    return 0.5 * d_phi_norm**2


def cfl_mass_term(m_q: float, phi: complex) -> float:
    """CFL mass term `m_q · |Φ|²`. Mirrors Lean `cflMassTerm`.

    Vanishes in the chiral limit `m_q = 0`; positive when m_q > 0
    AND `is_cfl_phase(phi)` (i.e., |Φ| > 0).
    """
    return m_q * (diquark_magnitude(phi) ** 2)
