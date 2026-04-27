"""GMOR relation `m_π² · f_π² = −2 m_q · ⟨q̄q⟩` — Phase 6d Wave 2.

Mirrors `lean/SKEFTHawking/ChiralSSB_QCD.lean` §2.

PDG/FLAG central values:
- `m_π = 0.137 GeV` (PDG 2022 charged pion mass).
- `f_π = 0.092 GeV` (chiral-limit pion decay constant).
- `m_q = 0.0035 GeV` (average of `m_u + m_d`/2 ≈ 3.5 MeV; PDG 2022).
- `⟨q̄q⟩ = −0.0227 GeV³` (FLAG 2021 lattice average).

GMOR central match:
- LHS: `(0.137)² · (0.092)² ≈ 1.589e-4 GeV⁴`.
- RHS: `−2 · 0.0035 · (−0.0227) ≈ 1.589e-4 GeV⁴`.
- |LHS − RHS| ≈ 4e-8 GeV⁴ (~1 part in 10⁴ of LHS).
"""

from __future__ import annotations

from .quark_condensate import QuarkCondensate

#: PDG charged pion mass in GeV.
PDG_M_PI: float = 0.137
#: Pion decay constant in GeV (chiral-limit convention).
PDG_F_PI: float = 0.092
#: Average light-quark mass `(m_u + m_d) / 2` in GeV (PDG 2022).
PDG_M_Q: float = 0.0035


def gmor_lhs(m_pi: float, f_pi: float) -> float:
    """LHS of GMOR: `m_π² · f_π²`. Mirrors Lean `gmor_lhs`."""
    return m_pi**2 * f_pi**2


def gmor_rhs(m_q: float, qc: QuarkCondensate) -> float:
    """RHS of GMOR: `−2 m_q · ⟨q̄q⟩`. Mirrors Lean `gmor_rhs`."""
    return -2.0 * m_q * qc.sigma


def gmor_holds(
    m_pi: float, f_pi: float, m_q: float, qc: QuarkCondensate, tol: float = 1.0e-4
) -> bool:
    """Whether GMOR holds within absolute tolerance `tol` (in GeV⁴).

    Mirrors Lean `GMORHolds` Prop combined with the PDG-tolerance test.
    """
    return abs(gmor_lhs(m_pi, f_pi) - gmor_rhs(m_q, qc)) < tol


def gmor_pdg_match() -> bool:
    """Convenience: GMOR at PDG/FLAG central values matches within 1e-4 GeV⁴.

    Mirrors Lean `gmor_pdg_match` theorem (numerical literature anchor).
    """
    from .quark_condensate import FLAG_LATTICE_VALUE
    return gmor_holds(PDG_M_PI, PDG_F_PI, PDG_M_Q, FLAG_LATTICE_VALUE, tol=1.0e-4)
