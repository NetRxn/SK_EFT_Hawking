"""Phase 6d Wave 2 — Chiral Symmetry Breaking in QCD.

Python mirror of `lean/SKEFTHawking/ChiralSSB_QCD.lean`.

Subpackage scope:
- `quark_condensate`: ⟨q̄q⟩ encoded as a negative-real dataclass with
  IsCandidate predicate (within fractional tolerance of FLAG-2021 lattice
  central value −0.0227 GeV³).
- `gmor_check`: GMOR relation `m_π² · f_π² = −2 m_q · ⟨q̄q⟩` with PDG
  numerical agreement check at central values (LHS = 1.589e-4 GeV⁴ ≈ RHS).
- `tetrad_ratio`: Tetrad-VEV / quark-condensate scale-naturalness tracked
  hypothesis (correctness-push, HPC-gated).

Cross-references:
- `lean/SKEFTHawking/WetterichNJL.lean`: scalar channel attractive ⟹
  quark condensate forms.
- `lean/SKEFTHawking/TetradGapEquation.lean`: bifurcation supports
  condensate scale.

Primary references:
- Nambu-Jona-Lasinio, PR 122 (1961).
- Gell-Mann, Oakes, Renner, PR 175 (1968).
- FLAG Working Group, EPJC 81 (2021): ⟨q̄q⟩ ≈ −(283 MeV)³.
- PDG 2022: m_π, f_π, light-quark mass averages.
- Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md §7 (6d.2).
"""

from .quark_condensate import (
    QuarkCondensate,
    FLAG_LATTICE_VALUE,
    is_quark_condensate_candidate,
)
from .gmor_check import (
    PDG_M_PI,
    PDG_F_PI,
    PDG_M_Q,
    gmor_lhs,
    gmor_rhs,
    gmor_holds,
    gmor_pdg_match,
)
from .tetrad_ratio import (
    H_TetradQuarkScalesNatural,
)

__all__ = [
    "QuarkCondensate",
    "FLAG_LATTICE_VALUE",
    "is_quark_condensate_candidate",
    "PDG_M_PI",
    "PDG_F_PI",
    "PDG_M_Q",
    "gmor_lhs",
    "gmor_rhs",
    "gmor_holds",
    "gmor_pdg_match",
    "H_TetradQuarkScalesNatural",
]
