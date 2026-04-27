"""Phase 6d Wave 3 — CFL Chiral Lagrangian.

Python mirror of `lean/SKEFTHawking/CFLChiralLagrangian.lean`.

Subpackage scope:
- `cfl_lagrangian`: CFL diquark order parameter, kinetic + mass terms,
  chiral-limit Goldstone behavior.
- `z3_one_form_action`: emergent ℤ_3 one-form symmetry generator
  (`emergentZ3Phase = exp(2πi/3)`) with the **correctness-push
  identification**: emergent ℤ_3 = QCD center ℤ_3 from W1.
- `topological_order_check`: Hirono-Tanizaki topological-order-beyond-
  Landau-Ginzburg tracked hypothesis.

Cross-references:
- `lean/SKEFTHawking/CenterSymmetryConfinement.lean`: QCD center ℤ_3 source.
- `lean/SKEFTHawking/ChiralSSB_QCD.lean`: chiral-broken-phase substrate.
- `src/center_symmetry/`: numerical companion for W1.
- `src/chiral_ssb/`: numerical companion for W2.

Primary references:
- Alford-Rajagopal-Wilczek, NPB 537 (1999): CFL phase.
- Son-Stephanov, PRL 86 (2001): CFL chiral Lagrangian.
- Hirono-Tanizaki, JHEP 12 (2018): emergent ℤ_3 one-form symmetry.
- Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md §7 (6d.3).
"""

from .cfl_lagrangian import (
    cfl_kinetic_term,
    cfl_mass_term,
    diquark_magnitude,
    is_cfl_phase,
)
from .z3_one_form_action import (
    EMERGENT_Z3_PHASE,
    QCD_CENTER_Z3_PHASE,
    cfl_emergent_z3_matches_qcd_center_z3,
    emergent_z3_action,
    emergent_z3_pow_3,
)
from .topological_order_check import (
    H_TopologicalOrderBeyondLG,
)

__all__ = [
    "cfl_kinetic_term",
    "cfl_mass_term",
    "diquark_magnitude",
    "is_cfl_phase",
    "EMERGENT_Z3_PHASE",
    "QCD_CENTER_Z3_PHASE",
    "cfl_emergent_z3_matches_qcd_center_z3",
    "emergent_z3_action",
    "emergent_z3_pow_3",
    "H_TopologicalOrderBeyondLG",
]
