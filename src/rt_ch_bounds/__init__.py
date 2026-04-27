"""Phase 6c Wave 5 — Ryu-Takayanagi / Casini-Huerta entropy bounds.

Python mirror of `lean/SKEFTHawking/RTCasiniHuertaBounds.lean`.

Subpackage scope:
- `rt_comparison`: classical Ryu-Takayanagi formula `S = A/(4 G_N)` vs
  Phase 6a Wave 3 Kaul-Majumdar microscopic entropy
  `S = A/(4 G_N) - (3/2) log(A/(4 G_N))`.  Quantifies the classical-RT
  vs quantum-microscopic universality-failure gap at canonical reduced
  areas.
- `ch_bound_check`: Casini-Huerta log bound `S(L) ≤ (c/3) log(L/ε)`
  evaluator on saturated witnesses + non-saturated entropy candidates.

Out of scope (deferred per Phase 6c roadmap §A):
- Bulk minimal-surface construction (Lewkowycz-Maldacena replica trick).
- Casini-Huerta proof from modular Hamiltonian.
- Full AdS/CFT spectrum identification.

Cross-references:
- `lean/SKEFTHawking/BHEntropyMicroscopic.lean`: Kaul-Majumdar entropy
  + Sen 4D non-universality witness.
- `lean/SKEFTHawking/QECHolographyBridge.lean` (W4): shared MTC substrate.

Primary references:
- Ryu-Takayanagi PRL 96, 181602 (2006); hep-th/0603001.
- Casini-Huerta J. Phys. A 42, 504007 (2009); arXiv:0905.2562.
"""

from .rt_comparison import (
    classical_rt_entropy,
    kaul_majumdar_entropy,
    rt_kaul_majumdar_gap,
    sen_4d_log_coeff,
    SEN_KAUL_MAJUMDAR_COEFF_GAP,
)
from .ch_bound_check import (
    saturated_ch_entropy,
    ch_log_bound,
    ch_bound_holds,
    central_charge_from_saturation,
)

__all__ = [
    "classical_rt_entropy",
    "kaul_majumdar_entropy",
    "rt_kaul_majumdar_gap",
    "sen_4d_log_coeff",
    "SEN_KAUL_MAJUMDAR_COEFF_GAP",
    "saturated_ch_entropy",
    "ch_log_bound",
    "ch_bound_holds",
    "central_charge_from_saturation",
]
