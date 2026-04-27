"""Phase 6d Wave 1 — Center-Symmetry Confinement.

Python mirror of `lean/SKEFTHawking/CenterSymmetryConfinement.lean`.

Subpackage scope:
- `polyakov_loop`: complex Polyakov loop, Confining predicate, center
  Z_N action by ζ_N, and order-parameter formulation (|P| = 0 ⟺ confining).
- `svetitsky_yaffe`: universality-class lookup (SU(2) → Ising,
  SU(3) → 3-state Potts) with literature critical-exponent values.
- `eta_over_s_prediction`: KSS bound 1/(4π) and Walker-Wang transport
  prediction (correctness-push, HPC-gated). Analytical bracket only;
  the η/s numerical validation is in Phase 6B HPC roadmap.

Cross-references:
- `lean/SKEFTHawking/GaugeErasure.lean`: SU(N) → discrete 1-form symmetry.
- `lean/SKEFTHawking/SU3kFusion.lean`: SU(3)_1 fusion = Z_3 ring.

Primary references:
- Polyakov, PLB 72 (1978).
- Svetitsky-Yaffe, NPB 210 (1982).
- Kovtun-Son-Starinets, PRL 94 (2005).
- Pelissetto-Vicari, Physics Reports 368 (2002).
- Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md §7 (6d.1).
"""

from .polyakov_loop import (
    CenterZN,
    Z2,
    Z3,
    center_phase,
    center_action,
    confining,
    polyakov_magnitude,
)
from .svetitsky_yaffe import (
    UniversalityClass,
    svetitsky_yaffe_class,
    critical_exponent_nu,
)
from .eta_over_s_prediction import (
    KSS_BOUND,
    WalkerWangPrediction,
    walker_wang_consistent_with_kss,
)

__all__ = [
    "CenterZN",
    "Z2",
    "Z3",
    "center_phase",
    "center_action",
    "confining",
    "polyakov_magnitude",
    "UniversalityClass",
    "svetitsky_yaffe_class",
    "critical_exponent_nu",
    "KSS_BOUND",
    "WalkerWangPrediction",
    "walker_wang_consistent_with_kss",
]
