"""Phase 6c Wave 4 — Hayden-Preskill structural QEC on MTC substrate.

Python mirror of `lean/SKEFTHawking/QECHolographyBridge.lean`.

Subpackage scope:
- `code_distance`: code-distance proxy `d_C := log d_max` over MTC spectra
  (Fibonacci, Ising, SU(3)_k=2, trivial-abelian).
- `scrambling_time`: Hayden-Preskill scrambling-time lower bound
  `t_scr := log D² = log Σ d_a²` (proxy for `(β/2π) S_BH` after
  area-law subtraction).

Out of scope (deferred per Phase 6c roadmap §A scope-tightening for W4):
- AdS/CFT spectrum identification.
- Yoshida-Kitaev decoder construction.
- Page-curve quantitative reproduction.

Cross-references:
- `lean/SKEFTHawking/BHEntropyMicroscopic.lean`: HorizonMTCBC substrate
  (Phase 6a Wave 3).
- `lean/SKEFTHawking/FibonacciMTC.lean`: Fibonacci concrete witness.

Primary references:
- Hayden-Preskill, JHEP 2007/9/120 (arXiv:0708.4025): black holes as
  mirrors.
- Almheiri-Dong-Harlow, JHEP 2015/4/163 (arXiv:1411.7041): bulk locality
  + holographic QEC.
- Pastawski-Yoshida-Harlow-Preskill, JHEP 2015/6/149 (arXiv:1503.06237):
  HaPPY codes.
"""

from .code_distance import (
    MTCSpectrum,
    FIBONACCI_SPECTRUM,
    ISING_SPECTRUM,
    SU3K2_SPECTRUM,
    TRIVIAL_ABELIAN_SPECTRUM,
    code_distance,
    code_distance_admissible,
    global_dim_sq,
)
from .scrambling_time import (
    scrambling_time_bound,
    recovery_threshold,
    recovery_possible_at_scrambling_bound,
)

__all__ = [
    "MTCSpectrum",
    "FIBONACCI_SPECTRUM",
    "ISING_SPECTRUM",
    "SU3K2_SPECTRUM",
    "TRIVIAL_ABELIAN_SPECTRUM",
    "code_distance",
    "code_distance_admissible",
    "global_dim_sq",
    "scrambling_time_bound",
    "recovery_threshold",
    "recovery_possible_at_scrambling_bound",
]
