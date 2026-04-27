"""KSS bound and Walker-Wang transport prediction — Phase 6d Wave 1.

Mirrors `lean/SKEFTHawking/CenterSymmetryConfinement.lean` §5–§6.

The Kovtun-Son-Starinets (KSS) bound `η/s ≥ 1/(4π)` applies to all
strongly-coupled relativistic QFTs with Einstein-gravity duals. The
Walker-Wang anyon-mediated transport prediction places SU(N) transport
in a narrow window above the bound.

The numerical η/s value from Walker-Wang transport is HPC-gated
(Phase 6B HPC roadmap). This module supports the analytical bracket
[KSS_BOUND, 2 · KSS_BOUND] used in the Lean module's tracked
hypothesis `H_WalkerWangTransportNearKSS`.
"""

from __future__ import annotations

import math
from dataclasses import dataclass


#: The KSS bound on shear viscosity to entropy density: η/s ≥ 1/(4π).
KSS_BOUND: float = 1.0 / (4.0 * math.pi)


@dataclass(frozen=True)
class WalkerWangPrediction:
    """Walker-Wang anyon-mediated transport prediction for η/s.

    Mirrors `H_WalkerWangTransportNearKSS` Lean tracked hypothesis.
    Two independent constraints (drop-conjunct test passes):
      (a) `eta_over_s >= KSS_BOUND` — universal lower bound
      (b) `eta_over_s <= 2 * KSS_BOUND` — Walker-Wang narrow window
    """

    eta_over_s: float

    @property
    def above_kss(self) -> bool:
        """Lower-bound conjunct: η/s ≥ KSS bound."""
        return self.eta_over_s >= KSS_BOUND

    @property
    def below_double_kss(self) -> bool:
        """Upper-bound conjunct: η/s ≤ 2·KSS (Walker-Wang window)."""
        return self.eta_over_s <= 2.0 * KSS_BOUND

    @property
    def consistent(self) -> bool:
        """Both KSS lower and Walker-Wang upper bounds satisfied."""
        return self.above_kss and self.below_double_kss


def walker_wang_consistent_with_kss(eta_over_s: float) -> bool:
    """Convenience: check whether `η/s` is in the Walker-Wang window.

    Returns True iff `KSS_BOUND ≤ η/s ≤ 2 · KSS_BOUND`. Mirrors
    `H_WalkerWangTransportNearKSS` Lean Prop.
    """
    return WalkerWangPrediction(eta_over_s=eta_over_s).consistent
