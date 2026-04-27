"""Topological order beyond Landau-Ginzburg — Phase 6d Wave 3.

Mirrors `lean/SKEFTHawking/CFLChiralLagrangian.lean` §5.

The CFL phase is the canonical example of topological order in a
strongly-coupled QCD context: phases with the same local order
parameter are distinguished by the emergent ℤ_3 one-form symmetry
(Hirono-Tanizaki framing). The non-trivial ℤ_3 charge is invisible
to local probes.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class H_TopologicalOrderBeyondLG:
    """Tracked-hypothesis predicate: charge ∈ {1, 2} characterizes
    topological order beyond Landau-Ginzburg in the CFL phase.

    Mirrors Lean `H_TopologicalOrderBeyondLG`. Two independent
    constraints:
      (a) `charge < 3` (cyclic ℤ_3 = {0, 1, 2}).
      (b) `charge ≠ 0` (non-trivial sector).
    """

    charge: int

    @property
    def cyclic_z3(self) -> bool:
        """Conjunct (a): charge < 3."""
        return self.charge < 3

    @property
    def nontrivial(self) -> bool:
        """Conjunct (b): charge ≠ 0."""
        return self.charge != 0

    @property
    def holds(self) -> bool:
        """Both conjuncts (drop-conjunct test passes)."""
        return self.cyclic_z3 and self.nontrivial
