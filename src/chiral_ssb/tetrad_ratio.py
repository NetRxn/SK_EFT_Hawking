"""Tetrad-VEV / quark-condensate scale-naturalness — Phase 6d Wave 2.

Mirrors `lean/SKEFTHawking/ChiralSSB_QCD.lean` §4.

The Wave 6d.2 correctness-push (HPC-gated for numerical validation): the
tetrad VEV scale and the quark-condensate scale should be within a factor
of 10 of each other for the NJL-ADW correspondence to hold without
fine-tuning.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class H_TetradQuarkScalesNatural:
    """Tracked-hypothesis predicate: tetrad VEV and condensate scale
    are within a factor of 10 of each other.

    Mirrors Lean `H_TetradQuarkScalesNatural` Prop. Three independent
    constraints:
      (a) `sigma_scale > 0`.
      (b) `sigma_scale / 10 ≤ v_tetrad`.
      (c) `v_tetrad ≤ 10 · sigma_scale`.
    """

    v_tetrad: float
    sigma_scale: float

    @property
    def positivity(self) -> bool:
        """Conjunct (a): `sigma_scale > 0`."""
        return self.sigma_scale > 0

    @property
    def lower_bound(self) -> bool:
        """Conjunct (b): `sigma_scale / 10 ≤ v_tetrad`."""
        return self.sigma_scale / 10.0 <= self.v_tetrad

    @property
    def upper_bound(self) -> bool:
        """Conjunct (c): `v_tetrad ≤ 10 · sigma_scale`."""
        return self.v_tetrad <= 10.0 * self.sigma_scale

    @property
    def holds(self) -> bool:
        """All three conjuncts (drop-conjunct test passes)."""
        return self.positivity and self.lower_bound and self.upper_bound
