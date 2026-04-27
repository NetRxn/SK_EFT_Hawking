"""Per-DM-candidate BBN-conformance evaluator — Phase 6b Wave 1.

Mirrors `lean/SKEFTHawking/BBN.lean` §3 + §4. Each Phase 5x candidate
is evaluated against a 3-field `BBNConformance` predicate; the
verdict is structural (parametric on candidate-specific observables)
plus literature-cited tracked-hypothesis values.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Optional

from .abundances import (
    N_EFF_2SIGMA_SLACK,
    OMEGA_B_H2_SIGMA,
)


class DMCandidate(Enum):
    """The five Phase 5x emergent-gravity DM candidates classified for
    BBN conformance. Aligned with
    `lean/SKEFTHawking/DarkSectorSynthesis.lean::EmergentGravityDMKind`.
    """

    Z16Topological_T0 = "Z16Topological_T0"
    Z16Singlet_S0 = "Z16Singlet_S0"
    Z16Mixed_C1 = "Z16Mixed_C1"
    FGTorsion = "FGTorsion"
    FractonPWave = "FractonPWave"


@dataclass(frozen=True)
class BBNConformance:
    """Three-field BBN-conformance verdict per candidate. Mirrors
    `H_BBN_Conformance` Lean structure: three mutually-independent
    fields (drop-conjunct test passes — each can fail independently).
    """

    omega_b_consistent: bool       # |Δ Ω_B h²| ≤ 2σ_Planck
    delta_n_eff_within_bound: bool # ΔN_eff ≤ 0.34
    injection_below_threshold: bool  # late-decay rate ≤ photodiss threshold

    @property
    def is_conformant(self) -> bool:
        """All three independent constraints satisfied."""
        return (
            self.omega_b_consistent
            and self.delta_n_eff_within_bound
            and self.injection_below_threshold
        )


def bbn_conformance(
    candidate: DMCandidate,
    delta_omega_b: float = 0.0,
    delta_n_eff: float = 0.0,
    injection_rate: float = 0.0,
) -> BBNConformance:
    """Evaluate BBN conformance for a candidate given its observables.

    Parametric — the user supplies the candidate-specific
    `delta_n_eff` etc.; this function returns the structural verdict.
    Mirrors the Lean `H_BBN_Conformance` constructor.

    Reference defaults (literature-cited tracked-hypothesis values for
    each candidate):
    - Z16Topological_T0: all three δ values = 0 (no local ops, no
      thermalization, no injection). BBN-conformant unconditionally.
    - Z16Mixed_C1: all three δ values = 0 (dark-SU(3) confining,
      Λ_dark > T_BBN). BBN-conformant unconditionally.
    - FractonPWave: all three δ values = 0 (σ_eff = 0 from dipole
      conservation). BBN-conformant unconditionally.
    - Z16Singlet_S0: δN_eff conditional on thermalization. If 3
      sterile Weyl fully thermalize, δN_eff = 3.0 ⟹ violates 0.34.
    - FGTorsion: δN_eff conditional on radiation-thermalization. If
      FG e-loops thermalize as radiation, δN_eff ≥ 1.0 ⟹ violates 0.34.
    """
    return BBNConformance(
        omega_b_consistent=abs(delta_omega_b) <= 2.0 * OMEGA_B_H2_SIGMA,
        delta_n_eff_within_bound=delta_n_eff <= N_EFF_2SIGMA_SLACK,
        injection_below_threshold=injection_rate <= 1.0e-30,
    )


# Reference tracked-hypothesis values per candidate (literature-cited
# defaults; downstream callers can override).

_DEFAULT_DELTA_N_EFF: dict[DMCandidate, float] = {
    DMCandidate.Z16Topological_T0: 0.0,    # K-gauge TQFT, no local ops
    DMCandidate.Z16Singlet_S0: 3.0,         # 3 sterile Weyl fully thermalize
    DMCandidate.Z16Mixed_C1: 0.0,           # dark-SU(3) confined at T_BBN
    DMCandidate.FGTorsion: 1.0,             # radiation-thermalized FG e-loops
    DMCandidate.FractonPWave: 0.0,          # σ_eff = 0
}


def evaluate_all_candidates(
    n_eff_overrides: Optional[dict[DMCandidate, float]] = None,
) -> dict[DMCandidate, BBNConformance]:
    """Evaluate all five Phase 5x candidates against BBN constraints
    using literature-cited default `δN_eff` values (overridable).

    Returns the verdict matrix used by `tests/test_bbn.py` and
    `fig_bbn_conformance_matrix`.
    """
    overrides = n_eff_overrides or {}
    return {
        candidate: bbn_conformance(
            candidate=candidate,
            delta_n_eff=overrides.get(candidate, default_n_eff),
        )
        for candidate, default_n_eff in _DEFAULT_DELTA_N_EFF.items()
    }
