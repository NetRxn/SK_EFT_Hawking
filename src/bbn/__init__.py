"""Phase 6b Wave 1 — BBN unified constraint framework.

Python mirror of `lean/SKEFTHawking/BBN.lean`.

Subpackage scope:
- `abundances`: Standard-BBN observational constants (Planck 2020 +
  PDG 2022 + Cooke 2018 + Sbordone 2010) with 1σ uncertainties.
- `candidate_checker`: per-Phase-5x-DM-candidate BBN-conformance
  evaluator with three independent fields (`omega_b_consistent`,
  `delta_n_eff_within_bound`, `injection_below_threshold`).

Five Phase 5x DM candidates classified (aligned with
`DarkSectorSynthesis.EmergentGravityDMKind`):
- Z16Topological_T0, Z16Mixed_C1, FractonPWave: BBN-conformant.
- Z16Singlet_S0, FGTorsion: BBN-violators conditional on thermalization.

Primary references:
- Planck Collaboration, A&A 641, A6 (2020) — `Ω_B h²`, `N_eff`.
- ParticleDataGroup, BBN Review (2022) — `Y_p`.
- Cooke et al., ApJ 855, 102 (2018) — `D/H`.
- Sbordone et al., A&A 522, A26 (2010) — `Li-7/H`.
"""

from .abundances import (
    OMEGA_B_H2_CENTRAL,
    OMEGA_B_H2_SIGMA,
    Y_P_CENTRAL,
    Y_P_SIGMA,
    D_OVER_H_CENTRAL,
    D_OVER_H_SIGMA,
    LI7_OVER_H_CENTRAL,
    LI7_OVER_H_SIGMA,
    N_EFF_CENTRAL,
    N_EFF_SIGMA,
    N_EFF_2SIGMA_SLACK,
)
from .candidate_checker import (
    DMCandidate,
    BBNConformance,
    bbn_conformance,
    evaluate_all_candidates,
)

__all__ = [
    "OMEGA_B_H2_CENTRAL",
    "OMEGA_B_H2_SIGMA",
    "Y_P_CENTRAL",
    "Y_P_SIGMA",
    "D_OVER_H_CENTRAL",
    "D_OVER_H_SIGMA",
    "LI7_OVER_H_CENTRAL",
    "LI7_OVER_H_SIGMA",
    "N_EFF_CENTRAL",
    "N_EFF_SIGMA",
    "N_EFF_2SIGMA_SLACK",
    "DMCandidate",
    "BBNConformance",
    "bbn_conformance",
    "evaluate_all_candidates",
]
