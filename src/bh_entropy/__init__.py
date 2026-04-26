"""Phase 6a Wave 3: Bekenstein-Hawking entropy from MTC state counting.

Numerical companion to ``lean/SKEFTHawking/BHEntropyMicroscopic.lean``.
All core formulas live in ``src.core.formulas``; this package provides:

- MTC state counting at the horizon (Verlinde formula numerics).
- Entropy coefficient + log-correction structural evaluation across a
  zoo of named MTCs (Fibonacci, Ising, D(S₃), toric code, SU(2)_k for
  k ∈ {2, ..., 10}).
- Horizon spectrum + falsifier-instance status check for each MTC.

**Wave 3 main physics content** (per the Lit-Search/Phase-6a deep-research
return, 2026-04-25):

1. The Kaul-Majumdar SU(2)_k Verlinde derivation gives the unique
   equation-level closed form S = A/(4 G_N) − (3/2) log(A/(4 G_N)) + c_0
   with γ-tuned 1/4 prefactor.
2. The −3/2 log coefficient is structurally ½ (Gaussian saddle) +
   1 (singlet projection); falsifies the toy-model −1/2 ansatz.
3. The 1/4 prefactor is a Sakharov-style tuning, not a derivation —
   encoded as the Immirzi γ field on the Lean structure.
4. The general MTC case ships in Outcome-3 (tracked-hypothesis) mode
   with five falsifier theorems and per-MTC instance status reports.
5. Abelian MTCs (toric code, D(Z_n)) are immediately falsified by F2
   (area-law leading scaling) since log d_max = 0.
"""

from src.bh_entropy.mtc_state_counting import (
    verlinde_dim_at_horizon,
    su2k_quantum_dimensions,
    su2k_S_matrix,
    mtc_global_dim_squared,
)
from src.bh_entropy.entropy_coefficient import (
    kaul_majumdar_entropy_grid,
    leading_coefficient_vs_immirzi,
    log_correction_zoo,
    sen_disagreement_witness,
)
from src.bh_entropy.horizon_spectrum import (
    HorizonMTCInstance,
    fibonacci_instance,
    ising_instance,
    toric_code_instance,
    ds3_instance,
    su2k_instance,
    falsifier_status_table,
)

__all__ = [
    # MTC state counting
    "verlinde_dim_at_horizon",
    "su2k_quantum_dimensions",
    "su2k_S_matrix",
    "mtc_global_dim_squared",
    # Entropy coefficient + log corrections
    "kaul_majumdar_entropy_grid",
    "leading_coefficient_vs_immirzi",
    "log_correction_zoo",
    "sen_disagreement_witness",
    # Horizon spectrum + falsifier status
    "HorizonMTCInstance",
    "fibonacci_instance",
    "ising_instance",
    "toric_code_instance",
    "ds3_instance",
    "su2k_instance",
    "falsifier_status_table",
]
