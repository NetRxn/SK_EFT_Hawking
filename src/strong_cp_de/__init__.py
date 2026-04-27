"""Phase 6c Wave 1 — Strong-CP ↔ Topological Dark Energy bridge.

Python mirror of `lean/SKEFTHawking/StrongCPTopologicalDE.lean`.

Subpackage scope:
- `zhitnitsky_eval`: Zhitnitsky DE prediction `ρ_DE ~ Λ_QCD^6 / M_P^2`,
  no free parameters; numerical match within ~3 orders of magnitude
  of observed `ρ_DE = (2.3 meV)^4`.
- `combined_de_consistency`: correctness-push tracked-hypothesis check
  that combining Zhitnitsky + q-theory DE both-active yields
  inconsistency with observation.

Cross-references:
- `lean/SKEFTHawking/Z16AnomalyComputation.lean`: Z16 anomaly cancellation.
- `lean/SKEFTHawking/ModularInvarianceConstraint.lean`: framing anomaly
  c₋ ≡ 0 mod 24.

Primary references:
- Van Waerbeke-Zhitnitsky, arXiv:2506.14182 (2025): QCD topological DE.
- Klinkhamer-Volovik, JETP Lett. 91 (2010): q-theory DE.
- Pendlebury et al., PRD 92 (2015): neutron EDM bound on θ.
- Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md §6 (6c.1).
"""

from .zhitnitsky_eval import (
    LAMBDA_QCD_GEV,
    NEUTRON_EDM_BOUND,
    RHO_DE_OBSERVED_EV4,
    ThetaVacuum,
    zhitnitsky_de_eV4,
    zhitnitsky_within_three_orders_of_observation,
)
from .combined_de_consistency import (
    H_BothActiveGivesInconsistency,
    combined_zhitnitsky_qtheory_exceeds_observation,
)

__all__ = [
    "LAMBDA_QCD_GEV",
    "NEUTRON_EDM_BOUND",
    "RHO_DE_OBSERVED_EV4",
    "ThetaVacuum",
    "zhitnitsky_de_eV4",
    "zhitnitsky_within_three_orders_of_observation",
    "H_BothActiveGivesInconsistency",
    "combined_zhitnitsky_qtheory_exceeds_observation",
]
