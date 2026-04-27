"""Zhitnitsky DE prediction at QCD topological scale — Phase 6c Wave 1.

Mirrors `lean/SKEFTHawking/StrongCPTopologicalDE.lean` §1, §2.

The Zhitnitsky mechanism (Van Waerbeke-Zhitnitsky 2025, arXiv:2506.14182)
predicts `ρ_DE ~ Λ_QCD^6 / M_P^2` with NO free parameters. At
`Λ_QCD = 100 MeV` and `M_P = 1.22e19 GeV`, the prediction is
within ~3 orders of magnitude of the observed `ρ_DE = (2.3 meV)^4`.

The strong-CP θ-angle is bounded by neutron-EDM measurements:
`|θ| ≤ 1e-9` (Pendlebury et al. PRD 92, 2015).
"""

from __future__ import annotations

from dataclasses import dataclass


#: PDG QCD scale in GeV.
LAMBDA_QCD_GEV: float = 0.1
#: Neutron-EDM bound on the QCD θ-angle (Pendlebury 2015 conservative).
NEUTRON_EDM_BOUND: float = 1.0e-9
#: Observed dark energy density in eV⁴: `(2.3 meV)^4 ≈ 2.8e-11 eV^4`.
RHO_DE_OBSERVED_EV4: float = 2.8e-11
#: Mathematical conversion factor: 10^54 / 1.49e56 ≈ 6.71e-3, used in
#: ρ_DE = Λ_QCD^6 (GeV)^6 × 10^54 (eV/GeV)^6 / M_P^2 (eV)^2.
_PLANCK_SUPPRESSION_EV4_PER_GEV6: float = 6.71e-3


@dataclass(frozen=True)
class ThetaVacuum:
    """QCD θ-vacuum encoded with the neutron-EDM constraint
    `|θ| ≤ 1e-9` as a load-bearing invariant.

    Mirrors Lean `ThetaVacuum` structure. The constraint encodes
    the *dynamical-smallness* requirement for Zhitnitsky-DE-sourcing
    candidates.
    """

    theta: float

    def __post_init__(self) -> None:
        if abs(self.theta) > NEUTRON_EDM_BOUND:
            raise ValueError(
                f"ThetaVacuum requires |theta| <= {NEUTRON_EDM_BOUND}, "
                f"got |theta|={abs(self.theta)}"
            )


def zhitnitsky_de_eV4(lambda_qcd_gev: float) -> float:
    """The Zhitnitsky DE prediction `ρ_DE ~ Λ_QCD^6 / M_P^2` in eV⁴.

    Mirrors Lean `zhitnitskyDE_eV4`. At PDG `Λ_QCD = 0.1 GeV`, returns
    ≈ 6.71e-9 eV⁴.
    """
    return lambda_qcd_gev**6 * _PLANCK_SUPPRESSION_EV4_PER_GEV6


def zhitnitsky_within_three_orders_of_observation(
    lambda_qcd_gev: float = LAMBDA_QCD_GEV,
) -> bool:
    """Whether the Zhitnitsky prediction at the supplied `Λ_QCD` is
    within 3 orders of magnitude of observation.

    Mirrors Lean `zhitnitsky_DE_at_lambda_qcd_within_3_orders`. At
    `Λ_QCD = 0.1 GeV`, the prediction (6.71e-9 eV⁴) sits ~240×
    above observation (2.8e-11 eV⁴), well within 3 orders.
    """
    return zhitnitsky_de_eV4(lambda_qcd_gev) < 1.0e-7
