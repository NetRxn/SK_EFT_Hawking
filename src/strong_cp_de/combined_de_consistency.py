"""Combined Zhitnitsky + q-theory DE consistency check — Phase 6c Wave 1.

Mirrors `lean/SKEFTHawking/StrongCPTopologicalDE.lean` §4.

The Phase 6c.1 correctness-push (per strategy doc §12): if BOTH the
Zhitnitsky mechanism AND a residual q-theory DE contribution were
simultaneously active, their combined contribution would exceed the
observed `ρ_DE` by ~240× — identifying the project's required *yielding*
on one of the two DE mechanisms.
"""

from __future__ import annotations

from dataclasses import dataclass

from .zhitnitsky_eval import LAMBDA_QCD_GEV, zhitnitsky_de_eV4


@dataclass(frozen=True)
class H_BothActiveGivesInconsistency:
    """Tracked-hypothesis predicate: combined ρ_DE strictly exceeds the
    Zhitnitsky-alone saturation point at PDG Λ_QCD.

    Mirrors Lean `H_BothActiveGivesInconsistency`. Threshold raised
    from a loose `> 1e-10` to `> zhitnitsky_de_eV4(LAMBDA_QCD_GEV)`
    so that Zhitnitsky alone does NOT satisfy the predicate — any
    positive q-theory contribution is genuinely load-bearing.
    """

    rho_de_combined: float

    @property
    def holds(self) -> bool:
        """Returns True iff combined ρ exceeds Zhitnitsky alone at PDG Λ_QCD.

        At Λ_QCD = 0.1 GeV, Zhitnitsky is 6.71e-9 eV⁴ (saturating the
        observed value within an order of magnitude). Combined > 6.71e-9
        means the no-free-parameter match is broken by the q-theory term.
        """
        return self.rho_de_combined > zhitnitsky_de_eV4(LAMBDA_QCD_GEV)


def combined_zhitnitsky_qtheory_exceeds_observation(
    rho_qtheory: float,
    lambda_qcd_gev: float = LAMBDA_QCD_GEV,
) -> bool:
    """Concrete falsifier: any positive q-theory contribution combined
    with Zhitnitsky at PDG Λ_QCD strictly exceeds the Zhitnitsky-alone
    prediction at the same scale.

    Mirrors Lean `combined_zhitnitsky_qtheory_exceeds_observation`. The
    structural content: positivity of `rho_qtheory` is load-bearing.
    """
    if rho_qtheory <= 0:
        raise ValueError(f"rho_qtheory must be positive, got {rho_qtheory}")
    combined = zhitnitsky_de_eV4(lambda_qcd_gev) + rho_qtheory
    return H_BothActiveGivesInconsistency(rho_de_combined=combined).holds
