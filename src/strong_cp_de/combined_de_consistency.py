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
    """Tracked-hypothesis predicate: combined ρ_DE from both
    mechanisms exceeds observation.

    Mirrors Lean `H_BothActiveGivesInconsistency`.
    """

    rho_de_combined: float

    @property
    def holds(self) -> bool:
        """Returns True iff combined ρ exceeds the threshold 1e-10 eV⁴.

        Bigger than observed ρ_DE = 2.8e-11 by >3×.
        """
        return self.rho_de_combined > 1.0e-10


def combined_zhitnitsky_qtheory_exceeds_observation(
    rho_qtheory: float,
    lambda_qcd_gev: float = LAMBDA_QCD_GEV,
) -> bool:
    """Concrete falsifier: any positive q-theory contribution combined
    with Zhitnitsky at PDG Λ_QCD exceeds observation.

    Mirrors Lean `combined_zhitnitsky_qtheory_exceeds_observation`. At
    `Λ_QCD = 0.1 GeV`, Zhitnitsky alone is 6.71e-9 — adding any
    positive `rho_qtheory` keeps combined > 1e-10.
    """
    if rho_qtheory <= 0:
        raise ValueError(f"rho_qtheory must be positive, got {rho_qtheory}")
    combined = zhitnitsky_de_eV4(lambda_qcd_gev) + rho_qtheory
    return H_BothActiveGivesInconsistency(rho_de_combined=combined).holds
