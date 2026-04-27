"""Quark condensate ⟨q̄q⟩ — Phase 6d Wave 2.

Mirrors `lean/SKEFTHawking/ChiralSSB_QCD.lean` §1. The condensate is
encoded with the load-bearing constraint that it is NEGATIVE in the QCD
vacuum — the negative sign drives chiral SSB via GMOR.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class QuarkCondensate:
    """Quark bilinear ⟨q̄q⟩ in [GeV³] with negativity constraint.

    The negative sign is what drives chiral SSB via the GMOR relation
    `m_π² · f_π² = −2 m_q · ⟨q̄q⟩`: with `m_q > 0` and a positive LHS,
    the RHS forces ⟨q̄q⟩ < 0.
    """

    sigma: float

    def __post_init__(self) -> None:
        if self.sigma >= 0:
            raise ValueError(
                f"QuarkCondensate requires sigma < 0 (chiral-broken phase), "
                f"got sigma={self.sigma}"
            )


#: FLAG Working Group 2021 lattice average: ⟨q̄q⟩ ≈ −(283 MeV)³ ≈ −0.0227 GeV³.
#: Mirrors Lean `flagLatticeValue`.
FLAG_LATTICE_VALUE = QuarkCondensate(sigma=-0.0227)


def is_quark_condensate_candidate(
    qc: QuarkCondensate,
    sigma_obs: float,
    tol: float,
) -> bool:
    """Whether `qc.sigma` is within fractional tolerance `tol` of `sigma_obs`.

    Mirrors Lean predicate `IsQuarkCondensateCandidate`. Returns
    `|qc.sigma − sigma_obs| < tol · |sigma_obs|`.
    """
    return abs(qc.sigma - sigma_obs) < tol * abs(sigma_obs)
