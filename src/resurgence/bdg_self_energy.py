"""
BdG self-energy diagrammatics for the BEC SK-EFT gradient expansion (Path A).

Phase 6n Wave 1a.3 Path A — Stage 1 module skeleton.

This module computes the Bogoliubov-de Gennes self-energy coefficients
γ_1, γ_2, ..., γ_7 from first principles (loop expansion of the BdG
self-energy) and feeds them into ``src/resurgence/borel.py`` for the
definitive Padé-Borel verdict on the Gevrey-1-vs-geometric question.

**Scope (per ``temporary/working-docs/phase6n/wave_1a_3_path_A_stage1.md``):**

  γ_1  -- Beliaev 1958 (Sov. Phys. JETP 7, 289): LO phonon damping rate
          in uniform BEC at T -> 0. Anchor for cross-validation.
  γ_2  -- Andreev-Khalatnikov 1963 (Sov. Phys. JETP 17, 1384): NLO
          transport coefficient. Anchor for NLO cross-validation.
  γ_3  -- Beliaev-Galitskii 1959 (or modern review): 2-loop self-energy.
  γ_4..γ_7 -- Higher-loop BdG self-energy via systematic loop-order
          enumeration. Genuine new content; multi-session work.

**Stage decomposition:**

  Stage 1 (this module): API + skeleton + skip-marked tests + literature
          anchor citations + module-level docstring.
  Stage 2: γ_1 implementation + cross-validation against Beliaev anchor.
  Stage 3: γ_2 implementation + cross-validation against AK anchor.
  Stage 4: γ_3-γ_5 systematic loop enumeration.
  Stage 5: γ_6-γ_7 + Padé-Borel pipeline re-run + definitive verdict.

**Companion modules:**

  ``src/resurgence/borel.py`` -- consumer of γ_n output (existing).
  ``src/resurgence/beliaev_anchors.py`` -- planned Stage 2 module with
       literature anchor values for γ_1, γ_2 sanity checks.

**MCP-first discipline:** all derivations should be implementable via
direct symbolic/numerical computation in Python (SymPy/SciPy). Aristotle
is NOT load-bearing for Path A; this is paper-math + numerical work +
Lean verdict formalization at Stage 5.

References:
  Beliaev S T, Sov. Phys. JETP 7, 289 (1958) -- LO phonon damping
  Andreev A F, Khalatnikov I M, Sov. Phys. JETP 17, 1384 (1963) -- NLO
  Beliaev S T, Galitskii V M, Sov. Phys. JETP 7, 96 (1958) -- 2-loop
  Pitaevskii L, Stringari S, *Bose-Einstein Condensation* (Oxford 2003) -- modern textbook
  Aniceto, Başar, Schiappa, Phys. Rep. 809 (2019) 1, arXiv:1802.10441 -- Borel-summability framework
  Liu T-S, Fukuyama H, Phys. Rev. B 31, 175 (1985) -- modern Beliaev rate review
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence


# ---------------------------------------------------------------------------
# Stage 1 API skeleton
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class BdGSelfEnergyResult:
    """Container for a BdG self-energy computation at a given loop order.

    Attributes:
        order: loop order n (1 = LO Beliaev; 2 = NLO Andreev-Khalatnikov;
            3+ = higher-loop, genuine new content).
        gamma: dimensionless self-energy coefficient γ_n.
        cross_validated: True if cross-validation against literature anchor
            (Beliaev for γ_1; AK for γ_2) passed within tolerance.
        anchor_citation: literature citation for cross-validation
            (None for higher loops with no published anchor).
        method: "Beliaev-LO" / "AK-NLO" / "BdG-2-loop" / etc.
    """

    order: int
    gamma: float
    cross_validated: bool
    anchor_citation: str | None
    method: str


def compute_gamma_n(order: int, c_s: float, xi: float) -> BdGSelfEnergyResult:
    """Compute the n-th BdG self-energy coefficient γ_n.

    Stage 1 placeholder: raises NotImplementedError. Stage 2+ implements
    the diagrammatic loop expansion via Wick contraction + numerical
    integration (LO + NLO via published anchors; higher loops via
    systematic enumeration).

    Args:
        order: loop order n (1 = LO Beliaev rate).
        c_s: BEC speed of sound (m/s).
        xi: BEC healing length (m).

    Returns:
        BdGSelfEnergyResult with the computed γ_n + provenance.

    Raises:
        NotImplementedError: until Stage 2 (γ_1) ships.

    References:
        Stage 2 implementation follows Beliaev's 1958 derivation
        (LO scattering channels: Beliaev decay + Landau damping) and
        Andreev-Khalatnikov's 1963 NLO transport-coefficient analysis.
    """
    raise NotImplementedError(
        "Stage 1 module skeleton — see "
        "temporary/working-docs/phase6n/wave_1a_3_path_A_stage1.md "
        "for Stage 2+ implementation plan."
    )


def compute_gamma_sequence(
    max_order: int, c_s: float, xi: float
) -> Sequence[BdGSelfEnergyResult]:
    """Compute γ_1 through γ_max_order via systematic loop expansion.

    Stage 1 placeholder. Stage 2+ implements the systematic enumeration.

    Args:
        max_order: highest loop order to compute (target: 7 per Path A scope).
        c_s: BEC speed of sound.
        xi: BEC healing length.

    Returns:
        Sequence of BdGSelfEnergyResult, indexed 0..max_order-1
        corresponding to γ_1..γ_max_order.

    Raises:
        NotImplementedError: until Stage 2+ ship.
    """
    raise NotImplementedError(
        "Stage 1 module skeleton. See wave_1a_3_path_A_stage1.md for "
        "Stage 2+ sub-stage decomposition (γ_1 -> γ_2 -> γ_3-γ_5 -> γ_6-γ_7)."
    )


# ---------------------------------------------------------------------------
# Literature anchor stubs (Stage 2 will populate with verified values)
# ---------------------------------------------------------------------------


def beliaev_anchor_gamma_1() -> float:
    """LO Beliaev rate γ_1 from primary literature.

    Stage 2 deliverable: source the dimensionless Beliaev rate γ_1 from
    Beliaev 1958 (Sov. Phys. JETP 7, 289) or modern review
    (Pitaevskii-Stringari §4.4, Liu-Fukuyama PRB 31, 175 (1985)).

    Stage 1: raises NotImplementedError. Stage 2+ returns the verified
    literature value used as the cross-validation anchor for
    compute_gamma_n(order=1, ...).

    Returns:
        Dimensionless γ_1 (units to be specified at Stage 2).

    Raises:
        NotImplementedError: until Stage 2.
    """
    raise NotImplementedError(
        "Stage 1 anchor stub. Stage 2: populate from Beliaev 1958 + "
        "modern review (Pitaevskii-Stringari §4.4 or Liu-Fukuyama 1985)."
    )


def andreev_khalatnikov_anchor_gamma_2() -> float:
    """NLO Andreev-Khalatnikov γ_2 from primary literature.

    Stage 2 deliverable: source γ_2 from Andreev-Khalatnikov 1963
    (Sov. Phys. JETP 17, 1384) or modern transport-coefficient review.

    Returns:
        Dimensionless γ_2 (units relative to γ_1 to be specified at Stage 2).

    Raises:
        NotImplementedError: until Stage 2.
    """
    raise NotImplementedError(
        "Stage 1 anchor stub. Stage 2: populate from Andreev-Khalatnikov 1963 "
        "or modern review (Pitaevskii-Stringari §4.5)."
    )
