"""Scalar linear perturbation theory around an FRW background.

Mirrors `lean/SKEFTHawking/CosmologicalPerturbations.lean` — regime
predicates, growth factors, and admissibility criterion.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

import numpy as np

from src.core import formulas
from src.core.constants import COSMOLOGICAL_PERTURBATIONS_PARAMS


class PerturbationRegime(str, Enum):
    """Mode-evolution regime determined by the sign of `c_s²`.

    Mirrors Lean: `OscillatoryRegime` / `GradientInstabilityRegime`.
    """

    OSCILLATORY = "oscillatory"          # c_s² > 0 — bounded cos(...)
    GRADIENT_INSTABILITY = "instability"  # c_s² < 0 — unbounded cosh(...)
    NEUTRAL = "neutral"                   # c_s² = 0 — frozen mode


@dataclass(frozen=True)
class LinearPerturbation:
    """Scalar perturbation data: sound speed squared, comoving wavenumber,
    conformal time. Mirrors Lean `LinearPerturbationData`.
    """

    cs_sq: float
    k_wavenumber: float   # 1/Mpc
    eta: float             # Mpc

    def __post_init__(self) -> None:
        if self.k_wavenumber <= 0:
            raise ValueError("k_wavenumber must be positive (genuine sub-horizon mode)")
        if self.eta <= 0:
            raise ValueError("eta must be positive (after Big Bang)")


def classify_regime(cs_sq: float) -> PerturbationRegime:
    """Return the perturbation regime for a background of given `c_s²`.

    Lean: `OscillatoryRegime` / `GradientInstabilityRegime` predicates +
    `regimes_complete_when_nonzero`.
    """
    if cs_sq > 0:
        return PerturbationRegime.OSCILLATORY
    if cs_sq < 0:
        return PerturbationRegime.GRADIENT_INSTABILITY
    return PerturbationRegime.NEUTRAL


def growth_factor(perturbation: LinearPerturbation) -> float:
    """Linear-perturbation growth factor at conformal time `η`.

    Lean: composite of `oscillatoryGrowthFactor` / `instabilityGrowthFactor`
    selected by regime. Mirrors `formulas.linear_growth_factor` but takes a
    structured input.
    """
    return formulas.linear_growth_factor(
        perturbation.cs_sq, perturbation.k_wavenumber, perturbation.eta
    )


def is_admissible_background(
    cs_sq: float,
    threshold: float | None = None,
) -> bool:
    """Spectrum-admissibility predicate.

    Lean: `IsAdmissibleBackground`. A background is admissible iff
    `c_s² > threshold` (default 0).
    """
    if threshold is None:
        threshold = COSMOLOGICAL_PERTURBATIONS_PARAMS["CS_SQ_ADMISSIBILITY_THRESHOLD"]
    return formulas.is_admissible_background(cs_sq, threshold=threshold)


# ─── Phase 5y cross-bridge specializations ───────────────────────────


def vestigial_perturbation_at_zero(
    k_wavenumber: float, eta: float
) -> LinearPerturbation:
    """Vestigial-EOS perturbation at the deep-vestigial limit τ = 0.

    Lean: `vestigialDataAtZero`. Substitutes
    `cs_sq_vest(0) = -1/3` from `VestigialEOS.cs_sq_vest_at_zero`.
    """
    return LinearPerturbation(
        cs_sq=COSMOLOGICAL_PERTURBATIONS_PARAMS[
            "OMEGA_J_SQ_OVER_K_SQ_VESTIGIAL_AT_ZERO"
        ],
        k_wavenumber=k_wavenumber,
        eta=eta,
    )


def lambda_cdm_perturbation(
    k_wavenumber: float, eta: float
) -> LinearPerturbation:
    """ΛCDM-style perturbation with `c_s² = 1` (relativistic-fluid limit).

    Lean: `lambdaCDMData`.
    """
    return LinearPerturbation(
        cs_sq=COSMOLOGICAL_PERTURBATIONS_PARAMS["CS_SQ_LAMBDA_CDM"],
        k_wavenumber=k_wavenumber,
        eta=eta,
    )


__all__ = [
    "PerturbationRegime",
    "LinearPerturbation",
    "classify_regime",
    "growth_factor",
    "is_admissible_background",
    "vestigial_perturbation_at_zero",
    "lambda_cdm_perturbation",
]
