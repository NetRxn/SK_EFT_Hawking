"""Planck 2018 base-ΛCDM reference + admissibility verdict.

Mirrors `lean/SKEFTHawking/CosmologicalPerturbations.lean` §7-§8 —
admissibility predicate and bundled-Prop falsifier.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np

from src.core.constants import COSMOLOGICAL_PERTURBATIONS_PARAMS

from .cmb_spectrum import (
    cmb_growth_amplitude_max,
    spectrum_amplitude_at_ell,
    spectrum_diverges_at_high_ell,
)
from .linear_perturbations import is_admissible_background


# ─── Planck 2018 reference cosmology ─────────────────────────────────


@dataclass(frozen=True)
class PlanckReference:
    """Planck 2018 base-ΛCDM cosmological parameters relevant to the
    perturbation-amplitude check.
    """

    n_s: float = COSMOLOGICAL_PERTURBATIONS_PARAMS["N_S_PLANCK"]
    A_s: float = COSMOLOGICAL_PERTURBATIONS_PARAMS["A_S_PLANCK"]
    sigma_8: float = COSMOLOGICAL_PERTURBATIONS_PARAMS["SIGMA_8_PLANCK"]
    tau_reio: float = COSMOLOGICAL_PERTURBATIONS_PARAMS["TAU_REIO_PLANCK"]
    k_pivot_inv_mpc: float = COSMOLOGICAL_PERTURBATIONS_PARAMS[
        "K_PIVOT_PLANCK_INV_MPC"
    ]
    ell_pivot_for_falsification: int = int(
        COSMOLOGICAL_PERTURBATIONS_PARAMS["ELL_PIVOT_FOR_FALSIFICATION"]
    )
    fractional_tolerance: float = COSMOLOGICAL_PERTURBATIONS_PARAMS[
        "PLANCK_TT_FRACTIONAL_TOLERANCE"
    ]


# ─── Admissibility verdict ───────────────────────────────────────────


@dataclass(frozen=True)
class AdmissibilityVerdict:
    """Outcome of the admissibility check on a candidate background."""

    is_admissible: bool
    cs_sq: float
    spectrum_amplitude_at_pivot: float
    diverges: bool
    rationale: str


def evaluate_admissibility(
    cs_sq: float,
    reference: PlanckReference | None = None,
) -> AdmissibilityVerdict:
    """Evaluate whether a background of given `c_s²` produces a
    spectrum-amplitude consistent with the Planck cosmic-variance
    ceiling at the falsification pivot.

    Returns an `AdmissibilityVerdict` with three independent fields plus
    a textual rationale.
    """
    if reference is None:
        reference = PlanckReference()

    admissible = is_admissible_background(cs_sq)
    amplitude = spectrum_amplitude_at_ell(
        cs_sq, float(reference.ell_pivot_for_falsification)
    )
    diverges = spectrum_diverges_at_high_ell(cs_sq, reference.ell_pivot_for_falsification)

    if admissible and not diverges:
        rationale = (
            "Background admissible (c_s² > 0); spectrum amplitude bounded "
            "at the falsification pivot."
        )
    elif not admissible and diverges:
        rationale = (
            "Background non-admissible (c_s² ≤ 0); spectrum amplitude "
            f"= {amplitude:.3e} at ℓ = {reference.ell_pivot_for_falsification} "
            "diverges past Planck cosmic-variance ceiling."
        )
    else:
        # Edge case: non-admissible but the schematic amplitude happens
        # not to exceed the threshold (only at very small k or close to
        # the c_s² = 0 boundary).
        rationale = (
            f"Edge case: admissible={admissible} but diverges={diverges}. "
            "Likely sub-threshold amplitude at the pivot ℓ; not a clean "
            "falsification signal."
        )

    return AdmissibilityVerdict(
        is_admissible=admissible,
        cs_sq=cs_sq,
        spectrum_amplitude_at_pivot=amplitude,
        diverges=diverges,
        rationale=rationale,
    )


def vestigial_falsification_check(
    reference: PlanckReference | None = None,
) -> AdmissibilityVerdict:
    """Specialization of `evaluate_admissibility` to the vestigial-EOS
    background at the deep-vestigial limit τ = 0.

    Mirrors Lean theorem
    `vestigial_at_zero_falsifies_H_StableSpectrum`.
    """
    cs_sq_vest_at_zero = COSMOLOGICAL_PERTURBATIONS_PARAMS[
        "OMEGA_J_SQ_OVER_K_SQ_VESTIGIAL_AT_ZERO"
    ]
    return evaluate_admissibility(cs_sq_vest_at_zero, reference)


__all__ = [
    "PlanckReference",
    "AdmissibilityVerdict",
    "evaluate_admissibility",
    "vestigial_falsification_check",
]
