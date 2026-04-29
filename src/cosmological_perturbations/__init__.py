"""Phase 6b Wave 2 — Linear cosmological perturbation theory.

Python mirror of `lean/SKEFTHawking/CosmologicalPerturbations.lean`.

Subpackage scope:
- `linear_perturbations`: scalar mode evolution `δ̈ + 2 H δ̇ + c_s² k² δ = 0`
  in the leading-order sub-horizon limit. Regime classification by sign
  of `c_s²` (oscillatory vs gradient-instability).
- `cmb_spectrum`: ℓ-space angular power-spectrum amplitude diagnostic,
  including the unbounded-growth divergence under c_s² < 0.
- `planck_comparison`: Planck 2018 base-ΛCDM reference + admissibility
  predicate against the cosmic-variance-limited fractional ceiling at
  the falsification pivot ℓ = 1500.

Central physical content: the Phase 5y H4 closed-form vestigial-EOS at
the deep-vestigial limit `τ = 0` has `c_s² = -1/3 < 0` (Lean theorem
`VestigialEOS.cs_sq_vest_negative_at_zero`). Linear perturbations of
that background grow as `cosh(√(1/3) · k · η)` rather than oscillating,
producing an unbounded CMB-ℓ spectrum amplitude — falsification of the
vestigial-DE branch at the perturbation level.

Primary references:
- Mukhanov, *Physical Foundations of Cosmology* (CUP, 2005), §7.4.
- Weinberg, *Cosmology* (OUP, 2008), §6.
- Planck Collaboration, A&A 641, A6 (2020) — base ΛCDM cosmology.
- Phase 5y H4 closed form,
  `Lit-Search/Phase-5y/Phase 5y Hypothesis 4 — Effective Fluid EOS for Volovik-Style Vestigial Gravity.md`.
"""

from .linear_perturbations import (
    LinearPerturbation,
    PerturbationRegime,
    classify_regime,
    growth_factor,
    is_admissible_background,
    vestigial_perturbation_at_zero,
    lambda_cdm_perturbation,
)
from .cmb_spectrum import (
    cmb_growth_amplitude_max,
    spectrum_amplitude_at_ell,
    spectrum_diverges_at_high_ell,
)
from .planck_comparison import (
    PlanckReference,
    AdmissibilityVerdict,
    evaluate_admissibility,
    vestigial_falsification_check,
)

__all__ = [
    "LinearPerturbation",
    "PerturbationRegime",
    "classify_regime",
    "growth_factor",
    "is_admissible_background",
    "vestigial_perturbation_at_zero",
    "lambda_cdm_perturbation",
    "cmb_growth_amplitude_max",
    "spectrum_amplitude_at_ell",
    "spectrum_diverges_at_high_ell",
    "PlanckReference",
    "AdmissibilityVerdict",
    "evaluate_admissibility",
    "vestigial_falsification_check",
]
