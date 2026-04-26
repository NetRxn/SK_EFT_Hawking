"""Phase 6a Wave 5 — BH thermodynamics four laws + regime partition.

Python mirror of `lean/SKEFTHawking/BHThermodynamicsFourLaws.lean`.

Subpackage scope:
- `regime_classifier`: Schwarzschild / BEC-acoustic (`ADWExtremality` constructor)
  / Boundary classification per `M ⋛ M_c(α_ADW, Λ_UV, N_f)`.
- `acoustic_evolution`: Balbinot 2005 BEC-acoustic time-evolution
  `T_H(t) = T_H,0 · exp(-t/τ_cool)` + Schwarzschild `T_H = 1/(8π M)`
  contrast + δ_ADW ansatz. (Replaces the deleted `schottky_saturation`
  module from initial Wave 5 ship; see process review at
  `papers/AutomatedReviews/2026-04-26-2230-wave5-process/deep_research_analog_conflation.md`.)
- `four_laws_data`: regime-dependent four-laws bundle dataclasses with
  evap-sign field replacing the previous heat-capacity sign.
- `falsifier_checks`: numerical implementations of the four Wave 5
  falsifiers (acoustic-decay-form, schwarzschild-heating, third-law-form,
  χ_vest dependence).

Primary references:
- Balbinot, Fagnocchi, Fabbri, Procopio, **PRD 71, 064019 (2005)**,
  arXiv:gr-qc/0405098 — primary anchor for BEC-acoustic cooling regime.
- Hawking, **CMP 43, 199 (1975)** — primary anchor for Schwarzschild
  heating regime.
- Glorioso-Liu arXiv:1612.07705 — SK-EFT second law (no NEC).
- Kehle-Unger arXiv:2211.15742; Reall arXiv:2410.11956 — third-law
  conditional on BPS local mass-charge inequality.
"""

from src.bh_thermodynamics.regime_classifier import (
    Regime,
    ADWParams,
    BHData,
    M_c_default,
    classify,
)
from src.bh_thermodynamics.acoustic_evolution import (
    T_H_acoustic_evolution,
    T_H_acoustic_evolution_grid,
    T_H_schwarzschild,
    T_H_schwarzschild_grid,
    delta_ADW_ansatz,
)
from src.bh_thermodynamics.four_laws_data import (
    FourLawsSchwarzschild,
    FourLawsADWExtremality,
)
from src.bh_thermodynamics.falsifier_checks import (
    falsifier_acoustic_decay_form,
    falsifier_schwarzschild_heating,
    falsifier_third_law_form,
    falsifier_alpha_ADW_dependence,
)

__all__ = [
    'Regime',
    'ADWParams',
    'BHData',
    'M_c_default',
    'classify',
    'T_H_acoustic_evolution',
    'T_H_acoustic_evolution_grid',
    'T_H_schwarzschild',
    'T_H_schwarzschild_grid',
    'delta_ADW_ansatz',
    'FourLawsSchwarzschild',
    'FourLawsADWExtremality',
    'falsifier_acoustic_decay_form',
    'falsifier_schwarzschild_heating',
    'falsifier_third_law_form',
    'falsifier_alpha_ADW_dependence',
]
