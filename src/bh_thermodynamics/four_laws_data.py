"""Regime-dependent four-laws bundle dataclasses.

Mirrors `FourLaws_Schwarzschild` and `FourLaws_ADWExtremality` Prop
bundles in `lean/SKEFTHawking/BHThermodynamicsFourLaws.lean`. Each
bundle's load-bearing distinguishing field is the **evap_dT_dt sign**
(positive in Schwarzschild = heats; negative in BEC-acoustic = cools)
rather than heat-capacity sign — see provenance correction in
`papers/AutomatedReviews/2026-04-26-2230-wave5-process/deep_research_analog_conflation.md`.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class FourLawsSchwarzschild:
    """Schwarzschild-regime four laws (M > M_c).

    Five mutually-independent fields (mirrors the Lean Prop bundle):
    - `zerothLaw_check`: κ constant on horizon (placeholder).
    - `G_N_emerg`: Wave-1 emergent Newton constant; Smarr-identity coupling
      requires positivity.
    - `secondLaw_check`: SK-EFT entropy current monotonicity (Glorioso-Liu).
    - `thirdLaw_check`: κ → 0 in finite affine time impossible
      (Israel 1986 strong form).
    - `evap_dT_dt`: time-derivative of T_H during Hawking evaporation
      (must be > 0 for the Schwarzschild signature; Hawking 1975).
    """

    G_N_emerg: float
    evap_dT_dt: float
    second_law_check: bool = True
    zeroth_law_check: bool = True
    third_law_check: bool = True

    def is_valid(self) -> bool:
        """Check all five fields satisfy the Schwarzschild signature."""
        return (
            self.G_N_emerg > 0
            and self.evap_dT_dt > 0
            and self.second_law_check
            and self.zeroth_law_check
            and self.third_law_check
        )


@dataclass(frozen=True)
class FourLawsADWExtremality:
    """BEC-acoustic-regime four laws (M < M_c).

    Five mutually-independent fields (mirrors the Lean Prop bundle):
    - `zerothLaw_check`: κ constant on horizon (placeholder).
    - `G_N_emerg`: Wave-1 emergent Newton constant.
    - `delta_ADW`: substrate-response coefficient.
    - `delta_ansatz_predicted`: deep-research §9 predicted value
      `(α_ADW − 1)·Λ_UV`.
    - `secondLaw_check`: SK-EFT entropy current monotonicity.
    - `thirdLaw_check`: third-law form conditional on Reall BPS condition;
      may be violated under Kehle-Unger charged-scalar matter.
    - `evap_dT_dt`: time-derivative of T_H during Hawking evaporation
      (must be < 0 for the BEC-acoustic signature; Balbinot 2005
      Eq. Tsonic).
    """

    G_N_emerg: float
    delta_ADW: float
    delta_ansatz_predicted: float
    evap_dT_dt: float
    second_law_check: bool = True
    zeroth_law_check: bool = True
    third_law_check: bool = True

    def is_valid(self, delta_tolerance: float = 1.0e-12) -> bool:
        """Check all six fields satisfy the BEC-acoustic signature.

        Includes a tolerance check on `delta_ADW` matching the deep-research
        ansatz `(α_ADW − 1)·Λ_UV` (`delta_ansatz_predicted`).
        """
        return (
            self.G_N_emerg > 0
            and self.evap_dT_dt < 0
            and abs(self.delta_ADW - self.delta_ansatz_predicted)
                < delta_tolerance
            and self.second_law_check
            and self.zeroth_law_check
            and self.third_law_check
        )
