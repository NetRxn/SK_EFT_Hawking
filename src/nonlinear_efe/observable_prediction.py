"""PPN-style observable predictions under the ADW α_ADW rescaling.

Mirrors ``deflectionRatio``, ``precessionRatio``, ``ringdownRatio``
and the cross-channel multi-observation theorems in
``lean/SKEFTHawking/NonlinearEFE.lean``.

The three canonical observables follow distinct functional forms in
α_ADW:

- Light deflection: linear in α (`δθ_ADW/δθ_GR = α`)
- Perihelion precession: PPN-mixed (`δφ_ADW/δφ_GR = (2α + 1)/3`)
- Ringdown frequency: linear in α (`ω_ADW/ω_GR = α`)

The precession's `(2α + 1)/3` form follows from the standard PPN
combination `(2 + 2γ − β)/3` with `γ = α, β = 1` (Will 2018 Eq. 4.31).
The factor `2/3` makes the perihelion deviation `2/3` times the
deflection deviation — testable structural cross-channel claim.
"""

from __future__ import annotations
from dataclasses import dataclass


@dataclass(frozen=True)
class ObservableSignature:
    """Single-observable prediction record at a specified α_ADW.

    Fields:

    - ``channel`` — observable name
    - ``alpha_ADW`` — calibration-parameter value
    - ``ratio`` — observable / GR baseline
    - ``deviation`` — ``ratio − 1``
    - ``observation_floor`` — relative-precision floor (Will 2018)
    - ``detectable`` — ``|deviation| > observation_floor``
    """

    channel: str
    alpha_ADW: float
    ratio: float
    deviation: float
    observation_floor: float
    detectable: bool


def deflection_signature(alpha_ADW: float,
                          observation_floor: float | None = None
                          ) -> ObservableSignature:
    """Light-deflection signature at α_ADW.

    GR baseline: 1.751 arcsec at solar limb (Will 2018 §4.1).  Best
    relative-precision floor: 3 × 10⁻⁴ from radio VLBI.

    Lean: NonlinearEFE.deflectionRatio,
          NonlinearEFE.deflectionRatio_minus_one_eq,
          NonlinearEFE.deflectionRatio_deviation_exceeds_VLBI_floor
    """
    from src.core.formulas import deflection_ratio
    from src.core.constants import NONLINEAR_EFE_PARAMS
    if observation_floor is None:
        observation_floor = (
            NONLINEAR_EFE_PARAMS['DEFLECTION_OBS_RELATIVE_PRECISION']
        )
    ratio = deflection_ratio(alpha_ADW)
    dev = ratio - 1.0
    return ObservableSignature(
        channel="deflection",
        alpha_ADW=float(alpha_ADW),
        ratio=ratio,
        deviation=dev,
        observation_floor=float(observation_floor),
        detectable=abs(dev) > float(observation_floor),
    )


def precession_signature(alpha_ADW: float,
                          observation_floor: float | None = None
                          ) -> ObservableSignature:
    """Perihelion-precession signature at α_ADW.

    GR baseline: 42.98 arcsec/century (Mercury, Will 2018 §4.2).
    MESSENGER + planetary-radar relative-precision floor: 1 × 10⁻⁴.

    Lean: NonlinearEFE.precessionRatio,
          NonlinearEFE.precessionRatio_eq_one_iff_alpha_unity,
          NonlinearEFE.precession_dev_eq_two_thirds_deflection_dev
    """
    from src.core.formulas import precession_ratio
    from src.core.constants import NONLINEAR_EFE_PARAMS
    if observation_floor is None:
        observation_floor = (
            NONLINEAR_EFE_PARAMS['PERIHELION_OBS_RELATIVE_PRECISION']
        )
    ratio = precession_ratio(alpha_ADW)
    dev = ratio - 1.0
    return ObservableSignature(
        channel="precession",
        alpha_ADW=float(alpha_ADW),
        ratio=ratio,
        deviation=dev,
        observation_floor=float(observation_floor),
        detectable=abs(dev) > float(observation_floor),
    )


def ringdown_signature(alpha_ADW: float,
                        observation_floor: float | None = None
                        ) -> ObservableSignature:
    """GW ringdown-frequency signature at α_ADW.

    GR baseline: ω · GM/c³ = 0.3737 (Schwarzschild ℓ=2 fundamental,
    Berti et al. CQG 26:163001 (2009)).  GWTC-3 spectroscopy
    relative-precision floor: 5 × 10⁻².

    Lean: NonlinearEFE.ringdownRatio
    """
    from src.core.formulas import ringdown_ratio
    from src.core.constants import NONLINEAR_EFE_PARAMS
    if observation_floor is None:
        observation_floor = (
            NONLINEAR_EFE_PARAMS['RINGDOWN_OBS_RELATIVE_PRECISION']
        )
    ratio = ringdown_ratio(alpha_ADW)
    dev = ratio - 1.0
    return ObservableSignature(
        channel="ringdown",
        alpha_ADW=float(alpha_ADW),
        ratio=ratio,
        deviation=dev,
        observation_floor=float(observation_floor),
        detectable=abs(dev) > float(observation_floor),
    )


def deviation_below_observation_floor(
    alpha_ADW: float,
) -> dict[str, bool]:
    """For each observable channel, is the predicted deviation below
    the observation floor?  Returns a dict ``{channel: True/False}``.

    Used by the figure / paper as the multi-channel observation
    pass/fail summary.
    """
    return {
        "deflection": (
            not deflection_signature(alpha_ADW).detectable
        ),
        "precession": (
            not precession_signature(alpha_ADW).detectable
        ),
        "ringdown": (
            not ringdown_signature(alpha_ADW).detectable
        ),
    }


def cross_channel_signature_table(
    alpha_ADW: float,
) -> list[ObservableSignature]:
    """All three observable signatures at a fixed α_ADW.

    Returns the list of signatures for paper / figure consumption.
    Demonstrates the project's testable cross-channel structural claim:
    the precession deviation equals 2/3 of the deflection deviation.

    Lean: NonlinearEFE.precession_dev_eq_two_thirds_deflection_dev
    """
    return [
        deflection_signature(alpha_ADW),
        precession_signature(alpha_ADW),
        ringdown_signature(alpha_ADW),
    ]
