"""Emergent vs bare-matter stress-energy trace comparator.

Mirrors ``emergentStressEnergyTrace``, ``matterStressEnergyTrace``, and
``emergentStressEnergyTrace_minus_matter_eq`` in
``lean/SKEFTHawking/NonlinearEFE.lean``.  The deviation channel
``T_emerg − T_matter = (α_ADW − 1) · ρ_ADW`` is the linear-response
content of Wave 4.
"""

from __future__ import annotations
from dataclasses import dataclass


@dataclass(frozen=True)
class StressEnergyComparison:
    """Comparison of emergent and bare-matter stress-energy traces
    at fixed (ρ_ADW, α_ADW).

    Fields:

    - ``rho_ADW`` — bare matter density (= bare T_matter trace)
    - ``alpha_ADW`` — ADW substrate-rescaling parameter
    - ``T_emerg`` — emergent stress-energy trace
    - ``T_matter`` — bare matter trace
    - ``deviation`` — ``T_emerg − T_matter = (α − 1) · ρ`` (linear in α-1)
    - ``deviation_relative`` — ``deviation / ρ`` for ρ ≠ 0; ``None`` else
    """

    rho_ADW: float
    alpha_ADW: float
    T_emerg: float
    T_matter: float
    deviation: float
    deviation_relative: float | None


def compare_emergent_vs_matter(
    rho_ADW: float,
    alpha_ADW: float,
) -> StressEnergyComparison:
    """Compute the full stress-energy comparison record.

    Lean: NonlinearEFE.emergentStressEnergyTrace,
          NonlinearEFE.emergentStressEnergyTrace_minus_matter_eq
    """
    from src.core.formulas import (
        emergent_stress_energy_trace,
        matter_stress_energy_trace,
        emergent_minus_matter_stress_energy_trace,
    )
    rho = float(rho_ADW)
    alpha = float(alpha_ADW)
    T_e = emergent_stress_energy_trace(rho, alpha)
    T_m = matter_stress_energy_trace(rho)
    dev = emergent_minus_matter_stress_energy_trace(rho, alpha)
    if rho == 0.0:
        rel = None
    else:
        rel = dev / rho
    return StressEnergyComparison(
        rho_ADW=rho,
        alpha_ADW=alpha,
        T_emerg=T_e,
        T_matter=T_m,
        deviation=dev,
        deviation_relative=rel,
    )


def deviation_channel(rho_ADW: float, alpha_ADW: float) -> float:
    """Linear-in-(α-1) deviation channel value.

    Mirrors the Lean theorem
    ``emergentStressEnergyTrace_minus_matter_eq``.

    Lean: NonlinearEFE.emergentStressEnergyTrace_minus_matter_eq
    """
    from src.core.formulas import emergent_minus_matter_stress_energy_trace
    return emergent_minus_matter_stress_energy_trace(rho_ADW, alpha_ADW)


def deviation_detectable_at_floor(
    rho_ADW: float,
    alpha_ADW: float,
    detect_floor: float | None = None,
) -> bool:
    """Is the relative T_emerg deviation above the detection floor?

    Returns ``True`` iff ``|deviation/ρ| > detect_floor`` (default:
    ``NONLINEAR_EFE_PARAMS['T_EMERG_DEVIATION_DETECT_FLOOR'] = 5e-3``).
    Falsifies the calibrated reading at the observable level.

    Lean: NonlinearEFE.emergentStressEnergyTrace_eq_matter_iff_alpha_unity
    """
    from src.core.constants import NONLINEAR_EFE_PARAMS
    if detect_floor is None:
        detect_floor = NONLINEAR_EFE_PARAMS['T_EMERG_DEVIATION_DETECT_FLOOR']
    if float(rho_ADW) == 0.0:
        return False
    rel_dev = abs(deviation_channel(rho_ADW, alpha_ADW) / float(rho_ADW))
    return rel_dev > float(detect_floor)
