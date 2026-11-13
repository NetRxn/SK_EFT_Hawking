"""Derived numerals for L1's conditional GW170817 comparison.

SCALARS uses the existing paper-table renderer. Inputs remain the adopted
GW_PARAMS cap and comparison endpoints, not microscopic measurements.
The exact width identity is GravitationalWaves.ligo_window_width_eq; the
formatted values are rounded evaluations, not new physical derivations.
"""

from __future__ import annotations

from src.core.constants import GW_PARAMS
from src.gravitational_waves.ligo_constraint_check import ligo_compatibility_check


def _sci(value: float, places: int) -> str:
    mantissa, exponent = f'{value:.{places}e}'.split('e')
    return f'{mantissa}\\times10^{{{int(exponent)}}}%'


def _width() -> float:
    # Stable preimage width; do not subtract rounded endpoints near unity.
    cap = GW_PARAMS['C_GW_TWO_SIDED_CAP']
    return 4.0 * cap if cap <= 1.0 else (1.0 + cap) ** 2


def _ratio(key: str) -> float:
    return ligo_compatibility_check(GW_PARAMS[key]).violation_factor


SCALARS = {
    'gw_compatible_width': {
        'description': 'Conditional nonnegative susceptibility preimage width at the adopted GW_PARAMS cap; formatted to two significant figures.',
        'value': lambda: _sci(_width(), 1),
    },
    'gw_relative_width': {
        'description': 'Conditional compatible width divided by the adopted comparison interval width, without a probability interpretation.',
        'value': lambda: _sci(_width() / (GW_PARAMS['CHI_VEST_NATURAL_UPPER'] - GW_PARAMS['CHI_VEST_NATURAL_LOWER']), 1),
    },
    'gw_lower_ratio_detailed': {
        'description': 'Absolute assumed-law speed deviation at the adopted lower endpoint divided by the adopted cap, three significant figures.',
        'value': lambda: _sci(_ratio('CHI_VEST_NATURAL_LOWER'), 2),
    },
    'gw_upper_ratio_detailed': {
        'description': 'Absolute assumed-law speed deviation at the adopted upper endpoint divided by the adopted cap, three significant figures.',
        'value': lambda: _sci(_ratio('CHI_VEST_NATURAL_UPPER'), 2),
    },
}
