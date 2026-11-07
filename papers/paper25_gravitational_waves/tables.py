"""Derived numerals for Paper25's conditional GW170817 comparison.

The existing SCALARS renderer evaluates the adopted GW_PARAMS cap/endpoints
through the canonical compatibility helper. These formatted arithmetic
values do not derive a microscopic mode, response, range or transport law.
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
        'description': 'Conditional nonnegative susceptibility preimage width at the adopted cap; two significant figures, avoiding endpoint subtraction.',
        'value': lambda: _sci(_width(), 1),
    },
    'gw_lower_ratio_detailed': {
        'description': 'Lower adopted endpoint deviation/cap ratio, three significant figures.',
        'value': lambda: _sci(_ratio('CHI_VEST_NATURAL_LOWER'), 2),
    },
    'gw_upper_ratio_detailed': {
        'description': 'Upper adopted endpoint deviation/cap ratio, three significant figures.',
        'value': lambda: _sci(_ratio('CHI_VEST_NATURAL_UPPER'), 2),
    },
    'gw_lower_ratio_rounded': {
        'description': 'Lower adopted endpoint deviation/cap ratio, two significant figures for abstract/caption.',
        'value': lambda: _sci(_ratio('CHI_VEST_NATURAL_LOWER'), 1),
    },
    'gw_upper_ratio_rounded': {
        'description': 'Upper adopted endpoint deviation/cap ratio, two significant figures for abstract/caption.',
        'value': lambda: _sci(_ratio('CHI_VEST_NATURAL_UPPER'), 1),
    },
}
