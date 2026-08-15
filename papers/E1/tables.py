"""Table and scalar specs for the E1 bundle (Paris-LKB polariton device).

Every device parameter E1 quotes — sound speed, healing length, both horizon
steepnesses, both Fresnel-like dispersion ratios, both Hawking temperatures and
the mean-field noise temperature — was a hand-typed ``\\SI{...}`` literal in the
draft, repeated at four to six sites each (abstract, §2, §3, §5, the Fig.~2
caption, §7). The device-parameter table on the old lines 118--130 was a
hand-written ``tabular``. Nothing bound any of them to
``src/core/constants.py``, so a change to the platform record would have left
the manuscript quoting the superseded numbers with no gate noticing:
``numerical_literals`` only counts literals against a frozen ceiling and
``bundle_tables_use_pipeline`` reads the ``\\input{tables/}`` form, which E1 did
not use.

Each entry renders to ``papers/E1/tables/<id>.tex``. Scalars are one-line
snippets the draft pulls in as ``\\input{tables/<id>.tex}\\unskip``; the table
renders a complete ``tabular`` the draft wraps in its own ``center`` envelope.

Regenerate after any change to constants or formulas, or to this spec:

    uv run python scripts/render_paper_tables.py --paper E1

Provenance of every value below:

* ``POLARITON_PLATFORMS['Paris_standard']`` in ``src/core/constants.py`` — the
  Falque et al.\\ 2025 §IV.1 measured record (``c_s``, ``xi``, ``kappa``).
* ``FALQUE_STEEP_HORIZON_KAPPA`` — the steep-horizon reach, same source.
* ``formulas.polariton_hawking_temperature`` — ``T_H = hbar*kappa/(2*pi*k_B)``.
* ``POLARITON_MASS`` — the mean-field noise floor ``T_noise = m* c_s^2 / k_B``.

⚠️ The downstream healing length (4.0 um) is NOT here. It has no record in
``constants.py``; binding it to a Python re-derivation would assert a freshness
relation that does not exist. It stays an inline literal until it is entered as
a provenanced parameter.

⚠️ Every value line is emitted without a trailing unit so the draft keeps
control of ``siunitx`` formatting; call sites read
``\\SI{\\input{tables/<id>.tex}\\unskip}{<unit>}``.
"""

from __future__ import annotations

from scripts.paper_tables import Col

from src.core.constants import (
    FALQUE_STEEP_HORIZON_KAPPA,
    K_B,
    POLARITON_MASS,
    POLARITON_PLATFORMS,
)
from src.core.formulas import polariton_hawking_temperature

_LKB = POLARITON_PLATFORMS['Paris_standard']

_C_S = _LKB['c_s']                       # m/s
_XI = _LKB['xi']                         # m
_KAPPA_SMOOTH = _LKB['kappa']            # s^-1
_KAPPA_STEEP = FALQUE_STEEP_HORIZON_KAPPA  # s^-1


def _dispersion_ratio(kappa: float) -> float:
    """``D = xi * kappa / c_s`` — the draft's dimensionless dispersion ratio."""
    return _XI * kappa / _C_S


def _kappa_tex(kappa: float) -> str:
    """``7e10`` -> ``7\\times 10^{10}``, the form the draft's math mode wants."""
    exponent = 0
    mantissa = float(kappa)
    while mantissa >= 10.0:
        mantissa /= 10.0
        exponent += 1
    mantissa_s = f'{mantissa:.1f}'.rstrip('0').rstrip('.')
    return rf'{mantissa_s}\times 10^{{{exponent}}}'


def _device_rows():
    return [
        {'config': 'Smooth horizon (baseline)',
         'kappa': f'${_kappa_tex(_KAPPA_SMOOTH)}$',
         'D': f'{_dispersion_ratio(_KAPPA_SMOOTH):.2f}'},
        {'config': 'Steep horizon (reach)',
         'kappa': f'${_kappa_tex(_KAPPA_STEEP)}$',
         'D': f'{_dispersion_ratio(_KAPPA_STEEP):.2f}'},
    ]


TABLES = {
    'lkb_device_params': {
        'description': 'E1 §2: the two Paris-LKB horizon configurations reported '
                       'by the primary source, with the dispersion ratio '
                       'D = xi*kappa/c_s derived rather than quoted',
        'rows': _device_rows,
        'columns': [
            Col('config', r'Configuration', align='l'),
            Col('kappa', r'$\kappa$ ($\SI{}{\per\second}$)'),
            Col('D', r'$D = \xi\kappa/c_s$'),
        ],
    },
}

SCALARS = {
    'lkb_c_s_um_per_ps': {
        'description': 'E1 abstract + §2: sound speed of the Paris-LKB fluid, in um/ps '
                       '(m/s * 1e6 um/m / 1e12 ps/s = m/s / 1e6).',
        'value': lambda: f'{_C_S / 1e6:.2f}',
    },
    'lkb_xi_um': {
        'description': 'E1 abstract + §2: upstream healing length, in um.',
        'value': lambda: f'{_XI * 1e6:.1f}',
    },
    'lkb_kappa_smooth': {
        'description': 'E1 abstract, §2, §5 and the Fig. 2 caption: smooth-horizon '
                       'surface gravity, in s^-1, in math-mode scientific form.',
        'value': lambda: _kappa_tex(_KAPPA_SMOOTH),
    },
    'lkb_kappa_steep': {
        'description': 'E1 abstract and §2: steep-horizon surface gravity, in s^-1, '
                       'in math-mode scientific form.',
        'value': lambda: _kappa_tex(_KAPPA_STEEP),
    },
    'lkb_D_smooth': {
        'description': 'E1 abstract, §2 and the Fig. 2 caption: dispersion ratio '
                       'D = xi*kappa/c_s at the smooth horizon.',
        'value': lambda: f'{_dispersion_ratio(_KAPPA_SMOOTH):.2f}',
    },
    'lkb_D_steep': {
        'description': 'E1 abstract and §2: dispersion ratio at the steep horizon.',
        'value': lambda: f'{_dispersion_ratio(_KAPPA_STEEP):.2f}',
    },
    'lkb_T_H_smooth_mK': {
        'description': 'E1 abstract and §5: Hawking temperature at the smooth '
                       'horizon, in mK, from formulas.polariton_hawking_temperature.',
        'value': lambda: f'{polariton_hawking_temperature(_KAPPA_SMOOTH) * 1e3:.0f}',
    },
    'lkb_T_H_steep_mK': {
        'description': 'E1 abstract and §5: Hawking temperature at the steep '
                       'horizon, in mK.',
        'value': lambda: f'{polariton_hawking_temperature(_KAPPA_STEEP) * 1e3:.0f}',
    },
    'lkb_T_noise_K': {
        'description': 'E1 §5: mean-field noise floor T_noise = m* c_s^2 / k_B, in K.',
        'value': lambda: f'{POLARITON_MASS * _C_S ** 2 / K_B:.2f}',
    },
}
