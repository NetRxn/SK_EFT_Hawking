"""Scalar specs for the D3 bundle (derived-numeral provenance).

D3 quotes a small number of *derived numerals* inline: the Einstein--Cartan
torsion amplitude and its margin against the published bound, the
cosmological-constant overshoot, the Stelle higher-curvature triple, the
regime-partition mass, and the width ratio between the GW170817-compatible
window and the substrate's natural range. Every one of them is a value of a
`src/core/formulas.py` function (or of a `src/core/constants.py` entry)
evaluated at a stated operating point, and before this file existed not one of
them was reachable from any freshness or provenance gate: the draft typed them
as literals, and `numerical_literals` counted thirteen of them.

Each SCALARS entry renders to `papers/D3/tables/<id>.tex`, a one-line snippet
the draft pulls in as `\\input{tables/<id>.tex}\\unskip`. A change to the
backing formula therefore changes the typeset numeral.

Regenerate after any change to formulas or to this spec:

    uv run python scripts/render_paper_tables.py --paper D3

⚠️ Every value line ends in a literal `%` so that TeX swallows the file's
trailing newline; `\\unskip` at the call site is belt-and-braces for the same
hazard.

⚠️ Rationals that come from a Lean theorem *statement* are NOT here. The
factor-6000 bracket (`1/6202`, `1/6000`), the GW170817 cap `3e-15`, the
Kaul--Majumdar `-3/2` and its `-1/2 - 1` decomposition, and the `10^100`
cosmological-constant lower bound are exact constants of kernel-checked
statements, not evaluations of a Python formula. Binding them to a Python
re-derivation would assert a freshness relation that does not exist.
"""

from __future__ import annotations

import math

from src.core.constants import (
    EINSTEIN_CARTAN_PARAMS,
    GW_PARAMS,
    MICRO_MACRO_PARAMS,
)
from src.core.formulas import (
    G_N_sakharov,
    adw_critical_coupling,
    higher_curvature_microscopic_stelle,
    lambda_emerg_microscopic,
    torsion_amplitude_at_cosmological_background,
)

# ── The natural microscopic point quoted throughout the draft ───────────────
# (Lambda_UV, N_f, alpha) = (M_Pl, 16, 1): the cutoff at the Planck mass, one
# Dirac species per Standard-Model Weyl fermion per generation-equivalent
# counting, and the matching condition alpha = 1 that §5 and §8 both close on.
_LAMBDA_UV = MICRO_MACRO_PARAMS['M_PLANCK_GEV']
_N_F = 16
_ALPHA = 1.0


def _fmt_sci(x: float, places: int = 2) -> str:
    """LaTeX scientific notation, e.g. `2.05 \\times 10^{-77}`."""
    mantissa, exp = f'{x:.{places}e}'.split('e')
    return f'{mantissa} \\times 10^{{{int(exp)}}}%'


def _fmt(x: float, places: int) -> str:
    return f'{x:.{places}f}%'


# ── Einstein--Cartan torsion (§8) ───────────────────────────────────────────

def _torsion() -> float:
    return torsion_amplitude_at_cosmological_background(_LAMBDA_UV, _N_F, _ALPHA)


# ── Cosmological constant (§8) ──────────────────────────────────────────────

def _lambda_ratio() -> float:
    return (lambda_emerg_microscopic(_LAMBDA_UV, _N_F)
            / MICRO_MACRO_PARAMS['LAMBDA_OBSERVED_GEV4'])


# ── The GW170817 window against the natural range (§4) ──────────────────────

def _chi_window_ratio() -> float:
    """Width of the natural chi_vest range divided by the width of the
    chi_vest interval the GW170817 two-sided cap admits."""
    tol = GW_PARAMS['C_GW_TWO_SIDED_CAP']
    natural = (GW_PARAMS['CHI_VEST_NATURAL_UPPER']
               - GW_PARAMS['CHI_VEST_NATURAL_LOWER'])
    admitted = (1.0 + tol) ** 2 - (1.0 - tol) ** 2
    return natural / admitted


SCALARS = {
    'torsion_amplitude_gev': {
        'description': 'D3 §8: the Einstein--Cartan torsion amplitude at the '
                       'cosmological spin background, in GeV, at the natural '
                       'point (Lambda_UV, N_f, alpha_EC) = (M_Pl, 16, 1).',
        'value': lambda: _fmt_sci(_torsion(), 2),
    },
    'torsion_orders_below_kostelecky': {
        'description': 'D3 §8: how many orders of magnitude the predicted '
                       'torsion amplitude sits beneath the '
                       'Kostelecky--Russell--Tasson cosmic-axial-torsion bound.',
        'value': lambda: _fmt(
            math.log10(EINSTEIN_CARTAN_PARAMS['TORSION_BOUND_KOSTELECKY_GEV']
                       / _torsion()), 0),
    },
    'torsion_bound_kostelecky_gev': {
        'description': 'D3 §8: the Kostelecky--Russell--Tasson cosmic-axial-'
                       'torsion bound in GeV, as stored in constants.py.',
        'value': lambda: _fmt_sci(
            EINSTEIN_CARTAN_PARAMS['TORSION_BOUND_KOSTELECKY_GEV'], 0),
    },
    'torsion_bound_hughes_drever_gev': {
        'description': 'D3 §8: the looser Hughes--Drever / Lammerzahl '
                       'rotational-axial-torsion bound in GeV.',
        'value': lambda: _fmt_sci(
            EINSTEIN_CARTAN_PARAMS['TORSION_BOUND_HUGHES_DREVER_GEV'], 0),
    },

    'lambda_overshoot_log10': {
        'description': 'D3 §8: log10 of Lambda_emerg / Lambda_obs at the '
                       'natural point. This is where the familiar '
                       'cosmological-constant figure comes from; the Lean '
                       'statement discharges only the weaker 10^100 bound.',
        'value': lambda: _fmt(math.log10(_lambda_ratio()), 1),
    },
    'lambda_observed_gev4': {
        'description': 'D3 §8: the observed cosmological constant in GeV^4 '
                       '(Planck 2018), the denominator of the overshoot.',
        'value': lambda: _fmt_sci(
            MICRO_MACRO_PARAMS['LAMBDA_OBSERVED_GEV4'], 1),
    },

    'stelle_r_sq_coefficient': {
        'description': 'D3 §8: the R^2 coefficient of the microscopic Stelle '
                       'triple read off the Dirac a_4 basis at N_f = 16.',
        'value': lambda: _fmt(higher_curvature_microscopic_stelle(_N_F)[0], 6),
    },
    'stelle_ricci_sq_coefficient': {
        'description': 'D3 §8: the Ricci^2 coefficient of the microscopic '
                       'Stelle triple at N_f = 16.',
        'value': lambda: _fmt(higher_curvature_microscopic_stelle(_N_F)[1], 6),
    },
    'stelle_riemann_sq_coefficient': {
        'description': 'D3 §8: the Riemann^2 coefficient of the microscopic '
                       'Stelle triple at N_f = 16.',
        'value': lambda: _fmt(higher_curvature_microscopic_stelle(_N_F)[2], 6),
    },

    'g_n_sakharov_planck_gev_inv2': {
        'description': 'D3 §2: the Sakharov closed form G_N = 12 pi / '
                       '(N_f Lambda_UV^2) evaluated at the natural point, in '
                       'GeV^-2.',
        'value': lambda: _fmt_sci(G_N_sakharov(_LAMBDA_UV, _N_F), 2),
    },
    'g_n_over_g_c_ratio': {
        'description': 'D3 §2: the ratio G_N^Sak / G_c^ADW as a decimal. The '
                       'Lean statement gives it in closed form as 3/(2 pi); '
                       'this is that number, evaluated, as a numerical check '
                       'that the two definitions agree.',
        'value': lambda: _fmt(
            G_N_sakharov(_LAMBDA_UV, _N_F) / adw_critical_coupling(_LAMBDA_UV, _N_F), 6),
    },

    'm_c_over_planck_mass': {
        'description': 'D3 §7: the regime-partition mass M_c = N_f Lambda_UV / '
                       '(12 pi alpha_ADW) in units of the Planck mass, at the '
                       'natural point. Astrophysical masses exceed it by many '
                       'orders, so they sit unambiguously on the Schwarzschild '
                       'branch.',
        'value': lambda: _fmt(_N_F / (12.0 * math.pi * _ALPHA), 2),
    },

    'gw170817_two_sided_cap': {
        'description': 'D3 §4: the GW170817 two-sided fractional cap on the '
                       'gravitational-wave propagation speed, as stored in '
                       'constants.py.',
        'value': lambda: _fmt_sci(GW_PARAMS['C_GW_TWO_SIDED_CAP'], 0),
    },
    'chi_vest_natural_lower': {
        'description': 'D3 §4: the lower endpoint of the natural chi_vest '
                       'range.',
        'value': lambda: _fmt(GW_PARAMS['CHI_VEST_NATURAL_LOWER'], 1),
    },
    'chi_vest_natural_upper': {
        'description': 'D3 §4: the upper endpoint of the natural chi_vest '
                       'range.',
        'value': lambda: _fmt(GW_PARAMS['CHI_VEST_NATURAL_UPPER'], 0),
    },
    'chi_window_ratio_log10': {
        'description': 'D3 §4: log10 of (width of the natural chi_vest range) '
                       '/ (width of the chi_vest interval the GW170817 '
                       'two-sided cap admits). The Lean statement discharges '
                       'the weaker claim that this ratio exceeds 10^14.',
        'value': lambda: _fmt(math.log10(_chi_window_ratio()), 1),
    },
}
