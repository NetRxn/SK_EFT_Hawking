"""Scalar specs for the D12 bundle (derived-numeral provenance).

D12 ships no tabular data. What it ships is a large surface of *derived
numerals* quoted inline in the prose: the folklore-floor undershoot factor and
its crossover, the Gaussian-tail fractions, and the whole thermal-link gradient
factor convention argument of §3.2. Every one of them is a value of a
`src/core/formulas.py` function evaluated at a stated operating point, and
before this file existed not one of them was reachable from any freshness or
provenance gate: `count_literals`, `numerical_literals`, `counts_fresh`,
`tables_fresh` and `paper_provenance` all evaluated **green and vacuous** for
D12 (Stage-13 rounds 8-12, finding 7.1, five consecutive reproductions).

Each SCALARS entry renders to `papers/D12/tables/<id>.tex`, a one-line snippet
the draft pulls in as `\\input{tables/<id>.tex}\\unskip`. A change to the
backing formula therefore changes the typeset numeral, and `tables_fresh`
regenerates on any `formulas.py` / `constants.py` / spec mtime bump. That is
the guard round 7's `23`, round 8's `21.5` derivation and round 9's `0.4651`
each needed and did not have.

Regenerate after any change to formulas or to this spec:

    uv run python scripts/render_paper_tables.py --paper D12

⚠️ Every value line ends in a literal `%` so that TeX swallows the file's
trailing newline; without it `\\input` injects a space before the following
token. `\\unskip` at the call site is belt-and-braces for the same hazard.

⚠️ Rationals that come from a Lean theorem *statement* (22/25, 3/25, the Mills
fractions 1/2 and 4/5, the certified 148-fold and 1000-fold factors) are NOT
here. They are exact constants of kernel-checked statements, not evaluations of
a Python formula, and binding them to a Python re-derivation would assert a
freshness relation that does not exist.
"""

from __future__ import annotations

import math
from collections.abc import Callable

from src.core.formulas import (
    folklore_gap_exponent,
    folklore_miss_floor,
    gaussian_q,
    gaussian_tail_birnbaum_lower,
    gaussian_tail_mills_upper,
    phonon_psd_gradient_factor,
    poisson_avg_error_floor,
)

# ── Operating points quoted in the draft ────────────────────────────────────
_NB_FIG1, _NA_FIG1 = 5.0, 10.0        # §2.2 false-strict witness
_NB_BRIGHT, _NA_BRIGHT = 50.0, 60.0   # §2.2 fail-open witness, Fig. 1(C)
_R_WORKED, _N_INDEX = 2.0, 4.0        # §3.2 worked gradient-factor point


def _bisect(f: Callable[[float], float], lo: float, hi: float,
            tol: float = 1e-12) -> float:
    """Plain bisection root-find; keeps this spec scipy-free.

    `f(lo)` and `f(hi)` must straddle zero. Used for the two roots the draft
    quotes that have no closed form: the fail-open crossover in `N_a`, and the
    bolometer-to-bath ratio at which the PSD reduction is exactly 30 %.
    """
    flo = f(lo)
    if flo == 0.0:
        return lo
    if flo * f(hi) > 0:
        raise ValueError(f'root not bracketed on [{lo}, {hi}]')
    for _ in range(400):
        mid = 0.5 * (lo + hi)
        fmid = f(mid)
        if fmid == 0.0 or (hi - lo) < tol:
            return mid
        if flo * fmid < 0:
            hi = mid
        else:
            lo, flo = mid, fmid
    return 0.5 * (lo + hi)


def _fmt(x: float, places: int) -> str:
    return f'{x:.{places}f}%'


# ── §2.2 the folklore floor ─────────────────────────────────────────────────

def _undershoot_exact() -> str:
    """e^{N_b}: the factor by which the ideal unit-threshold counter undershoots
    the folklore value, i.e. folklore / exp(-N_a) at the Fig. 1(A) point."""
    return _fmt(folklore_miss_floor(_NA_FIG1, _NB_FIG1) / math.exp(-_NA_FIG1), 2)


def _fail_open_crossover() -> str:
    """N_a at which the exact exponent gap 2*sqrt(N_b)(sqrt(N_a)-sqrt(N_b))
    reaches log 4, at the Fig. 1(B) baseline N_b = 50."""
    root = _bisect(
        lambda na: folklore_gap_exponent(na, _NB_BRIGHT) - math.log(4.0),
        _NB_BRIGHT + 1e-9, 4.0 * _NB_BRIGHT)
    return _fmt(root, 2)


def _bright_ratio() -> str:
    """True Le Cam floor / folklore value at (N_b, N_a) = (50, 60)."""
    return _fmt(poisson_avg_error_floor(_NA_BRIGHT, _NB_BRIGHT)
                / folklore_miss_floor(_NA_BRIGHT, _NB_BRIGHT), 2)


# ── §2.3 / §4 the Gaussian tail ─────────────────────────────────────────────

def _q_one() -> str:
    return _fmt(gaussian_q(1.0), 5)


def _birnbaum_fraction(z: float) -> str:
    """Birnbaum-Feller lower bound as a percentage of the true Q(z)."""
    return _fmt(100.0 * gaussian_tail_birnbaum_lower(z) / gaussian_q(z), 0)


def _mills_vacuity_root() -> str:
    """z below which the Mills upper bound phi(z)/z exceeds 1 and is vacuous."""
    return _fmt(_bisect(lambda z: gaussian_tail_mills_upper(z) - 1.0, 0.05, 2.0), 2)


def _relaxation_crossover(places: int) -> str:
    """x = t/T_1 solving x/(2(1+x)) = Q(1), i.e. 2Q(1)/(1-2Q(1))."""
    q = gaussian_q(1.0)
    return _fmt(2.0 * q / (1.0 - 2.0 * q), places)


# ── §3.2 the thermal-link gradient factor ───────────────────────────────────

def _gamma() -> float:
    return phonon_psd_gradient_factor(_R_WORKED, _N_INDEX)


def _gamma_limit() -> float:
    """lim_{r->inf} gamma = n/(2n+1)."""
    return _N_INDEX / (2.0 * _N_INDEX + 1.0)


def _r_at_psd_reduction(target: float) -> float:
    return _bisect(
        lambda r: (1.0 - phonon_psd_gradient_factor(r, _N_INDEX)) - target,
        1.0 + 1e-9, 10.0)


SCALARS = {
    # §2.2
    'folklore_undershoot_exact': {
        'description': 'D12 §2.2: exp(N_b) = the exact factor by which the ideal '
                       'unit-threshold counter undershoots the folklore miss floor '
                       'at (N_b, N_a) = (5, 10); the 148-fold Lean certificate is '
                       'the rational bound below it.',
        'value': _undershoot_exact,
    },
    'folklore_fail_open_crossover': {
        'description': 'D12 §2.2 and Fig. 1(B): the N_a at which the folklore '
                       'value crosses below the true Le Cam floor, at baseline '
                       'N_b = 50 (solves the exponent gap = log 4).',
        'value': _fail_open_crossover,
    },
    'folklore_bright_ratio': {
        'description': 'D12 §2.2: true Le Cam floor / folklore value at '
                       '(N_b, N_a) = (50, 60); the certified factor-1000 theorem '
                       'is the rational bound below it.',
        'value': _bright_ratio,
    },
    # §2.3 / §4
    'gaussian_q_one': {
        'description': 'D12 §4: Q(1), the true upper standard-normal tail against '
                       'which the rational enclosure Q(1) >= 3/25 is calibrated.',
        'value': _q_one,
    },
    'birnbaum_fraction_z1': {
        'description': 'D12 §4: Birnbaum-Feller lower bound as a percentage of '
                       'Q(1).',
        'value': lambda: _birnbaum_fraction(1.0),
    },
    'birnbaum_fraction_z2': {
        'description': 'D12 §4: Birnbaum-Feller lower bound as a percentage of '
                       'Q(2); the bound loosens as z falls.',
        'value': lambda: _birnbaum_fraction(2.0),
    },
    'mills_vacuity_root': {
        'description': 'D12 Fig. 2 caption: the z below which the Mills upper '
                       'bound phi(z)/z exceeds 1 and is therefore vacuous.',
        'value': _mills_vacuity_root,
    },
    'relaxation_crossover': {
        'description': 'D12 §4: t/T_1 above which the discarded relaxation term '
                       'exceeds the detection term, to four places.',
        'value': lambda: _relaxation_crossover(4),
    },
    'relaxation_crossover_precise': {
        'description': 'D12 §4: the same crossover x = 2Q(1)/(1-2Q(1)) to five '
                       'places.',
        'value': lambda: _relaxation_crossover(5),
    },
    # §3.2
    'gamma_worked': {
        'description': 'D12 §3.2: gamma(r = 2, n = 4), the worked value of the '
                       'thermal-link gradient factor, below the commonly quoted '
                       'F_link band [1/2, 1].',
        'value': lambda: _fmt(_gamma(), 4),
    },
    'gamma_psd_reduction_pct': {
        'description': 'D12 §3.2: 1 - gamma(2, 4) as a percentage, the PSD-domain '
                       'reading of the reduction (rounded to the point).',
        'value': lambda: _fmt(100.0 * (1.0 - _gamma()), 0),
    },
    'gamma_amp_reduction_pct': {
        'description': 'D12 §3.2: 1 - sqrt(gamma(2, 4)) as a percentage, the '
                       'amplitude-domain reading (rounded to the point).',
        'value': lambda: _fmt(100.0 * (1.0 - math.sqrt(_gamma())), 0),
    },
    'gamma_psd_reduction_pct_exact': {
        'description': 'D12 §3.2: the PSD reading to one decimal, one half of the '
                       'convention gap.',
        'value': lambda: _fmt(100.0 * (1.0 - _gamma()), 1),
    },
    'gamma_amp_reduction_pct_exact': {
        'description': 'D12 §3.2: the amplitude reading to one decimal, the other '
                       'half of the convention gap.',
        'value': lambda: _fmt(100.0 * (1.0 - math.sqrt(_gamma())), 1),
    },
    'gamma_convention_gap_points': {
        'description': 'D12 §3.2: the gap in percentage points between the PSD and '
                       'amplitude readings at the worked point. This is the numeral '
                       'PARAMETER_PROVENANCE[MATHER_1982_GRADIENT_REDUCTION] pins '
                       'the convention ambiguity on.',
        'value': lambda: _fmt(100.0 * (math.sqrt(_gamma()) - _gamma()), 1),
    },
    'gamma_sup_psd_reduction_pct': {
        'description': 'D12 §3.2: the supremum PSD reduction 1 - n/(2n+1) at n = 4, '
                       'approached as r -> infinity and never attained.',
        'value': lambda: _fmt(100.0 * (1.0 - _gamma_limit()), 0),
    },
    'gamma_sup_amp_reduction_pct': {
        'description': 'D12 §3.2: the supremum amplitude reduction '
                       '1 - sqrt(n/(2n+1)) at n = 4.',
        'value': lambda: _fmt(100.0 * (1.0 - math.sqrt(_gamma_limit())), 0),
    },
    'gamma_limit_decimal': {
        'description': 'D12 §3.2: n/(2n+1) = 4/9 at n = 4 as a decimal, the limit '
                       'gamma decreases to, which is not 1/2.',
        'value': lambda: _fmt(_gamma_limit(), 3),
    },
    'gamma_r_at_30pct': {
        'description': 'D12 §3.2: the bolometer-to-bath ratio r at which the PSD '
                       'reduction is exactly 30 %, the figure Mather quotes.',
        'value': lambda: _fmt(_r_at_psd_reduction(0.30), 5),
    },
    'gamma_psd_reduction_at_r119_pct': {
        'description': 'D12 §3.2: the PSD reduction at r = 1.19, showing a value '
                       'near 30 % is attained and so the available range settles '
                       'the convention neither way.',
        'value': lambda: _fmt(100.0 * (1.0 - phonon_psd_gradient_factor(1.19, _N_INDEX)), 2),
    },
}
