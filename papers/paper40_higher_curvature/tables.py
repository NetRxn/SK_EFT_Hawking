"""Table + scalar specs for paper40_higher_curvature.

Each TABLES entry is rendered by scripts/render_paper_tables.py into
papers/paper40_higher_curvature/tables/<id>.tex.

Each SCALARS entry is rendered into a single-line .tex snippet
(no `\\begin{tabular}` envelope) suitable for in-equation `\\input{}`.

Regenerate after any change to formulas/parameters or this spec:

    uv run python scripts/render_paper_tables.py --paper paper40_higher_curvature
"""
from __future__ import annotations

from src.core.formulas import (
    higher_curvature_R_sq_coefficient,
    higher_curvature_Ricci_sq_coefficient,
    higher_curvature_Riemann_sq_coefficient,
)


def _largest_at(nf: int) -> float:
    return max(
        abs(higher_curvature_R_sq_coefficient(nf)),
        abs(higher_curvature_Ricci_sq_coefficient(nf)),
        abs(higher_curvature_Riemann_sq_coefficient(nf)),
    )


def _format_sci(x: float, sig: int = 4) -> str:
    """Format `x` as ``M.NNN \\times 10^{E}`` LaTeX scientific notation."""
    if x == 0:
        return '0'
    from math import floor, log10
    e = int(floor(log10(abs(x))))
    m = x / (10 ** e)
    return f'{m:.{sig - 1}f} \\times 10^{{{e}}}'


SCALARS = {
    'c_riem_anchor_at_Nf_27': {
        'description': 'paper40 §5 anchor: |c_Riem(N_f=27)| = 27/(180·(4π)²) '
                       '— largest predicted dimensionless higher-curvature '
                       'coefficient at SM-with-νᴿ fermion count, consumed '
                       'by `higher_curvature_predicted_in_observational_band` '
                       'and the §5 "62 orders below" headline.',
        'value': lambda: _format_sci(_largest_at(27), sig=4),
    },
    'c_riem_pulsar_orders_below': {
        'description': 'paper40 §5: separation between predicted |c_Riem(27)| '
                       'and the tightest observational ceiling '
                       'HC_BOUND_PULSAR_C_SQ = 10^59 (the "62 orders below" '
                       'headline).',
        'value': lambda: f'10^{{{int(59 + abs(__import__("math").log10(_largest_at(27))))}}}',
    },
}


# No tabular output for paper40 — only scalar inline-equation values.
TABLES: dict = {}
