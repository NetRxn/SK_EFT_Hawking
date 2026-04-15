"""Table specs for paper1_first_order.

Each entry in TABLES is rendered by scripts/render_paper_tables.py into
papers/paper1_first_order/tables/<id>.tex, which paper_draft.tex
\\input{}s. Regenerate after any change to formulas/parameters or this
spec:

    uv run python scripts/render_paper_tables.py --paper paper1_first_order
"""

from scripts.paper_tables import Col
from scripts.paper_tables.sources import platform_rows


TABLES = {
    'table1_experimental_params': {
        'description': 'Parameters at the sonic horizon from the transonic '
                       'background solver for three analog Hawking experiments.',
        'rows': lambda: platform_rows(['Steinhauer', 'Heidelberg', 'Trento']),
        'columns': [
            Col('parameter',  'Parameter',                  align='l'),
            Col('unit',       'Units',                       align='c'),
            Col('Steinhauer', 'Steinhauer ($^{87}$Rb)',      align='c'),
            Col('Heidelberg', 'Heidelberg ($^{39}$K)',       align='c'),
            Col('Trento',     'Trento ($^{23}$Na)',          align='c'),
        ],
    },
}
