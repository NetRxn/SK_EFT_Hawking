"""Table specs for paper2_second_order.

Table 1 (platform corrections with off-shell δ^(2)) is deferred —
requires a dedicated source that computes off-shell Bogoliubov
wavenumbers. See docs/PAPER_TABLES_STATUS.md.

Table 2 (correction hierarchy reference) is autogen'd from the
canonical taxonomy in scripts/paper_tables/sources.py.
"""

from scripts.paper_tables import Col
from scripts.paper_tables.sources import correction_types


TABLES = {
    'table2_hierarchy': {
        'description': 'EFT correction hierarchy — types, scalings, frequency-dep, parity',
        'rows': correction_types,
        'columns': [
            Col('correction', 'Correction',           align='l'),
            Col('scaling',    'Scaling',              align='c'),
            Col('omega_dep',  r'$\omega$-dep.',       align='c'),
            Col('parity',     'Parity',               align='c'),
        ],
    },
}
