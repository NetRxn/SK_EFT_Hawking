"""Table specs for paper4_wkb_connection.

Paper 4's exact-WKB platform table, natural-units normalization. Values
come from src/wkb/spectrum.py PlatformParams + exact WKB connection
formula; no new formulas or Lean theorems required for this retrofit
(the math already existed as PlatformParams + SpectrumPoint; the
source function wkb_platform_rows just composes them).
"""

from scripts.paper_tables import Col
from scripts.paper_tables.sources import wkb_platform_rows


TABLES = {
    'table1_platforms': {
        'description': 'Exact WKB parameters for three BEC platforms (natural units)',
        'rows': lambda: wkb_platform_rows(['Steinhauer', 'Heidelberg', 'Trento']),
        'columns': [
            Col('quantity',   '',                            align='l'),
            Col('Steinhauer', r'Steinhauer (${}^{87}$Rb)',   align='c'),
            Col('Heidelberg', r'Heidelberg (${}^{39}$K)',    align='c'),
            Col('Trento',     r'Trento (${}^{23}$Na)',       align='c'),
        ],
    },
}
