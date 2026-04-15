"""Table specs for paper12_polariton.

Three tables — measured c_s values across groups (literature aggregate),
Paris platform horizon parameters (Falque 2025 + computed), platform
feasibility comparison (Falque-measured κ, projected lifetimes).
"""

from scripts.paper_tables import Col
from scripts.paper_tables.sources import (
    polariton_c_s_measurements,
    polariton_horizon_params,
    polariton_platform_comparison,
)


TABLES = {
    'table1_cs_measurements': {
        'description': 'Measured polariton speed of sound across GaAs microcavity groups',
        'rows': polariton_c_s_measurements,
        'columns': [
            Col('group',  'Group',                         align='l'),
            Col('c_s',    r'$c_s$ ($\mu$m/ps)',            align='c'),
            Col('method', 'Method',                        align='l'),
        ],
    },
    'table2_paris_params': {
        'description': 'Paris polariton horizon parameters — Falque 2025 + computed',
        'rows': polariton_horizon_params,
        'columns': [
            Col('parameter', 'Parameter',       align='l'),
            Col('smooth',    'Smooth baseline', align='c'),
            Col('steep',     'Steep reach',     align='c'),
            Col('source',    'Source',          align='l'),
        ],
    },
    'table3_platform_comparison': {
        'description': 'Platform feasibility comparison for polariton + BEC Hawking detection',
        'rows': polariton_platform_comparison,
        'columns': [
            Col('platform',    'Platform',                align='l'),
            Col('T_H',         '$T_H$',                   align='c'),
            Col('tau',         r'$\tau_{\text{pol}}$',    align='c'),
            Col('kappa_tau',   r'$\kappa\tau$',           align='c'),
            Col('feasibility', 'Feasibility',             align='l'),
        ],
    },
}
