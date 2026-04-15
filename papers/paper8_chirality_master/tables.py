"""Table specs for paper8_chirality_master.

Paper 8 is a synthesis paper organized around three pillars (No-Go /
Positive Construction / Algebraic Framework). The pillar → module
mapping below is the author's editorial structure — kept local to this
paper because pillar-organization is a paper-level rhetorical pattern,
not a project-wide concept. Per-pillar theorem counts come from
lean_module_summary; "Status" column is author-provided commentary.
"""

from scripts.paper_tables import Col
from scripts.paper_tables.sources import lean_module_summary


# Pillar → module-list mapping. Author's editorial decision; adding /
# removing pillars, or reassigning modules, is a content change for
# this paper. Module names must match the .lean file stems under
# lean/SKEFTHawking/ (so lean_module_summary can find them).
_PILLARS = [
    ('GS no-go (Pillar~1)', 'Proved', [
        'GoltermanShamir', 'LatticeHamiltonian', 'TPFEvasion', 'ChiralityWall',
    ]),
    ('GT construction (Pillar~2)', 'Proved', [
        'GTCommutation', 'GTWeylDoublet', 'PauliMatrices',
        'WilsonMass', 'BdGHamiltonian',
    ]),
    ('Anomaly framework (Pillar~3)', 'Proved (axiom discharged)', [
        'OnsagerAlgebra', 'OnsagerContraction',
        'Z16Classification', 'Z16AnomalyComputation',
        'RokhlinBridge', 'WangBridge',
        'ModularInvarianceConstraint', 'GenerationConstraint',
        'SteenrodA1', 'SpinBordism', 'SMFermionData',
    ]),
    ('Master synthesis (Bridges)', 'Proved', [
        'ChiralityWallMaster',
    ]),
]


def _pillar_rows() -> list[dict]:
    """Compute per-pillar theorem totals via lean_module_summary.
    The framework summary returns its own Total row as the last entry
    for each module-subset; we pluck that to aggregate per pillar."""
    rows = []
    grand_total = 0
    for pillar_name, status, modules in _PILLARS:
        summary = lean_module_summary(modules)
        # Total row is the last entry, with 'theorems' as a stringified count
        total_theorems = int(summary[-1]['theorems'])
        grand_total += total_theorems
        rows.append({
            'component': pillar_name,
            'theorems':  str(total_theorems),
            'status':    status,
        })
    rows.append({
        'component': r'\textbf{Total}',
        'theorems':  fr'\textbf{{{grand_total}}}',
        'status':    r'\textbf{Zero axioms, zero sorry}',
    })
    return rows


TABLES = {
    'table1_formalization_summary': {
        'description': 'Three-pillar formalization summary — per-pillar theorem '
                       'totals (author-curated module assignment)',
        'rows': _pillar_rows,
        'columns': [
            Col('component', 'Component', align='l'),
            Col('theorems',  'Theorems',  align='c'),
            Col('status',    'Status',    align='l'),
        ],
    },
}
