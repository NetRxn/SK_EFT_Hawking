"""Table specs for paper7_chirality_formal."""

from scripts.paper_tables import Col
from scripts.paper_tables.sources import lean_module_summary


# Key-result descriptions are author-provided (prose summaries of what
# each module accomplishes). The numeric columns are pipeline-derived.
_KEY_RESULTS = {
    'LatticeHamiltonian': r'BZ compact, $\ell^2(\mathbb{Z})$ $\infty$-dim',
    'GoltermanShamir':    '9 conditions, Fock space finite',
    'TPFEvasion':         'Master synthesis',
    'Total':              'Zero sorry',
}


def _verification_rows() -> list[dict]:
    rows = lean_module_summary(['LatticeHamiltonian', 'GoltermanShamir', 'TPFEvasion'])
    for row in rows:
        row['key_result'] = _KEY_RESULTS.get(row['module'], '')
    return rows


TABLES = {
    'table1_verification': {
        'description': 'Lean verification summary — GS no-go + TPF construction',
        'rows': _verification_rows,
        'columns': [
            Col('module',     'Module',      align='l'),
            Col('theorems',   'Thms',        align='c'),
            Col('aristotle',  'Aristotle',   align='c'),
            Col('key_result', 'Key Result',  align='l'),
        ],
    },
}
