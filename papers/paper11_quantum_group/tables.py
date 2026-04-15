"""Table specs for paper11_quantum_group."""

from scripts.paper_tables import Col
from scripts.paper_tables.sources import lean_module_summary


# Author-provided "concept" labels (left column). Each module has an
# associated mathematical object the paper foregrounds.
_CHAIN = [
    ('OnsagerAlgebra',       r'Onsager algebra $O$'),
    ('QNumber',              r'$q$-integers $[n]_q$'),
    ('Uqsl2',                r'$U_q(\mathfrak{sl}_2)$ definition'),
    ('Uqsl2Hopf',            r'$U_q$ Hopf algebra'),
    ('Uqsl2Affine',          r'$U_q(\widehat{\mathfrak{sl}}_2)$ affine'),
    ('Uqsl2AffineHopf',      r'$U_q(\widehat{\mathfrak{sl}}_2)$ Hopf'),
    ('CoidealEmbedding',     r'$O_q \hookrightarrow U_q(\widehat{\mathfrak{sl}}_2)$ coideal'),
    ('RestrictedUq',         r'Restricted $\bar{u}_q$'),
    ('RepUqFusion',          r'$\mathrm{Rep}(\bar{u}_q) \to \mathrm{SU}(2)_k$'),
    ('SU2kFusion',           r'SU(2)$_k$ fusion ($k$=1,2,3)'),
    ('SU2kSMatrix',          r'S-matrix + Verlinde'),
    ('RibbonCategory',       r'Ribbon / MTC definitions'),
    ('SU2kMTC',              r'Ising MTC ($k$=2)'),
    ('FibonacciMTC',         r'Fibonacci MTC ($k$=3)'),
    ('QSqrt2',               r'$\mathbb{Q}(\sqrt{2})$'),
    ('QSqrt5',               r'$\mathbb{Q}(\sqrt{5})$'),
    ('E8Lattice',            r'E$_8$ lattice'),
    ('AlgebraicRokhlin',     r'Algebraic Rokhlin ($8 \mid \sigma$)'),
    ('SpinBordism',          r'Spin bordism $\to$ Wang'),
]

_MODULES = [m for m, _ in _CHAIN]
_CONCEPT = dict(_CHAIN)


def _chain_rows():
    rows = lean_module_summary(_MODULES)
    # Drop the trailing Total row — the chain presentation is per-link
    rows = [r for r in rows if r['module'] != 'Total']
    for row in rows:
        row['concept'] = _CONCEPT.get(row['module'], row['module'])
        row['module_status'] = (
            f'{row["module"]}.lean ({row["theorems"]} thms'
            + (f', {row["sorry"]} sorry' if int(row['sorry']) > 0 else ', 0 sorry')
            + ')'
        )
    return rows


TABLES = {
    'table1_chain': {
        'description': 'Formalization chain: Onsager → Quantum Group → Gauge Theory',
        'rows': _chain_rows,
        'columns': [
            Col('concept',       r'\textbf{Formalized}', align='l'),
            Col('module_status', r'\textbf{Module}',     align='l'),
        ],
    },
}
