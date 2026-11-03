"""Qualitative D8 comparison tables and their manuscript references."""

from scripts.paper_tables import Col


def _table(description, columns, rows):
    fields = [column.field for column in columns]
    return {
        "description": description,
        "columns": columns,
        "rows": lambda: [dict(zip(fields, row, strict=True)) for row in rows],
    }


TABLES = {
    'results': _table(
        'D8 proved results and their theorem references',
        [
            Col('result', 'Result', align='l'),
            Col('statement', 'Statement', align='l'),
            Col('conditional', 'Conditional', align='c'),
        ],
        [
            ('SK over an abstract alphabet', 'Thm~\\ref{thm:substrate}', 'yes'),
            ('Logarithm with named radius', 'Thm~\\ref{thm:mercator}', 'no'),
            ('SK at arbitrary $\\su d$', 'Thm~\\ref{thm:sud}', 'yes'),
            ('Clifford$+T$ density', 'Thm~\\ref{thm:accpt}', 'no'),
            ('Clifford$+T$ compilation', 'Thm~\\ref{thm:cliffordt}', 'no'),
            ('$T$-free density at $\\su 8$', 'Thm~\\ref{thm:literal}', 'no'),
            ('Clifford-only is not dense', 'Thm~\\ref{thm:notdense}', 'no'),
            ('Toffoli-count lower bound', 'Thm~\\ref{thm:toffoli}', 'no'),
            ('Compiler correctness', 'Thm~\\ref{thm:compile}', 'no'),
            ('Grid-route length, exponent $1$', 'Thm~\\ref{thm:rslength}', 'yes'),
            ('Grid route from the hypothesis', 'Thm~\\ref{thm:rssynth}', 'yes'),
            ('Ancilla route, exponent $1$', 'Thm~\\ref{thm:kmm}', 'no'),
            ('Operator norm to diamond', 'Thm~\\ref{thm:akn}', 'no'),
            ('End-to-end channel certificate', 'Thm~\\ref{thm:capstone}', 'no'),
        ],
    ),
    'alphabets': _table(
        'D8 alphabets, target groups and alphabet-specific inputs',
        [
            Col('alphabet', 'Alphabet', align='l'),
            Col('target', 'Target', align='l'),
            Col('input', 'Alphabet-specific input', align='l'),
        ],
        [
            ('Clifford$+T$', '$\\su 2$', '$\\sqrt 2 \\sin(\\pi/8)$ not an algebraic integer'),
            ('Read--Rezayi $k=5$', '$\\su 2$', 'Chebyshev factorization of $T_7(x)+1$'),
            ('Read--Rezayi $k=7$', '$\\su 2$', 'triple-angle collapse at $\\cos(\\pi/9)$'),
            ('Trapped-ion M\\o lmer--S\\o rensen', '$\\su 4$', 'Brylinski entangling criterion'),
            ('Clifford$+$CCZ (with $T$)', '$\\su 8$', 'density of the $\\{H,T,\\mathrm{CNOT}\\}$ part'),
            ('Clifford$+$CCZ ($T$-free)', '$\\su 8$', '$\\mathrm{tr} = 1/\\sqrt2$ not an algebraic integer'),
        ],
    ),
    'mechanisms': _table(
        'D8 compilation mechanisms and conditions',
        [
            Col('mechanism', 'Mechanism', align='l'),
            Col('exponent', 'Exponent', align='l'),
            Col('condition', 'Conditional on', align='l'),
            Col('ancillas', 'Ancillas', align='l'),
        ],
        [
            ('Balanced commutator', '$3.97$', 'nothing', 'none'),
            ('Ross--Selinger grid', '$1$', 'Hypothesis~\\ref{hyp:residual}', 'none'),
            ('Kliuchnikov--Maslov--Mosca', '$1$', 'nothing', 'two'),
        ],
    ),
    'reusable': _table(
        'D8 reusable components and their source sections',
        [
            Col('component', 'Component', align='l'),
            Col('reference', 'Where it arises', align='l'),
        ],
        [
            ('Banach-algebra logarithm, named radius', 'Theorem~\\ref{thm:mercator}'),
            ('Euclidean domain instance for $\\mathbb Z[\\zeta_8]$', 'Sec.~\\ref{sec:length-appc}'),
            ('Euler $Z$--$X$--$Z$ decomposition of $\\su 2$', 'Sec.~\\ref{sec:length-kmm}'),
            ('Dimension-generic BCH order-two cubic estimate', 'Sec.~\\ref{sec:substrate}'),
            ('$\\su d$ Cartan density-from-witness lemma', 'Sec.~\\ref{sec:sud}'),
            ('Matrix-exponential local homeomorphism at $\\mathbf 1$', 'Sec.~\\ref{sec:sud}'),
        ],
    ),
}
