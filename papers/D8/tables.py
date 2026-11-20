"""Table specs for the four D8 manuscript tables.

The result and alphabet columns transcribe the linked theorem conditions
and density witnesses. The reusable-components rows retain their section
references. In the mechanisms table the two exact exponents of one and
the ancilla counts follow the Ross--Selinger grid length statement and
the Kliuchnikov--Maslov--Mosca ancilla statement, respectively.
The balanced-commutator exponent mirrors the defining expression in
FKLW/GenericSUdSkLengthExponent.lean and the executable D8 bound
producer d8_compilation_length_bounds.
"""

from math import log

from scripts.paper_tables import Col


def _balanced_commutator_exponent() -> str:
    return f"${log(5) / log(3 / 2):.2f}$"


TABLES = {
    "sk_results": {
        "description": "Results and statement conditions",
        "columns": [
            Col("result", "Result", align="l"),
            Col("statement", "Statement", align="l"),
            Col("conditional", "Conditional", align="c"),
        ],
        "rows": lambda: [
            {
                "result": "SK over an abstract alphabet",
                "statement": r"Thm~\ref{thm:substrate}",
                "conditional": "yes",
            },
            {
                "result": "Logarithm with named radius",
                "statement": r"Thm~\ref{thm:mercator}",
                "conditional": "no",
            },
            {
                "result": r"SK at arbitrary $\su d$",
                "statement": r"Thm~\ref{thm:sud}",
                "conditional": "yes",
            },
            {
                "result": "Clifford$+T$ density",
                "statement": r"Thm~\ref{thm:accpt}",
                "conditional": "no",
            },
            {
                "result": "Clifford$+T$ compilation",
                "statement": r"Thm~\ref{thm:cliffordt}",
                "conditional": "no",
            },
            {
                "result": r"$T$-free density at $\su 8$",
                "statement": r"Thm~\ref{thm:literal}",
                "conditional": "no",
            },
            {
                "result": "Clifford-only is not dense",
                "statement": r"Thm~\ref{thm:notdense}",
                "conditional": "no",
            },
            {
                "result": "Toffoli-count lower bound",
                "statement": r"Thm~\ref{thm:toffoli}",
                "conditional": "no",
            },
            {
                "result": "Compiler correctness",
                "statement": r"Thm~\ref{thm:compile}",
                "conditional": "no",
            },
            {
                "result": "Grid-route length, exponent $1$",
                "statement": r"Thm~\ref{thm:rslength}",
                "conditional": "yes",
            },
            {
                "result": "Grid route from the hypothesis",
                "statement": r"Thm~\ref{thm:rssynth}",
                "conditional": "yes",
            },
            {
                "result": "Ancilla route, exponent $1$",
                "statement": r"Thm~\ref{thm:kmm}",
                "conditional": "no",
            },
            {
                "result": "Operator norm to diamond",
                "statement": r"Thm~\ref{thm:akn}",
                "conditional": "no",
            },
            {
                "result": "End-to-end channel certificate",
                "statement": r"Thm~\ref{thm:capstone}",
                "conditional": "no",
            },
        ],
    },
    "alphabet_inputs": {
        "description": "Alphabet-specific input and target",
        "columns": [
            Col("alphabet", "Alphabet", align=r"@{}p{.31\columnwidth}"),
            Col("target", "Target", align="c"),
            Col("input", "Alphabet-specific input", align=r"p{.47\columnwidth}@{}"),
        ],
        "rows": lambda: [
            {
                "alphabet": "Clifford$+T$",
                "target": r"$\su 2$",
                "input": r"$\sqrt 2 \sin(\pi/8)$ not an algebraic integer",
            },
            {
                "alphabet": "Read--Rezayi $k=5$",
                "target": r"$\su 2$",
                "input": "Chebyshev factorization of $T_7(x)+1$",
            },
            {
                "alphabet": "Read--Rezayi $k=7$",
                "target": r"$\su 2$",
                "input": r"triple-angle collapse at $\cos(\pi/9)$",
            },
            {
                "alphabet": r"Trapped-ion M\o lmer--S\o rensen",
                "target": r"$\su 4$",
                "input": "Tensor-Pauli closure flows",
            },
            {
                "alphabet": "Clifford$+$CCZ (with $T$)",
                "target": r"$\su 8$",
                "input": r"density of the $\{H,T,\mathrm{CNOT}\}$ part",
            },
            {
                "alphabet": "Clifford$+$CCZ ($T$-free)",
                "target": r"$\su 8$",
                "input": r"$\mathrm{tr} = 1/\sqrt2$ not an algebraic integer",
            },
        ],
    },
    "compilation_mechanisms": {
        "description": "Compilation exponents, conditions and ancilla counts",
        "columns": [
            Col("mechanism", "Mechanism", align="l"),
            Col("exponent", "Exponent", align="l"),
            Col("condition", "Conditional on", align="l"),
            Col("ancillas", "Ancillas", align="l"),
        ],
        "rows": lambda: [
            {
                "mechanism": "Balanced commutator",
                "exponent": _balanced_commutator_exponent(),
                "condition": "nothing",
                "ancillas": "none",
            },
            {
                "mechanism": "Ross--Selinger grid",
                "exponent": "$1$",
                "condition": r"Hypothesis~\ref{hyp:residual}",
                "ancillas": "none",
            },
            {
                "mechanism": "Kliuchnikov--Maslov--Mosca",
                "exponent": "$1$",
                "condition": "nothing",
                "ancillas": "two",
            },
        ],
    },
    "reusable_components": {
        "description": "Reusable components and their locations",
        "columns": [
            Col("component", "Component", align="l"),
            Col("location", "Where it arises", align="l"),
        ],
        "rows": lambda: [
            {
                "component": "Banach-algebra logarithm, named radius",
                "location": r"Theorem~\ref{thm:mercator}",
            },
            {
                "component": r"Euclidean domain instance for $\mathbb Z[\zeta_8]$",
                "location": r"Sec.~\ref{sec:length-appc}",
            },
            {
                "component": r"Euler $Z$--$X$--$Z$ decomposition of $\su 2$",
                "location": r"Sec.~\ref{sec:length-kmm}",
            },
            {
                "component": "Dimension-generic BCH order-two cubic estimate",
                "location": r"Sec.~\ref{sec:substrate}",
            },
            {
                "component": r"$\su d$ Cartan density-from-witness lemma",
                "location": r"Sec.~\ref{sec:sud}",
            },
            {
                "component": r"Matrix-exponential local homeomorphism at $\mathbf 1$",
                "location": r"Sec.~\ref{sec:sud}",
            },
        ],
    },
}
