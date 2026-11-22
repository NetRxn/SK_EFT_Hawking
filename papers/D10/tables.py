"""Canonical table specifications for D10."""

from scripts.paper_tables import Col

_INHABITANCE_ROWS = (
    (r"Molecular Hamiltonian (\S\ref{sec:molecular})", 'none --- all three discharged', 'n/a: about the operator itself'),
    (r"\quad \thm{molecularHamiltonian\_essSelfAdjoint}", '', ''),
    (r"DFT variational (\S\ref{sec:dft-scope})", 'carried as structure fields', r"\textbf{none in the tree}"),
    (r"\quad \thm{hohenberg\_kohn\_variational}", '', ''),
    (r"DFT constrained search (\S\ref{sec:dft-scope})", 'carried as structure fields', r"\textbf{none in the tree}"),
    (r"\quad \thm{levyLieb\_functional}", '', ''),
    (r"NEGF transport (\S\ref{sec:negf})", r"$\tau_{i}\le1$, $G_{0}\ge0$", r"\thm{two\_channel\_no\_three\_quanta}"),
    (r"\quad \thm{conductance\_quantization\_falsifier}", '', ''),
    (r"Open systems (\S\ref{sec:lindblad})", r"Hermiticity, $t\ge0$; CPTP discharged", r"\thm{dampedTwoLevel\_decay\_envelope}"),
    (r"\quad \thm{traceDist\_lindblad\_monotone}", '', ''),
)

TABLES = {
    "inhabitance": {
        "description": "Apex statements and construction witnesses",
        "columns": [
            Col("layer", 'Layer / apex statement', align="l"),
            Col("hypotheses", 'Hypotheses in signature', align="l"),
            Col("witness", 'Witness constructed', align="l"),
        ],
        "rows": lambda: [dict(zip(('layer', 'hypotheses', 'witness'), row, strict=True)) for row in _INHABITANCE_ROWS],
    },
}
