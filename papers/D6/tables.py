"""Canonical table specifications for D6."""

from scripts.paper_tables import Col


# AGP2006 Sec. 8.3 (fault models and Eqs. 32--36) and its depolarizing example.
# Retain the reported count precision, then compute each displayed reciprocal.
_COUNTS = (
    (r"$A_{\rm CNOT}$, depolarizing noise", 7_183, True),
    (r"$A_{\rm CNOT}$, no storage faults", 22_701, False),
    (r"$A_{\rm CNOT}$, Eq.~\eqref{eq:acnot}", 35_235, False),
    (r"$A'_{\rm CNOT}$, cubic term absorbed", 36_108, True),
    (r"$A''_{\rm CNOT}$, ancilla acceptance", 36_511, True),
)


def _count_rows() -> list[dict[str, str]]:
    rows = []
    for label, count, approximate in _COUNTS:
        prefix = r"\approx " if approximate else ""
        digits = f"{count:,}".replace(",", r"\,")
        mantissa, exponent = f"{1 / count:.2e}".split("e")
        rows.append({
            "count": label,
            "value": f"${prefix}{digits}$",
            "inverse": rf"${mantissa}\times10^{{{int(exponent)}}}$",
        })
    return rows

_MODULES_ROWS = (
    (r"\verb|Basic|", 'shared definitions'),
    (r"\verb|StabilizerCode|", 'stabilizer substrate'),
    (r"\verb|SteaneCode|", 'the $[[7,1,3]]$ instance'),
    (r"\verb|Counting|", r"Eqs.~\eqref{eq:mcnot},~\eqref{eq:acnot}; well-formedness"),
    (r"\verb|MalignantUnionBound|", r"Lemmas~\ref{lem:union}--\ref{lem:submul}"),
    (r"\verb|Concatenation|", 'the level sequence'),
    (r"\verb|DoubleExp|", r"Eq.~\eqref{eq:double-exp}"),
    (r"\verb|ConcatenatedComposition|", r"Theorem~\ref{thm:levels}; the capstones"),
    (r"\verb|AGP/Threshold|", r"Eqs.~\eqref{eq:threshold-def},~\eqref{eq:threshold-numeric}"),
)

TABLES = {
    "counts": {
        "description": "Malignant-pair counts and their reciprocals",
        "columns": [
            Col("count", 'Count', align="l"),
            Col("value", 'Value', align="r"),
            Col("inverse", 'Inverse', align="l"),
        ],
        "rows": _count_rows,
    },
    "modules": {
        "description": "Modules in the capstone dependency closure",
        "columns": [
            Col("module", 'Module', align="l"),
            Col("contribution", 'Contributes', align="l"),
        ],
        "rows": lambda: [dict(zip(('module', 'contribution'), row, strict=True)) for row in _MODULES_ROWS],
    },
}
