"""D6 manuscript tables, including the AGP source count comparison."""

from math import ceil, comb, sqrt

from scripts.paper_tables import Col


def _table(description, columns, rows):
    fields = [column.field for column in columns]
    return {
        "description": description,
        "columns": columns,
        "rows": lambda: [dict(zip(fields, row, strict=True)) for row in rows],
    }


# Aliferis, Gottesman and Preskill, quant-ph/0504218v3, §8.3, Eq. (31).
_ADVERSARIAL_PAIRS = (
    (64,),
    (624, 630),
    (160, 468, 96),
    (160, 468, 0, 96),
    (192, 546, 0, 288, 168),
    (192, 546, 288, 0, 0, 168),
    (2560, 5924, 1888, 1888, 2288, 2288, 13245),
)


def _adversarial_count():
    return sum(sum(row) for row in _ADVERSARIAL_PAIRS)


def _count_rows():
    adversarial = _adversarial_count()
    # AGP omit the first two location types when storage faults are neglected.
    no_storage = sum(sum(row[2:]) for row in _ADVERSARIAL_PAIRS[2:])
    # Eq. (19) absorbs the cubic term, then Eq. (35) conditions on acceptance.
    cubic = (adversarial + sqrt(adversarial**2 + 4 * comb(575, 3))) / 2
    conditioned = cubic / (1 - 50 / cubic)**8
    # Use the source's reported approximate effective count from Eq. (44).
    counts = (
        (r"$A_{\rm CNOT}$, depolarizing noise", 7183, True),
        (r"$A_{\rm CNOT}$, no storage faults", no_storage, False),
        (r"$A_{\rm CNOT}$, Eq.~\eqref{eq:acnot}", adversarial, False),
        (r"$A'_{\rm CNOT}$, cubic term absorbed", ceil(cubic), True),
        (r"$A''_{\rm CNOT}$, ancilla acceptance", ceil(conditioned), True),
    )
    rows = []
    for label, count, approximate in counts:
        prefix = r"\approx " if approximate else ""
        value = f"{count:,}".replace(",", r"\,")
        mantissa, exponent = f"{1 / count:.2e}".split("e")
        rows.append({
            "count": label,
            "value": f"${prefix}{value}$",
            "inverse": rf"${mantissa}\times10^{{{int(exponent)}}}$",
        })
    return rows


TABLES = {
    "counts": {
        "description": "D6 Steane CNOT extended rectangle counts and reciprocals",
        "rows": _count_rows,
        "columns": [
            Col("count", "Count", align="l"),
            Col("value", "Value", align="r"),
            Col("inverse", "Inverse", align="l"),
        ],
    },
    'modules': _table(
        'D6 manuscript table modules',
        [
            Col('module', 'Module', align='l'),
            Col('contribution', 'Contributes', align='l'),
        ],
        [
            ('\\verb|Basic|', 'shared definitions'),
            ('\\verb|StabilizerCode|', 'stabilizer substrate'),
            ('\\verb|SteaneCode|', 'the $[[7,1,3]]$ instance'),
            ('\\verb|Counting|', 'Eqs.~\\eqref{eq:mcnot},~\\eqref{eq:acnot}; well-formedness'),
            ('\\verb|MalignantUnionBound|', 'Lemmas~\\ref{lem:union}--\\ref{lem:submul}'),
            ('\\verb|Concatenation|', 'the level sequence'),
            ('\\verb|DoubleExp|', 'Eq.~\\eqref{eq:double-exp}'),
            ('\\verb|ConcatenatedComposition|', 'Theorem~\\ref{thm:levels}; the capstones'),
            ('\\verb|AGP/Threshold|', 'Eqs.~\\eqref{eq:threshold-def},~\\eqref{eq:threshold-numeric}'),
        ],
    ),
}


# AGP Eq. (45), in units of 10^-5.
_DEPOLARIZING_LEVEL_ONE_MANTISSA = 9.376


SCALARS = {
    "agp_pair_inverse": {
        "description": "Reciprocal of the AGP Eq. (31) pair count, rounded",
        "value": lambda: rf"{1e5 / _adversarial_count():.3f} \times 10^{{-5}}",
    },
    "agp_theorem3_threshold": {
        "description": "AGP 2006 Theorem 3 guaranteed threshold",
        "value": r"2.73 \times 10^{-5}",
    },
    "agp_eq36_threshold": {
        "description": "AGP 2006 Eq. (36) stated threshold lower bound",
        "value": r"2.739 \times 10^{-5}",
    },
    "agp_eq45_depolarizing": {
        "description": "AGP 2006 Eq. (45) level-one depolarizing estimate",
        "value": lambda: rf"{_DEPOLARIZING_LEVEL_ONE_MANTISSA:.3f} \times 10^{{-5}}",
    },
    "agp_eq45_depolarizing_rounded": {
        "description": "AGP 2006 Eq. (45) level-one estimate, rounded for the caption",
        "value": lambda: rf"{_DEPOLARIZING_LEVEL_ONE_MANTISSA:.1f} \times 10^{{-5}}",
    },
}
