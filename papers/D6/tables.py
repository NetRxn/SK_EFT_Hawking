"""Qualitative D6 manuscript tables."""

from scripts.paper_tables import Col


def _table(description, columns, rows):
    fields = [column.field for column in columns]
    return {
        "description": description,
        "columns": columns,
        "rows": lambda: [dict(zip(fields, row, strict=True)) for row in rows],
    }


TABLES = {
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
