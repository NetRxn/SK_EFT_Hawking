"""Qualitative D4 manuscript tables."""

from scripts.paper_tables import Col


def _table(description, columns, rows):
    fields = [column.field for column in columns]
    return {
        "description": description,
        "columns": columns,
        "rows": lambda: [dict(zip(fields, row, strict=True)) for row in rows],
    }


TABLES = {
    'grades': _table(
        'D4 manuscript table grades',
        [
            Col('grade', 'Grade', align='l'),
            Col('meaning', 'Meaning', align='l'),
        ],
        [
            ('Theorem', 'A substantive statement, kernel-checked, no assumed hypothesis.'),
            ('Theorem (evaluated)', 'Substantive and correct, but discharged by\n  \\texttt{native\\_decide}; the trust base is the Lean compiler, not the kernel.'),
            ('Conditional', 'Substantive, kernel-checked, but consumes a hypothesis\n  the project has not discharged.'),
            ('Instance', 'Verified for named finite cases, not for a general object.'),
            ('Encoding', 'The statement unfolds to the definition it names; it fixes a\n  convention and proves nothing about it.'),
        ],
    ),
}
