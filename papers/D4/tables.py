"""Canonical table specifications for D4."""

from scripts.paper_tables import Col

_GRADES_ROWS = (
    ('Theorem', 'A substantive statement, kernel-checked, no assumed hypothesis.'),
    ('Theorem (evaluated)', r"Substantive and correct, but discharged by \texttt{native\_decide}; the trust base is the Lean compiler, not the kernel."),
    ('Conditional', 'Substantive, kernel-checked, but consumes a hypothesis the project has not discharged.'),
    ('Instance', 'Verified for named finite cases, not for a general object.'),
    ('Encoding', 'The statement unfolds to the definition it names; it fixes a convention and proves nothing about it.'),
)

TABLES = {
    "grades": {
        "description": "Proof trust grades",
        "columns": [
            Col("grade", 'Grade', align=r"p{.27\columnwidth}"),
            Col("meaning", 'Meaning', align=r"p{.62\columnwidth}"),
        ],
        "rows": lambda: [dict(zip(('grade', 'meaning'), row, strict=True)) for row in _GRADES_ROWS],
    },
}
