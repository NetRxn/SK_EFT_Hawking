"""Qualitative D9 manuscript tables."""

from scripts.paper_tables import Col


def _table(description, columns, rows):
    fields = [column.field for column in columns]
    return {
        "description": description,
        "columns": columns,
        "rows": lambda: [dict(zip(fields, row, strict=True)) for row in rows],
    }


TABLES = {
    'whatcertifies': _table(
        'D9 manuscript table whatcertifies',
        [
            Col('datum', 'Datum', align='l'),
            Col('certification', 'Certifies $\\ddist$', align='l'),
            Col('route', 'Route', align='l'),
        ],
        [
            ('Readout error prob.', 'exactly', 'Table~\\ref{tab:exact}'),
            ('Pauli error weights', 'exactly', 'Table~\\ref{tab:exact}'),
            ('Reconstructed Choi', 'from above', 'Thm.~\\ref{thm:sdp}'),
            ('Choi, spectral bound only', 'from above, loosely', 'Thm.~\\ref{thm:sandwich}'),
            ('Compiler accuracy $\\varepsilon$', 'from above', '\\lean{diamondDist\\_unitaryKraus\\_le}'),
            ('$F_{\\mathrm{avg}}$ (benchmark)', '\\emph{from below only}', 'Thm.~\\ref{thm:rblower}'),
        ],
    ),
    'classes': _table(
        'D9 manuscript table classes',
        [
            Col('class', 'Class', align='l'),
            Col('basis', 'Closed by', align='l'),
            Col('response', 'Response', align='l'),
        ],
        [
            ('1. Identification', 'literature', 'disclose, keep visible'),
            ('2. Library gap', 'work', 'schedule, or cite and say so'),
            ('3. Impossibility', 'nothing', 'state as a negative result'),
            ('4. Kernel-checked, empty', 'nothing to close', 'retract the claim'),
        ],
    ),
}
