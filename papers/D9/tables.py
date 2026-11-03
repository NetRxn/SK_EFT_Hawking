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
    'exact': _table(
        'D9 diamond-distance equalities and bounds',
        [
            Col('channel', 'Channel', align="l"),
            Col('distance', '$\\ddist(\\Phi,\\mathrm{id})$', align="l"),
            Col('declaration', 'Declaration', align="l"),
        ],
        [
            ('Dephasing $\\gamma$', '$\\gamma$', '\\lean{diamondDist\\_dephasing\\_eq}'),
            ('Depolarizing $p$', '$p$', '\\lean{diamondDist\\_depolarizing\\_eq}'),
            ('Pauli $\\mathbf p$', '$1-p_0$', '\\lean{diamondDist\\_pauliKraus\\_eq}'),
            ('Two-qubit Pauli', '$1-p_{00}$', '\\lean{diamondDist\\_twoQubitPauliKraus\\_eq}'),
            ('Qutrit Weyl', '$1-p_0$', '\\lean{diamondDist\\_weylKraus\\_eq}'),
            ('Unitary error basis', '$1-p_0$', '\\lean{diamondDist\\_errorBasisKraus\\_eq}'),
            ('Cyclic-shift leakage', 'leakage prob.', '\\lean{diamondDist\\_shiftLeakage\\_eq}'),
            ('Readout bit-flip $q$', '$q$', '\\lean{diamondDist\\_spamBitFlip\\_eq}'),
            ('Amp.\\ damping $\\gamma$', '$[\\gamma/2,\\,\\gamma{+}1{-}\\sqrt{1{-}\\gamma}]$', '\\lean{diamondDist\\_ampDamp\\_ge}, \\lean{\\ldots\\_le}'),
            ('Gen.\\ amp.\\ damping', '$\\ge (1-N)\\gamma$', '\\lean{diamondDist\\_genAmpDamp\\_bracket}'),
        ],
    ),
}
TABLES['exact']['rules_after'] = (8,)
