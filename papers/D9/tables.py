"""Canonical table specifications for D9."""

from scripts.paper_tables import Col

_WHAT_CERTIFIES_ROWS = (
    ('Readout error prob.', 'exactly', r"Table~\ref{tab:exact}"),
    ('Pauli error weights', 'exactly', r"Table~\ref{tab:exact}"),
    ('Reconstructed Choi', 'from above', r"Thm.~\ref{thm:sdp}"),
    ('Choi, spectral bound only', 'from above, loosely', r"Thm.~\ref{thm:sandwich}"),
    (r"Compiler accuracy $\varepsilon$", 'from above', r"\lean{diamondDist\_unitaryKraus\_le}"),
    (r"$F_{\mathrm{avg}}$ (benchmark)", r"\emph{from below only}", r"Thm.~\ref{thm:rblower}"),
)

_EXACT_ROWS = (
    (r"Dephasing $\gamma$", r"$\gamma$", r"\lean{diamondDist\_dephasing\_eq}"),
    ('Depolarizing $p$', '$p$', r"\lean{diamondDist\_depolarizing\_eq}"),
    (r"Pauli $\mathbf p$", '$1-p_0$', r"\lean{diamondDist\_pauliKraus\_eq}"),
    ('Two-qubit Pauli', '$1-p_{00}$', r"\lean{diamondDist\_twoQubitPauliKraus\_eq}"),
    ('Qutrit Weyl', '$1-p_0$', r"\lean{diamondDist\_weylKraus\_eq}"),
    ('Unitary error basis', '$1-p_0$', r"\lean{diamondDist\_errorBasisKraus\_eq}"),
    ('Cyclic-shift leakage', 'leakage prob.', r"\lean{diamondDist\_shiftLeakage\_eq}"),
    ('Readout bit-flip $q$', '$q$', r"\lean{diamondDist\_spamBitFlip\_eq}"),
    (r"Amp.\ damping $\gamma$", r"$[\gamma/2,\,\gamma{+}1{-}\sqrt{1{-}\gamma}]$", r"\lean{diamondDist\_ampDamp\_ge}, \lean{\ldots\_le}"),
    (r"Gen.\ amp.\ damping", r"$\ge (1-N)\gamma$", r"\lean{diamondDist\_genAmpDamp\_bracket}"),
)

_CLASSES_ROWS = (
    ('1. Identification', 'literature', 'disclose, keep visible'),
    ('2. Library gap', 'work', 'schedule, or cite and say so'),
    ('3. Impossibility', 'nothing', 'state as a negative result'),
    ('4. Kernel-checked, empty', 'nothing to close', 'retract the claim'),
)

TABLES = {
    "what_certifies": {
        "description": "Data and worst-case error certification",
        "columns": [
            Col("datum", 'Datum', align="l"),
            Col("certification", r"Certifies $\ddist$", align="l"),
            Col("route", 'Route', align="l"),
        ],
        "rows": lambda: [dict(zip(('datum', 'certification', 'route'), row, strict=True)) for row in _WHAT_CERTIFIES_ROWS],
    },
    "exact": {
        "description": "Exact distances and bounds by channel",
        "columns": [
            Col("channel", 'Channel', align="l"),
            Col("distance", r"$\ddist(\Phi,\mathrm{id})$", align="l"),
            Col("declaration", 'Declaration', align="l"),
        ],
        "rows": lambda: [dict(zip(('channel', 'distance', 'declaration'), row, strict=True)) for row in _EXACT_ROWS],
    },
    "classes": {
        "description": "Failure classes and responses",
        "columns": [
            Col("class", 'Class', align="l"),
            Col("closure", 'Closed by', align="l"),
            Col("response", 'Response', align="l"),
        ],
        "rows": lambda: [dict(zip(('class', 'closure', 'response'), row, strict=True)) for row in _CLASSES_ROWS],
    },
}
