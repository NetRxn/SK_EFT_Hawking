"""Canonical table specifications for D1."""

from scripts.paper_tables import Col

from scripts.gen_d1_hierarchy_table import compute_bec_hierarchy, fmt_sci_latex


_BEC_LABELS = {
    "Steinhauer": r"$^{87}$Rb BEC (Steinhauer/de~Nova)",
    "Heidelberg": r"$^{39}$K BEC (Heidelberg, projected)",
    "Trento": r"spin-sonic BEC (Trento)",
}


def _hierarchy_rows() -> list[dict[str, str]]:
    rows = []
    for name, values in compute_bec_hierarchy().items():
        dominance = values["dominance"]
        rows.append({
            "platform": _BEC_LABELS[name],
            "temperature": values["T_H_nominal_label"],
            "dispersion": fmt_sci_latex(values["delta_disp"]),
            "dissipation": fmt_sci_latex(values["delta_diss"]),
            "dominance": r"\textbf{diss}" if dominance == "diss" else dominance,
        })
    # Platform-specific orientation estimates as reported in the caption and text.
    rows.extend(_NON_BEC_ROWS)
    return rows

_NON_BEC_ROWS = [
    {
        "platform": 'LKB polariton (smooth, $D=0.59$)',
        "temperature": r"$\sim 85$\,mK",
        "dispersion": r"$-18\%$",
        "dissipation": r"$180\%$",
        "dominance": r"\emph{neither}",
    },
    {
        "platform": 'LKB polariton (steep, $D=0.94$)',
        "temperature": r"$\sim 134$\,mK",
        "dispersion": r"$-46\%$",
        "dissipation": r"$110\%$",
        "dominance": r"\emph{neither}",
    },
    {
        "platform": 'graphene (Dean, $D=0.23$)',
        "temperature": r"$\sim 2.4$\,K",
        "dispersion": r"$-2.8\%$",
        "dissipation": r"$+6.5\%$",
        "dominance": r"\textbf{diss}",
    },
]

_STATUS_ROWS = (
    (r"\texttt{acousticMetric\_det}", r"\ref{sec:eft-metric}", 'derived'),
    (r"\texttt{acoustic\_metric\_lorentzian}", r"\ref{sec:eft-metric}", 'derived'),
    (r"\texttt{acousticMetric\_inv\_correct}", r"\ref{sec:eft-metric}", 'derived'),
    (r"\texttt{hawking\_temp\_from\_surface\_gravity}", r"\ref{sec:eft-metric}", 'definitional'),
    (r"\texttt{firstOrder\_uniqueness}", r"\ref{sec:eft-first}", 'derived'),
    (r"\texttt{deltaDissFromTransport\_eq}", r"\ref{sec:eft-first}", 'definitional'),
    (r"\texttt{deltaDissFromTransport\_zero\_iff}", r"\ref{sec:eft-first}", 'derived'),
    (r"\texttt{hawking\_universality}", r"\ref{sec:eft-universality}", 'derived'),
    (r"\texttt{transport\_coefficient\_count}", r"\ref{sec:higher-count}", 'derived'),
    (r"\texttt{firstOrder\_count}, \texttt{secondOrder\_count}", r"\ref{sec:higher-count}", 'derived'),
    (r"\texttt{thirdOrder\_count}", r"\ref{sec:higher-count}", 'derived'),
    (r"\texttt{secondOrder\_count\_with\_parity}", r"\ref{sec:higher-parity}", 'derived'),
    (r"\texttt{secondOrder\_requires\_parity\_breaking}", r"\ref{sec:higher-parity}", 'definitional'),
    (r"\texttt{fullSecondOrder\_uniqueness}", r"\ref{sec:higher-positivity}", 'derived'),
    (r"\texttt{combined\_positivity\_constraint}", r"\ref{sec:higher-positivity}", 'derived'),
    (r"\texttt{firstOrder\_KMS\_optimal}", r"\ref{sec:higher-optimal}", 'derived'),
    (r"\texttt{firstOrder\_altSign\_uniqueness\_test}", r"\ref{sec:higher-optimal}", 'derived'),
    (r"\texttt{cgl\_fdr\_general}", r"\ref{sec:higher-fdr}", 'conditional'),
    (r"\texttt{einstein\_relation}", r"\ref{sec:higher-fdr}", 'conditional'),
    (r"\texttt{cgl\_implies\_secondOrderKMS}", r"\ref{sec:higher-fdr}", 'conditional'),
    (r"\texttt{turning\_point\_shift\_pos\_iff}", r"\ref{sec:wkb-turning}", 'definitional'),
    (r"\texttt{turning\_point\_shift\_eq\_decoherence}", r"\ref{sec:wkb-turning}", 'definitional'),
    (r"\texttt{unitarity\_deficit\_eq\_decoherence}", r"\ref{sec:wkb-unitarity}", 'definitional'),
    (r"\texttt{standard\_unitarity\_recovered}", r"\ref{sec:wkb-unitarity}", 'definitional'),
    (r"\texttt{decoherence\_nonneg}, \texttt{\_zero\_iff}", r"\ref{sec:wkb-unitarity}", 'definitional'),
    (r"\texttt{noise\_floor\_eq\_delta\_diss}", r"\ref{sec:wkb-crossover}", 'definitional'),
    (r"\texttt{noise\_floor\_nonneg}", r"\ref{sec:wkb-crossover}", 'definitional'),
    (r"\texttt{occupation\_reduces\_to\_beta\_sq}", r"\ref{sec:wkb-crossover}", 'definitional'),
    (r"\texttt{total\_occupation\_nonneg}", r"\ref{sec:wkb-crossover}", 'derived'),
    (r"\texttt{noise\_dominates\_when\_beta\_small}", r"\ref{sec:wkb-crossover}", 'definitional'),
    (r"\texttt{diracFluidMetric\_gtt\_vanishes}", r"\ref{sec:gr-metric}", 'derived'),
    (r"\texttt{diracFluidMetric\_y\_offdiag\_zero}", r"\ref{sec:gr-metric}", 'definitional'),
    (r"\texttt{diracFluidMetric\_txBlock\_lorentzian\_at\_horizon}", r"\ref{sec:gr-metric}", 'derived'),
    (r"\texttt{quasi1D\_validity\_bound}", r"\ref{sec:gr-metric}", 'conditional'),
    (r"\texttt{soundSpeed\_lt\_vF}", r"\ref{sec:gr-subluminal}", 'derived'),
    (r"\texttt{hawkingNoisePSD\_greybody\_mono}", r"\ref{sec:gr-noise}", 'derived'),
    (r"\texttt{snr\_sigma\_Q\_cancels}", r"\ref{sec:gr-noise}", 'derived'),
    (r"\texttt{snr\_independent\_of\_sigma\_Q}", r"\ref{sec:gr-noise}", 'derived'),
    (r"\texttt{fdt\_consistency}", r"\ref{sec:gr-noise}", 'definitional'),
    (r"\texttt{dean\_lowest\_channel\_above\_four\_omega\_H}", r"\ref{sec:gr-detect}", 'derived'),
    (r"\texttt{attenuation\_ge\_one}, \texttt{\_mono\_Gamma}", r"\ref{sec:pol-scope}", 'derived'),
    (r"\texttt{attenuation\_eq\_one\_at\_zero\_decay}", r"\ref{sec:pol-scope}", 'definitional'),
    (r"\texttt{polariton\_tier1\_fails\_tmds}", r"\ref{sec:pol-scope}", 'demarcation'),
)

TABLES = {
    "platform_hierarchy": {
        "description": "Dispersive and dissipative benchmark corrections",
        "columns": [
            Col("platform", 'Platform', align="l"),
            Col("temperature", '$T_H$', align="c"),
            Col("dispersion", r"$\delta_\text{disp}$", align="c"),
            Col("dissipation", r"$\delta_\text{diss}$", align="c"),
            Col("dominance", 'dominance', align="c"),
        ],
        "rows": _hierarchy_rows,
    },
    "status": {
        "description": "Results and proof status",
        "columns": [
            Col("result", 'Result', align="l"),
            Col("section", 'Sec.', align="l"),
            Col("status", 'Status', align="l"),
        ],
        "rows": lambda: [dict(zip(('result', 'section', 'status'), row, strict=True)) for row in _STATUS_ROWS],
    },
}
