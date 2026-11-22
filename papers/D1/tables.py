"""Canonical table specifications for D1."""

from math import pi, sqrt

from scripts.paper_tables import Col, Span
from scripts.paper_tables.sources import polariton_horizon_params

from scripts.gen_d1_hierarchy_table import compute_bec_hierarchy, fmt_sci_latex
from src.core.constants import GRAPHENE_PLATFORMS
from src.core.formulas import graphene_channel_cutoff_energy, quasi1d_correction_bound
from src.graphene.wkb_spectrum import compute_graphene_spectrum


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

def _dean_nozzle_rows() -> list[dict[str, str]]:
    name = "Dean_bilayer_nozzle"
    platform = GRAPHENE_PLATFORMS[name]
    spectrum = compute_graphene_spectrum(name)
    sound_speed = platform["c_s"]
    width_nm = platform["channel_width_nm"]
    throat_nm = platform["nozzle_throat_nm"]
    mean_free_path_nm = platform["l_ee_nm"]
    width, throat, mean_free_path = (x * 1e-9 for x in (width_nm, throat_nm, mean_free_path_nm))
    cutoff = graphene_channel_cutoff_energy(0, width, sound_speed)
    envelope_args = (spectrum.omega_H, cutoff, throat, width)
    total = quasi1d_correction_bound(*envelope_args, mean_free_path)
    transverse = quasi1d_correction_bound(*envelope_args, 0)
    rows = (
        (r"$c_s$ (adopted sound speed)", fmt_sci_latex(sound_speed) + r" m/s"),
        (r"$\sqrt{2}\,c_s$ (kinematic comparison)", fmt_sci_latex(sqrt(2) * sound_speed) + r" m/s"),
        (r"Velocity input for $\ell_{ee}$", fmt_sci_latex(platform["v_F"]) + " m/s"),
        (r"$L$ (throat length)", f"{throat_nm:g} nm"),
        (r"$W$ (channel width)", f"{width_nm:g} nm"),
        (r"$T_e$ (adopted electron temperature)", f"{spectrum.T_ambient_K:g} K"),
        (r"$\ell_{ee}$ (adopted spectral-model scale)", f"{mean_free_path_nm:.1f} nm"),
        (r"$\kappa$ (estimated gradient)", fmt_sci_latex(spectrum.kappa) + r" s$^{-1}$"),
        (r"$D$ (adiabaticity parameter)", f"{spectrum.D:.3f}"),
        (r"$T_H$ (leading temperature)", f"{spectrum.T_H_K:.2f} K"),
        (r"$\omega_H$ (angular frequency)", fmt_sci_latex(spectrum.omega_H) + r" s$^{-1}$"),
        (r"$f_H$ (ordinary frequency)", f"{spectrum.omega_H / (2 * pi * 1e9):.1f} GHz"),
        (r"$\omega_\perp(0)$ (first angular cutoff)", fmt_sci_latex(cutoff) + r" s$^{-1}$"),
        (r"Surface-gravity envelope at $\omega_H$", fmt_sci_latex(total - transverse)),
        (r"Evanescent envelope at $\omega_H$", fmt_sci_latex(transverse)),
        (r"Sum at $\omega_H$", f"{100 * total:.2f}" + r"\%"),
        (r"Sum at $\omega_H$ with doubled $\ell_{ee}$",
         f"{100 * quasi1d_correction_bound(*envelope_args, 2 * mean_free_path):.2f}" + r"\%"),
        (r"$S_{\rm JN}$ (ideal thermal reference)", fmt_sci_latex(spectrum.S_thermal[0]) + r" A$^2$/Hz"),
    )
    return [dict(quantity=label, value=value) for label, value in rows]


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
        "temperature": r"$\sim 134$\,mK (scale)",
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

def _paris_horizon_rows() -> list[dict]:
    rows = []
    for row in polariton_horizon_params():
        if row["parameter"] not in (r"$m^*$", r"$c_s$", r"$\xi$", r"$\kappa$"):
            continue
        smooth = row["smooth"]
        if isinstance(smooth, Span):
            rows.append({**row, "smooth": smooth.content, "steep": "--"})
        else:
            rows.append(row)
    return rows


TABLES = {
    "dean_nozzle": {
        "description": "Adopted Dean nozzle inputs and derived benchmark values",
        "columns": [Col("quantity", "Quantity", align="l"), Col("value", "Value", align="r")],
        "rows": _dean_nozzle_rows,
    },
    "paris_horizon": {
        "description": "Paris-LKB benchmark horizon inputs",
        "columns": [
            Col("parameter", "Parameter", align="l"),
            Col("smooth", "Smooth baseline", align="c"),
            Col("steep", "Steep", align="c"),
        ],
        "rows": _paris_horizon_rows,
    },
    "platform_hierarchy": {
        "description": "Dispersive and dissipative benchmark corrections",
        "columns": [
            Col("platform", 'Platform', align="l"),
            Col("temperature", "temperature scale", align="c"),
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
