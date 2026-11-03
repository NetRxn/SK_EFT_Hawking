"""D1 hierarchy table from the existing benchmark evaluators.

The non-BEC rows are model evaluations at the registered inputs. The adopted
dispersion law and Dean transport calibration have separate open obligations.
"""

from scripts.gen_d1_hierarchy_table import bec_hierarchy_cells
from scripts.paper_tables import Col
from src.core.constants import FALQUE_STEEP_HORIZON_KAPPA, POLARITON_PLATFORMS
from src.core.formulas import dispersive_correction, hawking_temperature
from src.graphene.hawking_predictions import graphene_hawking_prediction

_FIELDS = ("platform", "temperature", "dispersive", "dissipative", "dominance")


def _percent(value):
    return rf"${100 * value:+.1f}\%$"


def _hierarchy_rows():
    rows = bec_hierarchy_cells()
    paris = POLARITON_PLATFORMS["Paris_standard"]
    for label, kappa in (("smooth", paris["kappa"]), ("steep", FALQUE_STEEP_HORIZON_KAPPA)):
        ratio = kappa * paris["xi"] / paris["c_s"]
        rows.append((
            rf"LKB polariton ({label}, $D={ratio:.3f}$)",
            rf"${1000 * hawking_temperature(kappa):.1f}$\,mK",
            _percent(dispersive_correction(ratio)),
            _percent(paris["Gamma_pol"] / kappa),
            r"\emph{neither}",
        ))
    dean = graphene_hawking_prediction("Dean_bilayer_nozzle")
    rows.append((
        rf'graphene (Dean, $D={dean["D"]:.3f}$)',
        rf'${dean["T_H_K"]:.2f}$\,K',
        _percent(dean["delta_disp"]),
        _percent(dean["delta_diss"]),
        r"\textbf{diss}" if dean["delta_diss"] > abs(dean["delta_disp"]) else "disp",
    ))
    return [dict(zip(_FIELDS, cells, strict=True)) for cells in rows]


def _table(description, columns, rows):
    fields = [column.field for column in columns]
    return {
        "description": description,
        "columns": columns,
        "rows": lambda: [dict(zip(fields, row, strict=True)) for row in rows],
    }


TABLES = {
    "hierarchy": {
        "description": "D1 correction hierarchy at the registered benchmark inputs",
        "rows": _hierarchy_rows,
        "columns": [
            Col("platform", "Platform", align="l"),
            Col("temperature", r"$T_H$"),
            Col("dispersive", r"$\delta_\text{disp}$"),
            Col("dissipative", r"$\delta_\text{diss}$"),
            Col("dominance", "dominance"),
        ],
    },
    'status': _table(
        'D1 manuscript table status',
        [
            Col('result', 'Result', align='l'),
            Col('section', 'Sec.', align='l'),
            Col('status', 'Status', align='l'),
        ],
        [
            ('\\texttt{acousticMetric\\_det}', '\\ref{sec:eft-metric}', 'derived'),
            ('\\texttt{acoustic\\_metric\\_lorentzian}', '\\ref{sec:eft-metric}', 'derived'),
            ('\\texttt{acousticMetric\\_inv\\_correct}', '\\ref{sec:eft-metric}', 'derived'),
            ('\\texttt{hawking\\_temp\\_from\\_surface\\_gravity}', '\\ref{sec:eft-metric}', 'definitional'),
            ('\\texttt{firstOrder\\_uniqueness}', '\\ref{sec:eft-first}', 'derived'),
            ('\\texttt{deltaDissFromTransport\\_eq}', '\\ref{sec:eft-first}', 'definitional'),
            ('\\texttt{deltaDissFromTransport\\_zero\\_iff}', '\\ref{sec:eft-first}', 'derived'),
            ('\\texttt{hawking\\_universality}', '\\ref{sec:eft-universality}', 'derived'),
            ('\\texttt{transport\\_coefficient\\_count}', '\\ref{sec:higher-count}', 'derived'),
            ('\\texttt{firstOrder\\_count}, \\texttt{secondOrder\\_count}', '\\ref{sec:higher-count}', 'derived'),
            ('\\texttt{thirdOrder\\_count}', '\\ref{sec:higher-count}', 'derived'),
            ('\\texttt{secondOrder\\_count\\_with\\_parity}', '\\ref{sec:higher-parity}', 'derived'),
            ('\\texttt{secondOrder\\_requires\\_parity\\_breaking}', '\\ref{sec:higher-parity}', 'definitional'),
            ('\\texttt{fullSecondOrder\\_uniqueness}', '\\ref{sec:higher-positivity}', 'derived'),
            ('\\texttt{combined\\_positivity\\_constraint}', '\\ref{sec:higher-positivity}', 'derived'),
            ('\\texttt{firstOrder\\_KMS\\_optimal}', '\\ref{sec:higher-optimal}', 'derived'),
            ('\\texttt{firstOrder\\_altSign\\_uniqueness\\_test}', '\\ref{sec:higher-optimal}', 'derived'),
            ('\\texttt{cgl\\_fdr\\_general}', '\\ref{sec:higher-fdr}', 'conditional'),
            ('\\texttt{einstein\\_relation}', '\\ref{sec:higher-fdr}', 'conditional'),
            ('\\texttt{cgl\\_implies\\_secondOrderKMS}', '\\ref{sec:higher-fdr}', 'conditional'),
            ('\\texttt{turning\\_point\\_shift\\_pos\\_iff}', '\\ref{sec:wkb-turning}', 'definitional'),
            ('\\texttt{turning\\_point\\_shift\\_eq\\_decoherence}', '\\ref{sec:wkb-turning}', 'definitional'),
            ('\\texttt{unitarity\\_deficit\\_eq\\_decoherence}', '\\ref{sec:wkb-unitarity}', 'definitional'),
            ('\\texttt{standard\\_unitarity\\_recovered}', '\\ref{sec:wkb-unitarity}', 'definitional'),
            ('\\texttt{decoherence\\_nonneg}, \\texttt{\\_zero\\_iff}', '\\ref{sec:wkb-unitarity}', 'definitional'),
            ('\\texttt{noise\\_floor\\_eq\\_delta\\_diss}', '\\ref{sec:wkb-crossover}', 'definitional'),
            ('\\texttt{noise\\_floor\\_nonneg}', '\\ref{sec:wkb-crossover}', 'definitional'),
            ('\\texttt{occupation\\_reduces\\_to\\_beta\\_sq}', '\\ref{sec:wkb-crossover}', 'definitional'),
            ('\\texttt{total\\_occupation\\_nonneg}', '\\ref{sec:wkb-crossover}', 'derived'),
            ('\\texttt{noise\\_dominates\\_when\\_beta\\_small}', '\\ref{sec:wkb-crossover}', 'definitional'),
            ('\\texttt{diracFluidMetric\\_gtt\\_vanishes}', '\\ref{sec:gr-metric}', 'derived'),
            ('\\texttt{diracFluidMetric\\_y\\_offdiag\\_zero}', '\\ref{sec:gr-metric}', 'definitional'),
            ('\\texttt{diracFluidMetric\\_txBlock\\_lorentzian\\_at\\_horizon}', '\\ref{sec:gr-metric}', 'derived'),
            ('\\texttt{quasi1D\\_validity\\_bound}', '\\ref{sec:gr-metric}', 'conditional'),
            ('\\texttt{soundSpeed\\_lt\\_vF}', '\\ref{sec:gr-subluminal}', 'derived'),
            ('\\texttt{hawkingNoisePSD\\_greybody\\_mono}', '\\ref{sec:gr-noise}', 'derived'),
            ('\\texttt{snr\\_sigma\\_Q\\_cancels}', '\\ref{sec:gr-noise}', 'derived'),
            ('\\texttt{snr\\_independent\\_of\\_sigma\\_Q}', '\\ref{sec:gr-noise}', 'derived'),
            ('\\texttt{fdt\\_consistency}', '\\ref{sec:gr-noise}', 'definitional'),
            ('\\texttt{dean\\_lowest\\_channel\\_above\\_four\\_omega\\_H}', '\\ref{sec:gr-detect}', 'derived'),
            ('\\texttt{attenuation\\_ge\\_one}, \\texttt{\\_mono\\_Gamma}', '\\ref{sec:pol-scope}', 'derived'),
            ('\\texttt{attenuation\\_eq\\_one\\_at\\_zero\\_decay}', '\\ref{sec:pol-scope}', 'definitional'),
            ('\\texttt{polariton\\_tier1\\_fails\\_tmds}', '\\ref{sec:pol-scope}', 'demarcation'),
        ],
    ),
}
