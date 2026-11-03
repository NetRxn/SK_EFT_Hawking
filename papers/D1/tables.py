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
}
