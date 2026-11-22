"""Canonical table specifications for D2."""

from fractions import Fraction
from math import isclose

from scripts.paper_tables import Col
from src.core.constants import SM_FERMION_DATA, SM_Z4_CHARGE_FORMULA


_SPECIES = {
    "Q_L": r"$Q_L$",
    "u_R_bar": r"$\bar u_R$",
    "d_R_bar": r"$\bar d_R$",
    "L": r"$L$",
    "e_R_bar": r"$\bar e_R$",
    "nu_R_bar": r"$\bar\nu_R$",
}


def _sixths(value: float) -> Fraction:
    """Read the exact sixth-integer charge represented by a source float."""
    charge = Fraction(round(6 * value), 6)
    if not isclose(value, float(charge), rel_tol=0, abs_tol=1e-12):
        raise ValueError(f"Expected a sixth-integer Standard Model charge, got {value}")
    return charge


def _charge_rows() -> list[dict[str, str]]:
    rows = []
    for name, species in _SPECIES.items():
        fermion = SM_FERMION_DATA[name]
        y = _sixths(fermion["Y"])
        b_minus_l = _sixths(fermion["B_minus_L"])
        # Eq. (gem-standard) uses the rescaled García-Etxebarria--Montero charges.
        gem = -12 * y - 15 * b_minus_l
        ours = (SM_Z4_CHARGE_FORMULA["Y_coeff"] * y
                + SM_Z4_CHARGE_FORMULA["B_minus_L_coeff"] * b_minus_l)
        rows.append({
            "species": species,
            "hypercharge": f"${y}$",
            "b_minus_l": f"${b_minus_l}$",
            "gem": f"${gem}$",
            "ours": f"${ours}$",
            "difference": f"${gem - ours}$",
        })
    return rows

_BRANCHES_ROWS = (
    (r"$\mathbb{Z}_{16}$, with $\nu_R$", r"$16 N_f \equiv 0 \;(16)$", 'every $N_f$'),
    (r"$\mathbb{Z}_{16}$, no $\nu_R$", r"$15 N_f \equiv 0 \;(16)$", r"$N_f \in 16\mathbb{Z}$"),
    (r"framing, with $\nu_R$", r"$24 \mid 8 N_f$", r"$N_f \in 3\mathbb{Z}$"),
    (r"framing, no $\nu_R$", r"$48 \mid 15 N_f$", r"$N_f \in 16\mathbb{Z}$"),
)

TABLES = {
    "branches": {
        "description": "Anomaly constraints by branch",
        "columns": [
            Col("branch", 'branch', align="l"),
            Col("condition", 'condition', align="l"),
            Col("solutions", 'solutions', align="l"),
        ],
        "rows": lambda: [dict(zip(('branch', 'condition', 'solutions'), row, strict=True)) for row in _BRANCHES_ROWS],
    },
    "z4": {
        "description": "Z4 charges in both normalisations",
        "columns": [
            Col("species", 'species', align="l"),
            Col("hypercharge", '$Y$', align="r"),
            Col("b_minus_l", '$B-L$', align="r"),
            Col("gem", r"$X_{\rm GEM}$", align="r"),
            Col("ours", r"$X_{\rm ours}$", align="r"),
            Col("difference", 'difference', align="r"),
        ],
        "rows": _charge_rows,
    },
}
