"""D2 arithmetic table sources; physical interpretation remains in the draft."""

from fractions import Fraction
from math import gcd

from scripts.paper_tables import Col
from src.core.constants import SM_ANOMALY, SM_FERMION_DATA, SM_Z4_CHARGE_FORMULA
from src.core.formulas import sm_anomaly_index, wang_bridge_central_charge

_SPECIES = {
    "Q_L": r"$Q_L$", "u_R_bar": r"$\bar u_R$", "d_R_bar": r"$\bar d_R$",
    "L": r"$L$", "e_R_bar": r"$\bar e_R$", "nu_R_bar": r"$\bar\nu_R$",
}


def _exact_charge(value):
    charge = Fraction(value).limit_denominator(6)
    if float(charge) != value:
        raise ValueError(f"charge outside the tabulated rational convention: {value}")
    return charge


def _charge_rows():
    c = SM_Z4_CHARGE_FORMULA
    rows = []
    for key, label in _SPECIES.items():
        particle = SM_FERMION_DATA[key]
        y, b = map(_exact_charge, (particle["Y"], particle["B_minus_L"]))
        ours = c["B_minus_L_coeff"] * b + c["Y_coeff"] * y
        # Display the source-normalization conversion stated in eq:gem-standard.
        gem = -12 * y - 15 * b
        rows.append(dict(zip(("species", "Y", "BL", "GEM", "ours", "diff"),
                             (label, *(f"${x}$" for x in (y, b, gem, ours, gem - ours))),
                             strict=True)))
    return rows


def _branch_rows():
    w, wo = (sm_anomaly_index(SM_FERMION_DATA, include)["total_components"]
             for include in (True, False))
    all_weyl = sum(f["components"] for f in SM_FERMION_DATA.values())
    without_nu = all_weyl - SM_FERMION_DATA["nu_R_bar"]["components"]
    mod = SM_ANOMALY["MODULAR_INVARIANCE_MOD"]
    rows = []
    for kind, has_nu, a, m in (
        ("anomaly", True, w, 16), ("anomaly", False, wo, 16),
        ("framing", True, all_weyl, mod), ("framing", False, without_nu, mod),
    ):
        if kind == "anomaly":
            label = r"$\mathbb{Z}_{16}$"
            condition = rf'${a} N_f \equiv 0 \;({m})$'
        else:
            label = "framing"
            # c_- = a*N_f/2; keep the reduced integer condition.
            charge = Fraction(wang_bridge_central_charge(a)["c_minus_per_gen"])
            a, m = charge.numerator, m * charge.denominator
            condition = rf'${m} \mid {a} N_f$'
        n = m // gcd(m, a)
        rows.append({
            "branch": label + (r", with $\nu_R$" if has_nu else r", no $\nu_R$"),
            "condition": condition,
            "solutions": r"every $N_f$" if n == 1 else rf'$N_f \in {n}\mathbb{{Z}}$',
        })
    return rows


TABLES = {
    "branches": {
        "description": "D2 anomaly and framing divisibility by branch",
        "rows": _branch_rows,
        "columns": [Col(name, name, align="l") for name in ("branch", "condition", "solutions")],
    },
    "z4": {
        "description": "D2 generator charges in both normalizations",
        "rows": _charge_rows,
        "columns": [
            Col("species", "species", align="l"), Col("Y", "$Y$", align="r"),
            Col("BL", "$B-L$", align="r"), Col("GEM", r"$X_{\rm GEM}$", align="r"),
            Col("ours", r"$X_{\rm ours}$", align="r"), Col("diff", "difference", align="r"),
        ],
    },
}
