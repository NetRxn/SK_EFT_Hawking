#!/usr/bin/env python3
"""Canonical evaluator for Paper D1's BEC correction-hierarchy table.

This is the SINGLE declared source of truth for the numerical
dispersive/dissipative corrections quoted in the D1 hierarchy table
(``papers/D1/paper_draft.tex``, Tab.~\\ref{tab:hierarchy}) and for the
crossover / spectral-floor / accessibility narrative downstream of it.

Every value is computed from the canonical pipeline, HORIZON-evaluated
(the ``omega = kappa`` agreement point):

    constants.py (EXPERIMENTS parameters)
        -> transonic_background.solve_transonic_background  (surface gravity,
           adiabaticity D = kappa*xi/c_s)
        -> formulas.beliaev_transport_coefficients          (Gamma_Bel, gamma_dim)
        -> delta_disp = formulas.dispersive_correction(D) = -(pi/6) D^2
        -> delta_diss = gamma_dim = Gamma_H / kappa   (leading-order,
           frequency-INDEPENDENT; = first_order_correction(Gamma_H, kappa))

Both corrections are horizon quantities: ``delta_disp`` uses the horizon
adiabaticity ``D = kappa*xi/c_s`` and ``delta_diss`` is the leading-order
frequency-independent floor ``Gamma_H/kappa``. Neither depends on the
off-horizon WKB frequency contract (finding B-05), so the regenerated
numbers are stable under that reconciliation.

The three BEC platform factories in ``src/wkb/spectrum.py``
(``steinhauer_platform``, ``heidelberg_platform``, ``trento_platform``)
already route ``constants.py -> solver -> Beliaev`` through
``_platform_from_solver`` and return natural-unit ``PlatformParams`` with
``D`` and ``gamma_dim``. We reuse them verbatim so the generator and the
validated pipeline cannot diverge.

Usage::

    uv run python scripts/gen_d1_hierarchy_table.py            # print table + LaTeX rows
    uv run python scripts/gen_d1_hierarchy_table.py --json     # machine-readable dump

The rendered numbers are enforced against the paper draft by
``scripts/validate.py --check d1_hierarchy_table``.
"""

from __future__ import annotations

import argparse
import json
import math

# Canonical BEC platform factories (constants -> solver -> Beliaev chain).
from src.wkb.spectrum import (
    steinhauer_platform,
    heidelberg_platform,
    trento_platform,
)
from src.core.formulas import dispersive_correction

# Ordered exactly as the D1 hierarchy table lists the three BEC rows.
PLATFORM_FACTORIES = {
    "Steinhauer": steinhauer_platform,
    "Heidelberg": heidelberg_platform,
    "Trento": trento_platform,
}

# Nominal experimental Hawking-temperature scale printed in the table's
# T_H column. These are published / order-of-magnitude scale-setters
# (Steinhauer kappa~290 s^-1 -> 0.35 nK; Heidelberg/Trento ~1 nK), NOT the
# smooth-tanh-model surface gravity used for the correction columns. The
# table caption states this split explicitly. Values are labels, not
# computed outputs, so they are carried here as annotations only.
T_H_NOMINAL_LABEL = {
    "Steinhauer": r"$\sim 0.35$\,nK",
    "Heidelberg": r"$\sim 1$\,nK",
    "Trento": r"$\sim 1$\,nK",
}

# Dominance-classification thresholds on r = delta_diss / |delta_disp|.
_DOMINANCE_HI = 3.0   # r > 3   -> dissipation dominates
_DOMINANCE_LO = 1.0 / 3.0  # r < 1/3 -> dispersion dominates


def _dominance(ratio: float) -> str:
    if ratio > _DOMINANCE_HI:
        return "diss"
    if ratio < _DOMINANCE_LO:
        return "disp"
    return "comparable"


def compute_bec_hierarchy() -> dict[str, dict]:
    """Return the canonical horizon-evaluated hierarchy for the 3 BEC platforms.

    Returns a dict keyed by platform name; each value has keys:
        D                    adiabaticity kappa*xi/c_s (natural units)
        delta_disp           -(pi/6) D^2  (signed, dimensionless)
        delta_diss           Gamma_H/kappa = gamma_dim (dimensionless)
        ratio                delta_diss / |delta_disp|
        dominance            'disp' | 'diss' | 'comparable'
        ln_arg               ln(2 / delta_diss)
        omega_cross_over_TH  crossover frequency in units of T_H (= ln_arg)
        omega_max_over_TH    dispersive UV cutoff in units of T_H
        spectral_floor       delta_diss / 2  (FDR noise floor n_noise)
        cross_below_cutoff   omega_cross_over_TH < omega_max_over_TH
        T_H_nominal_label    LaTeX label for the (published) T_H column
    """
    out: dict[str, dict] = {}
    for name, factory in PLATFORM_FACTORIES.items():
        plat = factory()
        D = plat.D
        delta_disp = dispersive_correction(D)          # -(pi/6) D^2
        delta_diss = plat.gamma_dim                    # Gamma_H/kappa (horizon)
        ratio = delta_diss / abs(delta_disp)
        # ⚠️ THE NOISE FLOOR IS delta_diss, NOT delta_diss/2 — and halving it twice is
        # what produced a crossover too high by exactly ln 2 for three review cycles.
        #
        # `SKEFTHawking.WKBConnection.noise_floor_eq_delta_diss` states
        # `noiseFloor p = p.Gamma_H / p.kappa`, and its docstring gives the whole chain:
        # n_noise = delta_k/2 = (2*Gamma_H/kappa)/2 = Gamma_H/kappa = delta_diss. The
        # division by two is ALREADY TAKEN inside that identity. `delta_diss` here is
        # `plat.gamma_dim`, i.e. Gamma_H/kappa, so it IS the floor.
        #
        # The crossover is where the thermal occupation meets the floor:
        #     1/(exp(x) - 1) = n_noise  =>  x = ln(1 + 1/n_noise)
        # with n_noise = delta_diss.
        #
        # ⚠️ Do NOT halve the floor here, and do NOT approximate this as ln(2/delta_diss).
        # Both re-apply the halving `noise_floor_eq_delta_diss` has already taken, and the
        # two errors are consistent with each other — a halved floor and a ln(2/X)
        # crossover agree line-by-line while running high by exactly ln 2. The Lean
        # statement, not the pipeline's internal agreement, settles which form is right.
        #
        # Heidelberg: delta_diss = 1.585e-3 gives 6.44, matching the charter's "~6 T_H".
        ln_arg = math.log(1.0 + 1.0 / delta_diss)
        omega_max_over_TH = plat.omega_max / plat.T_H
        out[name] = {
            "D": D,
            "delta_disp": delta_disp,
            "delta_diss": delta_diss,
            "ratio": ratio,
            "dominance": _dominance(ratio),
            "ln_arg": ln_arg,
            "omega_cross_over_TH": ln_arg,
            "omega_max_over_TH": omega_max_over_TH,
            # n_noise = Gamma_H/kappa = delta_diss (noise_floor_eq_delta_diss). The
            # delta_k/2 halving is inside that identity, not on top of it.
            "spectral_floor": delta_diss,
            "cross_below_cutoff": ln_arg < omega_max_over_TH,
            "T_H_nominal_label": T_H_NOMINAL_LABEL[name],
        }
    return out


def fmt_sci_latex(x: float, sig: int = 3) -> str:
    """Format a small dimensionless value as LaTeX ``$m\\times10^{e}$``.

    Uses ``sig`` significant figures. This is the exact string form the
    D1 table cells carry, and the parser in ``validate.py`` reads it back.
    """
    if x == 0:
        return "$0$"
    exp = math.floor(math.log10(abs(x)))
    mant = x / (10.0 ** exp)
    mant_str = f"{mant:.{sig - 1}f}"
    return rf"${mant_str}\times10^{{{exp}}}$"


def render_latex_rows() -> str:
    """Emit the three BEC ``tabular`` rows for the D1 hierarchy table.

    Column order matches the draft:
        Platform & T_H & delta_disp & delta_diss & dominance
    with ``diss`` bold-faced (the dissipation-dominated platform).
    """
    hier = compute_bec_hierarchy()
    labels = {
        "Steinhauer": r"$^{87}$Rb BEC (Steinhauer/de~Nova)",
        "Heidelberg": r"$^{39}$K BEC (Heidelberg, projected)",
        "Trento": r"spin-sonic BEC (Trento)",
    }
    lines = []
    for name in PLATFORM_FACTORIES:
        h = hier[name]
        disp = fmt_sci_latex(h["delta_disp"])
        diss = fmt_sci_latex(h["delta_diss"])
        dom = h["dominance"]
        dom_cell = rf"\textbf{{{dom}}}" if dom == "diss" else dom
        lines.append(
            f"{labels[name]:<38s} & {h['T_H_nominal_label']} & "
            f"{disp} & {diss} & {dom_cell} \\\\"
        )
    return "\n".join(lines)


def _print_human(hier: dict[str, dict]) -> None:
    hdr = (
        f"{'Platform':<12s} {'D':>10s} {'delta_disp':>13s} {'delta_diss':>13s} "
        f"{'ratio':>8s} {'dom':>10s} {'ln(2/diss)':>11s} {'wmax/T_H':>9s} "
        f"{'floor':>11s}"
    )
    print(hdr)
    print("-" * len(hdr))
    for name, h in hier.items():
        print(
            f"{name:<12s} {h['D']:>10.4e} {h['delta_disp']:>13.4e} "
            f"{h['delta_diss']:>13.4e} {h['ratio']:>8.3f} {h['dominance']:>10s} "
            f"{h['ln_arg']:>11.4f} {h['omega_max_over_TH']:>9.2f} "
            f"{h['spectral_floor']:>11.4e}"
        )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true",
                        help="Emit machine-readable JSON and exit.")
    parser.add_argument("--latex", action="store_true",
                        help="Emit only the LaTeX tabular rows and exit.")
    args = parser.parse_args()

    hier = compute_bec_hierarchy()

    if args.json:
        print(json.dumps(hier, indent=2, sort_keys=True))
        return
    if args.latex:
        print(render_latex_rows())
        return

    _print_human(hier)
    print("\n--- LaTeX tabular rows (paste into Tab. tab:hierarchy) ---")
    print(render_latex_rows())
    print("\n--- Heidelberg crossover sentence numbers ---")
    heid = hier["Heidelberg"]
    print(f"  delta_diss = {fmt_sci_latex(heid['delta_diss'])}  "
          f"=> omega_x = T_H ln(2/delta_diss) ~ {heid['ln_arg']:.2f} T_H  "
          f"(UV cutoff ~ {heid['omega_max_over_TH']:.0f} T_H)")


if __name__ == "__main__":
    main()
