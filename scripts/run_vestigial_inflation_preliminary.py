"""Phase 6b Wave 3 Stage 3a — preliminary (n_s, r) scan.

Output:
  figures/data/vestigial_inflation_preliminary_scan.json
  figures/fig_ns_r_microscopic_vs_planck_bicep.png

Status: pre-Gate-B.3 reconnaissance. Per Phase6b_Roadmap.md §239,
the result of this scan is the user-authorization input to Gate B.3.
"""

import json
import dataclasses
import numpy as np
import plotly.graph_objects as go

from src.vestigial_inflation.ns_r_prediction import (
    VEST_TAU_LOWER,
    VEST_TAU_HILLTOP,
    VEST_TAU_UPPER,
    scan_microscopic_grid,
    ScanPoint,
)
from src.vestigial_inflation.planck_bicep_check import PlanckBICEPRegion


M_PL_RED = 2.435e18  # GeV (reduced Planck mass)


def main():
    # Wide log-scan over (f_0, M_φ, τ_*).
    # M_φ ∈ [10^15, 10^21] GeV  — sub-Planck → Planck → super-Planck
    # f_0 ∈ [10^48, 10^80] GeV^4 — vacuum-energy depth
    # τ_*  in (1/√5, 1) split around the hilltop √(3/5)
    Mphi_grid = np.logspace(15, 21, 13)
    f0_grid = np.logspace(48, 80, 9)
    tau_grid = np.concatenate([
        np.linspace(VEST_TAU_LOWER + 0.001, VEST_TAU_HILLTOP - 0.001, 10),
        [VEST_TAU_HILLTOP - 5e-4, VEST_TAU_HILLTOP - 1e-4],
        np.linspace(VEST_TAU_HILLTOP + 1e-4, VEST_TAU_UPPER - 0.001, 10),
    ])

    points = scan_microscopic_grid(f0_grid, Mphi_grid, tau_grid, M_Pl_red=M_PL_RED)
    region = PlanckBICEPRegion()

    viable = [p for p in points if p.viable]
    ns_r_pass = [
        p for p in points
        if abs(p.n_s - region.n_s_central) < 2 * region.n_s_sigma
        and 0 < p.r < region.r_upper_95
    ]

    # Summary statistics for the gate decision.
    all_eta = np.array([p.eta for p in points if np.isfinite(p.eta)])
    summary = {
        "scan_grid": {
            "f0_count": len(f0_grid),
            "Mphi_count": len(Mphi_grid),
            "tau_count": len(tau_grid),
            "total_points": len(points),
            "f0_GeV4_range": [float(f0_grid.min()), float(f0_grid.max())],
            "Mphi_GeV_range": [float(Mphi_grid.min()), float(Mphi_grid.max())],
            "tau_range": [float(tau_grid.min()), float(tau_grid.max())],
        },
        "planck_bicep_region": dataclasses.asdict(region),
        "verdict": {
            "viable_count_with_Ne": len(viable),
            "ns_r_pass_count_no_Ne": len(ns_r_pass),
            "Ne_min_among_ns_r_pass": float(np.min([p.N_e for p in ns_r_pass]))
                if ns_r_pass else None,
            "Mphi_over_MPlRed_at_ns_r_pass": [
                float(p.Mphi_over_MPl) for p in ns_r_pass[:5]
            ],
            "min_abs_eta_in_scan": float(np.min(np.abs(all_eta))),
            "median_abs_eta_in_scan": float(np.median(np.abs(all_eta))),
            "Mphi_required_for_eta_below_001": float(np.sqrt(3000) * M_PL_RED),
            "Mphi_required_in_MPlRed": float(np.sqrt(3000)),
            "structural_failures": [
                "eta_problem_sub_Planckian_Mphi: |η_hilltop| = 30·(M̄_P/M_φ)² > 1 for M_φ < √30 M̄_P ≈ 5.5 M̄_P",
                "Ne_overshoot_at_compatible_Mphi: even at M_φ ≈ 41 M̄_P (super-Planckian, EFT-invalid), every (n_s, r)-passing τ_* has N_e ≥ 72",
            ],
        },
        "scan_points": [dataclasses.asdict(p) for p in points],
    }

    out_json = (
        "figures/data/vestigial_inflation_preliminary_scan.json"
    )
    with open(out_json, "w") as f:
        json.dump(summary, f, indent=2, default=str)
    print(f"wrote {out_json}")

    # ── Figure: (n_s, r) scatter with Planck/BICEP region overlay ──
    finite = [
        p for p in points
        if np.isfinite(p.n_s) and np.isfinite(p.r)
        and -5 < p.n_s < 5 and 0 < p.r < 1.0
    ]
    pass_pts = ns_r_pass

    fig = go.Figure()

    # Planck/BICEP admissible region (n_s 2σ × r<0.036, light blue)
    ns_lo, ns_hi = region.n_s_band(2.0)
    fig.add_shape(
        type="rect", x0=ns_lo, x1=ns_hi, y0=0.0, y1=region.r_upper_95,
        fillcolor="rgba(50,130,220,0.18)", line={"color": "rgba(50,130,220,0.6)", "width": 1},
        layer="below",
    )
    fig.add_annotation(
        x=region.n_s_central, y=region.r_upper_95 * 0.9,
        text="Planck 2σ × BICEP r<0.036",
        showarrow=False, font={"color": "rgb(30,90,180)", "size": 11},
    )

    # All scan points (greyed)
    fig.add_trace(go.Scatter(
        x=[p.n_s for p in finite], y=[p.r for p in finite],
        mode="markers",
        marker={"size": 4, "color": "rgba(120,120,120,0.4)", "line": {"width": 0}},
        name=f"all scan ({len(finite)})",
    ))

    # (n_s, r)-passing points colored by N_e
    if pass_pts:
        fig.add_trace(go.Scatter(
            x=[p.n_s for p in pass_pts], y=[p.r for p in pass_pts],
            mode="markers",
            marker={
                "size": 7,
                "color": [p.N_e for p in pass_pts],
                "colorscale": "Viridis",
                "colorbar": {"title": "N_e"},
                "line": {"color": "rgb(0,0,0)", "width": 0.5},
            },
            text=[
                f"M_φ/M̄_P = {p.Mphi_over_MPl:.2f}<br>"
                f"τ_* = {p.tau_star:.3f}<br>"
                f"N_e = {p.N_e:.2f}"
                for p in pass_pts
            ],
            hovertemplate="n_s=%{x:.4f}<br>r=%{y:.3e}<br>%{text}<extra></extra>",
            name=f"(n_s, r)-passing ({len(pass_pts)})",
        ))

    fig.update_xaxes(
        title="n_s",
        range=[0.93, 1.0],  # zoom around Planck region
        zeroline=False,
    )
    fig.update_yaxes(
        title="r (tensor-to-scalar ratio)",
        range=[0, 0.06],
        zeroline=False,
    )
    fig.update_layout(
        title=("Vestigial Inflation Preliminary (n_s, r) Scan vs Planck/BICEP — "
               f"viable: {len(viable)}/{len(points)}"),
        template="plotly_white",
        width=900, height=600,
        margin={"l": 70, "r": 40, "t": 80, "b": 60},
    )

    out_png = "figures/fig_ns_r_microscopic_vs_planck_bicep.png"
    out_html = "figures/fig_ns_r_microscopic_vs_planck_bicep.html"
    fig.write_image(out_png, scale=2)
    fig.write_html(out_html)
    print(f"wrote {out_png}")
    print(f"wrote {out_html}")

    # ── Verdict to stdout ──
    print()
    print("─" * 64)
    print(f"VERDICT (Stage 3a preliminary, no Lean theorems committed):")
    print(f"  viable points (n_s 2σ × r<0.036 × 50<N_e<65): {len(viable)}")
    print(f"  (n_s, r)-passing only:                      {len(ns_r_pass)}")
    print(f"    — all at M_φ/M̄_P ≈ {ns_r_pass[0].Mphi_over_MPl:.1f} (super-Planckian, EFT-invalid)" if ns_r_pass else "")
    print(f"    — all with N_e ≥ {min(p.N_e for p in ns_r_pass):.1f} (overshoots [50,65])" if ns_r_pass else "")
    print(f"  η-problem: |η_hilltop| = 30·(M̄_P/M_φ)² >> 1 for any sub-Planckian M_φ")
    print(f"  M_φ required for |η_hilltop|<0.01: > {np.sqrt(3000)*M_PL_RED:.2e} GeV")
    print(f"  Recommendation: Gate B.3 → DE-ESCALATE (structural falsification path).")
    print("─" * 64)


if __name__ == "__main__":
    main()
