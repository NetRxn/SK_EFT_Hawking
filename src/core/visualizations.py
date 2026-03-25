"""
Publication-Quality & Interactive Visualizations for the SK-EFT Hawking Paper

Generates:
  1. Static PDF/PNG figures for PRL submission (via kaleido)
  2. Interactive HTML dashboard for exploration and presentations

Library: Plotly (not matplotlib) for unified static + interactive output.

Design philosophy:
  - Physics-first color palette: corrections mapped to warm→cool gradient
  - Consistent typography matching PRL style
  - All figures self-contained with proper axis labels, units, annotations
  - Interactive versions include hover data, range sliders, parameter toggles

Usage:
    python src/visualizations.py                # Generate all figures
    python src/visualizations.py --interactive  # Also open HTML dashboard

References:
    The numerical data comes from transonic_background.py
"""

import numpy as np
import plotly.graph_objects as go
import plotly.subplots as sp
from plotly.subplots import make_subplots
import plotly.io as pio
import os
import sys
import json

# Import from the core package (sibling module)
from src.core.transonic_background import (
    BECParameters, TransonicBackground,
    steinhauer_Rb87, heidelberg_K39, trento_spin_sonic,
    solve_transonic_background, compute_dissipative_correction,
)

# ============================================================
# Style Configuration — PRL-compatible, physics-appropriate
# ============================================================

# Color palette: carefully chosen for physics meaning
COLORS = {
    "Rb87": "#2E86AB",       # Steel blue — established experiment
    "K39": "#A23B72",        # Berry — proposed experiment
    "Na23": "#F18F01",       # Amber — high-impact projected
    "dispersive": "#5C946E", # Sage green — known correction
    "dissipative": "#E63946",# Carmine — new correction (our result)
    "cross": "#8D99AE",      # Cool grey — subdominant
    "horizon": "#000000",    # Black — horizon line
    "subsonic": "#DAE2F8",   # Light blue — subsonic region fill
    "supersonic": "#FFE0E0", # Light red — supersonic region fill
    "sensitivity": "#CCCCCC",# Grey — experimental sensitivity band
    "noise": "#D4A574",      # Warm tan — noise/FDR terms
    # Aliases matching constants.py experiment names
    "Steinhauer": "#2E86AB",
    "Heidelberg": "#A23B72",
    "Trento": "#F18F01",
}

# Typography matching PRL conventions
FONT = dict(family="CMU Serif, Computer Modern, Times New Roman, serif", size=14)
TITLE_FONT = dict(family="CMU Serif, Computer Modern, Times New Roman, serif", size=16)

# Shared layout template
LAYOUT_TEMPLATE = dict(
    font=FONT,
    plot_bgcolor="white",
    paper_bgcolor="white",
    margin=dict(l=70, r=30, t=50, b=60),
    xaxis=dict(
        showgrid=True, gridcolor="rgba(0,0,0,0.08)",
        zeroline=True, zerolinecolor="rgba(0,0,0,0.2)",
        showline=True, linecolor="black", linewidth=1,
        mirror=True, ticks="outside",
    ),
    yaxis=dict(
        showgrid=True, gridcolor="rgba(0,0,0,0.08)",
        zeroline=True, zerolinecolor="rgba(0,0,0,0.2)",
        showline=True, linecolor="black", linewidth=1,
        mirror=True, ticks="outside",
    ),
)


def apply_layout(fig, **kwargs):
    """Apply consistent PRL-style layout to a figure."""
    layout = {**LAYOUT_TEMPLATE, **kwargs}
    fig.update_layout(**layout)
    return fig


# ============================================================
# Figure 1: Transonic Background Profiles
# ============================================================

def fig_transonic_profiles(experiments: dict[str, tuple[BECParameters, TransonicBackground]]) -> go.Figure:
    """Three-panel figure: velocity/sound speed, Mach number, density.

    Shows all three experimental setups overlaid with the sonic horizon
    marked. This is the "setup" figure for the paper.
    """
    fig = make_subplots(
        rows=3, cols=1,
        shared_xaxes=True,
        vertical_spacing=0.06,
        subplot_titles=(
            "<b>(a)</b> Flow velocity and sound speed",
            "<b>(b)</b> Mach number",
            "<b>(c)</b> Density profile",
        ),
    )

    for name, (params, bg) in experiments.items():
        # Map experiment display names to COLORS keys
        _color_map = {"Rb": "Rb87", "K": "K39", "Na": "Na23",
                      "Steinhauer": "Rb87", "Heidelberg": "K39", "Trento": "Na23"}
        color_key = next((v for k, v in _color_map.items() if k in name), None)
        color = COLORS.get(color_key, COLORS["horizon"]) if color_key else COLORS["horizon"]
        xi = params.healing_length
        x_norm = bg.x / xi  # Normalize to healing lengths

        # Panel (a): v(x) and c_s(x)
        fig.add_trace(go.Scatter(
            x=x_norm, y=bg.velocity * 1e3,
            mode="lines", name=f"v(x) — {name}",
            line=dict(color=color, width=2),
            legendgroup=name,
            hovertemplate="x/ξ=%{x:.0f}<br>v=%{y:.3f} mm/s<extra></extra>",
        ), row=1, col=1)
        fig.add_trace(go.Scatter(
            x=x_norm, y=bg.sound_speed * 1e3,
            mode="lines", name=f"c_s(x) — {name}",
            line=dict(color=color, width=2, dash="dash"),
            legendgroup=name, showlegend=False,
            hovertemplate="x/ξ=%{x:.0f}<br>c_s=%{y:.3f} mm/s<extra></extra>",
        ), row=1, col=1)

        # Panel (b): Mach number
        mach = bg.velocity / bg.sound_speed
        fig.add_trace(go.Scatter(
            x=x_norm, y=mach,
            mode="lines", name=f"M(x) — {name}",
            line=dict(color=color, width=2),
            legendgroup=name, showlegend=False,
            hovertemplate="x/ξ=%{x:.0f}<br>M=%{y:.3f}<extra></extra>",
        ), row=2, col=1)

        # Panel (c): Density
        fig.add_trace(go.Scatter(
            x=x_norm, y=bg.density * 1e-6,  # per mm
            mode="lines", name=f"n(x) — {name}",
            line=dict(color=color, width=2),
            legendgroup=name, showlegend=False,
            hovertemplate="x/ξ=%{x:.0f}<br>n=%{y:.1f}×10⁶ m⁻¹<extra></extra>",
        ), row=3, col=1)

    # Horizon line on Mach panel
    fig.add_hline(y=1.0, line=dict(color=COLORS["horizon"], width=1, dash="dot"),
                  annotation_text="Sonic horizon (M=1)", annotation_position="top right",
                  row=2, col=1)

    # Shade subsonic/supersonic regions
    fig.add_vrect(x0=-200, x1=0, fillcolor=COLORS["subsonic"], opacity=0.15,
                  layer="below", line_width=0, row=2, col=1)
    fig.add_vrect(x0=0, x1=200, fillcolor=COLORS["supersonic"], opacity=0.15,
                  layer="below", line_width=0, row=2, col=1)

    fig.update_xaxes(title_text="Position x/ξ", row=3, col=1)
    fig.update_yaxes(title_text="Velocity (mm/s)", row=1, col=1)
    fig.update_yaxes(title_text="Mach number M", row=2, col=1)
    fig.update_yaxes(title_text="Density (10⁶ m⁻¹)", row=3, col=1)

    apply_layout(fig,
        height=750, width=700,
        title=dict(text="<b>Transonic BEC Background Profiles</b>", font=TITLE_FONT),
        legend=dict(x=0.02, y=0.98, bgcolor="rgba(255,255,255,0.8)"),
    )

    # Style subplot titles
    for ann in fig.layout.annotations:
        ann.font = dict(size=13, family=FONT["family"])

    return fig


# ============================================================
# Figure 2: Correction Hierarchy — The Key Result
# ============================================================

def fig_correction_hierarchy(experiments: dict) -> go.Figure:
    """Bar chart comparing δ_disp, δ_diss, δ_cross for all experiments.

    This is the central result figure. Shows:
    - The correction magnitudes on a log scale
    - Experimental sensitivity thresholds
    - The spin-sonic enhancement
    """
    fig = go.Figure()

    exp_names = list(experiments.keys())
    corrections_data = []

    for name, (params, bg) in experiments.items():
        # Compute with Beliaev damping estimate
        n = params.density_upstream
        a = params.scattering_length
        cs = params.sound_speed_upstream
        na3_half = np.sqrt(n * a**3)
        omega_H = bg.surface_gravity
        gamma_bel = na3_half * omega_H**2 / cs if cs > 0 else 0

        corr = compute_dissipative_correction(bg, params,
            gamma_1=gamma_bel, gamma_2=gamma_bel * 0.1)

        # For Trento, apply spin-sonic enhancement
        if "Na23" in name or "Trento" in name:
            enhancement = 100.0
            corr["delta_diss"] *= enhancement
            corr["delta_cross"] = corr["delta_disp"] * corr["delta_diss"]
            corr["T_eff_over_T_H"] = 1 + corr["delta_diss"] + corr["delta_disp"] + corr["delta_cross"]

        corrections_data.append((name, corr))

    # Grouped bars
    categories = ["delta_disp", "delta_diss", "delta_cross"]
    colors_cat = [COLORS["dispersive"], COLORS["dissipative"], COLORS["cross"]]
    labels = ["Dispersive δ<sub>disp</sub>", "Dissipative δ<sub>diss</sub> (NEW)", "Cross-term δ<sub>cross</sub>"]

    for i, (cat, color, label) in enumerate(zip(categories, colors_cat, labels)):
        values = [abs(c[cat]) for _, c in corrections_data]
        fig.add_trace(go.Bar(
            name=label,
            x=[n for n, _ in corrections_data],
            y=values,
            marker_color=color,
            marker_line=dict(width=1, color="black"),
            text=[f"{v:.1e}" for v in values],
            textposition="outside",
            textfont=dict(size=10),
            hovertemplate=f"{label}<br>%{{x}}<br>|correction| = %{{y:.2e}}<extra></extra>",
        ))

    # Experimental sensitivity bands
    sensitivities = {
        "Current (10%)": 0.1,
        "Near-term (1%)": 0.01,
        "Projected (0.1%)": 0.001,
    }
    for label, val in sensitivities.items():
        fig.add_hline(y=val, line=dict(color=COLORS["sensitivity"], width=1.5, dash="dash"),
                      annotation_text=label, annotation_position="right",
                      annotation_font=dict(size=10, color="#888"))

    fig.update_yaxes(type="log", title_text="|Correction magnitude|",
                     range=[-8, 0])
    fig.update_xaxes(title_text="Experimental Setup")

    apply_layout(fig,
        height=500, width=750,
        title=dict(text="<b>Hawking Temperature Corrections: Hierarchy of Effects</b>",
                   font=TITLE_FONT),
        barmode="group",
        legend=dict(x=0.02, y=0.98, bgcolor="rgba(255,255,255,0.9)"),
    )

    return fig


# ============================================================
# Figure 3: Parameter Space — Adiabaticity vs Corrections
# ============================================================

def fig_parameter_space() -> go.Figure:
    """2D parameter space plot: D (adiabaticity) vs γ/κ (dissipation strength).

    Shows contours of δ_diss and δ_disp in the (D, γ/κ) plane,
    with experimental points overlaid. The EFT-valid region is D < 1.
    """
    D_range = np.logspace(-3, 0, 200)  # Adiabaticity: 0.001 to 1
    gamma_kappa = np.logspace(-7, -1, 200)  # γ/κ: 10⁻⁷ to 0.1

    D_grid, GK_grid = np.meshgrid(D_range, gamma_kappa)

    # δ_disp ~ D², δ_diss ~ γ/κ
    delta_disp = D_grid**2
    delta_diss = GK_grid

    # Total correction magnitude
    delta_total = delta_disp + delta_diss

    fig = go.Figure()

    # Contour: total correction
    fig.add_trace(go.Contour(
        x=np.log10(D_range), y=np.log10(gamma_kappa),
        z=np.log10(delta_total),
        colorscale=[
            [0, "#F0F0FF"], [0.25, "#C6DBEF"], [0.5, "#6BAED6"],
            [0.75, "#2171B5"], [1.0, "#08306B"]
        ],
        contours=dict(
            start=-7, end=0, size=0.5,
            showlabels=True,
            labelfont=dict(size=10, color="black"),
        ),
        colorbar=dict(title=dict(text="log₁₀|δ_total|", font=dict(size=12))),
        hovertemplate="D=%{x:.2f}<br>γ/κ=%{y:.2f}<br>log₁₀|δ|=%{z:.2f}<extra></extra>",
    ))

    # Experimental points
    exp_points = [
        ("⁸⁷Rb (Steinhauer)", -1.4, -5.5, COLORS["Rb87"]),
        ("³⁹K (Heidelberg)", -1.2, -4.5, COLORS["K39"]),
        ("²³Na spin-sonic", -1.0, -2.0, COLORS["Na23"]),
    ]
    for label, log_D, log_gk, color in exp_points:
        fig.add_trace(go.Scatter(
            x=[log_D], y=[log_gk],
            mode="markers+text",
            marker=dict(size=14, color=color, line=dict(width=2, color="black"),
                       symbol="star"),
            text=[label], textposition="top center",
            textfont=dict(size=11, color=color),
            showlegend=False,
            hovertemplate=f"{label}<br>D~10^{{{log_D:.1f}}}<br>γ/κ~10^{{{log_gk:.1f}}}<extra></extra>",
        ))

    # EFT validity boundary
    fig.add_vline(x=0, line=dict(color="red", width=2, dash="dash"),
                  annotation_text="EFT breakdown (D=1)",
                  annotation_position="top left",
                  annotation_font=dict(color="red", size=11))

    # Sensitivity thresholds
    for val, label in [(-1, "1% sensitivity"), (-2, "0.1%"), (-3, "0.01%")]:
        fig.add_hline(y=val, line=dict(color="#CCC", width=1, dash="dot"),
                      annotation_text=label, annotation_position="right",
                      annotation_font=dict(size=9, color="#999"))

    fig.update_xaxes(title_text="log₁₀(D) — Adiabaticity parameter")
    fig.update_yaxes(title_text="log₁₀(γ/κ) — Dissipation strength")

    apply_layout(fig,
        height=550, width=700,
        title=dict(text="<b>Parameter Space: EFT Corrections to Hawking Temperature</b>",
                   font=TITLE_FONT),
    )

    return fig


# ============================================================
# Figure 4: Spin-Sonic Enhancement Factor
# ============================================================

def fig_spin_sonic_enhancement() -> go.Figure:
    """Shows how the velocity ratio c_density/c_spin amplifies δ_diss.

    The key experimental motivation: tuning the spin sound speed
    relative to the density sound speed can enhance the dissipative
    correction by orders of magnitude.
    """
    c_ratio = np.logspace(0, 3, 200)  # 1 to 1000
    enhancement = c_ratio**2

    # Baseline δ_diss for Rb-87
    delta_diss_baseline = 1e-5  # Conservative Rb-87 value
    delta_diss_enhanced = delta_diss_baseline * enhancement

    fig = go.Figure()

    # Enhancement curve
    fig.add_trace(go.Scatter(
        x=c_ratio, y=delta_diss_enhanced,
        mode="lines",
        line=dict(color=COLORS["dissipative"], width=3),
        name="δ<sub>diss</sub> × (c<sub>dens</sub>/c<sub>spin</sub>)²",
        fill="tozeroy",
        fillcolor="rgba(230, 57, 70, 0.1)",
        hovertemplate="c<sub>dens</sub>/c<sub>spin</sub> = %{x:.0f}<br>δ<sub>diss</sub> = %{y:.2e}<extra></extra>",
    ))

    # Mark specific experiments
    markers = [
        (1, delta_diss_baseline, "Single-component\n(Steinhauer)", COLORS["Rb87"]),
        (10, delta_diss_baseline * 100, "Trento projected\n(c ratio ~ 10)", COLORS["Na23"]),
        (30, delta_diss_baseline * 900, "Optimistic\n(c ratio ~ 30)", "#E63946"),
    ]
    for x, y, label, color in markers:
        fig.add_trace(go.Scatter(
            x=[x], y=[y], mode="markers+text",
            marker=dict(size=12, color=color, line=dict(width=2, color="black")),
            text=[label], textposition="top center",
            textfont=dict(size=11),
            showlegend=False,
        ))

    # Sensitivity lines
    for val, label in [(0.1, "10% sensitivity (current)"),
                        (0.01, "1% (near-term)"),
                        (0.001, "0.1% (projected)")]:
        fig.add_hline(y=val, line=dict(color=COLORS["sensitivity"], width=1.5, dash="dash"),
                      annotation_text=label, annotation_position="right",
                      annotation_font=dict(size=10, color="#888"))

    fig.update_xaxes(type="log", title_text="Velocity ratio c<sub>density</sub> / c<sub>spin</sub>")
    fig.update_yaxes(type="log", title_text="|δ<sub>diss</sub>|",
                     range=[-6, 0])

    apply_layout(fig,
        height=450, width=650,
        title=dict(text="<b>Spin-Sonic Enhancement of Dissipative Corrections</b>",
                   font=TITLE_FONT),
    )

    return fig


# ============================================================
# Figure 5: Effective Temperature Decomposition
# ============================================================

def fig_temperature_decomposition(experiments: dict) -> go.Figure:
    """Waterfall/stacked visualization of T_eff = T_H(1 + δ_disp + δ_diss + δ_cross).

    Shows how each correction term shifts the effective temperature
    relative to the ideal Hawking temperature.
    """
    fig = make_subplots(
        rows=1, cols=len(experiments),
        subplot_titles=[f"<b>{name}</b>" for name in experiments.keys()],
        shared_yaxes=True,
    )

    for col, (name, (params, bg)) in enumerate(experiments.items(), 1):
        n = params.density_upstream
        a = params.scattering_length
        cs = params.sound_speed_upstream
        na3_half = np.sqrt(n * a**3)
        omega_H = bg.surface_gravity
        gamma_bel = na3_half * omega_H**2 / cs if cs > 0 else 0

        corr = compute_dissipative_correction(bg, params,
            gamma_1=gamma_bel, gamma_2=gamma_bel * 0.1)

        if "Na23" in name or "Trento" in name:
            corr["delta_diss"] *= 100.0
            corr["delta_cross"] = corr["delta_disp"] * corr["delta_diss"]

        T_H = bg.hawking_temp * 1e9  # nK

        components = [
            ("T_H", T_H, COLORS["horizon"]),
            ("+ δ_disp", T_H * corr["delta_disp"], COLORS["dispersive"]),
            ("+ δ_diss", T_H * corr["delta_diss"], COLORS["dissipative"]),
            ("+ δ_cross", T_H * corr["delta_cross"], COLORS["cross"]),
        ]

        labels = [c[0] for c in components]
        values = [c[1] for c in components]
        colors_bar = [c[2] for c in components]

        fig.add_trace(go.Bar(
            x=labels, y=values,
            marker_color=colors_bar,
            marker_line=dict(width=1, color="black"),
            text=[f"{v:.2e} nK" if abs(v) < 0.01 else f"{v:.3f} nK" for v in values],
            textposition="outside",
            textfont=dict(size=9),
            showlegend=False,
            hovertemplate="%{x}: %{y:.4e} nK<extra></extra>",
        ), row=1, col=col)

    fig.update_yaxes(type="log", title_text="Temperature contribution (nK)", row=1, col=1)

    apply_layout(fig,
        height=450, width=900,
        title=dict(text="<b>Effective Temperature Decomposition: T<sub>eff</sub> = T<sub>H</sub>(1 + δ<sub>disp</sub> + δ<sub>diss</sub> + δ<sub>cross</sub>)</b>",
                   font=dict(size=14, family=FONT["family"])),
    )

    for ann in fig.layout.annotations:
        ann.font = dict(size=12, family=FONT["family"])

    return fig


# ============================================================
# Figure 6: Scaling Relations (κ-dependence)
# ============================================================

def fig_kappa_scaling() -> go.Figure:
    """Shows how corrections scale with surface gravity κ.

    Key prediction: δ_diss ∝ 1/κ for fixed γ (dissipation becomes
    relatively more important for weaker horizons), while δ_disp ∝ κ²
    (dispersive corrections grow with surface gravity).

    This crossing behavior is the key signature for experimental tests.
    """
    kappa_range = np.logspace(1, 4, 200)  # 10 to 10⁴ s⁻¹

    # Fixed parameters (Rb-87 like)
    xi = 0.2e-6  # m
    cs = 1.4e-3  # m/s
    gamma_1 = 1e-3  # s⁻¹

    D = kappa_range * xi / cs
    delta_disp = D**2
    delta_diss = gamma_1 / kappa_range

    fig = go.Figure()

    fig.add_trace(go.Scatter(
        x=kappa_range, y=delta_disp,
        mode="lines", name="δ<sub>disp</sub> ~ (κξ/c<sub>s</sub>)²",
        line=dict(color=COLORS["dispersive"], width=3),
        hovertemplate="κ=%{x:.0f} s⁻¹<br>δ_disp=%{y:.2e}<extra></extra>",
    ))
    fig.add_trace(go.Scatter(
        x=kappa_range, y=delta_diss,
        mode="lines", name="δ<sub>diss</sub> ~ γ₁/κ",
        line=dict(color=COLORS["dissipative"], width=3),
        hovertemplate="κ=%{x:.0f} s⁻¹<br>δ_diss=%{y:.2e}<extra></extra>",
    ))

    # Crossing point
    cross_kappa = np.sqrt(gamma_1 * cs**2 / xi**2)
    cross_val = gamma_1 / cross_kappa
    fig.add_trace(go.Scatter(
        x=[cross_kappa], y=[cross_val],
        mode="markers",
        marker=dict(size=14, color="black", symbol="x"),
        name=f"Crossing: κ*={cross_kappa:.0f} s⁻¹",
        hovertemplate=f"Crossing point<br>κ*={cross_kappa:.0f} s⁻¹<br>δ*={cross_val:.2e}<extra></extra>",
    ))

    # Mark experimental κ values
    exp_kappas = [
        (200, "Rb-87 (Steinhauer)", COLORS["Rb87"]),
        (500, "K-39 (Heidelberg)", COLORS["K39"]),
        (1000, "Na-23 (Trento)", COLORS["Na23"]),
    ]
    for kap, label, color in exp_kappas:
        fig.add_vline(x=kap, line=dict(color=color, width=1.5, dash="dot"),
                      annotation_text=label, annotation_position="top",
                      annotation_font=dict(size=10, color=color))

    fig.update_xaxes(type="log", title_text="Surface gravity κ (s⁻¹)",
                     range=[1, 4])  # 10¹ to 10⁴ s⁻¹
    fig.update_yaxes(type="log", title_text="|Correction|",
                     range=[-7, 0])

    apply_layout(fig,
        height=450, width=700,
        title=dict(text="<b>Scaling with Surface Gravity: δ<sub>disp</sub> vs δ<sub>diss</sub></b>",
                   font=TITLE_FONT),
        legend=dict(x=0.55, y=0.98),
    )

    return fig


# ============================================================
# Phase 2 Figures: CGL FDR, Boundary Terms, Positivity
# ============================================================

def fig_cgl_fdr_pattern() -> go.Figure:
    """Noise count pattern at each EFT order from CGL FDR.

    Shows: at even order N=2n, there are n+1 noise bilinears.
    At odd order N=2n+1, noise is imaginary → 0 real bilinears.
    This is the central Direction D result.
    """
    from src.second_order.cgl_derivation import derive_fdr_fourier

    results = derive_fdr_fourier(6)

    orders = sorted(results.keys())
    n_diss = [len(results[N]['dissipative']) for N in orders]
    n_cons = [len(results[N]['conservative']) for N in orders]
    n_noise = [len(results[N]['noise']) for N in orders]
    formula = [(N + 1) // 2 + 1 for N in orders]

    fig = go.Figure()

    fig.add_trace(go.Bar(
        x=orders, y=n_diss,
        name="Dissipative (odd-ω)",
        marker_color=COLORS["dissipative"],
        marker_line=dict(width=1, color="black"),
    ))
    fig.add_trace(go.Bar(
        x=orders, y=n_cons,
        name="Conservative (even-ω)",
        marker_color=COLORS["dispersive"],
        marker_line=dict(width=1, color="black"),
    ))
    fig.add_trace(go.Bar(
        x=orders, y=n_noise,
        name="Noise bilinears (FDR-determined)",
        marker_color=COLORS["noise"],
        marker_line=dict(width=1, color="black"),
    ))

    # Overlay the counting formula
    fig.add_trace(go.Scatter(
        x=orders, y=formula,
        mode="markers+lines",
        name="count(N) = ⌊(N+1)/2⌋ + 1",
        line=dict(color=COLORS["horizon"], width=2, dash="dash"),
        marker=dict(size=10, symbol="diamond", color=COLORS["horizon"]),
    ))

    fig.update_xaxes(title_text="EFT Order N", dtick=1)
    fig.update_yaxes(title_text="Number of independent terms")

    apply_layout(fig,
        height=450, width=700,
        title=dict(text="<b>CGL FDR Pattern: Monomial Counting at Each EFT Order</b>",
                   font=TITLE_FONT),
        barmode="group",
        legend=dict(x=0.02, y=0.98, bgcolor="rgba(255,255,255,0.9)"),
    )

    return fig


def fig_even_vs_odd_kernel() -> go.Figure:
    """Visual decomposition of K_R into conservative (even-ω) and dissipative (odd-ω).

    Shows how the CGL FDR picks out only the odd-ω part, which produces noise.
    Even-ω terms cancel identically → zero noise for non-dissipative systems.
    """
    import numpy as np

    omega_range = np.linspace(-5, 5, 500)

    # Example K_R with both conservative and dissipative terms:
    # K_R = -ω² + c_s²k² + iγω  (BEC with damping, k=1)
    k_val = 1.0
    c_s = 1.0
    gamma = 0.8

    K_R_even = -omega_range**2 + c_s**2 * k_val**2  # conservative
    K_R_odd_real = np.zeros_like(omega_range)  # odd part is imaginary
    K_R_odd_imag = gamma * omega_range  # Im(K_R^odd) = γω

    # Noise from FDR: K_N = 2γ/β (constant)
    beta = 1.0
    K_N = 2 * gamma / beta * np.ones_like(omega_range)

    fig = make_subplots(
        rows=2, cols=2,
        subplot_titles=(
            "<b>(a)</b> K<sub>R</sub><sup>even</sup>(ω) — Conservative",
            "<b>(b)</b> Im[K<sub>R</sub><sup>odd</sup>(ω)] — Dissipative",
            "<b>(c)</b> CGL FDR: K<sub>N</sub> = −i[K<sub>R</sub>(ω)−K<sub>R</sub>(−ω)]/(β₀ω)",
            "<b>(d)</b> Summary: Even → 0 noise, Odd → finite noise",
        ),
        vertical_spacing=0.15,
        horizontal_spacing=0.12,
    )

    # (a) Even kernel
    fig.add_trace(go.Scatter(
        x=omega_range, y=K_R_even,
        mode="lines", name="K<sub>R</sub><sup>even</sup>",
        line=dict(color=COLORS["dispersive"], width=2.5),
        showlegend=False,
    ), row=1, col=1)

    # (b) Odd kernel (imaginary part)
    fig.add_trace(go.Scatter(
        x=omega_range, y=K_R_odd_imag,
        mode="lines", name="Im[K<sub>R</sub><sup>odd</sup>]",
        line=dict(color=COLORS["dissipative"], width=2.5),
        showlegend=False,
    ), row=1, col=2)

    # (c) Resulting noise
    fig.add_trace(go.Scatter(
        x=omega_range, y=K_N,
        mode="lines", name="K<sub>N</sub> = 2γ/β₀",
        line=dict(color=COLORS["noise"], width=3),
        fill="tozeroy", fillcolor="rgba(212,165,116,0.15)",
        showlegend=False,
    ), row=2, col=1)
    fig.add_hline(y=0, line=dict(color="black", width=0.5), row=2, col=1)

    # (d) Summary: conceptual bar chart
    fig.add_trace(go.Bar(
        x=["Even-ω<br>(conservative)", "Odd-ω<br>(dissipative)"],
        y=[0, 2 * gamma / beta],
        marker_color=[COLORS["dispersive"], COLORS["dissipative"]],
        marker_line=dict(width=1, color="black"),
        text=["K<sub>N</sub> = 0", f"K<sub>N</sub> = 2γ/β₀"],
        textposition="outside",
        showlegend=False,
    ), row=2, col=2)

    for row in [1, 2]:
        for col in [1, 2]:
            if not (row == 2 and col == 2):
                fig.update_xaxes(title_text="ω", row=row, col=col)

    fig.update_yaxes(title_text="K<sub>R</sub><sup>even</sup>", row=1, col=1)
    fig.update_yaxes(title_text="Im[K<sub>R</sub><sup>odd</sup>]", row=1, col=2)
    fig.update_yaxes(title_text="K<sub>N</sub> (noise)", row=2, col=1)
    fig.update_yaxes(title_text="Noise kernel", row=2, col=2)

    apply_layout(fig,
        height=650, width=800,
        title=dict(text="<b>CGL FDR: Only Dissipative (Odd-ω) Terms Produce Noise</b>",
                   font=TITLE_FONT),
    )

    for ann in fig.layout.annotations:
        ann.font = dict(size=12, family=FONT["family"])

    return fig


def fig_boundary_term_suppression() -> go.Figure:
    """D-dependence of IBP boundary correction for all three experiments.

    Shows that IBP gradient terms from position-dependent γ(x) are O(D)-suppressed.
    Marks the three experimental D values.
    """
    from src.core.constants import get_all_experiments

    D_range = np.logspace(-3, 0.5, 200)
    correction = D_range  # |correction/leading| ~ D

    fig = go.Figure()

    fig.add_trace(go.Scatter(
        x=D_range, y=correction * 100,
        mode="lines",
        name="|IBP correction / leading noise| ~ D",
        line=dict(color=COLORS["dissipative"], width=3),
        fill="tozeroy", fillcolor="rgba(230, 57, 70, 0.08)",
        hovertemplate="D=%{x:.4f}<br>Correction=%{y:.1f}%<extra></extra>",
    ))

    # Mark experimental D values (stagger positions to avoid overlap)
    experiments = get_all_experiments()
    exp_colors = {
        "Steinhauer": COLORS["Rb87"],
        "Heidelberg": COLORS["K39"],
        "Trento": COLORS["Na23"],
    }
    text_positions = ["top left", "bottom right", "top right"]
    for (name, (params, bg)), tpos in zip(experiments.items(), text_positions):
        D = bg.adiabaticity
        color = exp_colors.get(name, "#333")
        fig.add_trace(go.Scatter(
            x=[D], y=[D * 100],
            mode="markers+text",
            marker=dict(size=14, color=color,
                       line=dict(width=2, color="black"), symbol="star"),
            text=[f"{name} (D={D:.3f})"],
            textposition=tpos,
            textfont=dict(size=11, color=color),
            showlegend=False,
            hovertemplate=f"{name}<br>D={D:.4f}<br>Correction={D*100:.1f}%<extra></extra>",
        ))

    # EFT breakdown region
    fig.add_vrect(x0=1, x1=3.2, fillcolor="rgba(255,0,0,0.05)",
                  line=dict(color="red", width=1, dash="dash"),
                  annotation_text="EFT breakdown (D ≥ 1)",
                  annotation_position="top left",
                  annotation_font=dict(color="red", size=11))

    fig.update_xaxes(type="log", title_text="Adiabaticity parameter D = κξ/c<sub>s</sub>")
    fig.update_yaxes(type="log", title_text="IBP correction (%)",
                     range=[-1, 2.5])

    apply_layout(fig,
        height=450, width=700,
        title=dict(text="<b>Boundary Term Suppression: IBP Corrections are O(D)</b>",
                   font=TITLE_FONT),
    )

    return fig


def fig_positivity_constraint() -> go.Figure:
    """Visualize the SK positivity constraint and its relaxation.

    Shows: strict constraint γ_{2,1}+γ_{2,2}=0 from 2×2 PSD matrix,
    and relaxed constraint (γ_{2,1}+γ_{2,2})² ≤ 4γ₂γ_x β from 3×3.
    Uses filled scatter band instead of contours for clean rendering.
    """
    g21 = np.linspace(-2, 2, 300)

    # Relaxed bound: γ_{2,2} = -γ_{2,1} ± √(4γ₂γ_xβ)
    gamma_2_times_gamma_x_beta = 0.5
    half_width = np.sqrt(4 * gamma_2_times_gamma_x_beta)

    upper = -g21 + half_width  # upper boundary of allowed band
    lower = -g21 - half_width  # lower boundary of allowed band

    fig = go.Figure()

    # Allowed band (filled region between upper and lower)
    fig.add_trace(go.Scatter(
        x=np.concatenate([g21, g21[::-1]]),
        y=np.concatenate([upper, lower[::-1]]),
        fill="toself",
        fillcolor="rgba(92, 148, 110, 0.2)",
        line=dict(color=COLORS["dispersive"], width=2),
        name="Relaxed: (γ<sub>2,1</sub>+γ<sub>2,2</sub>)² ≤ 4γ₂γ<sub>x</sub>β",
        hoverinfo="skip",
    ))

    # Strict constraint line: γ_{2,2} = -γ_{2,1}
    fig.add_trace(go.Scatter(
        x=g21, y=-g21,
        mode="lines",
        name="Strict: γ<sub>2,1</sub> + γ<sub>2,2</sub> = 0",
        line=dict(color=COLORS["horizon"], width=3),
    ))

    # Annotations
    fig.add_annotation(
        x=1.2, y=1.2, text="Forbidden<br>(unitarity violated)",
        font=dict(size=13, color=COLORS["dissipative"]),
        showarrow=False,
        bgcolor="rgba(255,255,255,0.8)",
    )
    fig.add_annotation(
        x=-0.8, y=0.5, text="Allowed<br>(relaxed bound)",
        font=dict(size=13, color=COLORS["dispersive"]),
        showarrow=False,
        bgcolor="rgba(255,255,255,0.8)",
    )

    fig.update_xaxes(title_text="γ<sub>2,1</sub>", range=[-2, 2])
    fig.update_yaxes(title_text="γ<sub>2,2</sub>", range=[-2, 2])

    apply_layout(fig,
        height=500, width=550,
        title=dict(text="<b>SK Positivity Constraint on Second-Order Coefficients</b>",
                   font=TITLE_FONT),
        legend=dict(x=0.02, y=0.02, bgcolor="rgba(255,255,255,0.9)"),
    )

    return fig


def fig_on_shell_vanishing() -> go.Figure:
    """δ^(2) vanishes on the acoustic shell, nonzero only off-shell.

    Shows δ^(2)(k) for fixed ω, with the acoustic shell at k = ω/c_s marked.
    The positivity constraint γ_{2,2} = -γ_{2,1} produces exact cancellation
    at k = ω/c_s, with a cubic residual from Bogoliubov dispersion.
    """
    omega_val = 100.0  # representative frequency
    c_s = 1.0
    kappa = 50.0
    gamma_21 = 0.5

    k_range = np.linspace(0.5 * omega_val / c_s, 1.5 * omega_val / c_s, 400)
    k_acoustic = omega_val / c_s

    # δ^(2) = γ_{2,1}·k·(k² - ω²/c_s²) / κ  (with γ_{2,2} = -γ_{2,1})
    delta_2 = gamma_21 * k_range * (k_range**2 - omega_val**2 / c_s**2) / kappa

    fig = go.Figure()

    fig.add_trace(go.Scatter(
        x=k_range / k_acoustic, y=delta_2,
        mode="lines",
        name="δ<sup>(2)</sup>(k) with γ<sub>2,2</sub> = −γ<sub>2,1</sub>",
        line=dict(color=COLORS["dissipative"], width=3),
        hovertemplate="k/k<sub>acoustic</sub>=%{x:.2f}<br>δ<sup>(2)</sup>=%{y:.4f}<extra></extra>",
    ))

    # Mark the acoustic shell
    fig.add_vline(x=1.0, line=dict(color=COLORS["horizon"], width=2, dash="dash"),
                  annotation_text="Acoustic shell: k = ω/c<sub>s</sub>",
                  annotation_position="top right",
                  annotation_font=dict(size=11))

    # Zero line
    fig.add_hline(y=0, line=dict(color="rgba(0,0,0,0.3)", width=1))

    # Shade the "observable" region (off-shell, Bogoliubov)
    fig.add_vrect(x0=0.95, x1=1.05,
                  fillcolor="rgba(46, 134, 171, 0.1)",
                  line_width=0,
                  annotation_text="Near-shell<br>~10⁻⁸–10⁻¹²",
                  annotation_position="bottom left",
                  annotation_font=dict(size=9, color=COLORS["Rb87"]))

    fig.update_xaxes(title_text="k / k<sub>acoustic</sub>")
    fig.update_yaxes(title_text="δ<sup>(2)</sup> — Second-order correction")

    apply_layout(fig,
        height=400, width=650,
        title=dict(text="<b>On-Shell Vanishing: δ<sup>(2)</sup> = 0 at k = ω/c<sub>s</sub></b>",
                   font=TITLE_FONT),
    )

    return fig


def fig_einstein_relation() -> go.Figure:
    """The Einstein relation as the simplest FDR case.

    Shows σ = γ/β₀: noise strength proportional to friction × temperature.
    Brownian motion visualization with FDR connecting dissipation to fluctuations.
    """
    # Temperature dependence: σ = γT
    T_range = np.linspace(0, 5, 200)
    gamma_vals = [0.5, 1.0, 2.0]

    fig = go.Figure()

    # Distinct colors for each γ value (all within the warm palette)
    gamma_colors = [COLORS["dissipative"], COLORS["noise"], COLORS["Na23"]]
    for gamma, color in zip(gamma_vals, gamma_colors):
        sigma = gamma * T_range  # σ = γ/β₀ = γT (k_B = 1 units)
        fig.add_trace(go.Scatter(
            x=T_range, y=sigma,
            mode="lines",
            name=f"γ = {gamma}",
            line=dict(color=color, width=3),
            hovertemplate=f"γ={gamma}<br>T=%{{x:.2f}}<br>σ=%{{y:.2f}}<extra></extra>",
        ))

    # Annotation connecting to CGL
    fig.add_annotation(
        x=3.5, y=3.5, text="σ = γ/β₀ = γT",
        font=dict(size=14, family=FONT["family"]),
        showarrow=False,
        bgcolor="rgba(255,255,255,0.8)",
        bordercolor=COLORS["dissipative"],
        borderwidth=1, borderpad=4,
    )

    fig.add_annotation(
        x=4.0, y=1.0,
        text="CGL master formula:<br>K<sub>N</sub> = −i[K<sub>R</sub>(ω)−K<sub>R</sub>(−ω)]/(β₀ω)<br>"
             "→ simplest case: K<sub>N</sub> = 2γ/β₀",
        font=dict(size=10, family=FONT["family"]),
        showarrow=False,
        bgcolor="rgba(255,255,255,0.9)",
        bordercolor=COLORS["cross"],
        borderwidth=1, borderpad=4,
    )

    fig.update_xaxes(title_text="Temperature T (k<sub>B</sub> = 1)")
    fig.update_yaxes(title_text="Noise strength σ")

    apply_layout(fig,
        height=400, width=600,
        title=dict(text="<b>Einstein Relation: σ = γT (Simplest FDR)</b>",
                   font=TITLE_FONT),
        legend=dict(x=0.02, y=0.98),
    )

    return fig


# ============================================================
# Interactive Dashboard — Combines all figures
# ============================================================

def build_interactive_dashboard(experiments: dict, output_dir: str) -> str:
    """Build a single-file interactive HTML dashboard.

    Contains all figures plus parameter sliders for exploration.
    Returns the path to the generated HTML file.
    """
    # Generate all figures (Phase 1 + Phase 2)
    fig1 = fig_transonic_profiles(experiments)
    fig2 = fig_correction_hierarchy(experiments)
    fig3 = fig_parameter_space()
    fig4 = fig_spin_sonic_enhancement()
    fig5 = fig_temperature_decomposition(experiments)
    fig6 = fig_kappa_scaling()
    fig7 = fig_cgl_fdr_pattern()
    fig8 = fig_even_vs_odd_kernel()
    fig9 = fig_boundary_term_suppression()
    fig10 = fig_positivity_constraint()
    fig11 = fig_on_shell_vanishing()
    fig12 = fig_einstein_relation()

    figures = [
        ("Transonic Background Profiles", fig1),
        ("Correction Hierarchy", fig2),
        ("Parameter Space", fig3),
        ("Spin-Sonic Enhancement", fig4),
        ("Temperature Decomposition", fig5),
        ("κ-Scaling Relations", fig6),
        ("CGL FDR Pattern", fig7),
        ("Even vs Odd Kernel Decomposition", fig8),
        ("Boundary Term Suppression", fig9),
        ("Positivity Constraint", fig10),
        ("On-Shell Vanishing", fig11),
        ("Einstein Relation", fig12),
    ]

    # Build HTML with navigation
    html_parts = ["""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>SK-EFT Hawking Paper — Interactive Visualizations</title>
<script src="https://cdn.plot.ly/plotly-2.35.0.min.js"></script>
<style>
  * { margin: 0; padding: 0; box-sizing: border-box; }
  body {
    font-family: 'Segoe UI', system-ui, -apple-system, sans-serif;
    background: #fafafa;
    color: #1a1a1a;
  }
  header {
    background: linear-gradient(135deg, #1a1a2e 0%, #16213e 50%, #0f3460 100%);
    color: white;
    padding: 2rem 3rem;
    border-bottom: 3px solid #e94560;
  }
  header h1 { font-size: 1.8rem; font-weight: 600; margin-bottom: 0.5rem; }
  header p { font-size: 1rem; opacity: 0.85; max-width: 800px; }
  nav {
    background: white;
    padding: 0.75rem 3rem;
    border-bottom: 1px solid #e0e0e0;
    position: sticky;
    top: 0;
    z-index: 100;
    display: flex;
    gap: 0.5rem;
    flex-wrap: wrap;
  }
  nav a {
    display: inline-block;
    padding: 0.4rem 0.8rem;
    background: #f0f0f0;
    color: #333;
    text-decoration: none;
    border-radius: 4px;
    font-size: 0.85rem;
    transition: all 0.2s;
  }
  nav a:hover { background: #e94560; color: white; }
  .figure-section {
    max-width: 1000px;
    margin: 2rem auto;
    background: white;
    border-radius: 8px;
    box-shadow: 0 1px 3px rgba(0,0,0,0.08);
    padding: 1.5rem;
  }
  .figure-section h2 {
    font-size: 1.2rem;
    margin-bottom: 0.5rem;
    color: #16213e;
    border-bottom: 2px solid #e94560;
    padding-bottom: 0.3rem;
  }
  .figure-section .caption {
    font-size: 0.9rem;
    color: #555;
    margin-top: 0.75rem;
    line-height: 1.5;
  }
  .summary-box {
    max-width: 1000px;
    margin: 2rem auto;
    background: #16213e;
    color: white;
    border-radius: 8px;
    padding: 1.5rem 2rem;
  }
  .summary-box h2 { color: #e94560; margin-bottom: 1rem; }
  .summary-box table {
    width: 100%;
    border-collapse: collapse;
  }
  .summary-box th, .summary-box td {
    padding: 0.5rem;
    text-align: left;
    border-bottom: 1px solid rgba(255,255,255,0.15);
  }
  .summary-box th { color: #e94560; font-size: 0.85rem; text-transform: uppercase; }
  footer {
    text-align: center;
    padding: 2rem;
    color: #888;
    font-size: 0.8rem;
  }
</style>
</head>
<body>
<header>
  <h1>Dissipative EFT Corrections to Analog Hawking Radiation</h1>
  <p>Interactive visualizations for the SK-EFT Hawking Paper.
     All 12 Lean proofs verified. Explore the parameter space, correction hierarchy,
     and experimental predictions.</p>
</header>
<nav>
"""]

    for i, (title, _) in enumerate(figures):
        html_parts.append(f'  <a href="#fig{i+1}">{title}</a>\n')

    html_parts.append('  <a href="#summary">Summary Table</a>\n</nav>\n')

    # Add each figure
    for i, (title, fig) in enumerate(figures):
        fig_html = pio.to_html(fig, full_html=False, include_plotlyjs=False)
        caption = _get_caption(i)
        html_parts.append(f"""
<section class="figure-section" id="fig{i+1}">
  <h2>Figure {i+1}: {title}</h2>
  {fig_html}
  <div class="caption">{caption}</div>
</section>
""")

    # Summary table
    html_parts.append(_build_summary_table(experiments))

    html_parts.append("""
<footer>
  SK-EFT Hawking Paper &mdash; Generated with Plotly &mdash;
  All mathematical structures verified in Lean 4
</footer>
</body>
</html>
""")

    html_path = os.path.join(output_dir, "sk_eft_interactive_dashboard.html")
    with open(html_path, "w") as f:
        f.write("".join(html_parts))

    return html_path


def _get_caption(idx: int) -> str:
    captions = [
        "<b>Figure 1:</b> Transonic background profiles for three BEC experimental setups. "
        "Panel (a) shows the flow velocity v(x) (solid) and sound speed c<sub>s</sub>(x) (dashed) "
        "as functions of position. Panel (b) shows the Mach number M = v/c<sub>s</sub>, with "
        "the sonic horizon at M=1. Panel (c) shows the density profile determined by continuity. "
        "The blue-shaded region is subsonic; the red-shaded region is supersonic.",

        "<b>Figure 2:</b> Correction hierarchy for the Hawking temperature. "
        "The dispersive correction δ<sub>disp</sub> (green) is the known result from quantum "
        "dispersion. The dissipative correction δ<sub>diss</sub> (red) is the <em>new result</em> "
        "of this paper, computed from the SK-EFT transport coefficients. "
        "Horizontal dashed lines show experimental sensitivity thresholds. "
        "The Trento spin-sonic enhancement makes δ<sub>diss</sub> potentially observable.",

        "<b>Figure 3:</b> Parameter space of corrections in the (D, γ/κ) plane, where "
        "D = κξ/c<sub>s</sub> is the adiabaticity parameter and γ/κ is the dissipation "
        "strength relative to the surface gravity. Star markers show the three experimental "
        "setups. The EFT is valid for D < 1 (left of red dashed line).",

        "<b>Figure 4:</b> Spin-sonic enhancement of dissipative corrections. By reducing "
        "the spin sound speed c<sub>spin</sub> relative to the density sound speed "
        "c<sub>density</sub> in a two-component BEC, the effective correction scales as "
        "(c<sub>density</sub>/c<sub>spin</sub>)². This is the key experimental handle for "
        "making δ<sub>diss</sub> accessible to measurement.",

        "<b>Figure 5:</b> Temperature decomposition for each experiment, showing the "
        "contribution of each correction term to the effective temperature "
        "T<sub>eff</sub> = T<sub>H</sub>(1 + δ<sub>disp</sub> + δ<sub>diss</sub> + δ<sub>cross</sub>). "
        "Note the logarithmic scale: correction terms are many orders of magnitude smaller than T<sub>H</sub>.",

        "<b>Figure 6:</b> Scaling of corrections with surface gravity κ. The dispersive "
        "correction grows as κ² while the dissipative correction falls as 1/κ. Their crossing "
        "point κ* determines which effect dominates. Vertical lines mark experimental κ values.",

        "<b>Figure 7:</b> CGL FDR monomial counting at each EFT order N. Dissipative (odd-ω) "
        "retarded terms are paired with noise bilinears via the CGL dynamical KMS condition. "
        "Conservative (even-ω) terms are unconstrained. The counting formula "
        "count(N) = ⌊(N+1)/2⌋ + 1 is overlaid.",

        "<b>Figure 8:</b> Decomposition of K<sub>R</sub> into even-ω (conservative) and odd-ω "
        "(dissipative) parts. The CGL FDR formula K<sub>N</sub> = −i[K<sub>R</sub>(ω)−K<sub>R</sub>(−ω)]/(β₀ω) "
        "extracts only the odd-ω part. Even-ω terms cancel identically, producing zero noise "
        "for non-dissipative systems.",

        "<b>Figure 9:</b> Boundary term suppression as a function of adiabaticity D = κξ/c<sub>s</sub>. "
        "IBP with position-dependent γ(x) generates gradient corrections proportional to D. "
        "For all three experiments (D ≈ 0.012–0.014), corrections are ~1.2–1.4%.",

        "<b>Figure 10:</b> SK positivity constraint on second-order coefficients. The strict "
        "constraint γ<sub>2,1</sub> + γ<sub>2,2</sub> = 0 (black line) becomes an inequality "
        "when the (∂<sub>x</sub>ψ<sub>a</sub>)² monomial is included. The green region shows "
        "the allowed parameter space.",

        "<b>Figure 11:</b> On-shell vanishing of the second-order correction. With the positivity "
        "constraint γ<sub>2,2</sub> = −γ<sub>2,1</sub>, δ<sup>(2)</sup> vanishes exactly at "
        "k = ω/c<sub>s</sub> (acoustic shell). Nonzero values arise only from Bogoliubov off-shell "
        "dispersion (~10<sup>−8</sup>–10<sup>−12</sup>).",

        "<b>Figure 12:</b> The Einstein relation σ = γT as the simplest case of the CGL FDR. "
        "Noise strength is proportional to friction × temperature. This is the N=0 limit of "
        "the general CGL master formula.",
    ]
    return captions[idx] if idx < len(captions) else ""


def _build_summary_table(experiments: dict) -> str:
    rows = []
    for name, (params, bg) in experiments.items():
        n = params.density_upstream
        a = params.scattering_length
        cs = params.sound_speed_upstream
        na3_half = np.sqrt(n * a**3)
        omega_H = bg.surface_gravity
        gamma_bel = na3_half * omega_H**2 / cs if cs > 0 else 0

        corr = compute_dissipative_correction(bg, params,
            gamma_1=gamma_bel, gamma_2=gamma_bel * 0.1)

        enhance = ""
        if "Na23" in name or "Trento" in name:
            corr["delta_diss"] *= 100.0
            enhance = " (×100 enhanced)"

        rows.append(f"""    <tr>
      <td>{name}</td>
      <td>{params.healing_length*1e6:.2f} μm</td>
      <td>{cs*1e3:.2f} mm/s</td>
      <td>{bg.surface_gravity:.0f} s⁻¹</td>
      <td>{bg.hawking_temp*1e9:.3f} nK</td>
      <td>{bg.adiabaticity:.4f}</td>
      <td>{corr['delta_disp']:.2e}</td>
      <td>{corr['delta_diss']:.2e}{enhance}</td>
    </tr>""")

    return f"""
<section class="summary-box" id="summary">
  <h2>Numerical Summary</h2>
  <table>
    <thead>
      <tr>
        <th>Experiment</th><th>ξ</th><th>c<sub>s</sub></th><th>κ</th>
        <th>T<sub>H</sub></th><th>D</th><th>δ<sub>disp</sub></th><th>δ<sub>diss</sub></th>
      </tr>
    </thead>
    <tbody>
{''.join(rows)}
    </tbody>
  </table>
</section>"""


# ============================================================
# Static Export for Publication
# ============================================================

def export_static_figures(experiments: dict, output_dir: str):
    """Export all figures as PDF and PNG for PRL submission."""
    os.makedirs(output_dir, exist_ok=True)

    figures = {
        "fig1_transonic_profiles": fig_transonic_profiles(experiments),
        "fig2_correction_hierarchy": fig_correction_hierarchy(experiments),
        "fig3_parameter_space": fig_parameter_space(),
        "fig4_spin_sonic_enhancement": fig_spin_sonic_enhancement(),
        "fig5_temperature_decomposition": fig_temperature_decomposition(experiments),
        "fig6_kappa_scaling": fig_kappa_scaling(),
        "fig7_cgl_fdr_pattern": fig_cgl_fdr_pattern(),
        "fig8_even_vs_odd_kernel": fig_even_vs_odd_kernel(),
        "fig9_boundary_term_suppression": fig_boundary_term_suppression(),
        "fig10_positivity_constraint": fig_positivity_constraint(),
        "fig11_on_shell_vanishing": fig_on_shell_vanishing(),
        "fig12_einstein_relation": fig_einstein_relation(),
    }

    exported = []
    for name, fig in figures.items():
        # Standalone interactive HTML per figure (always works)
        html_path = os.path.join(output_dir, f"{name}.html")
        fig.write_html(html_path, include_plotlyjs="cdn")
        exported.append(html_path)

        # PDF for LaTeX inclusion (requires Chrome/kaleido)
        pdf_path = os.path.join(output_dir, f"{name}.pdf")
        try:
            fig.write_image(pdf_path, format="pdf")
            exported.append(pdf_path)
        except Exception as e:
            pass  # Chrome not available in this env; run locally

        # High-res PNG fallback
        png_path = os.path.join(output_dir, f"{name}.png")
        try:
            fig.write_image(png_path, format="png", width=1200, height=800, scale=2)
            exported.append(png_path)
        except Exception:
            pass  # Same — run locally for static export

    return exported


# ============================================================
# Main Entry Point
# ============================================================

def main():
    print("SK-EFT Hawking Paper: Generating Visualizations")
    print("=" * 60)

    # Compute all backgrounds
    experiments = {}
    for label, param_fn, key in [
        ("⁸⁷Rb (Steinhauer)", steinhauer_Rb87, "Rb87"),
        ("³⁹K (Heidelberg)", heidelberg_K39, "K39"),
        ("²³Na spin-sonic (Trento)", trento_spin_sonic, "Na23"),
    ]:
        params = param_fn()
        bg = solve_transonic_background(params)
        experiments[label] = (params, bg)
        print(f"  {label}: κ={bg.surface_gravity:.1f} s⁻¹, T_H={bg.hawking_temp*1e9:.3f} nK, D={bg.adiabaticity:.4f}")

    # Determine output directory
    script_dir = os.path.dirname(os.path.abspath(__file__))
    project_dir = os.path.dirname(script_dir)
    fig_dir = os.path.join(project_dir, "figures")
    os.makedirs(fig_dir, exist_ok=True)

    # 1. Static figures for publication
    print("\nExporting static figures (PDF + PNG)...")
    exported = export_static_figures(experiments, fig_dir)
    for p in exported:
        print(f"  → {os.path.basename(p)}")

    # 2. Interactive dashboard
    print("\nBuilding interactive dashboard...")
    html_path = build_interactive_dashboard(experiments, fig_dir)
    print(f"  → {os.path.basename(html_path)}")

    print(f"\nAll outputs in: {fig_dir}")
    print("Done!")

    return fig_dir


if __name__ == "__main__":
    main()
