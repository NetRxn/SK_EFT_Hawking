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


def _find_experiment(experiments: dict, keyword: str):
    """Find an experiment entry by keyword substring match.

    The experiments dict uses keys like '⁸⁷Rb (Steinhauer)' while
    Phase 3 functions reference by short name 'Steinhauer'.
    """
    for key in experiments:
        if keyword.lower() in key.lower():
            return experiments[key]
    raise KeyError(f"No experiment matching '{keyword}' in {list(experiments.keys())}")


def _resolve_platform_color(name: str) -> str:
    """Resolve a platform display name to its COLORS palette entry.

    Handles both short names ('Steinhauer') and full display names
    ('⁸⁷Rb (Steinhauer)') by substring matching.
    """
    _color_map = {
        "Steinhauer": "Steinhauer", "Rb": "Rb87",
        "Heidelberg": "Heidelberg", "K": "K39",
        "Trento": "Trento", "Na": "Na23",
    }
    for keyword, color_key in _color_map.items():
        if keyword in name:
            return COLORS[color_key]
    return COLORS["horizon"]


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

    Row 1: All components (T_H dominates, corrections invisible).
    Row 2: Corrections only (δ_disp, δ_diss, δ_cross) at zoomed scale.
    """
    n_exp = len(experiments)
    row1_titles = [f"<b>{name}</b>" for name in experiments.keys()]
    row2_titles = [f"<b>{name} (corrections only)</b>" for name in experiments.keys()]
    fig = make_subplots(
        rows=2, cols=n_exp,
        subplot_titles=row1_titles + row2_titles,
        shared_yaxes=True,
        vertical_spacing=0.15,
        row_heights=[0.45, 0.55],
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

        # Row 1: all components including T_H
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

        # Row 2: corrections only (without T_H) at zoomed scale
        corr_components = [
            ("δ_disp", T_H * corr["delta_disp"], COLORS["dispersive"]),
            ("δ_diss", T_H * corr["delta_diss"], COLORS["dissipative"]),
            ("δ_cross", T_H * corr["delta_cross"], COLORS["cross"]),
        ]

        corr_labels = [c[0] for c in corr_components]
        corr_values = [c[1] for c in corr_components]
        corr_colors = [c[2] for c in corr_components]

        fig.add_trace(go.Bar(
            x=corr_labels, y=corr_values,
            marker_color=corr_colors,
            marker_line=dict(width=1, color="black"),
            text=[f"{v:.2e} nK" for v in corr_values],
            textposition="outside",
            textfont=dict(size=9),
            showlegend=False,
            hovertemplate="%{x}: %{y:.4e} nK<extra></extra>",
        ), row=2, col=col)

    fig.update_yaxes(type="log", title_text="Temperature contribution (nK)", row=1, col=1)
    fig.update_yaxes(type="log", title_text="Correction terms (nK)", row=2, col=1)

    apply_layout(fig,
        height=700, width=900,
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


# ============================================================
# Phase 3 Wave 1: Third-Order + Gauge Erasure Figures
# ============================================================

def fig_parity_alternation(stakeholder: bool = False) -> go.Figure:
    """Parity alternation structure of the EFT derivative expansion.

    If stakeholder=False: heatmap of monomial structure at each EFT order
    1-8 (rows=order, cols=m value, colored by universal/flow-only/killed).
    If stakeholder=True: bar chart showing count per order, colored
    green=universal, red=flow-only.

    Uses the parity_alternation theorem from enumeration.py and the
    count_coefficients formula from formulas.py.
    """
    from src.second_order.enumeration import parity_alternation
    from src.core.formulas import count_coefficients

    if stakeholder:
        orders = list(range(1, 9))
        counts_universal = []
        counts_flow = []
        for N in orders:
            pa = parity_alternation(N)
            if pa['requires_parity_breaking']:
                counts_universal.append(0)
                counts_flow.append(pa['count_no_parity'])
            else:
                counts_universal.append(pa['count_no_parity'])
                counts_flow.append(0)

        fig = go.Figure()

        fig.add_trace(go.Bar(
            x=orders, y=counts_universal,
            name="Universal (parity-preserving)",
            marker_color=COLORS["Steinhauer"],  # blue (color-blind accessible)
            marker_line=dict(width=1, color="black"),
            text=[str(c) if c > 0 else "" for c in counts_universal],
            textposition="outside",
        ))
        fig.add_trace(go.Bar(
            x=orders, y=counts_flow,
            name="Flow-only (parity-breaking)",
            marker_color=COLORS["Trento"],  # amber (color-blind accessible)
            marker_line=dict(width=1, color="black"),
            text=[str(c) if c > 0 else "" for c in counts_flow],
            textposition="outside",
        ))

        # Overlay counting formula
        formula_vals = [count_coefficients(N) for N in orders]
        fig.add_trace(go.Scatter(
            x=orders, y=formula_vals,
            mode="markers+lines",
            name="count(N) = floor((N+1)/2) + 1",
            line=dict(color=COLORS["horizon"], width=2, dash="dash"),
            marker=dict(size=10, symbol="diamond", color=COLORS["horizon"]),
        ))

        fig.update_xaxes(title_text="EFT Order N", dtick=1)
        fig.update_yaxes(title_text="Transport Coefficients")

        apply_layout(fig,
            height=450, width=700,
            title=dict(text="<b>Parity Alternation: Universal vs Flow-Only Corrections</b>",
                       font=TITLE_FONT),
            barmode="stack",
            legend=dict(x=0.02, y=0.98, bgcolor="rgba(255,255,255,0.9)"),
        )
    else:
        orders = list(range(1, 9))
        # Build heatmap data: rows=order, cols=m value (0,2,4,...,8)
        max_m = 8
        m_values = list(range(0, max_m + 1, 2))  # even m only

        z_data = []
        hover_text = []
        for N in orders:
            pa = parity_alternation(N)
            L = N + 1
            row = []
            hover_row = []
            for m in m_values:
                n = L - m
                if n < 0 or m > L:
                    row.append(0)  # outside range
                    hover_row.append(f"N={N}, m={m}: outside range")
                elif m % 2 != 0:
                    row.append(0)  # killed by T-reversal (shouldn't happen since m_values are even)
                    hover_row.append(f"N={N}, m={m}: killed by T-reversal")
                elif pa['requires_parity_breaking'] and n % 2 != 0:
                    row.append(2)  # flow-only (odd n, requires parity breaking)
                    hover_row.append(f"N={N}, m={m}, n={n}: flow-only (odd n)")
                elif not pa['requires_parity_breaking'] and n % 2 == 0:
                    row.append(1)  # universal (even n)
                    hover_row.append(f"N={N}, m={m}, n={n}: universal (even n)")
                else:
                    row.append(0)
                    hover_row.append(f"N={N}, m={m}, n={n}: not at this level")
            z_data.append(row)
            hover_text.append(hover_row)

        # Custom colorscale: 0=grey (empty), 1=blue (universal), 2=amber (flow-only)
        # Using blue/amber instead of green/red for color-blind accessibility
        colorscale = [
            [0.0, "#E0E0E0"],    # empty/killed
            [0.5, COLORS["Steinhauer"]],  # universal (blue)
            [1.0, COLORS["Trento"]],  # flow-only (amber)
        ]

        fig = go.Figure(data=go.Heatmap(
            z=z_data,
            x=[f"m={m}" for m in m_values],
            y=[f"N={N}" for N in orders],
            hovertext=hover_text,
            hoverinfo="text",
            colorscale=colorscale,
            showscale=False,
            zmin=0, zmax=2,
        ))

        # Annotations for cell values
        for i, N in enumerate(orders):
            L = N + 1
            for j, m in enumerate(m_values):
                n = L - m
                if n >= 0 and m <= L:
                    label = f"({m},{n})"
                    fig.add_annotation(
                        x=j, y=i, text=label,
                        font=dict(size=10, color="white" if z_data[i][j] > 0 else "grey"),
                        showarrow=False,
                    )

        fig.update_xaxes(title_text="Time derivatives m (even)")
        fig.update_yaxes(title_text="EFT Order N")

        apply_layout(fig,
            height=500, width=650,
            title=dict(text="<b>Parity Alternation: Monomial Structure at Each EFT Order</b>",
                       font=TITLE_FONT),
        )

    return fig


def fig_damping_rate_third_order(
    experiments: dict[str, tuple[BECParameters, TransonicBackground]],
) -> go.Figure:
    """Damping rate Gamma(k)/kappa vs k/k_H for Steinhauer at orders 1, 2, and 3.

    Shows three curves: order 1 only, through order 2, through order 3,
    illustrating the convergence of the EFT derivative expansion.
    """
    from src.core.formulas import damping_rate as dr
    from src.core.formulas import beliaev_transport_coefficients

    # Use Steinhauer parameters
    name = "Steinhauer"
    params, bg = _find_experiment(experiments, name)

    n_1D = params.density_upstream
    a_s = params.scattering_length
    cs = params.sound_speed_upstream
    kappa = bg.surface_gravity
    xi = params.healing_length

    coeffs = beliaev_transport_coefficients(n_1D, a_s, kappa, cs, xi)
    g1 = coeffs['gamma_1']
    g2 = coeffs['gamma_2']
    g21 = coeffs['gamma_2_1']
    g22 = coeffs['gamma_2_2']

    # Third-order coefficients: scale ~ gamma_dim * xi^2 / c_s^2
    Gamma_Bel = coeffs['Gamma_Bel']
    g31 = Gamma_Bel * (xi / cs)**2 / (2 * coeffs['k_H']**4)
    g32 = -g31
    g33 = g31 * 0.5  # subdominant

    k_H = kappa / cs
    k_range = np.linspace(0.1 * k_H, 5.0 * k_H, 300)
    omega_range = cs * k_range  # acoustic dispersion

    Gamma_1 = np.array([dr(k, cs * k, cs, g1, g2) for k in k_range]) / kappa
    Gamma_12 = np.array([dr(k, cs * k, cs, g1, g2, g21, g22) for k in k_range]) / kappa
    Gamma_123 = np.array([dr(k, cs * k, cs, g1, g2, g21, g22, g31, g32, g33) for k in k_range]) / kappa

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=("Damping rate |Gamma(k)|/kappa", "Fractional correction vs order 1"),
        horizontal_spacing=0.15,
    )

    fig.add_trace(go.Scatter(
        x=k_range / k_H, y=np.abs(Gamma_1),
        mode="lines", name="Order 1 only",
        line=dict(color=COLORS["Steinhauer"], width=2, dash="dash"),
    ), row=1, col=1)
    fig.add_trace(go.Scatter(
        x=k_range / k_H, y=np.abs(Gamma_12),
        mode="lines", name="Through order 2",
        line=dict(color=COLORS["Heidelberg"], width=2, dash="dot"),
    ), row=1, col=1)
    fig.add_trace(go.Scatter(
        x=k_range / k_H, y=np.abs(Gamma_123),
        mode="lines", name="Through order 3",
        line=dict(color=COLORS["dissipative"], width=3),
    ), row=1, col=1)

    # Right panel: fractional residuals relative to order 1
    safe_G1 = np.where(np.abs(Gamma_1) > 1e-30, Gamma_1, 1e-30)
    resid_2 = np.abs((Gamma_12 - Gamma_1) / safe_G1)
    resid_3 = np.abs((Gamma_123 - Gamma_1) / safe_G1)

    fig.add_trace(go.Scatter(
        x=k_range / k_H, y=resid_2,
        mode="lines", name="|delta Gamma/Gamma| order 2",
        line=dict(color=COLORS["Heidelberg"], width=2),
        showlegend=False,
    ), row=1, col=2)
    fig.add_trace(go.Scatter(
        x=k_range / k_H, y=resid_3,
        mode="lines", name="|delta Gamma/Gamma| order 3",
        line=dict(color=COLORS["dissipative"], width=2),
        showlegend=False,
    ), row=1, col=2)

    for col in [1, 2]:
        fig.add_vline(x=1.0, line=dict(color=COLORS["horizon"], width=1, dash="dot"),
                      row=1, col=col)

    fig.update_xaxes(title_text="k / k<sub>H</sub>", row=1, col=1)
    fig.update_xaxes(title_text="k / k<sub>H</sub>", row=1, col=2)
    fig.update_yaxes(title_text="|Gamma(k)| / kappa", type="log", row=1, col=1)
    fig.update_yaxes(title_text="Fractional correction", type="log", row=1, col=2)

    apply_layout(fig,
        height=450, width=1000,
        title=dict(text="<b>Damping Rate: EFT Order Convergence (Steinhauer ⁸⁷Rb)</b>",
                   font=TITLE_FONT),
        legend=dict(x=0.02, y=0.98, bgcolor="rgba(255,255,255,0.9)"),
    )

    return fig


def fig_spectral_correction_comparison(
    experiments: dict[str, tuple[BECParameters, TransonicBackground]],
) -> go.Figure:
    """Side-by-side comparison of second-order (odd) and third-order (even) spectral corrections.

    Left panel: delta^(2)(omega) ~ omega^3 (odd in frequency).
    Right panel: delta^(3)(omega) ~ omega^4 (even in frequency).
    Demonstrates the parity alternation in the spectral domain.
    """
    from src.core.formulas import second_order_correction, third_order_correction
    from src.core.formulas import beliaev_transport_coefficients

    # Use Steinhauer as representative
    name = "Steinhauer"
    params, bg = _find_experiment(experiments, name)

    n_1D = params.density_upstream
    a_s = params.scattering_length
    cs = params.sound_speed_upstream
    kappa = bg.surface_gravity
    xi = params.healing_length

    coeffs = beliaev_transport_coefficients(n_1D, a_s, kappa, cs, xi)
    g21 = coeffs['gamma_2_1']
    g22 = coeffs['gamma_2_2']

    Gamma_Bel = coeffs['Gamma_Bel']
    k_H = coeffs['k_H']
    g31 = Gamma_Bel * (xi / cs)**2 / (2 * k_H**4)
    g32 = -g31
    g33 = g31 * 0.5

    omega_range = np.linspace(-5 * kappa, 5 * kappa, 500)

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            "<b>(a)</b> delta<sup>(2)</sup>(omega) ~ omega<sup>3</sup> (odd)",
            "<b>(b)</b> delta<sup>(3)</sup>(omega) ~ omega<sup>4</sup> (even)",
        ),
        horizontal_spacing=0.15,
    )

    # Second-order correction: evaluate OFF-shell (k = 2*omega/c_s) to show odd symmetry.
    # On the acoustic shell (k = omega/c_s), positivity constraint gamma_2_2 = -gamma_2_1
    # makes delta^(2) vanish identically — that's correct physics but invisible in a plot.
    k_off = 2.0  # off-shell factor: k = k_off * omega/c_s
    delta_2 = np.array([
        second_order_correction(k_off * abs(w) / cs, w, cs, g21, g22, kappa)
        for w in omega_range
    ])
    fig.add_trace(go.Scatter(
        x=omega_range / kappa, y=delta_2,
        mode="lines", name="delta<sup>(2)</sup> (odd, off-shell)",
        line=dict(color=COLORS["Heidelberg"], width=2.5),
        showlegend=True,
    ), row=1, col=1)
    fig.add_hline(y=0, line=dict(color="rgba(0,0,0,0.3)", width=0.5), row=1, col=1)
    fig.add_annotation(
        x=0.25, y=0.15, xref="paper", yref="paper",
        text="Evaluated off-shell (k=2omega/c_s).<br>On-shell: vanishes by positivity.",
        showarrow=False, font=dict(size=9, color="#888"),
    )

    # Third-order correction
    delta_3 = np.array([
        third_order_correction(abs(w) / cs, abs(w), cs, g31, g32, g33, kappa)
        for w in omega_range
    ])
    fig.add_trace(go.Scatter(
        x=omega_range / kappa, y=delta_3,
        mode="lines", name="delta<sup>(3)</sup> (even)",
        line=dict(color=COLORS["dissipative"], width=2.5),
        showlegend=True,
    ), row=1, col=2)
    fig.add_hline(y=0, line=dict(color="rgba(0,0,0,0.3)", width=0.5), row=1, col=2)

    fig.update_xaxes(title_text="omega / kappa", row=1, col=1)
    fig.update_xaxes(title_text="omega / kappa", row=1, col=2)
    fig.update_yaxes(title_text="delta<sup>(2)</sup>", row=1, col=1)
    fig.update_yaxes(title_text="delta<sup>(3)</sup>", row=1, col=2)

    apply_layout(fig,
        height=400, width=900,
        title=dict(text="<b>Spectral Correction Parity: Odd (N=2) vs Even (N=3)</b>",
                   font=TITLE_FONT),
        legend=dict(x=0.02, y=0.98, bgcolor="rgba(255,255,255,0.9)"),
    )

    for ann in fig.layout.annotations:
        ann.font = dict(size=12, family=FONT["family"])

    return fig


def fig_kappa_crossing_phase3(
    experiments: dict[str, tuple[BECParameters, TransonicBackground]],
) -> go.Figure:
    """Log-log plot of |delta_disp| and delta_diss vs kappa for all 3 platforms.

    Shows the crossing point where dispersive and dissipative corrections
    are equal, with crossing diamonds marking each platform's crossing kappa.
    """
    from src.core.formulas import dispersive_correction, beliaev_transport_coefficients

    kappa_range = np.logspace(1, 5, 300)

    fig = go.Figure()

    for name, (params, bg) in experiments.items():
        cs = params.sound_speed_upstream
        xi = params.healing_length
        n_1D = params.density_upstream
        a_s = params.scattering_length
        color = _resolve_platform_color(name)

        # Dispersive correction: |delta_disp| = (pi/6) * D^2
        D_arr = kappa_range * xi / cs
        delta_disp_arr = np.abs(dispersive_correction(D_arr))

        # Dissipative correction: delta_diss = Gamma_Bel / kappa
        # Gamma_Bel = sqrt(n*a^3) * kappa^2 / c_s
        na3_half = np.sqrt(n_1D * a_s**3)
        Gamma_Bel = na3_half * kappa_range**2 / cs
        delta_diss_arr = Gamma_Bel / kappa_range

        fig.add_trace(go.Scatter(
            x=kappa_range, y=delta_disp_arr,
            mode="lines", name=f"|delta_disp| ({name})",
            line=dict(color=color, width=2, dash="dash"),
            legendgroup=name,
            hovertemplate="kappa=%{x:.0f}<br>|delta_disp|=%{y:.2e}<extra></extra>",
        ))
        fig.add_trace(go.Scatter(
            x=kappa_range, y=delta_diss_arr,
            mode="lines", name=f"delta_diss ({name})",
            line=dict(color=color, width=2),
            legendgroup=name,
            hovertemplate="kappa=%{x:.0f}<br>delta_diss=%{y:.2e}<extra></extra>",
        ))

        # Find crossing point
        log_diff = np.log10(delta_disp_arr) - np.log10(delta_diss_arr)
        sign_changes = np.where(np.diff(np.sign(log_diff)))[0]
        if len(sign_changes) > 0:
            idx = sign_changes[0]
            cross_kappa = kappa_range[idx]
            cross_val = delta_disp_arr[idx]
            fig.add_trace(go.Scatter(
                x=[cross_kappa], y=[cross_val],
                mode="markers",
                marker=dict(size=14, color=color, symbol="diamond",
                           line=dict(width=2, color="black")),
                name=f"Crossing ({name})",
                legendgroup=name,
                showlegend=False,
                hovertemplate=f"Crossing ({name})<br>kappa*={cross_kappa:.0f}<extra></extra>",
            ))

    fig.update_xaxes(type="log", title_text="Surface gravity κ (s<sup>-1</sup>)")
    fig.update_yaxes(type="log", title_text="|Correction|")

    apply_layout(fig,
        height=500, width=750,
        title=dict(text="<b>kappa Crossing: |delta_disp| vs delta_diss (All Platforms)</b>",
                   font=TITLE_FONT),
        legend=dict(x=0.55, y=0.98, bgcolor="rgba(255,255,255,0.9)"),
    )

    return fig


def fig_spin_sonic_enhancement_phase3(
    experiments: dict[str, tuple[BECParameters, TransonicBackground]],
) -> go.Figure:
    """Enhancement factor (c_density/c_spin)^2 vs velocity ratio with sensitivity thresholds.

    Shows how the spin-sonic channel amplifies the dissipative correction
    for all three platforms, with experimental sensitivity threshold lines.
    """
    from src.core.formulas import beliaev_transport_coefficients

    c_ratio = np.logspace(0, 3, 300)
    enhancement = c_ratio**2

    fig = go.Figure()

    for name, (params, bg) in experiments.items():
        cs = params.sound_speed_upstream
        kappa = bg.surface_gravity
        xi = params.healing_length
        n_1D = params.density_upstream
        a_s = params.scattering_length
        color = _resolve_platform_color(name)

        coeffs = beliaev_transport_coefficients(n_1D, a_s, kappa, cs, xi)
        Gamma_Bel = coeffs['Gamma_Bel']
        delta_diss_base = Gamma_Bel / kappa

        delta_diss_enhanced = delta_diss_base * enhancement

        fig.add_trace(go.Scatter(
            x=c_ratio, y=delta_diss_enhanced,
            mode="lines", name=f"{name}",
            line=dict(color=color, width=2.5),
            hovertemplate=f"{name}<br>c_dens/c_spin=%{{x:.0f}}<br>delta_diss=%{{y:.2e}}<extra></extra>",
        ))

    # Sensitivity thresholds
    for val, label in [(0.1, "10% (current)"),
                        (0.01, "1% (near-term)"),
                        (0.001, "0.1% (projected)")]:
        fig.add_hline(y=val, line=dict(color=COLORS["sensitivity"], width=1.5, dash="dash"),
                      annotation_text=label, annotation_position="right",
                      annotation_font=dict(size=10, color="#888"))

    fig.update_xaxes(type="log",
                     title_text="Velocity ratio c<sub>density</sub> / c<sub>spin</sub>")
    fig.update_yaxes(type="log", title_text="|δ<sub>diss</sub>|",
                     range=[-8, 0])

    apply_layout(fig,
        height=450, width=700,
        title=dict(text="<b>Spin-Sonic Enhancement: All Platforms</b>",
                   font=TITLE_FONT),
        legend=dict(x=0.02, y=0.98, bgcolor="rgba(255,255,255,0.9)"),
    )

    return fig


def fig_bogoliubov_connection(
    experiments: dict[str, tuple[BECParameters, TransonicBackground]],
) -> go.Figure:
    """Acoustic vs Bogoliubov dispersion relation and k^4 deviation.

    Side-by-side: left shows omega(k) for acoustic (linear) and
    Bogoliubov (superluminal), right shows the fractional k^4 deviation.
    """
    from src.core.constants import HBAR

    # Use Steinhauer as representative
    name = "Steinhauer"
    params, bg = _find_experiment(experiments, name)

    cs = params.sound_speed_upstream
    xi = params.healing_length
    mass = params.mass

    k_range = np.linspace(0, 5.0 / xi, 400)

    # Acoustic: omega = c_s * k
    omega_acoustic = cs * k_range

    # Bogoliubov: omega = c_s * k * sqrt(1 + (k*xi)^2 / 2)
    # More precisely: omega^2 = c_s^2 * k^2 + (hbar * k^2 / (2*m))^2
    omega_bog = cs * k_range * np.sqrt(1 + (k_range * xi)**2 / 4)

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            "<b>(a)</b> Dispersion relation",
            "<b>(b)</b> k<sup>4</sup> deviation",
        ),
        horizontal_spacing=0.15,
    )

    # Left: Dispersion relations
    fig.add_trace(go.Scatter(
        x=k_range * xi, y=omega_acoustic / (cs / xi),
        mode="lines", name="Acoustic: omega = c<sub>s</sub>k",
        line=dict(color=COLORS["dispersive"], width=2, dash="dash"),
    ), row=1, col=1)
    fig.add_trace(go.Scatter(
        x=k_range * xi, y=omega_bog / (cs / xi),
        mode="lines", name="Bogoliubov",
        line=dict(color=COLORS["Steinhauer"], width=2.5),
    ), row=1, col=1)

    # Right: Fractional deviation
    with np.errstate(divide='ignore', invalid='ignore'):
        deviation = np.where(
            omega_acoustic > 0,
            (omega_bog - omega_acoustic) / omega_acoustic,
            0.0,
        )

    fig.add_trace(go.Scatter(
        x=k_range * xi, y=deviation,
        mode="lines", name="(omega_Bog - omega_ac) / omega_ac",
        line=dict(color=COLORS["dissipative"], width=2.5),
        showlegend=True,
    ), row=1, col=2)

    # Overlay k^4 scaling guide
    k4_guide = (k_range * xi)**2 / 8  # leading correction ~ (k*xi)^2/4 at small k
    fig.add_trace(go.Scatter(
        x=k_range * xi, y=k4_guide,
        mode="lines", name="~ (k xi)<sup>2</sup>/8 guide",
        line=dict(color=COLORS["cross"], width=1.5, dash="dot"),
        showlegend=True,
    ), row=1, col=2)

    fig.update_xaxes(title_text="k xi", row=1, col=1)
    fig.update_xaxes(title_text="k xi", row=1, col=2)
    fig.update_yaxes(title_text="omega / (c<sub>s</sub>/xi)", row=1, col=1)
    fig.update_yaxes(title_text="Fractional deviation", row=1, col=2)

    apply_layout(fig,
        height=400, width=900,
        title=dict(text="<b>Bogoliubov vs Acoustic Dispersion: UV Connection to EFT</b>",
                   font=TITLE_FONT),
        legend=dict(x=0.02, y=0.98, bgcolor="rgba(255,255,255,0.9)"),
    )

    for ann in fig.layout.annotations:
        ann.font = dict(size=12, family=FONT["family"])

    return fig


def fig_sm_scorecard() -> go.Figure:
    """Standard Model gauge group bar chart: SU(3)/SU(2)/U(1), colored by survives/erased.

    Shows the gauge erasure theorem applied to each factor of the SM gauge group,
    with green for surviving (U(1)) and red for erased (SU(3), SU(2)).
    """
    from src.gauge_erasure.erasure_theorem import standard_model_analysis

    sm = standard_model_analysis()

    groups = list(sm.keys())
    dims = [sm[g].group.dim for g in groups]
    survives = [sm[g].survives for g in groups]
    colors = [COLORS["dispersive"] if s else COLORS["dissipative"] for s in survives]
    labels = ["SURVIVES" if s else "ERASED" for s in survives]

    fig = go.Figure()

    fig.add_trace(go.Bar(
        x=groups, y=dims,
        marker_color=colors,
        marker_line=dict(width=2, color="black"),
        text=labels,
        textposition="outside",
        textfont=dict(size=12, family=FONT["family"]),
        hovertemplate="%{x}<br>dim=%{y}<br>%{text}<extra></extra>",
    ))

    # Add center subgroup annotations
    for i, g in enumerate(groups):
        center = sm[g].group.center
        fig.add_annotation(
            x=i, y=dims[i] / 2,
            text=f"Center: {center}",
            font=dict(size=10, color="white"),
            showarrow=False,
        )

    fig.update_xaxes(title_text="SM Gauge Group Factor")
    fig.update_yaxes(title_text="Group Dimension")

    apply_layout(fig,
        height=450, width=550,
        title=dict(text="<b>Standard Model Gauge Erasure Scorecard</b>",
                   font=TITLE_FONT),
    )

    return fig


def fig_erasure_survey() -> go.Figure:
    """Survey bar chart of gauge erasure across SU(N), SO(N), and U(1) groups.

    Shows which gauge groups survive (green) vs are erased (red) upon
    hydrodynamization, demonstrating the universality of the theorem.
    """
    from src.gauge_erasure.erasure_theorem import (
        gauge_erasure_analysis, su, so, u1,
    )

    # Build survey data
    groups = []
    names = []
    survive_flags = []
    dimensions = []

    # SU(N) series
    for N in range(2, 11):
        g = su(N)
        result = gauge_erasure_analysis(g)
        groups.append(g)
        names.append(f"SU({N})")
        survive_flags.append(result.survives)
        dimensions.append(g.dim)

    # SO(N) series
    for N in range(3, 11):
        g = so(N)
        result = gauge_erasure_analysis(g)
        groups.append(g)
        names.append(f"SO({N})")
        survive_flags.append(result.survives)
        dimensions.append(g.dim)

    # U(1)
    g = u1()
    result = gauge_erasure_analysis(g)
    groups.append(g)
    names.append("U(1)")
    survive_flags.append(result.survives)
    dimensions.append(g.dim)

    colors = [COLORS["dispersive"] if s else COLORS["dissipative"] for s in survive_flags]
    labels = ["Survives" if s else "Erased" for s in survive_flags]

    fig = go.Figure()

    fig.add_trace(go.Bar(
        x=names, y=dimensions,
        marker_color=colors,
        marker_line=dict(width=1, color="black"),
        text=labels,
        textposition="outside",
        textfont=dict(size=9),
        hovertemplate="%{x}<br>dim=%{y}<br>%{text}<extra></extra>",
    ))

    # Visual dividers between group families
    fig.add_vline(x=8.5, line=dict(color=COLORS["cross"], width=1, dash="dot"),
                  annotation_text="SU(N) | SO(N)", annotation_position="top",
                  annotation_font=dict(size=10, color=COLORS["cross"]))
    fig.add_vline(x=16.5, line=dict(color=COLORS["cross"], width=1, dash="dot"),
                  annotation_text="SO(N) | U(1)", annotation_position="top",
                  annotation_font=dict(size=10, color=COLORS["cross"]))

    fig.update_yaxes(title_text="Group Dimension")

    apply_layout(fig,
        height=500, width=900,
        title=dict(text="<b>Gauge Erasure Survey: Which Gauge Groups Survive Hydrodynamization?</b>",
                   font=TITLE_FONT),
    )

    # Set tickangle after apply_layout to ensure it is not overridden
    fig.update_xaxes(title_text="Gauge Group", tickangle=-45)

    return fig


# ============================================================
# Phase 3 Wave 2: WKB Connection Figures
# ============================================================

def fig_complex_turning_point() -> go.Figure:
    """Imaginary part of the WKB turning point vs omega/T_H for all 3 platforms.

    Shows how the turning point shifts into the complex plane as a function
    of frequency, driven by the SK-EFT damping rate.
    """
    from src.wkb.connection_formula import compute_complex_turning_point
    from src.wkb.spectrum import steinhauer_platform, heidelberg_platform, trento_platform

    platforms = [
        ("Steinhauer", steinhauer_platform(), COLORS["Steinhauer"]),
        ("Heidelberg", heidelberg_platform(), COLORS["Heidelberg"]),
        ("Trento", trento_platform(), COLORS["Trento"]),
    ]

    fig = go.Figure()

    for name, p, color in platforms:
        T_H = p.T_H
        omega_arr = np.linspace(0.1 * T_H, 6.0 * T_H, 200)

        x_imag_arr = []
        for omega in omega_arr:
            tp = compute_complex_turning_point(
                omega, p.kappa, p.c_s, p.xi,
                p.gamma_1, p.gamma_2,
                p.gamma_2_1, p.gamma_2_2,
            )
            x_imag_arr.append(tp.x_imag)

        fig.add_trace(go.Scatter(
            x=omega_arr / T_H, y=x_imag_arr,
            mode="lines", name=name,
            line=dict(color=color, width=2.5),
            hovertemplate=f"{name}<br>omega/T_H=%{{x:.2f}}<br>x_imag=%{{y:.2e}}<extra></extra>",
        ))

    fig.update_xaxes(title_text="ω / T<sub>H</sub>")
    fig.update_yaxes(title_text="δx<sub>imag</sub> (turning point shift)",
                     type="log")

    apply_layout(fig,
        height=450, width=700,
        title=dict(text="<b>Complex Turning Point: Imaginary Shift vs Frequency</b>",
                   font=TITLE_FONT),
        legend=dict(x=0.02, y=0.98, bgcolor="rgba(255,255,255,0.9)"),
    )

    return fig


def fig_effective_surface_gravity() -> go.Figure:
    """Decomposition of kappa_eff/kappa into dispersive and dissipative contributions.

    Three-row subplot (one per platform) showing the frequency-dependent
    effective surface gravity and its correction decomposition.
    """
    from src.wkb.connection_formula import effective_surface_gravity as esg
    from src.wkb.spectrum import steinhauer_platform, heidelberg_platform, trento_platform

    platforms = [
        ("Steinhauer", steinhauer_platform(), COLORS["Steinhauer"]),
        ("Heidelberg", heidelberg_platform(), COLORS["Heidelberg"]),
        ("Trento", trento_platform(), COLORS["Trento"]),
    ]

    fig = make_subplots(
        rows=1, cols=3,
        subplot_titles=[f"<b>{name}</b>" for name, _, _ in platforms],
        shared_yaxes=True,
        horizontal_spacing=0.08,
    )

    for col, (name, p, color) in enumerate(platforms, 1):
        T_H = p.T_H
        omega_arr = np.linspace(0.1 * T_H, 6.0 * T_H, 200)

        delta_disp_arr = []
        delta_diss_arr = []
        keff_ratio_arr = []

        for omega in omega_arr:
            result = esg(
                omega, p.kappa, p.c_s, p.xi,
                p.gamma_1, p.gamma_2,
                p.gamma_2_1, p.gamma_2_2,
            )
            delta_disp_arr.append(abs(result.delta_disp))
            delta_diss_arr.append(result.delta_diss)
            keff_ratio_arr.append(result.kappa_eff / result.kappa)

        fig.add_trace(go.Scatter(
            x=omega_arr / T_H, y=delta_disp_arr,
            mode="lines", name=f"|delta_disp| ({name})",
            line=dict(color=COLORS["dispersive"], width=2),
            legendgroup="disp",
            showlegend=True,
        ), row=1, col=col)

        fig.add_trace(go.Scatter(
            x=omega_arr / T_H, y=delta_diss_arr,
            mode="lines", name=f"delta_diss ({name})",
            line=dict(color=COLORS["dissipative"], width=2),
            legendgroup="diss",
            showlegend=True,
        ), row=1, col=col)

        fig.update_xaxes(title_text="ω / T<sub>H</sub>", row=1, col=col)

    fig.update_yaxes(title_text="|Correction|", type="log", row=1, col=1)

    apply_layout(fig,
        height=400, width=1000,
        title=dict(text="<b>Effective Surface Gravity: Correction Decomposition</b>",
                   font=TITLE_FONT),
        legend=dict(x=0.02, y=0.98, bgcolor="rgba(255,255,255,0.9)"),
    )

    for ann in fig.layout.annotations:
        ann.font = dict(size=12, family=FONT["family"])

    return fig


def fig_decoherence_and_noise() -> go.Figure:
    """Combined plot: decoherence parameter and FDR noise floor vs omega/T_H.

    Shows delta_k and n_noise on a log scale for all 3 platforms, illustrating
    the interplay between unitarity deficit and mandatory noise.
    """
    from src.wkb.spectrum import steinhauer_platform, heidelberg_platform, trento_platform
    from src.core.formulas import damping_rate as dr
    from src.core.formulas import decoherence_parameter as dp
    from src.core.formulas import fdr_noise_floor as fnf

    platforms = [
        ("Steinhauer", steinhauer_platform(), COLORS["Steinhauer"]),
        ("Heidelberg", heidelberg_platform(), COLORS["Heidelberg"]),
        ("Trento", trento_platform(), COLORS["Trento"]),
    ]

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            "<b>(a)</b> Decoherence parameter delta_k",
            "<b>(b)</b> FDR noise floor n_noise",
        ),
        horizontal_spacing=0.12,
    )

    for name, p, color in platforms:
        T_H = p.T_H
        omega_arr = np.linspace(0.1 * T_H, 6.0 * T_H, 200)

        dk_arr = []
        noise_arr = []

        for omega in omega_arr:
            k_H = omega / p.c_s
            Gamma_H = dr(k_H, omega, p.c_s,
                         p.gamma_1, p.gamma_2,
                         p.gamma_2_1, p.gamma_2_2)
            dk = dp(Gamma_H, p.kappa)
            nf = fnf(dk)
            dk_arr.append(dk)
            noise_arr.append(nf)

        fig.add_trace(go.Scatter(
            x=omega_arr / T_H, y=dk_arr,
            mode="lines", name=name,
            line=dict(color=color, width=2.5),
            legendgroup=name,
            hovertemplate=f"{name}<br>omega/T_H=%{{x:.2f}}<br>dk=%{{y:.2e}}<extra></extra>",
        ), row=1, col=1)

        fig.add_trace(go.Scatter(
            x=omega_arr / T_H, y=noise_arr,
            mode="lines", name=name,
            line=dict(color=color, width=2.5),
            legendgroup=name,
            showlegend=False,
            hovertemplate=f"{name}<br>omega/T_H=%{{x:.2f}}<br>n_noise=%{{y:.2e}}<extra></extra>",
        ), row=1, col=2)

    fig.update_xaxes(title_text="ω / T<sub>H</sub>", row=1, col=1)
    fig.update_xaxes(title_text="ω / T<sub>H</sub>", row=1, col=2)
    fig.update_yaxes(title_text="delta<sub>k</sub>", type="log", row=1, col=1)
    fig.update_yaxes(title_text="n<sub>noise</sub>", type="log", row=1, col=2)

    apply_layout(fig,
        height=400, width=900,
        title=dict(text="<b>Decoherence and FDR Noise Floor: All Platforms</b>",
                   font=TITLE_FONT),
        legend=dict(x=0.02, y=0.98, bgcolor="rgba(255,255,255,0.9)"),
    )

    for ann in fig.layout.annotations:
        ann.font = dict(size=12, family=FONT["family"])

    return fig


def fig_hawking_spectrum_exact(stakeholder: bool = False) -> go.Figure:
    """Full Hawking spectrum with exact WKB corrections.

    If stakeholder=False: 3-row subplot (one per platform) showing
    n_total, n_Planck, and n_noise curves.
    If stakeholder=True: single overlay of all 3 platforms showing
    n_total vs n_Planck for a quick comparison.
    """
    from src.wkb.spectrum import (
        steinhauer_platform, heidelberg_platform, trento_platform,
        compute_spectrum,
    )

    platforms = [
        ("Steinhauer", steinhauer_platform(), COLORS["Steinhauer"]),
        ("Heidelberg", heidelberg_platform(), COLORS["Heidelberg"]),
        ("Trento", trento_platform(), COLORS["Trento"]),
    ]

    if stakeholder:
        fig = go.Figure()

        for name, p, color in platforms:
            spectrum = compute_spectrum(p, omega_min=0.1, omega_max_factor=5.0, n_points=80)
            T_H = spectrum.T_H

            fig.add_trace(go.Scatter(
                x=spectrum.omega_array / T_H, y=spectrum.n_total_array,
                mode="lines", name=f"n_total ({name})",
                line=dict(color=color, width=2.5),
                hovertemplate=f"{name}<br>omega/T_H=%{{x:.2f}}<br>n=%{{y:.4f}}<extra></extra>",
            ))
            fig.add_trace(go.Scatter(
                x=spectrum.omega_array / T_H, y=spectrum.n_planck_array,
                mode="lines", name=f"n_Planck ({name})",
                line=dict(color=color, width=1.5, dash="dot"),
                showlegend=False,
            ))

        fig.update_xaxes(title_text="ω / T<sub>H</sub>")
        fig.update_yaxes(title_text="Occupation number n(omega)", type="log")

        apply_layout(fig,
            height=500, width=750,
            title=dict(text="<b>Hawking Spectrum: All Platforms (Exact WKB)</b>",
                       font=TITLE_FONT),
            legend=dict(x=0.55, y=0.98, bgcolor="rgba(255,255,255,0.9)"),
        )
    else:
        fig = make_subplots(
            rows=3, cols=1,
            shared_xaxes=True,
            vertical_spacing=0.08,
            subplot_titles=[f"<b>{name}</b>" for name, _, _ in platforms],
        )

        for row, (name, p, color) in enumerate(platforms, 1):
            spectrum = compute_spectrum(p, omega_min=0.1, omega_max_factor=5.0, n_points=80)
            T_H = spectrum.T_H

            n_noise_arr = np.array([pt.n_noise for pt in spectrum.points])

            fig.add_trace(go.Scatter(
                x=spectrum.omega_array / T_H, y=spectrum.n_total_array,
                mode="lines", name="n<sub>total</sub>",
                line=dict(color=color, width=2.5),
                legendgroup="total",
                showlegend=(row == 1),
            ), row=row, col=1)

            fig.add_trace(go.Scatter(
                x=spectrum.omega_array / T_H, y=spectrum.n_planck_array,
                mode="lines", name="n<sub>Planck</sub>",
                line=dict(color=COLORS["horizon"], width=1.5, dash="dash"),
                legendgroup="planck",
                showlegend=(row == 1),
            ), row=row, col=1)

            fig.add_trace(go.Scatter(
                x=spectrum.omega_array / T_H, y=n_noise_arr,
                mode="lines", name="n<sub>noise</sub>",
                line=dict(color=COLORS["noise"], width=1.5, dash="dot"),
                legendgroup="noise",
                showlegend=(row == 1),
            ), row=row, col=1)

            fig.update_yaxes(type="log", row=row, col=1)

        for row in range(1, 4):
            fig.update_xaxes(title_text="ω / T<sub>H</sub>", row=row, col=1)
        fig.update_yaxes(title_text="n(ω)", row=2, col=1)

        apply_layout(fig,
            height=800, width=700,
            title=dict(text="<b>Hawking Spectrum: Exact WKB with Decoherence and Noise</b>",
                       font=TITLE_FONT),
            legend=dict(x=0.55, y=0.98, bgcolor="rgba(255,255,255,0.9)"),
        )

        for ann in fig.layout.annotations:
            ann.font = dict(size=12, family=FONT["family"])

    return fig


def fig_exact_vs_perturbative() -> go.Figure:
    """Fractional difference (n_exact - n_pert)/n_pert vs omega/T_H for all 3 platforms.

    Shows where the exact WKB connection formula deviates from the
    perturbative EFT treatment, highlighting the UV regime.
    """
    from src.wkb.spectrum import (
        steinhauer_platform, heidelberg_platform, trento_platform,
        compare_exact_vs_perturbative,
    )

    platforms = [
        ("Steinhauer", steinhauer_platform(), COLORS["Steinhauer"]),
        ("Heidelberg", heidelberg_platform(), COLORS["Heidelberg"]),
        ("Trento", trento_platform(), COLORS["Trento"]),
    ]

    fig = go.Figure()

    for name, p, color in platforms:
        comparison = compare_exact_vs_perturbative(
            p, omega_min=0.1, omega_max_factor=8.0, n_points=100,
        )
        T_H = p.T_H

        fig.add_trace(go.Scatter(
            x=comparison.omega / T_H, y=comparison.fractional_difference,
            mode="lines", name=name,
            line=dict(color=color, width=2.5),
            hovertemplate=f"{name}<br>omega/T_H=%{{x:.2f}}<br>frac_diff=%{{y:.4f}}<extra></extra>",
        ))

    fig.add_hline(y=0, line=dict(color="rgba(0,0,0,0.3)", width=1))
    fig.add_hline(y=0.01, line=dict(color=COLORS["sensitivity"], width=1, dash="dash"),
                  annotation_text="1% level", annotation_position="right",
                  annotation_font=dict(size=10, color="#888"))
    fig.add_hline(y=-0.01, line=dict(color=COLORS["sensitivity"], width=1, dash="dash"))

    fig.update_xaxes(title_text="ω / T<sub>H</sub>")
    fig.update_yaxes(title_text="Fractional difference (n<sub>exact</sub> − n<sub>pert</sub>) / n<sub>pert</sub>")

    apply_layout(fig,
        height=450, width=750,
        title=dict(text="<b>Exact vs Perturbative WKB: Fractional Difference</b>",
                   font=TITLE_FONT),
        legend=dict(x=0.02, y=0.98, bgcolor="rgba(255,255,255,0.9)"),
    )

    return fig


# ════════════════════════════════════════════════════════════════════
# Phase 3 Wave 3: ADW Gap Equation Figures
# ════════════════════════════════════════════════════════════════════

def fig_adw_effective_potential() -> go.Figure:
    """V_eff(C) for three coupling ratios: G/G_c = 0.5, 1.0, 2.0.

    Shows the Coleman-Weinberg effective potential transitioning from
    a single minimum at C=0 (pre-geometric) to a Mexican hat with
    nontrivial minimum (full tetrad) as coupling increases.
    """
    from src.adw.gap_equation import (
        effective_potential, critical_coupling, effective_potential_landscape,
    )
    import numpy as np

    Lambda, N_f = 1.0, 4
    G_c = critical_coupling(Lambda, N_f)

    ratios = [0.5, 1.0, 2.0]
    labels = ["G/G<sub>c</sub> = 0.5 (pre-geometric)",
              "G/G<sub>c</sub> = 1.0 (critical)",
              "G/G<sub>c</sub> = 2.0 (full tetrad)"]
    colors_list = [COLORS["dispersive"], COLORS["horizon"], COLORS["dissipative"]]
    dashes = ["dash", "dot", "solid"]

    fig = go.Figure()

    for ratio, label, color, dash in zip(ratios, labels, colors_list, dashes):
        landscape = effective_potential_landscape(
            G=ratio * G_c, Lambda=Lambda, N_f=N_f, n_points=200,
        )
        # Normalize by Lambda^4 for clean axis
        C_norm = landscape['C'] / Lambda
        V_norm = landscape['V_eff'] / Lambda**4

        fig.add_trace(go.Scatter(
            x=C_norm, y=V_norm,
            mode="lines", name=label,
            line=dict(color=color, width=2.5, dash=dash),
        ))

    fig.add_hline(y=0, line=dict(color="rgba(0,0,0,0.2)", width=1))

    fig.update_xaxes(title_text="C / \u039B", range=[0, 1])
    fig.update_yaxes(title_text="V<sub>eff</sub> / \u039B\u2074")

    apply_layout(fig,
        height=450, width=700,
        title=dict(text="<b>ADW Effective Potential: Phase Transition</b>",
                   font=TITLE_FONT),
        legend=dict(x=0.35, y=0.98, bgcolor="rgba(255,255,255,0.9)"),
    )

    return fig


def fig_adw_phase_diagram() -> go.Figure:
    """Phase diagram: tetrad VEV C/Lambda vs coupling ratio G/G_c.

    Shows pre-geometric phase (C=0) below G_c and full tetrad phase
    (C>0) above, with vestigial metric window near G_c.
    """
    from src.adw.gap_equation import full_gap_analysis, critical_coupling
    import numpy as np

    Lambda, N_f = 1.0, 4
    G_c = critical_coupling(Lambda, N_f)

    ratios = np.linspace(0.1, 5.0, 100)
    C_values = []
    for r in ratios:
        result = full_gap_analysis(G=r * G_c, Lambda=Lambda, N_f=N_f)
        if result.nontrivial_solution and result.phase.value == "full_tetrad":
            C_values.append(result.nontrivial_solution.C / Lambda)
        else:
            C_values.append(0.0)

    fig = go.Figure()

    fig.add_trace(go.Scatter(
        x=ratios, y=C_values,
        mode="lines", name="C / \u039B",
        line=dict(color=COLORS["dissipative"], width=3),
        fill="tozeroy",
        fillcolor="rgba(230,57,70,0.1)",
    ))

    # Mark G_c
    fig.add_vline(x=1.0, line=dict(color=COLORS["horizon"], width=2, dash="dash"),
                  annotation_text="G = G<sub>c</sub>",
                  annotation_position="top",
                  annotation_font=dict(size=12))

    # Phase labels
    fig.add_annotation(x=0.5, y=0.15, text="Pre-geometric<br>(e = 0)",
                       showarrow=False, font=dict(size=13, color=COLORS["dispersive"]))
    fig.add_annotation(x=3.0, y=0.5, text="Full tetrad<br>(e \u2260 0, Lorentzian)",
                       showarrow=False, font=dict(size=13, color=COLORS["dissipative"]))

    fig.update_xaxes(title_text="G / G<sub>c</sub>")
    fig.update_yaxes(title_text="C / \u039B (tetrad VEV)", range=[0, 1.0])

    apply_layout(fig,
        height=450, width=700,
        title=dict(text="<b>ADW Phase Diagram: Tetrad Condensation</b>",
                   font=TITLE_FONT),
    )

    return fig


def fig_adw_ng_mode_decomposition() -> go.Figure:
    """Bar chart: tetrad component decomposition in 4D.

    16 = 6 (spin connection) + 4 (diffeomorphisms) + 2 (graviton) + 4 (massive)
    """
    from src.adw.fluctuations import classify_ng_modes

    modes = classify_ng_modes(4)

    names = []
    counts = []
    colors_list = []
    mode_colors = {
        "absorbed": COLORS["cross"],
        "pure_gauge": COLORS["sensitivity"],
        "massless_graviton": COLORS["Steinhauer"],
        "massive_higgs": COLORS["Trento"],
    }

    for m in modes:
        names.append(m.mode_type.value.replace("_", " ").title())
        counts.append(m.count)
        colors_list.append(mode_colors.get(m.mode_type.value, "#999999"))

    fig = go.Figure()

    fig.add_trace(go.Bar(
        x=names, y=counts,
        marker_color=colors_list,
        text=[str(c) for c in counts],
        textposition="outside",
        textfont=dict(size=14, color="black"),
    ))

    # Annotate total
    fig.add_annotation(x=1.5, y=15, text="Total: 16 = 4<sup>2</sup>",
                       showarrow=False, font=dict(size=13))

    fig.update_xaxes(title_text="Mode Type")
    fig.update_yaxes(title_text="Count", range=[0, 18])

    apply_layout(fig,
        height=450, width=650,
        title=dict(text="<b>Tetrad Mode Decomposition (Vergeles Counting)</b>",
                   font=TITLE_FONT),
    )

    return fig


def fig_adw_he3_analogy() -> go.Figure:
    """Side-by-side comparison: ADW tetrad vs He-3 superfluid order parameter.

    Two columns showing the parallel structure:
    - Order parameter (e^a_mu vs A_{alpha i})
    - Symmetry breaking pattern
    - NG modes absorbed by gauge field
    - Remaining Higgs modes (graviton vs superfluid collective modes)
    """
    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=["<b>ADW Tetrad Condensation</b>",
                        "<b>Superfluid ³He (p-wave BCS)</b>"],
        horizontal_spacing=0.15,
    )

    # ADW properties
    adw_props = ["e<sup>a</sup><sub>\u03bc</sub> (4\u00d74)", "SO(3,1) \u00d7 SO(3,1)", "6 \u2192 spin connection",
                 "2 massless graviton", "4 massive Higgs"]
    adw_labels = ["Order Parameter", "Symmetry", "NG Absorbed", "Massless", "Massive"]

    # He-3 properties
    he3_props = ["A<sub>\u03b1i</sub> (3\u00d73)", "SO(3)<sub>S</sub> \u00d7 SO(3)<sub>L</sub> \u00d7 U(1)",
                 "3 \u2192 spin-orbit", "2 sound modes", "4 massive modes"]

    y_pos = list(range(len(adw_props), 0, -1))

    for i, (label, adw, he3) in enumerate(zip(adw_labels, adw_props, he3_props)):
        fig.add_trace(go.Scatter(
            x=[0.5], y=[y_pos[i]],
            mode="text", text=[f"<b>{label}:</b> {adw}"],
            textposition="middle center",
            textfont=dict(size=12),
            showlegend=False,
        ), row=1, col=1)

        fig.add_trace(go.Scatter(
            x=[0.5], y=[y_pos[i]],
            mode="text", text=[f"<b>{label}:</b> {he3}"],
            textposition="middle center",
            textfont=dict(size=12),
            showlegend=False,
        ), row=1, col=2)

    for col in [1, 2]:
        fig.update_xaxes(showticklabels=False, showgrid=False, zeroline=False,
                         showline=False, range=[0, 1], row=1, col=col)
        fig.update_yaxes(showticklabels=False, showgrid=False, zeroline=False,
                         showline=False, range=[0.2, 5.8], row=1, col=col)

    apply_layout(fig,
        height=320, width=900,
        title=dict(text="<b>Structural Analogy: Tetrad vs Superfluid ³He</b>",
                   font=TITLE_FONT),
        margin=dict(l=30, r=30, t=50, b=20),
    )

    return fig


def fig_adw_structural_obstacles() -> go.Figure:
    """Horizontal bar chart of the four structural obstacles with severity.

    Uses blue/amber for severity levels (not red/green for colorblind accessibility).
    """
    from src.adw.fluctuations import structural_obstacles

    obstacles = structural_obstacles()
    short_names = {
        "spin_connection_gap": "Spin Connection\nGap",
        "grassmann_bosonic_incompatibility": "Grassmann-Bosonic\nIncompatibility",
        "nielsen_ninomiya_doubling": "Nielsen-Ninomiya\nDoubling",
        "cosmological_constant": "Cosmological\nConstant",
    }
    names = [short_names.get(o.name, o.name.replace("_", " ").title()) for o in obstacles]
    severities = [o.severity for o in obstacles]

    # Severity scoring
    severity_score = {"serious": 2, "moderate": 1}
    scores = [severity_score[s] for s in severities]

    # Blue/amber for severity (colorblind accessible)
    color_map = {"serious": COLORS["Steinhauer"], "moderate": COLORS["Trento"]}
    bar_colors = [color_map[s] for s in severities]

    fig = go.Figure()

    fig.add_trace(go.Bar(
        y=names, x=scores,
        orientation="h",
        marker_color=bar_colors,
        text=[s.upper() for s in severities],
        textposition="inside",
        textfont=dict(size=12, color="white"),
    ))

    fig.update_xaxes(title_text="Severity", tickvals=[1, 2],
                     ticktext=["Moderate", "Serious"], range=[0, 2.5])
    fig.update_yaxes(title_text="")

    # Legend annotations
    fig.add_annotation(x=2.3, y=3, text="<b>Status: All Open</b>",
                       showarrow=False, font=dict(size=11))

    apply_layout(fig,
        height=350, width=700,
        title=dict(text="<b>Structural Obstacles for Emergent Fermion Bootstrap</b>",
                   font=TITLE_FONT),
    )

    return fig


def fig_adw_coupling_scan(stakeholder: bool = False) -> go.Figure:
    """V_eff and tetrad VEV scanned across G/G_c for N_f = 2, 4, 8.

    Two panels:
    - Left: V_eff(C_min) vs G/G_c (depth of the minimum)
    - Right: C_min/Lambda vs G/G_c (order parameter)

    Stakeholder version uses simpler labels and larger fonts.
    """
    from src.adw.gap_equation import full_gap_analysis, critical_coupling
    import numpy as np

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=["<b>Potential Depth at Minimum</b>",
                        "<b>Tetrad VEV (Order Parameter)</b>"],
        horizontal_spacing=0.12,
    )

    Lambda = 1.0
    nf_values = [2, 4, 8]
    nf_colors = [COLORS["Steinhauer"], COLORS["Heidelberg"], COLORS["Trento"]]

    for N_f, color in zip(nf_values, nf_colors):
        G_c = critical_coupling(Lambda, N_f)
        ratios = np.linspace(0.5, 5.0, 80)
        V_mins = []
        C_mins = []

        for r in ratios:
            result = full_gap_analysis(G=r * G_c, Lambda=Lambda, N_f=N_f)
            if result.nontrivial_solution and result.phase.value == "full_tetrad":
                V_mins.append(result.nontrivial_solution.V_eff / Lambda**4)
                C_mins.append(result.nontrivial_solution.C / Lambda)
            else:
                V_mins.append(0.0)
                C_mins.append(0.0)

        label = f"N<sub>f</sub> = {N_f}" if not stakeholder else f"{N_f} fermion species"

        fig.add_trace(go.Scatter(
            x=ratios, y=V_mins,
            mode="lines", name=label,
            line=dict(color=color, width=2.5),
            legendgroup=f"nf{N_f}",
        ), row=1, col=1)

        fig.add_trace(go.Scatter(
            x=ratios, y=C_mins,
            mode="lines", name=label,
            line=dict(color=color, width=2.5),
            legendgroup=f"nf{N_f}",
            showlegend=False,
        ), row=1, col=2)

    fig.add_vline(x=1.0, line=dict(color="black", width=1, dash="dash"),
                  annotation_text="G<sub>c</sub>", annotation_position="top",
                  row=1, col=1)
    fig.add_vline(x=1.0, line=dict(color="black", width=1, dash="dash"),
                  row=1, col=2)

    fig.update_xaxes(title_text="G / G<sub>c</sub>", row=1, col=1)
    fig.update_xaxes(title_text="G / G<sub>c</sub>", row=1, col=2)
    fig.update_yaxes(title_text="V<sub>eff</sub>(C<sub>min</sub>) / \u039B<sup>4</sup>", row=1, col=1)
    fig.update_yaxes(title_text="C<sub>min</sub> / \u039B", row=1, col=2)

    title = ("<b>ADW Gap Equation: Coupling Scan</b>" if not stakeholder
             else "<b>Tetrad Condensation Across Coupling Strength</b>")

    apply_layout(fig,
        height=450, width=900,
        title=dict(text=title, font=TITLE_FONT),
        legend=dict(x=0.02, y=0.98, bgcolor="rgba(255,255,255,0.9)"),
    )

    return fig


# ════════════════════════════════════════════════════════════════
# Phase 4 Wave 1: Experimental Prediction Figures (fig35-fig38)
# ════════════════════════════════════════════════════════════════

def fig_prediction_table_comparison():
    """Fig 35: Platform prediction comparison — n(omega) for all three platforms.

    Shows the full spectral occupation n(omega)/n_Planck(omega) for
    Steinhauer, Heidelberg, and Trento, highlighting the frequency
    dependence of deviations from the Planckian.
    """
    from src.experimental.predictions import compute_all_predictions

    tables = compute_all_predictions()

    fig = go.Figure()

    platform_colors = {
        'steinhauer': COLORS['Steinhauer'],
        'heidelberg': COLORS['Heidelberg'],
        'trento': COLORS['Trento'],
    }
    platform_labels = {
        'steinhauer': 'Steinhauer <sup>87</sup>Rb',
        'heidelberg': 'Heidelberg <sup>39</sup>K',
        'trento': 'Trento <sup>23</sup>Na',
    }

    for name, table in tables.items():
        omegas = [p.omega_over_T_H for p in table.predictions]
        deviations = [p.fractional_deviation * 100 for p in table.predictions]

        fig.add_trace(go.Scatter(
            x=omegas, y=deviations,
            mode="lines+markers",
            name=platform_labels[name],
            line=dict(color=platform_colors[name], width=2.5),
            marker=dict(size=8, color=platform_colors[name]),
        ))

    fig.add_hline(y=0, line=dict(color="black", width=0.5, dash="dash"))

    apply_layout(fig,
        height=450, width=700,
        title=dict(text="<b>Spectral Deviation from Planckian</b>", font=TITLE_FONT),
        xaxis_title="\u03c9 / T<sub>H</sub>",
        yaxis_title="Fractional deviation [%]",
        legend=dict(x=0.02, y=0.98, bgcolor="rgba(255,255,255,0.9)"),
    )

    return fig


def fig_detector_requirements():
    """Fig 36: Detector requirements — shots needed vs measurement goal.

    Bar chart comparing the required experimental shots for three
    measurement goals across all platforms.
    """
    from src.experimental.predictions import compute_detector_requirements
    from src.wkb.spectrum import steinhauer_platform, heidelberg_platform, trento_platform

    platforms = [
        ('Steinhauer', steinhauer_platform()),
        ('Heidelberg', heidelberg_platform()),
        ('Trento', trento_platform()),
    ]
    platform_colors_list = [COLORS['Steinhauer'], COLORS['Heidelberg'], COLORS['Trento']]

    fig = go.Figure()

    goal_short = ['\u03b4<sub>diss</sub>', 'n<sub>noise</sub>', 'WKB vs EFT']

    for i, (pname, platform) in enumerate(platforms):
        reqs = compute_detector_requirements(platform)
        shots = [np.log10(max(r.required_shots, 1)) for r in reqs]

        fig.add_trace(go.Bar(
            x=goal_short,
            y=shots,
            name=pname,
            marker_color=platform_colors_list[i],
        ))

    fig.add_hline(y=np.log10(7000), line=dict(color="black", width=1, dash="dot"),
                  annotation_text="Current (7000 shots)",
                  annotation_position="top right")

    apply_layout(fig,
        height=450, width=700,
        title=dict(text="<b>Detector Requirements by Measurement Goal</b>", font=TITLE_FONT),
        xaxis_title="Measurement goal",
        yaxis_title="log\u2081\u2080(shots needed)",
        barmode='group',
        legend=dict(x=0.02, y=0.98, bgcolor="rgba(255,255,255,0.9)"),
    )

    return fig


def fig_kappa_scaling_phase4():
    """Fig 37: Kappa-scaling test prediction for Heidelberg K-39.

    Shows how dispersive (D^2) and dissipative corrections scale with
    the adiabaticity parameter D, demonstrating the experimental handle
    for separating the two effects.
    """
    from src.experimental.predictions import kappa_scaling_prediction

    pred = kappa_scaling_prediction(n_points=20)
    D_values = np.linspace(0.01, 0.05, 20)

    fig = make_subplots(rows=1, cols=2,
                        subplot_titles=["Dispersive correction",
                                        "Dissipative correction"])

    fig.add_trace(go.Scatter(
        x=D_values, y=np.abs(pred.delta_disp_values),
        mode="lines+markers",
        name=f"|\u03b4<sub>disp</sub>| \u221d D<sup>{pred.scaling_exponent_disp:.1f}</sup>",
        line=dict(color=COLORS['dispersive'], width=2.5),
        marker=dict(size=5),
    ), row=1, col=1)

    # Reference D^2 line
    ref_disp = (np.pi / 6) * D_values**2
    fig.add_trace(go.Scatter(
        x=D_values, y=ref_disp,
        mode="lines",
        name="D\u00b2 reference",
        line=dict(color="grey", width=1, dash="dash"),
        showlegend=True,
    ), row=1, col=1)

    fig.add_trace(go.Scatter(
        x=D_values, y=pred.delta_diss_values,
        mode="lines+markers",
        name=f"\u03b4<sub>diss</sub> \u221d D<sup>{pred.scaling_exponent_diss:.1f}</sup>",
        line=dict(color=COLORS['dissipative'], width=2.5),
        marker=dict(size=5),
    ), row=1, col=2)

    fig.update_xaxes(title_text="D = \u03ba\u03be/c<sub>s</sub>", row=1, col=1)
    fig.update_xaxes(title_text="D = \u03ba\u03be/c<sub>s</sub>", row=1, col=2)
    fig.update_yaxes(title_text="|\u03b4<sub>disp</sub>|", type="log", row=1, col=1)
    # δ_diss is D-independent (~5e-5), so show actual scale
    diss_max = max(abs(v) for v in pred.delta_diss_values) if any(pred.delta_diss_values) else 1e-4
    fig.update_yaxes(title_text="\u03b4<sub>diss</sub>",
                     range=[0, diss_max * 3], row=1, col=2)
    fig.add_annotation(
        text=f"\u03b4<sub>diss</sub> \u2248 {diss_max:.1e} (D-independent)",
        xref="x2", yref="y2",
        x=0.03, y=diss_max * 2, showarrow=False,
        font=dict(size=11, color=COLORS['dissipative']),
    )

    apply_layout(fig,
        height=400, width=850,
        title=dict(text="<b>Kappa-Scaling Test: Dispersive vs Dissipative</b>", font=TITLE_FONT),
        legend=dict(x=0.02, y=0.98, bgcolor="rgba(255,255,255,0.9)"),
    )

    return fig


def fig_kappa_scaling_physical():
    """Fig 45: Physical kappa-scaling predictions for all three BEC platforms.

    Shows how |δ_disp| (∝ κ²) and δ_diss (∝ κ) scale with surface gravity
    for each platform at fixed BEC material properties. The crossover κ_cross
    where |δ_disp| = δ_diss is marked for each platform.

    Key physics: the different scaling exponents (2 vs 1) provide an
    experimental discriminant. Platforms span the crossover:
    - Heidelberg: dissipative-dominated (κ_nom ≪ κ_cross)
    - Steinhauer: near crossover (κ_nom ≈ κ_cross)
    - Trento: dispersive-dominated (κ_nom ≫ κ_cross)
    """
    from src.experimental.kappa_scaling import compute_all_sweeps

    sweeps = compute_all_sweeps()

    fig = go.Figure()

    for name in ['Steinhauer', 'Heidelberg', 'Trento']:
        sweep = sweeps[name]
        color = COLORS[name]
        kappa = sweep.kappa_values

        # |delta_disp| (dashed) — quadratic scaling
        fig.add_trace(go.Scatter(
            x=kappa, y=np.abs(sweep.delta_disp_values),
            mode="lines",
            name=f"{name} |δ<sub>disp</sub>| ∝ κ²",
            line=dict(color=color, width=2, dash="dash"),
            legendgroup=name,
        ))

        # delta_diss (solid) — linear scaling
        fig.add_trace(go.Scatter(
            x=kappa, y=sweep.delta_diss_values,
            mode="lines",
            name=f"{name} δ<sub>diss</sub> ∝ κ",
            line=dict(color=color, width=2.5),
            legendgroup=name,
        ))

        # Mark nominal kappa
        nom_idx = np.argmin(np.abs(kappa - sweep.kappa_nominal))
        fig.add_trace(go.Scatter(
            x=[sweep.kappa_nominal],
            y=[sweep.delta_diss_values[nom_idx]],
            mode="markers",
            name=f"{name} nominal κ",
            marker=dict(size=8, color=color, symbol="circle"),
            legendgroup=name,
            showlegend=False,
        ))

        # Mark crossover kappa if it's in range
        if kappa[0] < sweep.kappa_cross < kappa[-1]:
            from src.core.formulas import kappa_scaling_dissipative
            d_diss_cross = kappa_scaling_dissipative(
                sweep.kappa_cross, sweep.gamma_1, sweep.gamma_2, sweep.c_s
            )
            fig.add_trace(go.Scatter(
                x=[sweep.kappa_cross],
                y=[d_diss_cross],
                mode="markers",
                name=f"{name} κ<sub>cross</sub>",
                marker=dict(size=10, color=color, symbol="x", line=dict(width=2)),
                legendgroup=name,
                showlegend=False,
            ))

    apply_layout(fig,
        height=500, width=800,
        title=dict(text="<b>κ-Scaling Test: EFT Corrections vs Surface Gravity</b>",
                   font=TITLE_FONT),
        xaxis_title="κ [s⁻¹]",
        yaxis_title="Correction magnitude",
        xaxis_type="log",
        yaxis_type="log",
        legend=dict(x=0.02, y=0.02, yanchor="bottom",
                    bgcolor="rgba(255,255,255,0.9)", font=dict(size=10)),
    )

    return fig


def fig_polariton_regime_map():
    """Fig 47: Polariton Tier 1 regime map — Gamma_pol/kappa vs cavity lifetime.

    Shows the three cavity quality regimes (intractable, borderline,
    perturbative/excellent) as colored regions, with the three Paris
    polariton configurations marked. Includes the BEC platforms for
    comparison (all deep in the perturbative regime).
    """
    from src.experimental.polariton_predictions import polariton_regime_map

    regime = polariton_regime_map()

    # Regime boundaries
    tau_range = np.logspace(-12, -9, 100)  # 1 ps to 1 ns
    kappa = 5.0e10  # s^-1 (same for all polariton platforms)
    gamma_over_kappa = 1.0 / (tau_range * kappa)

    fig = go.Figure()

    # Background regime bands
    fig.add_hrect(y0=1.0, y1=10, fillcolor="rgba(230,57,70,0.15)",
                  line_width=0, annotation_text="Intractable",
                  annotation_position="top left")
    fig.add_hrect(y0=0.1, y1=1.0, fillcolor="rgba(241,143,1,0.15)",
                  line_width=0, annotation_text="Borderline",
                  annotation_position="top left")
    fig.add_hrect(y0=0.03, y1=0.1, fillcolor="rgba(92,148,110,0.15)",
                  line_width=0, annotation_text="Perturbative (Tier 1)",
                  annotation_position="top left")
    fig.add_hrect(y0=0.001, y1=0.03, fillcolor="rgba(46,134,171,0.15)",
                  line_width=0, annotation_text="Excellent",
                  annotation_position="top left")

    # Polariton platforms
    regime_colors = {
        'intractable': COLORS['dissipative'],
        'borderline': COLORS['Trento'],
        'perturbative': COLORS['dispersive'],
        'excellent': COLORS['Steinhauer'],
    }

    for name, data in regime.items():
        color = regime_colors.get(data['tier1_regime'], 'grey')
        fig.add_trace(go.Scatter(
            x=[data['tau_cav_ps']],
            y=[data['Gamma_pol_over_kappa']],
            mode="markers+text",
            name=name.replace('_', ' '),
            marker=dict(size=12, color=color, symbol="diamond"),
            text=[f"  {name.split('_')[1]}"],
            textposition="middle right",
            textfont=dict(size=11),
        ))

    # Reference line: Gamma_pol/kappa = 1/tau*kappa
    fig.add_trace(go.Scatter(
        x=tau_range * 1e12,
        y=gamma_over_kappa,
        mode="lines",
        name="Γ_pol/κ = 1/(τκ)",
        line=dict(color="grey", width=1, dash="dot"),
        showlegend=False,
    ))

    apply_layout(fig,
        height=450, width=700,
        title=dict(text="<b>Polariton Tier 1 Regime Map</b>", font=TITLE_FONT),
        xaxis_title="Cavity lifetime τ [ps]",
        yaxis_title="Γ<sub>pol</sub> / κ",
        xaxis_type="log",
        yaxis_type="log",
        legend=dict(x=0.02, y=0.98, bgcolor="rgba(255,255,255,0.9)"),
    )
    fig.update_yaxes(range=[np.log10(0.001), np.log10(10)])

    return fig


def fig_noise_floor_crossover():
    """Fig 38: Noise floor crossover — where FDR noise exceeds Hawking signal.

    Shows n_Hawking and n_noise vs frequency for each platform, marking
    the crossover frequency where the noise floor dominates.
    """
    from src.wkb.spectrum import compute_spectrum, steinhauer_platform, heidelberg_platform, trento_platform

    platforms = [
        ('Steinhauer', steinhauer_platform(), COLORS['Steinhauer']),
        ('Heidelberg', heidelberg_platform(), COLORS['Heidelberg']),
        ('Trento', trento_platform(), COLORS['Trento']),
    ]

    fig = go.Figure()

    for pname, platform, color in platforms:
        spectrum = compute_spectrum(platform, omega_min=0.2, omega_max_factor=10.0, n_points=80)
        T_H = platform.T_H
        omegas = spectrum.omega_array / T_H
        n_hawking = np.array([p.n_hawking for p in spectrum.points])
        n_noise = np.array([p.n_noise for p in spectrum.points])

        fig.add_trace(go.Scatter(
            x=omegas, y=n_hawking,
            mode="lines",
            name=f"{pname} n<sub>Hawking</sub>",
            line=dict(color=color, width=2),
            legendgroup=pname,
        ))

        fig.add_trace(go.Scatter(
            x=omegas, y=n_noise,
            mode="lines",
            name=f"{pname} n<sub>noise</sub>",
            line=dict(color=color, width=1.5, dash="dot"),
            legendgroup=pname,
        ))

        # Find crossover
        crossover_idx = None
        for i in range(len(n_hawking)):
            if n_noise[i] > n_hawking[i] and n_hawking[i] > 1e-20:
                crossover_idx = i
                break

        if crossover_idx is not None:
            fig.add_trace(go.Scatter(
                x=[omegas[crossover_idx]],
                y=[n_noise[crossover_idx]],
                mode="markers",
                name=f"{pname} crossover",
                marker=dict(size=10, symbol="x", color=color, line=dict(width=2)),
                legendgroup=pname,
                showlegend=False,
            ))

    apply_layout(fig,
        height=450, width=700,
        title=dict(text="<b>Noise Floor Crossover</b>", font=TITLE_FONT),
        xaxis_title="\u03c9 / T<sub>H</sub>",
        yaxis_title="Occupation number n(\u03c9)",
        yaxis_type="log",
        legend=dict(x=0.65, y=0.98, bgcolor="rgba(255,255,255,0.9)", font=dict(size=10)),
    )

    return fig


def fig_chirality_wall_status():
    """Fig 39: Chirality wall status — GS conditions vs TPF evasion.

    Shows each GS no-go condition and whether TPF evades it, color-coded
    by verdict: evaded (blue), applies (amber), unclear (grey).
    """
    from src.chirality.tpf_gs_analysis import gs_conditions

    conditions = gs_conditions()

    names = [c.name.replace("_", " ").title() for c in conditions]
    verdicts = [c.applies_to_tpf.value for c in conditions]

    verdict_colors = {
        'evaded': COLORS['Steinhauer'],      # blue — good news
        'applies': COLORS['Trento'],          # amber — constraint holds
        'unclear': '#8D99AE',                 # grey — undetermined
    }
    colors = [verdict_colors.get(v, '#8D99AE') for v in verdicts]

    fig = go.Figure()
    fig.add_trace(go.Bar(
        x=names,
        y=[1] * len(conditions),
        marker_color=colors,
        text=[v.upper() for v in verdicts],
        textposition='inside',
        textfont=dict(size=14, color='white'),
    ))

    fig.update_yaxes(visible=False)

    apply_layout(fig,
        height=350, width=700,
        title=dict(text="<b>Chirality Wall: GS Conditions vs TPF Construction</b>",
                   font=TITLE_FONT),
        xaxis_title="Golterman-Shamir condition",
    )

    return fig


def fig_gl_phase_diagram():
    """Fig 40: GL phase diagram — B-phase, A-phase, and pre-geometric regions.

    Shows the ground state energy as a function of coupling G/G_c for
    each phase classification.
    """
    from src.adw.ginzburg_landau import compute_phase_diagram

    diagram = compute_phase_diagram(Lambda=1.0, N_f=4, n_points=60)

    fig = go.Figure()

    # Pre-geometric: F = 0 for all couplings
    fig.add_trace(go.Scatter(
        x=list(diagram.coupling_ratios),
        y=[0.0] * len(diagram.coupling_ratios),
        mode="lines",
        name="Pre-geometric",
        line=dict(color='#8D99AE', width=2.5, dash="dash"),
    ))

    fig.add_trace(go.Scatter(
        x=list(diagram.coupling_ratios),
        y=list(diagram.free_energies_B),
        mode="lines",
        name="B-phase (isotropic)",
        line=dict(color=COLORS['Steinhauer'], width=2.5),
    ))

    fig.add_trace(go.Scatter(
        x=list(diagram.coupling_ratios),
        y=list(diagram.free_energies_A),
        mode="lines",
        name="A-phase (anisotropic)",
        line=dict(color=COLORS['Heidelberg'], width=2.5),
    ))

    fig.add_trace(go.Scatter(
        x=list(diagram.coupling_ratios),
        y=list(diagram.free_energies_polar),
        mode="lines",
        name="Polar",
        line=dict(color=COLORS['Trento'], width=2.5),
    ))

    fig.add_vline(x=1.0, line=dict(color="black", width=1, dash="dash"),
                  annotation_text="G<sub>c</sub>", annotation_position="top")

    apply_layout(fig,
        height=450, width=700,
        title=dict(text="<b>Ginzburg-Landau Phase Diagram</b>", font=TITLE_FONT),
        xaxis_title="G / G<sub>c</sub>",
        yaxis_title="F<sub>GL</sub> / \u039B<sup>4</sup>",
        legend=dict(x=0.02, y=0.98, bgcolor="rgba(255,255,255,0.9)"),
    )

    return fig


def fig_he3_comparison_table():
    """Fig 41: He-3 vs ADW structural comparison — match/mismatch indicators.

    Visual table showing which aspects of He-3 superfluid physics have
    structural analogs in the ADW tetrad condensation framework.
    """
    from src.adw.ginzburg_landau import he3_comparison

    comparisons = he3_comparison()

    adw_items = [c.adw_quantity for c in comparisons]
    he3_items = [c.he3_analog for c in comparisons]
    matches = [c.structural_match for c in comparisons]

    colors = [COLORS['Steinhauer'] if m else COLORS['Trento'] for m in matches]
    symbols = ['\u2713' if m else '\u2717' for m in matches]

    fig = go.Figure()
    fig.add_trace(go.Table(
        header=dict(
            values=['ADW Quantity', 'He-3 Analog', 'Match'],
            fill_color='lightgrey',
            align='center',
            font=dict(size=13, family=FONT['family']),
        ),
        cells=dict(
            values=[adw_items, he3_items, symbols],
            fill_color=[['white'] * len(adw_items),
                        ['white'] * len(he3_items),
                        [c if m else c for c, m in zip(
                            ['rgba(46,134,171,0.15)'] * len(matches),
                            matches
                        )]],
            align='center',
            font=dict(size=12, family=FONT['family']),
        ),
    ))

    fig.update_layout(
        title=dict(text="<b>He-3 vs ADW Structural Comparison</b>", font=TITLE_FONT),
        height=400, width=700,
        margin=dict(l=10, r=10, t=50, b=10),
    )

    return fig


# ════════════════════════════════════════════════════════════════
# Phase 4 Wave 2: Vestigial Gravity + Backreaction (fig42-fig44)
# ════════════════════════════════════════════════════════════════

def fig_vestigial_effective_potential():
    """Paper 6 native V_eff figure: effective potential at three coupling ratios
    showing the transition from pre-geometric (stable origin) through vestigial
    (small curvature) to full tetrad (Mexican hat).

    Uses G/G_c = 0.5 (pre-geometric), 0.9 (vestigial), 1.5 (full tetrad).
    """
    from src.adw.gap_equation import effective_potential
    from src.core.formulas import adw_critical_coupling, adw_curvature_at_origin

    Lambda = 1.0
    N_f = 4
    G_c = adw_critical_coupling(Lambda, N_f)

    C_range = np.linspace(0, 0.6 * Lambda, 200)

    ratios = [0.5, 0.9, 2.0]
    labels = [
        f"G/G<sub>c</sub> = 0.5 (pre-geometric)",
        f"G/G<sub>c</sub> = 0.9 (vestigial)",
        f"G/G<sub>c</sub> = 2.0 (full tetrad)",
    ]
    colors_list = [COLORS['dispersive'], COLORS['Trento'], COLORS['Steinhauer']]

    fig = go.Figure()

    for r, label, color in zip(ratios, labels, colors_list):
        G = r * G_c
        V_vals = [effective_potential(c, G, Lambda, N_f) for c in C_range]
        fig.add_trace(go.Scatter(
            x=C_range / Lambda, y=V_vals,
            mode="lines", name=label,
            line=dict(color=color, width=2.5),
        ))

    fig.add_hline(y=0, line=dict(color="grey", width=0.5, dash="dash"))

    # Cap y-range so the Mexican-hat dip at G > G_c is visible
    apply_layout(fig,
        height=450, width=650,
        title=dict(text="<b>Effective Potential V<sub>eff</sub>(C)</b>", font=TITLE_FONT),
        xaxis_title="C / \u039b",
        yaxis_title="V<sub>eff</sub>(C)",
        legend=dict(x=0.35, y=0.98, bgcolor="rgba(255,255,255,0.9)"),
    )
    fig.update_yaxes(range=[-0.002, 0.005])

    return fig


def fig_vestigial_phase_diagram():
    """Fig 42: Vestigial gravity phase diagram from mean-field scan."""
    from src.vestigial.phase_diagram import scan_coupling

    result = scan_coupling(
        method="mean_field", Lambda=1.0, N_f=4,
        coupling_range=(0.3, 3.0), n_points=60,
    )

    fig = make_subplots(rows=1, cols=2,
                        subplot_titles=["Order parameters",
                                        "Phase classification"])

    fig.add_trace(go.Scatter(
        x=list(result.coupling_ratios),
        y=list(result.tetrad_values),
        mode="lines", name="Tetrad VEV",
        line=dict(color=COLORS['Steinhauer'], width=2.5),
    ), row=1, col=1)

    fig.add_trace(go.Scatter(
        x=list(result.coupling_ratios),
        y=list(result.metric_values),
        mode="lines", name="Metric correlator",
        line=dict(color=COLORS['Trento'], width=2.5),
    ), row=1, col=1)

    phase_colors = {
        'pre_geometric': '#8D99AE',
        'vestigial': COLORS['Trento'],
        'full_tetrad': COLORS['Steinhauer'],
    }
    y_phase = [1 if p == 'full_tetrad' else (0.5 if p == 'vestigial' else 0)
               for p in result.phases]

    fig.add_trace(go.Scatter(
        x=list(result.coupling_ratios),
        y=y_phase,
        mode="lines",
        name="Phase",
        line=dict(color="black", width=2),
        fill="tozeroy",
        fillcolor="rgba(46,134,171,0.1)",
    ), row=1, col=2)

    fig.add_vline(x=1.0, line=dict(color="black", width=1, dash="dash"),
                  row=1, col=1)
    fig.add_vline(x=1.0, line=dict(color="black", width=1, dash="dash"),
                  row=1, col=2)

    fig.update_xaxes(title_text="G / G<sub>c</sub>", row=1, col=1)
    fig.update_xaxes(title_text="G / G<sub>c</sub>", row=1, col=2)
    fig.update_yaxes(title_text="Magnitude / \u039B", row=1, col=1)
    fig.update_yaxes(title_text="Phase (0=pre, 0.5=vestigial, 1=full)", row=1, col=2)

    apply_layout(fig,
        height=400, width=850,
        title=dict(text="<b>Vestigial Gravity: Mean-Field Phase Diagram</b>",
                   font=TITLE_FONT),
        legend=dict(x=0.02, y=0.98, bgcolor="rgba(255,255,255,0.9)"),
    )

    return fig


def fig_backreaction_cooling():
    """Fig 43: Acoustic BH cooling — T_H(t) for all three platforms."""
    from src.wkb.backreaction import all_platform_backreaction

    results = all_platform_backreaction()

    platform_colors_map = {
        'steinhauer': COLORS['Steinhauer'],
        'heidelberg': COLORS['Heidelberg'],
        'trento': COLORS['Trento'],
    }
    platform_labels = {
        'steinhauer': 'Steinhauer <sup>87</sup>Rb',
        'heidelberg': 'Heidelberg <sup>39</sup>K',
        'trento': 'Trento <sup>23</sup>Na',
    }

    fig = go.Figure()

    for name, result in results.items():
        evo = result.evolution
        # Normalize time by cooling timescale
        tau = result.timescale.tau_cool
        t_norm = np.array(evo.times) / tau if tau > 0 else np.array(evo.times)
        T_norm = np.array(evo.T_H_values) / evo.T_H_values[0]

        color = platform_colors_map.get(name, 'grey')
        label = platform_labels.get(name, name)

        fig.add_trace(go.Scatter(
            x=t_norm, y=T_norm,
            mode="lines",
            name=label,
            line=dict(color=color, width=2.5),
        ))

    fig.add_hline(y=0, line=dict(color="black", width=0.5, dash="dash"))

    apply_layout(fig,
        height=450, width=700,
        title=dict(text="<b>Acoustic BH Cooling: Approach to Extremality</b>",
                   font=TITLE_FONT),
        xaxis_title="t / \u03c4<sub>cool</sub>",
        yaxis_title="T<sub>H</sub>(t) / T<sub>H</sub>(0)",
        legend=dict(x=0.65, y=0.98, bgcolor="rgba(255,255,255,0.9)"),
    )

    return fig


def fig_information_retention():
    """Fig 44: Information retention — fracton vs standard hydro."""
    from src.fracton.information_retention import (
        standard_hydro_charges, fracton_hydro_charges,
    )

    dims = [2, 3, 4, 5]
    standard_charges = []
    fracton_charges_dipole = []
    fracton_charges_quad = []

    for d in dims:
        si = standard_hydro_charges(d)
        fi_dip = fracton_hydro_charges(d, max_multipole=1)
        fi_quad = fracton_hydro_charges(d, max_multipole=2)
        standard_charges.append(si.conserved_charges)
        fracton_charges_dipole.append(fi_dip.conserved_charges)
        fracton_charges_quad.append(fi_quad.conserved_charges)

    fig = go.Figure()

    fig.add_trace(go.Bar(
        x=[str(d) for d in dims],
        y=standard_charges,
        name="Standard hydro",
        marker_color='#8D99AE',
    ))

    fig.add_trace(go.Bar(
        x=[str(d) for d in dims],
        y=fracton_charges_dipole,
        name="Fracton (dipole)",
        marker_color=COLORS['Steinhauer'],
    ))

    fig.add_trace(go.Bar(
        x=[str(d) for d in dims],
        y=fracton_charges_quad,
        name="Fracton (quadrupole)",
        marker_color=COLORS['Trento'],
    ))

    apply_layout(fig,
        height=400, width=700,
        title=dict(text="<b>UV Information Retention: Fracton vs Standard Hydro</b>",
                   font=TITLE_FONT),
        xaxis_title="Spacetime dimension d",
        yaxis_title="Conserved charges",
        barmode='group',
        legend=dict(x=0.02, y=0.98, bgcolor="rgba(255,255,255,0.9)"),
    )

    return fig


def fig_grassmann_trg_2d_phase():
    """Fig 48: 2D ADW phase diagram from Grassmann TRG.

    Shows free energy and specific heat as functions of the
    Einstein-Hilbert coupling at fixed cosmological coupling.
    Specific heat peaks signal phase transitions.
    """
    from src.vestigial.grassmann_trg import scan_coupling_2d, TRGParams

    scan = scan_coupling_2d(
        g_cosmo=1.0,
        g_EH_range=(0.0, 5.0),
        n_points=40,
        trg_params=TRGParams(D_cut=8, n_rg_steps=3),
    )

    fig = make_subplots(
        rows=2, cols=1,
        shared_xaxes=True,
        vertical_spacing=0.08,
        subplot_titles=[
            "<b>Free energy density</b>",
            "<b>Specific heat (phase transition signal)</b>",
        ],
    )

    # Free energy
    fig.add_trace(go.Scatter(
        x=scan.g_EH_values,
        y=scan.free_energies,
        mode='lines+markers',
        line=dict(color=COLORS['Steinhauer'], width=2),
        marker=dict(size=4),
        name="f(g<sub>EH</sub>)",
        showlegend=False,
    ), row=1, col=1)

    # Specific heat
    fig.add_trace(go.Scatter(
        x=scan.g_EH_values,
        y=scan.specific_heat,
        mode='lines+markers',
        line=dict(color=COLORS['Trento'], width=2),
        marker=dict(size=4),
        name="C(g<sub>EH</sub>)",
        showlegend=False,
    ), row=2, col=1)

    # Mark phase boundary if found
    if scan.phase_boundary is not None:
        for row in [1, 2]:
            fig.add_vline(
                x=scan.phase_boundary,
                line_dash="dash",
                line_color=COLORS['Heidelberg'],
                annotation_text=f"g*≈{scan.phase_boundary:.1f}" if row == 2 else None,
                row=row, col=1,
            )

    apply_layout(fig,
        height=600, width=700,
        title=dict(
            text="<b>2D ADW Phase Diagram (Grassmann TRG)</b>",
            font=TITLE_FONT,
        ),
    )

    for row in [1, 2]:
        fig.update_xaxes(title_text="g<sub>EH</sub> (Einstein-Hilbert coupling)", row=row, col=1)
    fig.update_yaxes(title_text="f = −ln Z / V", row=1, col=1)
    fig.update_yaxes(title_text="C = −d²f/dg²", row=2, col=1)

    return fig


def fig_fermion_bag_4d_binder():
    """Fig 49: 4D Binder cumulant scan from fermion-bag MC.

    Shows tetrad and metric Binder cumulants as functions of the
    Einstein-Hilbert coupling. Splitting between the two curves
    (metric ordering before tetrad) would indicate a vestigial phase.
    """
    from src.vestigial.phase_scan import scan_coupling_4d
    from src.vestigial.fermion_bag import FermionBagParams

    mc = FermionBagParams(n_thermalize=50, n_measure=100, n_skip=2, seed=42)
    scan = scan_coupling_4d(
        g_cosmo=1.0,
        g_EH_range=(0.0, 4.0),
        n_points=20,
        L=3,
        mc_params=mc,
    )

    fig = go.Figure()

    fig.add_trace(go.Scatter(
        x=scan.g_EH_values,
        y=scan.binder_metric,
        mode='lines+markers',
        line=dict(color=COLORS['Steinhauer'], width=2),
        marker=dict(size=5),
        name="U<sub>L</sub> (metric)",
    ))

    fig.add_trace(go.Scatter(
        x=scan.g_EH_values,
        y=scan.binder_tetrad,
        mode='lines+markers',
        line=dict(color=COLORS['Trento'], width=2, dash='dash'),
        marker=dict(size=5, symbol='diamond'),
        name="U<sub>L</sub> (tetrad)",
    ))

    # Reference lines
    fig.add_hline(y=2/3, line_dash="dot", line_color="gray",
                  annotation_text="ordered (2/3)")
    fig.add_hline(y=0, line_dash="dot", line_color="gray",
                  annotation_text="disordered (0)")

    apply_layout(fig,
        height=450, width=700,
        title=dict(
            text=f"<b>4D Binder Cumulants (L={scan.L}, fermion-bag MC)</b>",
            font=TITLE_FONT,
        ),
        xaxis_title="g<sub>EH</sub> (Einstein-Hilbert coupling)",
        yaxis_title="Binder cumulant U<sub>L</sub>",
        legend=dict(x=0.02, y=0.98, bgcolor="rgba(255,255,255,0.9)"),
    )

    return fig


def fig_fermion_bag_4d_phase_diagram():
    """Fig 50: 4D phase classification from fermion-bag MC.

    Shows the phase (pre-geometric, vestigial, tetrad-ordered) as
    a function of coupling, with metric correlator on secondary axis.
    """
    from src.vestigial.phase_scan import scan_coupling_4d
    from src.vestigial.fermion_bag import FermionBagParams

    mc = FermionBagParams(n_thermalize=50, n_measure=100, n_skip=2, seed=42)
    scan = scan_coupling_4d(
        g_cosmo=1.0,
        g_EH_range=(0.0, 4.0),
        n_points=20,
        L=3,
        mc_params=mc,
    )

    fig = make_subplots(
        rows=2, cols=1,
        shared_xaxes=True,
        vertical_spacing=0.08,
        subplot_titles=[
            "<b>Connected metric correlator (vestigial diagnostic)</b>",
            "<b>MC acceptance rate</b>",
        ],
    )

    # Metric correlator
    fig.add_trace(go.Scatter(
        x=scan.g_EH_values,
        y=scan.metric_correlator,
        mode='lines+markers',
        line=dict(color=COLORS['Steinhauer'], width=2),
        marker=dict(size=4),
        name="⟨g_μν g_ρσ⟩_c",
        showlegend=False,
    ), row=1, col=1)

    # Acceptance rate
    fig.add_trace(go.Scatter(
        x=scan.g_EH_values,
        y=scan.acceptance_rates,
        mode='lines+markers',
        line=dict(color=COLORS['Trento'], width=2),
        marker=dict(size=4),
        name="acceptance",
        showlegend=False,
    ), row=2, col=1)

    apply_layout(fig,
        height=550, width=700,
        title=dict(
            text="<b>4D ADW Phase Diagnostics (fermion-bag MC)</b>",
            font=TITLE_FONT,
        ),
    )

    for row in [1, 2]:
        fig.update_xaxes(title_text="g<sub>EH</sub> (Einstein-Hilbert coupling)", row=row, col=1)
    fig.update_yaxes(title_text="⟨gg⟩_c", row=1, col=1)
    fig.update_yaxes(title_text="acceptance rate", row=2, col=1)

    return fig


# ════════════════════════════════════════════════════════════════════
# Phase 5 Wave 5D: Comprehensive figure suite
# Paper 6 update (vestigial MC), Paper 7 (chirality), categorical
# ════════════════════════════════════════════════════════════════════


def fig_vestigial_binder_crossing() -> go.Figure:
    """Binder cumulant U₄ vs coupling at L=4,6,8 from production MC.

    Shows Binder cumulants for tetrad and metric order parameters.
    Crossing points between different L values indicate phase transitions.
    """
    import json
    import os

    data_dir = os.path.join(os.path.dirname(__file__), '..', '..',
                           'docs', 'vestigial_mc_results')
    # Find the production run (largest file)
    files = sorted([f for f in os.listdir(data_dir) if f.endswith('.json')],
                  key=lambda f: os.path.getsize(os.path.join(data_dir, f)),
                  reverse=True)
    with open(os.path.join(data_dir, files[0])) as f:
        mc = json.load(f)

    fig = make_subplots(rows=1, cols=2,
                        subplot_titles=["Tetrad Binder U₄", "Metric Binder U₄"])

    L_colors = {4: COLORS['Steinhauer'], 6: COLORS['Heidelberg'], 8: COLORS['Trento']}

    for L_str, scan in mc['binder_crossing']['data'].items():
        L = int(L_str)
        color = L_colors.get(L, '#666666')
        fig.add_trace(go.Scatter(
            x=scan['g_EH_values'], y=scan['binder_tetrad'],
            mode='lines+markers', name=f'L={L}',
            line=dict(color=color, width=2), marker=dict(size=3),
            legendgroup=f'L{L}', showlegend=True,
        ), row=1, col=1)
        fig.add_trace(go.Scatter(
            x=scan['g_EH_values'], y=scan['binder_metric'],
            mode='lines+markers', name=f'L={L}',
            line=dict(color=color, width=2), marker=dict(size=3),
            legendgroup=f'L{L}', showlegend=False,
        ), row=1, col=2)

    apply_layout(fig, height=400, width=900,
        title=dict(text="<b>Vestigial MC: Binder Cumulants vs Coupling (L=4,6,8)</b>",
                   font=TITLE_FONT))
    fig.update_xaxes(title_text="g<sub>EH</sub>", row=1, col=1)
    fig.update_xaxes(title_text="g<sub>EH</sub>", row=1, col=2)
    fig.update_yaxes(title_text="U₄ (tetrad)", row=1, col=1)
    fig.update_yaxes(title_text="U₄ (metric)", row=1, col=2)
    return fig


def fig_vestigial_susceptibility_split() -> go.Figure:
    """Susceptibility peaks for tetrad and metric at L=4,6,8.

    The split transition: tetrad and metric peaks at different couplings
    indicates a vestigial metric phase between pre-geometric and full tetrad.
    """
    import json, os
    from src.core.constants import DRINFELD_DOUBLE  # just for import test

    data_dir = os.path.join(os.path.dirname(__file__), '..', '..',
                           'docs', 'vestigial_mc_results')
    files = sorted([f for f in os.listdir(data_dir) if f.endswith('.json')],
                  key=lambda f: os.path.getsize(os.path.join(data_dir, f)),
                  reverse=True)
    with open(os.path.join(data_dir, files[0])) as f:
        mc = json.load(f)

    peaks = mc['finite_size_scaling']['susceptibility_peaks']
    L_values = sorted([int(k) for k in peaks.keys()])

    fig = go.Figure()
    fig.add_trace(go.Bar(
        x=[f'L={L}' for L in L_values],
        y=[peaks[str(L)]['tetrad_peak_coupling'] for L in L_values],
        name='Tetrad χ peak',
        marker_color=COLORS['Steinhauer'],
        width=0.35, offset=-0.18,
    ))
    fig.add_trace(go.Bar(
        x=[f'L={L}' for L in L_values],
        y=[peaks[str(L)]['metric_peak_coupling'] for L in L_values],
        name='Metric χ peak',
        marker_color=COLORS['Heidelberg'],
        width=0.35, offset=0.18,
    ))

    # Add split annotation at L=8
    if len(L_values) >= 3:
        L8 = str(L_values[-1])
        t_peak = peaks[L8]['tetrad_peak_coupling']
        m_peak = peaks[L8]['metric_peak_coupling']
        if abs(t_peak - m_peak) > 0.05:
            fig.add_annotation(
                x=f'L={L_values[-1]}', y=max(t_peak, m_peak) + 0.15,
                text=f"Split: Δ={abs(m_peak-t_peak):.2f}",
                showarrow=True, arrowhead=2,
                font=dict(size=12, color='red', family=FONT['family']),
            )

    apply_layout(fig, height=450, width=600,
        title=dict(text="<b>Split Transition: Susceptibility Peaks at Different Couplings</b>",
                   font=TITLE_FONT),
        yaxis=dict(title="G/G<sub>c</sub> at susceptibility peak"),
        barmode='group')
    return fig


def fig_vestigial_phase_diagram_mc() -> go.Figure:
    """Mean-field phase diagram with MC susceptibility peaks overlaid."""
    import json
    from src.vestigial.phase_diagram import scan_coupling

    # Mean-field scan
    result = scan_coupling(
        method="mean_field", Lambda=1.0, N_f=4,
        coupling_range=(0.3, 3.0), n_points=60,
    )

    fig = go.Figure()

    # Mean-field order parameters
    fig.add_trace(go.Scatter(
        x=list(result.coupling_ratios),
        y=list(result.tetrad_values),
        mode="lines", name="MF Tetrad VEV",
        line=dict(color=COLORS['Steinhauer'], width=2),
    ))
    fig.add_trace(go.Scatter(
        x=list(result.coupling_ratios),
        y=list(result.metric_values),
        mode="lines", name="MF Metric correlator",
        line=dict(color=COLORS['Trento'], width=2),
    ))

    # Mean-field vestigial window shading
    fig.add_vrect(x0=0.8, x1=1.0, fillcolor=COLORS['Trento'],
                  opacity=0.1, line_width=0,
                  annotation_text="MF vestigial", annotation_position="top left")

    # MC susceptibility peaks from production data
    from pathlib import Path as _Path
    mc_path = _Path(__file__).resolve().parent.parent.parent / "docs" / "vestigial_mc_results" / "vestigial_mc_20260329T192611.json"
    if mc_path.exists():
        with open(mc_path) as f:
            mc_data = json.load(f)
        peaks = mc_data.get('finite_size_scaling', {}).get('susceptibility_peaks', {})
        markers = {'4': 'circle', '6': 'square', '8': 'diamond'}
        for L_str, pdata in peaks.items():
            t_peak = pdata['tetrad_peak_coupling']
            m_peak = pdata['metric_peak_coupling']
            fig.add_trace(go.Scatter(
                x=[t_peak], y=[0.02], mode='markers',
                marker=dict(symbol=markers.get(L_str, 'circle'), size=14,
                            color=COLORS['Steinhauer'], line=dict(width=2, color='black')),
                name=f'MC tetrad χ peak L={L_str}', showlegend=(L_str == '8'),
            ))
            fig.add_trace(go.Scatter(
                x=[m_peak], y=[0.04], mode='markers',
                marker=dict(symbol=markers.get(L_str, 'circle'), size=14,
                            color=COLORS['Heidelberg'], line=dict(width=2, color='black')),
                name=f'MC metric χ peak L={L_str}', showlegend=(L_str == '8'),
            ))

    fig.add_vline(x=1.0, line=dict(color="black", width=1, dash="dash"))

    apply_layout(fig, height=450, width=750,
        title=dict(text="<b>Phase Diagram: Mean-Field + MC Susceptibility Peaks</b>",
                   font=TITLE_FONT),
        xaxis=dict(title="G / G<sub>c</sub>"),
        yaxis=dict(title="Magnitude / Λ"),
        legend=dict(x=0.02, y=0.98, bgcolor="rgba(255,255,255,0.9)"),
    )
    return fig


def fig_gs_condition_formalization() -> go.Figure:
    """9 GS conditions with formalization status and TPF violation status.

    Color-coded: green = substantive Prop, yellow = well-typed axiom,
    red outline = violated by TPF.
    """
    from src.core.constants import GS_CONDITIONS, TPF_VIOLATIONS

    conditions = []
    statuses = []
    tpf_violated = []

    # Map conditions to formalization status
    formalization = {
        'C1': 'Substantive', 'C2': 'Substantive', 'C3': 'Substantive',
        'C4': 'Axiom', 'C5': 'Substantive', 'C6': 'Axiom',
        'I1': 'Substantive', 'I2': 'Substantive', 'I3': 'Substantive',
    }
    tpf_violations = {'C1', 'C2', 'I3'}  # clean violations
    tpf_conditional = {'C3'}  # conditional
    tpf_extra = {'dim'}  # extra-dimensional (not a GS condition per se)

    all_conds = list(GS_CONDITIONS['explicit'].keys()) + list(GS_CONDITIONS['implicit'].keys())
    for c in all_conds:
        conditions.append(c)
        statuses.append(formalization.get(c, 'Unknown'))
        tpf_violated.append(c in tpf_violations or c in tpf_conditional)

    colors = []
    for s, v in zip(statuses, tpf_violated):
        if v:
            colors.append(COLORS['Heidelberg'])  # Berry — violated
        elif s == 'Substantive':
            colors.append(COLORS['Steinhauer'])  # Steel blue — substantive
        else:
            colors.append(COLORS['Trento'])  # Amber — axiom

    fig = go.Figure(go.Bar(
        x=conditions, y=[1]*len(conditions),
        marker_color=colors,
        marker_line=dict(width=2, color='black'),
        text=[f"{s}<br>{'VIOLATED' if v else ''}" for s, v in zip(statuses, tpf_violated)],
        textposition='inside',
        textfont=dict(size=11, color='white', family=FONT['family']),
    ))

    apply_layout(fig, height=350, width=700,
        title=dict(text="<b>GS No-Go Conditions: Formalization & TPF Violation Status</b>",
                   font=TITLE_FONT),
        yaxis=dict(showticklabels=False, showgrid=False),
        xaxis=dict(title="Golterman-Shamir condition"))

    # Legend annotations
    for color, label, y in [(COLORS['Steinhauer'], 'Substantive Prop', 0.85),
                             (COLORS['Trento'], 'Well-typed Axiom', 0.75),
                             (COLORS['Heidelberg'], 'TPF Violated', 0.65)]:
        fig.add_annotation(x=0.98, y=y, xref='paper', yref='paper',
            text=f"<span style='color:{color}'>■</span> {label}",
            showarrow=False, font=dict(size=11, family=FONT['family']),
            xanchor='right')
    return fig


def fig_lean_theorem_summary() -> go.Figure:
    """Theorem counts per Lean module: manual vs Aristotle-proved."""
    modules = [
        ('LatticeHamiltonian', 28, 7), ('GoltermanShamir', 15, 7),
        ('TPFEvasion', 12, 0), ('KLinearCategory', 16, 4),
        ('SphericalCategory', 18, 7), ('FusionCategory', 14, 0),
        ('FusionExamples', 30, 7), ('VecG', 9, 6),
        ('DrinfeldDouble', 15, 2), ('GaugeEmergence', 14, 0),
    ]

    names = [m[0] for m in modules]
    manual = [m[1] - m[2] for m in modules]
    aristotle = [m[2] for m in modules]

    fig = go.Figure()
    fig.add_trace(go.Bar(name='Manual', x=names, y=manual,
                         marker_color=COLORS['Steinhauer']))
    fig.add_trace(go.Bar(name='Aristotle', x=names, y=aristotle,
                         marker_color=COLORS['Trento']))

    apply_layout(fig, height=450, width=800, barmode='stack',
        title=dict(text="<b>Phase 5 Lean Verification: Manual vs Aristotle Proofs</b>",
                   font=TITLE_FONT),
        yaxis=dict(title="Theorem count"),
        xaxis=dict(title="Lean module", tickangle=-45))
    return fig


def fig_category_hierarchy() -> go.Figure:
    """Categorical hierarchy: Mathlib existing → Wave 4A → 4B → 4C."""
    from src.core.constants import CATEGORY_HIERARCHY

    layers = [
        ('Mathlib (existing)', CATEGORY_HIERARCHY['mathlib_existing'], COLORS['Steinhauer']),
        ('Wave 4A (new)', CATEGORY_HIERARCHY['wave4a_new'], COLORS['Heidelberg']),
        ('Wave 4B (new)', CATEGORY_HIERARCHY['wave4b_new'], COLORS['Trento']),
    ]

    fig = go.Figure()
    for i, (label, items, color) in enumerate(layers):
        fig.add_trace(go.Bar(
            x=[label], y=[len(items)],
            name=label, marker_color=color,
            text=[f"{len(items)} structures<br>{'<br>'.join(items[:3])}{'...' if len(items) > 3 else ''}"],
            textposition='inside',
            textfont=dict(size=10, color='white', family=FONT['family']),
        ))

    apply_layout(fig, height=400, width=600,
        title=dict(text="<b>Categorical Infrastructure: What We Built</b>",
                   font=TITLE_FONT),
        yaxis=dict(title="Number of structures"),
        showlegend=False)
    return fig


def fig_fusion_rules_comparison() -> go.Figure:
    """Fusion rules comparison: Vec_Z2, Rep_S3, Fibonacci side by side."""
    import numpy as np
    from src.core.constants import FUSION_EXAMPLES

    examples = ['Vec_Z2', 'Rep_S3', 'Fibonacci']
    fig = make_subplots(rows=1, cols=3, subplot_titles=examples)

    for col, name in enumerate(examples, 1):
        ex = FUSION_EXAMPLES[name]
        if 'fusion_rules' not in ex:
            continue
        N = np.array(ex['fusion_rules'])
        n = ex['n_simples']
        labels = ex.get('simple_labels', [str(i) for i in range(n)])

        # Sum over output channel: total multiplicity matrix M_{ij} = Σ_k N^k_{ij}
        M = np.sum(N, axis=0)

        fig.add_trace(go.Heatmap(
            z=M, x=labels, y=labels,
            colorscale=[[0, 'white'], [1, COLORS['Steinhauer']]],
            showscale=(col == 3),
            text=M.astype(str), texttemplate='%{text}',
            textfont=dict(size=14),
        ), row=1, col=col)

    apply_layout(fig, height=350, width=900,
        title=dict(text="<b>Fusion Rules: Total Multiplicity Σ<sub>k</sub> N<sup>k</sup><sub>ij</sub></b>",
                   font=TITLE_FONT))
    for col in range(1, 4):
        fig.update_xaxes(title_text="j", row=1, col=col)
        fig.update_yaxes(title_text="i", row=1, col=col)
    return fig


def fig_fibonacci_f_matrix() -> go.Figure:
    """Fibonacci F-matrix heatmap showing golden ratio structure."""
    import numpy as np
    from src.core.constants import FUSION_EXAMPLES

    F = FUSION_EXAMPLES['Fibonacci']['F_matrix_tau']
    phi = (1 + np.sqrt(5)) / 2

    fig = go.Figure(go.Heatmap(
        z=F, x=['𝟙 channel', 'τ channel'], y=['𝟙 channel', 'τ channel'],
        colorscale='RdBu', zmid=0,
        text=[[f'{F[i,j]:.4f}' for j in range(2)] for i in range(2)],
        texttemplate='%{text}', textfont=dict(size=16),
    ))

    apply_layout(fig, height=400, width=450,
        title=dict(text=f"<b>Fibonacci F-matrix F<sup>τττ</sup><sub>τ</sub> (φ={(phi):.4f})</b>",
                   font=TITLE_FONT),
        xaxis=dict(title="Output channel"),
        yaxis=dict(title="Input channel"))
    return fig


def fig_drinfeld_anyon_spectrum() -> go.Figure:
    """Anyon content of Drinfeld doubles: D(Z/2) and D(S₃)."""
    from src.core.constants import DRINFELD_DOUBLE

    groups = ['Z2', 'Z3', 'S3']
    n_simples = [DRINFELD_DOUBLE[g]['n_simples'] for g in groups]
    dim_D = [DRINFELD_DOUBLE[g]['dim_D'] for g in groups]
    labels = ['D(ℤ/2)\ntoric code', 'D(ℤ/3)', 'D(S₃)\nnon-abelian']

    fig = make_subplots(rows=1, cols=2, subplot_titles=["# Anyons", "dim D(G)"])

    fig.add_trace(go.Bar(
        x=labels, y=n_simples,
        marker_color=[COLORS['Steinhauer'], COLORS['Heidelberg'], COLORS['Trento']],
        text=n_simples, textposition='outside',
        textfont=dict(size=14, family=FONT['family']),
    ), row=1, col=1)

    fig.add_trace(go.Bar(
        x=labels, y=dim_D,
        marker_color=[COLORS['Steinhauer'], COLORS['Heidelberg'], COLORS['Trento']],
        text=dim_D, textposition='outside',
        textfont=dict(size=14, family=FONT['family']),
    ), row=1, col=2)

    apply_layout(fig, height=400, width=750,
        title=dict(text="<b>Drinfeld Double: Anyon Spectrum & Algebra Dimension</b>",
                   font=TITLE_FONT),
        showlegend=False)
    fig.update_yaxes(title_text="# simple modules", row=1, col=1)
    fig.update_yaxes(title_text="dim D(G) = |G|²", row=1, col=2)
    return fig


def fig_layer123_bridge() -> go.Figure:
    """Three-layer architecture with formal verification at each level."""
    fig = go.Figure()

    layers = [
        ('Layer 1: Categorical', 'Vec_G → Z(Vec_G) ≅ Rep(D(G))',
         '116 theorems across 7 modules (KLinearCategory → GaugeEmergence)', COLORS['Trento'], 3),
        ('Layer 2: Gauge Theory', 'Gauge erasure: non-Abelian erased, U(1) survives',
         '11 theorems + 1 axiom (GaugeErasure.lean)', COLORS['Heidelberg'], 2),
        ('Layer 3: EFT / Hydro', 'SK-EFT: δ_diss, δ_disp, spectral predictions',
         '302 theorems + 1 axiom across 22 modules (Phases 1-5)', COLORS['Steinhauer'], 1),
    ]

    for name, physics, verification, color, y in layers:
        fig.add_trace(go.Bar(
            x=[1], y=[name], orientation='h',
            marker_color=color, marker_line=dict(width=2, color='black'),
            text=[f"<b>{physics}</b><br><i>{verification}</i>"],
            textposition='inside',
            textfont=dict(size=11, color='white', family=FONT['family']),
            showlegend=False,
        ))

    # Connection arrows (annotations)
    fig.add_annotation(x=0.5, y=1.5, text="↓ gauge emergence (Z(Vec_G))",
        showarrow=False, font=dict(size=11, color='black', family=FONT['family']))
    fig.add_annotation(x=0.5, y=0.5, text="↓ hydrodynamization (gauge erasure)",
        showarrow=False, font=dict(size=11, color='black', family=FONT['family']))

    apply_layout(fig, height=350, width=800,
        title=dict(text="<b>Three-Layer Architecture: Formally Verified End-to-End</b>",
                   font=TITLE_FONT),
        xaxis=dict(showticklabels=False, showgrid=False),
        yaxis=dict(showgrid=False),
        barmode='stack')
    return fig


def fig_tpf_evasion_architecture() -> go.Figure:
    """TPF evasion: 5 violations of GS conditions, assembled into synthesis."""
    violations = [
        ('I3: Finite-dim', 'ℓ²(ℤ) infinite-dim', 'rotor_hilbert_not_finite_dim'),
        ('C1: Smoothness', 'round(x) discontinuous', 'round_not_continuous_at_half'),
        ('C2: Fermion-only', 'Bosonic rotor L²(S¹)', 'tpf_violates_C2'),
        ('Extra-dim', '4+1D SPT slab', 'tpf_bulk_dimension'),
        ('C3: No bosons', 'Rotor Goldstone modes', 'C3 conditional'),
    ]

    names = [v[0] for v in violations]
    reasons = [v[1] for v in violations]
    theorems = [v[2] for v in violations]

    colors = [COLORS['Heidelberg']] * 4 + [COLORS['Trento']]  # last is conditional

    fig = go.Figure(go.Bar(
        y=names[::-1], x=[1]*5, orientation='h',
        marker_color=colors[::-1],
        marker_line=dict(width=2, color='black'),
        text=[f"<b>{r}</b><br><i>{t}</i>" for r, t in zip(reasons[::-1], theorems[::-1])],
        textposition='inside',
        textfont=dict(size=11, color='white', family=FONT['family']),
    ))

    apply_layout(fig, height=350, width=700,
        title=dict(text="<b>TPF Evasion: 5 GS Conditions Violated</b>",
                   font=TITLE_FONT),
        xaxis=dict(showticklabels=False, showgrid=False),
        yaxis=dict(showgrid=False))

    fig.add_annotation(x=0.5, y=-0.15, xref='paper', yref='paper',
        text="Master synthesis: tpf_outside_gs_scope_main (5-part conjunction, zero sorry)",
        showarrow=False, font=dict(size=11, family=FONT['family']))
    return fig


def fig_fock_exterior_algebra() -> go.Figure:
    """ExteriorAlgebra as fermionic Fock space: dim = 2^k."""
    import numpy as np

    k_values = list(range(1, 9))
    dims = [2**k for k in k_values]

    fig = go.Figure()
    fig.add_trace(go.Bar(
        x=[f'k={k}' for k in k_values], y=dims,
        marker_color=COLORS['Steinhauer'],
        text=[str(d) for d in dims], textposition='outside',
        textfont=dict(size=12, family=FONT['family']),
        name='dim(FockSpace k)', showlegend=True,
    ))

    fig.add_trace(go.Scatter(
        x=[f'k={k}' for k in k_values], y=dims,
        mode='lines', line=dict(color=COLORS['Trento'], width=2, dash='dot'),
        name='2^k', showlegend=True,
    ))

    apply_layout(fig, height=400, width=600,
        title=dict(text="<b>Fermionic Fock Space: dim(ExteriorAlgebra) = 2<sup>k</sup></b>",
                   font=TITLE_FONT),
        yaxis=dict(title="dim(FermionicFockSpace k)", type='log'),
        xaxis=dict(title="k (number of modes)"))

    fig.add_annotation(x=0.5, y=0.95, xref='paper', yref='paper',
        text="fock_space_finite_dim: proved by Aristotle via graded decomposition",
        showarrow=False, font=dict(size=10, family=FONT['family'], color='gray'))
    return fig


# ════════════════════════════════════════════════════════════════════
# Wave 6: Analytical Vestigial Susceptibility Figures
# ════════════════════════════════════════════════════════════════════

def fig_vestigial_susceptibility() -> go.Figure:
    """RPA metric susceptibility χ_g⁻¹(G) vs G/G_c.

    Shows the inverse susceptibility crossing zero at G_ves for multiple u_g values.
    The crossing point moves toward G_c as u_g decreases (exponentially narrow window).
    """
    from src.core.formulas import (
        adw_metric_susceptibility_inv, adw_critical_coupling
    )
    from src.core.constants import ADW_VESTIGIAL

    G_c = adw_critical_coupling(np.pi, 2)
    c_D = ADW_VESTIGIAL['c_D_trace']

    fig = go.Figure()

    # Multiple u_g values to show how window shifts
    u_g_values = [0.3, 0.5, 1.0, 2.0]
    colors = [COLORS['cross'], COLORS['dispersive'], COLORS['Rb87'], COLORS['K39']]

    G_over_Gc = np.linspace(0.01, 0.999, 500)

    for u_g, color in zip(u_g_values, colors):
        chi_inv = [adw_metric_susceptibility_inv(
            g * G_c, G_c, u_g, c_D, np.pi
        ) for g in G_over_Gc]
        fig.add_trace(go.Scatter(
            x=G_over_Gc, y=chi_inv,
            mode='lines', line=dict(color=color, width=2),
            name=f'u_g = {u_g}',
        ))

    # Zero line
    fig.add_hline(y=0, line=dict(color='black', width=1, dash='dash'))

    # Vertical line at G_c
    fig.add_vline(x=1.0, line=dict(color=COLORS['dissipative'], width=1, dash='dot'),
                  annotation_text="G_c", annotation_position="top right")

    apply_layout(fig, height=450, width=700,
        title=dict(text="<b>RPA Metric Susceptibility: Vestigial Transition</b>",
                   font=TITLE_FONT),
        xaxis=dict(title="G / G_c"),
        yaxis=dict(title="χ_g⁻¹(G)"),
        legend=dict(x=0.02, y=0.98, bgcolor='rgba(255,255,255,0.8)'))

    fig.add_annotation(x=0.5, y=0.02, xref='paper', yref='paper',
        text="χ_g⁻¹ = 0 defines G_ves (vestigial transition). Shaded: vestigial phase (metric ordered, tetrad disordered).",
        showarrow=False, font=dict(size=10, family=FONT['family'], color='gray'))
    return fig


def fig_vestigial_window() -> go.Figure:
    """Vestigial window G_ves/G_c vs u_g, showing exponential narrowness.

    Log-scale plot demonstrating BCS-like exponential scaling in d=4.
    """
    from src.core.formulas import adw_vestigial_critical_coupling, adw_critical_coupling
    from src.core.constants import ADW_VESTIGIAL

    G_c = adw_critical_coupling(np.pi, 2)
    c_D = ADW_VESTIGIAL['c_D_trace']

    fig = go.Figure()

    u_g_vals = np.linspace(0.1, 3.0, 200)
    G_ves_over_Gc = []
    window_width = []
    for u_g in u_g_vals:
        G_ves = adw_vestigial_critical_coupling(G_c, u_g, c_D, np.pi)
        ratio = G_ves / G_c if G_ves < G_c else 1.0
        G_ves_over_Gc.append(ratio)
        window_width.append(max(G_c - G_ves, 1e-300))

    # G_ves/G_c plot
    fig.add_trace(go.Scatter(
        x=u_g_vals, y=G_ves_over_Gc,
        mode='lines', line=dict(color=COLORS['Rb87'], width=2.5),
        name='G_ves / G_c (trace channel)',
    ))

    # Also show traceless-symmetric channel (c_D = 8)
    c_D_tl = ADW_VESTIGIAL['c_D_traceless']
    G_ves_tl = []
    for u_g in u_g_vals:
        G_ves = adw_vestigial_critical_coupling(G_c, u_g, c_D_tl, np.pi)
        ratio = G_ves / G_c if G_ves < G_c else 1.0
        G_ves_tl.append(ratio)

    fig.add_trace(go.Scatter(
        x=u_g_vals, y=G_ves_tl,
        mode='lines', line=dict(color=COLORS['Na23'], width=2, dash='dash'),
        name='G_ves / G_c (traceless-sym)',
    ))

    fig.add_hline(y=1.0, line=dict(color='black', width=1, dash='dot'),
                  annotation_text="G_c (tetrad condensation)")

    apply_layout(fig, height=450, width=700,
        title=dict(text="<b>Vestigial Window: Exponential Narrowness in d=4</b>",
                   font=TITLE_FONT),
        xaxis=dict(title="u_g (metric-channel quartic coupling)"),
        yaxis=dict(title="G_ves / G_c", range=[0, 1.05]),
        legend=dict(x=0.02, y=0.15, bgcolor='rgba(255,255,255,0.8)'))

    fig.add_annotation(x=0.5, y=0.02, xref='paper', yref='paper',
        text="BCS-like scaling: G_ves/G_c ~ 1 − exp(−16π²/(c_D·u_g)). Window only visible for u_g ≳ 0.3.",
        showarrow=False, font=dict(size=10, family=FONT['family'], color='gray'))
    return fig


def fig_vestigial_phase_diagram_analytical() -> go.Figure:
    """Analytical phase diagram: pre-geometric / vestigial / full-tetrad regions.

    Shows the three phases as a function of G/G_c with the vestigial window shaded.
    """
    from src.core.formulas import adw_vestigial_critical_coupling, adw_critical_coupling
    from src.core.constants import ADW_VESTIGIAL

    G_c = adw_critical_coupling(np.pi, 2)
    c_D = ADW_VESTIGIAL['c_D_trace']

    fig = go.Figure()

    # Phase boundaries vs u_g
    u_g_vals = np.linspace(0.1, 3.0, 200)
    G_ves_vals = []
    for u_g in u_g_vals:
        G_ves = adw_vestigial_critical_coupling(G_c, u_g, c_D, np.pi)
        G_ves_vals.append(G_ves / G_c if G_ves < G_c else 1.0)

    # G_c line (always at 1)
    fig.add_trace(go.Scatter(
        x=u_g_vals, y=[1.0] * len(u_g_vals),
        mode='lines', line=dict(color=COLORS['dissipative'], width=2),
        name='G_c (tetrad condensation)',
    ))

    # G_ves line
    fig.add_trace(go.Scatter(
        x=u_g_vals, y=G_ves_vals,
        mode='lines', line=dict(color=COLORS['Rb87'], width=2.5),
        name='G_ves (metric condensation)',
    ))

    # Shade vestigial region
    fig.add_trace(go.Scatter(
        x=list(u_g_vals) + list(reversed(u_g_vals)),
        y=G_ves_vals + [1.0] * len(u_g_vals),
        fill='toself', fillcolor='rgba(46,134,171,0.15)',
        line=dict(width=0), showlegend=True,
        name='Vestigial phase (metric ordered, tetrad disordered)',
    ))

    # Phase labels
    fig.add_annotation(x=1.5, y=0.3, text="<b>Pre-geometric</b><br>(fully disordered)",
        showarrow=False, font=dict(size=13, family=FONT['family']))
    fig.add_annotation(x=2.5, y=1.15, text="<b>Einstein-Cartan</b><br>(tetrad condensed)",
        showarrow=False, font=dict(size=13, family=FONT['family']))

    apply_layout(fig, height=500, width=700,
        title=dict(text="<b>ADW Phase Diagram: Vestigial Metric Ordering</b>",
                   font=TITLE_FONT),
        xaxis=dict(title="u_g (metric-channel quartic coupling)", range=[0.1, 3.0]),
        yaxis=dict(title="G / G_c", range=[0, 1.3]),
        legend=dict(x=0.02, y=0.98, bgcolor='rgba(255,255,255,0.8)'))

    fig.add_annotation(x=0.5, y=-0.12, xref='paper', yref='paper',
        text="Volovik (2024): EP violated in vestigial phase — bosons see metric, fermions don't.",
        showarrow=False, font=dict(size=10, family=FONT['family'], color='gray'))
    return fig


# ============================================================
# Phase 5a: GT Lattice Chiral Fermion + Chirality Wall
# ============================================================


def fig_gt_band_structure() -> go.Figure:
    """GT BdG band structure along high-symmetry path in the Brillouin zone.

    Shows the 4 BdG energy bands for the Gioia-Thorngren single-Weyl
    construction. The key feature: exactly one gapless Weyl node at k=0
    (Gamma), while all doublers at zone boundary are gapped by the Wilson mass.

    Lean: wilson_mass_zero_iff_cos_eq_one (WilsonMass.lean)
    """
    from src.chirality.gioia_thorngren import bdg_hamiltonian_fast, band_structure

    # High-symmetry path: Gamma -> X -> M -> Gamma -> R
    N = 200
    paths = {
        'Gamma-X': np.column_stack([np.linspace(0, np.pi, N), np.zeros(N), np.zeros(N)]),
        'X-M': np.column_stack([np.full(N, np.pi), np.linspace(0, np.pi, N), np.zeros(N)]),
        'M-Gamma': np.column_stack([np.linspace(np.pi, 0, N), np.linspace(np.pi, 0, N), np.zeros(N)]),
        'Gamma-R': np.column_stack([np.linspace(0, np.pi, N), np.linspace(0, np.pi, N), np.linspace(0, np.pi, N)]),
    }

    fig = go.Figure()
    x_offset = 0
    tick_positions = [0]
    tick_labels = ['Gamma']

    for seg_name, k_path in paths.items():
        bands = band_structure(k_path, r=1.0)
        x = np.linspace(x_offset, x_offset + 1, len(k_path))

        for b in range(4):
            fig.add_trace(go.Scatter(
                x=x, y=bands[:, b],
                mode='lines',
                line=dict(color=COLORS['Rb87'] if b < 2 else COLORS['K39'], width=1.5),
                showlegend=(seg_name == 'Gamma-X' and b in [0, 2]),
                name='Valence' if b < 2 else 'Conduction',
            ))

        x_offset += 1
        label = seg_name.split('-')[1]
        tick_positions.append(x_offset)
        tick_labels.append(label)

    # Mark Weyl node at Gamma
    fig.add_annotation(x=0, y=0, text='<b>Weyl node</b>', showarrow=True,
        arrowhead=2, ax=50, ay=-40, font=dict(size=13, color=COLORS['dissipative']))

    # Vertical segment dividers
    for pos in tick_positions[1:-1]:
        fig.add_vline(x=pos, line_dash='dot', line_color='rgba(0,0,0,0.3)')

    apply_layout(fig, height=450, width=700,
        title=dict(text='<b>GT BdG Band Structure (r=1)</b>', font=TITLE_FONT),
        xaxis=dict(title='', tickvals=tick_positions, ticktext=tick_labels),
        yaxis=dict(title='Energy (arb. units)'),
        legend=dict(x=0.02, y=0.98))
    return fig


def fig_wilson_mass_bz() -> go.Figure:
    """Wilson mass M(k) on the kz=0 plane of the Brillouin zone.

    Heatmap showing M(kx,ky,0) = 3 - cos(kx) - cos(ky) - 1. The single
    zero at kx=ky=0 (the Weyl node) is clearly visible. All doublers
    at zone boundary are gapped (M > 0).

    Lean: wilson_mass_nonneg, wilson_mass_pos_of_ne_zero (WilsonMass.lean)
    """
    from src.core.formulas import gt_wilson_mass

    N = 100
    kx = np.linspace(-np.pi, np.pi, N)
    ky = np.linspace(-np.pi, np.pi, N)
    KX, KY = np.meshgrid(kx, ky)
    M = np.vectorize(lambda x, y: gt_wilson_mass(x, y, 0)['mass'])(KX, KY)

    fig = go.Figure(data=go.Heatmap(
        z=M, x=kx, y=ky,
        colorscale=[[0, '#FFFFFF'], [0.01, '#DAE2F8'], [0.5, COLORS['Rb87']], [1, '#1A1A2E']],
        colorbar=dict(title='M(k)'),
        hovertemplate='kx=%{x:.2f}, ky=%{y:.2f}<br>M=%{z:.3f}<extra></extra>',
    ))

    # Mark Weyl node
    fig.add_trace(go.Scatter(
        x=[0], y=[0], mode='markers',
        marker=dict(size=14, color=COLORS['Na23'], symbol='x', line=dict(width=3, color=COLORS['Na23'])),
        name='Weyl node (M=0)', showlegend=True,
    ))

    apply_layout(fig, height=500, width=550,
        title=dict(text='<b>Wilson Mass M(kx,ky,0)</b>', font=TITLE_FONT),
        xaxis=dict(title='kx', range=[-np.pi, np.pi]),
        yaxis=dict(title='ky', range=[-np.pi, np.pi], scaleanchor='x'))
    return fig


def fig_chiral_charge_spectrum() -> go.Figure:
    """Chiral charge eigenvalues ±cos(p3/2) as a function of p3.

    Shows the non-compact (continuous, non-integer) spectrum of Q_A,
    demonstrating violation of GS condition I3 (compact spectrum).
    Also shows the Ginsparg-Wilson norm cos^2(p3/2).

    Lean: chiral_charge_noncompact, chiral_charge_range (BdGHamiltonian.lean)
    """
    p3 = np.linspace(-np.pi, np.pi, 300)
    ev_plus = np.cos(p3 / 2)
    ev_minus = -np.cos(p3 / 2)
    gw_norm = np.cos(p3 / 2) ** 2

    fig = make_subplots(rows=1, cols=2, subplot_titles=[
        'Chiral charge eigenvalues', 'Ginsparg-Wilson norm'])

    fig.add_trace(go.Scatter(x=p3, y=ev_plus, mode='lines',
        line=dict(color=COLORS['Rb87'], width=2), name='+cos(p3/2)'), row=1, col=1)
    fig.add_trace(go.Scatter(x=p3, y=ev_minus, mode='lines',
        line=dict(color=COLORS['K39'], width=2), name='-cos(p3/2)'), row=1, col=1)
    # Integer grid lines to show non-quantization
    for val in [-1, 0, 1]:
        fig.add_hline(y=val, line_dash='dot', line_color='rgba(0,0,0,0.2)', row=1, col=1)

    fig.add_trace(go.Scatter(x=p3, y=gw_norm, mode='lines',
        line=dict(color=COLORS['dispersive'], width=2), name='cos^2(p3/2)'), row=1, col=2)
    fig.add_hline(y=1, line_dash='dot', line_color='rgba(0,0,0,0.2)', row=1, col=2)

    apply_layout(fig, height=400, width=800,
        title=dict(text='<b>GT Chiral Charge: Non-Compact Spectrum</b>', font=TITLE_FONT))
    fig.update_xaxes(title_text='p3', row=1, col=1)
    fig.update_xaxes(title_text='p3', row=1, col=2)
    fig.update_yaxes(title_text='Eigenvalue', row=1, col=1)
    fig.update_yaxes(title_text='q_A^2 norm', row=1, col=2)
    return fig


def fig_gt_commutator_verification() -> go.Figure:
    """Numerical verification of [H_BdG(k), q_A(k)] = 0 on a finite lattice.

    Shows |[H,Q_A]|_max at each k-point for L=8, demonstrating that the
    commutator is at machine epsilon (~10^-16) everywhere. This is the
    numerical mirror of the Lean theorem gt_commutation_4x4.

    Lean: gt_commutation_4x4, gt_tau_commutator_vanishes (GTCommutation.lean)
    """
    from src.chirality.gioia_thorngren import (
        brillouin_zone, bdg_hamiltonian_fast, chiral_charge_4x4,
    )

    L = 8
    k = brillouin_zone(L)
    H = bdg_hamiltonian_fast(k, r=1.0)
    Q = chiral_charge_4x4(k)
    comm = H @ Q - Q @ H
    norms = np.max(np.abs(comm), axis=(1, 2))

    fig = go.Figure()
    fig.add_trace(go.Scatter(
        x=np.arange(len(norms)), y=norms,
        mode='markers',
        marker=dict(size=3, color=COLORS['Rb87']),
        name='|[H(k), Q_A(k)]|_max',
    ))
    fig.add_hline(y=1e-14, line_dash='dash', line_color=COLORS['dissipative'],
        annotation_text='machine epsilon', annotation_position='top right')

    apply_layout(fig, height=400, width=700,
        title=dict(text=f'<b>[H, Q_A] = 0 Verification (L={L}, {L**3} k-points)</b>',
                   font=TITLE_FONT),
        xaxis=dict(title='k-point index'),
        yaxis=dict(title='Max |commutator entry|', type='log',
                   range=[-17, -13]))
    return fig


def fig_chirality_wall_three_pillars() -> go.Figure:
    """Overview of the three-pillar chirality wall formal verification.

    Structured diagram showing:
      Pillar 1 (red): GS no-go — 9 conditions, 5 TPF violations
      Pillar 2 (blue): GT construction — [H,Q_A]=0, non-on-site, 1 Weyl
      Pillar 3 (green): Z16 + Onsager — anomaly classification

    With bridge connections between pillars.

    Lean: chirality_wall_assessment (ChiralityWallMaster.lean)
    """
    fig = go.Figure()

    # Three pillars as colored boxes
    pillars = [
        {'x': 0.15, 'color': COLORS['dissipative'], 'title': 'Pillar 1: No-Go',
         'items': ['GS: 9 conditions', '5 violated by TPF', '14 theorems (GS)', '12 theorems (TPF)']},
        {'x': 0.50, 'color': COLORS['Rb87'], 'title': 'Pillar 2: GT Construction',
         'items': ['[H, Q_A] = 0 verified', 'Non-on-site (R=1)', '1 Weyl node', '56 theorems (Wave 2)']},
        {'x': 0.85, 'color': COLORS['Na23'], 'title': 'Pillar 3: Anomaly',
         'items': ['Onsager (DG=16)', 'O → su(2) contraction', 'Z16 axiom + A(1)', '87 theorems (W1+3)']},
    ]

    for p in pillars:
        # Box
        fig.add_shape(type='rect',
            x0=p['x'] - 0.13, x1=p['x'] + 0.13, y0=0.15, y1=0.85,
            fillcolor=p['color'], opacity=0.12,
            line=dict(color=p['color'], width=2))
        # Title
        fig.add_annotation(x=p['x'], y=0.92, text=f"<b>{p['title']}</b>",
            showarrow=False, font=dict(size=15, color=p['color'], family=FONT['family']))
        # Items
        for i, item in enumerate(p['items']):
            fig.add_annotation(x=p['x'], y=0.72 - i * 0.14, text=item,
                showarrow=False, font=dict(size=13, family=FONT['family']))

    # Bridge arrows
    fig.add_annotation(x=0.33, y=0.50, ax=0.15 + 0.13, ay=0.50,
        text='GS evasion', showarrow=True, arrowhead=2, arrowcolor='gray',
        font=dict(size=10, color='gray'))
    fig.add_annotation(x=0.67, y=0.50, ax=0.50 + 0.13, ay=0.50,
        text='Anomaly protection', showarrow=True, arrowhead=2, arrowcolor='gray',
        font=dict(size=10, color='gray'))

    # Summary bar
    fig.add_annotation(x=0.50, y=0.03,
        text='<b>900 theorems + 2 axioms | 58 Lean modules | zero sorry | 254 Aristotle-proved</b>',
        showarrow=False, font=dict(size=14, family=FONT['family']))

    fig.update_layout(
        height=500, width=800,
        title=dict(text='<b>Chirality Wall: Three-Pillar Formal Verification</b>',
                   font=TITLE_FONT, x=0.5),
        xaxis=dict(visible=False, range=[0, 1]),
        yaxis=dict(visible=False, range=[0, 1]),
        plot_bgcolor='white', paper_bgcolor='white',
        margin=dict(l=20, r=20, t=60, b=40),
    )
    return fig


# ════════════════════════════════════════════════════════════════════
# Phase 5b: SM Anomaly in ℤ₁₆
# ════════════════════════════════════════════════════════════════════

def fig_sm_fermion_z16_anomaly() -> go.Figure:
    """SM fermion anomaly contributions in ℤ₁₆.

    Bar chart showing each SM fermion's component count (= anomaly contribution).
    Stacked to show the total of 16 (with ν_R) or 15 (without).
    The ℤ₁₆ cancellation boundary at 16 is shown as a dashed line.

    Lean: total_anomaly_with_nu_R, total_anomaly_without_nu_R (SMFermionData.lean)
    """
    from src.core.constants import SM_FERMION_DATA

    names = []
    components = []
    colors = []
    fermion_colors = {
        'Q_L': COLORS['Rb87'],        # blue — quarks
        'u_R_bar': COLORS['Rb87'],
        'd_R_bar': COLORS['Rb87'],
        'L': COLORS['Na23'],           # amber — leptons
        'e_R_bar': COLORS['Na23'],
        'nu_R_bar': COLORS['dispersive'],  # green — ν_R (hidden sector candidate)
    }

    for name, f in SM_FERMION_DATA.items():
        names.append(f['label'].split('(')[0].strip())
        components.append(f['components'])
        colors.append(fermion_colors[name])

    fig = go.Figure()

    # Cumulative bar
    cumulative = 0
    for i, (n, c, col) in enumerate(zip(names, components, colors)):
        fig.add_trace(go.Bar(
            x=[c], y=['SM Fermions'], orientation='h',
            base=cumulative,
            marker_color=col, marker_line=dict(color='white', width=1),
            text=f'{n}<br>({c})', textposition='inside',
            textfont=dict(size=13, color='white', family=FONT['family']),
            showlegend=False,
            hovertemplate=f'{n}: {c} components<extra></extra>',
        ))
        cumulative += c

    # ℤ₁₆ boundary
    fig.add_vline(x=16, line=dict(color=COLORS['dissipative'], width=2.5, dash='dash'),
                  annotation=dict(text='ℤ₁₆ boundary (16)', font=dict(size=13, color=COLORS['dissipative'])))

    # Without ν_R marker
    fig.add_vline(x=15, line=dict(color=COLORS['cross'], width=1.5, dash='dot'),
                  annotation=dict(text='Without ν_R (15)', font=dict(size=12, color=COLORS['cross']),
                                  yshift=-25))

    fig.update_layout(
        height=250, width=700,
        title=dict(text='<b>SM Fermion Anomaly Contributions in ℤ₁₆</b>',
                   font=TITLE_FONT, x=0.5),
        xaxis=dict(title=dict(text='Cumulative Weyl Fermion Components',
                             font=dict(size=14, family=FONT['family'])),
                   range=[0, 19], tickfont=dict(size=13, family=FONT['family'])),
        yaxis=dict(visible=False),
        plot_bgcolor='white', paper_bgcolor='white',
        margin=dict(l=20, r=20, t=60, b=50),
        barmode='stack',
    )
    return fig


def fig_sm_generation_anomaly() -> go.Figure:
    """Anomaly index vs number of generations.

    Shows how the ℤ₁₆ anomaly depends on the number of fermion generations,
    for both the SM with and without right-handed neutrinos.

    Lean: three_gen_anomalous (Z16AnomalyComputation.lean)
    """
    from src.core.formulas import sm_three_gen_anomaly

    n_gens = list(range(1, 17))
    anomaly_with = [(n * 16) % 16 for n in n_gens]
    anomaly_without = [(n * 15) % 16 for n in n_gens]

    fig = go.Figure()

    fig.add_trace(go.Scatter(
        x=n_gens, y=anomaly_with,
        mode='markers+lines',
        marker=dict(size=10, color=COLORS['Rb87']),
        line=dict(color=COLORS['Rb87'], width=2),
        name='With ν_R (16 per gen)',
    ))

    fig.add_trace(go.Scatter(
        x=n_gens, y=anomaly_without,
        mode='markers',
        marker=dict(size=11, color=COLORS['Na23'], symbol='diamond'),
        name='Without ν_R (15 per gen)',
    ))

    # Highlight N_f = 3
    fig.add_vline(x=3, line=dict(color=COLORS['cross'], width=1, dash='dot'))
    fig.add_annotation(x=3, y=14, text='N_f = 3<br>(observed)',
        showarrow=False, font=dict(size=12, color=COLORS['cross'], family=FONT['family']))

    # Anomaly-free line
    fig.add_hline(y=0, line=dict(color='black', width=0.5, dash='dash'))
    fig.add_annotation(x=15, y=0.8, text='Anomaly-free',
        showarrow=False, font=dict(size=11, color='gray', family=FONT['family']))

    fig.update_layout(
        height=400, width=700,
        title=dict(text='<b>ℤ₁₆ Anomaly Index vs Generation Count</b>',
                   font=TITLE_FONT, x=0.5),
        xaxis=dict(title=dict(text='Number of Generations (N_f)',
                             font=dict(size=14, family=FONT['family'])),
                   dtick=1, tickfont=dict(size=13, family=FONT['family'])),
        yaxis=dict(title=dict(text='Anomaly Index (mod 16)',
                             font=dict(size=14, family=FONT['family'])),
                   range=[-1, 16], dtick=2, tickfont=dict(size=13, family=FONT['family'])),
        legend=dict(x=0.55, y=0.95, font=dict(size=13, family=FONT['family'])),
        plot_bgcolor='white', paper_bgcolor='white',
    )
    return fig


def fig_sm_generation_constraint() -> go.Figure:
    """Generation constraint N_f ≡ 0 mod 3 visualization.

    Shows c₋ = 8N_f vs the modular invariance requirement c₋ ≡ 0 mod 24.
    Highlights which values of N_f satisfy the constraint.

    Lean: generation_mod3_constraint (GenerationConstraint.lean)
    """
    from src.core.formulas import sm_generation_constraint

    n_f_values = list(range(0, 10))
    c_minus = [8 * n for n in n_f_values]
    satisfies = [sm_generation_constraint(n)['satisfies_generation_constraint']
                 for n in n_f_values]

    fig = go.Figure()

    # All points
    fig.add_trace(go.Bar(
        x=n_f_values, y=c_minus,
        marker_color=[COLORS['Rb87'] if s else COLORS['cross'] for s in satisfies],
        text=[f'c₋={c}' for c in c_minus],
        textposition='outside',
        textfont=dict(size=12, family=FONT['family']),
        showlegend=False,
        hovertemplate='N_f=%{x}<br>c₋=%{y}<br>Satisfies: %{customdata}<extra></extra>',
        customdata=['Yes' if s else 'No' for s in satisfies],
    ))

    # Modular invariance lines at multiples of 24
    for mult in [24, 48, 72]:
        fig.add_hline(y=mult, line=dict(color=COLORS['Rb87'], width=1, dash='dash'),
                      annotation=dict(text=f'c₋ = {mult}', x=0.98,
                                      font=dict(size=11, color=COLORS['Rb87'])))

    fig.update_layout(
        height=400, width=600,
        title=dict(text='<b>Generation Constraint: c₋ = 8N_f ≡ 0 mod 24</b>',
                   font=TITLE_FONT, x=0.5),
        xaxis=dict(title=dict(text='Number of Generations (N_f)',
                             font=dict(size=14, family=FONT['family'])),
                   dtick=1, tickfont=dict(size=13, family=FONT['family'])),
        yaxis=dict(title=dict(text='Chiral Central Charge (c₋)',
                             font=dict(size=14, family=FONT['family'])),
                   tickfont=dict(size=13, family=FONT['family'])),
        plot_bgcolor='white', paper_bgcolor='white',
    )
    return fig


def fig_drinfeld_equivalence_structure() -> go.Figure:
    """Z(Vec_G) ≅ Rep(D(G)) equivalence: anyon content for concrete groups.

    Shows the anyon/simple-module content for Z/2 (toric code, 4 anyons)
    and S₃ (8 non-abelian anyons), verifying D² = |G|² on both sides.
    Quantum dimensions displayed as bar heights, with D² totals annotated.

    Data from: ToricCodeCenter.lean (25 thms), S3CenterAnyons.lean (22 thms),
    DrinfeldEquivalence.lean (12 thms).
    """
    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=["Z(Vec<sub>ℤ/2</sub>) — Toric Code (4 anyons)",
                        "Z(Vec<sub>S₃</sub>) — 8 Non-Abelian Anyons"],
        horizontal_spacing=0.15,
    )

    # === Panel 1: Z/2 toric code ===
    z2_labels = ["1 (vacuum)", "e (electric)", "m (magnetic)", "ε (fermion)"]
    z2_dims = [1, 1, 1, 1]  # all dimension 1
    z2_colors = [COLORS["Rb87"]] * 4  # steel blue

    fig.add_trace(go.Bar(
        x=z2_labels, y=z2_dims,
        marker_color=z2_colors,
        text=["d=1"] * 4,
        textposition="outside",
        textfont=dict(size=13),
        showlegend=False,
    ), row=1, col=1)

    # D² annotation
    fig.add_annotation(
        x=1.5, y=1.3,
        text="D² = 4 = |ℤ/2|²",
        showarrow=False, font=dict(size=13, color=COLORS["Rb87"],
                                    family=FONT['family']),
        row=1, col=1,
    )

    # R(e,m) = -1 annotation — prominent for publication
    fig.add_annotation(
        x=1.5, y=0.4,
        text="<b>R(e,m) = −1</b>",
        showarrow=False, font=dict(size=14, color=COLORS["dissipative"],
                                    family=FONT['family']),
        row=1, col=1,
    )

    # === Panel 2: S₃ non-abelian ===
    s3_labels = ["A₁", "A₂", "A₃", "B₁", "B₂", "C₁", "C₂", "C₃"]
    s3_dims = [1, 1, 2, 3, 3, 2, 2, 2]
    s3_classes = ["e", "e", "e", "(12)", "(12)", "(123)", "(123)", "(123)"]
    s3_colors = [COLORS["Rb87"] if c == "e"
                 else COLORS["Na23"] if c == "(12)"
                 else COLORS["K39"]
                 for c in s3_classes]

    fig.add_trace(go.Bar(
        x=s3_labels, y=s3_dims,
        marker_color=s3_colors,
        text=[f"d={d}" for d in s3_dims],
        textposition="outside",
        textfont=dict(size=13),
        showlegend=False,
    ), row=1, col=2)

    # D² annotation
    fig.add_annotation(
        x=3.5, y=3.5,
        text="D² = 36 = |S₃|²",
        showarrow=False, font=dict(size=13, color=COLORS["K39"],
                                    family=FONT['family']),
        row=1, col=2,
    )

    # Class legend
    for i, (label, color) in enumerate([
        ("{e} class", COLORS["Rb87"]),
        ("(12) class", COLORS["Na23"]),
        ("(123) class", COLORS["K39"]),
    ]):
        fig.add_trace(go.Bar(
            x=[None], y=[None],
            marker_color=color,
            name=label,
            showlegend=True,
        ))

    fig.update_layout(
        title=dict(text="Drinfeld Center Equivalence: Z(Vec<sub>G</sub>) ≅ Rep(D(G))",
                   font=TITLE_FONT),
        font=FONT,
        plot_bgcolor='white', paper_bgcolor='white',
        legend=dict(x=0.75, y=0.95, bgcolor='rgba(255,255,255,0.8)'),
        height=400, width=900,
        barmode='group',
    )
    fig.update_yaxes(title_text="Quantum Dimension d", range=[0, 4], row=1, col=1)
    fig.update_yaxes(title_text="Quantum Dimension d", range=[0, 4.2], row=1, col=2)

    return fig


if __name__ == "__main__":
    main()
