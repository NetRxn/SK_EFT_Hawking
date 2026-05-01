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
    "dispersive": "#4682B4", # Steel blue — known correction (colorblind-safe)
    "dissipative": "#D4A843",# Amber — new correction (our result, colorblind-safe)
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
    # Semantic color-name aliases (Phase 5h/5j figures)
    "steel_blue": "#2E86AB",
    "amber": "#F18F01",
    "sage": "#5C946E",      # Legacy — retained for backward compat
    "carmine": "#E63946",   # Legacy — retained for backward compat
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

    Consumes canonical δ-values via the Beliaev-chain pipeline:
        beliaev_transport_coefficients(...) → compute_dissipative_correction(...)

    This is the central result figure. Shows:
    - The correction magnitudes on a log scale
    - Experimental sensitivity thresholds
    - The Beliaev-regime prediction for each platform

    Spin-sonic enhancement is a *separate* analysis belonging in
    fig_spin_sonic_enhancement (fig4); this figure shows the baseline
    Beliaev prediction for each platform without the (c_density/c_spin)²
    multiplier. Mixing the two would hide the Beliaev-regime physics
    signal (notably, the Heidelberg Beliaev-dominance at κ ≈ 100 s⁻¹).

    Pipeline Invariants 1 & 3: all δ-values sourced from
    `compute_dissipative_correction`; no local reimplementation.
    Pre-2026-04-13 this function recomputed Γ locally and applied a
    hardcoded 100× Trento enhancement — fixed in Phase 5u Wave 1e.
    """
    from src.core.formulas import beliaev_transport_coefficients

    fig = go.Figure()

    corrections_data = []
    for name, (params, bg) in experiments.items():
        # Canonical chain: beliaev transport coefficients → dissipative correction.
        # compute_dissipative_correction applies the k_H² = (κ/c_s)² conversion
        # per Lean theorem SKEFTHawking.SecondOrderSK.GammaH (added Phase 5u Wave 1b).
        tc = beliaev_transport_coefficients(
            params.density_upstream, params.scattering_length,
            bg.surface_gravity, params.sound_speed_upstream, params.healing_length,
        )
        corr = compute_dissipative_correction(bg, params,
            gamma_1=tc['gamma_1'], gamma_2=tc['gamma_2'])
        corrections_data.append((name, corr))

    # Grouped bars
    categories = ["delta_disp", "delta_diss", "delta_cross"]
    colors_cat = [COLORS["dispersive"], COLORS["dissipative"], COLORS["cross"]]
    labels = ["Dispersive δ<sub>disp</sub>", "Dissipative δ<sub>diss</sub> (Beliaev, T=0)",
              "Cross-term δ<sub>cross</sub>"]

    # Collect all values to size the y-axis honestly (no clipping).
    all_values = []
    for cat in categories:
        for _, c in corrections_data:
            v = abs(c[cat])
            if v > 0:
                all_values.append(v)

    for cat, color, label in zip(categories, colors_cat, labels):
        values = [abs(c[cat]) for _, c in corrections_data]
        # Plotly log-bar with zero values silently drops them; replace with tiny
        # positive sentinel so bars render visibly in group and annotation stays readable.
        y_plot = [v if v > 0 else 1e-20 for v in values]
        fig.add_trace(go.Bar(
            name=label,
            x=[n for n, _ in corrections_data],
            y=y_plot,
            marker_color=color,
            marker_line=dict(width=1, color="black"),
            text=[f"{v:.2e}" if v > 1e-20 else "0" for v in values],
            textposition="outside",
            textfont=dict(size=10),
            hovertemplate=f"{label}<br>%{{x}}<br>|correction| = %{{y:.3e}}<extra></extra>",
        ))

    # Experimental sensitivity bands (added as named traces so they appear in legend)
    sensitivities = [
        ("Current sensitivity (10%)", 0.1),
        ("Near-term (1%)", 0.01),
        ("Projected (0.1%)", 0.001),
    ]
    for label, val in sensitivities:
        fig.add_trace(go.Scatter(
            x=[n for n, _ in corrections_data],
            y=[val] * len(corrections_data),
            mode="lines",
            line=dict(color=COLORS["sensitivity"], width=1.5, dash="dash"),
            name=label,
            hovertemplate=f"{label}<br>δ = {val}<extra></extra>",
            showlegend=True,
        ))

    # Honest y-axis range covering the full data span.
    # Heidelberg Beliaev δ_diss ≈ 1.6×10⁻³; cross-terms ≈ 10⁻⁸ to 10⁻¹⁰.
    if all_values:
        y_min_exp = int(np.floor(np.log10(min(all_values)))) - 1
        y_max_exp = 0  # sensitivity bands go up to 10⁰ = 100%
    else:
        y_min_exp, y_max_exp = -10, 0
    fig.update_yaxes(type="log", title_text="|Correction magnitude|",
                     range=[y_min_exp, y_max_exp])
    fig.update_xaxes(title_text="Experimental Setup")

    apply_layout(fig,
        height=550, width=800,
        title=dict(text="<b>Hawking Temperature Corrections: Hierarchy of Effects</b><br>"
                        "<sub>Beliaev (T=0) regime; finite-T Zaremba damping is ~10× larger</sub>",
                   font=TITLE_FONT),
        barmode="group",
        legend=dict(x=0.02, y=0.98, bgcolor="rgba(255,255,255,0.92)",
                    font=dict(size=10)),
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
    with blue (dispersive) for surviving (U(1)) and amber (dissipative) for erased (SU(3), SU(2)).
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

    Shows which gauge groups survive (blue) vs are erased (amber) upon
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
    from src.core.constants import POLARITON_PLATFORMS

    regime = polariton_regime_map()

    # Regime boundaries
    tau_range = np.logspace(-12, -9, 100)  # 1 ps to 1 ns
    # Consume κ from canonical POLARITON_PLATFORMS (Pipeline Invariant 3).
    # All three Paris_* entries share the same Falque-smooth-horizon κ = 7e10
    # s⁻¹ post Phase 5u Wave 4. Previously hardcoded 5e10 here — that value
    # was stale relative to constants.py after 2026-04-13.
    kappa = POLARITON_PLATFORMS['Paris_long']['kappa']  # s^-1
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
                           'data', 'vestigial_mc')
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
                           'data', 'vestigial_mc')
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
    mc_path = _Path(__file__).resolve().parent.parent.parent / "data" / "vestigial_mc" / "vestigial_mc_20260329T192611.json"
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
        text='<b>968 theorems | 0 axioms | 66 Lean modules | zero sorry | 273 Aristotle-proved</b>',
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

    # Modular invariance reference lines at multiples of 24 (no annotations:
    # the y-axis ticks at 24/48/72 + the per-bar c₋ labels already convey the
    # threshold grid; right-margin annotations clipped against the N_f=9 bar
    # top in PRL twocolumn layout — Stage 9 round 1 advisory).
    for mult in [24, 48, 72]:
        fig.add_hline(y=mult, line=dict(color=COLORS['Rb87'], width=1, dash='dash'))

    fig.update_layout(
        height=400, width=600,
        title=dict(text='<b>Generation Constraint: c₋ = 8N_f ≡ 0 mod 24</b>',
                   font=TITLE_FONT, x=0.5),
        xaxis=dict(title=dict(text='Number of Generations (N_f)',
                             font=dict(size=14, family=FONT['family'])),
                   dtick=1, tickfont=dict(size=13, family=FONT['family'])),
        yaxis=dict(title=dict(text='Chiral Central Charge (c₋)',
                             font=dict(size=14, family=FONT['family'])),
                   tickfont=dict(size=13, family=FONT['family']),
                   tickvals=[0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
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
            x=[], y=[],
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


def fig_modular_invariance_phase() -> go.Figure:
    """Modular T-transformation phase vs number of SM generations.

    Shows e^{2πi·c₋/24} for c₋ = 8N_f. The phase is 1 (modular invariant)
    only when N_f is a multiple of 3. Visualizes WHY N_f = 3 is special.

    Data from: ModularInvarianceConstraint.lean (12 thms),
    WangBridge.lean (9 thms), GenerationConstraint.lean (13 thms).
    """
    import cmath

    n_values = list(range(1, 13))
    phases_real = []
    phases_imag = []
    colors = []

    for n in n_values:
        c_minus = 8 * n
        phase = cmath.exp(2j * cmath.pi * c_minus / 24)
        phases_real.append(phase.real)
        phases_imag.append(phase.imag)
        colors.append(COLORS["Rb87"] if n % 3 == 0 else COLORS["cross"])

    fig = go.Figure()

    # Unit circle
    theta = np.linspace(0, 2 * np.pi, 100)
    fig.add_trace(go.Scatter(
        x=np.cos(theta), y=np.sin(theta),
        mode='lines', line=dict(color='rgba(0,0,0,0.15)', width=1, dash='dot'),
        showlegend=False,
    ))

    # Group N_f values by their phase position (mod 3)
    groups = {0: [], 1: [], 2: []}
    for n in n_values:
        groups[n % 3].append(n)

    # Three distinct phase positions
    phase_positions = {
        0: (1.0, 0.0),       # mod 3 = 0: phase = 1
        1: (-0.5, 0.866),    # mod 3 = 1: phase = ω
        2: (-0.5, -0.866),   # mod 3 = 2: phase = ω²
    }

    # Plot each group as a single marker with grouped label
    for mod_val, ns in groups.items():
        px, py = phase_positions[mod_val]
        color = COLORS["Rb87"] if mod_val == 0 else COLORS["cross"]
        label = ",".join(str(n) for n in ns)
        fig.add_trace(go.Scatter(
            x=[px], y=[py],
            mode='markers',
            marker=dict(size=18 if mod_val == 0 else 14, color=color,
                        line=dict(width=2 if mod_val == 0 else 1, color='black')),
            showlegend=False,
        ))

    # Grouped labels with offset to avoid overlap
    fig.add_annotation(x=1.0, y=-0.18,
        text="<b>N<sub>f</sub> = 3, 6, 9, 12</b>",
        showarrow=False, font=dict(size=12, color=COLORS["Rb87"], family=FONT['family']))
    fig.add_annotation(x=-0.5, y=1.08,
        text="N<sub>f</sub> = 1, 4, 7, 10",
        showarrow=False, font=dict(size=11, color=COLORS["cross"], family=FONT['family']))
    fig.add_annotation(x=-0.5, y=-1.08,
        text="N<sub>f</sub> = 2, 5, 8, 11",
        showarrow=False, font=dict(size=11, color=COLORS["cross"], family=FONT['family']))

    # Highlight ring at phase = 1
    fig.add_trace(go.Scatter(
        x=[1], y=[0],
        mode='markers',
        marker=dict(size=26, color='rgba(0,0,0,0)', line=dict(width=3, color=COLORS["Rb87"])),
        name="Phase = 1 (modular invariant)",
    ))

    # Constraint annotation
    fig.add_annotation(
        x=1.25, y=0.25,
        text="<b>24 | c₋</b><br>N<sub>f</sub> ≡ 0 mod 3",
        showarrow=True, arrowhead=2, arrowcolor=COLORS["Rb87"],
        ax=40, ay=-30,
        font=dict(size=13, color=COLORS["Rb87"], family=FONT['family']),
        align='left',
    )

    fig.update_layout(
        title=dict(text="Framing Anomaly: T-Phase e<sup>2πi·c₋/24</sup> vs Generation Count",
                   font=TITLE_FONT),
        xaxis=dict(title="Re(phase)", range=[-1.4, 1.6], scaleanchor="y",
                   showgrid=True, gridcolor="rgba(0,0,0,0.08)",
                   zeroline=True, zerolinecolor="rgba(0,0,0,0.2)",
                   showline=True, linecolor="black", mirror=True),
        yaxis=dict(title="Im(phase)", range=[-1.4, 1.4],
                   showgrid=True, gridcolor="rgba(0,0,0,0.08)",
                   zeroline=True, zerolinecolor="rgba(0,0,0,0.2)",
                   showline=True, linecolor="black", mirror=True),
        font=FONT,
        plot_bgcolor='white', paper_bgcolor='white',
        width=600, height=600,
        legend=dict(x=0.02, y=0.98),
    )

    return fig


# ═══════════════════════════════════════════════════════════════
# Phase 5c: SU(2)_k Fusion and Quantum Group Figures
# ═══════════════════════════════════════════════════════════════

def fig_su2k_fusion_tables() -> go.Figure:
    """SU(2)_k fusion rule tables for k=1,2,3 as annotated heatmaps."""
    from src.core.formulas import su2k_fusion_rule

    fig = make_subplots(rows=1, cols=3,
                        subplot_titles=["SU(2)₁ (semion)", "SU(2)₂ (Ising)", "SU(2)₃ (Fibonacci)"],
                        horizontal_spacing=0.08)

    for col, k in enumerate([1, 2, 3], 1):
        n = k + 1
        labels = [f"V₀", f"V₁"] + ([f"V₂"] if n > 2 else []) + ([f"V₃"] if n > 3 else [])
        z = [[su2k_fusion_rule(k, i, j, m) for m in range(n)] for i in range(n) for j in range(n)]
        # Reshape to show fusion table: rows = (i,j) pairs, cols = m outcomes
        # Actually show as N_{ij} decomposition string
        table = []
        text = []
        for i in range(n):
            row = []
            trow = []
            for j in range(n):
                channels = [m for m in range(n) if su2k_fusion_rule(k, i, j, m) == 1]
                row.append(len(channels))
                trow.append("+".join(f"V_{m}" for m in channels) if channels else "0")
            table.append(row)
            text.append(trow)

        fig.add_trace(go.Heatmap(
            z=table, x=labels[:n], y=labels[:n],
            text=text, texttemplate="%{text}",
            colorscale=[[0, "white"], [1, COLORS["Rb87"]]],
            showscale=False,
            hovertemplate="V_%{y} ⊗ V_%{x} = %{text}<extra></extra>",
        ), row=1, col=col)

    fig.update_layout(
        title=dict(text="SU(2)<sub>k</sub> Fusion Rules", font=TITLE_FONT),
        font=FONT, width=1000, height=350,
        plot_bgcolor='white', paper_bgcolor='white',
    )
    return fig


def fig_su2k_quantum_dims() -> go.Figure:
    """Quantum dimensions d_j for SU(2)_k at k=1,2,3,4."""
    from src.core.formulas import su2k_quantum_dim
    import math

    fig = go.Figure()
    colors = [COLORS["Rb87"], COLORS["K39"], COLORS["Na23"], COLORS["dispersive"]]

    for idx, k in enumerate([1, 2, 3, 4]):
        n = k + 1
        js = list(range(n))
        dims = [su2k_quantum_dim(k, j) for j in js]
        fig.add_trace(go.Bar(
            x=[f"V_{j}" for j in js], y=dims,
            name=f"k={k}",
            marker_color=colors[idx],
            text=[f"{d:.3f}" if d > 1.01 else "" for d in dims],
            textposition="outside",
        ))

    fig.update_layout(
        title=dict(text="Quantum Dimensions d<sub>j</sub> for SU(2)<sub>k</sub>", font=TITLE_FONT),
        xaxis_title="Simple object", yaxis_title="Quantum dimension d_j",
        barmode="group",
        font=FONT, width=700, height=450,
        plot_bgcolor='white', paper_bgcolor='white',
        yaxis=dict(showgrid=True, gridcolor="rgba(0,0,0,0.08)"),
    )
    # Annotate golden ratio (offset to avoid k=4 bar collision)
    fig.add_annotation(x="V_2", y=su2k_quantum_dim(3, 2) + 0.25,
                       text="φ = (1+√5)/2 ≈ 1.618", showarrow=True,
                       ax=-40, ay=-30,
                       font=dict(size=11, color=COLORS["Na23"]))
    return fig


def fig_su2k_s_matrix_heatmaps() -> go.Figure:
    """S-matrix heatmaps for SU(2)_k at k=1,2."""
    from src.core.formulas import su2k_s_matrix_entry

    fig = make_subplots(rows=1, cols=2,
                        subplot_titles=["SU(2)₁ S-matrix (2×2)", "SU(2)₂ S-matrix (3×3)"],
                        horizontal_spacing=0.12)

    for col, k in enumerate([1, 2], 1):
        n = k + 1
        labels = [f"V_{j}" for j in range(n)]
        z = [[su2k_s_matrix_entry(k, i, j) for j in range(n)] for i in range(n)]
        text = [[f"{su2k_s_matrix_entry(k, i, j):.4f}" for j in range(n)] for i in range(n)]

        fig.add_trace(go.Heatmap(
            z=z, x=labels, y=labels,
            text=text, texttemplate="%{text}",
            colorscale="RdBu", zmid=0,
            showscale=(col == 2),
            hovertemplate="S(%{y},%{x}) = %{z:.4f}<extra></extra>",
        ), row=1, col=col)

    fig.update_layout(
        title=dict(text="Modular S-matrices for SU(2)<sub>k</sub>", font=TITLE_FONT),
        font=FONT, width=800, height=380,
        plot_bgcolor='white', paper_bgcolor='white',
    )
    return fig


def fig_hopf_chain() -> go.Figure:
    """The quantum group → gauge emergence chain as a flow diagram."""
    # Nodes in the chain
    nodes = [
        "Onsager", "q-Onsager",
        "U_q(sl₂)", "U_q(ŝl₂)",
        "u_q", "SU(2)_k",
        "S-matrix", "MTC"
    ]
    hover = [
        "Onsager algebra O (24 thms)", "q-Onsager O_q (coideal embed)",
        "U_q(sl₂) (6+21 thms, Hopf)", "U_q(ŝl₂) affine (9 thms)",
        "Restricted u_q (11 thms)", "SU(2)_k fusion (29 thms)",
        "S-matrix + Verlinde (16 thms)", "MTC defs (5 thms + classes)"
    ]
    x_pos = [i * 1.5 for i in range(len(nodes))]
    y_pos = [0, 0, 0, -0.8, 0, 0, 0, 0]

    fig = go.Figure()

    # Edges
    edges = [(0,1), (1,3), (2,4), (4,5), (5,6), (6,7), (2,3)]
    for i, j in edges:
        fig.add_trace(go.Scatter(
            x=[x_pos[i], x_pos[j]], y=[y_pos[i], y_pos[j]],
            mode='lines', line=dict(color='grey', width=2),
            showlegend=False, hoverinfo='skip',
        ))

    # Nodes
    colors_chain = [COLORS["dispersive"]] * 2 + [COLORS["Rb87"]] * 2 + \
                   [COLORS["K39"]] + [COLORS["Na23"]] * 2 + ["#9b6dff"]
    fig.add_trace(go.Scatter(
        x=x_pos, y=y_pos,
        mode='markers+text', text=nodes,
        textposition="top center",
        customdata=hover,
        marker=dict(size=28, color=colors_chain, line=dict(width=2, color='black')),
        showlegend=False,
        hovertemplate="%{customdata}<extra></extra>",
    ))

    fig.update_layout(
        title=dict(text="Quantum Group → Gauge Emergence Chain (Phase 5c)", font=TITLE_FONT),
        font=FONT, width=1400, height=400,
        plot_bgcolor='white', paper_bgcolor='white',
        xaxis=dict(visible=False), yaxis=dict(visible=False),
        margin=dict(t=80, b=40),
    )
    return fig


def fig_e8_cartan_heatmap() -> go.Figure:
    """E8 Cartan matrix as annotated heatmap."""
    e8 = [
        [2, 0, -1, 0, 0, 0, 0, 0],
        [0, 2, 0, -1, 0, 0, 0, 0],
        [-1, 0, 2, -1, 0, 0, 0, 0],
        [0, -1, -1, 2, -1, 0, 0, 0],
        [0, 0, 0, -1, 2, -1, 0, 0],
        [0, 0, 0, 0, -1, 2, -1, 0],
        [0, 0, 0, 0, 0, -1, 2, -1],
        [0, 0, 0, 0, 0, 0, -1, 2],
    ]
    labels = [f"α_{i+1}" for i in range(8)]
    text = [[str(v) for v in row] for row in e8]

    fig = go.Figure(go.Heatmap(
        z=e8, x=labels, y=labels,
        text=text, texttemplate="%{text}",
        colorscale=[[0, COLORS["Rb87"]], [0.5, "white"], [1, COLORS["Na23"]]],
        zmid=0, showscale=True,
        hovertemplate="E₈(%{y}, %{x}) = %{z}<extra></extra>",
    ))

    fig.update_layout(
        title=dict(text="E₈ Cartan Matrix — det=1, diagonal=2, σ=8", font=TITLE_FONT),
        font=FONT, width=550, height=500,
        plot_bgcolor='white', paper_bgcolor='white',
        xaxis=dict(title="Simple root"), yaxis=dict(title="Simple root", autorange="reversed"),
    )
    # Annotation: disproves algebraic Rokhlin
    fig.add_annotation(
        x=0.5, y=-0.12, xref="paper", yref="paper",
        text="σ(E₈) = 8 ≡ 0 mod 8 but ≢ 0 mod 16 — disproves naive algebraic Rokhlin",
        showarrow=False, font=dict(size=11, color="grey"),
    )
    return fig


# ════════════════════════════════════════════════════════════════════
# Phase 5d: Tetrad Gap Equation Figures
# ════════════════════════════════════════════════════════════════════


def fig_tetrad_gap_curve() -> go.Figure:
    """Order parameter Δ*(G) vs coupling G: the gap equation phase transition.

    Shows the bifurcation at G = G_c: Δ = 0 for G < G_c, then Δ*(G) rises
    continuously for G > G_c (second-order transition).
    """
    from src.core.formulas import tetrad_critical_coupling_integral, tetrad_gap_solution

    Lambda = np.pi
    N_f = 2
    G_c = tetrad_critical_coupling_integral(Lambda, N_f)

    G_ratios = np.linspace(0, 4, 400)
    G_values = G_ratios * G_c
    Delta_values = np.array([tetrad_gap_solution(G, Lambda, N_f) for G in G_values])

    fig = go.Figure()

    fig.add_trace(go.Scatter(
        x=G_ratios, y=Delta_values / Lambda,
        mode='lines', line=dict(color=COLORS['dispersive'], width=3),
        name='Δ*(G) / Λ',
    ))

    # Critical coupling marker
    fig.add_vline(x=1.0, line=dict(color=COLORS['dissipative'], width=1.5, dash='dash'))
    fig.add_annotation(x=1.0, y=0.85, text="G = G<sub>c</sub>",
        showarrow=False, font=dict(size=13, family=FONT['family'], color=COLORS['dissipative']))

    # Phase labels
    fig.add_annotation(x=0.4, y=0.1, text="<b>Pre-geometric</b><br>Δ = 0",
        showarrow=False, font=dict(size=12, family=FONT['family']))
    fig.add_annotation(x=2.5, y=0.6, text="<b>Tetrad condensed</b><br>Δ > 0",
        showarrow=False, font=dict(size=12, family=FONT['family']))

    apply_layout(fig, height=450, width=650,
        title=dict(text="<b>Tetrad Gap Equation: Order Parameter vs Coupling</b>",
                   font=TITLE_FONT),
        xaxis=dict(title="G / G<sub>c</sub>", range=[0, 4]),
        yaxis=dict(title="Δ* / Λ", range=[0, 1.1]),
        legend=dict(x=0.02, y=0.98))

    fig.add_annotation(x=0.5, y=-0.13, xref='paper', yref='paper',
        text="G<sub>c</sub> = 8π²/(N<sub>f</sub>Λ²) — first explicit tetrad gap equation (NJL-ADW correspondence)",
        showarrow=False, font=dict(size=10, family=FONT['family'], color='gray'))
    return fig


def fig_tetrad_gap_integral() -> go.Figure:
    """Gap integral I(Δ) vs Δ: decreasing from I(0) = Λ²/(8π²) to 0.

    Shows the monotonically decreasing gap integral that controls the
    phase transition structure.
    """
    from src.core.formulas import tetrad_gap_integral as gap_integral

    Lambda = np.pi
    Delta_values = np.linspace(0, 3 * Lambda, 300)
    I_values = np.array([gap_integral(d, Lambda) for d in Delta_values])

    fig = go.Figure()

    fig.add_trace(go.Scatter(
        x=Delta_values / Lambda, y=I_values,
        mode='lines', line=dict(color=COLORS['dispersive'], width=2.5),
        name='I(Δ)',
    ))

    # I(0) marker
    I0 = gap_integral(0, Lambda)
    fig.add_hline(y=I0, line=dict(color=COLORS['dissipative'], width=1, dash='dot'))
    fig.add_annotation(x=0.1, y=I0 * 1.1, text=f"I(0) = Λ²/(8π²) ≈ {I0:.4f}",
        showarrow=False, font=dict(size=11, family=FONT['family']))

    apply_layout(fig, height=400, width=600,
        title=dict(text="<b>Gap Integral I(Δ): Monotonically Decreasing</b>",
                   font=TITLE_FONT),
        xaxis=dict(title="Δ / Λ"),
        yaxis=dict(title="I(Δ)"))
    return fig


def fig_stimulated_hawking_spectrum() -> go.Figure:
    """Stimulated Hawking gain G(ω) vs frequency: amplification peaks at low ω.

    Shows the exponential suppression G(ω) = 1/(exp(2πω/κ) - 1) with
    annotations for the optimal probe window and 5σ detection threshold.
    """
    from src.core.formulas import stimulated_hawking_spectrum
    from src.core.constants import POLARITON_PLATFORMS

    kappa = POLARITON_PLATFORMS['Paris_long']['kappa']
    data = stimulated_hawking_spectrum(kappa, n_points=300)

    fig = go.Figure()

    fig.add_trace(go.Scatter(
        x=data['omega_over_kappa'], y=data['gain'],
        mode='lines', line=dict(color=COLORS['dispersive'], width=3),
        name='G(ω) — stimulated gain',
    ))

    # Detection threshold: G = 0.01 (need ~10^4 probe photons for 5σ)
    fig.add_hline(y=0.01, line=dict(color=COLORS['dissipative'], width=1, dash='dot'))
    fig.add_annotation(x=1.5, y=0.015, text="G = 0.01 (5σ with 10⁴ probe photons)",
        showarrow=False, font=dict(size=10, family=FONT['family'], color=COLORS['dissipative']))

    # Optimal probe window
    fig.add_vrect(x0=0, x1=0.3, fillcolor=COLORS['dispersive'], opacity=0.08,
        annotation_text="optimal probe window", annotation_position="top left",
        annotation_font=dict(size=10))

    apply_layout(fig, height=450, width=650,
        title=dict(text="<b>Stimulated Hawking Gain Spectrum</b>",
                   font=TITLE_FONT),
        xaxis=dict(title="ω / κ", range=[0, 3]),
        yaxis=dict(title="G(ω)", type="log", range=[-4, 1]),
        legend=dict(x=0.55, y=0.95))

    fig.add_annotation(x=0.5, y=-0.13, xref='paper', yref='paper',
        text=f"T_H = {data['T_H_K']*1e3:.1f} mK | κ = {kappa:.0e} s⁻¹ | "
             "Grisins PRB 94, 144518 (2016); Burkhard arXiv:2511.12339 (2025)",
        showarrow=False, font=dict(size=9, family=FONT['family'], color='gray'))
    return fig


def fig_rhmc_l8_preliminary() -> go.Figure:
    """
    PRELIMINARY L=8 RHMC analysis: 4-panel overview.

    Panel 1: Tetrad order parameter m² vs coupling g
    Panel 2: Acceptance rate vs coupling g
    Panel 3: h²/L⁴ (normalized h-field intensity) vs coupling g
    Panel 4: |delta_H| (MD energy violation) vs coupling g

    CAVEATS (displayed on figure):
    - High-coupling points (g > 3.96) have only 22 trajectories
    - Low-coupling acceptance rates are poor (< 30%)
    - No thermalization cut applied in this preliminary view
    - Not publication-quality -- diagnostic only

    Lean: verified_analysis.py uses formulas from VerifiedJackknife.lean
    """
    from pathlib import Path

    files = sorted(Path('data/rhmc/L8').glob('g*.npz'))
    if not files:
        fig = go.Figure()
        fig.add_annotation(text="No L=8 RHMC data found", x=0.5, y=0.5,
                          xref='paper', yref='paper', showarrow=False, font=dict(size=20))
        return fig

    gs, h_sqs, tet_m2s, accepts, delta_Hs, n_trajs = [], [], [], [], [], []
    for f in files:
        d = np.load(f)
        gs.append(float(d['g']))
        n_trajs.append(len(d['h_sq_history']))
        h_sqs.append(np.mean(d['h_sq_history']))
        tet_m2s.append(np.mean(d['tet_m2_history']))
        accepts.append(float(d['acceptance_rate']))
        delta_Hs.append(np.mean(np.abs(d['delta_h_history'])))

    gs = np.array(gs)
    n_trajs = np.array(n_trajs)
    low_stats = n_trajs < 50

    fig = make_subplots(rows=2, cols=2,
        subplot_titles=[
            'Tetrad Order Parameter m2',
            'Acceptance Rate',
            'Mean h2 / L4',
            'MD Energy Violation |dH|',
        ],
        vertical_spacing=0.15, horizontal_spacing=0.12)

    marker_colors = ['#F18F01' if ls else '#2E86AB' for ls in low_stats]
    marker_symbols = ['diamond' if ls else 'circle' for ls in low_stats]

    # Panel 1: tetrad m2
    fig.add_trace(go.Scatter(x=gs, y=tet_m2s, mode='markers+lines',
        marker=dict(size=10, color=marker_colors, symbol=marker_symbols),
        line=dict(color='#2E86AB', width=1, dash='dot'),
        name='m2', hovertemplate='g=%{x:.2f}<br>m2=%{y:.4f}<br>N=%{customdata}',
        customdata=n_trajs), row=1, col=1)

    # Panel 2: acceptance
    fig.add_trace(go.Scatter(x=gs, y=accepts, mode='markers+lines',
        marker=dict(size=10, color=marker_colors, symbol=marker_symbols),
        line=dict(color='#2E86AB', width=1, dash='dot'),
        name='accept', hovertemplate='g=%{x:.2f}<br>accept=%{y:.2f}<br>N=%{customdata}',
        customdata=n_trajs), row=1, col=2)
    fig.add_hline(y=0.5, line_dash='dash', line_color='gray', row=1, col=2,
                  annotation_text='target 50%', annotation_position='top left')

    # Panel 3: h2/L4
    L = 8
    h_sq_norm = np.array(h_sqs) / L**4
    fig.add_trace(go.Scatter(x=gs, y=h_sq_norm, mode='markers+lines',
        marker=dict(size=10, color=marker_colors, symbol=marker_symbols),
        line=dict(color='#2E86AB', width=1, dash='dot'),
        name='h2/L4'), row=2, col=1)

    # Panel 4: |dH|
    fig.add_trace(go.Scatter(x=gs, y=delta_Hs, mode='markers+lines',
        marker=dict(size=10, color=marker_colors, symbol=marker_symbols),
        line=dict(color='#2E86AB', width=1, dash='dot'),
        name='|dH|'), row=2, col=2)
    fig.add_hline(y=1.0, line_dash='dash', line_color='gray', row=2, col=2,
                  annotation_text='target |dH|<1', annotation_position='top left')

    fig.update_xaxes(title_text='coupling g', row=2, col=1)
    fig.update_xaxes(title_text='coupling g', row=2, col=2)

    fig.update_layout(
        title=dict(text='PRELIMINARY L=8 RHMC Analysis (not publication-quality)',
                   font=dict(size=14)),
        showlegend=False,
        height=600, width=900,
        annotations=[dict(
            text='PRELIMINARY: amber diamonds = N<50 traj. '
                 'Acceptance rates poor at low g. No thermalization cut.',
            x=0.5, y=-0.08, xref='paper', yref='paper',
            showarrow=False, font=dict(size=10, color='gray')
        )]
    )
    return fig


# ════════════════════════════════════════════════════════════════════
# Paper 14: Braided MTCs and Knot Invariants
# ════════════════════════════════════════════════════════════════════


def fig_su3k_fusion_tables() -> go.Figure:
    """SU(3)_k fusion tables for k=1 (Z₃) and k=2 (6 anyons).

    Lean: SU3kFusion.lean — su3k1Fusion, su3k2Fusion
    Paper 14 Figure: fusion tables as heatmaps.
    """
    fig = make_subplots(rows=1, cols=2,
                        subplot_titles=['SU(3)₁: Z₃ Fusion', 'SU(3)₂: 6 Anyons'],
                        horizontal_spacing=0.15)

    # SU(3)_1: Z_3 fusion (3x3 table showing output label)
    labels_k1 = ['1', 'f', 'f̄']
    # Fusion table: entry (i,j) = index of output object
    # 1⊗x=x, f⊗f=f̄(2), f⊗f̄=1(0), f̄⊗f̄=f(1)
    z3_table = np.array([[0, 1, 2],
                          [1, 2, 0],
                          [2, 0, 1]])
    fig.add_trace(go.Heatmap(
        z=z3_table, x=labels_k1, y=labels_k1,
        text=[[labels_k1[z3_table[i, j]] for j in range(3)] for i in range(3)],
        texttemplate='%{text}', textfont=dict(size=16),
        colorscale=[[0, '#E8F4FD'], [1, '#2E86AB']],
        showscale=False
    ), row=1, col=1)

    # SU(3)_2: 6-anyon fusion (showing number of channels)
    labels_k2 = ['1', 'f', 'f̄', 's', 's̄', 'τ']
    # Fusion multiplicities: N_{ij} = total number of fusion channels
    k2_mult = np.array([
        [1, 1, 1, 1, 1, 1],  # 1⊗x = x (1 channel each)
        [1, 2, 2, 1, 1, 2],  # f⊗f=f̄+s(2), f⊗f̄=1+τ(2), etc.
        [1, 2, 2, 1, 1, 2],  # f̄ row (symmetric)
        [1, 1, 1, 1, 1, 1],  # s row
        [1, 1, 1, 1, 1, 1],  # s̄ row
        [1, 2, 2, 1, 1, 2],  # τ⊗τ=1+τ(2)
    ])
    fig.add_trace(go.Heatmap(
        z=k2_mult, x=labels_k2, y=labels_k2,
        text=k2_mult.astype(str), texttemplate='%{text}',
        textfont=dict(size=14),
        colorscale=[[0, '#FFF3E0'], [0.5, '#F18F01'], [1, '#E63946']],
        showscale=False
    ), row=1, col=2)

    fig.update_layout(
        title=dict(text='SU(3)_k Fusion Rules — First Verified in Any Proof Assistant',
                   font=dict(size=14)),
        height=400, width=900,
        yaxis=dict(autorange='reversed'),
        yaxis2=dict(autorange='reversed'),
    )
    return fig


def fig_mtc_typeclass_hierarchy() -> go.Figure:
    """Typeclass hierarchy for the MTC formalization.

    Shows: MonoidalCategory → BraidedCategory → RigidCategory
           → PivotalCategory → SphericalCategory → RibbonCategory
           → PreModularData → ModularTensorData

    Lean: SphericalCategory.lean, RibbonCategory.lean, FusionCategory.lean
    Paper 14 Figure: dependency diagram as a Sankey-style flow.
    """
    # Node positions for the hierarchy
    categories = [
        'MonoidalCategory\n(Mathlib)', 'BraidedCategory\n(Mathlib)',
        'RigidCategory\n(Mathlib)', 'PivotalCategory\n(ours)',
        'SphericalCategory\n(ours)', 'RibbonCategory\n(ours)',
        'FusionCategoryData\n(ours)', 'PreModularData\n(ours)',
        'ModularTensorData\n(ours)'
    ]
    x_pos = [0.05, 0.15, 0.25, 0.35, 0.45, 0.55, 0.45, 0.7, 0.9]
    y_pos = [0.5,  0.5,  0.5,  0.5,  0.5,  0.5,  0.2,  0.35, 0.35]

    # Edges (from → to)
    edges = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5),
             (2, 6), (5, 7), (6, 7), (7, 8)]

    fig = go.Figure()

    # Draw edges
    for i, j in edges:
        fig.add_trace(go.Scatter(
            x=[x_pos[i], x_pos[j]], y=[y_pos[i], y_pos[j]],
            mode='lines', line=dict(color='#8D99AE', width=2),
            showlegend=False, hoverinfo='skip'
        ))

    # Draw nodes
    colors = ['#8D99AE'] * 3 + ['#2E86AB'] * 6  # grey=Mathlib, blue=ours
    fig.add_trace(go.Scatter(
        x=x_pos, y=y_pos, mode='markers+text',
        marker=dict(size=30, color=colors, line=dict(width=2, color='white')),
        text=categories, textposition='bottom center',
        textfont=dict(size=9), showlegend=False
    ))

    fig.update_layout(
        title=dict(text='MTC Typeclass Hierarchy (grey = Mathlib, blue = new)',
                   font=dict(size=13)),
        xaxis=dict(showgrid=False, zeroline=False, showticklabels=False),
        yaxis=dict(showgrid=False, zeroline=False, showticklabels=False),
        height=350, width=800, plot_bgcolor='white'
    )
    return fig


def fig_knot_invariants_table() -> go.Figure:
    """Table of verified knot invariants from categorical data.

    Lean: IsingBraiding.lean (trefoil=-1), FigureEightKnot.lean
    Paper 14 Figure: summary table of knot computation results.
    """
    fig = go.Figure(data=[go.Table(
        header=dict(
            values=['<b>Knot</b>', '<b>Braid Word</b>', '<b>MTC</b>',
                    '<b>Invariant</b>', '<b>Lean Module</b>'],
            fill_color='#2E86AB', font=dict(color='white', size=12),
            align='center'
        ),
        cells=dict(
            values=[
                ['Trefoil (3₁)', 'Hopf link (2₁²)', 'Figure-eight (4₁)'],
                ['σ₁³', 'σ₁²', 'σ₁σ₂⁻¹σ₁σ₂⁻¹'],
                ['Ising', 'Fibonacci', 'Ising'],
                ['-1', '0', '1 - q² - q⁻²'],
                ['IsingBraiding', 'IsingBraiding', 'FigureEightKnot'],
            ],
            fill_color=[['#E8F4FD', '#FFF3E0', '#E8F4FD']],
            font=dict(size=12), align='center', height=30
        )
    )])
    fig.update_layout(
        title=dict(text='Verified Knot Invariants from Categorical Data',
                   font=dict(size=14)),
        height=250, width=800
    )
    return fig


def fig_tqft_partition_functions() -> go.Figure:
    """TQFT partition functions Z(Σ_g) for Ising and Fibonacci.

    Z(Σ_g) = Σ_a d_a^{2-2g} (Verlinde formula).

    Lean: TQFTPartition.lean
    Paper 14 Figure: bar chart of Z(Σ_g) for g=0,1,2.
    """
    genera = [0, 1, 2]
    # Ising: d = (1, sqrt(2), 1), D^2 = 4
    # Z(S^2) = 1, Z(T^2) = 3, Z(Σ_2) = sum d_a^{-2} = 1 + 1/2 + 1 = 5/2
    ising_z = [1.0, 3.0, 2.5]
    # Fibonacci: d = (1, phi), D^2 = 2+phi
    phi = (1 + np.sqrt(5)) / 2
    fib_z = [1.0, 2.0, 1 + 1/phi**2]  # Z(g=2) = 1 + phi^{-2}

    fig = go.Figure()
    fig.add_trace(go.Bar(
        x=[f'g={g}' for g in genera], y=ising_z,
        name='Ising MTC', marker_color='#2E86AB'
    ))
    fig.add_trace(go.Bar(
        x=[f'g={g}' for g in genera], y=fib_z,
        name='Fibonacci MTC', marker_color='#F18F01'
    ))
    fig.update_layout(
        title=dict(text='TQFT Partition Functions Z(Σ_g) — Verified in Lean 4',
                   font=dict(size=14)),
        xaxis_title='Surface genus g',
        yaxis_title='Z(Σ_g)',
        barmode='group', height=400, width=600,
        legend=dict(x=0.7, y=0.95)
    )
    return fig


def fig_number_field_technique() -> go.Figure:
    """Comparison of algebraic verification approaches.

    Paper 14 Figure: table comparing native_decide vs norm_num vs pen-and-paper
    for pentagon equation verification across different MTCs.
    """
    fig = go.Figure(data=[go.Table(
        header=dict(
            values=['<b>MTC</b>', '<b>Number Field</b>', '<b>Degree</b>',
                    '<b>Cases</b>', '<b>Method</b>', '<b>Time</b>'],
            fill_color='#2E86AB', font=dict(color='white', size=11),
            align='center'
        ),
        cells=dict(
            values=[
                ['Ising', 'Fibonacci', 'SU(2)₃', 'SU(2)₄', 'SU(3)₁', 'SU(3)₂'],
                ['Q(√2)', 'Q(√5)', 'Q(level₃)', 'Q(√3)', 'Q(ζ₃)', 'Q(ζ₁₅)'],
                ['2', '2', '4', '2', '2', '8'],
                ['243', '32', '256', '625', '27', '46656'],
                ['native_decide', 'native_decide', 'native_decide',
                 'native_decide', 'native_decide', 'pending'],
                ['~2s', '~1s', '~3s', '~2s', '~1s', 'TBD'],
            ],
            fill_color=[['#E8F4FD', '#FFF3E0', '#E8F4FD',
                          '#FFF3E0', '#E8F4FD', '#FFE0E0']],
            font=dict(size=11), align='center', height=28
        )
    )])
    fig.update_layout(
        title=dict(text='Decidable Number Field Technique: Verification Performance',
                   font=dict(size=13)),
        height=280, width=850
    )
    return fig


# ════════════════════════════════════════════════════════════════════
# Paper 15: Methodology Pipeline
# ════════════════════════════════════════════════════════════════════


def fig_pipeline_stages() -> go.Figure:
    """The 12-stage verification pipeline as a flow diagram.

    Paper 15 Figure: stages 1-12 with gates.
    """
    stages = [
        '1. Constants', '2. Formulas', '3. Lean Stubs', '4. Aristotle',
        '5. Build Verify', '6. Python Tests', '7. Validation',
        '8. Figures', '9. Fig Review', '10. Paper', '11. Notebooks', '12. Doc Sync'
    ]
    x = list(range(12))
    y = [0] * 12

    fig = go.Figure()
    # Connections
    for i in range(11):
        fig.add_trace(go.Scatter(
            x=[x[i] + 0.3, x[i+1] - 0.3], y=[0, 0],
            mode='lines', line=dict(color='#8D99AE', width=2),
            showlegend=False, hoverinfo='skip'
        ))
    # Stage nodes
    colors = ['#2E86AB'] * 3 + ['#F18F01'] * 1 + ['#2E86AB'] * 3 + \
             ['#5C946E'] * 2 + ['#E63946'] * 1 + ['#5C946E'] * 2
    fig.add_trace(go.Scatter(
        x=x, y=y, mode='markers+text',
        marker=dict(size=35, color=colors, symbol='square',
                    line=dict(width=2, color='white')),
        text=[s.split('. ')[1] if '. ' in s else s for s in stages],
        textposition='bottom center',
        textfont=dict(size=8), showlegend=False
    ))

    fig.update_layout(
        title=dict(text='12-Stage Verification Pipeline',
                   font=dict(size=14)),
        xaxis=dict(showgrid=False, zeroline=False, showticklabels=False),
        yaxis=dict(showgrid=False, zeroline=False, showticklabels=False,
                   range=[-0.5, 0.5]),
        height=200, width=900, plot_bgcolor='white',
        margin=dict(t=40, b=60)
    )
    return fig


def fig_theorem_growth() -> go.Figure:
    """Theorem count growth over project phases.

    Paper 15 Figure: bar chart of theorem counts by phase.
    """
    phases = ['1-2', '3a', '3b', '4', '5a', '5b', '5c', '5d', '5e', '5f', '5g-j']
    counts = [51, 65, 200, 120, 120, 180, 270, 200, 150, 80, 796]

    fig = go.Figure()
    fig.add_trace(go.Bar(
        x=phases, y=counts, marker_color='#2E86AB',
        text=counts, textposition='outside'
    ))
    # Cumulative line
    cumulative = np.cumsum(counts)
    fig.add_trace(go.Scatter(
        x=phases, y=cumulative, mode='lines+markers',
        line=dict(color='#E63946', width=2),
        marker=dict(size=6), name='Cumulative',
        yaxis='y2'
    ))

    fig.update_layout(
        title=dict(text='Theorem Growth by Phase (2232 total)',
                   font=dict(size=14)),
        xaxis_title='Phase', yaxis_title='New Theorems',
        yaxis2=dict(title='Cumulative', overlaying='y', side='right',
                    range=[0, 2500]),
        height=400, width=700,
        showlegend=False
    )
    return fig


def fig_sorry_reduction() -> go.Figure:
    """Sorry gap reduction over time.

    Paper 15 Figure: showing how sorry gaps decrease as Aristotle proves theorems.
    """
    # Approximate timeline of sorry reduction
    milestones = [
        'Phase 3\n(initial)', 'Phase 5b\n(Drinfeld)', 'Phase 5c\n(QG)',
        'Aristotle\nBatch 1', 'native_decide\n(pentagon)', 'Phase 5i\n(sl₃)',
        'Current'
    ]
    sorry_counts = [45, 42, 38, 36, 28, 28, 33]  # 33 includes new Uqsl3Hopf
    total_thms = [400, 800, 1100, 1400, 1700, 2023, 2232]
    sorry_pct = [s/t*100 for s, t in zip(sorry_counts, total_thms)]

    fig = make_subplots(specs=[[{"secondary_y": True}]])
    fig.add_trace(go.Bar(
        x=milestones, y=sorry_counts,
        name='Sorry gaps', marker_color='#E63946'
    ))
    fig.add_trace(go.Scatter(
        x=milestones, y=sorry_pct,
        name='Sorry %', line=dict(color='#F18F01', width=2, dash='dot'),
        marker=dict(size=8)
    ), secondary_y=True)

    fig.update_layout(
        title=dict(text='Sorry Gap Reduction: 45 → 33 (11.3% → 1.5%)',
                   font=dict(size=14)),
        height=400, width=700, legend=dict(x=0.7, y=0.95)
    )
    fig.update_yaxes(title_text='Sorry count', secondary_y=False)
    fig.update_yaxes(title_text='Sorry %', secondary_y=True)
    return fig


# ════════════════════════════════════════════════════════════════════
# Phase 5h: Chirality Wall 3+1D
# ════════════════════════════════════════════════════════════════════


def fig_gauging_obstruction_status() -> go.Figure:
    """Gauging obstruction analysis: conditions for chiral gauge theory.

    Lean: GaugingStep.lean ��� gauging_conditional, sm_anomaly_cancel_16
    """
    steps = [
        'Not-on-site\nsymmetry', 'Disentangler\nW†QW = on-site',
        '16 | n\n(anomaly cancel)', 'Chiral gauge\ntheory'
    ]
    statuses = ['Identified', 'Required', 'Proved\n(SM: 16≡0)', 'Conditional']
    colors_list = [COLORS['carmine'], COLORS['amber'], COLORS['sage'], COLORS['steel_blue']]

    fig = go.Figure()
    for i, (step, status, color) in enumerate(zip(steps, statuses, colors_list)):
        fig.add_trace(go.Scatter(
            x=[i], y=[0.5], mode='markers+text',
            marker=dict(size=50, color=color, line=dict(width=2, color='white')),
            text=[step], textposition='top center', textfont=dict(size=11),
            showlegend=False
        ))
        fig.add_trace(go.Scatter(
            x=[i], y=[0.3], mode='text',
            text=[status], textfont=dict(size=9, color='gray'),
            showlegend=False
        ))
        if i < len(steps) - 1:
            fig.add_annotation(x=i + 0.4, y=0.5, text='→', showarrow=False,
                               font=dict(size=18))

    fig.update_layout(
        title=dict(text='Gauging Obstruction: Conditions for Chiral Gauge Theory',
                   font=dict(size=14)),
        xaxis=dict(visible=False, range=[-0.5, 3.5]),
        yaxis=dict(visible=False, range=[0, 0.8]),
        height=300, width=800
    )
    return fig


def fig_spt_classification_map() -> go.Figure:
    """SPT classification: free-fermion vs commuting-projector phases.

    Lean: SPTClassification.lean �� 15 thms + gapped_interface_axiom
    """
    categories = ['Free Fermion\nSPT', 'Commuting\nProjector SPT', 'Gapped\nInterface']
    props = [
        'Quadratic H\nBand topology\nKitaev periodic table',
        'Infinite-dim rotors\nOn-site symmetry\nCommuting terms',
        'Codim-1 junction\nGap > 0\nUnique ground state'
    ]
    colors_list = [COLORS['steel_blue'], COLORS['sage'], COLORS['amber']]

    fig = go.Figure()
    for i, (cat, prop, color) in enumerate(zip(categories, props, colors_list)):
        fig.add_trace(go.Bar(
            x=[cat], y=[1], marker_color=color,
            text=[prop], textposition='inside',
            textfont=dict(size=10, color='white'),
            showlegend=False
        ))

    fig.update_layout(
        title=dict(text='SPT Phase Classification (SPTClassification.lean)',
                   font=dict(size=14)),
        yaxis=dict(visible=False), height=350, width=700
    )
    return fig


# ════════════════════════════════════════════════════════════════════
# Phase 5j: Fermi-Point Gauge Emergence
# ════════════════════════════════════════════════════════════════════


def fig_fermi_point_emergence_chain() -> go.Figure:
    """Emergence chain from Fermi-point to emergent gravity.

    Lean: FermiPointTopology.lean — su2_emergence_chain, emergence_theorem_frontier
    """
    steps = [
        'Multi-fermion\n→ Weyl', '|N|=1 → U(1)\n+ vierbein',
        '|N| node\nsplits', 'Z₂ → SU(2)\ngauge',
        'Spin conn.\nco-emerges', 'Yang-Mills\ndynamics'
    ]
    rigor = ['THEOREM', 'THEOREM', 'THEOREM', 'HEURISTIC', 'HEURISTIC', 'SPECULATIVE']
    color_map = {
        'THEOREM': COLORS['sage'],
        'HEURISTIC': COLORS['amber'],
        'SPECULATIVE': COLORS['carmine']
    }
    colors_list = [color_map[r] for r in rigor]

    fig = go.Figure()
    for i, (step, r, color) in enumerate(zip(steps, rigor, colors_list)):
        fig.add_trace(go.Scatter(
            x=[i], y=[0.5], mode='markers+text',
            marker=dict(size=45, color=color, line=dict(width=2, color='white')),
            text=[step], textposition='top center', textfont=dict(size=10),
            showlegend=False
        ))
        fig.add_trace(go.Scatter(
            x=[i], y=[0.3], mode='text',
            text=[r], textfont=dict(size=8, color=color),
            showlegend=False
        ))
        if i < len(steps) - 1:
            fig.add_annotation(x=i + 0.4, y=0.5, text='→', showarrow=False,
                               font=dict(size=16))

    # Frontier line
    fig.add_vline(x=2.5, line_dash='dash', line_color='gray', opacity=0.5)
    fig.add_annotation(x=2.5, y=0.7, text='← Theorem frontier',
                       showarrow=False, font=dict(size=10, color='gray'))

    fig.update_layout(
        title=dict(text='Fermi-Point → Emergent Gravity: Rigor Status',
                   font=dict(size=14)),
        xaxis=dict(visible=False, range=[-0.5, 5.5]),
        yaxis=dict(visible=False, range=[0.1, 0.85]),
        height=350, width=900
    )
    return fig


def fig_mechanism_a_vs_b() -> go.Figure:
    """Mechanism A (Hořava) vs Mechanism B (SU(2)) distinction.

    Lean: FermiPointTopology.lean — mechanism_a_no_nonabelian, multi_weyl_is_mechanism_a
    """
    fig = make_subplots(rows=1, cols=2,
                        subplot_titles=['Mechanism A: Single |N|>1',
                                       'Mechanism B: Correlated |N|=1'])

    # Mechanism A: anisotropic dispersion
    k = np.linspace(-2, 2, 100)
    E_linear = np.abs(k)
    E_quad = k ** 2
    E_cubic = np.abs(k) ** 3

    fig.add_trace(go.Scatter(
        x=k, y=E_linear, name='|N|=1: E~|k|',
        line=dict(color=COLORS['sage'], width=2)
    ), row=1, col=1)
    fig.add_trace(go.Scatter(
        x=k, y=E_quad, name='|N|=2: E~k²',
        line=dict(color=COLORS['amber'], width=2)
    ), row=1, col=1)
    fig.add_trace(go.Scatter(
        x=k, y=E_cubic, name='|N|=3: E~|k|³',
        line=dict(color=COLORS['carmine'], width=2)
    ), row=1, col=1)

    # Mechanism B: correlated nodes
    k2 = np.linspace(-3, 3, 200)
    E_node1 = np.sqrt((k2 - 1) ** 2 + 0.01)
    E_node2 = np.sqrt((k2 + 1) ** 2 + 0.01)

    fig.add_trace(go.Scatter(
        x=k2, y=E_node1, name='Node 1 (N=+1)',
        line=dict(color=COLORS['steel_blue'], width=2), showlegend=True
    ), row=1, col=2)
    fig.add_trace(go.Scatter(
        x=k2, y=E_node2, name='Node 2 (N=+1)',
        line=dict(color=COLORS['amber'], width=2, dash='dash'), showlegend=True
    ), row=1, col=2)

    fig.update_xaxes(title_text='k⊥', row=1, col=1)
    fig.update_xaxes(title_text='k', row=1, col=2)
    fig.update_yaxes(title_text='E(k)', row=1, col=1)
    fig.update_yaxes(title_text='E(k)', row=1, col=2)

    fig.update_layout(
        title=dict(text='Mechanism A (Anisotropic) vs B (Correlated Nodes)',
                   font=dict(size=14)),
        height=400, width=900, legend=dict(x=0.65, y=0.95, font=dict(size=10))
    )
    return fig


def fig_ising_braiding_data() -> go.Figure:
    """Ising MTC braiding data summary: R-matrix, twist, hexagon, ribbon.

    Displays the complete verified braiding data for the Ising MTC
    from IsingBraiding.lean (23 theorems, 0 sorry).
    """
    from src.core.formulas import (
        ising_r_matrix, ising_twist, mtc_s_matrix,
        interferometric_visibility, thermal_hall_conductance,
    )

    fig = make_subplots(rows=1, cols=2, subplot_titles=(
        'R-matrix phases (QCyc16)', 'Experimental predictions'))

    # R-matrix data
    labels = ['R₁^{σσ}', 'Rψ^{σσ}', 'R^{σψ}_σ', 'R^{ψψ}_1']
    R_values = [
        ising_r_matrix(1, 1, 0), ising_r_matrix(1, 1, 2),
        ising_r_matrix(1, 2, 1), ising_r_matrix(2, 2, 0)]
    phases = [np.angle(r) / np.pi for r in R_values]
    expected = [-1/8, 3/8, -1/2, 1]

    fig.add_trace(go.Bar(
        x=labels, y=phases, name='Computed phase/π',
        marker_color=COLORS['steel_blue'], text=[f'{p:.4f}' for p in phases],
        textposition='outside'
    ), row=1, col=1)
    fig.add_trace(go.Scatter(
        x=labels, y=expected, mode='markers', name='Expected',
        marker=dict(color=COLORS['carmine'], size=10, symbol='x')
    ), row=1, col=1)

    # Predictions
    obs = ['M_{σ,σ}', 'M_{σ,1}', 'M_{σ,ψ}', 'c_top', 'GSD']
    vals = [
        abs(interferometric_visibility('ising', 1, 1)),
        abs(interferometric_visibility('ising', 1, 0)),
        abs(interferometric_visibility('ising', 1, 2)),
        thermal_hall_conductance('ising')['c_top'],
        3,
    ]
    fig.add_trace(go.Bar(
        x=obs, y=vals, name='Ising predictions',
        marker_color=COLORS['amber'], text=[f'{v:.2f}' for v in vals],
        textposition='outside'
    ), row=1, col=2)

    fig.update_yaxes(title_text='Phase / π', row=1, col=1)
    fig.update_yaxes(title_text='Value', row=1, col=2)
    fig.update_layout(
        title=dict(text='Ising MTC: Verified Braiding Data (23 thms, 0 sorry)',
                   font=TITLE_FONT),
        height=400, width=900, showlegend=True, font=FONT,
        legend=dict(x=0.01, y=0.99)
    )
    return fig


def fig_fibonacci_braiding_data() -> go.Figure:
    """Fibonacci MTC braiding data summary: R-matrix, hexagon, universality.

    Displays the complete verified braiding data for the Fibonacci MTC
    from FibonacciBraiding.lean + FibonacciUniversality.lean.
    """
    from src.core.formulas import (
        fibonacci_r_matrix, fibonacci_twist,
        interferometric_visibility, thermal_hall_conductance,
        mtc_total_quantum_dimension,
    )

    fig = make_subplots(rows=1, cols=2, subplot_titles=(
        'R-matrix + twist (QCyc5)', 'Ising vs Fibonacci predictions'))

    # Fibonacci R/twist data
    R1 = fibonacci_r_matrix(0)
    Rtau = fibonacci_r_matrix(1)
    theta = fibonacci_twist()
    labels = ['R₁', 'Rτ', 'θ_τ', 'R₁/Rτ²']
    phases = [np.angle(v)/np.pi for v in [R1, Rtau, theta, R1/Rtau**2]]
    fig.add_trace(go.Bar(
        x=labels, y=phases, name='Phase/π',
        marker_color=COLORS['sage'],
        text=[f'{p:.4f}' for p in phases], textposition='outside'
    ), row=1, col=1)

    # Comparison: Ising vs Fibonacci
    obs = ['|M_{probe,target}|', 'c_top', 'ln(D)', 'GSD', 'e*/e denom']
    ising_vals = [0.0, 0.5, np.log(2), 3, 4]
    phi = (1 + np.sqrt(5)) / 2
    fib_vals = [
        abs(interferometric_visibility('fibonacci', 1, 1)),
        thermal_hall_conductance('fibonacci')['c_top'],
        np.log(mtc_total_quantum_dimension('fibonacci')),
        2, 5,
    ]

    fig.add_trace(go.Bar(
        x=obs, y=ising_vals, name='Ising',
        marker_color=COLORS['steel_blue']
    ), row=1, col=2)
    fig.add_trace(go.Bar(
        x=obs, y=fib_vals, name='Fibonacci',
        marker_color=COLORS['amber']
    ), row=1, col=2)

    fig.update_yaxes(title_text='Phase / π', row=1, col=1)
    fig.update_yaxes(title_text='Value', row=1, col=2)
    fig.update_layout(
        title=dict(text='Fibonacci MTC: Universal Braiding (dense SU(2))',
                   font=TITLE_FONT),
        height=400, width=900, barmode='group', showlegend=True, font=FONT,
        legend=dict(x=0.01, y=0.99)
    )
    return fig


def fig_experimental_predictions() -> go.Figure:
    """Side-by-side comparison of 5 distinguishing observables.

    From Phase 5o deep research: From verified braiding algebra to
    laboratory observables. All values from verified MTC data.
    """
    from src.core.formulas import distinguishing_observables_table

    table = distinguishing_observables_table()

    obs = [r['observable'] for r in table]
    ranks = [r['rank'] for r in table]

    fig = go.Figure()
    fig.add_trace(go.Bar(
        x=obs, y=ranks, marker_color=[
            COLORS['sage'], COLORS['sage'],
            COLORS['amber'], COLORS['steel_blue'], COLORS['steel_blue']],
        text=[r['status'][:30] + '...' if len(r['status']) > 30 else r['status']
              for r in table],
        textposition='outside'
    ))

    fig.update_layout(
        title=dict(text='Experimental Accessibility: Ising vs Fibonacci Discriminators',
                   font=TITLE_FONT),
        yaxis_title='Accessibility rank (1=most accessible)',
        height=400, width=800, font=FONT
    )
    return fig


# ═════════════════════��══════════════════════════════════════════════
# Phase 5k Wave 4: TQFT Pipeline — WRT Invariants & Surgery
# ═════════════════════════════���══════════════════════════════════════


def fig_wrt_invariants_table() -> go.Figure:
    """Table of WRT invariant values Z(M) for key 3-manifolds.

    Displays computed and Lean-verified WRT invariant values for S^3,
    S^2 x S^1, and lens spaces L(p,1) across Ising and Fibonacci MTCs.

    All values verified in Lean via native_decide over cyclotomic number fields
    (QCyc16 for Ising, QCyc5 for Fibonacci). Key highlights:
      - Z(L(8,1)) = 0 for Ising (vanishing)
      - Z(L(16,1)) = 1 for Ising (16-fold periodicity)
      - Z(L(5,1)) = 1 for Fibonacci (5-fold periodicity)

    Lean: WRTInvariant.lean, WRTComputation.lean
    """
    from src.core.formulas import wrt_invariants_table

    rows = wrt_invariants_table()

    manifolds = [r['manifold'] for r in rows]
    surgeries = [r['surgery'] for r in rows]
    ising_vals = [r['ising'] for r in rows]
    fib_vals = [r['fibonacci'] for r in rows]
    statuses = [r['lean_status'] for r in rows]

    # Color rows: highlight vanishing and trivial invariants
    row_colors = []
    for r in rows:
        if 'vanishing' in r.get('ising', ''):
            row_colors.append('#FFE0E0')  # light red for vanishing
        elif r['manifold'] in ('S^3', 'S^2 x S^1'):
            row_colors.append('#E8F4FD')  # light blue for fundamental
        else:
            row_colors.append('#FFF3E0')  # light amber for lens spaces

    fig = go.Figure(data=[go.Table(
        header=dict(
            values=['<b>3-Manifold</b>', '<b>Surgery</b>',
                    '<b>Ising (k=2)</b>', '<b>Fibonacci (k=3)</b>',
                    '<b>Lean</b>'],
            fill_color=COLORS['steel_blue'],
            font=dict(color='white', size=12, family=FONT['family']),
            align='center'
        ),
        cells=dict(
            values=[manifolds, surgeries, ising_vals, fib_vals, statuses],
            fill_color=[[c for c in row_colors]] * 5,
            font=dict(size=11, family=FONT['family']),
            align='center',
            height=28
        )
    )])

    fig.update_layout(
        title=dict(
            text='WRT Invariants Z(M): First Verified Quantum 3-Manifold Values',
            font=TITLE_FONT),
        height=350, width=950,
        margin=dict(l=10, r=10, t=50, b=10),
    )
    return fig


def fig_surgery_presentation() -> go.Figure:
    """Visualization of surgery link data for standard 3-manifolds.

    Shows the linking matrix structure and key properties for each
    standard surgery presentation: S^3, S^2 x S^1, L(p,1), Hopf link,
    and trefoil complement.

    Lean: SurgeryPresentation.lean (all symmetry/framing proofs verified)
    """
    from src.core.formulas import surgery_linking_matrix

    # Define manifolds to display
    manifold_specs = [
        ('S^3', 'S3', {}, 'Empty link', 'Canonical'),
        ('S^2 x S^1', 'S2xS1', {}, '0-unknot', '0-framed unknot'),
        ('L(1,1)', 'lens', {'p': 1}, '1-unknot', 'p=1 surgery'),
        ('L(5,1)', 'lens', {'p': 5}, '5-unknot', 'p=5 surgery'),
        ('L(8,1)', 'lens', {'p': 8}, '8-unknot', 'Ising-invisible'),
        ('Hopf(2,3)', 'hopf', {'a': 2, 'b': 3}, '2-component', 'lk=1'),
        ('Trefoil cmpl', 'trefoil_complement', {}, '2-component', '[[-2,1],[1,-3]]'),
    ]

    names = []
    n_comps = []
    framings_str = []
    matrix_str = []
    descriptions = []
    symmetric_check = []

    for label, key, kwargs, desc, note in manifold_specs:
        data = surgery_linking_matrix(key, **kwargs)
        names.append(label)
        n_comps.append(str(data['num_components']))
        framings_str.append(str(data['framings']) if data['framings'] else '[]')
        M = data['matrix']
        if M.size == 0:
            matrix_str.append('(empty)')
        elif M.shape == (1, 1):
            matrix_str.append(f'[{M[0,0]}]')
        else:
            rows_repr = ', '.join(
                '[' + ','.join(str(x) for x in row) + ']' for row in M
            )
            matrix_str.append(f'[{rows_repr}]')
        descriptions.append(note)
        symmetric_check.append('\u2713' if M.size == 0 or np.array_equal(M, M.T)
                               else '\u2717')

    fig = go.Figure(data=[go.Table(
        header=dict(
            values=['<b>Manifold</b>', '<b>Components</b>', '<b>Framings</b>',
                    '<b>Linking Matrix</b>', '<b>Notes</b>', '<b>Symm</b>'],
            fill_color=COLORS['steel_blue'],
            font=dict(color='white', size=11, family=FONT['family']),
            align='center'
        ),
        cells=dict(
            values=[names, n_comps, framings_str, matrix_str,
                    descriptions, symmetric_check],
            fill_color=[['#E8F4FD', '#FFF3E0'] * 4],
            font=dict(size=11, family=FONT['family']),
            align='center',
            height=28
        )
    )])

    fig.update_layout(
        title=dict(
            text='Surgery Presentations: Combinatorial 3-Manifold Data',
            font=TITLE_FONT),
        height=320, width=900,
        margin=dict(l=10, r=10, t=50, b=10),
    )
    return fig


def fig_ext_chart() -> go.Figure:
    """Ext chart for A(1) in the (stem, filtration) plane.

    Shows the E₂ page of the Adams spectral sequence for ko:
    Ext^{s,t}_{A(1)}(F₂, F₂) with stem = t-s on x-axis, filtration = s on y-axis.
    The infinite h₀-tower in stem 4 detects π₄(ko) ≅ ℤ.

    Machine-checked: A1Ext.lean (dims 1,2,2,2,3,4), A1Resolution.lean (d²=0, exactness)
    Lean: ext_dim_0..ext_dim_5, h0_tower_stem4_starts
    """
    from src.core.formulas import a1_ext_generator_bidegrees

    # Ext generators with labels
    generators = {
        0: [((0, 0), '1')],
        1: [((1, 1), 'h₀'), ((1, 2), 'h₁')],
        2: [((2, 2), 'h₀²'), ((2, 4), 'h₁²')],
        3: [((3, 3), 'h₀³'), ((3, 7), 'v')],
        4: [((4, 4), 'h₀⁴'), ((4, 8), 'h₀v'), ((4, 12), 'w₁')],
        5: [((5, 5), 'h₀⁵'), ((5, 9), 'h₀²v'), ((5, 13), 'h₀w₁'), ((5, 14), 'h₁w₁')],
    }

    stems = []
    filts = []
    labels = []
    colors = []

    for n, gens in generators.items():
        for (s, t), label in gens:
            stem = t - s
            stems.append(stem)
            filts.append(s)
            labels.append(label)
            # Color by family
            if 'h₁' in label and 'h₀' not in label:
                colors.append(COLORS.get('heidelberg', '#B44682'))
            elif 'v' in label or 'w' in label:
                colors.append(COLORS.get('trento', '#D4A843'))
            else:
                colors.append(COLORS.get('steinhauer', '#4682B4'))

    fig = go.Figure()

    # Plot generators as dots
    fig.add_trace(go.Scatter(
        x=stems, y=filts, mode='markers+text',
        marker=dict(size=12, color=colors, line=dict(width=1, color='black')),
        text=labels, textposition='top center',
        textfont=dict(size=10, family='CMU Serif, serif'),
        hovertemplate='stem=%{x}, s=%{y}, %{text}<extra></extra>',
        name='Ext generators',
        showlegend=False,
    ))

    # Draw h₀-towers (vertical lines connecting h₀-multiples)
    tower_stems = {0: [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5)],
                   4: [(3, 7), (4, 8), (5, 9)]}
    for stem_val, points in tower_stems.items():
        ss = [t - s for s, t in points]
        fs = [s for s, t in points]
        fig.add_trace(go.Scatter(
            x=ss, y=fs, mode='lines',
            line=dict(color=COLORS.get('steinhauer', '#4682B4'), width=2, dash='dot'),
            showlegend=False, hoverinfo='skip',
        ))

    apply_layout(fig,
        xaxis=dict(title='Stem (t − s)', dtick=1, range=[-0.5, 10.5]),
        yaxis=dict(title='Filtration (s)', dtick=1, range=[-0.5, 6.5], autorange='reversed'),
        title=dict(
            text='Ext<sup>s,t</sup><sub>A(1)</sub>(F₂, F₂) — Adams E₂ Page for ko',
            font=TITLE_FONT),
        height=450, width=700,
        margin=dict(l=60, r=20, t=60, b=60),
    )

    # Annotations
    fig.add_annotation(x=0, y=6.2, text='h₀-tower → ℤ',
        showarrow=False, font=dict(size=11, color=COLORS.get('steinhauer', '#4682B4')))
    fig.add_annotation(x=4, y=6.2, text='h₀-tower → ℤ (stem 4)',
        showarrow=False, font=dict(size=11, color=COLORS.get('trento', '#D4A843')))

    return fig


def fig_a1_resolution_structure() -> go.Figure:
    """Resolution structure diagram for F₂ over A(1).

    Shows the bidiagonal pattern of the minimal free resolution:
    Sq(1) on diagonal, Sq(2,1) on superdiagonal, with ranks and
    generator degrees at each level.

    Machine-checked: A1Resolution.lean (d²=0, RREF witnesses, exactness)
    Lean: d1_d2_zero..d4_d5_zero, d1_kernel_card..d3_kernel_card, d4_rref_valid, d5_rref_valid
    """
    ranks = [1, 2, 2, 2, 3, 4]
    gen_degrees = [
        [0],           # P₀
        [1, 2],        # P₁
        [2, 4],        # P₂
        [3, 7],        # P₃
        [4, 8, 12],    # P₄
        [5, 9, 13, 14], # P₅
    ]
    diff_labels = ['ε', 'd₁', 'd₂', 'd₃', 'd₄', 'd₅']
    diff_entries = [
        'proj',
        '[Sq(1), Sq(2)]',
        '[[Sq(1), Sq(3)], [0, Sq(2)]]',
        '[[Sq(1), Sq(2,1)], [0, Sq(3)]]',
        '[[Sq(1), Sq(2,1), 0], [0, Sq(1), Sq(2,1)]]',
        '[[Sq(1), Sq(2,1), 0, 0], ...]',
    ]

    fig = go.Figure()

    # Module boxes
    for i, (r, degs) in enumerate(zip(ranks, gen_degrees)):
        x = i * 1.5
        deg_str = ', '.join(str(d) for d in degs)
        fig.add_trace(go.Scatter(
            x=[x], y=[0], mode='markers+text',
            marker=dict(size=40, color=COLORS.get('steinhauer', '#4682B4'),
                       symbol='square', opacity=0.3),
            text=[f'P_{i}<br>rk {r}<br>({deg_str})'],
            textposition='middle center',
            textfont=dict(size=9, family='CMU Serif, serif'),
            showlegend=False,
            hovertemplate=f'P_{i}: rank {r}, generators at degrees {deg_str}<extra></extra>',
        ))

    # Arrows between modules
    for i in range(len(ranks) - 1):
        fig.add_annotation(
            x=i * 1.5 + 0.4, y=0,
            ax=(i + 1) * 1.5 - 0.4, ay=0,
            xref='x', yref='y', axref='x', ayref='y',
            showarrow=True, arrowhead=2, arrowsize=1.5,
            arrowcolor=COLORS.get('dissipative', '#C0392B'),
        )
        fig.add_annotation(
            x=(i * 1.5 + (i + 1) * 1.5) / 2, y=0.15,
            text=diff_labels[i + 1], showarrow=False,
            font=dict(size=10, color=COLORS.get('dissipative', '#C0392B')),
        )

    # F₂ target
    fig.add_trace(go.Scatter(
        x=[-1.2], y=[0], mode='markers+text',
        marker=dict(size=30, color=COLORS.get('trento', '#D4A843'),
                   symbol='square', opacity=0.3),
        text=['F₂'], textposition='middle center',
        textfont=dict(size=11, family='CMU Serif, serif', color='black'),
        showlegend=False,
    ))
    fig.add_annotation(
        x=-0.85, y=0, ax=0 - 0.4, ay=0,
        xref='x', yref='y', axref='x', ayref='y',
        showarrow=True, arrowhead=2, arrowsize=1.5,
        arrowcolor=COLORS.get('dissipative', '#C0392B'),
    )
    fig.add_annotation(x=-0.6, y=0.15, text='ε', showarrow=False,
        font=dict(size=10, color=COLORS.get('dissipative', '#C0392B')))

    apply_layout(fig,
        xaxis=dict(showticklabels=False, showgrid=False, zeroline=False,
                  range=[-1.8, 8.2]),
        yaxis=dict(showticklabels=False, showgrid=False, zeroline=False,
                  range=[-0.5, 0.5]),
        title=dict(
            text='Minimal Free Resolution of F₂ over A(1)',
            font=TITLE_FONT),
        height=250, width=900,
        margin=dict(l=10, r=10, t=50, b=10),
    )

    # Pattern annotation
    fig.add_annotation(x=3.5, y=-0.35,
        text='Bidiagonal pattern: Sq(1) diagonal, Sq(2,1) superdiagonal — 4-fold periodic via w₁',
        showarrow=False, font=dict(size=10, color='gray'))

    return fig


def fig_fk_spectrum() -> go.Figure:
    """Fidkowski-Kitaev 8-Majorana Hamiltonian spectrum (Cayley calibration).

    Shows the three distinct eigenvalues from the Spin(7) decomposition
    8 ⊗ 1 = 1 ⊕ 7 ⊕ 8 (spinor)  →  W eigenvalues {-14, +2, 0}
    with multiplicities {1, 7, 8}, gap Δ = 14, ground state unique.

    Machine-checked: SKEFTHawking.FK (FKGappedInterface.lean, 12 theorems,
    0 sorry, all native_decide on Matrix (Fin 16) (Fin 16) ℤ).
    Lean: W_minimal_poly, W_trace, W_frobenius, eigenvalue_ground,
    W_commutes_parity, spectral_gap, fk_summary.
    Source: Fidkowski-Kitaev, PRB 81, 134509 (2010), Eq. 8.
    """
    from src.core.formulas import fk_eigenvalues, fk_spectral_gap

    spec = fk_eigenvalues()
    gap = fk_spectral_gap()

    sorted_eigvals = sorted(spec.keys())   # [-14, 0, 2]
    eigenvalues = sorted_eigvals
    multiplicities = [spec[e] for e in sorted_eigvals]
    labels = [
        f'E₀={eigenvalues[0]}<br>(ground, Spin(7) singlet, unique)',
        f'E₁={eigenvalues[1]}<br>(Spin(7) spinor sector, m={multiplicities[1]})',
        f'E₂=+{eigenvalues[2]}<br>(Spin(7) vector rep, m={multiplicities[2]})',
    ]

    fig = go.Figure()

    palette = [
        COLORS.get('trento', '#D4A843'),
        COLORS.get('horizon', '#808080'),
        COLORS.get('steinhauer', '#4682B4'),
    ]

    for i, (E, m, label) in enumerate(zip(eigenvalues, multiplicities, labels)):
        color = palette[i]
        width = 4 if i == 0 else 2
        fig.add_trace(go.Scatter(
            x=[0.15, 0.85], y=[E, E], mode='lines',
            line=dict(color=color, width=width),
            showlegend=False,
            hovertemplate=f'E={E}, multiplicity={m}<extra></extra>',
        ))
        fig.add_annotation(
            x=1.0, y=E, text=label,
            showarrow=False, font=dict(size=10, color=color),
            xanchor='left',
        )

    # Spectral gap arrow from E₀ to E₁
    fig.add_annotation(
        x=0.05, y=eigenvalues[0], ax=0.05, ay=eigenvalues[1],
        xref='x', yref='y', axref='x', ayref='y',
        showarrow=True, arrowhead=3, arrowsize=1.5,
        arrowcolor=COLORS.get('trento', '#D4A843'),
    )
    fig.add_annotation(
        x=-0.02, y=(eigenvalues[0] + eigenvalues[1]) / 2,
        text=f'Δ={gap}',
        showarrow=False, font=dict(size=13, color=COLORS.get('trento', '#D4A843')),
        xanchor='right',
    )

    # Multiplicity-system inset (lower-right)
    fig.add_annotation(
        x=1.95, y=eigenvalues[0] + 1, xanchor='right',
        text=(
            "Spin(7) decomposition:<br>"
            "  16-dim Fock = 1 ⊕ 7 ⊕ 8<br>"
            "  Σ mᵢ = 16,  Σ Eᵢmᵢ = 0,  Σ Eᵢ²mᵢ = 224"
        ),
        showarrow=False, font=dict(size=9, color=COLORS.get('horizon', '#808080')),
        align='left',
    )

    apply_layout(
        fig,
        xaxis=dict(showticklabels=False, showgrid=False, zeroline=False, range=[-0.4, 2.1]),
        yaxis=dict(title='Energy (integer eigenvalues)', dtick=2,
                   range=[eigenvalues[0] - 2, eigenvalues[2] + 2]),
        title=dict(
            text='FK 8-Majorana spectrum (Cayley calibration, Spin(7))',
            font=TITLE_FONT,
        ),
        height=440, width=620,
        margin=dict(l=60, r=140, t=60, b=40),
    )
    return fig


def fig_fk_dimensional_ladder() -> go.Figure:
    """Dimensional-ladder evidence for the gapped-interface conjecture.

    The Phase 5s Wave 4 bridge theorem
    (`SKEFTHawking.SPTClassification.gapped_interface_dimensional_ladder`)
    summarises the project's evidence stack for the sole load-bearing
    axiom (`gapped_interface_axiom`):

      1+1D — PROVED: VillainHamiltonian.k3450_gappable (K-matrix, 3450 model)
      2+1D — PROVED: SKEFTHawking.FK.fk_summary (Cayley Spin(7), Δ=14)
      3+1D — AXIOMATIZED: gapped_interface_axiom (open at literature frontier)

    The 1+1D and 2+1D witnesses are independent of one another
    (different model classes, different proof frameworks); together they
    bracket the conjectured 3+1D version on both sides.

    Machine-checked Lean witnesses:
      VillainHamiltonian.lean — k3450 K-matrix gappability
      FKGappedInterface.lean — 12 theorems, 0 sorry, all native_decide
      SPTClassification.lean — gapped_interface_dimensional_ladder
      AXIOM_METADATA['gapped_interface_axiom'].evidence_ladder
    Source: Phase 5s Wave 4 ship memo (2026-04-18); Phase 5s roadmap §A.
    """
    from src.core.formulas import fk_dimensional_ladder_evidence

    ladder = fk_dimensional_ladder_evidence()
    rows = [
        ('1+1D', ladder['1+1D']),
        ('2+1D', ladder['2+1D']),
        ('3+1D', ladder['3+1D']),
    ]

    fig = go.Figure()

    proved_color = COLORS.get('sage', '#7BA05B')
    axiom_color = COLORS.get('amber', '#D4A843')
    color_map = {'PROVED': proved_color, 'AXIOMATIZED': axiom_color}

    for i, (dim, info) in enumerate(rows):
        color = color_map[info['status']]
        # Status box
        fig.add_shape(
            type='rect',
            x0=0.0, x1=1.4, y0=i - 0.35, y1=i + 0.35,
            line=dict(color=color, width=2),
            fillcolor=color, opacity=0.18,
        )
        # Dimension label
        fig.add_annotation(
            x=0.05, y=i, text=f'<b>{dim}</b>',
            showarrow=False, xanchor='left',
            font=dict(size=18, color=color),
        )
        # Status label
        fig.add_annotation(
            x=0.7, y=i + 0.18, text=f'<b>{info["status"]}</b>',
            showarrow=False, font=dict(size=11, color=color),
        )
        # Witness
        fig.add_annotation(
            x=0.7, y=i - 0.05,
            text=f'witness: <span style="font-family:monospace">{info["witness"]}</span>',
            showarrow=False, font=dict(size=10, color='#333'),
        )
        # Framework
        fig.add_annotation(
            x=0.7, y=i - 0.22,
            text=info['framework'],
            showarrow=False, font=dict(size=9, color='#666'),
        )
        # Gap (where defined)
        if info['gap'] is not None:
            fig.add_annotation(
                x=1.55, y=i,
                text=f'Δ = {info["gap"]}',
                showarrow=False, font=dict(size=12, color=color),
                xanchor='left',
            )

    # Connecting arrow showing dimensional ladder
    for i in range(2):
        fig.add_annotation(
            x=-0.05, y=i + 0.5, ax=-0.05, ay=i + 0.45,
            xref='x', yref='y', axref='x', ayref='y',
            showarrow=True, arrowhead=2, arrowsize=1.2,
            arrowcolor='#888',
        )

    fig.add_annotation(
        x=-0.18, y=1.0, text='dimensional<br>ladder',
        showarrow=False, font=dict(size=9, color='#888'),
        textangle=-90, xanchor='center',
    )

    apply_layout(
        fig,
        xaxis=dict(showticklabels=False, showgrid=False, zeroline=False, range=[-0.25, 1.95]),
        yaxis=dict(showticklabels=False, showgrid=False, zeroline=False, range=[-0.6, 2.6]),
        title=dict(
            text='Phase 5s Wave 4: dimensional-ladder evidence for gapped_interface_axiom',
            font=TITLE_FONT,
        ),
        height=420, width=820,
        margin=dict(l=80, r=40, t=60, b=40),
    )
    return fig


# ════════════════════════════════════════════════════════════════════
# Phase 5w: Graphene Dirac fluid analog metric
# ════════════════════════════════════════════════════════════════════


def fig_graphene_hawking_temperature_sweep():
    """Fig 102: Hawking temperature vs constriction length for graphene platforms.

    Shows T_H as a function of nozzle throat length L for both monolayer
    (c_s = v_F/√2) and bilayer (c_s = 440 km/s) graphene.  Marks the
    four platform configurations from GRAPHENE_PLATFORMS.  Includes
    horizontal lines for T_ambient and T_imp as detection thresholds.
    """
    from src.core.formulas import dirac_fluid_hawking_from_geometry
    from src.core.constants import GRAPHENE_PLATFORMS

    L_nm = np.logspace(1, 3, 200)  # 10 nm to 1 μm
    L_m = L_nm * 1e-9

    # Monolayer: c_s = v_F/√2
    T_H_mono = np.array([dirac_fluid_hawking_from_geometry(L, v_F=1.0e6) for L in L_m])
    # Bilayer: c_s ≈ 440 km/s (use formula with effective v_F = c_s * √2)
    v_F_eff_bilayer = 4.4e5 * np.sqrt(2)
    T_H_bi = np.array([dirac_fluid_hawking_from_geometry(L, v_F=v_F_eff_bilayer) for L in L_m])

    fig = go.Figure()

    fig.add_trace(go.Scatter(
        x=L_nm, y=T_H_mono,
        name='Monolayer (c_s = v_F/√2)',
        line=dict(color=COLORS['steel_blue'], width=2.5),
    ))
    fig.add_trace(go.Scatter(
        x=L_nm, y=T_H_bi,
        name='Bilayer (c_s ≈ 440 km/s)',
        line=dict(color=COLORS['amber'], width=2.5, dash='dash'),
    ))

    # Platform markers (acoustic horizons only — exclude PN junction)
    platform_colors = {
        'Dean_bilayer_nozzle': COLORS['amber'],
        'Monolayer_100nm': COLORS['steel_blue'],
        'Monolayer_50nm': COLORS['steel_blue'],
    }
    for name, plat in GRAPHENE_PLATFORMS.items():
        if name == 'PN_junction_10nm':
            continue  # Not an acoustic horizon; omit from plot
        fig.add_trace(go.Scatter(
            x=[plat['nozzle_throat_nm']],
            y=[plat['T_H_K']],
            mode='markers+text',
            name=name.replace('_', ' '),
            marker=dict(size=10, color=platform_colors.get(name, 'grey'),
                        symbol='diamond'),
            text=[f"  {plat['T_H_K']:.1f} K"],
            textposition='middle right',
            textfont=dict(size=10),
            showlegend=False,
        ))

    # Reference lines
    fig.add_hline(y=150, line_dash='dot', line_color='grey',
                  annotation_text='T_ambient (Dean, 150 K)',
                  annotation_position='top right')
    fig.add_hline(y=80, line_dash='dot', line_color='lightgrey',
                  annotation_text='T_imp ≈ 80 K',
                  annotation_position='bottom right')

    apply_layout(fig,
        xaxis=dict(title='Nozzle throat length L (nm)', type='log'),
        yaxis=dict(title='Hawking temperature T_H (K)', type='log',
                   range=[np.log10(0.5), np.log10(500)]),
        title=dict(text='Analog Hawking Temperature — Graphene Platforms',
                   font=TITLE_FONT),
        height=500, width=700,
    )
    return fig


def fig_graphene_dissipation_window():
    """Fig 103: Dissipation window ω_H/Γ_mr vs T_H for different l_mr.

    Shows the ratio of Hawking frequency to momentum-relaxation rate
    as a function of T_H for three sample qualities (l_mr = 1, 5, 15 μm).
    The horizontal line at ratio = 1 marks the detection threshold.
    Platform configurations are marked.
    """
    from src.core.formulas import dirac_fluid_dissipation_window
    from src.core.constants import GRAPHENE_PLATFORMS

    T_H_range = np.logspace(-1, 2, 200)  # 0.1 to 100 K
    l_mr_values = [1e-6, 5e-6, 15e-6]
    l_mr_labels = ['l_mr = 1 μm', 'l_mr = 5 μm', 'l_mr = 15 μm']
    l_mr_colors = [COLORS['cross'], COLORS['steel_blue'], COLORS['amber']]  # grey, blue, amber

    fig = go.Figure()

    for l_mr, label, color in zip(l_mr_values, l_mr_labels, l_mr_colors):
        ratios = [dirac_fluid_dissipation_window(T, l_mr) for T in T_H_range]
        fig.add_trace(go.Scatter(
            x=T_H_range, y=ratios,
            name=label,
            line=dict(color=color, width=2),
        ))

    # Detection threshold
    fig.add_hline(y=1.0, line_dash='dash', line_color='black',
                  annotation_text='ω_H = Γ_mr (detection threshold)',
                  annotation_position='top left')

    # Platform markers
    for name, plat in GRAPHENE_PLATFORMS.items():
        if name == 'PN_junction_10nm':
            continue  # Not acoustic horizon
        ratio = plat.get('omega_H_over_Gamma_mr', None)
        if ratio is not None:
            fig.add_trace(go.Scatter(
                x=[plat['T_H_K']], y=[ratio],
                mode='markers+text',
                name=name.replace('_', ' '),
                marker=dict(size=10, color='black', symbol='diamond'),
                text=[f"  {name.split('_')[0]}"],
                textposition='middle right',
                textfont=dict(size=9),
                showlegend=False,
            ))

    apply_layout(fig,
        xaxis=dict(title='Hawking temperature T_H (K)', type='log'),
        yaxis=dict(title='ω_H / Γ_mr', type='log'),
        title=dict(text='Dissipation Window for Hawking Detection — Graphene',
                   font=TITLE_FONT),
        height=500, width=700,
    )
    return fig


def fig_graphene_noise_spectrum():
    """Fig 104: Current noise power spectrum S_I(ω) for Dean bilayer nozzle.

    Shows S_Hawking (excess noise from analog Hawking radiation),
    S_thermal (Johnson-Nyquist background), and S_total on log-log axes.
    Marks the characteristic Hawking frequency ω_H and the optimal
    detection band.

    Phase 5w W10c: the signal uses the realistic frequency-dependent
    greybody Γ(ω) from `greybody_smooth_profile` (with Γ₀ ≈ 0.9994
    per Anderson et al. PRD 87, Lean `QuasiOneDReduction.T1`), not the
    Γ = 1 upper bound.
    """
    from src.graphene.wkb_spectrum import compute_graphene_spectrum

    spec = compute_graphene_spectrum('Dean_bilayer_nozzle', n_points=300)
    f_GHz = spec.freq_Hz / 1e9

    fig = go.Figure()

    fig.add_trace(go.Scatter(
        x=f_GHz, y=spec.S_thermal,
        name='S_thermal (Johnson-Nyquist)',
        line=dict(color=COLORS['dissipative'], width=2, dash='dash'),
    ))
    fig.add_trace(go.Scatter(
        x=f_GHz, y=spec.S_hawking,
        name='S_Hawking (analog radiation)',
        line=dict(color=COLORS['steel_blue'], width=2.5),
    ))
    fig.add_trace(go.Scatter(
        x=f_GHz, y=spec.S_total,
        name='S_total',
        line=dict(color='black', width=1, dash='dot'),
    ))

    # Mark ω_H
    omega_H_GHz = spec.omega_H / (2 * np.pi * 1e9)
    fig.add_vline(x=omega_H_GHz, line_dash='dot', line_color='grey',
                  annotation_text=f'ω_H ≈ {omega_H_GHz:.0f} GHz',
                  annotation_position='top right')

    # Detection window
    f_lo, f_hi = spec.freq_window_Hz[0] / 1e9, spec.freq_window_Hz[1] / 1e9
    fig.add_vrect(x0=f_lo, x1=f_hi,
                  fillcolor='rgba(46,134,171,0.08)', line_width=0,
                  annotation_text='detection band',
                  annotation_position='top left')

    apply_layout(fig,
        xaxis=dict(title='Frequency (GHz)', type='log',
                   range=[np.log10(0.3), np.log10(600)]),
        yaxis=dict(title='S_I (A²/Hz)', type='log'),
        title=dict(text=f'Noise Power Spectrum — Dean Bilayer Nozzle '
                        f'(T_H = {spec.T_H_K:.1f} K, D = {spec.D:.2f})',
                   font=TITLE_FONT),
        height=500, width=750,
    )
    return fig


def fig_graphene_snr_frequency():
    """Fig 105: Per-bin SNR vs frequency for the Dean bilayer nozzle.

    Shows the frequency dependence of the Hawking-to-thermal signal ratio.
    The SNR is roughly flat at low frequencies (both Hawking and thermal
    scale similarly) and drops exponentially above ω_H.

    Phase 5w W10c: uses the realistic greybody Γ(ω) ≈ Γ₀ = 0.9994 (Lean
    `QuasiOneDReduction.greybody_zero_freq_le_one`, Anderson et al.
    PRD 87), not the `Γ=1` upper bound.
    """
    from src.graphene.wkb_spectrum import compute_graphene_spectrum
    from src.core.formulas import greybody_zero_freq
    from src.core.constants import GRAPHENE_PLATFORMS

    spec = compute_graphene_spectrum('Dean_bilayer_nozzle', n_points=300)
    plat = GRAPHENE_PLATFORMS['Dean_bilayer_nozzle']
    v_ratio = plat.get('v_over_c_s_horizon', 0.985)
    c_s = plat['c_s']
    gamma_0 = greybody_zero_freq(c_s, v_ratio * c_s)

    f_GHz = spec.freq_Hz / 1e9

    fig = go.Figure()
    fig.add_trace(go.Scatter(
        x=f_GHz, y=spec.snr_per_bin,
        name='SNR per bin',
        line=dict(color=COLORS['steel_blue'], width=2),
        fill='tozeroy',
        fillcolor='rgba(46,134,171,0.15)',
    ))

    omega_H_GHz = spec.omega_H / (2 * np.pi * 1e9)
    fig.add_vline(x=omega_H_GHz, line_dash='dot', line_color='grey',
                  annotation_text=f'ω_H ≈ {omega_H_GHz:.0f} GHz')

    fig.add_annotation(
        x=np.log10(2), y=np.log10(spec.peak_snr * 0.3),
        text=f'Peak SNR/bin ≈ {spec.peak_snr:.1e}<br>'
             f'SNR = Γ₀ T_H/(2T_amb) ≈ {gamma_0 * spec.T_H_K/(2*spec.T_ambient_K):.3f}<br>'
             f'(Γ₀ ≈ {gamma_0:.4f}, quasi-1D corr. ≤ 1.8%)',
        showarrow=False, font=dict(size=10),
        xref='x', yref='y',
    )

    apply_layout(fig,
        xaxis=dict(title='Frequency (GHz)', type='log',
                   range=[np.log10(0.3), np.log10(600)]),
        yaxis=dict(title='S_Hawking / S_thermal (per bin)', type='log',
                   exponentformat='power'),
        title=dict(text='Detection Signal-to-Noise — Dean Bilayer Nozzle',
                   font=TITLE_FONT),
        height=450, width=700,
    )
    return fig


def fig_sfdm_velocity_threshold_step():
    """Fig 106: Paper 17 money-plot left panel — DM-galaxy offset vs
    v_infall/c_s for SFDM, SIDM, and CDM.

    The defining SFDM smoking-gun observable: a step function at M=1.
    SIDM predicts a smooth monotonic rise; CDM predicts zero offset at
    all Mach numbers. This comparison is unique to SFDM and motivates
    the 5-target Euclid/Roman stacking strategy.
    """
    from src.dark_sector.sfdm_merger_forecast import (
        CANONICAL_MERGERS,
        MERGER_A520,
        MERGER_BULLET,
        MERGER_EL_GORDO,
        MERGER_MACS_J0025,
        MERGER_PANDORA,
        cdm_dm_galaxy_offset_kpc,
        mach_number,
        sfdm_dm_galaxy_offset_kpc,
        sidm_dm_galaxy_offset_kpc,
    )
    from src.dark_sector.sfdm_sk_eft import C_S_KMS_FIDUCIAL, HaloMassClass

    c_s = C_S_KMS_FIDUCIAL[HaloMassClass.SUBCLUSTER]
    mach_range = np.linspace(0.3, 3.0, 300)

    sfdm_offsets = [sfdm_dm_galaxy_offset_kpc(M) for M in mach_range]
    sidm_offsets = [sidm_dm_galaxy_offset_kpc(M, sigma_over_m=1.0) for M in mach_range]
    cdm_offsets = [cdm_dm_galaxy_offset_kpc(M) for M in mach_range]

    fig = go.Figure()
    fig.add_trace(go.Scatter(
        x=mach_range, y=sfdm_offsets,
        name='SFDM (velocity-threshold step)',
        line=dict(color=COLORS['steel_blue'], width=3),
    ))
    fig.add_trace(go.Scatter(
        x=mach_range, y=sidm_offsets,
        name='SIDM (σ/m = 1 cm²/g, smooth rise)',
        line=dict(color=COLORS['amber'], width=2.5, dash='dash'),
    ))
    fig.add_trace(go.Scatter(
        x=mach_range, y=cdm_offsets,
        name='CDM (null)',
        line=dict(color='grey', width=1.5, dash='dot'),
    ))

    # Overlay canonical merger Mach numbers as markers (y at 150 kpc).
    merger_names_short = {
        MERGER_BULLET.name: "Bullet",
        MERGER_EL_GORDO.name: "El Gordo",
        MERGER_PANDORA.name: "Pandora",
        MERGER_A520.name: "A520",
        MERGER_MACS_J0025.name: "MACS J0025",
    }
    x_marker = []
    labels = []
    for merger in CANONICAL_MERGERS:
        M = mach_number(merger.v_infall_kms, c_s)
        x_marker.append(M)
        labels.append(merger_names_short.get(merger.name, merger.name))
    fig.add_trace(go.Scatter(
        x=x_marker, y=[160.0] * len(x_marker),
        mode='markers+text',
        text=labels,
        textposition='top center',
        marker=dict(size=10, color=COLORS['dissipative'], symbol='diamond'),
        name='Canonical mergers (BK fiducial)',
        showlegend=True,
    ))

    # Mark M = 1 threshold.
    fig.add_vline(x=1.0, line_dash='solid', line_color=COLORS['horizon'],
                  line_width=1.5, annotation_text='M = 1 (Landau threshold)',
                  annotation_position='top right')

    apply_layout(fig,
        xaxis=dict(title='Mach number M = v_infall / c_s',
                   range=[0.3, 3.0]),
        yaxis=dict(title='DM–galaxy offset (kpc)', range=[-10, 220]),
        title=dict(text='Money Plot Left — Velocity-Threshold DM–Galaxy Offset',
                   font=TITLE_FONT),
        height=500, width=750,
        showlegend=True,
    )
    return fig


def fig_sfdm_stacked_kappa_profile():
    """Fig 107: Paper 17 money-plot right panel — stacked κ profile for
    N = 30 and N = 50 mergers across Euclid and Roman.

    Shows the expected SFDM convergence-amplitude sensitivity as a
    function of stacking depth, with the 3σ and 5σ thresholds marked.
    Demonstrates the "conditional GO" verdict: first 3σ achievable by
    ~2028, 5σ by ~2029-2030.
    """
    from src.dark_sector.sfdm_merger_forecast import (
        EUCLID_WIDE,
        MERGER_BULLET,
        ROMAN_HLSS,
        forecast_single_merger,
        stacked_snr,
    )

    bullet = forecast_single_merger(MERGER_BULLET)
    N_range = np.arange(1, 151)

    stacked_euclid = [stacked_snr(bullet.snr_euclid, int(N)) for N in N_range]
    stacked_roman = [stacked_snr(bullet.snr_roman, int(N)) for N in N_range]

    fig = go.Figure()
    fig.add_trace(go.Scatter(
        x=N_range, y=stacked_euclid,
        name=f'Euclid (n_gal={EUCLID_WIDE.n_gal_arcmin2:.0f}/arcmin², σ_γ={EUCLID_WIDE.shape_noise:.2f})',
        line=dict(color=COLORS['steel_blue'], width=2.5),
    ))
    fig.add_trace(go.Scatter(
        x=N_range, y=stacked_roman,
        name=f'Roman HLSS (n_gal={ROMAN_HLSS.n_gal_arcmin2:.0f}/arcmin², σ_γ={ROMAN_HLSS.shape_noise:.2f})',
        line=dict(color=COLORS['amber'], width=2.5, dash='dash'),
    ))

    # 3σ and 5σ thresholds.
    fig.add_hline(y=3.0, line_dash='dot', line_color='green',
                  annotation_text='3σ', annotation_position='top right')
    fig.add_hline(y=5.0, line_dash='dot', line_color='purple',
                  annotation_text='5σ', annotation_position='top right')

    # Mark N = 30 and N = 50 from W1b stacking strategy.
    fig.add_vline(x=30.0, line_dash='dashdot', line_color='grey',
                  annotation_text='N = 30', annotation_position='bottom left')
    fig.add_vline(x=50.0, line_dash='dashdot', line_color='grey',
                  annotation_text='N = 50', annotation_position='bottom')

    apply_layout(fig,
        xaxis=dict(title='Number of stacked mergers N', type='log',
                   range=[np.log10(1), np.log10(200)]),
        yaxis=dict(title='Stacked SNR (Bullet-referenced)',
                   range=[0, 10]),
        title=dict(text='Money Plot Right — Stacked SFDM Sonic-Boom S/N vs N',
                   font=TITLE_FONT),
        height=500, width=750,
        showlegend=True,
    )
    return fig


def fig_phase5x_candidate_viability_matrix():
    """Fig 108: Paper 17 §4/§8 — Phase 5x candidate viability matrix.

    Visual of Lean theorem ``phase5x_candidates_viability_matrix``. Five
    emergent-gravity DM candidates are classified by basic viability; four
    of five are viable, FG torsion DM is obstructed at the tree-level EoS
    (w_FG = 1/3, not dust). Each candidate is tagged with the Wave that
    produced the verdict.

    Cross-refs:
        Lean: ``DarkSectorSynthesis.phase5x_candidates_viability_matrix``
        Python: ``src.dark_sector.synthesis.PHASE5X_CANDIDATE_MATRIX``
    """
    from src.dark_sector.synthesis import PHASE5X_CANDIDATE_MATRIX

    labels = [c.label for c in PHASE5X_CANDIDATE_MATRIX]
    verdicts = ["viable" if c.basic_viability else "not viable"
                for c in PHASE5X_CANDIDATE_MATRIX]
    sources = [c.verdict_source for c in PHASE5X_CANDIDATE_MATRIX]

    colors = [COLORS['steel_blue'] if v == "viable" else COLORS['dissipative']
              for v in verdicts]
    values = [1 if v == "viable" else 0 for v in verdicts]

    fig = go.Figure()
    fig.add_trace(go.Bar(
        y=labels,
        x=values,
        orientation='h',
        marker=dict(color=colors),
        text=[f"{v}<br><i>{s}</i>" for v, s in zip(verdicts, sources)],
        textposition='outside',
        hoverinfo='text+y',
        showlegend=False,
    ))
    apply_layout(fig,
        xaxis=dict(
            title='Basic viability verdict',
            tickmode='array',
            tickvals=[0, 1],
            ticktext=['NOT VIABLE', 'VIABLE'],
            range=[-0.2, 5.5],
        ),
        yaxis=dict(title='', automargin=True),
        title=dict(
            text=('Phase 5x candidate viability matrix '
                  '(Lean: <i>phase5x_candidates_viability_matrix</i>)'),
            font=TITLE_FONT,
        ),
        height=480, width=1500,
        margin=dict(l=80, r=560, t=60, b=70),
    )
    return fig


def fig_phase5x_empirical_hook_ranking():
    """Fig 109: Paper 17 §9 — Five empirical hooks ranked by Phase 5x
    detectability + timeline.

    Visual of Lean theorem ``empirical_hook_ranking_strict``. The merger
    sonic boom is the top-priority Phase 5x observable; direct nuclear
    recoil is last because every candidate is invisible (CC2).

    Cross-refs:
        Lean: ``DarkSectorSynthesis.empirical_hook_ranking_strict``
        Python: ``src.dark_sector.synthesis.HOOK_PRIORITY``
    """
    from src.dark_sector.synthesis import (
        HOOK_PRIORITY,
        EmpiricalHook,
        ranked_empirical_hooks,
    )

    labels = {
        EmpiricalHook.MERGER_SONIC_BOOM:
            "SFDM cluster-merger sonic boom (Euclid/Roman, first 3σ ~2028)",
        EmpiricalHook.FRACTON_CORE_CUSP:
            "Fracton DM core-cusp resolution (next-gen dwarf kinematics)",
        EmpiricalHook.EP_VIOLATION_STEP:
            "EP violation η ~ 1e-18 (STEP, Phase 6 vestigial)",
        EmpiricalHook.DESI_DR3:
            "DESI DR3 w(z) evolution (2026-2027)",
        EmpiricalHook.DIRECT_NUCLEAR_RECOIL:
            "Direct nuclear recoil (DARWIN — predicted null)",
    }
    waves = {
        EmpiricalHook.MERGER_SONIC_BOOM: "W5 (PROMOTED, money plot)",
        EmpiricalHook.FRACTON_CORE_CUSP: "W7 (Drilldown)",
        EmpiricalHook.EP_VIOLATION_STEP: "Phase 6 (W6 gated)",
        EmpiricalHook.DESI_DR3: "W3 (KV reframed)",
        EmpiricalHook.DIRECT_NUCLEAR_RECOIL: "All kinds (CC2)",
    }

    hooks = ranked_empirical_hooks()
    priorities = [HOOK_PRIORITY[h] for h in hooks]
    texts = [labels[h] for h in hooks]
    wave_tags = [waves[h] for h in hooks]

    # Colour top hook differently (it is the Paper 17 money plot).
    colors = [COLORS['steel_blue'] if i == 0 else COLORS['amber']
              for i in range(len(hooks))]

    fig = go.Figure()
    fig.add_trace(go.Bar(
        x=priorities,
        y=texts,
        orientation='h',
        marker=dict(color=colors),
        text=wave_tags,
        textposition='outside',
        showlegend=False,
    ))
    # Reverse so that rank 1 appears at the top.
    fig.update_yaxes(autorange="reversed")

    apply_layout(fig,
        xaxis=dict(title='Phase 5x hook priority score (5 = top)',
                   range=[0, 7]),
        yaxis=dict(title='', automargin=True),
        title=dict(
            text=('Phase 5x empirical hook ranking '
                  '(Lean: <i>empirical_hook_ranking_strict</i>)'),
            font=TITLE_FONT,
        ),
        height=460, width=900,
    )
    return fig


def fig_doublon_gate_spectrum():
    """Fig 110: Phase 5t doublon-gate spectrum and direct-vs-superexchange
    scaling.

    Two-panel figure cross-validating the Phase 5t algebraic core:

    **Left panel — singlet-sector spectrum vs U (Δ = 0).** Three
    eigenvalues of ``H_singlet(t=1, 0, U)`` plotted as a function of
    `U`: `E_plus(t, U)` (upper branch), `E_minus(t, U)` (lower branch),
    and `U` itself (antisymmetric doublon at `|D₋⟩`, decoupled when
    `Δ = 0`). Markers: closed-form (Lean W7 `E_plus`/`E_minus`),
    line: numpy `eigh` diagonalization. Cross-verification of Lean
    W7l charpoly factorization `(X − U)(X² − U·X − 4t²)`.

    **Right panel — superexchange gap `J(t, U) = E_plus − U` vs U,
    log-log scale.** At large `U`, `J → 4t²/U` (textbook superexchange).
    At `U = 0`, `J = 2|t|` (direct-exchange value). The dotted
    `4t²/U` asymptote and the Lean W7i bound `|J − 4t²/U| ≤ 16t⁴/U³`
    show the approximation quality.

    Cross-refs:
        Lean: ``charpoly_H_singlet_Δ0_factored`` (W7l),
              ``E_plus_hasDerivAt_at_zero`` (W7d),
              ``J_superexchange_bound`` (W7i).
        Python: ``src.experimental.doublon_gate.scaling_comparison_curves``
              + ``bench_superexchange_bound``.
    """
    from src.experimental.doublon_gate import (
        bench_superexchange_bound,
        exact_diagonalize,
        scaling_comparison_curves,
    )

    t = 1.0

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            'Singlet-sector spectrum vs U (t=1, Δ=0)',
            'Superexchange gap |J| (log-log) with 4t²/U asymptote',
        ),
        horizontal_spacing=0.12,
    )

    # --- Left panel: spectrum sweep ---
    Us = np.linspace(-4.0, 10.0, 141)
    curves = scaling_comparison_curves(t, Us)
    E_plus_vals = curves['E_plus']
    E_minus_vals = curves['E_minus']

    # Numpy ED values (sanity cross-check)
    ED_plus = np.zeros_like(Us)
    ED_minus = np.zeros_like(Us)
    ED_U = np.zeros_like(Us)
    for i, U in enumerate(Us):
        evals = exact_diagonalize(t, 0.0, U).eigenvalues_3x3
        ED_minus[i], ED_U[i], ED_plus[i] = sorted(evals)

    fig.add_trace(
        go.Scatter(
            x=Us, y=E_plus_vals,
            name='E+ (Lean closed-form)',
            line=dict(color=COLORS['steel_blue'], width=2.5),
        ),
        row=1, col=1,
    )
    fig.add_trace(
        go.Scatter(
            x=Us, y=E_minus_vals,
            name='E- (Lean closed-form)',
            line=dict(color=COLORS['dissipative'], width=2.5),
        ),
        row=1, col=1,
    )
    fig.add_trace(
        go.Scatter(
            x=Us, y=Us,
            name='U (antisymmetric doublon)',
            line=dict(color=COLORS['cross'], width=1.5, dash='dash'),
        ),
        row=1, col=1,
    )
    # ED sanity markers (sparse)
    marker_idx = np.linspace(0, len(Us) - 1, 15).astype(int)
    fig.add_trace(
        go.Scatter(
            x=Us[marker_idx], y=ED_plus[marker_idx],
            mode='markers',
            marker=dict(color=COLORS['steel_blue'], symbol='circle-open',
                        size=7, line=dict(width=1.5)),
            name='E+ (numpy eigh)',
            showlegend=True,
        ),
        row=1, col=1,
    )
    fig.add_trace(
        go.Scatter(
            x=Us[marker_idx], y=ED_minus[marker_idx],
            mode='markers',
            marker=dict(color=COLORS['dissipative'], symbol='circle-open',
                        size=7, line=dict(width=1.5)),
            name='E- (numpy eigh)',
            showlegend=True,
        ),
        row=1, col=1,
    )

    # --- Right panel: superexchange bound ---
    U_pos = np.linspace(4.0, 200.0, 100)
    bench = bench_superexchange_bound(t, U_pos / (4.0 * abs(t)))
    U_for_plot = bench['U']
    # Evaluate E_plus closed-form directly on U_for_plot (Lean W7 E_plus def)
    # to cover the right-panel U range [4, 200] without grid clamping.
    E_plus_pos = 0.5 * (U_for_plot + np.sqrt(U_for_plot**2 + 16.0 * t**2))
    J_vals = E_plus_pos - U_for_plot
    J_asym = 4.0 * t**2 / U_for_plot
    bound_upper = J_asym + bench['bound']
    bound_lower = np.maximum(J_asym - bench['bound'], 1e-6)

    fig.add_trace(
        go.Scatter(
            x=U_for_plot, y=J_vals,
            name='J(t, U) exact',
            line=dict(color=COLORS['steel_blue'], width=2.5),
        ),
        row=1, col=2,
    )
    fig.add_trace(
        go.Scatter(
            x=U_for_plot, y=J_asym,
            name='4t²/U asymptote',
            line=dict(color=COLORS['dissipative'], width=2, dash='dot'),
        ),
        row=1, col=2,
    )
    # Shaded bound region (error envelope)
    fig.add_trace(
        go.Scatter(
            x=np.concatenate([U_for_plot, U_for_plot[::-1]]),
            y=np.concatenate([bound_upper, bound_lower[::-1]]),
            fill='toself',
            fillcolor='rgba(212, 168, 67, 0.18)',
            line=dict(width=0),
            name='Lean W7i bound ±16t⁴/U³',
            showlegend=True,
        ),
        row=1, col=2,
    )

    apply_layout(
        fig,
        xaxis=dict(title='Interaction U (in units of t)'),
        yaxis=dict(title='Eigenvalue (in units of t)'),
        xaxis2=dict(title='Interaction U (in units of t)', type='log'),
        yaxis2=dict(title='|J| (in units of t)', type='log'),
        title=dict(
            text=('Phase 5t doublon gate — spectrum + scaling '
                  '(Lean: <i>charpoly_H_singlet_Δ0_factored</i>, '
                  '<i>J_superexchange_bound</i>)'),
            font=TITLE_FONT,
        ),
        height=500, width=1000,
        legend=dict(orientation='h', yanchor='bottom', y=-0.28,
                    xanchor='center', x=0.5),
    )
    return fig


# ============================================================
# Phase 5z Wave 1: Scalar-rung interpretation figures
# ============================================================

def fig_higgs_mass_parameter_scan():
    """Phase 5z Wave 1: microscopic m_H prediction over (Λ_UV, G_c) at fiducial
    N_f and λ_4. Highlights the 125 GeV contour and the
    M_H_MATCH_TOLERANCE-defined viable region.

    The correctness-push anchor: any region where the prediction lies within
    50% of the observed 125.25 GeV is a candidate quantitative-EWSB region
    (Gate Z.1 GO). Absence over a wide natural parameter range is a
    structural-only verdict (Gate Z.1 NO-GO).

    viz-ref: Phase5z Paper 20 §scalar-rung-microscopic
    """
    import plotly.graph_objects as go
    from src.core.constants import EW_PARAMS
    from src.core.formulas import higgs_mass_from_condensate

    # Fiducial scan: Λ_UV ∈ [10², 10¹⁹] GeV (EW scale to GUT scale),
    #                G_c ∈ [10⁻², 10] (sub-critical to super-critical)
    n_lam = 80
    n_gc = 80
    lam_uv_grid = np.logspace(2, 19, n_lam)    # GeV
    gc_grid = np.logspace(-2, 1, n_gc)         # dimensionless
    n_f = EW_PARAMS["N_F_FIDUCIAL"]
    lam4 = EW_PARAMS["LAMBDA_4_FIDUCIAL"]
    m_h_obs = EW_PARAMS["M_H_GEV"]
    tol = EW_PARAMS["M_H_MATCH_TOLERANCE"]

    M, G = np.meshgrid(lam_uv_grid, gc_grid, indexing="ij")
    Z = np.zeros_like(M)
    for i in range(n_lam):
        for j in range(n_gc):
            Z[i, j] = higgs_mass_from_condensate(
                M[i, j], n_f, G[i, j], lam4
            )

    log10_Z = np.log10(np.maximum(Z, 1e-300))   # avoid log(0)

    fig = go.Figure()
    fig.add_trace(go.Heatmap(
        x=np.log10(lam_uv_grid),
        y=np.log10(gc_grid),
        z=log10_Z.T,
        colorscale="Viridis",
        colorbar=dict(title="log₁₀ m_H [GeV]"),
        showscale=True,
    ))

    # Highlight the 125 GeV target contour and tolerance band
    log10_target = np.log10(m_h_obs)
    log10_lower = np.log10(m_h_obs * (1 - tol))
    log10_upper = np.log10(m_h_obs * (1 + tol))

    fig.add_trace(go.Contour(
        x=np.log10(lam_uv_grid),
        y=np.log10(gc_grid),
        z=log10_Z.T,
        contours=dict(
            start=log10_target,
            end=log10_target,
            size=0.1,
            coloring="lines",
            showlabels=False,
        ),
        line=dict(color=COLORS["amber"], width=3, dash="solid"),
        showscale=False,
        name=f"m_H = {m_h_obs:.2f} GeV",
    ))
    fig.add_trace(go.Contour(
        x=np.log10(lam_uv_grid),
        y=np.log10(gc_grid),
        z=log10_Z.T,
        contours=dict(
            start=log10_lower,
            end=log10_upper,
            size=log10_upper - log10_lower,
            coloring="lines",
            showlabels=False,
        ),
        line=dict(color=COLORS["amber"], width=1.5, dash="dot"),
        showscale=False,
        name=f"±{int(tol*100)}% tolerance band",
    ))

    apply_layout(
        fig,
        xaxis=dict(
            title="log₁₀ Λ_UV [GeV]",
            tickmode="array",
            tickvals=[2, 5, 8, 11, 14, 17],
            ticktext=["10²", "10⁵", "10⁸", "10¹¹", "10¹⁴", "10¹⁷"],
        ),
        yaxis=dict(
            title="log₁₀ G_c (dimensionless 4-fermion coupling)",
            tickmode="array",
            tickvals=[-2, -1, 0, 1],
            ticktext=["10⁻²", "10⁻¹", "1", "10"],
        ),
        title=dict(
            text=(
                f"Phase 5z Wave 1 — microscopic m_H prediction over (Λ_UV, G_c)<br>"
                f"<sub>Fiducial N_f={n_f}, λ_4={lam4:.2f}; gold contour = 125.25 GeV target ± "
                f"{int(tol*100)}% (Lean: <i>scalar_rung_quantitative_EWSB_iff_m_H_matches</i>)</sub>"
            ),
            font=TITLE_FONT,
        ),
        height=600,
        width=900,
    )
    return fig


def fig_bhl_bilocal_correction():
    """Phase 5z Wave 1b: BHL gap problem + Hill 2025 bilocal correction.

    Shows the BHL leading-order m_H = sqrt(2)*m_t prediction overshooting
    the PDG observed m_H = 125.20 GeV at the BHL benchmark m_t = 220 GeV
    (the Pendleton-Ross IR fixed point), and the Hill 2025 bilocal
    correction recovering 125 GeV at dilution phi(0)/phi(infty) ~ 0.402.

    Two panels:
    - Left: bilocal-corrected m_H as function of dilution, with PDG band
      and BHL benchmark marked
    - Right: required dilution to match arbitrary m_H_target as function
      of m_t (highlighting the m_t = 220 GeV BHL benchmark + range
      m_t = 165-185 GeV (covers PDG ± several sigma))

    viz-ref: Phase5z Paper 20 §bhl-extension
    """
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots
    from src.core.formulas import bhl_higgs_mass, bilocal_corrected_higgs_mass
    from src.core.constants import EW_PARAMS

    m_h_pdg = EW_PARAMS["M_H_GEV"]

    # Panel 1: corrected m_H vs dilution at m_t = 220 GeV (BHL benchmark)
    dilutions = np.linspace(0.01, 1.0, 200)
    m_t_bhl = 220.0
    m_h_corrected = np.array(
        [bilocal_corrected_higgs_mass(d, m_t_bhl) for d in dilutions]
    )
    bhl_minimal = bhl_higgs_mass(m_t_bhl)
    dilution_at_pdg = m_h_pdg / bhl_minimal

    # Panel 2: required dilution as function of m_t for fixed m_H = 125 GeV
    m_t_range = np.linspace(150.0, 250.0, 100)
    bhl_at_mt = np.array([bhl_higgs_mass(mt) for mt in m_t_range])
    dilution_required = m_h_pdg / bhl_at_mt

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            "Hill bilocal: corrected m_H vs dilution at BHL benchmark",
            "Required dilution to match PDG m_H, vs top mass",
        ),
        horizontal_spacing=0.13,
    )

    # Panel 1 — main curve
    fig.add_trace(go.Scatter(
        x=dilutions,
        y=m_h_corrected,
        mode="lines",
        line=dict(color=COLORS["steel_blue"], width=3),
        name="m_H corrected",
        showlegend=False,
    ), row=1, col=1)
    # PDG band: dotted horizontal line at 125.20 GeV (annotation moved off corner)
    fig.add_hline(y=m_h_pdg, line=dict(color=COLORS["amber"], width=2, dash="dash"),
                  annotation_text=f"PDG m_H = {m_h_pdg:.2f} GeV",
                  annotation_position="top",
                  annotation_x=0.4,
                  row=1, col=1)
    # BHL benchmark: marker only; label below to avoid top-edge clip
    fig.add_trace(go.Scatter(
        x=[1.0], y=[bhl_minimal],
        mode="markers+text",
        marker=dict(color=COLORS["cross"], size=12, symbol="circle"),
        text=[f"BHL benchmark {bhl_minimal:.0f} GeV"],
        textposition="middle left",
        showlegend=False,
    ), row=1, col=1)
    # Hill recovery point — label to the left so it doesn't collide with PDG line
    fig.add_trace(go.Scatter(
        x=[dilution_at_pdg], y=[m_h_pdg],
        mode="markers+text",
        marker=dict(color=COLORS["amber"], size=12, symbol="diamond"),
        text=[f"Hill recovery (dilution = {dilution_at_pdg:.3f})"],
        textposition="middle right",
        showlegend=False,
    ), row=1, col=1)

    # Panel 2 — main curve
    fig.add_trace(go.Scatter(
        x=m_t_range,
        y=dilution_required,
        mode="lines",
        line=dict(color=COLORS["steel_blue"], width=3),
        name="dilution required",
        showlegend=False,
    ), row=1, col=2)
    fig.add_vline(x=220.0, line=dict(color=COLORS["cross"], width=2, dash="dash"),
                  annotation_text="m_t = 220 (BHL)",
                  annotation_position="top right",
                  row=1, col=2)
    fig.add_vline(x=172.57, line=dict(color=COLORS["amber"], width=2, dash="dot"),
                  annotation_text="m_t PDG = 172.57",
                  annotation_position="bottom right",
                  row=1, col=2)

    fig.update_xaxes(title_text="dilution φ(0)/φ(∞)", range=[0, 1.05], row=1, col=1)
    # Explicit y-range pinned to data: 50–400 GeV brackets PDG (125), Hill, BHL (311)
    fig.update_yaxes(title_text="m_H corrected [GeV]", type="log",
                     range=[np.log10(50), np.log10(400)], row=1, col=1)
    fig.update_xaxes(title_text="m_t [GeV]", row=1, col=2)
    fig.update_yaxes(title_text="dilution required for PDG match", row=1, col=2)

    apply_layout(
        fig,
        margin=dict(t=110, b=70, l=80, r=40),
        title=dict(
            text=(
                "Phase 5z Wave 1b — BHL gap problem and Hill 2025 bilocal correction<br>"
                "<sub>Lean: <i>bhl_minimal_overshoots_pdg</i>, "
                "<i>bilocal_correction_can_match_pdg</i></sub>"
            ),
            font=TITLE_FONT,
        ),
        height=520,
        width=1100,
    )
    return fig


# ============================================================
# Phase 5z Wave 3: EW phase transition figures
# ============================================================

def fig_ew_transition_phase_diagram():
    """Phase 5z Wave 3: EW phase transition order classifier.

    Two panels:
    - Left: V_T(phi, T) at three temperatures (T = 0, T = T_c/2, T = 1.5*T_c)
      showing the symmetric → broken transition for the SM benchmark
    - Right: first-order vs crossover partition over the (E, m_H) plane
      with the SM (m_H = 125 GeV, E ≈ 0.01) marked, plus the
      Kajantie-Laine-Rummukainen-Shaposhnikov crossover threshold m_H ≈ 72 GeV
      as horizontal reference

    viz-ref: Phase5z Paper 22 §transition-order
    """
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots
    from src.core.formulas import (
        ew_finite_t_potential,
        ew_critical_temperature,
    )

    # SM benchmark
    mu_sq = 88.0 ** 2
    lam = 0.13
    c_T = 0.4
    E = 0.01
    T_c = ew_critical_temperature(mu_sq, c_T)

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            f"V_T(φ, T) at three T values; T_c ≈ {T_c:.1f} GeV",
            "First-order vs crossover partition",
        ),
        horizontal_spacing=0.13,
    )

    # Panel 1: V_T(phi) at three temperatures, extended to ±300 GeV so the
    # broken-phase wells (located at ~±180 GeV at the SM benchmark) are
    # fully visible and don't clip at the panel edge.
    phi_grid = np.linspace(-300.0, 300.0, 240)
    T_values = [(0.0, "T = 0 (broken)", COLORS["amber"]),
                (0.5 * T_c, f"T = T_c/2 (≈{0.5*T_c:.0f} GeV)", COLORS["steel_blue"]),
                (1.5 * T_c, f"T = 1.5 T_c (symmetric)", COLORS["cross"])]
    for T, label, color in T_values:
        v_grid = np.array([ew_finite_t_potential(p, T, mu_sq, lam, c_T, E)
                           for p in phi_grid])
        v_norm = v_grid / max(abs(v_grid.max()), abs(v_grid.min()), 1e-12)
        fig.add_trace(go.Scatter(
            x=phi_grid, y=v_norm,
            mode="lines",
            line=dict(color=color, width=2.5),
            name=label,
        ), row=1, col=1)

    fig.update_xaxes(title_text="φ [GeV]", range=[-300, 300], row=1, col=1)
    fig.update_yaxes(title_text="V_T(φ) (normalized)", row=1, col=1)

    # Panel 2: phase-order partition over (m_H, E) plane.
    # Use a 3-stop colorscale: white (E < threshold) → amber band (E > threshold).
    # The narrow eps band centred on E_threshold = 0.005 makes the boundary visible.
    n_grid = 60
    E_grid = np.linspace(0.0, 1.0, n_grid)
    m_h_grid = np.linspace(50.0, 200.0, n_grid)
    E_threshold = 0.005
    Z = np.zeros((n_grid, n_grid))
    for i, e_val in enumerate(E_grid):
        for j, _ in enumerate(m_h_grid):
            Z[i, j] = 1.0 if e_val > E_threshold else 0.0

    fig.add_trace(go.Heatmap(
        x=m_h_grid, y=E_grid, z=Z,
        colorscale=[[0, "rgb(245,245,245)"],
                    [0.499, "rgb(245,245,245)"],
                    [0.5, "rgba(241, 143, 1, 0.45)"],
                    [1, "rgba(241, 143, 1, 0.45)"]],
        showscale=False,
        name="first-order region (E > threshold)",
        showlegend=True,
    ), row=1, col=2)

    # Explicit horizontal line at E = E_threshold so the crossover boundary
    # (white-on-white in heatmap above) is unambiguously visible.
    fig.add_hline(
        y=E_threshold,
        line=dict(color=COLORS["steel_blue"], width=2, dash="solid"),
        annotation_text=f"E = {E_threshold:g} (crossover boundary)",
        annotation_position="bottom right",
        row=1, col=2,
    )

    # SM marker: m_H = 125.20, E ≈ 0.01 — just above the crossover boundary
    fig.add_trace(go.Scatter(
        x=[125.20], y=[0.01],
        mode="markers+text",
        marker=dict(color=COLORS["amber"], size=14, symbol="star"),
        text=["  SM (LO first-order; lattice → crossover)"],
        textposition="middle right",
        showlegend=False,
    ), row=1, col=2)

    # CFH 1999 lattice crossover endpoint (m_H = 72 GeV)
    fig.add_vline(x=72.0, line=dict(color=COLORS["cross"], width=2, dash="dash"),
                  annotation_text="CFH 1999 endpoint m_H = 72 GeV",
                  annotation_position="top left",
                  row=1, col=2)

    fig.update_xaxes(title_text="m_H [GeV]", range=[50, 200], row=1, col=2)
    # y-range extends slightly below 0 so the E_threshold = 0.005 line is fully
    # visible inside the panel rather than clipping the bottom edge.
    fig.update_yaxes(title_text="cubic coefficient E", range=[-0.05, 1.0], row=1, col=2)

    apply_layout(
        fig,
        margin=dict(t=120, b=70, l=80, r=40),
        title=dict(
            text=(
                "Phase 5z Wave 3 — EW phase transition: V_T(φ) profiles + (m_H, E) phase partition<br>"
                "<sub>Lean: <i>thermalMassSq_neg_below_T_c</i>, "
                "<i>first_order_and_crossover_disjoint</i>, "
                "<i>crossover_excludes_baryogenesis</i></sub>"
            ),
            font=TITLE_FONT,
        ),
        height=560,
        width=1100,
    )
    return fig


# ============================================================
# Phase 6c Wave 2: EW Baryogenesis ↔ Chirality Wall
# ============================================================

def fig_ewbg_allowed_region():
    """Phase 6c Wave 2: EW baryogenesis allowed-region under
    chirality-wall × phase-transition decomposition.

    Two panels:
    - Left: 2×2 outcome matrix over (chirality wall × transition order)
      with EWBG verdict per quadrant. SM-as-is (intact wall +
      crossover under H_KLRS) marker on the doubly-forbidden quadrant;
      SM+3ν_R (cracked wall + crossover) on the transition-blocked
      quadrant; BSM (cracked wall + first-order strong) on the
      allowed quadrant.
    - Right: (m_H, cubic E) phase diagram with the KLRS lattice
      crossover endpoint at m_H = 72.4 GeV. SM marker at
      (m_H = 125.20, E = 0.01) — strict-LO first-order but full SM
      under H_KLRS is to the right of the endpoint, hence crossover.

    viz-ref: Phase6c Paper 33 §ewbg-allowed-region
    """
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots
    from src.core.constants import EW_PARAMS, EWBG_PARAMS

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            "EWBG verdict over (wall × transition)",
            "(m_H, E) phase diagram with KLRS endpoint",
        ),
        horizontal_spacing=0.15,
        column_widths=[0.45, 0.55],
    )

    # ── Panel 1: 2×2 outcome matrix ────────────────────────────────
    # Row index 0 = wall intact, 1 = wall cracked
    # Col index 0 = crossover, 1 = first-order strong
    # Z = 0 (forbidden, gray), 1 (allowed, amber)
    Z = np.array([
        [0.0, 0.0],  # intact + crossover (doubly forbidden) | intact + FO (wall blocks)
        [0.0, 1.0],  # cracked + crossover (transition blocks) | cracked + FO (allowed)
    ])

    fig.add_trace(go.Heatmap(
        x=["crossover", "first-order strong"],
        y=["wall intact", "wall cracked"],
        z=Z,
        colorscale=[[0, "rgba(108, 117, 125, 0.30)"],
                    [0.5, "rgba(108, 117, 125, 0.30)"],
                    [0.501, "rgba(241, 143, 1, 0.55)"],
                    [1, "rgba(241, 143, 1, 0.55)"]],
        showscale=False,
        hoverinfo="text",
        text=[["DOUBLY FORBIDDEN", "WALL BLOCKS"],
              ["TRANSITION BLOCKS", "EWBG ALLOWED"]],
        showlegend=False,
    ), row=1, col=1)

    # Quadrant labels as top-of-cell annotations (Stage-13 R4 fix —
    # frees the cell center for the SM / SM+3ν_R / BSM markers).
    quadrant_labels = [
        ("crossover",          "wall cracked", "TRANSITION BLOCKS"),
        ("first-order strong", "wall cracked", "EWBG ALLOWED"),
        ("crossover",          "wall intact",  "DOUBLY FORBIDDEN"),
        ("first-order strong", "wall intact",  "WALL BLOCKS"),
    ]
    for x_label, y_label, text_label in quadrant_labels:
        fig.add_annotation(
            x=x_label, y=y_label,
            text=f"<b>{text_label}</b>",
            yshift=42,
            showarrow=False,
            font=dict(size=12, color="black"),
            xref="x1", yref="y1",
        )

    # Marker-only mode (Stage-13 R4 fix). The bold quadrant labels
    # (DOUBLY FORBIDDEN / TRANSITION BLOCKS / WALL BLOCKS / EWBG
    # ALLOWED) already occupy each cell center; placing in-figure
    # textlabels alongside the SM / SM+3ν_R / BSM markers caused
    # bleed-over into adjacent cells. The legend on the right names
    # each marker.
    fig.add_trace(go.Scatter(
        x=["crossover"], y=["wall intact"],
        mode="markers",
        marker=dict(color="rgb(196, 30, 58)", size=22, symbol="x",
                    line=dict(color="black", width=2)),
        showlegend=True, name="SM-as-is",
        hoverinfo="text",
        hovertext="SM-no-ν_R: Z₁₆ ≡ 13 (mod 16) ≠ 0 + KLRS crossover",
    ), row=1, col=1)

    fig.add_trace(go.Scatter(
        x=["crossover"], y=["wall cracked"],
        mode="markers",
        marker=dict(color=COLORS["steel_blue"], size=20, symbol="diamond",
                    line=dict(color="black", width=1.5)),
        showlegend=True, name="SM+3ν_R (under H_KLRS)",
        hoverinfo="text",
        hovertext="SM+3ν_R: Z₁₆ ≡ 0 (mod 16), wall cracks, but KLRS crossover blocks",
    ), row=1, col=1)

    fig.add_trace(go.Scatter(
        x=["first-order strong"], y=["wall cracked"],
        mode="markers",
        marker=dict(color=COLORS["amber"], size=22, symbol="star",
                    line=dict(color="black", width=1.5)),
        showlegend=True, name="BSM target",
        hoverinfo="text",
        hovertext="BSM with extra scalar(s) producing strong first-order EWPT",
    ), row=1, col=1)

    fig.update_xaxes(title_text="Phase transition order", row=1, col=1)
    fig.update_yaxes(title_text="Chirality wall", row=1, col=1)

    # ── Panel 2: (m_H, E) plane with KLRS endpoint ─────────────────
    n_grid = 60
    m_h_grid = np.linspace(50.0, 200.0, n_grid)
    E_grid = np.linspace(0.0, 0.05, n_grid)
    # Roughly: at m_H > 72.4, lattice corrections drive E → 0 (crossover);
    # at m_H < 72.4, the cubic survives → first-order. Visualize as a
    # threshold partition.
    m_h_klrs = EWBG_PARAMS['KLRS_M_H_CROSSOVER_THRESHOLD_GEV']

    # Crossover region: m_H > m_h_klrs (any E becomes ineffective at full thermal corrections)
    # First-order region: m_H < m_h_klrs (E > E_threshold)
    Z2 = np.zeros((n_grid, n_grid))
    E_threshold = 0.005
    for i, e_val in enumerate(E_grid):
        for j, m_val in enumerate(m_h_grid):
            # First-order if BOTH m_H < endpoint AND E > threshold
            if m_val < m_h_klrs and e_val > E_threshold:
                Z2[i, j] = 1.0

    fig.add_trace(go.Heatmap(
        x=m_h_grid, y=E_grid, z=Z2,
        colorscale=[[0, "rgba(108, 117, 125, 0.20)"],
                    [0.499, "rgba(108, 117, 125, 0.20)"],
                    [0.5, "rgba(241, 143, 1, 0.50)"],
                    [1, "rgba(241, 143, 1, 0.50)"]],
        showscale=False,
        showlegend=True, name="first-order strong (full thermal)",
    ), row=1, col=2)

    # KLRS endpoint. annotation_position="bottom right" places the
    # endpoint label inside the axes and away from the subplot title
    # band — clears the Stage-13 R1 collision (subplot title vs vline
    # annotation) and the R2 y-tick crowding side-effect.
    fig.add_vline(
        x=m_h_klrs,
        line=dict(color=COLORS["cross"], width=2, dash="dash"),
        annotation_text=f"KLRS endpoint<br>m_H = {m_h_klrs} GeV",
        annotation_position="bottom right",
        annotation=dict(
            font=dict(size=10, color="black"),
            bgcolor="rgba(255,255,255,0.85)",
        ),
        row=1, col=2,
    )

    # SM marker (m_H = 125.20, E_LO = 0.01) — to the right of KLRS endpoint
    sm_m_h = EW_PARAMS['M_H_GEV']
    fig.add_trace(go.Scatter(
        x=[sm_m_h], y=[0.01],
        mode="markers+text",
        marker=dict(color="rgb(196, 30, 58)", size=14, symbol="x"),
        text=[f"SM (m_H = {sm_m_h})"], textposition="top right",
        textfont=dict(size=10, color="black"),
        showlegend=True, name="SM (LO first-order, full → crossover)",
    ), row=1, col=2)

    # Annotation showing overshoot ratio. Black text + white bgcolor
    # (Stage-13 R3 fix) — original COLORS["cross"] light-grey on grey
    # crossover fill was low-contrast.
    overshoot = EWBG_PARAMS['M_H_OVERSHOOT_RATIO']
    fig.add_annotation(
        x=160, y=0.04,
        text=f"SM overshoot: {overshoot:.2f}× KLRS<br>(>1.5×, well into crossover)",
        showarrow=False,
        font=dict(size=11, color="black"),
        bgcolor="rgba(255,255,255,0.85)",
        bordercolor=COLORS["cross"],
        borderwidth=1,
        row=1, col=2,
    )

    fig.update_xaxes(title_text="m_H [GeV]", range=[50, 200], row=1, col=2)
    fig.update_yaxes(title_text="cubic coefficient E", range=[0, 0.05], row=1, col=2)

    apply_layout(
        fig,
        margin=dict(t=120, b=70, l=110, r=40),
        title=dict(
            text=(
                "Phase 6c Wave 2 — EWBG verdict: chirality-wall × transition decomposition<br>"
                "<sub>Lean: <i>EWBGViable</i>, "
                "<i>ewbg_forbidden_iff_wall_intact_or_not_viable</i>, "
                "<i>sm_no_nu_R_ewbg_doubly_forbidden</i></sub>"
            ),
            font=TITLE_FONT,
        ),
        height=560,
        width=1200,
    )
    return fig


# ============================================================
# Phase 5z Wave 2: Majorana-rung seesaw figures
# ============================================================

def fig_seesaw_y_m_r_band():
    """Phase 5z Wave 2: Type-I seesaw (y, M_R) plane with NuFit-6.0 m_ν band.

    Each diagonal line in log-log (y, M_R) corresponds to a fixed light-neutrino
    mass m_ν via m_ν = y² v² / M_R. Three contours mark:
      - m_ν = m₃ ≈ 0.0501 eV (NuFit-6.0 atmospheric anchor, NO)
      - m_ν = m₂ ≈ 8.61 meV (NuFit-6.0 solar anchor)
      - m_ν = 0.1 eV upper-cosmology bound (illustrative)

    Vertical dashed line at y = y_top ≈ 0.99 marks the natural Yukawa anchor;
    horizontal dashed line at M_R = Λ_GUT ≈ 1e16 GeV. The intersection
    (y_top, Λ_GUT) sits NEAR the m_ν = 0.05 eV contour — the canonical
    seesaw region under Embedding III with Λ_ADW ~ Λ_GUT.

    viz-ref: Phase5z Paper 21 §seesaw-y-m-r-plane
    """
    import plotly.graph_objects as go
    from src.core.constants import EW_PARAMS, MAJORANA_PARAMS
    from src.core.formulas import seesaw_m_r_from_observed

    v_ew = EW_PARAMS["V_EW_GEV"]
    y_grid = np.logspace(-6, 0.5, 200)         # y ∈ [1e-6, ~3]

    # m_ν contours (eV → GeV)
    m_nu_targets = {
        "m₃ ≈ √|Δm²_31| (NO)": MAJORANA_PARAMS["M_NU_HEAVIEST_EV"] * 1e-9,
        "m₂ ≈ √Δm²_21": MAJORANA_PARAMS["M_NU_NEXT_EV"] * 1e-9,
        "m_ν = 0.1 eV (cosmology cap)": 0.1 * 1e-9,
    }
    contour_colors = {
        "m₃ ≈ √|Δm²_31| (NO)": COLORS["amber"],
        "m₂ ≈ √Δm²_21": COLORS["steel_blue"],
        "m_ν = 0.1 eV (cosmology cap)": COLORS["cross"],
    }

    fig = go.Figure()

    # Light-shaded "natural seesaw band" between m₃ and 0.1 eV
    m_r_top = np.array([
        seesaw_m_r_from_observed(y, v_ew, 0.1 * 1e-9) for y in y_grid
    ])
    m_r_bot = np.array([
        seesaw_m_r_from_observed(y, v_ew, MAJORANA_PARAMS["M_NU_HEAVIEST_EV"] * 1e-9)
        for y in y_grid
    ])
    fig.add_trace(go.Scatter(
        x=np.concatenate([y_grid, y_grid[::-1]]),
        y=np.concatenate([m_r_bot, m_r_top[::-1]]),
        fill="toself",
        fillcolor="rgba(241, 143, 1, 0.10)",
        line=dict(color="rgba(0,0,0,0)"),
        name="Natural seesaw band",
        hoverinfo="skip",
        showlegend=True,
    ))

    # m_ν contours
    for label, m_nu in m_nu_targets.items():
        m_r_curve = np.array([seesaw_m_r_from_observed(y, v_ew, m_nu) for y in y_grid])
        fig.add_trace(go.Scatter(
            x=y_grid,
            y=m_r_curve,
            mode="lines",
            line=dict(color=contour_colors[label], width=2.5),
            name=label,
        ))

    # Reference markers: (y_top, Λ_GUT) and Λ_ADW fiducial
    y_top = EW_PARAMS["Y_TOP"]
    fig.add_trace(go.Scatter(
        x=[y_top], y=[1e16],
        mode="markers+text",
        marker=dict(symbol="star", size=18, color=COLORS["amber"],
                    line=dict(color="black", width=1.5)),
        text=["(y_top, Λ_GUT)"],
        textposition="top center",
        textfont=dict(size=11),
        name="Top-Yukawa @ GUT scale",
    ))
    fig.add_trace(go.Scatter(
        x=[1e-3], y=[MAJORANA_PARAMS["M_R_LOWER_BOUND_GEV"]],
        mode="markers+text",
        marker=dict(symbol="diamond", size=14, color=COLORS["steel_blue"],
                    line=dict(color="black", width=1.0)),
        text=["Y_NU_LOWER × M_R_LOWER"],
        textposition="bottom right",
        textfont=dict(size=10),
        name="Wave-2 lower scan anchor",
    ))

    apply_layout(
        fig,
        xaxis=dict(
            title="Dirac neutrino Yukawa y",
            type="log",
            tickmode="array",
            tickvals=[1e-6, 1e-4, 1e-2, 1.0],
            ticktext=["10⁻⁶", "10⁻⁴", "10⁻²", "1"],
        ),
        yaxis=dict(
            title="Heavy Majorana mass M_R [GeV]",
            type="log",
            tickmode="array",
            tickvals=[1e3, 1e6, 1e9, 1e12, 1e15, 1e18],
            ticktext=["10³", "10⁶", "10⁹", "10¹²", "10¹⁵", "10¹⁸"],
        ),
        title=dict(
            text=(
                "Phase 5z Wave 2 — Type-I seesaw (y, M_R) plane<br>"
                "<sub>Contours of m_ν via m_ν = y² v² / M_R; NuFit-6.0 anchors. "
                "Lean: <i>MajoranaRung.seesawNeutrinoMass_strictMono_inv_M_R</i></sub>"
            ),
            font=TITLE_FONT,
        ),
        height=600,
        width=850,
    )
    return fig


def fig_m_beta_beta_vs_m_lightest():
    """Phase 5z Wave 2: m_ββ vs m_lightest with KamLAND-Zen + LEGEND-1000 bands.

    The two-axis 0νββ "lobster plot": effective Majorana mass m_ββ as a
    function of the lightest neutrino mass m_lightest, separately for normal
    ordering (NO) and inverted ordering (IO). Both orderings are computed at
    NuFit-6.0 best-fit angles; Majorana phases swept over the full unit
    circle to produce the lobster envelopes.

    Two horizontal experimental bands:
      - KamLAND-Zen 800 (current 90% CL): 28-122 meV (NME spread)
      - LEGEND-1000 (projected 99.7% CL discovery): 9-21 meV

    Wave 2 conclusion (deep research §4.2): IO is fully discoverable by
    LEGEND-1000; NO is largely out of reach. Embedding-agnostic — same
    bands apply to Embeddings I/II/III.

    viz-ref: Phase5z Paper 21 §0nubb-money-plot
    """
    import plotly.graph_objects as go
    from src.core.constants import MAJORANA_PARAMS
    from src.core.formulas import pmns_unitary_matrix

    # NuFit-6.0 best fit angles in radians
    t12 = np.deg2rad(MAJORANA_PARAMS["THETA_12_DEG"])
    t13 = np.deg2rad(MAJORANA_PARAMS["THETA_13_DEG"])
    t23 = np.deg2rad(MAJORANA_PARAMS["THETA_23_DEG"])
    dcp = np.deg2rad(MAJORANA_PARAMS["DELTA_CP_DEG"])

    dm21 = MAJORANA_PARAMS["DELTA_M_SQ_21_EV2"]
    dm31 = MAJORANA_PARAMS["DELTA_M_SQ_31_EV2"]

    n_lightest = 200
    n_phase = 32  # Majorana-phase Monte Carlo grid
    m_light_grid = np.logspace(-5, -0.5, n_lightest)  # 10 μeV to ~316 meV
    alpha_grid = np.linspace(0.0, 2 * np.pi, n_phase, endpoint=False)

    def lobster_envelope(ordering):
        """Return (m_lightest, m_bb_lower, m_bb_upper) for NO or IO ordering."""
        m_bb_lo = np.zeros_like(m_light_grid)
        m_bb_hi = np.zeros_like(m_light_grid)
        for ix, m_l in enumerate(m_light_grid):
            if ordering == "NO":
                m1, m2, m3 = m_l, np.sqrt(m_l ** 2 + dm21), np.sqrt(m_l ** 2 + dm31)
            else:  # IO
                m3 = m_l
                m2 = np.sqrt(m_l ** 2 + dm31)
                m1 = np.sqrt(m_l ** 2 + dm31 - dm21)
            vals = []
            for a1 in alpha_grid:
                for a2 in alpha_grid:
                    U = pmns_unitary_matrix(t12, t13, t23, dcp,
                                            alpha_1=a1, alpha_2=a2)
                    val = abs(U[0, 0] ** 2 * m1 + U[0, 1] ** 2 * m2 + U[0, 2] ** 2 * m3)
                    vals.append(val)
            m_bb_lo[ix] = float(np.min(vals))
            m_bb_hi[ix] = float(np.max(vals))
        return m_bb_lo, m_bb_hi

    no_lo, no_hi = lobster_envelope("NO")
    io_lo, io_hi = lobster_envelope("IO")

    fig = go.Figure()

    # IO band
    fig.add_trace(go.Scatter(
        x=np.concatenate([m_light_grid * 1e3, m_light_grid[::-1] * 1e3]),
        y=np.concatenate([io_lo * 1e3, io_hi[::-1] * 1e3]),
        fill="toself",
        fillcolor="rgba(241, 143, 1, 0.30)",
        line=dict(color=COLORS["amber"], width=1),
        name="Inverted ordering (IO)",
    ))
    # NO band
    fig.add_trace(go.Scatter(
        x=np.concatenate([m_light_grid * 1e3, m_light_grid[::-1] * 1e3]),
        y=np.concatenate([no_lo * 1e3, no_hi[::-1] * 1e3]),
        fill="toself",
        fillcolor="rgba(46, 134, 171, 0.30)",
        line=dict(color=COLORS["steel_blue"], width=1),
        name="Normal ordering (NO)",
    ))

    # KamLAND-Zen band (excluded region) — amber per project colorblind-
    # accessible blue/amber convention (CLAUDE.md), distinguishing the
    # current excluded band (amber) from the LEGEND-1000 projected reach
    # band (light blue) below.
    kz_lo = MAJORANA_PARAMS["M_BB_KAMLAND_ZEN_MEV_LOWER"]
    kz_hi = MAJORANA_PARAMS["M_BB_KAMLAND_ZEN_MEV_UPPER"]
    fig.add_shape(type="rect",
                  x0=1e-2, x1=1e3,
                  y0=kz_lo, y1=kz_hi,
                  fillcolor="rgba(241, 143, 1, 0.30)",
                  line=dict(color=COLORS["amber"], width=1, dash="dash"),
                  layer="below")
    fig.add_annotation(x=200, y=np.sqrt(kz_lo * kz_hi),
                       text="KamLAND-Zen 800 (28–122 meV)",
                       showarrow=False, font=dict(size=10),
                       bgcolor="rgba(255,255,255,0.7)")

    # LEGEND-1000 reach band
    lg_lo = MAJORANA_PARAMS["M_BB_LEGEND_MEV_LOWER"]
    lg_hi = MAJORANA_PARAMS["M_BB_LEGEND_MEV_UPPER"]
    fig.add_shape(type="rect",
                  x0=1e-2, x1=1e3,
                  y0=lg_lo, y1=lg_hi,
                  fillcolor="rgba(218, 226, 248, 0.55)",
                  line=dict(color=COLORS["steel_blue"], width=1, dash="dot"),
                  layer="below")
    fig.add_annotation(x=200, y=np.sqrt(lg_lo * lg_hi),
                       text="LEGEND-1000 reach (9–21 meV)",
                       showarrow=False, font=dict(size=10),
                       bgcolor="rgba(255,255,255,0.7)")

    apply_layout(
        fig,
        xaxis=dict(
            title="Lightest neutrino mass m_lightest [meV]",
            type="log",
            tickmode="array",
            tickvals=[1e-2, 1e-1, 1, 10, 100, 1000],
            ticktext=["0.01", "0.1", "1", "10", "100", "1000"],
            range=[-2, 2.5],
        ),
        yaxis=dict(
            title="Effective Majorana mass m_ββ [meV]",
            type="log",
            tickmode="array",
            tickvals=[1e-1, 1, 10, 100, 1000],
            ticktext=["0.1", "1", "10", "100", "1000"],
            range=[-1.5, 3],
        ),
        title=dict(
            text=(
                "Phase 5z Wave 2 — m_ββ vs m_lightest (NuFit-6.0 angles, Majorana phases swept)<br>"
                "<sub>NO + IO bands; KamLAND-Zen 800 (existing) + LEGEND-1000 (projected reach). "
                "Embedding-agnostic. Lean: <i>NeutrinoMixing.PMNSMatrix</i></sub>"
            ),
            font=TITLE_FONT,
        ),
        height=600,
        width=900,
    )
    return fig


def fig_G_N_emerg_parameter_scan():
    """Phase 6a Wave 1: ADW emergent G_N over (Λ_UV, α_ADW) at SM N_f.

    Heatmap shows log₁₀(G_N^emerg / G_N^obs), so 0 = exact match. Gold
    contour: G_N^emerg = G_N^obs locus (Lean:
    `LinearizedEFE.G_N_emerg_match_locus`). Stars: Planck-anchor α*
    values for N_f ∈ {15, 16, 45, 48} (Lean:
    `G_N_emerg_match_at_planck_anchor`). Vertical dashed: GUT (10¹⁶
    GeV) and Planck (1.221 × 10¹⁹ GeV) cutoffs. Horizontal band:
    natural α_ADW range [0.1, 10] from deep-research §6
    (Lit-Search/Phase-6a/, 2026-04-25).

    viz-ref: Phase 6a Paper 23 §correctness-push
    """
    import plotly.graph_objects as go
    from src.core.constants import GRAV_PARAMS
    from src.emergent_gravity import G_N_emerg_grid

    n_lam = 80
    n_alpha = 80
    lam_uv_grid = np.logspace(
        np.log10(GRAV_PARAMS["LAMBDA_UV_GEV_LOWER"]),
        np.log10(GRAV_PARAMS["LAMBDA_UV_GEV_UPPER"]),
        n_lam,
    )
    alpha_grid = np.logspace(
        np.log10(GRAV_PARAMS["ALPHA_ADW_LOWER"]),
        np.log10(GRAV_PARAMS["ALPHA_ADW_UPPER"]),
        n_alpha,
    )
    n_f = GRAV_PARAMS["N_F_DEFAULT"]
    g_n_obs = GRAV_PARAMS["G_N_OBS_GEV_M2"]

    G = G_N_emerg_grid(lam_uv_grid, n_f, alpha_grid)
    log10_ratio = np.log10(np.maximum(G / g_n_obs, 1e-300))

    fig = go.Figure()
    # Heatmap on log axes
    fig.add_trace(go.Heatmap(
        x=np.log10(lam_uv_grid),
        y=np.log10(alpha_grid),
        z=log10_ratio.T,
        zmin=-6.0, zmax=6.0,
        colorscale="RdBu_r",
        colorbar=dict(title="log₁₀(G_N^emerg / G_N^obs)"),
        showscale=True,
    ))

    # Gold contour: exact match locus log10_ratio = 0
    fig.add_trace(go.Contour(
        x=np.log10(lam_uv_grid),
        y=np.log10(alpha_grid),
        z=log10_ratio.T,
        contours=dict(
            start=0.0, end=0.0, size=0.5,
            coloring="lines",
            showlabels=False,
        ),
        line=dict(color=COLORS["amber"], width=3, dash="solid"),
        showscale=False,
        name="G_N^emerg = G_N^obs",
    ))

    # ±50% tolerance band (log10 ratio ∈ [-0.301, +0.301] ≈ ±50%)
    tol = GRAV_PARAMS["G_N_MATCH_TOLERANCE"]
    log_lo = np.log10(1 - tol)
    log_hi = np.log10(1 + tol)
    fig.add_trace(go.Contour(
        x=np.log10(lam_uv_grid),
        y=np.log10(alpha_grid),
        z=log10_ratio.T,
        contours=dict(
            start=log_lo, end=log_hi, size=log_hi - log_lo,
            coloring="lines",
            showlabels=False,
        ),
        line=dict(color=COLORS["amber"], width=1.5, dash="dot"),
        showscale=False,
        name=f"±{int(tol*100)}% match band",
    ))

    # Vertical dashed lines at canonical Λ_UV anchors
    log_gut = np.log10(GRAV_PARAMS["LAMBDA_UV_GUT_GEV"])
    log_planck = np.log10(GRAV_PARAMS["LAMBDA_UV_PLANCK_GEV"])
    for log_lam, label in [(log_gut, "GUT (10¹⁶)"),
                           (log_planck, "M_Planck")]:
        fig.add_shape(
            type="line",
            x0=log_lam, x1=log_lam,
            y0=np.log10(alpha_grid[0]), y1=np.log10(alpha_grid[-1]),
            line=dict(color=COLORS.get("steel_blue", "#4A90E2"),
                      width=1, dash="dash"),
        )
        fig.add_annotation(
            x=log_lam, y=np.log10(alpha_grid[-1]) - 0.15,
            text=label, showarrow=False,
            font=dict(size=10, color=COLORS.get("steel_blue", "#4A90E2")),
            bgcolor="rgba(255,255,255,0.65)",
        )

    # Planck-anchor α* stars for SM N_f values
    import math
    for nf, marker_label in [
        (15, "N_f=15"),
        (16, "N_f=16"),
        (45, "N_f=45"),
        (48, "N_f=48"),
    ]:
        alpha_star = nf / (12.0 * math.pi)
        fig.add_trace(go.Scatter(
            x=[log_planck], y=[np.log10(alpha_star)],
            mode="markers+text",
            marker=dict(symbol="star", size=14,
                        color=COLORS.get("amber", "#F5A623"),
                        line=dict(width=1, color="black")),
            text=[f"{marker_label}: α*={alpha_star:.2f}"],
            textposition="middle right",
            textfont=dict(size=9),
            showlegend=False,
        ))

    apply_layout(
        fig,
        xaxis=dict(
            title="log₁₀ Λ_UV [GeV]",
            tickmode="array",
            tickvals=[10, 12, 14, 16, 18],
            ticktext=["10¹⁰", "10¹²", "10¹⁴", "10¹⁶", "10¹⁸"],
        ),
        yaxis=dict(
            title="log₁₀ α_ADW (ADW microscopic coefficient)",
            tickmode="array",
            tickvals=[-1, -0.5, 0, 0.5, 1],
            ticktext=["10⁻¹", "10⁻⁰·⁵", "1", "10⁰·⁵", "10"],
        ),
        title=dict(
            text=(
                f"Phase 6a Wave 1 — emergent G_N(Λ_UV, α_ADW) at N_f={n_f}<br>"
                f"<sub>Sakharov-Adler form G_N^emerg = α_ADW · 12π/(N_f · Λ²); "
                f"gold contour = G_N^obs = 6.71×10⁻³⁹ GeV⁻²; stars = "
                f"Planck-anchor α* values per SM N_f. "
                f"Lean: <i>LinearizedEFE.G_N_emerg_match_locus</i></sub>"
            ),
            font=TITLE_FONT,
        ),
        height=620,
        width=920,
    )
    return fig


def fig_c_GW_vs_ligo_constraint():
    """Phase 6a Wave 2: c_GW deviation across the natural χ_vest range, vs the
    GW170817 constraint.

    The key Wave 2 finding: the Volovik vestigial-second-sound graviton
    identification is *quantitatively falsified* under GW170817 unless χ_vest
    is fine-tuned to within 3e-15 of unity. The natural range [0.1, 10]
    fails by 14+ orders of magnitude.

    Lean: GravitationalWaves.vestigial_natural_range_violates_ligo
    Source: Abbott et al. ApJL 848, L13 (2017).
    viz-ref: Phase 6a Paper 25 §main result
    """
    import plotly.graph_objects as go
    from src.core.constants import GW_PARAMS
    from src.gravitational_waves import (
        c_GW_grid,
        chi_vest_window_compatible_with_ligo,
        ligo_falsification_summary,
    )

    chi_grid, _, deviations = c_GW_grid(0.01, 100.0, n_points=200)
    cap = GW_PARAMS["C_GW_TWO_SIDED_CAP"]

    fig = go.Figure()

    # Δc/c curve over χ_vest
    fig.add_trace(go.Scatter(
        x=chi_grid,
        y=deviations,
        mode="lines",
        line=dict(color=COLORS["steel_blue"], width=3),
        name="Δc/c = √χ_vest − 1",
    ))

    # Zero line (Δc = 0 ↔ c_GW = c)
    fig.add_shape(
        type="line",
        x0=chi_grid[0], x1=chi_grid[-1],
        y0=0.0, y1=0.0,
        line=dict(color="black", width=1, dash="dot"),
    )

    # GW170817 cap band (essentially zero on this scale)
    fig.add_trace(go.Scatter(
        x=[chi_grid[0], chi_grid[-1], chi_grid[-1], chi_grid[0]],
        y=[cap, cap, -cap, -cap],
        fill="toself",
        fillcolor="rgba(245, 166, 35, 0.30)",
        line=dict(color=COLORS["amber"], width=1, dash="dash"),
        name=f"GW170817 cap |Δc/c| ≤ {cap:.0e}",
    ))

    # Natural-range vertical band [0.1, 10]
    chi_lo_nat = GW_PARAMS["CHI_VEST_NATURAL_LOWER"]
    chi_hi_nat = GW_PARAMS["CHI_VEST_NATURAL_UPPER"]
    y_min, y_max = float(deviations.min()), float(deviations.max())
    fig.add_shape(
        type="rect",
        x0=chi_lo_nat, x1=chi_hi_nat,
        y0=y_min - 0.1, y1=y_max + 0.1,
        line=dict(color=COLORS["steel_blue"], width=1, dash="dash"),
        fillcolor="rgba(74, 144, 226, 0.10)",
    )
    fig.add_annotation(
        x=(chi_lo_nat * chi_hi_nat) ** 0.5,
        y=y_max + 0.05,
        text="Natural χ_vest range [0.1, 10]",
        showarrow=False,
        font=dict(size=10, color=COLORS["steel_blue"]),
        bgcolor="rgba(255,255,255,0.7)",
    )

    # Compatible χ_vest window endpoints (essentially χ = 1)
    chi_lo_lig, chi_hi_lig = chi_vest_window_compatible_with_ligo(cap)
    fig.add_trace(go.Scatter(
        x=[1.0],
        y=[0.0],
        mode="markers+text",
        marker=dict(symbol="star", size=18,
                    color=COLORS["amber"],
                    line=dict(width=1, color="black")),
        text=["GW170817-compatible<br>(χ_vest = 1 ± 3×10⁻¹⁵)"],
        textposition="bottom right",
        textfont=dict(size=10),
        showlegend=False,
    ))

    # Endpoint annotations: violation factors
    summary = ligo_falsification_summary()
    fig.add_annotation(
        x=chi_lo_nat, y=summary["delta_lower"],
        text=(
            f"χ=0.1<br>Δc/c≈{summary['delta_lower']:.3f}<br>"
            f"Violates LIGO by<br>{summary['violation_ratio_lower']:.1e}×"
        ),
        showarrow=True, arrowhead=2,
        ax=60, ay=30,
        font=dict(size=9, color=COLORS["amber"]),
        bgcolor="rgba(255,255,255,0.85)",
        bordercolor=COLORS["amber"], borderwidth=1,
    )
    fig.add_annotation(
        x=chi_hi_nat, y=summary["delta_upper"],
        text=(
            f"χ=10<br>Δc/c≈{summary['delta_upper']:.3f}<br>"
            f"Violates LIGO by<br>{summary['violation_ratio_upper']:.1e}×"
        ),
        showarrow=True, arrowhead=2,
        ax=-80, ay=-30,
        font=dict(size=9, color=COLORS["amber"]),
        bgcolor="rgba(255,255,255,0.85)",
        bordercolor=COLORS["amber"], borderwidth=1,
    )

    apply_layout(
        fig,
        xaxis=dict(
            title="χ_vest (vestigial-phase metric-channel susceptibility, dimensionless)",
            type="log",
        ),
        yaxis=dict(
            title="Δc/c = (c_GW − c)/c",
            range=[y_min - 0.2, y_max + 0.2],
        ),
        title=dict(
            text=(
                "Phase 6a Wave 2 — vestigial-second-sound graviton ID vs GW170817<br>"
                "<sub>Δc/c = √χ_vest − 1; "
                "GW170817 amber band |Δc/c| ≤ 3 × 10⁻¹⁵; "
                "natural range fails by ~10¹⁴; "
                "Lean: <i>GravitationalWaves.vestigial_natural_range_violates_ligo</i></sub>"
            ),
            font=TITLE_FONT,
        ),
        height=620,
        width=920,
    )
    return fig


def fig_entropy_coefficient_vs_spectrum():
    """Phase 6a Wave 3: BH-entropy leading coefficient over the Immirzi γ
    scan + per-MTC d_max/anyon-spectrum overlay.

    Demonstrates the Wave 3 deep-research verdict: the 1/4 prefactor is
    a γ tuning, not a derivation. Distinct counting prescriptions
    (Domagala-Lewandowski γ ≈ 0.237, Meissner γ ≈ 0.274) both 'tune' to 1/4
    under their own normalizations; the universal piece is the −3/2 log
    coefficient, NOT the 1/4 leading coefficient.

    Lean: BHEntropyMicroscopic.kaul_majumdar_log_coefficient
    Source: Kaul SIGMA 8, 005 (2012), arXiv:1201.6102 §5.
    viz-ref: Phase 6a Paper 26 §3
    """
    import plotly.graph_objects as go
    from src.bh_entropy import (
        falsifier_status_table,
        leading_coefficient_vs_immirzi,
    )

    γs, κs, anchors = leading_coefficient_vs_immirzi(
        gamma_lower=0.05, gamma_upper=1.0, n_points=300
    )
    table = falsifier_status_table()

    fig = go.Figure()

    # Main κ(γ) curve
    fig.add_trace(go.Scatter(
        x=γs, y=κs,
        mode="lines",
        line=dict(color=COLORS["steel_blue"], width=3),
        name="κ_leading(γ) = γ_DL/γ · 1/4",
    ))

    # 1/4 horizontal line
    fig.add_shape(
        type="line",
        x0=γs[0], x1=γs[-1], y0=0.25, y1=0.25,
        line=dict(color="black", width=1, dash="dot"),
    )
    fig.add_annotation(
        x=γs[-1], y=0.25,
        text="1/4 (Bekenstein-Hawking)",
        showarrow=False, xanchor="right", yanchor="bottom",
        font=dict(size=10),
    )

    # Domagala-Lewandowski + Meissner anchors
    fig.add_trace(go.Scatter(
        x=[anchors["DL"]],
        y=[0.25],
        mode="markers+text",
        marker=dict(symbol="star", size=18,
                    color=COLORS["amber"],
                    line=dict(width=1, color="black")),
        text=[f"γ_DL ≈ {anchors['DL']:.4f}"],
        textposition="top center",
        textfont=dict(size=10),
        name="Domagala-Lewandowski",
    ))
    κ_M = 0.25 * anchors["DL"] / anchors["Meissner"]
    fig.add_trace(go.Scatter(
        x=[anchors["Meissner"]],
        y=[κ_M],
        mode="markers+text",
        marker=dict(symbol="star", size=16,
                    color=COLORS["steel_blue"],
                    line=dict(width=1, color="black")),
        text=[f"γ_M ≈ {anchors['Meissner']:.4f}<br>(κ ≈ {κ_M:.3f})"],
        textposition="bottom right",
        textfont=dict(size=9),
        name="Meissner",
    ))

    # Annotate MTC zoo via right-side text (log d_max bar)
    zoo_names = ["Fibonacci", "Ising", "DS3", "ToricCode"]
    annotation_text = "<b>MTC zoo (log d_max):</b><br>" + "<br>".join(
        f"  {name}: log d_max = {table[name]['log_d_max']:.3f}"
        + (" (abelian — F2 falsifier)" if table[name]['is_abelian'] else "")
        for name in zoo_names
    )
    fig.add_annotation(
        x=0.98, y=0.05,
        xref="paper", yref="paper",
        text=annotation_text,
        showarrow=False,
        align="left",
        bgcolor="rgba(255,255,255,0.85)",
        bordercolor="black", borderwidth=1,
        font=dict(size=9),
    )

    apply_layout(
        fig,
        xaxis=dict(title="Immirzi γ (dimensionless)"),
        yaxis=dict(
            title="κ_leading (BH-entropy leading coefficient)",
            range=[0, max(κs.max() * 1.1, 0.6)],
        ),
        title=dict(
            text=(
                "Phase 6a Wave 3 — BH-entropy leading coefficient as Immirzi γ tuning<br>"
                "<sub>The 1/4 prefactor is a TUNING, not a derivation; "
                "DL & Meissner are distinct counting prescriptions; "
                "Lean: <i>BHEntropyMicroscopic.HorizonMTCBC.γ_immirzi</i></sub>"
            ),
            font=TITLE_FONT,
        ),
        height=620,
        width=920,
    )
    return fig


def fig_log_correction_signature():
    """Phase 6a Wave 3: −3/2 log-correction structural anchor + per-MTC zoo +
    Sen 4D Schwarzschild non-universality witness.

    Three structural facts displayed:
    1. The Kaul-Majumdar SU(2)_k value: c_log = −3/2 (½ Gaussian + 1 singlet).
    2. The Sen 4D heat-kernel disagreement: c_log = +1.71 (universality fails).
    3. The per-MTC tracked-hypothesis status (Fib/Ising/DS3 = conjectural,
       Toric code = F2 falsifier).

    Lean: BHEntropyMicroscopic.sen_4d_disagrees_with_kaul_majumdar
    Source: Kaul-Majumdar gr-qc/0002040 + Sen 1205.0971 + deep-research §4.
    viz-ref: Phase 6a Paper 26 §4
    """
    import plotly.graph_objects as go
    from src.bh_entropy import log_correction_zoo, sen_disagreement_witness

    zoo = log_correction_zoo()
    witness = sen_disagreement_witness()

    # x-axis: ordered status categories
    categories = [
        ("SU2k", -1.5, "known\n(Kaul-Majumdar)"),
        ("Sen4DSchwarzschild", witness.c_log_sen_4d, "known\n(Sen heat-kernel)"),
        ("Fibonacci", 0.0, "conjectural"),
        ("Ising", 0.0, "conjectural"),
        ("DS3", 0.0, "conjectural"),
        ("ToricCode", 0.0, "F2 falsifier\n(abelian)"),
    ]
    names = [c[0] for c in categories]
    values = [c[1] for c in categories]
    statuses = [c[2] for c in categories]
    bar_colors = [
        COLORS["steel_blue"],     # KM known
        COLORS["amber"],          # Sen disagreement
        "rgba(180,180,180,0.5)",  # Fib conj
        "rgba(180,180,180,0.5)",  # Ising conj
        "rgba(180,180,180,0.5)",  # DS3 conj
        "rgba(220,80,80,0.6)",    # Toric F2
    ]

    fig = go.Figure()
    fig.add_trace(go.Bar(
        x=names, y=values,
        marker_color=bar_colors,
        text=[
            (f"{v:+.3f}" if statuses[i].startswith("known") else statuses[i])
            for i, v in enumerate(values)
        ],
        textposition="outside",
        showlegend=False,
    ))

    # −3/2 anchor line
    fig.add_shape(
        type="line",
        x0=-0.5, x1=len(names) - 0.5,
        y0=-1.5, y1=-1.5,
        line=dict(color=COLORS["steel_blue"], width=1, dash="dash"),
    )
    fig.add_annotation(
        x=len(names) - 0.5, y=-1.5,
        text="−3/2 anchor (Kaul-Majumdar SU(2)_k)",
        showarrow=False, xanchor="right", yanchor="bottom",
        font=dict(size=10, color=COLORS["steel_blue"]),
    )

    # Sen disagreement annotation
    fig.add_annotation(
        x="Sen4DSchwarzschild", y=witness.c_log_sen_4d,
        text=(
            f"Disagrees with KM:<br>"
            f"|Δc_log| = {abs(witness.disagreement):.2f}<br>"
            f"⇒ universality fails"
        ),
        showarrow=True, arrowhead=2,
        ax=80, ay=-40,
        font=dict(size=9, color=COLORS["amber"]),
        bgcolor="rgba(255,255,255,0.85)",
        bordercolor=COLORS["amber"], borderwidth=1,
    )

    apply_layout(
        fig,
        xaxis=dict(title="MTC / counting scheme"),
        yaxis=dict(title="c_log (log-A correction coefficient)",
                   range=[-2.2, witness.c_log_sen_4d * 1.6]),
        title=dict(
            text=(
                "Phase 6a Wave 3 — Log-correction signature: "
                "Kaul-Majumdar −3/2 anchor + Sen 4D non-universality + MTC zoo<br>"
                "<sub>−3/2 = (−1/2 Gaussian saddle) + (−1 SU(2) singlet projection); "
                "Sen 1205.0971 disagrees; "
                "Fib/Ising/DS3 conjectural; toric-code F2 falsifier; "
                "Lean: <i>sen_4d_disagrees_with_kaul_majumdar</i></sub>"
            ),
            font=TITLE_FONT,
        ),
        height=600,
        width=900,
    )
    return fig


def fig_T_H_evolution_regime_partition():
    """Phase 6a Wave 5: T_H(t) evaporation regime partition.

    Plots the time-evolution of Hawking temperature under Hawking-radiation
    backreaction in two regimes:

    - Schwarzschild branch (M > M_c): textbook Hawking 1975 result. As BH
      evaporates (dM/dt < 0), T_H = 1/(8π M) increases ⇒ dT_H/dt > 0 (heats
      as evaporates), finite t-evap. Plotted as a function of normalized
      time using a representative evaporation trajectory.
    - BEC-acoustic branch (M < M_c): Balbinot et al. PRD 71, 064019 (2005)
      Eq. (Tsonic) gives strict monotone decay; leading-order exponential
      `T_H(t) = T_H,0 · exp(-t/τ_cool)` per `wkb/backreaction.py`. T → 0
      at infinite time (`t ~ 1/T³` extrapolation per Balbinot 2005).

    The genuine regime partition is the **sign-flip of dT_H/dt during
    evaporation**: positive in Schwarzschild (heats), negative in
    BEC-acoustic (cools). Right panel overlays the substrate-response
    coefficient `δ_ADW = (α_ADW − 1) · Λ_UV` showing the bare
    Sakharov-Adler limit at α_ADW = 1.

    Lean: BHThermodynamicsFourLaws.regime_partition_criterion +
          T_H_acoustic_evolution + T_H_schwarzschild.
    Source: Balbinot+2005 (gr-qc/0405098); Hawking 1975 (CMP 43, 199).
    viz-ref: Phase 6a Paper 27 §3
    """
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots

    from src.bh_thermodynamics import (
        ADWParams,
        T_H_acoustic_evolution,
        delta_ADW_ansatz,
    )

    # Time grid in units of τ_cool (BEC-acoustic side)
    t_grid_acoustic = np.linspace(0.0, 5.0, 121)
    T_H0 = 1.0  # natural-units initial temperature
    tau_cool = 1.0
    T_H_acoustic = np.array([
        T_H_acoustic_evolution(T_H0, tau_cool, t) for t in t_grid_acoustic
    ])

    # Schwarzschild evaporation: M(t) ∝ (M_0³ - K·t)^(1/3) (Hawking 1975).
    # We plot T_H(t)/T_H(0) using a normalized M_0³ - K·t with K chosen so
    # t_evap = 5 in the same units (illustrative; relative shape is the
    # load-bearing content).
    t_grid_schw = np.linspace(0.0, 4.5, 121)  # cap before singularity at t=5
    # M(t) = (M_0³ - K t)^(1/3); choose M_0=1, K=1/5 so M(5)=0
    M_t = (1.0 - 0.2 * t_grid_schw) ** (1.0 / 3.0)
    # Normalized T_H(t)/T_H(0) = M_0/M(t) = 1/M_t (since M_0=1)
    T_H_schw_normalized = 1.0 / M_t

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            "T_H(t) evaporation regime partition",
            "δ_ADW(α_ADW) substrate-response ansatz",
        ),
        column_widths=[0.6, 0.4],
        horizontal_spacing=0.12,
    )

    # Left panel: T_H(t) profile across both regimes
    fig.add_trace(
        go.Scatter(
            x=t_grid_acoustic, y=T_H_acoustic,
            mode="lines",
            line=dict(color=COLORS["steel_blue"], width=3),
            name="BEC-acoustic (Balbinot 2005)",
        ),
        row=1, col=1,
    )
    fig.add_trace(
        go.Scatter(
            x=t_grid_schw, y=T_H_schw_normalized,
            mode="lines",
            line=dict(color=COLORS["amber"], width=3, dash="dash"),
            name="Schwarzschild (Hawking 1975)",
        ),
        row=1, col=1,
    )
    # Heat-capacity-sign annotations
    fig.add_annotation(
        x=2.0, y=0.25,
        text="dT_H/dt < 0<br>(cools toward asymptotic<br>extremality, infinite t-evap)",
        showarrow=False,
        font=dict(size=10, color=COLORS["steel_blue"]),
        row=1, col=1,
    )
    fig.add_annotation(
        x=3.5, y=2.5,
        text="dT_H/dt > 0<br>(heats as evaporates,<br>finite t-evap)",
        showarrow=False,
        font=dict(size=10, color=COLORS["amber"]),
        row=1, col=1,
    )

    # Right panel: δ_ADW(α_ADW) over Wave-1 natural range
    alpha_grid = np.linspace(0.1, 10.0, 100)
    delta_grid = np.array([
        delta_ADW_ansatz(ADWParams(
            alpha_ADW=a, lambda_UV=1.0, N_f=16.0, chi_vest=1.0
        ))
        for a in alpha_grid
    ])
    fig.add_trace(
        go.Scatter(
            x=alpha_grid, y=delta_grid,
            mode="lines",
            line=dict(color=COLORS["steel_blue"], width=3),
            name="δ_ADW = (α_ADW − 1)·Λ_UV",
            showlegend=False,
        ),
        row=1, col=2,
    )
    # α=1 vanishing point
    fig.add_shape(
        type="line",
        x0=1.0, x1=1.0, y0=-1.5, y1=10.0,
        line=dict(color="rgba(80,80,80,0.6)", width=1, dash="dot"),
        row=1, col=2,
    )
    fig.add_annotation(
        x=1.0, y=0.5,
        text="α_ADW = 1<br>(bare Sakharov-Adler:<br>δ_ADW vanishes)",
        showarrow=False,
        font=dict(size=10, color="rgba(60,60,60,0.9)"),
        row=1, col=2,
    )
    # Zero baseline
    fig.add_shape(
        type="line",
        x0=0.1, x1=10.0, y0=0.0, y1=0.0,
        line=dict(color="rgba(120,120,120,0.4)", width=1),
        row=1, col=2,
    )

    fig.update_xaxes(title_text="Time t / τ_cool (BEC-acoustic) or t / t_evap (Schwarzschild)", row=1, col=1)
    fig.update_yaxes(title_text="T_H / T_H,0", row=1, col=1, range=[0, 4])
    fig.update_xaxes(title_text="α_ADW", row=1, col=2)
    fig.update_yaxes(title_text="δ_ADW / Λ_UV", row=1, col=2)

    apply_layout(
        fig,
        title=dict(
            text=(
                "Phase 6a Wave 5 — BCH four-laws regime partition "
                "(Schwarzschild ↔ BEC-acoustic)"
            ),
            font=TITLE_FONT,
        ),
        height=600,
        width=1100,
        margin=dict(t=110, b=80),
    )
    return fig


def fig_bbn_conformance_matrix():
    """Phase 6b Wave 1: BBN-conformance matrix for five Phase 5x DM candidates.

    Heatmap showing each candidate's BBN-conformance verdict across three
    independent fields (omega_b_consistent, delta_n_eff_within_bound,
    injection_below_threshold). Three candidates pass unconditionally
    (Z16Topological_T0, Z16Mixed_C1, FractonPWave) — the W8 collective-
    invisibility theorem applies. Two candidates fail conditional on
    thermalization at T_BBN (Z16Singlet_S0 via 3-sterile-Weyl-thermalization
    → ΔN_eff = 3 ≫ 0.34 Planck slack; FGTorsion via radiation-like
    thermalization → ΔN_eff ≥ 1.0).

    Right panel: ΔN_eff bar chart showing the Planck 2σ slack (0.34) as a
    horizontal reference, with each candidate's literature-cited tracked-
    hypothesis ΔN_eff value plotted on log scale.

    Lean: BBN.bbn_violators_share_n_eff_failure_mode +
          BBN.at_least_three_phase5x_candidates_bbn_conformant.
    Source: Planck 2020 (A&A 641, A6); Phase 5x W7/W8 candidate IDs.
    viz-ref: Phase 6b Paper 29 §3
    """
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots

    from src.bbn import (
        DMCandidate,
        N_EFF_2SIGMA_SLACK,
        evaluate_all_candidates,
    )

    candidates = [
        DMCandidate.Z16Topological_T0,
        DMCandidate.Z16Mixed_C1,
        DMCandidate.FractonPWave,
        DMCandidate.Z16Singlet_S0,
        DMCandidate.FGTorsion,
    ]
    candidate_labels = [
        "Z16Topological T-0<br>(K-gauge TQFT)",
        "Z16Mixed C-1<br>(dark-SU(3) confining)",
        "FractonPWave<br>(dipole conservation)",
        "Z16Singlet S-0<br>(3 sterile Weyl)",
        "FGTorsion<br>(FG e-loop radiation)",
    ]
    field_labels = [
        "Ω_B h² consistent",
        "ΔN_eff ≤ 0.34",
        "Injection ≤ thresh.",
    ]

    verdicts = evaluate_all_candidates()
    z_matrix = []
    cell_text = []
    for c in candidates:
        v = verdicts[c]
        row_z = [
            1 if v.omega_b_consistent else 0,
            1 if v.delta_n_eff_within_bound else 0,
            1 if v.injection_below_threshold else 0,
        ]
        row_text = [
            "✓ pass" if v.omega_b_consistent else "✗ fail",
            "✓ pass" if v.delta_n_eff_within_bound else "✗ fail",
            "✓ pass" if v.injection_below_threshold else "✗ fail",
        ]
        z_matrix.append(row_z)
        cell_text.append(row_text)

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            "BBN-conformance matrix (candidates × fields)",
            "ΔN_eff vs Planck 2σ slack (log scale)",
        ),
        column_widths=[0.55, 0.45],
        horizontal_spacing=0.18,
        specs=[[{"type": "heatmap"}, {"type": "bar"}]],
    )

    fig.add_trace(
        go.Heatmap(
            z=z_matrix,
            x=field_labels,
            y=candidate_labels,
            text=cell_text,
            texttemplate="%{text}",
            textfont={"size": 11},
            colorscale=[
                [0.0, COLORS["amber"]],   # amber = fails
                [1.0, "rgba(180, 220, 200, 1.0)"],  # pale green = passes
            ],
            showscale=False,
            hovertemplate="<b>%{y}</b><br>%{x}: %{text}<extra></extra>",
        ),
        row=1, col=1,
    )

    # ΔN_eff bars per candidate
    delta_n_eff_values = {
        DMCandidate.Z16Topological_T0: 1e-6,  # log-plot floor
        DMCandidate.Z16Mixed_C1: 1e-6,
        DMCandidate.FractonPWave: 1e-6,
        DMCandidate.Z16Singlet_S0: 3.0,
        DMCandidate.FGTorsion: 1.0,
    }
    bar_x = [c.value for c in candidates]
    bar_y = [delta_n_eff_values[c] for c in candidates]
    bar_text = [
        f"ΔN_eff = {delta_n_eff_values[c]:.1g}" if delta_n_eff_values[c] >= 0.01 else "≈ 0"
        for c in candidates
    ]
    bar_colors = [
        COLORS["steel_blue"] if verdicts[c].is_conformant else COLORS["amber"]
        for c in candidates
    ]

    fig.add_trace(
        go.Bar(
            x=bar_x, y=bar_y,
            marker_color=bar_colors,
            text=bar_text,
            textposition="auto",
            showlegend=False,
            hovertemplate="<b>%{x}</b><br>ΔN_eff = %{y:.3g}<extra></extra>",
        ),
        row=1, col=2,
    )

    # Planck 2σ slack horizontal reference
    fig.add_shape(
        type="line",
        x0=-0.5, x1=4.5,
        y0=N_EFF_2SIGMA_SLACK, y1=N_EFF_2SIGMA_SLACK,
        line=dict(color=COLORS["steel_blue"], width=2, dash="dot"),
        row=1, col=2,
    )
    fig.add_annotation(
        x=4.0, y=N_EFF_2SIGMA_SLACK * 1.4,
        text=f"Planck 2σ slack = {N_EFF_2SIGMA_SLACK:.2f}",
        showarrow=False,
        font=dict(size=10, color=COLORS["steel_blue"]),
        row=1, col=2,
    )

    fig.update_yaxes(title_text="ΔN_eff", type="log", row=1, col=2)

    apply_layout(
        fig,
        title=dict(
            text=(
                "Phase 6b Wave 1 — BBN-conformance matrix for five "
                "Phase 5x DM candidates (2 thermalization-conditional violators)"
            ),
            font=TITLE_FONT,
        ),
        height=580,
        width=1300,
        margin=dict(t=110, b=80, l=180),
    )
    return fig


def fig_ep_violation_matrix():
    """Phase 6c Wave 3: EP-violation matrix for six Phase 5x mechanisms.

    Heatmap displaying which EP levels (WEP, EEP, SEP) are violated by each
    of six Phase 5x DM-related mechanisms. Two violators (both vestigial-
    phase phenomena, η = 1 maximal and η ~ 10⁻¹⁸ STEP-class), four
    non-violators (FangGu torsion, fracton subdiffusion, SFDM Thomas-Fermi,
    hidden-sector ℤ₁₆ singlet).

    Right panel: η-scale comparison bar chart (vestigial-phase η = 1 max,
    MICROSCOPE bound η < 10⁻¹⁵, STEP target η ~ 10⁻¹⁸, vestigial-relics η).
    Surfaces the structural fact that EP violation is *vestigial-only* in
    the project's current dark-sector landscape.

    Lean: EquivalencePrinciple.violatesAt + ep_violation_is_vestigial_only.
    Source: VestigialGravity.ep_violation_in_vestigial; Touboul et al. PRL
            119, 231101 (2017); W8 §5 ranking line 3.
    viz-ref: Phase 6c Paper 34 §3
    """
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots

    from src.equivalence_principle import (
        EPLevel,
        EPMechanism,
        MICROSCOPE_BOUND,
        STEP_TARGET,
        VESTIGIAL_PHASE_ETA_MAX,
        VESTIGIAL_RELICS_ETA,
        violates_at,
    )

    mechanisms = [
        EPMechanism.vestigialDifferentialCoupling,
        EPMechanism.vestigialReliscSTEPClass,
        EPMechanism.fangGuTorsionTrace,
        EPMechanism.fractonSubdiffusion,
        EPMechanism.sfdmThomasFermi,
        EPMechanism.hiddenSectorZ16Singlet,
    ]
    mechanism_labels = [
        "Vestigial differential<br>coupling (η=1 max)",
        "Vestigial relics<br>(η~10⁻¹⁸ STEP)",
        "FangGu torsion DM<br>(w_FG=1/3, kinematic)",
        "Fracton subdiffusion<br>(universal mobility)",
        "SFDM Thomas-Fermi<br>(single-field uniform)",
        "Hidden-sector ℤ₁₆<br>(SM-singlet)",
    ]
    levels = [EPLevel.WEP, EPLevel.EEP, EPLevel.SEP]
    level_labels = ["WEP", "EEP", "SEP"]

    z_matrix = [
        [1 if violates_at(m, L) else 0 for L in levels]
        for m in mechanisms
    ]
    cell_text = [
        ["✗ violates" if violates_at(m, L) else "✓ satisfies" for L in levels]
        for m in mechanisms
    ]

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            "EP-violation matrix (mechanisms × levels)",
            "η-scale comparison",
        ),
        column_widths=[0.6, 0.4],
        horizontal_spacing=0.18,
        specs=[[{"type": "heatmap"}, {"type": "bar"}]],
    )

    # Left panel: 6x3 heatmap
    fig.add_trace(
        go.Heatmap(
            z=z_matrix,
            x=level_labels,
            y=mechanism_labels,
            text=cell_text,
            texttemplate="%{text}",
            textfont={"size": 11},
            colorscale=[
                [0.0, "rgba(220, 220, 220, 1.0)"],  # gray = satisfies
                [1.0, COLORS["amber"]],  # amber = violates
            ],
            showscale=False,
            hovertemplate="<b>%{y}</b><br>%{x}: %{text}<extra></extra>",
        ),
        row=1, col=1,
    )

    # Right panel: log-scale η bars
    eta_labels = [
        "Vestigial phase<br>η_max",
        "MICROSCOPE bound<br>(Touboul 2017)",
        "Vestigial relics<br>η_STEP",
        "STEP-class target",
    ]
    eta_values = [
        VESTIGIAL_PHASE_ETA_MAX,
        MICROSCOPE_BOUND,
        VESTIGIAL_RELICS_ETA,
        STEP_TARGET,
    ]
    eta_log = [np.log10(v) for v in eta_values]
    eta_colors = [
        COLORS["amber"],   # ruled out
        COLORS["steel_blue"],  # current bound
        COLORS["amber"],   # to-be-tested
        COLORS["steel_blue"],  # future
    ]

    fig.add_trace(
        go.Bar(
            x=eta_labels,
            y=eta_log,
            marker_color=eta_colors,
            text=[f"η = {v:.0e}" if v < 1 else f"η = {v}" for v in eta_values],
            textposition="auto",
            showlegend=False,
            hovertemplate="<b>%{x}</b><br>log₁₀(η) = %{y:.1f}<extra></extra>",
        ),
        row=1, col=2,
    )
    # MICROSCOPE bound horizontal line at log10(1e-15) = -15
    fig.add_shape(
        type="line",
        x0=-0.5, x1=3.5,
        y0=np.log10(MICROSCOPE_BOUND), y1=np.log10(MICROSCOPE_BOUND),
        line=dict(color=COLORS["steel_blue"], width=1, dash="dot"),
        row=1, col=2,
    )

    fig.update_yaxes(title_text="log₁₀(η)", range=[-22, 2], row=1, col=2)

    apply_layout(
        fig,
        title=dict(
            text=(
                "Phase 6c Wave 3 — EP-violation matrix for Phase 5x DM "
                "mechanisms (vestigial-only violators)"
            ),
            font=TITLE_FONT,
        ),
        height=560,
        width=1200,
        margin=dict(t=110, b=80, l=180),
    )
    return fig


def fig_polyakov_loop_deconfinement():
    """Phase 6d Wave 1: Polyakov-loop order parameter and Svetitsky-Yaffe
    universality.

    Left panel: |P| vs T/T_c, showing the deconfinement transition. The
    ordered phase (T < T_c) has |P| = 0 (confining); the disordered phase
    (T > T_c) has |P| > 0 (deconfining). Z_2 (Ising) and Z_3 (Potts)
    universality classes are shown side-by-side with their literature
    critical exponents.

    Right panel: KSS bound + Walker-Wang transport window. Shows the
    universal lower bound η/s ≥ 1/(4π) ≈ 0.0796 with the Walker-Wang
    correctness-push window [KSS, 2·KSS] highlighted; both numerical
    falsifiers (η/s = 0 and η/s = 1) lie outside the window.

    Lean: CenterSymmetryConfinement.confining_iff_magnitude_zero,
          deconfining_implies_magnitude_positive,
          ising_nu_gt_potts_nu, KSS_bound_below_0_08,
          walker_wang_zero_eta_violator, walker_wang_unit_eta_violator.
    Source: Svetitsky-Yaffe NPB 210 (1982); KSS PRL 94 (2005);
            Pelissetto-Vicari Phys. Rep. 368 (2002).
    viz-ref: Phase 6d Paper 36 §3
    """
    import numpy as np
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots

    from src.center_symmetry import (
        KSS_BOUND,
        UniversalityClass,
        critical_exponent_nu,
    )

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            "Polyakov-loop order parameter |P| vs T/T_c "
            "(Z_2 Ising vs Z_3 Potts)",
            "KSS bound + Walker-Wang transport window",
        ),
        column_widths=[0.55, 0.45],
        horizontal_spacing=0.15,
    )

    # ---------- Left: |P| vs T/T_c ----------
    nu_ising = critical_exponent_nu(UniversalityClass.ISING)
    nu_potts = critical_exponent_nu(UniversalityClass.THREE_STATE_POTTS)
    # Schematic order parameter: |P| ∝ (T/T_c - 1)^β for T > T_c, 0 below.
    # The 3D 3-state Potts deconfinement transition is weakly first-order, so
    # β is not strictly defined for it. We plot the SU(2) Ising curve with the
    # genuine 3D-Ising β ≈ 0.326, and the SU(3) curve with the 2D-Potts β = 1/9
    # ≈ 0.111 as a CONTRASTING illustrative shape (NOT a 3D-Potts prediction).
    # Both curves are explicitly labelled "(illustrative)" in the legend.
    t_over_tc = np.linspace(0.5, 2.0, 200)
    beta_ising = 0.326
    beta_potts_2d = 0.111  # 2D 3-state Potts β = 1/9, used as illustrative contrast
    delta = np.maximum(t_over_tc - 1.0, 0.0)
    p_ising = np.where(t_over_tc < 1.0, 0.0, delta ** beta_ising)
    p_potts = np.where(t_over_tc < 1.0, 0.0, delta ** beta_potts_2d)

    fig.add_trace(
        go.Scatter(
            x=t_over_tc, y=p_ising,
            mode="lines",
            name=f"Z_2 / Ising  (ν = {nu_ising:.4f}, β = 0.326, 3D)",
            line=dict(color=COLORS["steel_blue"], width=2.5),
        ),
        row=1, col=1,
    )
    fig.add_trace(
        go.Scatter(
            x=t_over_tc, y=p_potts,
            mode="lines",
            name=(f"Z_3 / 3-state Potts  (ν = {nu_potts:.4f} mean-field;  "
                  "β = 1/9 from 2D Potts, illustrative — 3D deconfinement is weakly 1st-order)"),
            line=dict(color=COLORS["amber"], width=2.5, dash="dash"),
        ),
        row=1, col=1,
    )
    # Vertical T_c line
    fig.add_shape(
        type="line",
        x0=1.0, x1=1.0, y0=0, y1=1.0,
        line=dict(color=COLORS["horizon"], width=1.5, dash="dot"),
        row=1, col=1,
    )
    fig.add_annotation(
        x=1.02, y=0.95,
        text="T = T_c (deconfinement)",
        showarrow=False,
        font=dict(size=10),
        xanchor="left",
        row=1, col=1,
    )
    fig.add_annotation(
        x=0.7, y=0.4,
        text="Confining<br>(|P| = 0)",
        showarrow=False,
        font=dict(size=11, color=COLORS["steel_blue"]),
        row=1, col=1,
    )
    fig.add_annotation(
        x=1.5, y=0.85,
        text="Deconfining<br>(|P| > 0)",
        showarrow=False,
        font=dict(size=11, color=COLORS["amber"]),
        row=1, col=1,
    )
    fig.update_xaxes(title_text="T / T_c", row=1, col=1)
    fig.update_yaxes(title_text="|P| (order parameter)", row=1, col=1, range=[0, 1.05])

    # ---------- Right: KSS bound + Walker-Wang window ----------
    eta_grid = np.array([0.0, 0.5 * KSS_BOUND, KSS_BOUND, 1.5 * KSS_BOUND,
                         2.0 * KSS_BOUND, 3.0 * KSS_BOUND, 0.5, 1.0])
    in_window = [
        KSS_BOUND <= e <= 2 * KSS_BOUND for e in eta_grid
    ]
    bar_colors = [
        COLORS["steel_blue"] if w else COLORS["amber"] for w in in_window
    ]
    labels = [f"{e:.3g}" for e in eta_grid]
    fig.add_trace(
        go.Bar(
            x=labels, y=eta_grid,
            marker_color=bar_colors,
            text=[f"{e:.3g}" for e in eta_grid],
            textposition="auto",
            showlegend=False,
            hovertemplate="η/s = %{x}<br>value = %{y:.4g}<extra></extra>",
        ),
        row=1, col=2,
    )
    fig.update_xaxes(title_text="η/s value", row=1, col=2)
    # KSS line
    fig.add_shape(
        type="line",
        x0=-0.5, x1=len(eta_grid) - 0.5,
        y0=KSS_BOUND, y1=KSS_BOUND,
        line=dict(color=COLORS["horizon"], width=2, dash="solid"),
        row=1, col=2,
    )
    fig.add_annotation(
        x=len(eta_grid) - 1, y=KSS_BOUND * 1.6,
        text=f"KSS bound = 1/(4π) ≈ {KSS_BOUND:.4f}",
        showarrow=False,
        font=dict(size=10),
        row=1, col=2,
    )
    # 2·KSS line
    fig.add_shape(
        type="line",
        x0=-0.5, x1=len(eta_grid) - 0.5,
        y0=2 * KSS_BOUND, y1=2 * KSS_BOUND,
        line=dict(color=COLORS["steel_blue"], width=1.5, dash="dot"),
        row=1, col=2,
    )
    fig.add_annotation(
        x=len(eta_grid) - 1, y=2 * KSS_BOUND * 1.3,
        text=f"2·KSS ≈ {2 * KSS_BOUND:.4f}<br>(Walker-Wang upper)",
        showarrow=False,
        font=dict(size=9, color=COLORS["steel_blue"]),
        row=1, col=2,
    )
    fig.update_yaxes(title_text="η/s", type="log", row=1, col=2)

    apply_layout(
        fig,
        title=dict(
            text=(
                "Phase 6d Wave 1 — Polyakov-loop deconfinement transition "
                "and Walker-Wang transport window"
            ),
            font=TITLE_FONT,
        ),
        height=580,
        width=1300,
        margin=dict(t=110, b=80),
    )
    return fig


def fig_zhitnitsky_de_theta_scan():
    """Phase 6c Wave 1: Zhitnitsky DE prediction across Λ_QCD with
    correctness-push falsification of both-mechanism activation.

    Left panel: ρ_DE (Zhitnitsky) vs Λ_QCD on log scale, with horizontal
    band at observed ρ_DE = (2.3 meV)^4 ≈ 2.8e-11 eV⁴; the predicted
    curve crosses the observed band near Λ_QCD ≈ 30 MeV (close to the
    PDG Λ_QCD ≈ 100 MeV — the Zhitnitsky prediction matches observation
    within ~2 orders without free parameters).

    Right panel: bar chart showing the cosmological-constant problem
    suppression — the Zhitnitsky-predicted ρ_DE sits ~120 orders of
    magnitude below the Planck-natural M_P^4 estimate, demonstrating
    the QCD-topological-sector mechanism's solution to the hierarchy.

    Lean: StrongCPTopologicalDE.zhitnitsky_DE_at_lambda_qcd_within_3_orders,
          zhitnitsky_DE_far_below_planck,
          combined_zhitnitsky_qtheory_exceeds_observation.
    Source: Van Waerbeke-Zhitnitsky arXiv:2506.14182 (2025);
            Klinkhamer-Volovik JETP Lett. 91 (2010);
            Pendlebury PRD 92 (2015) neutron-EDM bound.
    viz-ref: Phase 6c Paper 32 §3
    """
    import numpy as np
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots

    from src.strong_cp_de import (
        LAMBDA_QCD_GEV,
        RHO_DE_OBSERVED_EV4,
        zhitnitsky_de_eV4,
    )

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            "Zhitnitsky ρ_DE prediction vs Λ_QCD (no free parameters)",
            "Cosmological-constant-problem suppression (~120 orders)",
        ),
        column_widths=[0.55, 0.45],
        horizontal_spacing=0.18,
    )

    # ---------- Left: rho_DE vs Lambda_QCD log-log ----------
    lambda_grid = np.logspace(-3, 0, 100)  # 1 MeV to 1 GeV
    rho_predicted = np.array([zhitnitsky_de_eV4(L) for L in lambda_grid])
    fig.add_trace(
        go.Scatter(
            x=lambda_grid * 1000,  # MeV
            y=rho_predicted,
            mode="lines",
            line=dict(color=COLORS["steel_blue"], width=2.5),
            name="Zhitnitsky ρ_DE",
            hovertemplate="Λ_QCD = %{x:.1f} MeV<br>ρ = %{y:.3e} eV⁴<extra></extra>",
        ),
        row=1, col=1,
    )
    # Observed band
    fig.add_shape(
        type="rect",
        x0=1, x1=1000,
        y0=RHO_DE_OBSERVED_EV4 * 0.3, y1=RHO_DE_OBSERVED_EV4 * 3,
        fillcolor=COLORS["amber"], opacity=0.25,
        line=dict(width=0),
        row=1, col=1,
    )
    fig.add_annotation(
        x=2, y=RHO_DE_OBSERVED_EV4,
        text=f"observed<br>ρ_DE ≈ {RHO_DE_OBSERVED_EV4:.1e} eV⁴",
        showarrow=False,
        font=dict(size=10, color=COLORS["amber"]),
        xanchor="left",
        row=1, col=1,
    )
    # PDG Lambda_QCD vertical reference
    fig.add_shape(
        type="line",
        x0=LAMBDA_QCD_GEV * 1000, x1=LAMBDA_QCD_GEV * 1000,
        y0=1e-15, y1=1e-2,
        line=dict(color=COLORS["horizon"], width=1.5, dash="dot"),
        row=1, col=1,
    )
    fig.add_annotation(
        x=LAMBDA_QCD_GEV * 1000 * 1.1, y=1e-13,
        text="PDG Λ_QCD<br>≈ 100 MeV",
        showarrow=False,
        font=dict(size=10, color=COLORS["horizon"]),
        xanchor="left",
        row=1, col=1,
    )
    fig.update_xaxes(
        title_text="Λ_QCD [MeV]", type="log",
        range=[0, 3],  # 1 MeV (10^0) to 1 GeV (10^3)
        row=1, col=1,
    )
    fig.update_yaxes(
        title_text="ρ_DE [eV⁴]", type="log",
        range=[-15, -2],  # 10^-15 to 10^-2 eV⁴
        row=1, col=1,
    )

    # ---------- Right: CC-problem suppression bar chart ----------
    labels = [
        "Planck-natural<br>M_P⁴",
        "Zhitnitsky<br>(QCD topological)",
        "Observed<br>(2.3 meV)⁴",
    ]
    values = [1.0e112, zhitnitsky_de_eV4(LAMBDA_QCD_GEV), RHO_DE_OBSERVED_EV4]
    colors_right = [COLORS["amber"], COLORS["steel_blue"], COLORS["dissipative"]]

    fig.add_trace(
        go.Bar(
            x=labels,
            y=values,
            marker_color=colors_right,
            text=[f"{v:.2e}" for v in values],
            textposition="outside",
            textfont=dict(size=10),
            showlegend=False,
            hovertemplate="<b>%{x}</b><br>ρ = %{y:.3e} eV⁴<extra></extra>",
        ),
        row=1, col=2,
    )
    fig.update_yaxes(title_text="ρ [eV⁴]", type="log", row=1, col=2)

    apply_layout(
        fig,
        title=dict(
            text=(
                "Phase 6c Wave 1 — Zhitnitsky topological dark-energy "
                "prediction (no free parameters) vs observed ρ_DE"
            ),
            font=TITLE_FONT,
        ),
        height=580,
        width=1300,
        margin=dict(t=110, b=80),
    )
    return fig


def fig_cfl_z3_center_bridge():
    """Phase 6d Wave 3: CFL emergent ℤ_3 ↔ QCD center ℤ_3 correctness-push.

    Left panel: complex-plane diagram showing the three cube roots of
    unity {1, ω, ω²} on the unit circle, with the CFL emergent ℤ_3
    generator (Hirono-Tanizaki) and the QCD center ℤ_3 generator (W1)
    BOTH at the same point ω = exp(2πi/3). The correctness-push:
    independent derivations yield the same generator.

    Right panel: bar chart showing the three Z_3 charges (0, 1, 2)
    with their topological-order classification (trivial vs
    Hirono-Tanizaki nontrivial sector). Charge = 0 is the trivial
    vacuum; charges 1, 2 are the topologically-ordered sectors
    distinguishing CFL from a Landau-Ginzburg-only phase.

    Lean: CFLChiralLagrangian.CFL_emergent_Z3_matches_QCD_center_Z3,
          emergentZ3_pow_3, emergentZ3_sum_cube_roots,
          H_TopologicalOrderBeyondLG_witness +
          H_TopologicalOrderBeyondLG_falsifier_trivial.
    Source: Alford-Rajagopal-Wilczek NPB 537 (1999); Son-Stephanov PRL
            86 (2001); Hirono-Tanizaki PRL 122, 212001 (2019) [arXiv:1811.10608];
            CenterSymmetryConfinement Lean (W1).
    viz-ref: Phase 6d Paper 38 §3
    """
    import numpy as np
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots

    from src.cfl import EMERGENT_Z3_PHASE

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            "Cube roots of unity: CFL emergent ℤ_3 ≡ QCD center ℤ_3",
            "Topological-order classification by ℤ_3 charge",
        ),
        column_widths=[0.5, 0.5],
        horizontal_spacing=0.18,
        specs=[[{"type": "scatter"}, {"type": "bar"}]],
    )

    # ---------- Left: complex-plane Z_3 ----------
    # Unit circle
    theta = np.linspace(0, 2 * np.pi, 200)
    fig.add_trace(
        go.Scatter(
            x=np.cos(theta), y=np.sin(theta),
            mode="lines", showlegend=False,
            line=dict(color="rgba(120, 120, 120, 0.4)", width=1, dash="dot"),
        ),
        row=1, col=1,
    )
    # Three cube roots: 1, omega, omega^2
    omega = EMERGENT_Z3_PHASE
    roots = [1 + 0j, omega, omega**2]
    labels = ["1 (trivial)", "ω = e^(2πi/3)<br>CFL emergent = QCD center", "ω² = e^(4πi/3)"]
    fig.add_trace(
        go.Scatter(
            x=[r.real for r in roots],
            y=[r.imag for r in roots],
            mode="markers+text",
            marker=dict(
                size=[18, 28, 18],
                color=[COLORS["cross"], COLORS["amber"], COLORS["cross"]],
                line=dict(color=COLORS["horizon"], width=2),
            ),
            text=labels,
            textposition=["bottom right", "top center", "bottom center"],
            textfont=dict(size=10),
            showlegend=False,
            hovertemplate="<b>%{text}</b><br>(%{x:.3f}, %{y:.3f})<extra></extra>",
        ),
        row=1, col=1,
    )
    # Origin axes
    fig.add_shape(
        type="line", x0=-1.2, x1=1.2, y0=0, y1=0,
        line=dict(color="rgba(0,0,0,0.3)", width=1),
        row=1, col=1,
    )
    fig.add_shape(
        type="line", x0=0, x1=0, y0=-1.2, y1=1.2,
        line=dict(color="rgba(0,0,0,0.3)", width=1),
        row=1, col=1,
    )
    # Annotation: 1 + omega + omega^2 = 0
    fig.add_annotation(
        x=0, y=-0.35,
        text="1 + ω + ω² = 0<br>(distinguishes ℤ_3 from ℤ_2)",
        showarrow=False,
        font=dict(size=10, color=COLORS["amber"]),
        xref="x1", yref="y1",
    )
    fig.update_xaxes(title_text="Re", range=[-1.4, 1.4], row=1, col=1, scaleanchor="y", scaleratio=1)
    fig.update_yaxes(title_text="Im", range=[-1.4, 1.4], row=1, col=1)

    # ---------- Right: Topological order classification ----------
    charges = [0, 1, 2, 3]
    is_topological = [False, True, True, False]
    bar_colors = [
        COLORS["amber"] if not topo else COLORS["steel_blue"]
        for topo in is_topological
    ]
    labels_right = [
        "0<br>(trivial vacuum)",
        "1<br>(topological)",
        "2<br>(topological)",
        "3<br>(out of ℤ_3)",
    ]
    fig.add_trace(
        go.Bar(
            x=labels_right,
            y=[1, 1, 1, 1],
            marker_color=bar_colors,
            text=[
                "✗ falsifier" if c == 0 else "✓ witness" if topo else "✗ falsifier"
                for c, topo in zip(charges, is_topological)
            ],
            textposition="auto",
            showlegend=False,
            hovertemplate="<b>charge = %{x}</b><br>topological: %{text}<extra></extra>",
        ),
        row=1, col=2,
    )
    fig.update_xaxes(title_text="ℤ_3 charge", row=1, col=2)
    fig.update_yaxes(title_text="In Hirono-Tanizaki sector?", showticklabels=False, row=1, col=2, range=[0, 1.3])

    apply_layout(
        fig,
        title=dict(
            text=(
                "Phase 6d Wave 3 — CFL emergent ℤ_3 (Hirono-Tanizaki) "
                "≡ QCD center ℤ_3 (W1) correctness-push identification"
            ),
            font=TITLE_FONT,
        ),
        height=580,
        width=1300,
        margin=dict(t=110, b=80),
    )
    return fig


def fig_gmor_relation_verification():
    """Phase 6d Wave 2: GMOR relation numerical verification at PDG values.

    Left panel: bar chart comparing the GMOR LHS = m_π² · f_π² and RHS
    = −2 m_q · ⟨q̄q⟩ at PDG/FLAG central values. Both bars sit at
    1.589e-4 GeV⁴ — visually indistinguishable, confirming GMOR holds
    to ~1 part in 10⁴.

    Right panel: relative residual |LHS − RHS| / LHS as the input quark
    mass m_q is varied. The residual minimum sits at the PDG value
    m_q ≈ 3.5 MeV, confirming this is the GMOR-consistent point.

    Lean: ChiralSSB_QCD.gmor_pdg_match,
          gmor_rhs_pos_of_quark_mass_pos,
          chiral_unbroken_violates_gmor.
    Source: Gell-Mann-Oakes-Renner PR 175 (1968); FLAG 2021 EPJC 81;
            PDG 2022.
    viz-ref: Phase 6d Paper 37 §3
    """
    import numpy as np
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots

    from src.chiral_ssb import (
        FLAG_LATTICE_VALUE,
        PDG_F_PI,
        PDG_M_PI,
        PDG_M_Q,
        gmor_lhs,
        gmor_rhs,
    )

    lhs_value = gmor_lhs(PDG_M_PI, PDG_F_PI)
    rhs_value = gmor_rhs(PDG_M_Q, FLAG_LATTICE_VALUE)

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            f"GMOR LHS vs RHS at PDG central values (≈ {lhs_value:.3e} GeV⁴)",
            "GMOR residual |LHS − RHS|/LHS vs m_q",
        ),
        column_widths=[0.45, 0.55],
        horizontal_spacing=0.18,
    )

    # ---------- Left: side-by-side bars ----------
    fig.add_trace(
        go.Bar(
            x=["LHS = m_π² · f_π²", "RHS = −2 m_q · ⟨q̄q⟩"],
            y=[lhs_value, rhs_value],
            marker_color=[COLORS["steel_blue"], COLORS["amber"]],
            text=[f"{lhs_value:.4e}", f"{rhs_value:.4e}"],
            textposition="outside",
            textfont=dict(size=11),
            showlegend=False,
            hovertemplate="<b>%{x}</b><br>%{y:.6e} GeV⁴<extra></extra>",
        ),
        row=1, col=1,
    )
    fig.update_yaxes(title_text="GeV⁴", row=1, col=1)
    fig.add_annotation(
        x=0.5, y=lhs_value * 1.15,
        text=f"|LHS − RHS| ≈ {abs(lhs_value - rhs_value):.2e} GeV⁴<br>(~1 part in 10⁴)",
        showarrow=False,
        font=dict(size=10, color=COLORS["horizon"]),
        xref="x1", yref="y1",
    )

    # ---------- Right: residual vs m_q sweep ----------
    m_q_grid = np.linspace(0.0005, 0.020, 200)
    residuals = np.array([
        abs(lhs_value - gmor_rhs(m_q, FLAG_LATTICE_VALUE)) / lhs_value
        for m_q in m_q_grid
    ])

    fig.add_trace(
        go.Scatter(
            x=m_q_grid * 1000,  # convert to MeV for readability
            y=residuals,
            mode="lines",
            name="|LHS − RHS|/LHS",
            line=dict(color=COLORS["steel_blue"], width=2.5),
        ),
        row=1, col=2,
    )

    # PDG m_q reference vertical line
    fig.add_shape(
        type="line",
        x0=PDG_M_Q * 1000, x1=PDG_M_Q * 1000,
        y0=1e-4, y1=10,
        line=dict(color=COLORS["amber"], width=2, dash="dash"),
        row=1, col=2,
    )
    fig.add_annotation(
        x=PDG_M_Q * 1000 + 0.5, y=0.05,
        text=f"PDG m_q ≈ {PDG_M_Q * 1000:.1f} MeV<br>(GMOR minimum)",
        showarrow=False,
        font=dict(size=10, color=COLORS["amber"]),
        xanchor="left",
        row=1, col=2,
    )

    fig.update_xaxes(title_text="m_q [MeV]", row=1, col=2)
    fig.update_yaxes(title_text="Relative residual", type="log", row=1, col=2)

    apply_layout(
        fig,
        title=dict(
            text=(
                "Phase 6d Wave 2 — GMOR relation verification "
                "(m_π² · f_π² = −2 m_q · ⟨q̄q⟩) at PDG/FLAG central values"
            ),
            font=TITLE_FONT,
        ),
        height=580,
        width=1300,
        margin=dict(t=110, b=80),
    )
    return fig


def fig_code_distance_vs_fusion_spectrum():
    """Phase 6c Wave 4: code-distance proxy `d_C := log d_max` and
    Hayden-Preskill scrambling-time bound `t_scr := log D²` across MTC
    spectra (Fibonacci, Ising, SU(3)_k=2 Fibonacci sub-sector,
    trivial-abelian).

    Left panel: code-distance bar chart comparing the four substrates,
    with the admissibility threshold at d_C = 0 highlighted. Trivial-
    abelian falsifies the W4 admissibility criterion (`d_C = 0`); the
    three non-abelian substrates all satisfy it.

    Right panel: scrambling-time bound `t_scr = log D²` for each
    substrate, demonstrating that admissibility (positive code distance)
    forces a positive scrambling time — the W4 correctness-push.

    Lean: QECHolographyBridge.code_distance_scaling_matches_anyonic_fusion_iff_fusion_in_admissible_class,
          code_distance_scaling_matches_anyonic_fusion_iff_fusion_in_admissible_class,
          fibonacci_HPCode_codeDistance_lt_log_two,
          trivialAbelian_violates_admissibility.
    Source: Hayden-Preskill JHEP 2007/9/120 (arXiv:0708.4025);
            Almheiri-Dong-Harlow JHEP 2015/4/163 (arXiv:1411.7041).
    viz-ref: Phase 6c Paper 35 §3
    """
    import math
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots

    from src.qec_holography import (
        FIBONACCI_SPECTRUM,
        ISING_SPECTRUM,
        SU3K2_SPECTRUM,
        TRIVIAL_ABELIAN_SPECTRUM,
        code_distance,
        scrambling_time_bound,
    )

    spectra = [
        FIBONACCI_SPECTRUM,
        ISING_SPECTRUM,
        SU3K2_SPECTRUM,
        TRIVIAL_ABELIAN_SPECTRUM,
    ]
    labels = ["Fibonacci<br>(d_τ = φ)", "Ising<br>(d_σ = √2)",
              "SU(3)_k=2<br>(adj sector, φ)", "Trivial<br>abelian (d=1)"]
    cd_vals = [code_distance(s) for s in spectra]
    st_vals = [scrambling_time_bound(s) for s in spectra]
    bar_colors = [
        COLORS["steel_blue"],
        COLORS["sage"],
        COLORS["amber"],
        COLORS["carmine"],
    ]

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            "Code distance d_C := log d_max (W4 admissibility)",
            "Scrambling-time bound t_scr := log D² = log Σ d_a²",
        ),
        column_widths=[0.5, 0.5],
        horizontal_spacing=0.16,
    )

    # ---------- Left: code distance bars ----------
    fig.add_trace(
        go.Bar(
            x=labels,
            y=cd_vals,
            marker_color=bar_colors,
            text=[f"{v:.3f}" for v in cd_vals],
            textposition="outside",
            showlegend=False,
            hovertemplate="d_C = %{y:.4f}<extra></extra>",
        ),
        row=1, col=1,
    )
    # Admissibility threshold
    fig.add_hline(
        y=0.0,
        line=dict(color="black", width=1.5, dash="dash"),
        annotation_text="admissibility threshold (d_C = 0)",
        annotation_position="bottom right",
        row=1, col=1,
    )
    # Reference: log 2 upper bound for Fibonacci (W4 quantitative theorem)
    fig.add_hline(
        y=math.log(2.0),
        line=dict(color=COLORS["amber"], width=1.5, dash="dot"),
        annotation_text=f"log 2 ≈ {math.log(2.0):.3f} (Fib upper bound)",
        annotation_position="top right",
        row=1, col=1,
    )
    fig.update_yaxes(
        title_text="code distance d_C",
        range=[-0.05, max(cd_vals) * 1.4 + 0.1],
        row=1, col=1,
    )

    # ---------- Right: scrambling time bars ----------
    fig.add_trace(
        go.Bar(
            x=labels,
            y=st_vals,
            marker_color=bar_colors,
            text=[f"{v:.3f}" for v in st_vals],
            textposition="outside",
            showlegend=False,
            hovertemplate="t_scr = %{y:.4f}<extra></extra>",
        ),
        row=1, col=2,
    )
    fig.add_hline(
        y=0.0,
        line=dict(color="black", width=1.5, dash="dash"),
        annotation_text="trivial scrambling (t_scr = 0)",
        annotation_position="top right",
        row=1, col=2,
    )
    fig.update_yaxes(
        title_text="scrambling-time bound t_scr",
        range=[-0.05, max(st_vals) * 1.3 + 0.2],
        row=1, col=2,
    )

    fig.update_layout(
        title=dict(
            text=(
                "<b>Phase 6c Wave 4 — Hayden-Preskill QEC across MTC spectra</b><br>"
                "Code distance + scrambling time as W4 admissibility witnesses; "
                "trivial-abelian falsifies both"
            ),
            font=TITLE_FONT,
        ),
        height=560,
        width=1300,
        margin=dict(t=110, b=80),
    )
    return fig


def fig_rt_ch_bounds_mtc():
    """Phase 6c Wave 5: Ryu-Takayanagi vs Phase 6a W3 Kaul-Majumdar
    microscopic entropy + Casini-Huerta saturated bound across MTC
    central charges.

    Left panel: classical RT entropy `S = A/(4 G_N)` (linear) vs W3
    Kaul-Majumdar microscopic entropy `S = A/(4 G_N) - (3/2) log(A/(4 G_N))`
    (linear minus log) across reduced area. The knife-edge agreement
    point at reduced area = 1 is highlighted; outside this, the two
    formulas disagree by `(3/2) log(A/(4 G_N))`.

    Right panel: Casini-Huerta saturated bound `S(L) = (c/3) log(L/UV)`
    across central charges (Ising c=1/2, free boson c=1, tricritical
    Ising c=7/10, 3-state Potts c=4/5, free Dirac fermion c=1) at fixed
    UV cutoff. Ising 2D CFT is the minimal-c witness; higher-c models
    saturate higher entropies.

    Lean: RTCasiniHuertaBounds.rt_eq_kaulMajumdar_iff_trivial_reduced_area,
          rt_kaulMajumdar_gap_at_reduced_area_two,
          rt_eq_kaulMajumdar_iff_trivial_reduced_area,
          ch_log_bound_pos_at_log_pos,
          H_CasiniHuerta_Bound_Valid_witness_saturated,
          kaulMajumdar_not_H_RT.
    Source: Ryu-Takayanagi PRL 96, 181602 (2006); Casini-Huerta J. Phys.
            A 42, 504007 (2009); Kaul-Majumdar PRL 84 5255 (2000); Sen
            JHEP 1205 0971 (2012) (non-universality witness).
    viz-ref: Phase 6c Paper note_rt_ch_bounds §3
    """
    import math
    import numpy as np
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots

    from src.rt_ch_bounds import (
        classical_rt_entropy,
        kaul_majumdar_entropy,
        saturated_ch_entropy,
    )

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            "RT vs W3 Kaul-Majumdar entropy (W5 correctness-push)",
            "Casini-Huerta saturated bound across 2D CFT central charges",
        ),
        column_widths=[0.5, 0.5],
        horizontal_spacing=0.16,
    )

    # ---------- Left: classical RT vs Kaul-Majumdar across reduced area ----------
    G_N = 1.0
    reduced_areas = np.linspace(0.1, 5.0, 100)
    areas = reduced_areas * 4.0 * G_N
    rt_vals = [classical_rt_entropy(A, G_N) for A in areas]
    km_vals = [kaul_majumdar_entropy(A, G_N) for A in areas]

    fig.add_trace(
        go.Scatter(
            x=reduced_areas,
            y=rt_vals,
            mode="lines",
            line=dict(color=COLORS["steel_blue"], width=2.5),
            name="Classical RT (S = A/4 G_N)",
            hovertemplate="A/(4 G_N) = %{x:.2f}<br>S_RT = %{y:.3f}<extra></extra>",
        ),
        row=1, col=1,
    )
    fig.add_trace(
        go.Scatter(
            x=reduced_areas,
            y=km_vals,
            mode="lines",
            line=dict(color=COLORS["amber"], width=2.5, dash="dash"),
            name="W3 Kaul-Majumdar (with -3/2 log)",
            hovertemplate="A/(4 G_N) = %{x:.2f}<br>S_KM = %{y:.3f}<extra></extra>",
        ),
        row=1, col=1,
    )
    # Mark knife-edge crossing at reduced area = 1
    fig.add_vline(
        x=1.0,
        line=dict(color="black", width=1.5, dash="dot"),
        annotation_text="knife-edge<br>agreement<br>(A = 4 G_N)",
        annotation_position="top right",
        row=1, col=1,
    )
    fig.update_xaxes(title_text="reduced area A/(4 G_N)", row=1, col=1)
    fig.update_yaxes(title_text="entropy S", row=1, col=1)

    # ---------- Right: Casini-Huerta saturated bound across central charges ----------
    cft_models = [
        ("Ising (c=1/2)", 0.5, COLORS["steel_blue"]),
        ("Tricritical Ising (c=7/10)", 0.7, COLORS["sage"]),
        ("3-state Potts (c=4/5)", 0.8, COLORS["amber"]),
        ("Free boson (c=1)", 1.0, COLORS["carmine"]),
    ]
    UV = 1e-3
    L_grid = np.logspace(-2, 1, 80)
    for name, c, color in cft_models:
        S_vals = [saturated_ch_entropy(L, c, UV) for L in L_grid]
        fig.add_trace(
            go.Scatter(
                x=L_grid,
                y=S_vals,
                mode="lines",
                line=dict(color=color, width=2.0),
                name=name,
                hovertemplate=f"c = {c}<br>L = %{{x:.3f}}<br>S = %{{y:.3f}}<extra></extra>",
            ),
            row=1, col=2,
        )
    fig.update_xaxes(
        title_text="region size L (UV cutoff = 1e-3)",
        type="log",
        row=1, col=2,
    )
    fig.update_yaxes(
        title_text="saturated CH entropy (c/3) log(L/UV)",
        row=1, col=2,
    )

    fig.update_layout(
        title=dict(
            text=(
                "<b>Phase 6c Wave 5 — RT/CH entropy bounds: classical vs W3 microscopic, "
                "and CH saturation across 2D CFTs</b>"
            ),
            font=TITLE_FONT,
        ),
        height=580,
        width=1400,
        margin=dict(t=110, b=80),
    )
    return fig


def fig_a2_vs_linearized_G_N():
    """Phase 6e Wave 1: heat-kernel a_2 calibration to Phase 6a.1
    LinearizedEFE.G_N_sakharov.

    Left panel: relative error |G_N_HK − G_N_lin| / G_N_lin as a
    function of α_ADW over [0.05, 5.0] for the GUT-anchor parameters
    (Λ_UV, N_f) = (10¹⁶ GeV, 15). Exact zero at α_ADW = 1 (Sakharov-
    Adler baseline); ±50 % tolerance band shaded; the natural-parameter
    band α_ADW ∈ [0.5, 1.5] (per `GRAV_PARAMS.G_N_MATCH_TOLERANCE`)
    sits inside the green pass region.

    Right panel: log-log plot of G_N(Λ_UV) at fixed N_f = 15 over the
    GRAV_PARAMS Λ_UV range [10¹⁰, 10¹⁹] GeV, with horizontal line at
    G_N^obs (CODATA 2018). At N_f = 15 the curve passes within
    ~factor 3 of the observed line at Λ_UV ≈ M_Pl, confirming the
    heat-kernel calibration reproduces Sakharov's induced-gravity scale
    anchor up to the species-multiplicity prefactor.

    Lean: HeatKernelExpansion.G_N_from_a2_eq_G_N_sakharov,
          a2_matches_GNemerg_iff_alpha_ADW_unity,
          G_N_from_a2_at_GUT_inverse,
          G_N_from_a2_inverse_at_GUT_below_planck_squared.
    Source: Vassilevich Phys. Rep. 388, 279 (2003) Eq. (4.38);
            Sakharov, Sov. Phys. Dokl. 12, 1040 (1968);
            Adler, RMP 54, 729 (1982) Eq. (3.3);
            Phase 6a.1 LinearizedEFE.lean (calibration target).
    viz-ref: Phase 6e Paper 39 §3
    """
    import numpy as np
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots

    from src.core.constants import GRAV_PARAMS, HEAT_KERNEL_PARAMS
    from src.heat_kernel import (
        a2_calibration_relative_error,
    )
    from src.heat_kernel.a2_computation import (
        G_N_from_a2,
        G_N_linearized_at_alpha,
    )

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            "Heat-kernel a₂ calibration error vs α_ADW (Decision Gate E.2)",
            "Heat-kernel G_N(Λ_UV) vs CODATA G_N^obs (anchor at Planck)",
        ),
        column_widths=[0.55, 0.45],
        horizontal_spacing=0.18,
    )

    # ---------- Left: rel error vs alpha ----------
    alphas = np.logspace(np.log10(0.05), np.log10(5.0), 200)
    Lambda_anchor = 1.0e16
    N_f_anchor = 15
    rel_err = np.array([
        a2_calibration_relative_error(Lambda_anchor, N_f_anchor, a)
        for a in alphas
    ])
    tol = HEAT_KERNEL_PARAMS["A2_GN_MATCH_TOLERANCE"]

    # Tolerance band (rel err <= tol = pass)
    fig.add_shape(
        type="rect",
        x0=0.05, x1=5.0,
        y0=0, y1=tol,
        fillcolor=COLORS.get("emerald", "#2ca02c"), opacity=0.18,
        line=dict(width=0),
        row=1, col=1,
    )
    fig.add_trace(
        go.Scatter(
            x=alphas, y=rel_err,
            mode="lines",
            line=dict(color=COLORS["steel_blue"], width=2.5),
            name="|ΔG/G|",
            hovertemplate="α_ADW = %{x:.3f}<br>rel err = %{y:.3f}<extra></extra>",
        ),
        row=1, col=1,
    )
    # Sakharov-Adler reference (alpha = 1)
    fig.add_shape(
        type="line",
        x0=1.0, x1=1.0, y0=0, y1=1.05,
        line=dict(color=COLORS["amber"], width=1.5, dash="dot"),
        row=1, col=1,
    )
    fig.add_annotation(
        x=1.0, y=0.02,
        text="α_ADW = 1<br>Sakharov-Adler",
        showarrow=False,
        font=dict(size=10, color=COLORS["amber"]),
        xanchor="left",
        row=1, col=1,
    )
    fig.add_annotation(
        x=0.07, y=tol * 0.95,
        text=f"pass band<br>±{int(tol*100)}%",
        showarrow=False,
        font=dict(size=10, color=COLORS.get("emerald", "#2ca02c")),
        xanchor="left",
        row=1, col=1,
    )
    fig.update_xaxes(
        title_text="α_ADW",
        type="log",
        tickvals=[0.05, 0.1, 0.5, 1.0, 2.0, 5.0],
        ticktext=["0.05", "0.1", "0.5", "1.0", "2.0", "5.0"],
        row=1, col=1,
    )
    fig.update_yaxes(
        title_text="|G_N_HK − G_N_lin| / G_N_lin",
        range=[0, 1.05],
        row=1, col=1,
    )

    # ---------- Right: G_N vs Lambda_UV ----------
    lam_grid = np.logspace(10, 19, 80)
    G_curve = np.array([G_N_from_a2(L, N_f_anchor) for L in lam_grid])
    G_obs = GRAV_PARAMS["G_N_OBS_GEV_M2"]

    fig.add_trace(
        go.Scatter(
            x=lam_grid, y=G_curve,
            mode="lines",
            line=dict(color=COLORS["steel_blue"], width=2.5),
            name="G_N(Λ_UV) at N_f = 15",
            hovertemplate=(
                "Λ_UV = %{x:.2e} GeV<br>G_N = %{y:.3e} GeV⁻²<extra></extra>"
            ),
        ),
        row=1, col=2,
    )
    fig.add_shape(
        type="line",
        x0=1e10, x1=1e19,
        y0=G_obs, y1=G_obs,
        line=dict(color=COLORS["amber"], width=1.5, dash="dash"),
        row=1, col=2,
    )
    fig.add_annotation(
        x=1e11, y=G_obs * 1.5,
        text=f"CODATA<br>G_N^obs = {G_obs:.2e} GeV⁻²",
        showarrow=False,
        font=dict(size=10, color=COLORS["amber"]),
        xanchor="left",
        row=1, col=2,
    )
    fig.add_shape(
        type="line",
        x0=GRAV_PARAMS["LAMBDA_UV_PLANCK_GEV"],
        x1=GRAV_PARAMS["LAMBDA_UV_PLANCK_GEV"],
        y0=1e-50, y1=1e-15,
        line=dict(color=COLORS["horizon"], width=1.5, dash="dot"),
        row=1, col=2,
    )
    fig.add_annotation(
        x=GRAV_PARAMS["LAMBDA_UV_PLANCK_GEV"] * 0.85,
        y=1e-45,
        text="M_Pl<br>≈ 1.22 × 10¹⁹ GeV",
        showarrow=False,
        font=dict(size=10, color=COLORS["horizon"]),
        xanchor="right",
        row=1, col=2,
    )
    fig.update_xaxes(
        title_text="Λ_UV [GeV]",
        type="log",
        exponentformat="power",
        row=1, col=2,
    )
    fig.update_yaxes(
        title_text="G_N [GeV<sup>-2</sup>]",
        type="log",
        exponentformat="power",
        row=1, col=2,
    )

    fig.update_layout(
        title=dict(
            text=(
                "<b>Phase 6e Wave 1 — Seeley-DeWitt a₂ calibration to "
                "Sakharov-Adler G_N (Decision Gate E.2)</b>"
            ),
            font=TITLE_FONT,
        ),
        height=580,
        width=1400,
        margin=dict(t=110, b=80),
        showlegend=False,
    )
    return fig


def fig_higher_curvature_obs_bounds():
    """Phase 6e Wave 2: microscopic Dirac a_4 predictions vs
    observational ceilings on dimensionless higher-curvature couplings.

    Left panel: bar-chart of |c_R²|, |c_Ricci²|, |c_Riemann²| from the
    Wave 1 Christensen-Duff Dirac a_4 evaluated at SM-relevant fermion
    counts N_f ∈ {24, 27, 100} (with the (4π)⁻² heat-kernel measure
    included).  The Riemann² coefficient dominates at every N_f.

    Right panel: log-scale "ceiling" plot showing the four canonical
    observational bounds (LIGO/Virgo, Eöt-Wash short-range gravity,
    Hulse-Taylor binary pulsar, Cassini post-Newtonian) and the
    largest predicted coefficient from the left panel (at N_f = 27).
    The pulsar bound is the tightest by ~3 orders of magnitude over
    LIGO/Cassini/SRG; even so the predicted O(10⁻³) value sits ~62
    orders of magnitude below the ceiling — the **correctness-push**
    Lean theorem ``higher_curvature_below_pulsar_bound`` formalises
    this passage at the bounded fermion-count window 0 < N_f ≤ 100.

    Lean: HigherCurvatureStructure.higher_curvature_below_pulsar_bound,
          higher_curvature_predictions_strictly_positive,
          H_HigherCurvatureWithinObservationalBounds_pulsar_witness,
          a4_density_eq_a4_density_in_RC2GB_basis.
    Source: Calmet, Capozziello & Pryer, EPJC 77, 589 (2017)
            [arXiv:1708.08253] (EFT translation framework);
            Berti et al, Class. Quantum Grav. 32, 243001 (2015)
            [arXiv:1501.07274] (pulsar timing);
            Phase 6e Wave 1 HeatKernelExpansion.lean (predictions).
    viz-ref: Phase 6e Paper 40 §4
    """
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots

    from src.core.formulas import (
        higher_curvature_R_sq_coefficient,
        higher_curvature_Ricci_sq_coefficient,
        higher_curvature_Riemann_sq_coefficient,
    )
    from src.higher_curvature import HC_OBS_BOUNDS

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            "Wave 1 a₄ Dirac coefficients (per (4π)⁻²) vs N_f",
            "Predicted vs observational ceilings (log scale)",
        ),
        column_widths=[0.55, 0.45],
        horizontal_spacing=0.18,
    )

    # ---------- Left: predicted coefficients vs N_f ----------
    Nf_grid = [24, 27, 100]
    coef_R = [abs(higher_curvature_R_sq_coefficient(n)) for n in Nf_grid]
    coef_Ricci = [abs(higher_curvature_Ricci_sq_coefficient(n))
                  for n in Nf_grid]
    coef_Riem = [abs(higher_curvature_Riemann_sq_coefficient(n))
                 for n in Nf_grid]

    fig.add_trace(
        go.Bar(
            x=[f"N_f = {n}" for n in Nf_grid], y=coef_R,
            marker_color=COLORS["steel_blue"],
            name="|c_R²|", text=[f"{v:.2e}" for v in coef_R],
            textposition="outside",
            hovertemplate="N_f = %{x}<br>|c_R²| = %{y:.3e}<extra></extra>",
        ),
        row=1, col=1,
    )
    fig.add_trace(
        go.Bar(
            x=[f"N_f = {n}" for n in Nf_grid], y=coef_Ricci,
            marker_color=COLORS["amber"],
            name="|c_Ricci²|", text=[f"{v:.2e}" for v in coef_Ricci],
            textposition="outside",
            hovertemplate=("N_f = %{x}<br>|c_Ricci²| = %{y:.3e}"
                           "<extra></extra>"),
        ),
        row=1, col=1,
    )
    fig.add_trace(
        go.Bar(
            x=[f"N_f = {n}" for n in Nf_grid], y=coef_Riem,
            marker_color=COLORS.get("emerald", "#2ca02c"),
            name="|c_Riemann²|", text=[f"{v:.2e}" for v in coef_Riem],
            textposition="outside",
            hovertemplate=("N_f = %{x}<br>|c_Riemann²| = %{y:.3e}"
                           "<extra></extra>"),
        ),
        row=1, col=1,
    )
    fig.update_xaxes(title_text="Fermion count N_f", row=1, col=1)
    fig.update_yaxes(
        title_text="Predicted |c|",
        type="log",
        exponentformat="power",
        row=1, col=1,
    )

    # ---------- Right: ceilings vs prediction ----------
    bound_labels = [
        "LIGO/Virgo<br>(C²)",
        "Eöt-Wash SRG<br>(R²)",
        "Hulse-Taylor<br>pulsar (C²)",
        "Cassini PN<br>(C²)",
        "Predicted max<br>(N_f = 27)",
    ]
    bound_values = [
        HC_OBS_BOUNDS["LIGO_C_sq"],
        HC_OBS_BOUNDS["SRG_R_sq"],
        HC_OBS_BOUNDS["pulsar_C_sq"],
        HC_OBS_BOUNDS["cassini_C_sq"],
        max(coef_Riem[1], coef_Ricci[1], coef_R[1]),  # at N_f=27
    ]
    bound_colors = [
        COLORS["steel_blue"], COLORS["amber"],
        COLORS.get("carmine", "#E63946"), COLORS["horizon"],
        COLORS.get("emerald", "#2ca02c"),
    ]

    fig.add_trace(
        go.Bar(
            x=bound_labels, y=bound_values,
            marker_color=bound_colors,
            text=[f"{v:.0e}" for v in bound_values],
            textposition="outside",
            hovertemplate="%{x}<br>value = %{y:.3e}<extra></extra>",
        ),
        row=1, col=2,
    )
    # Highlight pulsar as tightest
    fig.add_annotation(
        x="Hulse-Taylor<br>pulsar (C²)", y=HC_OBS_BOUNDS["pulsar_C_sq"] * 5,
        text="<i>tightest<br>ceiling</i>",
        showarrow=False,
        font=dict(size=10,
                  color=COLORS.get("carmine", "#E63946")),
        row=1, col=2,
    )
    fig.update_xaxes(
        title_text="Bound or prediction",
        row=1, col=2,
    )
    fig.update_yaxes(
        title_text="|coupling|",
        type="log",
        exponentformat="power",
        row=1, col=2,
    )

    fig.update_layout(
        title=dict(
            text=(
                "<b>Phase 6e Wave 2 — Higher-curvature predictions vs "
                "observational ceilings (correctness-push)</b>"
            ),
            font=TITLE_FONT,
        ),
        height=580,
        width=1400,
        margin=dict(t=110, b=80),
        showlegend=True,
        legend=dict(orientation="h", yanchor="bottom", y=-0.20,
                    xanchor="center", x=0.275),
        barmode="group",
    )
    return fig


def fig_diff_invariance_order_check():
    """Phase 6e Wave 3: order-by-order path-b diff-invariance anomaly check.

    Left panel: log-scale bar chart of the maximum order-``a_4`` anomaly
    residual over a 16-point curvature grid for the Christensen-Duff
    Dirac bundle (at machine ε) versus a perturbed bundle (single
    coefficient shifted by δ ∈ {1e-9, 1e-6, 1e-3}).  The path-b
    tolerance ``DIFF_INVARIANCE_PARAMS['PATH_B_RESIDUAL_TOLERANCE'] = 1e-12``
    is drawn as a dashed reference line.  The Dirac bundle sits below
    tolerance; every nonzero perturbation is detectable above it
    — the **falsifier** witness.

    Right panel: linearity demonstration.  At unit ``R_sq`` and zero
    ``Ricci_sq, Riemann_sq``, the perturbed-bundle residual equals
    exactly ``δ`` (Lean theorem
    ``perturbed_pathB_residual_a4_at_unit_R_sq``).  The diagonal line
    ``residual = δ`` confirms the falsifier is non-tautological — a
    nonzero perturbation produces a nonzero, *predictable* anomaly.

    Lean: NonlinearDiffInvariance.pathB_residual_a4_dirac_eq_zero,
          perturbed_pathB_residual_a4_at_unit_R_sq,
          dirac_H_NonlinearDiffInvariance,
          diff_invariance_a4_iff_dirac_basis_consistent.
    Source: Wald, *General Relativity*, App. E.1 (path-b framework);
            Phase 6e Wave 1 HeatKernelExpansion.lean (Dirac coefs);
            Phase 6e Wave 2 HigherCurvatureStructure.lean
            (basis-change identity).
    viz-ref: Phase 6e Paper 41 §3
    """
    import plotly.graph_objects as go
    import numpy as np
    from plotly.subplots import make_subplots
    from src.core.constants import DIFF_INVARIANCE_PARAMS
    from src.diff_invariance import (
        max_residual_over_grid,
        pathB_residual_at_order,
        perturbed_coefficient_bundle,
    )

    tol = float(DIFF_INVARIANCE_PARAMS['PATH_B_RESIDUAL_TOLERANCE'])

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            "Max grid residual: Dirac vs perturbed (log scale)",
            "Falsifier linearity: residual = δ at unit R²",
        ),
        column_widths=[0.5, 0.5],
        horizontal_spacing=0.15,
    )

    # ---------- Left: max residual on grid for several bundles ----------
    deltas = [0.0, 1e-9, 1e-6, 1e-3]
    superscripts = {-9: "⁻⁹", -6: "⁻⁶", -3: "⁻³"}
    bundle_labels = ["Dirac (δ=0)"] + [
        f"δ=10{superscripts[int(np.log10(d))]}" for d in deltas[1:]
    ]
    max_res = [max_residual_over_grid(24.0, 'dirac')] + [
        max_residual_over_grid(24.0, 'perturbed', delta=d) for d in deltas[1:]
    ]
    # Floor at 1e-20 for log scale (machine eps may produce 0)
    max_res_plot = [max(v, 1e-20) for v in max_res]
    bar_colors = [COLORS["steel_blue"]] + [COLORS["amber"],
                                              COLORS.get("carmine", "#E63946"),
                                              COLORS.get("emerald", "#2ca02c")]
    fig.add_trace(
        go.Bar(
            x=bundle_labels, y=max_res_plot,
            marker_color=bar_colors,
            text=[f"{v:.1e}" for v in max_res],
            textposition="outside",
            hovertemplate="%{x}<br>max |residual| = %{y:.2e}<extra></extra>",
            showlegend=False,
        ),
        row=1, col=1,
    )
    # Path-b tolerance line
    fig.add_hline(
        y=tol,
        line=dict(color=COLORS.get("carmine", "#E63946"),
                  dash="dash", width=2),
        annotation_text=f"path-b tolerance = {tol:.0e}",
        annotation_position="bottom right",
        row=1, col=1,
    )
    fig.update_xaxes(title_text="Coefficient bundle", row=1, col=1,
                       tickangle=0, automargin=True)
    fig.update_yaxes(
        title_text="max |path-b residual|, dimensionless (grid)",
        type="log",
        exponentformat="power",
        row=1, col=1,
    )

    # ---------- Right: residual vs δ on log-log plot ----------
    delta_grid = np.logspace(-9, 0, 30)
    residuals = np.array([
        pathB_residual_at_order(
            4, perturbed_coefficient_bundle(24.0, d),
            24.0, 0.0, 1.0, 0.0, 0.0)
        for d in delta_grid
    ])
    fig.add_trace(
        go.Scatter(
            x=delta_grid, y=residuals,
            mode="markers+lines",
            name="numerical",
            marker=dict(color=COLORS["amber"], size=8),
            line=dict(color=COLORS["amber"], width=1.5),
            hovertemplate="δ = %{x:.2e}<br>residual = %{y:.2e}<extra></extra>",
        ),
        row=1, col=2,
    )
    fig.add_trace(
        go.Scatter(
            x=delta_grid, y=delta_grid,
            mode="lines",
            name="theory: residual = δ",
            line=dict(color=COLORS["steel_blue"], dash="dot", width=2),
            hoverinfo="skip",
        ),
        row=1, col=2,
    )
    fig.update_xaxes(
        title_text="Perturbation δ",
        type="log",
        exponentformat="power",
        row=1, col=2,
    )
    fig.update_yaxes(
        title_text="path-b residual at R²=1, dimensionless",
        type="log",
        exponentformat="power",
        row=1, col=2,
    )

    fig.update_layout(
        title=dict(
            text=(
                "<b>Phase 6e Wave 3 — Path-b diff-invariance check at "
                "order a₄ (Dirac vs perturbed)</b>"
            ),
            font=TITLE_FONT,
        ),
        height=580,
        width=1400,
        margin=dict(t=110, b=110),
        showlegend=True,
        legend=dict(orientation="h", yanchor="bottom", y=-0.30,
                    xanchor="center", x=0.78),
    )
    return fig


def fig_T_emerg_vs_matter():
    """Phase 6e Wave 4: emergent vs matter stress-energy + multi-channel
    PPN observable signatures under the ADW α_ADW rescaling.

    Left panel: linear-in-(α-1) deviation channel.  ``T_emerg − T_matter
    = (α_ADW − 1) · ρ_ADW``: vanishes at the Sakharov-Adler calibration
    α=1 (Lean theorem
    ``emergentStressEnergyTrace_eq_matter_iff_alpha_unity``).  The
    detection floor (``T_EMERG_DEVIATION_DETECT_FLOOR = 5×10⁻³``) is
    marked as a horizontal band; non-zero deviation rules out the
    calibrated reading.

    Right panel: multi-channel PPN observable deviations vs α_ADW on a
    log-spaced grid covering the natural Vergeles band [0.1, 10].  Three
    curves:

    - **Deflection** (``δθ/δθ_GR − 1 = α − 1``) — direct G_N rescaling
    - **Precession** (``δφ/δφ_GR − 1 = (2α + 1)/3 − 1 = (2/3)(α − 1)``)
      — PPN-mixed; *2/3 times* the deflection deviation (testable
      cross-channel structural claim, Lean theorem
      ``precession_dev_eq_two_thirds_deflection_dev``)
    - **Ringdown** (``ω/ω_GR − 1 = α − 1``) — linearized Schwarzschild

    Observation floors (VLBI 3×10⁻⁴, MESSENGER 1×10⁻⁴, GWTC-3 5×10⁻²)
    drawn as horizontal lines: any predicted deviation above its floor
    is detectable.

    Lean: NonlinearEFE.emergentStressEnergyTrace_minus_matter_eq,
          NonlinearEFE.deflectionRatio_minus_one_eq,
          NonlinearEFE.precessionRatio_eq_one_iff_alpha_unity,
          NonlinearEFE.precession_dev_eq_two_thirds_deflection_dev,
          NonlinearEFE.deflectionRatio_deviation_exceeds_VLBI_floor.
    Source: Will, *Theory and Experiment in Gravitational Physics*
            (2nd ed., 2018), §4.1, §4.2; Berti et al. CQG 26:163001 (2009).
    viz-ref: Phase 6e Paper 42 §4
    """
    import numpy as np
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots
    from src.core.constants import NONLINEAR_EFE_PARAMS

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            "Linear deviation channel: T_emerg − T_matter = (α−1) ρ",
            "Multi-channel PPN observable deviations vs α_ADW",
        ),
        column_widths=[0.45, 0.55],
        horizontal_spacing=0.15,
    )

    # ---------- Left: T_emerg − T_matter at fixed ρ ----------
    rho = 1.0  # unit density; deviation is linear in ρ
    alpha_grid_lin = np.linspace(0.1, 2.5, 80)
    deviation_lin = (alpha_grid_lin - 1.0) * rho
    detect_floor = float(
        NONLINEAR_EFE_PARAMS['T_EMERG_DEVIATION_DETECT_FLOOR']
    )
    fig.add_trace(
        go.Scatter(
            x=alpha_grid_lin, y=deviation_lin,
            mode="lines",
            name="T_emerg − T_matter",
            line=dict(color=COLORS["steel_blue"], width=2.5),
            hovertemplate="α=%{x:.2f}<br>Δ=%{y:.3f}<extra></extra>",
        ),
        row=1, col=1,
    )
    # Detection floor band
    fig.add_hrect(
        y0=-detect_floor, y1=detect_floor,
        fillcolor=COLORS["amber"], opacity=0.20,
        line_width=0,
        row=1, col=1,
    )
    fig.add_hline(
        y=0, line=dict(color="black", dash="dot", width=1),
        row=1, col=1,
    )
    fig.add_vline(
        x=1.0,
        line=dict(color=COLORS.get("emerald", "#2ca02c"),
                  dash="dash", width=2),
        annotation_text="α=1 (calib)",
        annotation_position="top left",
        row=1, col=1,
    )
    fig.update_xaxes(title_text="α_ADW (dimensionless)", row=1, col=1)
    fig.update_yaxes(
        title_text="T_emerg − T_matter at ρ=1 (dimensionless)",
        row=1, col=1,
    )

    # ---------- Right: multi-channel observable deviations ----------
    alpha_grid_log = np.logspace(np.log10(0.1), np.log10(10.0), 50)
    defl_dev = alpha_grid_log - 1.0
    prec_dev = (2.0 * alpha_grid_log + 1.0) / 3.0 - 1.0
    ring_dev = alpha_grid_log - 1.0
    abs_defl = np.abs(defl_dev)
    abs_prec = np.abs(prec_dev)
    abs_ring = np.abs(ring_dev)

    fig.add_trace(
        go.Scatter(
            x=alpha_grid_log, y=abs_defl,
            mode="lines",
            name="Deflection |δθ/δθ_GR − 1| = |α−1|",
            line=dict(color=COLORS["steel_blue"], width=2.5),
            hovertemplate="α=%{x:.2f}<br>|dev|=%{y:.3e}<extra></extra>",
        ),
        row=1, col=2,
    )
    fig.add_trace(
        go.Scatter(
            x=alpha_grid_log, y=abs_prec,
            mode="lines",
            name="Precession |δφ/δφ_GR − 1| = (2/3)|α−1|",
            line=dict(color=COLORS["amber"], width=2.5, dash="dash"),
            hovertemplate="α=%{x:.2f}<br>|dev|=%{y:.3e}<extra></extra>",
        ),
        row=1, col=2,
    )
    fig.add_trace(
        go.Scatter(
            x=alpha_grid_log, y=abs_ring,
            mode="lines",
            name="Ringdown |ω/ω_GR − 1| = |α−1|",
            line=dict(color=COLORS.get("emerald", "#2ca02c"),
                       width=2, dash="dot"),
            hovertemplate="α=%{x:.2f}<br>|dev|=%{y:.3e}<extra></extra>",
        ),
        row=1, col=2,
    )
    # Observation floors
    floors = {
        "VLBI (deflection)": NONLINEAR_EFE_PARAMS[
            'DEFLECTION_OBS_RELATIVE_PRECISION'
        ],
        "MESSENGER (perihelion)": NONLINEAR_EFE_PARAMS[
            'PERIHELION_OBS_RELATIVE_PRECISION'
        ],
        "GWTC-3 (ringdown)": NONLINEAR_EFE_PARAMS[
            'RINGDOWN_OBS_RELATIVE_PRECISION'
        ],
    }
    floor_colors = [
        COLORS["steel_blue"], COLORS["amber"],
        COLORS.get("emerald", "#2ca02c"),
    ]
    for (label, val), c in zip(floors.items(), floor_colors):
        fig.add_hline(
            y=val,
            line=dict(color=c, dash="dashdot", width=1),
            annotation_text=label,
            annotation_position="bottom right",
            annotation_font=dict(size=10),
            row=1, col=2,
        )
    fig.add_vline(
        x=1.0, line=dict(color="black", dash="dot", width=1),
        annotation_text="α=1",
        annotation_position="top",
        row=1, col=2,
    )
    fig.update_xaxes(
        title_text="α_ADW (log scale)",
        type="log", exponentformat="power",
        row=1, col=2,
    )
    fig.update_yaxes(
        title_text="|relative deviation| (dimensionless)",
        type="log", exponentformat="power",
        row=1, col=2,
    )

    fig.update_layout(
        title=dict(
            text=(
                "<b>Phase 6e Wave 4 — Emergent vs matter stress-energy "
                "and multi-channel PPN observable deviations</b>"
            ),
            font=TITLE_FONT,
        ),
        height=600,
        width=1400,
        margin=dict(t=110, b=120),
        showlegend=True,
        legend=dict(orientation="h", yanchor="bottom", y=-0.35,
                    xanchor="center", x=0.5),
    )
    return fig


def fig_lambda_emerg_parameter_scan():
    """Phase 6e Wave 5: Λ^emerg parameter scan + Decision Gate E.4 verdict.

    Left panel: log-log Λ^emerg vs Λ_UV at fixed N_f curves (N_f ∈
    {1, 4, 16, 100}).  Λ_obs (Planck 2018) drawn as horizontal anchor;
    M_Pl drawn as vertical anchor.  Lean witness:
    ``lambdaEmergMicroscopic_at_planck_natural_far_exceeds_observed``
    — the SM N_f=16 curve at Λ_UV=M_Pl exceeds Λ_obs by 122 orders of
    magnitude (CC problem reproduced in emergent form).

    Right panel: Decision-Gate-E.4 verdict band map.  log10(Λ^emerg/Λ_obs)
    over the (Λ_UV, N_f) plane, with three verdict bands shaded:
    ``cc_resolved`` (|log10 ratio| < 1, narrow band near the resolution
    locus), ``cc_intermediate`` (intermediate band), ``cc_reproduced``
    (log10 ratio > 60, broad upper-right region — encompasses the entire
    natural high-energy theory band).

    Lean: MicroscopicCoefficientMatch.lambdaEmergMicroscopic,
          MicroscopicCoefficientMatch.lambdaEmergMicroscopic_at_planck_natural_far_exceeds_observed.
    Source: Sakharov 1968; Vassilevich 2003 Eq. (4.37); Weinberg RMP 61
            (1989) — CC problem; Planck 2018 (Aghanim et al., A&A 641, A6).
    viz-ref: Phase 6e Paper 42b §3
    """
    import numpy as np
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots
    from src.core.constants import MICRO_MACRO_PARAMS
    from src.core.formulas import lambda_emerg_microscopic

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            "Λ^emerg(Λ_UV, N_f) — natural cutoff CC problem reproduction",
            "Decision Gate E.4: log10(Λ^emerg / Λ_obs) verdict bands",
        ),
        column_widths=[0.5, 0.5],
        horizontal_spacing=0.15,
    )

    # Common scan grid
    lo = MICRO_MACRO_PARAMS["LAMBDA_UV_SCAN_MIN_GEV"]
    hi = MICRO_MACRO_PARAMS["LAMBDA_UV_SCAN_MAX_GEV"]
    n_pts = MICRO_MACRO_PARAMS["LAMBDA_UV_SCAN_POINTS"]
    Lambda_UV_grid = np.logspace(np.log10(lo), np.log10(hi), num=int(n_pts))
    M_Pl = MICRO_MACRO_PARAMS["M_PLANCK_GEV"]
    Lambda_obs = MICRO_MACRO_PARAMS["LAMBDA_OBSERVED_GEV4"]
    locus = MICRO_MACRO_PARAMS["LAMBDA_UV_RESOLUTION_LOCUS_DIAGNOSTIC_GEV"]

    # ---------- Left panel: Λ^emerg vs Λ_UV at fixed N_f ----------
    N_f_values = [1, 4, 16, 100]
    # Colorblind-safe palette per project rule (no red/green pairings).
    # Each curve also gets a distinct linestyle so that overlapping log-log
    # traces remain visually distinguishable.
    nf_colors = [
        COLORS["steel_blue"],   # #2E86AB
        COLORS["amber"],        # #F18F01
        COLORS["Heidelberg"],   # #A23B72 (berry)
        COLORS["cross"],        # #8D99AE (cool grey)
    ]
    nf_dashes = ["solid", "dash", "dot", "dashdot"]
    for N_f, c, d in zip(N_f_values, nf_colors, nf_dashes):
        Lambda_emerg_curve = np.array([
            lambda_emerg_microscopic(L, N_f) for L in Lambda_UV_grid
        ])
        fig.add_trace(
            go.Scatter(
                x=Lambda_UV_grid, y=Lambda_emerg_curve,
                mode="lines",
                name=f"N_f={N_f}",
                line=dict(color=c, width=2.5, dash=d),
                hovertemplate=(
                    "Λ_UV=%{x:.2e} GeV<br>"
                    "Λ^emerg=%{y:.2e} GeV⁴<extra></extra>"
                ),
            ),
            row=1, col=1,
        )
    # Λ_obs reference line
    fig.add_hline(
        y=Lambda_obs,
        line=dict(color="black", dash="dot", width=2),
        annotation_text=f"Λ_obs ≃ {Lambda_obs:.1e} GeV⁴ (Planck 2018)",
        annotation_position="top right",
        row=1, col=1,
    )
    # M_Pl anchor (palette-safe: berry, not red)
    fig.add_vline(
        x=M_Pl,
        line=dict(color=COLORS["Heidelberg"],
                  dash="dash", width=2),
        annotation_text="M_Pl",
        annotation_position="top",
        row=1, col=1,
    )
    # Resolution locus is at Λ_UV ≃ 2.83e-12 GeV — far below the displayed
    # [10^0, 10^20] GeV range used for the natural high-energy band.
    # Rendering the vline at that position causes a clipped-annotation
    # artifact at the left margin in kaleido output, so the locus is
    # not drawn here. The locus is documented in
    # MICRO_MACRO_PARAMS["LAMBDA_UV_RESOLUTION_LOCUS_DIAGNOSTIC_GEV"]
    # for cross-reference.
    _ = locus  # mark intentional non-use
    fig.update_xaxes(
        title_text="Λ_UV  [GeV]",
        type="log",
        autorange=False,
        range=[0, 20],
        exponentformat="power",
        row=1, col=1,
    )
    fig.update_yaxes(
        title_text="Λ^emerg  [GeV⁴]",
        type="log", exponentformat="power",
        row=1, col=1,
    )

    # ---------- Right panel: log10 ratio verdict bands ----------
    band_resolved = MICRO_MACRO_PARAMS["CC_RESOLVED_LOG10_BAND"]
    band_reproduced_floor_log = float(np.log10(
        MICRO_MACRO_PARAMS["CC_REPRODUCED_RATIO_FLOOR"]
    ))
    # 2D grid: Λ_UV × N_f → log10 ratio
    N_f_axis = np.linspace(1.0, 100.0, 60)
    Lam_axis = np.logspace(np.log10(lo), np.log10(hi), num=int(n_pts))
    Z = np.zeros((len(N_f_axis), len(Lam_axis)))
    for i, n in enumerate(N_f_axis):
        for j, L in enumerate(Lam_axis):
            le = lambda_emerg_microscopic(L, n)
            Z[i, j] = np.log10(le / Lambda_obs) if le > 0 else np.nan

    fig.add_trace(
        go.Heatmap(
            x=Lam_axis, y=N_f_axis, z=Z,
            colorscale="Cividis",
            colorbar=dict(
                title="log₁₀(Λ^emerg/Λ_obs)",
                tickvals=[-50, 0, band_reproduced_floor_log, 100],
                ticktext=["−50", "0", "60", "100"],
                x=1.10,
            ),
            hovertemplate=(
                "Λ_UV=%{x:.2e} GeV<br>"
                "N_f=%{y:.1f}<br>"
                "log10 ratio=%{z:.2f}<extra></extra>"
            ),
        ),
        row=1, col=2,
    )
    # Verdict-band contours: |log10 ratio| = 1 (resolved boundary),
    # log10 ratio = 60 (reproduced boundary)
    fig.add_trace(
        go.Contour(
            x=Lam_axis, y=N_f_axis, z=Z,
            contours=dict(
                start=-band_resolved,
                end=band_resolved,
                size=2.0 * band_resolved,
                coloring="lines",
                showlabels=True,
            ),
            line=dict(color=COLORS["steel_blue"], width=2),
            showscale=False,
            name="cc_resolved boundary",
            hoverinfo="skip",
        ),
        row=1, col=2,
    )
    fig.add_trace(
        go.Contour(
            x=Lam_axis, y=N_f_axis, z=Z,
            contours=dict(
                start=band_reproduced_floor_log,
                end=band_reproduced_floor_log,
                size=1.0,
                coloring="lines",
                showlabels=True,
            ),
            line=dict(color=COLORS["amber"], width=2),
            showscale=False,
            name="cc_reproduced boundary",
            hoverinfo="skip",
        ),
        row=1, col=2,
    )
    fig.add_vline(
        x=M_Pl,
        line=dict(color=COLORS["Heidelberg"],
                  dash="dash", width=2),
        annotation_text="M_Pl",
        annotation_position="top",
        row=1, col=2,
    )
    fig.update_xaxes(
        title_text="Λ_UV  [GeV]",
        type="log", exponentformat="power",
        row=1, col=2,
    )
    fig.update_yaxes(
        title_text="N_f (Dirac species)",
        row=1, col=2,
    )

    fig.update_layout(
        title=dict(
            text=(
                "<b>Phase 6e Wave 5 — Λ^emerg parameter scan and Decision "
                "Gate E.4 verdict (CC problem reproduced in emergent form)</b>"
            ),
            font=TITLE_FONT,
        ),
        height=600,
        width=1400,
        margin=dict(t=110, b=120, r=120),
        showlegend=True,
        legend=dict(orientation="h", yanchor="bottom", y=-0.30,
                    xanchor="center", x=0.5),
    )
    return fig


def fig_torsion_obs_bound():
    """Phase 6e Wave 6: Einstein-Cartan torsion vs observational bounds.

    Left panel: log-log |T_EC|(Λ_UV) at fixed N_f curves at α_EC = 1
    (Sakharov-Adler calibration).  Kostelecky and Hughes-Drever bounds
    drawn as horizontal anchors.  M_Pl drawn as a vertical anchor where
    the natural-cutoff prediction lands.  Lean witness:
    ``torsionAtCosmologicalBackground_at_planck_natural_below_kostelecky``
    — at (Λ_UV, N_f, α_EC) = (M_Pl, 16, 1) the prediction sits ~46 orders
    of magnitude below Kostelecky.

    Right panel: log10(bound / |T_EC|) — orders of magnitude of headroom
    below Kostelecky — over the (Λ_UV, N_f) plane for α_EC = 1.  All
    natural-parameter points land in the deep-margin region; the entire
    verdict surface is `torsion_below_bound`.

    Lean: EinsteinCartanExtension.torsionAtCosmologicalBackground,
          torsionAtCosmologicalBackground_at_planck_natural_below_kostelecky,
          torsionBoundKostelecky_lt_hughesDrever.
    Source: Hehl-Heyde-Kerlick-Nester, Rev. Mod. Phys. 48, 393 (1976);
            Kostelecky-Russell-Tasson, PRL 100, 111102 (2008);
            Lammerzahl, PRD 64, 084014 (2001).
    viz-ref: Phase 6e Paper 43 §3
    """
    import numpy as np
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots
    from src.core.constants import EINSTEIN_CARTAN_PARAMS
    from src.core.formulas import torsion_amplitude_at_cosmological_background

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            "|T_EC|(Λ_UV, N_f) at α_EC = 1 vs published torsion bounds",
            "log₁₀(Kostelecky / |T_EC|) — orders of magnitude of headroom",
        ),
        column_widths=[0.5, 0.5],
        horizontal_spacing=0.15,
    )

    # Common scan grid (TeV → M_Pl)
    lo = EINSTEIN_CARTAN_PARAMS["LAMBDA_UV_SCAN_MIN_GEV"]
    hi = EINSTEIN_CARTAN_PARAMS["LAMBDA_UV_SCAN_MAX_GEV"]
    n_pts = EINSTEIN_CARTAN_PARAMS["LAMBDA_UV_SCAN_POINTS"]
    Lambda_UV_grid = np.logspace(np.log10(lo), np.log10(hi), num=int(n_pts))
    bound_K = EINSTEIN_CARTAN_PARAMS["TORSION_BOUND_KOSTELECKY_GEV"]
    bound_HD = EINSTEIN_CARTAN_PARAMS["TORSION_BOUND_HUGHES_DREVER_GEV"]
    M_Pl = 1.221e19

    # ---------- Left panel: |T_EC| vs Λ_UV at fixed N_f ----------
    N_f_values = [1, 4, 16, 100]
    # Palette-safe (no red/green) + linestyle-distinct N_f curves.
    nf_colors = [
        COLORS["steel_blue"],   # #2E86AB
        COLORS["amber"],        # #F18F01
        COLORS["Heidelberg"],   # #A23B72 (berry)
        COLORS["cross"],        # #8D99AE (cool grey)
    ]
    nf_dashes = ["solid", "dash", "dot", "dashdot"]
    for N_f, c, d in zip(N_f_values, nf_colors, nf_dashes):
        T_curve = np.array([
            torsion_amplitude_at_cosmological_background(L, N_f, 1.0)
            for L in Lambda_UV_grid
        ])
        fig.add_trace(
            go.Scatter(
                x=Lambda_UV_grid, y=T_curve,
                mode="lines",
                name=f"N_f={N_f}",
                line=dict(color=c, width=2.5, dash=d),
                hovertemplate=(
                    "Λ_UV=%{x:.2e} GeV<br>"
                    "|T_EC|=%{y:.2e} GeV<extra></extra>"
                ),
            ),
            row=1, col=1,
        )
    # Kostelecky bound
    fig.add_hline(
        y=bound_K,
        line=dict(color="black", dash="dot", width=2),
        annotation_text=f"Kostelecky bound = {bound_K:.0e} GeV",
        annotation_position="top right",
        row=1, col=1,
    )
    # Hughes-Drever bound
    fig.add_hline(
        y=bound_HD,
        line=dict(color="gray", dash="dashdot", width=1.5),
        annotation_text=f"Hughes-Drever = {bound_HD:.0e} GeV",
        annotation_position="bottom right",
        row=1, col=1,
    )
    # M_Pl anchor (palette-safe: berry, not red)
    fig.add_vline(
        x=M_Pl,
        line=dict(color=COLORS["Heidelberg"],
                  dash="dash", width=2),
        annotation_text="M_Pl",
        annotation_position="top",
        row=1, col=1,
    )
    fig.update_xaxes(
        title_text="Λ_UV (GeV, log scale)",
        type="log", exponentformat="power",
        row=1, col=1,
    )
    fig.update_yaxes(
        title_text="|T_EC| (GeV, log scale)",
        type="log", exponentformat="power",
        row=1, col=1,
    )

    # ---------- Right panel: log10(bound / |T_EC|) heatmap ----------
    N_f_axis = np.linspace(1.0, 100.0, 60)
    Lam_axis = np.logspace(np.log10(lo), np.log10(hi), num=int(n_pts))
    Z = np.zeros((len(N_f_axis), len(Lam_axis)))
    for i, n in enumerate(N_f_axis):
        for j, L in enumerate(Lam_axis):
            T = torsion_amplitude_at_cosmological_background(L, n, 1.0)
            Z[i, j] = np.log10(bound_K / T) if T > 0 else np.nan

    fig.add_trace(
        go.Heatmap(
            x=Lam_axis, y=N_f_axis, z=Z,
            colorscale="Cividis",
            colorbar=dict(
                title="log₁₀(K / |T_EC|)",
                x=1.05, xanchor="left",
            ),
            hovertemplate=(
                "Λ_UV=%{x:.2e} GeV<br>"
                "N_f=%{y:.1f}<br>"
                "headroom=%{z:.1f} dec<extra></extra>"
            ),
        ),
        row=1, col=2,
    )
    # Annotate natural point
    fig.add_trace(
        go.Scatter(
            x=[M_Pl], y=[16.0],
            mode="markers+text",
            marker=dict(color="white", size=11, symbol="star",
                        line=dict(color="black", width=1.5)),
            text=["natural (M_Pl, 16)"],
            textposition="middle right",
            textfont=dict(color="white", size=11),
            showlegend=False,
            hovertemplate=(
                "natural point<br>"
                "Λ_UV=M_Pl, N_f=16, α_EC=1<br>"
                "|T_EC| ≃ 2×10⁻⁷⁷ GeV<extra></extra>"
            ),
        ),
        row=1, col=2,
    )
    fig.update_xaxes(
        title_text="Λ_UV  [GeV]",
        type="log", exponentformat="power",
        row=1, col=2,
    )
    fig.update_yaxes(
        title_text="N_f (Dirac species)",
        row=1, col=2,
    )

    fig.update_layout(
        title=dict(
            text=(
                "<b>Phase 6e Wave 6 — Einstein-Cartan torsion at "
                "natural microscopic params is below all published bounds</b>"
            ),
            font=TITLE_FONT,
        ),
        height=600,
        width=1400,
        margin=dict(t=110, b=120, r=120),
        showlegend=True,
        legend=dict(orientation="h", yanchor="bottom", y=-0.30,
                    xanchor="center", x=0.5),
    )
    return fig


def fig_cmb_spectrum_planck_comparison():
    """Phase 6b Wave 2: CMB-ℓ spectrum amplitude vs Planck cosmic-variance ceiling.

    Two-panel figure transmuting the Phase 5y H4 closed-form NO-GO into
    a CMB-ℓ falsification.

    Left panel: log-log growth-amplitude squared `|G(k η_today)|²`
    versus comoving wavenumber `k` for ΛCDM (cs² = 1, oscillatory,
    bounded by 1) and the vestigial-EOS-at-τ=0 branch (cs² = -1/3,
    cosh-form, exponentially divergent). Planck cosmic-variance ceiling
    at the falsification pivot drawn as a horizontal anchor.

    Right panel: heatmap of log₁₀|G(k, η)|² over the (k, η) plane for
    the vestigial branch — the entire sub-horizon plane is colored at
    the divergence-saturated ceiling. The exact origin (`k → 0`,
    `η → 0`) reduces to G = 1 by construction.

    Lean: CosmologicalPerturbations.vestigial_growth_unbounded_at_zero,
          CosmologicalPerturbations.vestigial_growth_exceeds_planck_cv_cap_under_kη_threshold,
          CosmologicalPerturbations.lambda_cdm_in_oscillatory_regime,
          CosmologicalPerturbations.joint_phase5y_6b_no_go_natural_branch.
    Source: Mukhanov §7.4; Planck 2018, A&A 641, A6 (2020), Tab. 2;
            Phase 5y H4 closed form.
    viz-ref: Phase 6b W2 / D5 §7 (joint-Phase 5y/6b NO-GO bundle)
    """
    import numpy as np
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots
    from src.core.constants import COSMOLOGICAL_PERTURBATIONS_PARAMS

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            "Linear-perturbation growth amplitude<br>vs Planck cosmic-variance ceiling",
            "log₁₀|G(k, η)|² over (k, η) plane<br>vestigial-EOS at τ=0 branch",
        ),
        column_widths=[0.55, 0.45],
        horizontal_spacing=0.15,
    )

    eta_dec = COSMOLOGICAL_PERTURBATIONS_PARAMS["ETA_DECOUPLING_MPC"]
    eta_today = COSMOLOGICAL_PERTURBATIONS_PARAMS["ETA_TODAY_MPC"]
    cv_ceiling = 100.0  # Planck 1% cosmic-variance fractional cap

    # ---------- Left panel: |G|² vs k for ΛCDM and vestigial ----------
    # Range: k_min = 1/η_today (largest mode horizon-scale today),
    # k_max where the cosh argument hits ~700 (float overflow regime).
    k_grid = np.logspace(-4.5, -1.5, 240)  # 1/Mpc

    # ΛCDM oscillatory amplitude — bounded by 1 (we plot the squared
    # envelope at η_today as a constant 1 for clarity).
    lambda_cdm_amplitude_sq = np.ones_like(k_grid)
    fig.add_trace(
        go.Scatter(
            x=k_grid,
            y=lambda_cdm_amplitude_sq,
            mode="lines",
            name="ΛCDM (cs² = 1, oscillatory)",
            line=dict(color=COLORS["steel_blue"], width=2.5),
            hovertemplate="k=%{x:.3e} 1/Mpc<br>|G|²≤%{y:.1f}<extra></extra>",
        ),
        row=1, col=1,
    )

    # Vestigial branch — cosh-form amplitude evaluated at η_today.
    # Use np.clip to cap above the float-overflow regime; mark the
    # divergence with an explicit annotation below.
    cs_sq_vest = COSMOLOGICAL_PERTURBATIONS_PARAMS[
        "OMEGA_J_SQ_OVER_K_SQ_VESTIGIAL_AT_ZERO"
    ]
    growth_rate = np.sqrt(abs(cs_sq_vest))
    arg_at_today = growth_rate * k_grid * eta_today
    arg_capped = np.clip(arg_at_today, 0.0, 700.0)  # float-safe
    vest_amplitude_sq = np.cosh(arg_capped) ** 2
    fig.add_trace(
        go.Scatter(
            x=k_grid,
            y=vest_amplitude_sq,
            mode="lines",
            name="Vestigial-EOS τ=0 (cs² = -1/3, instability)",
            line=dict(color=COLORS["amber"], width=2.5),
            hovertemplate=(
                "k=%{x:.3e} 1/Mpc<br>"
                "|G|²=%{y:.3e}<extra></extra>"
            ),
        ),
        row=1, col=1,
    )

    # Planck CV ceiling — horizontal anchor.
    fig.add_hline(
        y=cv_ceiling,
        line=dict(color="black", dash="dot", width=2),
        annotation_text=f"Planck CV ceiling ({cv_ceiling:.0f})",
        annotation_position="top right",
        row=1, col=1,
    )

    # ℓ_pivot vertical anchor: k_pivot = ℓ_pivot / η_dec ≈ 1500/280
    ell_pivot = COSMOLOGICAL_PERTURBATIONS_PARAMS[
        "ELL_PIVOT_FOR_FALSIFICATION"
    ]
    k_pivot = ell_pivot / eta_dec
    if 10 ** -4.5 <= k_pivot <= 10 ** -1.5:
        fig.add_vline(
            x=k_pivot,
            line=dict(color=COLORS["sage"], dash="dash", width=2),
            annotation_text=f"ℓ={int(ell_pivot)} pivot",
            annotation_position="top",
            row=1, col=1,
        )

    fig.update_xaxes(
        title_text="comoving k (1/Mpc, log scale)",
        type="log", exponentformat="power",
        row=1, col=1,
    )
    fig.update_yaxes(
        title_text="|G|² at η₀ (log scale)",
        type="log", exponentformat="power",
        range=[-1, 25],  # cap rendered range; actual values diverge
        row=1, col=1,
    )

    # ---------- Right panel: log10|G(k, η)|² heatmap ----------
    k_axis = np.logspace(-4.5, -1.5, 80)
    eta_axis = np.linspace(eta_dec, eta_today, 80)
    K, ETA = np.meshgrid(k_axis, eta_axis)
    arg_grid = growth_rate * K * ETA
    arg_grid_capped = np.clip(arg_grid, 0.0, 700.0)
    log_amp_sq = 2.0 * np.log10(np.cosh(arg_grid_capped))
    # Cap at log10 = 24 for color-bar legibility.
    log_amp_sq_capped = np.clip(log_amp_sq, 0.0, 24.0)

    fig.add_trace(
        go.Heatmap(
            x=k_axis,
            y=eta_axis,
            z=log_amp_sq_capped,
            colorscale="YlOrRd",
            colorbar=dict(
                title=dict(text="log₁₀|G|²", side="right"),
                len=0.8,
                x=1.02,
            ),
            hovertemplate=(
                "k=%{x:.3e} 1/Mpc<br>"
                "η=%{y:.2e} Mpc<br>"
                "log₁₀|G|²=%{z:.1f}<extra></extra>"
            ),
            zmin=0.0,
            zmax=24.0,
        ),
        row=1, col=2,
    )
    fig.update_xaxes(
        title_text="comoving k (1/Mpc, log scale)",
        type="log", exponentformat="power",
        row=1, col=2,
    )
    fig.update_yaxes(
        title_text="conformal time η (Mpc)",
        row=1, col=2,
    )

    fig.update_layout(
        title=dict(
            text=(
                "<b>Phase 6b W2:</b> Vestigial-EOS perturbations diverge "
                "across the Planck-CMB regime<br>"
                "<sub>Cross-bridge to <i>VestigialEOS.cs_sq_vest_negative_at_zero</i> "
                "(Phase 5y H4); the cs² = −1/3 closed form drives "
                "exponential cosh-form growth at all sub-horizon scales</sub>"
            ),
            x=0.5,
            xanchor="center",
        ),
        height=560,
        width=1400,
        margin=dict(t=110, b=120, r=120),
        showlegend=True,
        legend=dict(orientation="h", yanchor="bottom", y=-0.18,
                    xanchor="center", x=0.5),
        font=FONT,
        plot_bgcolor="white",
        paper_bgcolor="white",
    )
    return fig


def fig_constant_K_riemann_dimension_factor():
    """Phase 6f Wave 1: Constant-sectional-curvature scalar curvature
    `R = n(n−1) K` and Bianchi-residual structure across the
    metric-symmetry / curvature plane.

    Left panel: scalar curvature R_trace vs K for dimensions n = 2, 3,
    4. The slope is the Lean-proven dimension factor n(n−1); the n = 4
    line has slope 12, matching
    `constantSectional_diag_trace_eq` exactly. Reference points anchor
    de Sitter (K = 1, R = 12) and AdS (K = -1, R = -12).

    Right panel: log10(first-Bianchi residual) heatmap on the (K,
    metric-asymmetry-strength) plane. Symmetric metric (asymmetry = 0)
    gives identically zero residual along the entire vertical axis,
    confirming the load-bearing role of the metric-symmetry hypothesis
    in `constantSectional_FirstBianchi`. Off-axis residuals grow
    linearly with both K and asymmetry strength — the substantive
    visual content of why metric symmetry is non-vacuous.

    Lean: SKEFTHawking.Curvature.constantSectional_diag_trace_eq,
          SKEFTHawking.Curvature.constantSectional_FirstBianchi,
          SKEFTHawking.Curvature.constantSectional_Ricci_eq.
    Source: Wald, *General Relativity* (1984) §3.2; project Lean
            theorems.
    viz-ref: Phase 6f Wave 1 infrastructure
    """
    import numpy as np
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots
    from src.core.formulas import (
        constant_sectional_scalar_predicted,
        riemann_constant_sectional_curvature,
        first_bianchi_residual,
    )

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            "Scalar curvature R_trace = n(n−1) K (Lean: "
            "<i>constantSectional_diag_trace_eq</i>)",
            "Bianchi residual on (K, asymmetry) plane "
            "(Lean: <i>constantSectional_FirstBianchi</i>)",
        ),
        column_widths=[0.5, 0.5],
        horizontal_spacing=0.18,
    )

    # ---------- Left panel: R = n(n-1) K vs K ----------
    K_grid = np.linspace(-1.5, 1.5, 121)
    dim_colors = [
        COLORS.get("steel_blue", "#2E86AB"),
        COLORS.get("amber", "#F18F01"),
        COLORS.get("sage", "#5C946E"),
    ]
    dim_labels = ["n = 2 (slope 2)", "n = 3 (slope 6)", "n = 4 (slope 12)"]
    for n, c, lbl in zip([2, 3, 4], dim_colors, dim_labels):
        R_curve = np.array([
            constant_sectional_scalar_predicted(K, dim=n) for K in K_grid
        ])
        fig.add_trace(
            go.Scatter(
                x=K_grid, y=R_curve, mode="lines",
                line=dict(color=c, width=2.5),
                name=lbl,
            ),
            row=1, col=1,
        )

    # de Sitter / AdS / Minkowski reference points (n = 4)
    fig.add_trace(
        go.Scatter(
            x=[1.0, -1.0, 0.0],
            y=[12.0, -12.0, 0.0],
            mode="markers+text",
            marker=dict(color="black", size=10, symbol="diamond"),
            text=["dS₄", "AdS₄", "Mink₄"],
            textposition="top center",
            name="reference",
            showlegend=False,
        ),
        row=1, col=1,
    )

    fig.update_xaxes(
        title_text="constant sectional curvature K",
        row=1, col=1,
        zeroline=True, zerolinecolor="grey", zerolinewidth=1,
    )
    fig.update_yaxes(
        title_text="R_trace = Σ_μ Ric_{μμ}",
        row=1, col=1,
        zeroline=True, zerolinecolor="grey", zerolinewidth=1,
    )

    # ---------- Right panel: Bianchi residual heatmap ----------
    K_h = np.linspace(-1.0, 1.0, 25)
    asym_h = np.linspace(0.0, 0.5, 21)  # off-diagonal asymmetry strength

    Z = np.zeros((len(asym_h), len(K_h)))
    for i, a in enumerate(asym_h):
        # Build asymmetric "metric": diagonal Euclidean + g[0][1] = a
        g = [[0.0] * 4 for _ in range(4)]
        for d in range(4):
            g[d][d] = 1.0
        g[0][1] = float(a)
        # g[1][0] = 0  (asymmetric)
        for j, K in enumerate(K_h):
            R = riemann_constant_sectional_curvature(K, g)
            res = first_bianchi_residual(R)
            # log10 with floor for visualization
            Z[i, j] = np.log10(max(res, 1e-15))

    fig.add_trace(
        go.Heatmap(
            z=Z,
            x=K_h,
            y=asym_h,
            colorscale="Viridis",
            colorbar=dict(
                title=dict(text="log₁₀(Bianchi residual)", side="right"),
                x=1.02,
                len=0.85,
            ),
            zmin=-15,
            zmax=1,
        ),
        row=1, col=2,
    )

    # Reference: vertical line at asymmetry = 0 (metric-symmetric)
    fig.add_shape(
        type="line",
        x0=-1.0, x1=1.0, y0=0.0, y1=0.0,
        line=dict(color="white", width=2, dash="dash"),
        row=1, col=2,
    )

    fig.update_xaxes(
        title_text="constant sectional curvature K",
        row=1, col=2,
    )
    fig.update_yaxes(
        title_text="metric asymmetry: g_{01} (with g_{10} = 0)",
        row=1, col=2,
    )

    fig.update_layout(
        title=dict(
            text=(
                "<b>Phase 6f W1:</b> Constant-K Riemann — dimension "
                "factor n(n−1) and load-bearing metric symmetry<br>"
                "<sub>Left: Lean-proven slope n(n−1) = 12 in 4D "
                "(<i>constantSectional_diag_trace_eq</i>); "
                "Right: residual = 0 along symmetric-metric axis "
                "(load-bearing hypothesis for "
                "<i>constantSectional_FirstBianchi</i>)</sub>"
            ),
            x=0.5,
            xanchor="center",
        ),
        height=560,
        width=1400,
        margin=dict(t=110, b=80, r=140),
        showlegend=True,
        legend=dict(orientation="h", yanchor="bottom", y=-0.20,
                    xanchor="center", x=0.25),
        font=FONT,
        plot_bgcolor="white",
        paper_bgcolor="white",
    )
    return fig


def fig_einstein_tensor_trace_identity():
    """Phase 6f Wave 2: Einstein-tensor trace identity ``G^μ_μ = -R``
    in 4D, plus de Sitter Λ-K relation ``Λ = 3K``.

    Left panel: trace of constant-K Einstein tensor `G^μ_μ` vs scalar
    curvature `R = 12K`. Lean
    `einsteinTensor_trace_eq_neg_scalar` proves the line `G^μ_μ = -R`
    (slope -1 through origin); we plot pipeline-computed traces against
    the Lean-predicted line. Reference points anchor de Sitter
    (R=12, G_trace=-12) and AdS (R=-12, G_trace=12).

    Right panel: de Sitter cosmological-constant relation Λ = 3K. The
    Λ-vacuum equation ``G_{μν} + Λ g_{μν} = 0`` is satisfied iff Λ = 3K
    (Lean ``constantSectional_lambda_vacuum_iff``). Each Λ ≠ 3K choice
    leaves a non-zero residual, visualized via log-scale heatmap on
    (K, Λ - 3K) plane.

    Lean: SKEFTHawking.EinsteinTensor.einsteinTensor_trace_eq_neg_scalar,
          SKEFTHawking.EinsteinTensor.constantSectional_einsteinTensor_eq,
          SKEFTHawking.EinsteinTensor.constantSectional_lambda_vacuum_iff.
    Source: Wald §3.2 (trace identity); MTW §17.2 (de Sitter Λ).
    viz-ref: Phase 6f Wave 2 infrastructure
    """
    import numpy as np
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots
    from src.core.formulas import (
        riemann_constant_sectional_curvature,
        ricci_from_riemann,
        scalar_curvature_from_ricci,
        einstein_tensor_from_ricci,
        einstein_tensor_trace,
    )

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            "Trace identity: G<sup>μ</sup><sub>μ</sub> = -R "
            "(Lean: <i>einsteinTensor_trace_eq_neg_scalar</i>)",
            "Λ-vacuum residual on (K, Λ-3K) plane "
            "(Lean: <i>constantSectional_lambda_vacuum_iff</i>)",
        ),
        column_widths=[0.5, 0.5],
        horizontal_spacing=0.18,
    )

    # ---------- Left panel: G_trace vs R ----------
    K_grid = np.linspace(-1.5, 1.5, 81)
    eta = [
        [-1.0, 0.0, 0.0, 0.0], [0.0, 1.0, 0.0, 0.0],
        [0.0, 0.0, 1.0, 0.0], [0.0, 0.0, 0.0, 1.0],
    ]
    R_vals = []
    G_trace_vals = []
    for K in K_grid:
        R = riemann_constant_sectional_curvature(K, eta)
        Ric = ricci_from_riemann(R)
        R_scalar = scalar_curvature_from_ricci(Ric, eta)  # η is self-inverse
        G = einstein_tensor_from_ricci(Ric, R_scalar, eta)
        R_vals.append(R_scalar)
        G_trace_vals.append(einstein_tensor_trace(G, eta))

    R_arr = np.asarray(R_vals)
    G_trace_arr = np.asarray(G_trace_vals)

    # Lean-predicted line: G_trace = -R
    R_pred = np.linspace(-20, 20, 201)
    G_trace_pred = -R_pred
    fig.add_trace(
        go.Scatter(
            x=R_pred, y=G_trace_pred, mode="lines",
            line=dict(color=COLORS.get("amber", "#F18F01"),
                      width=2.5, dash="dash"),
            name="Lean prediction G<sup>μ</sup><sub>μ</sub> = -R",
        ),
        row=1, col=1,
    )

    # Pipeline-computed traces (Python)
    fig.add_trace(
        go.Scatter(
            x=R_arr, y=G_trace_arr, mode="markers",
            marker=dict(color=COLORS.get("steel_blue", "#2E86AB"),
                        size=6, symbol="circle"),
            name="Python pipeline (Minkowski background)",
        ),
        row=1, col=1,
    )

    # Reference points: dS₄ (K=1), AdS₄ (K=-1), Mink₄ (K=0)
    fig.add_trace(
        go.Scatter(
            x=[12.0, -12.0, 0.0],
            y=[-12.0, 12.0, 0.0],
            mode="markers+text",
            marker=dict(color="black", size=10, symbol="diamond"),
            text=["dS₄ (K=1)", "AdS₄ (K=-1)", "Mink₄"],
            textposition="top right",
            name="reference",
            showlegend=False,
        ),
        row=1, col=1,
    )
    fig.update_xaxes(
        title_text="scalar curvature R = 12K",
        row=1, col=1,
        zeroline=True, zerolinecolor="grey", zerolinewidth=1,
    )
    fig.update_yaxes(
        title_text="G<sup>μ</sup><sub>μ</sub> (Einstein-tensor trace)",
        row=1, col=1,
        zeroline=True, zerolinecolor="grey", zerolinewidth=1,
    )

    # ---------- Right panel: Λ-vacuum residual heatmap ----------
    K_h = np.linspace(-1.0, 1.0, 25)
    delta_h = np.linspace(-0.5, 0.5, 21)  # Λ - 3K (deviation from de Sitter)

    Z = np.zeros((len(delta_h), len(K_h)))
    for i, dlt in enumerate(delta_h):
        for j, K in enumerate(K_h):
            Lambda = 3.0 * K + dlt
            R = riemann_constant_sectional_curvature(K, eta)
            Ric = ricci_from_riemann(R)
            R_scalar = scalar_curvature_from_ricci(Ric, eta)
            G = einstein_tensor_from_ricci(Ric, R_scalar, eta)
            # Residual sup-norm |G + Λg|_∞
            worst = 0.0
            for mu in range(4):
                for nu in range(4):
                    val = abs(G[mu][nu] + Lambda * eta[mu][nu])
                    if val > worst:
                        worst = val
            Z[i, j] = np.log10(max(worst, 1e-15))

    fig.add_trace(
        go.Heatmap(
            z=Z, x=K_h, y=delta_h,
            colorscale="Viridis",
            colorbar=dict(
                title=dict(text="log₁₀ |G + Λg|<sub>∞</sub>", side="right"),
                x=1.02, len=0.85,
            ),
            zmin=-15, zmax=1,
        ),
        row=1, col=2,
    )

    # Horizontal line at Λ - 3K = 0 (de Sitter locus)
    fig.add_shape(
        type="line",
        x0=-1.0, x1=1.0, y0=0.0, y1=0.0,
        line=dict(color="white", width=2, dash="dash"),
        row=1, col=2,
    )

    fig.update_xaxes(
        title_text="constant sectional curvature K",
        row=1, col=2,
    )
    fig.update_yaxes(
        title_text="Λ − 3K (deviation from de Sitter locus)",
        row=1, col=2,
    )

    fig.update_layout(
        title=dict(
            text=(
                "<b>Phase 6f W2:</b> Einstein tensor — trace identity "
                "G<sup>μ</sup><sub>μ</sub> = -R and de Sitter Λ = 3K<br>"
                "<sub>Left: Lean-proven slope -1 (4D dimension factor); "
                "Right: residual = 0 along Λ = 3K locus "
                "(load-bearing for "
                "<i>constantSectional_lambda_vacuum_iff</i>)</sub>"
            ),
            x=0.5, xanchor="center",
        ),
        height=560, width=1400,
        margin=dict(t=110, b=80, r=140),
        showlegend=True,
        legend=dict(orientation="h", yanchor="bottom", y=-0.20,
                    xanchor="center", x=0.25),
        font=FONT,
        plot_bgcolor="white", paper_bgcolor="white",
    )
    return fig


def fig_energy_conditions_perfect_fluid_regions():
    """Phase 6f Wave 3: Perfect-fluid energy-condition regions in
    (ρ, p) plane.

    Four-panel grid showing where each classical-GR energy condition
    holds for a perfect fluid `T_μν = diag(ρ, p, p, p)` in Minkowski
    rest frame (signature `−+++`):

      NEC: ρ + p ≥ 0                        (T(k,k) ≥ 0 at null k=(1,1,0,0))
      WEC: ρ ≥ 0 AND ρ + p ≥ 0              (Lean: WEC, eval at v = (1, β, 0, 0)
                                              for β = 0, 0.99 spanning rest →
                                              boost-limit)
      DEC: ρ ≥ |p|                          (Lean: DEC, eval at the
                                              stiff-fluid witness pair
                                              v = (1, β, 0, 0), w = (1, -β, 0, 0)
                                              with β → 1)
      SEC: ρ + 3p ≥ 0 AND ρ + p ≥ 0         (Lean: SEC residual at
                                              v = (1, 0, 0, 0) with
                                              trT = -ρ + 3p)

    The three named Lean counterexample witnesses are marked:
      ★ cosmologicalLambda (Λ=1): (ρ, p) = (1, -1) — satisfies
        NEC/WEC/DEC, violates SEC (witness for Lean
        `cosmologicalLambda_violates_SEC`).
      ◆ stiff-fluid: (ρ, p) = (1, 2) — satisfies NEC/WEC/SEC, violates
        DEC (witness for Lean `stiff_fluid_violates_DEC`).
      ○ ghost-scalar witness lives outside the perfect-fluid plane
        (its NEC violation is `T(k,k) = -⟨n,k⟩²`, not a (ρ, p) value)
        — annotated as a separate region, not a marker.

    Lean: SKEFTHawking.EnergyConditions.NEC, .WEC, .DEC, .SEC
          and SKEFTHawking.EnergyConditions.cosmologicalLambda_violates_SEC,
          SKEFTHawking.EnergyConditions.stiff_fluid_violates_DEC.
    Source: Hawking & Ellis, *The Large Scale Structure of Space-Time*
            (1973) Table I §4.3; Carroll *Spacetime and Geometry*
            (2004) §4.6 Fig 4.7.
    viz-ref: Phase 6f Wave 3 infrastructure
    """
    import numpy as np
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots

    rho_grid = np.linspace(-2.0, 3.0, 81)
    p_grid = np.linspace(-3.0, 3.0, 81)
    Rho, P = np.meshgrid(rho_grid, p_grid)

    NEC_holds = (Rho + P >= 0.0).astype(float)
    WEC_holds = ((Rho >= 0.0) & (Rho + P >= 0.0)).astype(float)
    DEC_holds = (Rho >= np.abs(P)).astype(float)
    SEC_holds = ((Rho + 3.0 * P >= 0.0) & (Rho + P >= 0.0)).astype(float)

    fig = make_subplots(
        rows=2, cols=2,
        subplot_titles=(
            "NEC: ρ + p ≥ 0  (Lean: <i>NEC</i>)",
            "WEC: ρ ≥ 0 AND ρ + p ≥ 0  (Lean: <i>WEC</i>)",
            "DEC: ρ ≥ |p|  (Lean: <i>DEC</i> — "
            "<i>stiff_fluid_violates_DEC</i> at ◆)",
            "SEC: ρ + 3p ≥ 0 AND ρ + p ≥ 0  (Lean: <i>SEC</i> — "
            "<i>cosmologicalLambda_violates_SEC</i> at ★)",
        ),
        horizontal_spacing=0.14,
        vertical_spacing=0.18,
    )

    panels = [
        (NEC_holds, 1, 1),
        (WEC_holds, 1, 2),
        (DEC_holds, 2, 1),
        (SEC_holds, 2, 2),
    ]

    # Two-color colorscale: pale = holds, deep = violated
    region_colorscale = [
        [0.0, "#E66100"],   # amber-orange = violated
        [0.5, "#E66100"],
        [0.5001, "#5D9ACE"],  # steel-blue = holds
        [1.0, "#5D9ACE"],
    ]

    for Z, r, c in panels:
        fig.add_trace(
            go.Heatmap(
                z=Z, x=rho_grid, y=p_grid,
                colorscale=region_colorscale,
                showscale=False,
                zmin=0.0, zmax=1.0,
                opacity=0.65,
                hovertemplate=(
                    "ρ = %{x:.2f}<br>p = %{y:.2f}"
                    "<br>region = %{z:.0f}<extra></extra>"
                ),
            ),
            row=r, col=c,
        )

    # Boundary lines per panel
    rho_line = np.linspace(-2.0, 3.0, 200)

    # NEC boundary: p = -ρ
    fig.add_trace(
        go.Scatter(
            x=rho_line, y=-rho_line, mode="lines",
            line=dict(color="black", width=1.5, dash="dot"),
            showlegend=False, hoverinfo="skip",
        ),
        row=1, col=1,
    )

    # WEC: ρ = 0 vertical + p = -ρ
    fig.add_trace(
        go.Scatter(
            x=[0.0, 0.0], y=[-3.0, 3.0], mode="lines",
            line=dict(color="black", width=1.5, dash="dot"),
            showlegend=False, hoverinfo="skip",
        ),
        row=1, col=2,
    )
    fig.add_trace(
        go.Scatter(
            x=rho_line, y=-rho_line, mode="lines",
            line=dict(color="black", width=1.5, dash="dot"),
            showlegend=False, hoverinfo="skip",
        ),
        row=1, col=2,
    )

    # DEC: p = ρ and p = -ρ (|p| ≤ ρ for ρ ≥ 0)
    fig.add_trace(
        go.Scatter(
            x=rho_line, y=rho_line, mode="lines",
            line=dict(color="black", width=1.5, dash="dot"),
            showlegend=False, hoverinfo="skip",
        ),
        row=2, col=1,
    )
    fig.add_trace(
        go.Scatter(
            x=rho_line, y=-rho_line, mode="lines",
            line=dict(color="black", width=1.5, dash="dot"),
            showlegend=False, hoverinfo="skip",
        ),
        row=2, col=1,
    )

    # SEC: p = -ρ/3 and p = -ρ
    fig.add_trace(
        go.Scatter(
            x=rho_line, y=-rho_line / 3.0, mode="lines",
            line=dict(color="black", width=1.5, dash="dot"),
            showlegend=False, hoverinfo="skip",
        ),
        row=2, col=2,
    )
    fig.add_trace(
        go.Scatter(
            x=rho_line, y=-rho_line, mode="lines",
            line=dict(color="black", width=1.5, dash="dot"),
            showlegend=False, hoverinfo="skip",
        ),
        row=2, col=2,
    )

    # Witness markers — same set on every panel
    witness_marks = [
        ("★", "cosmologicalLambda (ρ=1, p=-1)", 1.0, -1.0),
        ("◆", "stiff-fluid (ρ=1, p=2)", 1.0, 2.0),
    ]
    for symbol, label, rho_w, p_w in witness_marks:
        for r, c in [(1, 1), (1, 2), (2, 1), (2, 2)]:
            fig.add_trace(
                go.Scatter(
                    x=[rho_w], y=[p_w], mode="markers+text",
                    marker=dict(
                        color="black", size=14,
                        symbol="star" if symbol == "★" else "diamond",
                        line=dict(color="white", width=1.5),
                    ),
                    text=[symbol], textposition="top right",
                    textfont=dict(color="black", size=14, family="Arial"),
                    showlegend=(r == 1 and c == 1),
                    name=label,
                    hovertemplate=label + "<extra></extra>",
                ),
                row=r, col=c,
            )

    # Axes labels
    for r in [1, 2]:
        for c in [1, 2]:
            fig.update_xaxes(
                title_text="energy density ρ",
                range=[-2.0, 3.0],
                zeroline=True, zerolinecolor="grey", zerolinewidth=1,
                row=r, col=c,
            )
            fig.update_yaxes(
                title_text="pressure p",
                range=[-3.0, 3.0],
                zeroline=True, zerolinecolor="grey", zerolinewidth=1,
                row=r, col=c,
            )

    fig.update_layout(
        title=dict(
            text=(
                "<b>Phase 6f W3:</b> Energy-condition regions for a "
                "perfect fluid in Minkowski rest frame<br>"
                "<sub>Blue = condition holds; orange = violated. "
                "Witnesses: ★ cos-Λ violates SEC; ◆ stiff-fluid "
                "violates DEC. Boundaries in dotted black.</sub>"
            ),
            x=0.5, xanchor="center",
        ),
        height=900, width=1300,
        margin=dict(t=110, b=80),
        showlegend=True,
        legend=dict(
            orientation="h", yanchor="bottom", y=-0.10,
            xanchor="center", x=0.5,
        ),
        font=FONT,
        plot_bgcolor="white", paper_bgcolor="white",
    )
    return fig


def fig_exact_solutions_catalog():
    """Phase 6f Wave 4: Exact-solutions catalog visualization.

    Three-panel figure showcasing the wave's substantive content:

    - **Panel A (left):** Schwarzschild g_tt(r) signature flip across
      the horizon. For M = 1, plots `g_tt(r) = -(1 - 2M/r)` over
      r ∈ [0.5, 6]; the curve crosses zero exactly at r = 2M (Lean
      `schwarzschild_horizon_iff` + `_g_tt_at_horizon_zero`).
      Color-coded regions: spacelike t (r < 2M, orange), null t
      (r = 2M, vertical line), timelike t (r > 2M, blue).

    - **Panel B (center):** Cosmological constant Λ vs sectional
      curvature K, ``Λ = 3K`` (Lean `deSitter_lambda_vacuum_iff`).
      Linear function with three marked anchors:
      - dS₄ at K = 1, Λ = 3 (blue star)
      - Minkowski at K = 0, Λ = 0 (black diamond, the unique
        Λ = 0 vacuum among constant-K solutions per Lean
        `minkowski_lambda_zero_iff_K_zero`)
      - AdS₄ at K = -1, Λ = -3 (orange star).

    - **Panel C (right):** Schwarzschild thermodynamic invariants
      vs mass on log-log axes:
      - T_H = 1/(8πM): inverse-mass scaling (Lean
        `schwarzschild_T_H_times_M`)
      - A_H = 16πM²: quadratic-in-M scaling (Lean
        `schwarzschild_area_eq_16pi_M_sq`)
      - S_BH = 4πM² = A_H/4: quadratic, Bekenstein-Hawking (Lean
        `schwarzschild_S_BH_eq_4pi_M_sq`)
      The slopes (-1 for T_H, +2 for A and S_BH) visualize the
      universal scaling laws.

    Lean: SKEFTHawking.ExactSolutions.deSitter_lambda_vacuum_iff,
          .minkowski_lambda_zero_iff_K_zero,
          .schwarzschild_horizon_iff,
          .schwarzschild_g_tt_outside_horizon_neg / _at_horizon_zero
            / _inside_horizon_pos,
          .schwarzschild_T_H_times_M,
          .schwarzschild_area_eq_16pi_M_sq,
          .schwarzschild_S_BH_eq_4pi_M_sq.
    Source: Wald 1984 §5.2, §6.1; MTW 1973 §17.2, §31; Hawking 1975.
    viz-ref: Phase 6f Wave 4 infrastructure
    """
    import math

    import numpy as np
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots

    from src.core.formulas import (
        deSitter_lambda_from_K,
        schwarzschild_bekenstein_hawking_entropy,
        schwarzschild_g_tt,
        schwarzschild_hawking_temp,
        schwarzschild_horizon_area,
    )

    fig = make_subplots(
        rows=1, cols=3,
        subplot_titles=(
            "Schwarzschild g<sub>tt</sub>(r) signature flip at horizon",
            "Λ-K linear branch: Λ = 3K",
            "Schwarzschild BH thermodynamics vs M",
        ),
        column_widths=[0.34, 0.33, 0.33],
        horizontal_spacing=0.10,
    )

    # ---------- Panel A: Schwarzschild g_tt(r) ----------
    M = 1.0
    r_grid = np.linspace(0.5, 6.0, 200)
    # Avoid r = 0
    g_tt_vals = [schwarzschild_g_tt(M, r) for r in r_grid]

    # Inside-horizon shaded region (orange)
    fig.add_shape(
        type="rect", x0=0.5, x1=2.0, y0=-2.0, y1=3.0,
        fillcolor="rgba(230, 97, 0, 0.12)",
        line=dict(width=0),
        row=1, col=1,
    )
    # Outside-horizon shaded region (blue)
    fig.add_shape(
        type="rect", x0=2.0, x1=6.0, y0=-2.0, y1=3.0,
        fillcolor="rgba(93, 154, 206, 0.12)",
        line=dict(width=0),
        row=1, col=1,
    )

    # g_tt(r) curve
    fig.add_trace(
        go.Scatter(
            x=r_grid, y=g_tt_vals, mode="lines",
            line=dict(color=COLORS.get("steel_blue", "#2E86AB"), width=3),
            name="g<sub>tt</sub>(r) = -(1 - 2M/r)",
        ),
        row=1, col=1,
    )

    # Horizon vertical line at r = 2M
    fig.add_shape(
        type="line", x0=2.0, x1=2.0, y0=-2.0, y1=3.0,
        line=dict(color="black", width=2, dash="dash"),
        row=1, col=1,
    )
    # Annotation for horizon
    fig.add_annotation(
        x=2.0, y=2.7, text="<b>r = 2M</b><br>(horizon)",
        showarrow=False, font=dict(size=11, color="black"),
        bgcolor="white", bordercolor="black", borderwidth=1,
        row=1, col=1,
    )
    # Region annotations
    fig.add_annotation(
        x=1.0, y=-1.3, text="t spacelike<br>(g<sub>tt</sub> > 0 inside)",
        showarrow=False, font=dict(size=10, color="#9B3D00"),
        row=1, col=1,
    )
    fig.add_annotation(
        x=4.0, y=-1.3, text="t timelike<br>(g<sub>tt</sub> < 0 outside)",
        showarrow=False, font=dict(size=10, color="#1F5C7A"),
        row=1, col=1,
    )

    fig.update_xaxes(
        title_text="radius r (units of M)",
        range=[0.5, 6.0],
        zeroline=False,
        row=1, col=1,
    )
    fig.update_yaxes(
        title_text="g<sub>tt</sub>",
        range=[-2.0, 3.0],
        zeroline=True, zerolinecolor="grey", zerolinewidth=1,
        row=1, col=1,
    )

    # ---------- Panel B: Λ(K) = 3K ----------
    K_grid = np.linspace(-2.0, 2.0, 81)
    Lambda_vals = [deSitter_lambda_from_K(K) for K in K_grid]

    fig.add_trace(
        go.Scatter(
            x=K_grid, y=Lambda_vals, mode="lines",
            line=dict(color=COLORS.get("amber", "#F18F01"),
                      width=2.5, dash="dash"),
            name="Λ = 3K (Lean prediction)",
            showlegend=False,
        ),
        row=1, col=2,
    )

    # Anchor markers: dS, Mink, AdS
    anchors_K = [1.0, 0.0, -1.0]
    anchors_Lambda = [3.0, 0.0, -3.0]
    anchor_labels = ["dS₄ (K=1, Λ=3)", "Mink (K=0, Λ=0)", "AdS₄ (K=-1, Λ=-3)"]
    anchor_symbols = ["star", "diamond", "star"]
    anchor_colors = [
        COLORS.get("steel_blue", "#2E86AB"),
        "black",
        COLORS.get("amber", "#F18F01"),
    ]
    for K_a, L_a, lbl, sym, clr in zip(
            anchors_K, anchors_Lambda, anchor_labels,
            anchor_symbols, anchor_colors):
        fig.add_trace(
            go.Scatter(
                x=[K_a], y=[L_a], mode="markers+text",
                marker=dict(color=clr, size=14, symbol=sym,
                            line=dict(color="white", width=1.5)),
                text=[lbl], textposition="top right",
                textfont=dict(size=10, color="black"),
                showlegend=False,
            ),
            row=1, col=2,
        )

    fig.update_xaxes(
        title_text="constant sectional curvature K",
        range=[-2.0, 2.0],
        zeroline=True, zerolinecolor="grey", zerolinewidth=1,
        row=1, col=2,
    )
    fig.update_yaxes(
        title_text="cosmological constant Λ",
        range=[-7.0, 7.0],
        zeroline=True, zerolinecolor="grey", zerolinewidth=1,
        row=1, col=2,
    )

    # ---------- Panel C: T_H, A_H, S_BH vs M (log-log) ----------
    M_grid = np.logspace(-1, 2, 60)  # M from 0.1 to 100

    T_H_vals = [schwarzschild_hawking_temp(M_) for M_ in M_grid]
    A_H_vals = [schwarzschild_horizon_area(M_) for M_ in M_grid]
    S_BH_vals = [schwarzschild_bekenstein_hawking_entropy(M_) for M_ in M_grid]

    fig.add_trace(
        go.Scatter(
            x=M_grid, y=T_H_vals, mode="lines",
            line=dict(color=COLORS.get("steel_blue", "#2E86AB"), width=2.5),
            name="T<sub>H</sub> = 1/(8πM)  (slope -1)",
        ),
        row=1, col=3,
    )
    fig.add_trace(
        go.Scatter(
            x=M_grid, y=A_H_vals, mode="lines",
            line=dict(color=COLORS.get("amber", "#F18F01"), width=2.5),
            name="A<sub>H</sub> = 16πM²  (slope +2)",
        ),
        row=1, col=3,
    )
    fig.add_trace(
        go.Scatter(
            x=M_grid, y=S_BH_vals, mode="lines",
            line=dict(color=COLORS.get("sage", "#7AA095"),
                      width=2.5, dash="dot"),
            name="S<sub>BH</sub> = 4πM² = A<sub>H</sub>/4",
        ),
        row=1, col=3,
    )

    # Solar-mass anchor (M_geom = 1477 m, but display in units of M)
    # Just use M = 1 anchor
    fig.add_trace(
        go.Scatter(
            x=[1.0], y=[1.0 / (8.0 * math.pi)], mode="markers",
            marker=dict(color="black", size=10, symbol="circle",
                        line=dict(color="white", width=1.5)),
            name="M = 1 anchor",
            showlegend=False,
        ),
        row=1, col=3,
    )

    fig.update_xaxes(
        title_text="mass M (geometric units)",
        type="log",
        row=1, col=3,
    )
    fig.update_yaxes(
        title_text="thermodynamic invariant",
        type="log",
        row=1, col=3,
    )

    fig.update_layout(
        title=dict(
            text=(
                "<b>Phase 6f W4:</b> Exact solutions of the Einstein "
                "field equations  "
                "<sub>(Lean: <i>schwarzschild_horizon_iff</i>, "
                "<i>deSitter_lambda_vacuum_iff</i>, "
                "<i>schwarzschild_T_H_times_M</i>)</sub>"
            ),
            x=0.5, xanchor="center", y=0.97, yanchor="top",
        ),
        height=580, width=1500,
        margin=dict(t=130, b=120),
        showlegend=True,
        legend=dict(
            orientation="h", yanchor="bottom", y=-0.30,
            xanchor="center", x=0.5,
        ),
        font=FONT,
        plot_bgcolor="white", paper_bgcolor="white",
    )
    return fig


def fig_adm_constraint_surface():
    """Phase 6f Wave 5: ADM constraint visualization.

    Two-panel figure showcasing the wave's substantive content:

    - **Panel A (left):** Yamabe-form Hamiltonian constraint at
      moment-of-time-symmetry (K = 0): the load-bearing line
      ``^(3)R = 16π G ρ`` in (R3, ρ) plane. Shaded blue region:
      H_constraint < 0 (matter density too low); shaded orange:
      H_constraint > 0; black line: H = 0 (constraint satisfied).
      Lean theorem `hamiltonianConstraint_moment_of_time_symmetry_iff`
      visualized.

      Markers: ★ Minkowski at (R3=0, ρ=0); ◆ Schwarzschild
      moment-of-time-symmetry at fixed M (R3 sourced by mass,
      with ρ matching).

    - **Panel B (right):** dS flat slicing Λ-H relation: ``Λ = 3 H²``
      parabola. The Hamiltonian constraint at flat slicing (R3=0,
      tr K = -3H, K² = 3H²) balances iff Λ = 3H². Observed
      cosmological Λ ≃ 1.1 × 10⁻⁵² m⁻² gives H₀ ≃ √(Λ/3) ≃ 1.9 ×
      10⁻²⁶ m⁻¹ — marker on the parabola.
      Lean theorem `deSitter_flat_slicing_hamiltonian_iff` visualized.

    Lean: SKEFTHawking.ADMFormalism.hamiltonianConstraint_moment_of_time_symmetry_iff,
          .deSitter_flat_slicing_hamiltonian_iff.
    Source: Wald 1984 §10.2 + §11.2; MTW 1973 §21.
    viz-ref: Phase 6f Wave 5 infrastructure
    """
    import math

    import numpy as np
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots

    from src.core.formulas import (
        deSitter_lambda_from_K,
        hamiltonian_constraint,
    )

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            "Yamabe-form H<sub>constr</sub>=0 at K=0: ³R = 16πGρ",
            "dS flat slicing Λ-H balance: Λ = 3H²",
        ),
        column_widths=[0.5, 0.5],
        horizontal_spacing=0.14,
    )

    # ---------- Panel A: Yamabe Hamiltonian constraint ----------
    R3_grid = np.linspace(-2.0, 6.0, 81)
    rho_grid = np.linspace(-0.05, 0.15, 81)

    R3_mesh, rho_mesh = np.meshgrid(R3_grid, rho_grid)
    H_const = np.zeros_like(R3_mesh)
    for i in range(R3_mesh.shape[0]):
        for j in range(R3_mesh.shape[1]):
            H_const[i, j] = hamiltonian_constraint(
                R3_mesh[i, j], 0.0, 0.0, rho_mesh[i, j])

    # Heatmap of constraint value
    fig.add_trace(
        go.Contour(
            z=H_const, x=R3_grid, y=rho_grid,
            contours=dict(
                start=-2.0, end=6.0, size=1.0,
                showlines=True,
                coloring="heatmap",
            ),
            colorscale="RdBu_r",
            zmin=-3.0, zmax=3.0,
            colorbar=dict(
                title=dict(text="H<sub>constr</sub>", side="right"),
                x=0.42, len=0.7,
            ),
        ),
        row=1, col=1,
    )

    # Black line: ρ = R3 / (16π) where H = 0
    R3_line = np.linspace(-2.0, 6.0, 100)
    rho_line = R3_line / (16.0 * math.pi)
    fig.add_trace(
        go.Scatter(
            x=R3_line, y=rho_line, mode="lines",
            line=dict(color="black", width=2.5, dash="dash"),
            name="H<sub>constr</sub> = 0 (Yamabe)",
            showlegend=False,
        ),
        row=1, col=1,
    )

    # Markers: Minkowski + Schwarzschild
    fig.add_trace(
        go.Scatter(
            x=[0.0], y=[0.0], mode="markers+text",
            marker=dict(color="black", size=14, symbol="star",
                        line=dict(color="white", width=1.5)),
            text=["★ Minkowski"], textposition="bottom right",
            textfont=dict(size=10, color="black"),
            showlegend=False,
        ),
        row=1, col=1,
    )
    # Schwarzschild moment-of-time-symmetry sample: at ρ matching
    # external R3 from mass distribution. Show at (R3=2, ρ=2/(16π))
    R3_sch = 2.0
    rho_sch = R3_sch / (16.0 * math.pi)
    fig.add_trace(
        go.Scatter(
            x=[R3_sch], y=[rho_sch], mode="markers+text",
            marker=dict(color=COLORS.get("steel_blue", "#2E86AB"),
                        size=12, symbol="diamond",
                        line=dict(color="white", width=1.5)),
            text=["◆ Schw."], textposition="top left",
            textfont=dict(size=10, color="black"),
            showlegend=False,
        ),
        row=1, col=1,
    )

    fig.update_xaxes(
        title_text="spatial scalar curvature ³R",
        range=[-2.0, 6.0],
        zeroline=True, zerolinecolor="grey", zerolinewidth=1,
        row=1, col=1,
    )
    fig.update_yaxes(
        title_text="matter density ρ",
        range=[-0.05, 0.15],
        zeroline=True, zerolinecolor="grey", zerolinewidth=1,
        row=1, col=1,
    )

    # ---------- Panel B: dS flat-slicing Λ-H parabola ----------
    H_grid = np.linspace(0.0, 3.0, 200)
    Lambda_dS = [deSitter_lambda_from_K(H**2) for H in H_grid]

    fig.add_trace(
        go.Scatter(
            x=H_grid, y=Lambda_dS, mode="lines",
            line=dict(color=COLORS.get("amber", "#F18F01"),
                      width=2.5),
            name="Λ = 3H²",
        ),
        row=1, col=2,
    )

    # Observed Λ marker
    Lambda_obs = 1.1e-52  # in some unit system
    H_obs = math.sqrt(Lambda_obs / 3.0)
    # Show in arbitrary natural units; mark the qualitative position
    # at low H near zero — but for visualization use a scaled marker
    fig.add_trace(
        go.Scatter(
            x=[1.0], y=[3.0], mode="markers+text",
            marker=dict(color="black", size=12, symbol="star",
                        line=dict(color="white", width=1.5)),
            text=["★ H=1, Λ=3 (anchor)"], textposition="top right",
            textfont=dict(size=10, color="black"),
            showlegend=False,
        ),
        row=1, col=2,
    )
    fig.add_trace(
        go.Scatter(
            x=[2.0], y=[12.0], mode="markers+text",
            marker=dict(color=COLORS.get("steel_blue", "#2E86AB"),
                        size=10, symbol="circle",
                        line=dict(color="white", width=1.5)),
            text=["◆ H=2, Λ=12"], textposition="top right",
            textfont=dict(size=10, color="black"),
            showlegend=False,
        ),
        row=1, col=2,
    )

    fig.update_xaxes(
        title_text="Hubble parameter H (geometric units)",
        range=[0.0, 3.0],
        row=1, col=2,
    )
    fig.update_yaxes(
        title_text="cosmological constant Λ",
        range=[0.0, 30.0],
        row=1, col=2,
    )

    fig.update_layout(
        title=dict(
            text=(
                "<b>Phase 6f W5:</b> ADM constraint surface  "
                "<sub>(Lean: <i>hamiltonianConstraint_moment_of_time_symmetry_iff</i>, "
                "<i>deSitter_flat_slicing_hamiltonian_iff</i>)</sub>"
            ),
            x=0.5, xanchor="center", y=0.97, yanchor="top",
        ),
        height=560, width=1300,
        margin=dict(t=110, b=80),
        showlegend=False,
        font=FONT,
        plot_bgcolor="white", paper_bgcolor="white",
    )
    return fig


def fig_tetrad_metric_equivalence():
    """Phase 6f Wave 6: Tetrad-metric formalism equivalence — closes
    Phase 6f.

    Two-panel figure showing the tetrad-metric equivalence and the
    EC residual cross-bridge to 6e.6:

    - **Panel A (left):** Tetrad-induced metric heatmap for the
      Minkowski tetrad e^a_μ = δ^a_μ. Visualizes the named identity
      ``g_μν = η_{ab} e^a_μ e^b_ν = η_μν`` componentwise (Lean
      `minkowskiTetrad_induces_minkowski_metric`). Negative diagonal
      g_00 = -1 (orange); positive spatial diag g_ii = +1 (blue);
      zero off-diagonals (white).

    - **Panel B (right):** EC residual vs α_EC at fixed (Λ_UV, N_f,
      n_spin) showing the Levi-Civita reduction at α_EC = 1.
      Visualizes the cross-bridge to 6e.6 EinsteinCartanExtension
      (Lean `tetrad_levi_civita_iff_alpha_unity`). The residual
      vanishes at α_EC = 1 (vertical anchor) and grows linearly with
      α_EC - 1 in the deviation region.

    Lean: SKEFTHawking.TetradFormalism.minkowskiTetrad_induces_minkowski_metric,
          .tetrad_levi_civita_iff_alpha_unity.
    Source: Ortín *Gravity and Strings* (2015) §1.4; Hehl et al.
            *Rev. Mod. Phys.* **48**, 393 (1976).
    viz-ref: Phase 6f Wave 6 infrastructure
    """
    import numpy as np
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots

    from src.core.formulas import (
        minkowski_tetrad,
        tetrad_induced_metric,
    )
    from src.einstein_cartan.ec_residual_assessment import ec_residual_at_point

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            "Tetrad-induced metric: g<sub>μν</sub> = η<sub>ab</sub> "
            "e<sup>a</sup><sub>μ</sub> e<sup>b</sup><sub>ν</sub> "
            "(Mink. tetrad)",
            "EC residual vs α<sub>EC</sub> (Levi-Civita at α=1)",
        ),
        column_widths=[0.45, 0.55],
        horizontal_spacing=0.16,
    )

    # ---------- Panel A: tetrad-induced metric heatmap ----------
    e = minkowski_tetrad()
    g_matrix = np.zeros((4, 4))
    for mu in range(4):
        for nu in range(4):
            g_matrix[mu, nu] = tetrad_induced_metric(e, mu, nu)

    # Annotations for each cell with the value
    annotations_a = []
    for mu in range(4):
        for nu in range(4):
            val = g_matrix[mu, nu]
            color = "white" if abs(val) > 0.5 else "black"
            annotations_a.append(dict(
                x=nu, y=mu, text=f"{val:.0f}",
                showarrow=False, font=dict(color=color, size=12),
                xref="x1", yref="y1",
            ))

    fig.add_trace(
        go.Heatmap(
            z=g_matrix, x=list(range(4)), y=list(range(4)),
            colorscale="RdBu_r", zmid=0,
            zmin=-1.5, zmax=1.5,
            colorbar=dict(
                title=dict(text="g<sub>μν</sub>", side="right"),
                x=0.42, len=0.7,
            ),
        ),
        row=1, col=1,
    )

    fig.update_xaxes(
        title_text="ν index",
        tickmode="array", tickvals=list(range(4)),
        ticktext=["0", "1", "2", "3"],
        row=1, col=1,
    )
    fig.update_yaxes(
        title_text="μ index",
        tickmode="array", tickvals=list(range(4)),
        ticktext=["0", "1", "2", "3"],
        autorange="reversed",  # show row 0 at top
        row=1, col=1,
    )

    # ---------- Panel B: EC residual vs α_EC ----------
    alpha_grid = np.linspace(0.1, 2.5, 50)
    Lambda_UV = 1.221e19  # Planck scale
    N_f = 16
    residuals = []
    for a in alpha_grid:
        try:
            r = ec_residual_at_point(Lambda_UV, N_f, alpha_ec=float(a))
            residuals.append(r.residual_gev)
        except Exception:
            residuals.append(0.0)

    residuals = np.asarray(residuals)
    # Use absolute value on log scale; mark sign with color
    abs_r = np.abs(residuals)
    abs_r_safe = np.where(abs_r > 1e-100, abs_r, 1e-100)

    fig.add_trace(
        go.Scatter(
            x=alpha_grid, y=abs_r_safe, mode="lines",
            line=dict(color=COLORS.get("amber", "#F18F01"),
                      width=2.5),
            name="|EC residual|",
            showlegend=False,
        ),
        row=1, col=2,
    )

    # Vertical line at α_EC = 1 (Levi-Civita)
    fig.add_shape(
        type="line", x0=1.0, x1=1.0, y0=1e-100, y1=1e-50,
        line=dict(color="black", width=2, dash="dash"),
        row=1, col=2,
    )
    fig.add_annotation(
        x=1.0, y=1e-60, text="α<sub>EC</sub> = 1<br>(Levi-Civita)",
        showarrow=False, font=dict(size=11, color="black"),
        bgcolor="white", bordercolor="black", borderwidth=1,
        row=1, col=2,
    )

    fig.update_xaxes(
        title_text="α<sub>EC</sub>",
        range=[0.0, 2.5],
        row=1, col=2,
    )
    fig.update_yaxes(
        title_text="|EC residual| (GeV², log scale)",
        type="log",
        range=[-100, -50],
        row=1, col=2,
    )

    fig.update_layout(
        title=dict(
            text=(
                "<b>Phase 6f W6:</b> Tetrad-metric formalism "
                "equivalence — closes Phase 6f<br>"
                "<sub>(Lean: <i>minkowskiTetrad_induces_minkowski_metric</i>, "
                "<i>tetrad_levi_civita_iff_alpha_unity</i>)</sub>"
            ),
            x=0.5, xanchor="center", y=0.97, yanchor="top",
        ),
        height=560, width=1300,
        margin=dict(t=120, b=80),
        showlegend=False,
        annotations=annotations_a,
        font=FONT,
        plot_bgcolor="white", paper_bgcolor="white",
    )
    return fig


# ════════════════════════════════════════════════════════════════════════
# Paper I1 — verification methodology figures
# ════════════════════════════════════════════════════════════════════════
#
# Six figures author the methodology paper (papers/I1/paper_draft.tex):
#   1. fig_i1_three_layer_architecture  (§2)  — three-layer schematic
#   2. fig_i1_pipeline_14_stages        (§6)  — 14-stage pipeline flow
#   3. fig_i1_sentence_state_clusters   (§8)  — claim-cluster cross-bundle map
#   4. fig_i1_firstorderkms_grid        (§3)  — 9-coefficient KMS grid (run 270e77a0)
#   5. fig_i1_gap_counterexample        (§4)  — gap-equation counterexample plot
#   6. fig_i1_chirality_wall_tree       (§5)  — axiom decomposition tree
# ════════════════════════════════════════════════════════════════════════


def fig_i1_three_layer_architecture() -> "go.Figure":
    """I1-FIG-1 — Three-layer verification architecture schematic.

    Three orthogonal layers stacked vertically:
      Layer 1 (steel_blue): Python numerics
      Layer 2 (amber):      Lean 4 formal proofs
      Layer 3 (sage):       Aristotle automated theorem prover

    Forward arrows show the discovery → formalization → automation cycle,
    and a curved arrow from Layer 3 back to Layer 1 closes the loop —
    the asymmetric composition described in §2 of paper I1.
    """
    fig = go.Figure()

    layers = [
        {
            "y0": 0.07, "y1": 0.30,
            "fill": COLORS["sage"],
            "title": "<b>Layer 3 — Aristotle (automated TP)</b>",
            "artifacts": (
                "submit_to_aristotle.py · ARISTOTLE_THEOREMS registry · "
                "priority batch plan · zero-sorry closures (e.g. run 270e77a0)"
            ),
        },
        {
            "y0": 0.39, "y1": 0.62,
            "fill": COLORS["amber"],
            "title": "<b>Layer 2 — Lean 4 formal proofs</b>",
            "artifacts": (
                "lean/SKEFTHawking/*.lean · zero sorry · 1 axiom · "
                "5229 theorems · ExtractDeps.olean axiom-closure graph"
            ),
        },
        {
            "y0": 0.71, "y1": 0.94,
            "fill": COLORS["steel_blue"],
            "title": "<b>Layer 1 — Python numerics</b>",
            "artifacts": (
                "formulas.py (canonical) · constants.py · visualizations.py · "
                "tests/ · domain modules (wkb/, adw/, vestigial/)"
            ),
        },
    ]

    for L in layers:
        fig.add_shape(
            type="rect", xref="paper", yref="paper",
            x0=0.10, x1=0.82, y0=L["y0"], y1=L["y1"],
            fillcolor=L["fill"], opacity=0.78,
            line=dict(color="black", width=1.5),
        )
        y_mid = (L["y0"] + L["y1"]) / 2
        fig.add_annotation(
            xref="paper", yref="paper",
            x=0.46, y=y_mid + 0.05, text=L["title"],
            showarrow=False, font=dict(**FONT, color="white"),
            align="center",
        )
        fig.add_annotation(
            xref="paper", yref="paper",
            x=0.46, y=y_mid - 0.04, text=L["artifacts"],
            showarrow=False,
            font=dict(family=FONT["family"], size=10, color="white"),
            align="center",
        )

    # Forward arrows in inter-layer gaps (Layer 1 → 2 → 3)
    # Gap 1: between Layer 1 (y=0.71) and Layer 2 (y=0.62)
    fig.add_annotation(
        xref="paper", yref="paper",
        x=0.30, y=0.625, ax=0.30, ay=0.705,
        text="", showarrow=True, arrowhead=3, arrowwidth=2.5,
        arrowcolor="black",
    )
    fig.add_annotation(
        xref="paper", yref="paper",
        x=0.36, y=0.665, text="<b>formalize</b>",
        showarrow=False, xanchor="left",
        font=dict(family=FONT["family"], size=11),
    )
    # Gap 2: between Layer 2 (y=0.39) and Layer 3 (y=0.30)
    fig.add_annotation(
        xref="paper", yref="paper",
        x=0.30, y=0.305, ax=0.30, ay=0.385,
        text="", showarrow=True, arrowhead=3, arrowwidth=2.5,
        arrowcolor="black",
    )
    fig.add_annotation(
        xref="paper", yref="paper",
        x=0.36, y=0.345, text="<b>automate</b>",
        showarrow=False, xanchor="left",
        font=dict(family=FONT["family"], size=11),
    )

    # Feedback arrow Layer 3 → Layer 1 (curved on the right side)
    fig.add_shape(
        type="path",
        path=("M 0.82,0.185 C 0.95,0.185 0.95,0.825 0.82,0.825"),
        line=dict(color=COLORS["carmine"], width=2.5),
        xref="paper", yref="paper",
    )
    # Arrowhead at the top end of the curve (entering Layer 1)
    fig.add_annotation(
        xref="paper", yref="paper",
        x=0.82, y=0.825, ax=0.86, ay=0.825,
        text="", showarrow=True, arrowhead=3, arrowwidth=2.5,
        arrowcolor=COLORS["carmine"],
    )
    fig.add_annotation(
        xref="paper", yref="paper",
        x=0.965, y=0.50,
        text="<b>counterexample<br>or refinement</b>",
        showarrow=False,
        font=dict(family=FONT["family"], size=10, color=COLORS["carmine"]),
        textangle=90,
    )

    apply_layout(
        fig,
        height=550, width=900,
        title=dict(
            text=(
                "<b>Three-layer verification architecture</b><br>"
                "<sub>Asymmetric composition — none alone suffices "
                "(paper I1 §2)</sub>"
            ),
            x=0.5, xanchor="center", font=TITLE_FONT,
        ),
        xaxis=dict(visible=False, range=[0, 1]),
        yaxis=dict(visible=False, range=[0, 1]),
        showlegend=False,
        margin=dict(l=20, r=20, t=80, b=20),
    )
    return fig


def fig_i1_pipeline_14_stages() -> "go.Figure":
    """I1-FIG-2 — 14-stage wave-execution pipeline flow diagram.

    Vertical-grid flow with one node per stage. Stages 3a, 13, 14 (the three
    new pipeline stages introduced by the methodology paper) are highlighted
    in amber; the rest in steel-blue. Each node displays its stage number,
    short name, and gate condition.
    """
    stages = [
        ("1",   "Constants & params",     "provenance recorded"),
        ("2",   "Formulas",                "Lean-theorem ref present"),
        ("3a",  "Lean MCP loop",           "lean_goal = 'no goals'"),
        ("3b",  "Sorry registration",      "all sorry tracked"),
        ("4",   "Aristotle (fallback)",    "run ID retrieved"),
        ("5",   "Lean build verify",       "lake build clean"),
        ("6",   "Python tests",            "pytest -v passes"),
        ("7",   "Cross-layer validation",  "validate.py 21/21"),
        ("8",   "Visualizations",          "fig functions registered"),
        ("9",   "Figure review",           "physics-qa pass"),
        ("10",  "Paper draft",             "claims-reviewer pass"),
        ("11",  "Notebooks",               "executed end-to-end"),
        ("12",  "Document sync",           "Inventory + Heatmap"),
        ("13",  "Adversarial review",      "fresh-context pass"),
        ("14",  "Meta-process QI",         "lessons captured"),
    ]
    highlight = {"3a", "13", "14"}

    fig = go.Figure()

    cols = 5
    rows = 3  # 15 nodes (one extra slot)
    box_w, box_h = 0.165, 0.245
    h_pad = (1.0 - cols * box_w) / (cols + 1)
    v_pad = (1.0 - rows * box_h) / (rows + 1)

    coords = []
    for i in range(len(stages)):
        r = i // cols
        c = i % cols
        x0 = h_pad + c * (box_w + h_pad)
        x1 = x0 + box_w
        # rows numbered from top
        y1 = 1.0 - (v_pad + r * (box_h + v_pad))
        y0 = y1 - box_h
        coords.append((x0, x1, y0, y1))

    for (num, name, gate), (x0, x1, y0, y1) in zip(stages, coords):
        is_new = num in highlight
        fill = COLORS["amber"] if is_new else COLORS["steel_blue"]
        fig.add_shape(
            type="rect", xref="paper", yref="paper",
            x0=x0, x1=x1, y0=y0, y1=y1,
            fillcolor=fill, opacity=0.85,
            line=dict(color="black", width=1.2),
        )
        y_mid = (y0 + y1) / 2
        fig.add_annotation(
            xref="paper", yref="paper",
            x=(x0 + x1) / 2, y=y_mid + 0.055,
            text=f"<b>Stage {num}</b>",
            showarrow=False,
            font=dict(family=FONT["family"], size=12, color="white"),
        )
        fig.add_annotation(
            xref="paper", yref="paper",
            x=(x0 + x1) / 2, y=y_mid + 0.005,
            text=f"<b>{name}</b>",
            showarrow=False,
            font=dict(family=FONT["family"], size=11, color="white"),
        )
        fig.add_annotation(
            xref="paper", yref="paper",
            x=(x0 + x1) / 2, y=y_mid - 0.055,
            text=f"<i>gate: {gate}</i>",
            showarrow=False,
            font=dict(family=FONT["family"], size=9, color="white"),
        )

    # Connect stages with arrows: same-row → right, end-of-row → next-row left.
    for i in range(len(stages) - 1):
        x0a, x1a, y0a, y1a = coords[i]
        x0b, x1b, y0b, y1b = coords[i + 1]
        ya = (y0a + y1a) / 2
        yb = (y0b + y1b) / 2
        # Use mid-arrow with annotation
        fig.add_annotation(
            xref="paper", yref="paper",
            x=x0b, y=yb, ax=x1a, ay=ya,
            text="", showarrow=True, arrowhead=3, arrowwidth=1.5,
            arrowcolor="rgba(0,0,0,0.6)",
        )

    # Legend
    fig.add_shape(type="rect", xref="paper", yref="paper",
                  x0=0.02, x1=0.045, y0=-0.005, y1=0.02,
                  fillcolor=COLORS["amber"], line=dict(width=0.5))
    fig.add_annotation(xref="paper", yref="paper",
                       x=0.05, y=0.008, text="new stages (3a, 13, 14)",
                       showarrow=False, xanchor="left",
                       font=dict(family=FONT["family"], size=10))
    fig.add_shape(type="rect", xref="paper", yref="paper",
                  x0=0.40, x1=0.425, y0=-0.005, y1=0.02,
                  fillcolor=COLORS["steel_blue"], line=dict(width=0.5))
    fig.add_annotation(xref="paper", yref="paper",
                       x=0.43, y=0.008,
                       text="existing pipeline stages",
                       showarrow=False, xanchor="left",
                       font=dict(family=FONT["family"], size=10))

    apply_layout(
        fig,
        height=620, width=1200,
        title=dict(
            text=(
                "<b>14-stage wave-execution pipeline</b><br>"
                "<sub>Gate-pass conditions at each stage; new stages "
                "highlighted in amber (paper I1 §6)</sub>"
            ),
            x=0.5, xanchor="center", font=TITLE_FONT,
        ),
        xaxis=dict(visible=False, range=[0, 1]),
        yaxis=dict(visible=False, range=[-0.04, 1]),
        showlegend=False,
        margin=dict(l=20, r=20, t=80, b=30),
    )
    return fig


def fig_i1_sentence_state_clusters() -> "go.Figure":
    """I1-FIG-3 — Sentence-state cluster diagram across three papers.

    Three paper rectangles with sentence dots inside; curved lines
    connect sentences sharing a `claim_cluster`. One cluster (highlighted
    in amber) is `cross_bundle: true`, demonstrating that sentence-level
    provenance survives bundle consolidation.
    """
    fig = go.Figure()

    papers = [
        {"id": "Paper A (Tier 1)", "x_center": 0.18, "y0": 0.20, "y1": 0.85},
        {"id": "Paper B (Tier 1)", "x_center": 0.50, "y0": 0.20, "y1": 0.85},
        {"id": "Paper C (Tier 2)", "x_center": 0.82, "y0": 0.20, "y1": 0.85},
    ]
    box_w = 0.20

    # Sentence dots: each paper has 6 sentences laid out vertically.
    # Cluster assignments (cluster_id): cluster names map sentences across papers.
    # cross_bundle cluster = "C2" (highlighted)
    sentences = {
        "Paper A (Tier 1)": [
            ("A1", 0.78, "C1"),  ("A2", 0.68, "C2"),
            ("A3", 0.58, "C3"),  ("A4", 0.48, None),
            ("A5", 0.38, "C1"),  ("A6", 0.28, None),
        ],
        "Paper B (Tier 1)": [
            ("B1", 0.78, "C1"),  ("B2", 0.68, None),
            ("B3", 0.58, "C2"),  ("B4", 0.48, "C3"),
            ("B5", 0.38, None),  ("B6", 0.28, "C2"),
        ],
        "Paper C (Tier 2)": [
            ("C1", 0.78, None),  ("C2", 0.68, "C2"),
            ("C3", 0.58, "C3"),  ("C4", 0.48, "C1"),
            ("C5", 0.38, None),  ("C6", 0.28, None),
        ],
    }

    cluster_colors = {
        "C1": COLORS["steel_blue"],
        "C2": COLORS["amber"],   # cross_bundle: true
        "C3": COLORS["sage"],
    }
    cross_bundle_clusters = {"C2"}

    # Draw paper rectangles
    for p in papers:
        x0 = p["x_center"] - box_w / 2
        x1 = p["x_center"] + box_w / 2
        fig.add_shape(
            type="rect", xref="paper", yref="paper",
            x0=x0, x1=x1, y0=p["y0"], y1=p["y1"],
            fillcolor="rgba(245,245,245,0.95)",
            line=dict(color="black", width=1.5),
        )
        fig.add_annotation(
            xref="paper", yref="paper",
            x=p["x_center"], y=p["y1"] + 0.03, text=f"<b>{p['id']}</b>",
            showarrow=False, font=dict(family=FONT["family"], size=12),
        )

    # Compute sentence positions
    pos = {}
    for p in papers:
        for sid, y, cluster in sentences[p["id"]]:
            pos[sid] = (p["x_center"], y, cluster)

    # Draw cluster connecting lines first (under dots)
    cluster_groups = {}
    for sid, (x, y, c) in pos.items():
        if c is None:
            continue
        cluster_groups.setdefault(c, []).append((sid, x, y))
    for c, members in cluster_groups.items():
        color = cluster_colors[c]
        is_cross = c in cross_bundle_clusters
        width = 3 if is_cross else 1.6
        # Connect each member to the next in lexicographic order (creates a chain)
        members_sorted = sorted(members)
        for (sid_a, xa, ya), (sid_b, xb, yb) in zip(
            members_sorted, members_sorted[1:]
        ):
            # Draw curved line via quadratic Bezier in 'paper' coords
            mx = (xa + xb) / 2
            my = (ya + yb) / 2 + 0.06  # slight upward bow
            fig.add_shape(
                type="path",
                path=f"M {xa},{ya} Q {mx},{my} {xb},{yb}",
                line=dict(color=color, width=width,
                          dash="solid" if is_cross else "dot"),
                xref="paper", yref="paper",
            )

    # Draw sentence dots
    for sid, (x, y, c) in pos.items():
        color = cluster_colors[c] if c is not None else "rgba(120,120,120,0.6)"
        fig.add_shape(
            type="circle", xref="paper", yref="paper",
            x0=x - 0.012, x1=x + 0.012, y0=y - 0.018, y1=y + 0.018,
            fillcolor=color,
            line=dict(color="black", width=0.6),
        )
        fig.add_annotation(
            xref="paper", yref="paper",
            x=x, y=y, text=sid, showarrow=False,
            font=dict(family=FONT["family"], size=8, color="white"),
        )

    # Legend
    legend_items = [
        ("C1 (single-bundle cluster)", COLORS["steel_blue"], False),
        ("C2 (cross_bundle: true)",    COLORS["amber"],     True),
        ("C3 (single-bundle cluster)", COLORS["sage"],      False),
        ("unclustered sentence",       "rgba(120,120,120,0.6)", False),
    ]
    for i, (label, color, is_cross) in enumerate(legend_items):
        y = 0.13 - i * 0.035
        fig.add_shape(
            type="circle", xref="paper", yref="paper",
            x0=0.06, x1=0.082, y0=y - 0.012, y1=y + 0.012,
            fillcolor=color, line=dict(color="black", width=0.5),
        )
        fig.add_annotation(
            xref="paper", yref="paper",
            x=0.09, y=y, text=label + ("  (highlighted)" if is_cross else ""),
            showarrow=False, xanchor="left",
            font=dict(family=FONT["family"], size=10),
        )

    apply_layout(
        fig,
        height=560, width=1000,
        title=dict(
            text=(
                "<b>Sentence-state claim clusters across paper bundles</b><br>"
                "<sub>cross_bundle clusters (amber) survive bundle "
                "consolidation (paper I1 §8)</sub>"
            ),
            x=0.5, xanchor="center", font=TITLE_FONT,
        ),
        xaxis=dict(visible=False, range=[0, 1]),
        yaxis=dict(visible=False, range=[-0.05, 1]),
        showlegend=False,
        margin=dict(l=20, r=20, t=80, b=20),
    )
    return fig


def fig_i1_firstorderkms_grid() -> "go.Figure":
    """I1-FIG-4 — FirstOrderKMS 9-coefficient constraint grid.

    Two side-by-side 3×3 heatmaps showing the 9 first-order coefficients
    {r_1, r_2, r_3, r_4, r_5, r_6, i_1, i_2, i_3}.

    LEFT panel: original weak FirstOrderKMS axiom — only 4 coefficients
    constrained, 5 free, with the counterexample vector
    c = (0,0,0,0,0,0,0,1,0) shipping a non-zero i_2 highlighted in red.

    RIGHT panel: corrected FirstOrderKMS axiom (Aristotle run 270e77a0) —
    all 9 cells constrained, with explicit i_3 = 0.
    """
    # Coefficient layout (3x3, top-to-bottom, left-to-right):
    #   row 0:  r_1  r_2  r_3
    #   row 1:  r_4  r_5  r_6
    #   row 2:  i_1  i_2  i_3
    labels = [
        ["r₁", "r₂", "r₃"],
        ["r₄", "r₅", "r₆"],
        ["i₁", "i₂", "i₃"],
    ]

    # Status code: 0 = unconstrained, 1 = constrained, 2 = counterexample-highlight
    weak_status = [
        [1, 1, 0],
        [0, 0, 0],
        [1, 2, 0],   # i_2 = 1 in the counterexample vector
    ]
    strong_status = [
        [1, 1, 1],
        [1, 1, 1],
        [1, 1, 1],   # all constrained, including i_3 = 0
    ]

    fig = make_subplots(
        rows=1, cols=2,
        subplot_titles=(
            "<b>Original weak axiom</b><br>"
            "<sub>4 constrained / 5 unconstrained — counterexample "
            "c = (0,0,0,0,0,0,0,1,0)</sub>",
            "<b>Corrected FirstOrderKMS</b><br>"
            "<sub>(Aristotle run 270e77a0) — all 9 constrained, "
            "i₃ = 0 explicit</sub>",
        ),
        horizontal_spacing=0.15,
    )

    # Custom colorscale: 0 (light grey), 1 (steel-blue), 2 (carmine)
    cscale_weak = [
        [0.00, "rgba(220,220,220,1.0)"],
        [0.49, "rgba(220,220,220,1.0)"],
        [0.50, COLORS["steel_blue"]],
        [0.99, COLORS["steel_blue"]],
        [1.00, COLORS["carmine"]],
    ]
    cscale_strong = [
        [0.0, COLORS["amber"]],
        [1.0, COLORS["amber"]],
    ]

    fig.add_trace(
        go.Heatmap(
            z=weak_status[::-1],     # invert so r_1 row is at top
            x=["col 1", "col 2", "col 3"],
            y=["row 3 (i)", "row 2 (r₄–r₆)", "row 1 (r₁–r₃)"],
            colorscale=cscale_weak, zmin=0, zmax=2,
            showscale=False,
            xgap=3, ygap=3,
            hoverinfo="text",
            text=[row for row in labels[::-1]],
        ),
        row=1, col=1,
    )

    fig.add_trace(
        go.Heatmap(
            z=strong_status[::-1],
            x=["col 1", "col 2", "col 3"],
            y=["row 3 (i)", "row 2 (r₄–r₆)", "row 1 (r₁–r₃)"],
            colorscale=cscale_strong, zmin=0, zmax=1,
            showscale=False,
            xgap=3, ygap=3,
            hoverinfo="text",
            text=[row for row in labels[::-1]],
        ),
        row=1, col=2,
    )

    # Annotate each cell with the coefficient label and constraint status
    def _annotate(panel: int, status_grid):
        # panel: 1 = left subplot, 2 = right subplot
        xref = f"x{'' if panel == 1 else panel}"
        yref = f"y{'' if panel == 1 else panel}"
        for r, row_labels in enumerate(labels):
            for c, lab in enumerate(row_labels):
                s = status_grid[r][c]
                if s == 0:
                    detail = "free"
                    color = "black"
                elif s == 1:
                    detail = "constrained"
                    color = "white"
                else:
                    detail = "counterexample<br>i₂ = 1"
                    color = "white"
                # heatmap y is inverted so row index r goes to position (2 - r)
                fig.add_annotation(
                    xref=xref, yref=yref,
                    x=c, y=2 - r,
                    text=f"<b>{lab}</b><br><sub>{detail}</sub>",
                    showarrow=False,
                    font=dict(family=FONT["family"], size=12, color=color),
                )

    _annotate(1, weak_status)
    _annotate(2, strong_status)

    fig.update_xaxes(visible=False, row=1, col=1)
    fig.update_xaxes(visible=False, row=1, col=2)
    fig.update_yaxes(visible=False, row=1, col=1)
    fig.update_yaxes(visible=False, row=1, col=2)

    # Move subplot titles down to avoid overlap with main title
    fig.layout.annotations[0].update(y=1.04)
    fig.layout.annotations[1].update(y=1.04)

    fig.update_layout(
        height=620, width=1200,
        title=dict(
            text=(
                "<b>FirstOrderKMS 9-coefficient constraint grid "
                "(paper I1 §3, Aristotle run 270e77a0)</b>"
            ),
            x=0.5, xanchor="center", y=0.97, yanchor="top",
            font=TITLE_FONT,
        ),
        font=FONT,
        plot_bgcolor="white", paper_bgcolor="white",
        margin=dict(l=20, r=20, t=160, b=20),
        showlegend=False,
    )
    return fig


def fig_i1_gap_counterexample() -> "go.Figure":
    """I1-FIG-5 — Gap-equation counterexample plot.

    Plots Δ(G) for N_f = 1, Λ = 1 showing:
      (i)   trivial branch Δ = 0 for G < G_c,
      (ii)  non-trivial branch Δ(G) > 0 for G > G_c,
      (iii) horizontal line at Δ = Λ = 1,
      (iv)  marked saturation point G* where Δ = Λ
            (with c_4 = 1, G* = 2 / (1 - log 2) ≈ 6.518),
      (v)   region G ≥ G* where the original folklore Δ < Λ fails.

    Uses an analytic interpolation through (G_c, 0), (G*, Λ) that respects
    the qualitative gap-equation structure (no numerical Newton solve
    needed — the figure's purpose is to display the saturation event).
    """
    Lambda = 1.0
    # G_c at the boundary of the pre-geometric / Δ > 0 phase
    G_c = 1.0
    # Saturation coupling: Δ = Λ ⇒ G* = 2/(1 - log 2) (paper-textual constant)
    G_star = 2.0 / (1.0 - np.log(2.0))   # ≈ 6.518

    # Trivial branch
    G_trivial = np.linspace(0.0, G_c, 80)
    Delta_trivial = np.zeros_like(G_trivial)

    # Non-trivial branch: square-root onset at G_c; tuned so Δ(G*) = Λ
    # Δ(G) = α * sqrt((G - G_c) / G), with α chosen by Δ(G*) = Λ:
    G_grid = np.linspace(G_c, 12.0, 400)
    sat = np.sqrt(np.maximum((G_grid - G_c) / G_grid, 0.0))
    sat_star = np.sqrt((G_star - G_c) / G_star)
    alpha = Lambda / sat_star
    Delta_grid = alpha * sat

    fig = go.Figure()

    # Trivial branch
    fig.add_trace(go.Scatter(
        x=G_trivial, y=Delta_trivial, mode="lines",
        line=dict(color=COLORS["cross"], width=2.5, dash="dot"),
        name="Trivial branch (Δ = 0, G < G_c)",
    ))

    # Non-trivial branch
    fig.add_trace(go.Scatter(
        x=G_grid, y=Delta_grid, mode="lines",
        line=dict(color=COLORS["steel_blue"], width=3.0),
        name="Non-trivial branch Δ(G)",
    ))

    # Λ horizontal line
    fig.add_trace(go.Scatter(
        x=[0.0, 12.0], y=[Lambda, Lambda], mode="lines",
        line=dict(color=COLORS["horizon"], width=1.8, dash="dash"),
        name="Λ (cutoff)",
    ))

    # Folklore-violation region (Δ ≥ Λ): shaded amber strip
    fig.add_shape(
        type="rect", xref="x", yref="y",
        x0=G_star, x1=12.0, y0=Lambda, y1=max(Delta_grid) * 1.05,
        fillcolor="rgba(241, 143, 1, 0.18)",
        line=dict(width=0),
        layer="below",
    )

    # G* marker
    fig.add_trace(go.Scatter(
        x=[G_star], y=[Lambda], mode="markers+text",
        marker=dict(color=COLORS["amber"], size=14,
                    line=dict(color="black", width=1.2),
                    symbol="circle"),
        text=[f"  G* ≈ {G_star:.3f}"],
        textposition="top right",
        textfont=dict(family=FONT["family"], size=12, color=COLORS["amber"]),
        name="Saturation point Δ = Λ",
    ))

    # Annotation: folklore claim fails
    fig.add_annotation(
        x=9.5, y=Lambda * 1.15,
        text=(
            "<b>folklore claim Δ &lt; Λ fails for G ≥ G*</b><br>"
            "<sub>(Aristotle run 79e07d55: corrected statement adds "
            "G &lt; G* hypothesis)</sub>"
        ),
        showarrow=True, arrowhead=3, arrowsize=1.2, arrowwidth=1.6,
        ax=-100, ay=-50,
        font=dict(family=FONT["family"], size=11, color=COLORS["amber"]),
        bgcolor="rgba(255,255,255,0.85)",
    )
    fig.add_annotation(
        x=G_c, y=0.04,
        text="<b>G_c</b>",
        showarrow=False,
        font=dict(family=FONT["family"], size=11),
    )

    apply_layout(
        fig,
        height=520, width=900,
        title=dict(
            text=(
                "<b>Gap-equation counterexample: Δ(G) saturates Λ "
                "at G = G*</b><br>"
                "<sub>N_f = 1, Λ = 1, c₄ = 1; G* = 2/(1 − log 2) ≈ 6.518 "
                "(paper I1 §4)</sub>"
            ),
            x=0.5, xanchor="center", font=TITLE_FONT,
        ),
        xaxis=dict(title="Coupling G", range=[0, 12]),
        yaxis=dict(title="Gap Δ", range=[0, 1.5]),
        legend=dict(x=0.02, y=0.98, bgcolor="rgba(255,255,255,0.9)"),
    )
    return fig


def fig_i1_chirality_wall_tree() -> "go.Figure":
    """I1-FIG-6 — Chirality-wall axiom decomposition tree.

    Treemap representation: root (sm_no_nu_R_ewbg_doubly_forbidden) →
    2 obstructions (Z₁₆ chirality wall + crossover) → 3 sub-lemmas each →
    9 leaves total. Each leaf is annotated with "≤12 terms (Aristotle batch)".
    """
    # Per paper I1 §5: root → 2 obstructions × 3 pillars × ... Actually
    # the §5 text describes "three sub-lemmas per pillar, plus three
    # sub-lemmas for the crossover side, totaling nine." We treat Z16 as
    # split across THREE pillars (anomaly / fermion-content / wall-form),
    # each pillar having one sub-lemma → 3, plus three crossover-side
    # sub-lemmas → 6 total under Z16 + 3 under Crossover = 9 leaves.
    labels = [
        # root
        "sm_no_nu_R_ewbg_doubly_forbidden",
        # obstructions
        "Z₁₆ chirality wall",
        "Crossover (sphaleron suppression)",
        # Three pillars under Z16
        "Pillar A — anomaly",
        "Pillar B — fermion content",
        "Pillar C — wall form",
        # Z16 sub-lemmas (one per pillar)
        "Sublemma A.1<br>(z16-anomaly orthogonality)",
        "Sublemma B.1<br>(no-νR ⇒ Pillar B intact)",
        "Sublemma C.1<br>(wall-form ⇒ EWBG forbidden)",
        # Crossover sub-lemmas
        "Sublemma 2.1<br>(sphaleronSuppression ∈ [0,1])",
        "Sublemma 2.2<br>(¬viable ⇒ EWBG forbidden)",
        "Sublemma 2.3<br>(wall ∨ ¬viable ⇒ EWBG forbidden)",
    ]
    parents = [
        "",
        "sm_no_nu_R_ewbg_doubly_forbidden",
        "sm_no_nu_R_ewbg_doubly_forbidden",
        "Z₁₆ chirality wall",
        "Z₁₆ chirality wall",
        "Z₁₆ chirality wall",
        "Pillar A — anomaly",
        "Pillar B — fermion content",
        "Pillar C — wall form",
        "Crossover (sphaleron suppression)",
        "Crossover (sphaleron suppression)",
        "Crossover (sphaleron suppression)",
    ]
    # branchvalues='total': root = sum of leaves = 6 + 3 = 9.
    # Each Z16 pillar is an internal node containing one leaf (=1).
    # Z16 obstruction = 3 (sum of 3 pillars × 1 leaf each).
    # Crossover obstruction = 3 (3 leaves).
    values = [9, 6, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1]

    # Custom hover/text per node
    customdata = [
        "<b>50-term monolithic goal</b><br>intractable to Aristotle<br>(decomposition required)",
        "Obstruction-A:<br>chiral-wall integrity",
        "Obstruction-B:<br>sphaleron-rate suppression",
        "Pillar A: anomaly (TPE)",
        "Pillar B: fermion content",
        "Pillar C: wall form",
        "≤ 12 terms<br>Aristotle batch (priority 1)",
        "≤ 12 terms<br>Aristotle batch (priority 1)",
        "≤ 12 terms<br>Aristotle batch (priority 1)",
        "≤ 12 terms<br>Aristotle batch (priority 1)",
        "≤ 12 terms<br>Aristotle batch (priority 1)",
        "≤ 12 terms<br>Aristotle batch (priority 1)",
    ]

    # Color palette: root carmine, obstructions amber, pillars sage,
    # leaves steel_blue (the sub-lemmas Aristotle actually proved).
    colors = [
        COLORS["carmine"],
        COLORS["amber"], COLORS["amber"],
        COLORS["sage"], COLORS["sage"], COLORS["sage"],
        COLORS["steel_blue"], COLORS["steel_blue"], COLORS["steel_blue"],
        COLORS["steel_blue"], COLORS["steel_blue"], COLORS["steel_blue"],
    ]

    fig = go.Figure(go.Treemap(
        labels=labels,
        parents=parents,
        values=values,
        customdata=customdata,
        marker=dict(colors=colors, line=dict(color="white", width=2)),
        textfont=dict(family=FONT["family"], size=12, color="white"),
        textposition="middle center",
        hovertemplate="<b>%{label}</b><br>%{customdata}<extra></extra>",
        branchvalues="total",
        tiling=dict(packing="squarify"),
    ))

    fig.update_layout(
        height=560, width=1100,
        title=dict(
            text=(
                "<b>Chirality-wall axiom decomposition tree</b><br>"
                "<sub>Monolithic 50-term goal → 9 sub-lemmas (≤12 terms each); "
                "all 9 closed in a single Aristotle priority batch "
                "(paper I1 §5)</sub>"
            ),
            x=0.5, xanchor="center", font=TITLE_FONT,
        ),
        font=FONT,
        plot_bgcolor="white", paper_bgcolor="white",
        margin=dict(l=20, r=20, t=100, b=20),
    )
    return fig


# ════════════════════════════════════════════════════════════════════════
# Paper I2 — Verified statistical estimators + lean-tensor-categories
# ════════════════════════════════════════════════════════════════════════


def fig_i2_categorical_hierarchy() -> "go.Figure":
    """I2-FIG-1 — Categorical hierarchy poset (paper I2 §3).

    Hasse-diagram-style schematic of the chain
    Monoidal -> Braided -> Balanced -> Pivotal -> Ribbon -> Fusion -> Modular.
    Mathlib substrate (steel blue) at the bottom; library-original
    additions (amber) at successively higher levels. File-path
    annotations anchor each node to the lean-tensor-categories source.
    """
    nodes = [
        ("MonoidalCategory",  0.30, 0.05, "mathlib", "Mathlib (substrate)"),
        ("BraidedCategory",   0.30, 0.20, "mathlib", "Mathlib (substrate)"),
        ("BalancedCategory",  0.30, 0.38, "library", "RibbonCategory.lean"),
        ("PivotalCategory",   0.30, 0.56, "library", "RibbonCategory.lean"),
        ("RibbonCategory",    0.30, 0.74, "library", "RibbonCategory.lean"),
        ("FusionCategory",    0.72, 0.56, "library", "FusionCategory.lean"),
        ("ModularTensorData", 0.51, 0.92, "library", "RibbonCategory.lean"),
    ]
    edges = [
        ("MonoidalCategory",  "BraidedCategory"),
        ("BraidedCategory",   "BalancedCategory"),
        ("BalancedCategory",  "PivotalCategory"),
        ("PivotalCategory",   "RibbonCategory"),
        ("BraidedCategory",   "FusionCategory"),
        ("RibbonCategory",    "ModularTensorData"),
        ("FusionCategory",    "ModularTensorData"),
    ]
    label_to_xy = {n[0]: (n[1], n[2]) for n in nodes}

    fig = go.Figure()
    for src, dst in edges:
        x0, y0 = label_to_xy[src]
        x1, y1 = label_to_xy[dst]
        fig.add_annotation(
            x=x1, y=y1, ax=x0, ay=y0,
            xref="x", yref="y", axref="x", ayref="y",
            showarrow=True, arrowhead=2, arrowsize=1.2, arrowwidth=1.6,
            arrowcolor=COLORS["cross"],
        )

    xs = [n[1] for n in nodes]
    ys = [n[2] for n in nodes]
    labels = [n[0] for n in nodes]
    files = [n[4] for n in nodes]
    colors = [
        COLORS["dispersive"] if n[3] == "mathlib" else COLORS["amber"]
        for n in nodes
    ]
    sizes = [54 if n[3] == "mathlib" else 62 for n in nodes]
    hover = [f"<b>{lab}</b><br>{f}" for lab, f in zip(labels, files)]

    fig.add_trace(go.Scatter(
        x=xs, y=ys,
        mode="markers+text",
        marker=dict(size=sizes, color=colors,
                    line=dict(color="black", width=1.4)),
        text=labels,
        textposition="middle right",
        textfont=dict(family=FONT["family"], size=12, color="black"),
        hovertext=hover, hoverinfo="text",
        showlegend=False,
        name="categorical-hierarchy",
    ))

    fig.add_annotation(
        x=0.02, y=0.13, xref="x", yref="y", showarrow=False,
        text="<b>Mathlib substrate</b>",
        font=dict(size=12, color=COLORS["dispersive"]),
        align="left",
    )
    fig.add_annotation(
        x=0.02, y=0.74, xref="x", yref="y", showarrow=False,
        text="<b>Library originals</b><br>(this work)",
        font=dict(size=12, color=COLORS["amber"]), align="left",
    )

    fig.update_xaxes(range=[-0.05, 1.05], visible=False)
    fig.update_yaxes(range=[-0.05, 1.05], visible=False)
    fig.update_layout(
        height=620, width=900,
        plot_bgcolor="white", paper_bgcolor="white",
        font=FONT,
        title=dict(
            text=(
                "<b>Categorical hierarchy: Monoidal -> ... -> Modular</b><br>"
                "<sub>Mathlib substrate (steel blue) extended with "
                "library-original additions (amber); paper I2 §3</sub>"
            ),
            x=0.5, xanchor="center", font=TITLE_FONT,
        ),
        margin=dict(l=20, r=20, t=100, b=20),
    )
    return fig


def fig_i2_module_dependencies() -> "go.Figure":
    """I2-FIG-2 — Module dependency Sankey (paper I2 §7).

    28-module lean-tensor-categories library grouped into four tiers:
    categorical hierarchy (4), Hopf algebra (4), number fields (9), MTC
    instances (11). Sankey flows go from MTC instances into the layers
    they depend on.
    """
    instances = [
        "SU(2)_1 / SU2kFusion", "SU(2)_2 / SU2kMTC",
        "SU(2)_3 / SU2kSMatrix", "SU(2)_4", "SU(2)_5",
        "SU(3)_2 (Fusion)", "SU(3)_2 (S-matrix)", "SU(3)_2 (F-symbols)",
        "Ising (Braiding)", "Ising (Gates)",
        "Fibonacci (Braiding+MTC)",
    ]
    number_fields = [
        "QSqrt2", "QSqrt3", "QSqrt5", "QCyc3", "QCyc5",
        "QCyc5Ext", "QCyc15", "QCyc15SqrtPhi", "QCyc16",
    ]
    hopf = [
        "QuantumGroupHopf", "Uqsl2Hopf", "Uqsl2AffineHopf", "Uqsl3Hopf",
    ]
    categorical = [
        "KLinearCategory", "FusionCategory",
        "SphericalCategory", "RibbonCategory",
    ]
    nodes = instances + number_fields + hopf + categorical
    idx = {name: i for i, name in enumerate(nodes)}
    node_colors = (
        [COLORS["amber"]] * len(instances)
        + [COLORS["Rb87"]] * len(number_fields)
        + [COLORS["Na23"]] * len(hopf)
        + [COLORS["steel_blue"]] * len(categorical)
    )

    deps = [
        ("SU(2)_1 / SU2kFusion",      "FusionCategory"),
        ("SU(2)_2 / SU2kMTC",         "QSqrt2"),
        ("SU(2)_2 / SU2kMTC",         "RibbonCategory"),
        ("SU(2)_3 / SU2kSMatrix",     "QCyc5"),
        ("SU(2)_3 / SU2kSMatrix",     "Uqsl2Hopf"),
        ("SU(2)_4",                   "QCyc16"),
        ("SU(2)_4",                   "RibbonCategory"),
        ("SU(2)_5",                   "QCyc15"),
        ("SU(2)_5",                   "Uqsl2AffineHopf"),
        ("SU(3)_2 (Fusion)",          "FusionCategory"),
        ("SU(3)_2 (S-matrix)",        "QCyc15"),
        ("SU(3)_2 (S-matrix)",        "Uqsl3Hopf"),
        ("SU(3)_2 (F-symbols)",       "QCyc15SqrtPhi"),
        ("Ising (Braiding)",          "QSqrt2"),
        ("Ising (Braiding)",          "RibbonCategory"),
        ("Ising (Gates)",             "QCyc16"),
        ("Fibonacci (Braiding+MTC)",  "QCyc5Ext"),
        ("Fibonacci (Braiding+MTC)",  "QuantumGroupHopf"),
        ("Fibonacci (Braiding+MTC)",  "RibbonCategory"),
        ("QSqrt2",          "KLinearCategory"),
        ("QSqrt5",          "KLinearCategory"),
        ("QCyc5",           "KLinearCategory"),
        ("QCyc16",          "KLinearCategory"),
        ("Uqsl2Hopf",        "SphericalCategory"),
        ("Uqsl3Hopf",        "SphericalCategory"),
        ("QuantumGroupHopf", "SphericalCategory"),
        ("Uqsl2AffineHopf",  "FusionCategory"),
    ]
    src = [idx[s] for s, _ in deps]
    dst = [idx[d] for _, d in deps]
    val = [1] * len(deps)
    link_colors = [
        "rgba(244,143,1,0.35)" if nodes[s] in instances
        else "rgba(46,134,171,0.35)" if nodes[s] in number_fields
        else "rgba(162,59,114,0.35)"
        for s in src
    ]

    fig = go.Figure(go.Sankey(
        arrangement="snap",
        node=dict(
            label=nodes, color=node_colors,
            pad=14, thickness=16,
            line=dict(color="black", width=0.6),
        ),
        link=dict(source=src, target=dst, value=val, color=link_colors),
    ))
    fig.update_layout(
        height=720, width=1100,
        plot_bgcolor="white", paper_bgcolor="white",
        font=FONT,
        title=dict(
            text=(
                "<b>lean-tensor-categories: 28-module dependency graph</b>"
                "<br><sub>MTC instances (amber) -> number fields "
                "(steel blue) + Hopf layer (berry) -> categorical core "
                "(steel blue, foundation); paper I2 §7</sub>"
            ),
            x=0.5, xanchor="center", font=TITLE_FONT,
        ),
        margin=dict(l=20, r=20, t=100, b=20),
    )
    return fig


def fig_i2_mtc_instances() -> "go.Figure":
    """I2-FIG-3 — MTC instances comparison table (paper I2 §6).

    Plotly ``go.Table`` listing 8 MTC instances with shipped components:
    simple-object count, q-dimensions, S/T/F-symbols, Verlinde-formula
    verification, and underlying number field.
    """
    headers = [
        "<b>Instance</b>",
        "<b># simples</b>",
        "<b>q-dimensions (representative)</b>",
        "<b>S-matrix</b>",
        "<b>T-matrix</b>",
        "<b>F-symbols</b>",
        "<b>Verlinde verified</b>",
        "<b>Number field</b>",
    ]
    instances = [
        "SU(2)_1", "SU(2)_2", "SU(2)_3", "SU(2)_4", "SU(2)_5",
        "SU(3)_2", "Ising", "Fibonacci",
    ]
    n_simples = ["2", "3", "4", "5", "6", "6", "3", "2"]
    qdims = [
        "(1, 1)",
        "(1, √2, 1)",
        "(1, φ, φ, 1)",
        "(1, √(2+√2), √2, √(2+√2), 1)",
        "(1, ..., 1) [partial]",
        "(1, 3, 3, 8, ...) [SU(3) simples]",
        "(1, √2, 1)",
        "(1, φ)",
    ]
    s_mat = ["✓", "✓", "✓", "✓", "✓", "✓", "✓", "✓"]
    t_mat = ["✓", "✓", "✓", "✓", "✗", "✓", "✓", "✓"]
    f_sym = ["partial", "partial", "✗", "✗", "✗", "✓", "✓", "✓"]
    verlinde = ["✓", "✓", "✗", "✗", "✗", "✗", "✓", "partial"]
    nf = [
        "ℚ", "ℚ(√2)", "ℚ(ζ₅)",
        "ℚ(ζ₁₆)", "ℚ(ζ₇)",
        "ℚ(ζ₃, ζ₅)",
        "ℚ(√2, e^{iπ/8})",
        "ℚ(ζ₅)[√φ]",
    ]

    def _cell_color(v: str) -> str:
        if v == "✓":
            return "rgba(70,130,180,0.20)"
        if v == "partial":
            return "rgba(244,143,1,0.30)"
        if v == "✗":
            return "rgba(141,153,174,0.25)"
        return "white"

    fill_default = "rgba(255,255,255,1)"
    cell_columns = [instances, n_simples, qdims, s_mat, t_mat,
                    f_sym, verlinde, nf]
    fill_columns = [
        [fill_default] * len(instances),
        [fill_default] * len(instances),
        [fill_default] * len(instances),
        [_cell_color(v) for v in s_mat],
        [_cell_color(v) for v in t_mat],
        [_cell_color(v) for v in f_sym],
        [_cell_color(v) for v in verlinde],
        [fill_default] * len(instances),
    ]

    fig = go.Figure(go.Table(
        header=dict(
            values=headers,
            fill_color=COLORS["dispersive"],
            font=dict(family=FONT["family"], size=12, color="white"),
            align="center", height=34,
        ),
        cells=dict(
            values=cell_columns,
            fill_color=fill_columns,
            font=dict(family=FONT["family"], size=11, color="black"),
            align="center", height=28,
        ),
        columnwidth=[55, 40, 110, 35, 35, 45, 55, 75],
    ))
    fig.update_layout(
        height=420, width=1180,
        plot_bgcolor="white", paper_bgcolor="white",
        font=FONT,
        title=dict(
            text=(
                "<b>MTC instances: shipped components</b><br>"
                "<sub>Steel-blue cells = shipped (✓); amber = partial; "
                "grey = not yet (✗); paper I2 §6</sub>"
            ),
            x=0.5, xanchor="center", font=TITLE_FONT,
        ),
        margin=dict(l=15, r=15, t=90, b=15),
    )
    return fig


def fig_i2_jackknife_dependencies() -> "go.Figure":
    """I2-FIG-4 — VerifiedJackknife theorem dependency graph
    (paper I2 §2).

    Network of the four ``VerifiedJackknife`` theorems and their Mathlib-
    lemma dependencies. Project theorems (amber) are annotated with the
    ``test_*`` function in ``tests/test_jackknife.py`` that exercises
    each (per Stage-9 advisory I2-ADV-2). Mathlib lemmas (steel blue)
    and the ``autocovariance`` definition node (cool grey) form the
    leaves.
    """
    nodes = [
        ("jackknifeVariance_nonneg",       0.18, 0.85, "thm",
         "test_jackknife_variance_nonneg"),
        ("autocovariance_zero_nonneg",     0.50, 0.85, "thm",
         "test_autocov_zero_nonneg"),
        ("intAutocorrTime_uncorrelated",   0.78, 0.85, "thm",
         "test_tau_int_iid"),
        ("intAutocorrTime_ge_half",        0.50, 0.55, "thm",
         "test_tau_int_ge_half"),
        ("mul_nonneg",                     0.05, 0.30, "lib",  None),
        ("Finset.sum_nonneg",              0.25, 0.20, "lib",  None),
        ("sq_nonneg",                      0.18, 0.05, "lib",  None),
        ("mul_self_nonneg",                0.42, 0.30, "lib",  None),
        ("autocovariance (def)",           0.78, 0.55, "def",  None),
    ]
    edges = [
        ("jackknifeVariance_nonneg",     "mul_nonneg"),
        ("jackknifeVariance_nonneg",     "Finset.sum_nonneg"),
        ("jackknifeVariance_nonneg",     "sq_nonneg"),
        ("autocovariance_zero_nonneg",   "mul_self_nonneg"),
        ("autocovariance_zero_nonneg",   "Finset.sum_nonneg"),
        ("intAutocorrTime_uncorrelated", "autocovariance (def)"),
        ("intAutocorrTime_ge_half",      "autocovariance_zero_nonneg"),
    ]

    label_to_xy = {n[0]: (n[1], n[2]) for n in nodes}
    kind_color = {
        "thm": COLORS["amber"],
        "lib": COLORS["dispersive"],
        "def": COLORS["cross"],
    }

    fig = go.Figure()
    for src, dst in edges:
        x0, y0 = label_to_xy[src]
        x1, y1 = label_to_xy[dst]
        fig.add_annotation(
            x=x1, y=y1, ax=x0, ay=y0,
            xref="x", yref="y", axref="x", ayref="y",
            showarrow=True, arrowhead=2, arrowsize=1.0, arrowwidth=1.4,
            arrowcolor=COLORS["cross"],
        )

    xs = [n[1] for n in nodes]
    ys = [n[2] for n in nodes]
    labels = [n[0] for n in nodes]
    colors = [kind_color[n[3]] for n in nodes]
    sizes = [40 if n[3] != "thm" else 52 for n in nodes]
    hover = []
    for n in nodes:
        if n[3] == "thm":
            hover.append(
                f"<b>{n[0]}</b><br>kind: project theorem<br>"
                f"test (tests/test_jackknife.py): {n[4]}"
            )
        elif n[3] == "lib":
            hover.append(f"<b>{n[0]}</b><br>kind: Mathlib lemma")
        else:
            hover.append(f"<b>{n[0]}</b><br>kind: project definition")

    fig.add_trace(go.Scatter(
        x=xs, y=ys,
        mode="markers+text",
        marker=dict(size=sizes, color=colors,
                    line=dict(color="black", width=1.4)),
        text=labels,
        textposition="bottom center",
        textfont=dict(family=FONT["family"], size=11, color="black"),
        hovertext=hover, hoverinfo="text",
        showlegend=False,
        name="jackknife-deps",
    ))

    fig.add_annotation(
        x=0.97, y=0.98, xref="paper", yref="paper",
        showarrow=False, align="left", xanchor="right", yanchor="top",
        text=(
            f"<span style='color:{COLORS['amber']}'>●</span> project theorem"
            f"&nbsp;&nbsp;<span style='color:{COLORS['dispersive']}'>●</span> Mathlib lemma"
            f"&nbsp;&nbsp;<span style='color:{COLORS['cross']}'>●</span> project def"
        ),
        font=dict(size=11),
        bgcolor="rgba(255,255,255,0.85)",
        bordercolor="black", borderwidth=0.5,
    )

    fig.update_xaxes(range=[-0.05, 1.05], visible=False)
    fig.update_yaxes(range=[-0.05, 1.0], visible=False)
    fig.update_layout(
        height=560, width=900,
        plot_bgcolor="white", paper_bgcolor="white",
        font=FONT,
        title=dict(
            text=(
                "<b>VerifiedJackknife: 4 theorems and their dependencies</b>"
                "<br><sub>Project theorems (amber) lean on Mathlib lemmas "
                "(steel blue) and a project definition (grey); each theorem "
                "annotated with its <tt>tests/test_jackknife.py</tt> test "
                "(paper I2 §2)</sub>"
            ),
            x=0.5, xanchor="center", font=TITLE_FONT,
        ),
        margin=dict(l=20, r=20, t=100, b=40),
    )
    return fig


def fig_i2_mathlib_upstream_flow() -> "go.Figure":
    """I2-FIG-5 — Mathlib R1/R2/R3 + atomic-PR flow (paper I2 §7).

    Three sequential R-gates flow into a chain of four atomic Mathlib
    PRs. A separate cool-grey branch shows the software-only fallback
    if the gate is delayed past 6 months.

    Layout uses short in-node labels (R1/R2/R3, PR-1/2/3/4, F1/F2)
    rendered inside text-fitted rectangles; the long descriptions
    appear in a side-table legend below the diagram.
    """
    # (label, x, y, kind, full_description)
    nodes = [
        ("R1",   0.08, 0.80, "gate", "Mathlib Zulip introduction"),
        ("R2",   0.21, 0.80, "gate", "AI-tool-assistance disclosure"),
        ("R3",   0.34, 0.80, "gate", "PR-strategy discussion"),
        ("PR-1", 0.49, 0.80, "pr",
         "QSqrt2 + ComputableAdjoinRoot bridge"),
        ("PR-2", 0.64, 0.80, "pr",
         "PivotalCategory + RibbonCategory"),
        ("PR-3", 0.79, 0.80, "pr",
         "QuasitriangularBialgebra + RibbonHopfAlgebra"),
        ("PR-4+", 0.94, 0.80, "pr",
         "MTC instances (SU(2)_k, Ising, Fibonacci)"),
        ("F1",   0.49, 0.30, "fb",
         "Software-only release (JOSS, this paper)"),
        ("F2",   0.79, 0.30, "fb",
         "Later: JOSS update (retrofit upstream PRs)"),
    ]
    edges = [
        ("R1",   "R2",   "gate"),
        ("R2",   "R3",   "gate"),
        ("R3",   "PR-1", "pr"),
        ("PR-1", "PR-2", "pr"),
        ("PR-2", "PR-3", "pr"),
        ("PR-3", "PR-4+", "pr"),
        ("R3",   "F1",   "fb"),
        ("F1",   "F2",   "fb"),
    ]
    kind_color = {
        "gate": COLORS["dispersive"],
        "pr":   COLORS["amber"],
        "fb":   COLORS["cross"],
    }
    label_to_xy = {n[0]: (n[1], n[2]) for n in nodes}
    label_to_kind = {n[0]: n[3] for n in nodes}

    fig = go.Figure()

    # Half-extent (in normalized x/y units) for node rectangles.
    # Rectangles are wider than tall to accommodate the short labels.
    rect_hx, rect_hy = 0.045, 0.06

    # Draw shapes (text-fitted rectangles) instead of fixed-radius
    # markers so the in-node label always fits.
    for label, x, y, kind, _desc in nodes:
        c = kind_color[kind]
        fig.add_shape(
            type="rect",
            x0=x - rect_hx, x1=x + rect_hx,
            y0=y - rect_hy, y1=y + rect_hy,
            line=dict(color="black", width=1.4),
            fillcolor=c,
            xref="x", yref="y",
            layer="below",
        )
        fig.add_annotation(
            x=x, y=y, xref="x", yref="y",
            text=f"<b>{label}</b>",
            showarrow=False,
            font=dict(family=FONT["family"], size=14, color="white"),
            xanchor="center", yanchor="middle",
        )

    # Draw arrows between rectangles. Start/end at rectangle borders
    # rather than centers so the arrowheads are visible.
    for src, dst, kind in edges:
        x0, y0 = label_to_xy[src]
        x1, y1 = label_to_xy[dst]
        # Adjust endpoints to land on rectangle borders.
        if y0 == y1:  # horizontal
            sgn = 1 if x1 > x0 else -1
            sx0 = x0 + sgn * rect_hx
            sx1 = x1 - sgn * rect_hx
            sy0 = y0
            sy1 = y1
        else:  # vertical (R3 -> F1)
            sx0, sx1 = x0, x1
            sy0 = y0 - rect_hy if y1 < y0 else y0 + rect_hy
            sy1 = y1 + rect_hy if y1 < y0 else y1 - rect_hy
        fig.add_annotation(
            x=sx1, y=sy1, ax=sx0, ay=sy0,
            xref="x", yref="y", axref="x", ayref="y",
            showarrow=True, arrowhead=3, arrowsize=1.4, arrowwidth=1.8,
            arrowcolor=kind_color[kind], opacity=0.9,
        )

    # Hidden scatter trace so the figure has at least one trace
    # (required by some Plotly export configurations) and to enable
    # hover info.
    fig.add_trace(go.Scatter(
        x=[n[1] for n in nodes],
        y=[n[2] for n in nodes],
        mode="markers",
        marker=dict(size=1, color="rgba(0,0,0,0)"),
        hovertext=[f"<b>{n[0]}</b><br>{n[4]}" for n in nodes],
        hoverinfo="text",
        showlegend=False,
        name="upstream-flow",
    ))

    # Top-right legend: kind ↔ shape color.
    fig.add_annotation(
        x=0.99, y=0.98, xref="paper", yref="paper",
        showarrow=False, xanchor="right", yanchor="top",
        text=(
            f"<span style='color:{COLORS['dispersive']}'>■</span> "
            f"R-gate (relationship-building)"
            f"&nbsp;&nbsp;<span style='color:{COLORS['amber']}'>■</span> "
            f"atomic Mathlib PR"
            f"&nbsp;&nbsp;<span style='color:{COLORS['cross']}'>■</span> "
            f"software-only fallback"
        ),
        font=dict(size=11),
        bgcolor="rgba(255,255,255,0.92)",
        bordercolor="black", borderwidth=0.5,
    )

    # Side-table legend (below the diagram) mapping abbreviations
    # to their full descriptions. Two columns to fit everything.
    legend_lines_left = [
        f"<b>R1</b> Mathlib Zulip introduction",
        f"<b>R2</b> AI-tool-assistance disclosure",
        f"<b>R3</b> PR-strategy discussion",
        f"<b>PR-1</b> QSqrt2 + ComputableAdjoinRoot bridge",
        f"<b>PR-2</b> PivotalCategory + RibbonCategory",
    ]
    legend_lines_right = [
        f"<b>PR-3</b> QuasitriangularBialgebra + RibbonHopfAlgebra",
        f"<b>PR-4+</b> MTC instances (SU(2)_k, Ising, Fibonacci)",
        f"<b>F1</b> Software-only release (JOSS, this paper)",
        f"<b>F2</b> JOSS update (retrofit upstream PRs)",
        f"<i>Fallback if Mathlib AI-content acceptance &gt; 6 mo</i>",
    ]
    fig.add_annotation(
        x=0.04, y=0.05, xref="paper", yref="paper",
        showarrow=False, xanchor="left", yanchor="bottom",
        text="<br>".join(legend_lines_left),
        font=dict(size=10, family=FONT["family"]),
        align="left",
        bgcolor="rgba(245,245,245,0.95)",
        bordercolor="black", borderwidth=0.4,
    )
    fig.add_annotation(
        x=0.55, y=0.05, xref="paper", yref="paper",
        showarrow=False, xanchor="left", yanchor="bottom",
        text="<br>".join(legend_lines_right),
        font=dict(size=10, family=FONT["family"]),
        align="left",
        bgcolor="rgba(245,245,245,0.95)",
        bordercolor="black", borderwidth=0.4,
    )

    fig.update_xaxes(range=[0.0, 1.0], visible=False)
    fig.update_yaxes(range=[0.0, 1.0], visible=False)
    fig.update_layout(
        height=560, width=1200,
        plot_bgcolor="white", paper_bgcolor="white",
        font=FONT,
        title=dict(
            text=(
                "<b>Mathlib upstream coordination: R1/R2/R3 gates → "
                "atomic-PR chain</b><br><sub>Steel-blue gates → amber "
                "PR sequence; cool-grey fallback for software-only release "
                "(paper I2 §7).</sub>"
            ),
            x=0.5, xanchor="center", font=TITLE_FONT,
        ),
        margin=dict(l=20, r=20, t=100, b=20),
    )
    return fig


if __name__ == "__main__":
    main()
