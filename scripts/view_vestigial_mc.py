#!/usr/bin/env python3
"""Interactive viewer for vestigial MC results.

Generates Plotly HTML dashboard from vestigial_mc_*.json results files.
Supports single-file viewing and side-by-side comparison (ADW vs NJL).

Usage:
  # View latest results (any model)
  python scripts/view_vestigial_mc.py

  # View latest NJL or ADW results
  python scripts/view_vestigial_mc.py --latest njl
  python scripts/view_vestigial_mc.py --latest adw

  # View a specific file
  python scripts/view_vestigial_mc.py data/vestigial_mc/vestigial_mc_njl_20260331T175303.json

  # Compare two runs side-by-side
  python scripts/view_vestigial_mc.py --compare data/vestigial_mc/vestigial_mc_njl_*.json data/vestigial_mc/vestigial_mc_adw_*.json

  # Compare latest of each model
  python scripts/view_vestigial_mc.py --compare-models

  # List all available results
  python scripts/view_vestigial_mc.py --list
"""

import argparse
import json
import sys
from pathlib import Path

import numpy as np
import plotly.graph_objects as go
from plotly.subplots import make_subplots

# Project palette
BLUES = ['#1f77b4', '#2E86AB', '#4ECDC4', '#45B7D1', '#96CEB4',
         '#7FB3D8', '#5DADE2', '#3498DB', '#2980B9', '#1A5276',
         '#154360', '#0E2F44', '#0B1F30']
REDS = ['#E63946', '#A23B72', '#C0392B', '#E74C3C', '#F39C12',
        '#D35400', '#CB4335', '#922B21', '#7B241C', '#641E16']
AMBERS = ['#F18F01', '#E8A317', '#D4A017', '#C68E17', '#B8860B']

RESULTS_DIR = Path("data/vestigial_mc")


# ── Utilities ──

def load_results(path: str) -> dict:
    with open(path) as f:
        return json.load(f)


def detect_model(path: str, data: dict = None) -> str:
    """Detect model type from filename or metadata."""
    p = Path(path).name
    if '_njl_' in p:
        return 'NJL'
    if '_adw_' in p:
        return 'ADW'
    # Legacy files without model tag — check coupling range
    if data:
        bc = data.get('binder_crossing', {}).get('data', {})
        for Ld in bc.values():
            g_vals = Ld.get('g_EH_values', [])
            if g_vals and min(g_vals) < 0:
                return 'ADW'
            if g_vals and min(g_vals) >= 0:
                return 'NJL'
    return 'Unknown'


def find_results(model: str = None) -> list[Path]:
    """Find results files, optionally filtered by model."""
    pattern = f"vestigial_mc_{model.lower()}_*.json" if model else "vestigial_mc_*.json"
    files = sorted(RESULTS_DIR.glob(pattern), key=lambda p: p.stat().st_mtime)
    return files


def find_latest(model: str = None) -> str:
    files = find_results(model)
    if not files:
        tag = f" for model '{model}'" if model else ""
        print(f"No results files found{tag} in {RESULTS_DIR}/")
        sys.exit(1)
    return str(files[-1])


def make_color_map(sizes: list[int], palette: list[str]) -> dict[int, str]:
    return {L: palette[i % len(palette)] for i, L in enumerate(sizes)}


def list_results():
    """Print all available results files with key stats."""
    files = find_results()
    if not files:
        print(f"No results in {RESULTS_DIR}/")
        return
    print(f"{'File':<65s}  {'Model':>5s}  {'Sizes':>20s}  {'Sweeps':>6s}  {'Runtime':>8s}  {'Binder':>8s}  {'Split':>5s}")
    print("-" * 135)
    for f in files:
        try:
            data = load_results(str(f))
            m = data.get('metadata', {})
            model = detect_model(str(f), data)
            sizes = m.get('lattice_sizes', [])
            sweeps = m.get('n_measure', '?')
            runtime = f"{m.get('total_runtime_s', 0) / 3600:.1f}h"
            bc = data.get('binder_crossing', {})
            binder = bc.get('vestigial_detected', '?')
            fss = data.get('finite_size_scaling', {})
            split = fss.get('split_transition', '?')
            sizes_str = f"L={min(sizes)}-{max(sizes)} ({len(sizes)})" if sizes else "?"
            print(f"{f.name:<65s}  {model:>5s}  {sizes_str:>20s}  {sweeps:>6}  {runtime:>8s}  {str(binder):>8s}  {str(split):>5s}")
        except Exception as e:
            print(f"{f.name:<65s}  ERROR: {e}")


# ── Single-file figures ──

def fig_binder_tetrad(data: dict, title_suffix: str = "") -> go.Figure:
    bc = data['binder_crossing']
    sizes = sorted(int(k) for k in bc['data'].keys())
    colors = make_color_map(sizes, BLUES)
    fig = go.Figure()
    for L in sizes:
        Ld = bc['data'][str(L)]
        fig.add_trace(go.Scatter(
            x=Ld['g_EH_values'], y=Ld['binder_tetrad'],
            mode='lines+markers', name=f'L={L}', marker=dict(size=4),
            line=dict(color=colors[L], width=1.5),
        ))
    fig.add_hline(y=2/3, line_dash="dash", line_color="gray", annotation_text="Gaussian (2/3)")
    fig.update_layout(title=f"Binder Cumulant — Tetrad{title_suffix}",
                      xaxis_title="Coupling", yaxis_title="U₄ (tetrad)", legend_title="Lattice size")
    return fig


def fig_binder_metric(data: dict, title_suffix: str = "") -> go.Figure:
    bc = data['binder_crossing']
    sizes = sorted(int(k) for k in bc['data'].keys())
    colors = make_color_map(sizes, BLUES)
    fig = go.Figure()
    for L in sizes:
        Ld = bc['data'][str(L)]
        fig.add_trace(go.Scatter(
            x=Ld['g_EH_values'], y=Ld['binder_metric'],
            mode='lines+markers', name=f'L={L}', marker=dict(size=4),
            line=dict(color=colors[L], width=1.5),
        ))
    fig.add_hline(y=2/3, line_dash="dash", line_color="gray", annotation_text="Gaussian (2/3)")
    fig.update_layout(title=f"Binder Cumulant — Metric{title_suffix}",
                      xaxis_title="Coupling", yaxis_title="U₄ (metric)", legend_title="Lattice size")
    return fig


def fig_susceptibility(data: dict, title_suffix: str = "", log_scale: bool = False) -> go.Figure:
    fss = data['finite_size_scaling']
    raw = fss.get('raw_results', [])
    if not raw:
        return go.Figure().update_layout(title="No FSS raw_results available")
    sizes = sorted(set(r['L'] for r in raw))
    colors_t = make_color_map(sizes, BLUES)
    colors_m = make_color_map(sizes, REDS)
    fig = make_subplots(rows=2, cols=1, shared_xaxes=True,
                        subplot_titles=[f"Tetrad χ{' (log)' if log_scale else ''}",
                                        f"Metric χ{' (log)' if log_scale else ''}"])
    for L in sizes:
        pts = sorted([r for r in raw if r['L'] == L], key=lambda r: r['ratio'])
        ratios = [r['ratio'] for r in pts]
        chi_t = [max(r['chi_tetrad'], 1e-10) for r in pts] if log_scale else [r['chi_tetrad'] for r in pts]
        chi_m = [max(r['chi_metric'], 1e-10) for r in pts] if log_scale else [r['chi_metric'] for r in pts]
        fig.add_trace(go.Scatter(x=ratios, y=chi_t, mode='lines+markers', name=f'L={L}',
                                  marker=dict(size=4), line=dict(color=colors_t[L], width=1.5),
                                  legendgroup=f'L{L}', showlegend=True), row=1, col=1)
        fig.add_trace(go.Scatter(x=ratios, y=chi_m, mode='lines+markers', name=f'L={L}',
                                  marker=dict(size=4), line=dict(color=colors_m[L], width=1.5),
                                  legendgroup=f'L{L}', showlegend=False), row=2, col=1)
    if log_scale:
        fig.update_yaxes(type="log", row=1, col=1)
        fig.update_yaxes(type="log", row=2, col=1)
    fig.update_xaxes(title_text="G / G_c", row=2, col=1)
    fig.update_layout(title=f"Susceptibility vs Coupling{title_suffix}", height=700, legend_title="Lattice size")
    return fig


def fig_peak_scaling(data: dict, title_suffix: str = "") -> go.Figure:
    """Peak locations + heights in a 2-column layout."""
    fss = data['finite_size_scaling']
    peaks = fss.get('susceptibility_peaks', {})
    if not peaks:
        return go.Figure().update_layout(title="No susceptibility peaks available")
    sizes = sorted(int(k) for k in peaks.keys())
    tet_loc = [peaks[str(L)]['tetrad_peak_coupling'] for L in sizes]
    met_loc = [peaks[str(L)]['metric_peak_coupling'] for L in sizes]
    tet_h = [peaks[str(L)]['tetrad_peak_height'] for L in sizes]
    met_h = [peaks[str(L)]['metric_peak_height'] for L in sizes]

    fig = make_subplots(rows=1, cols=2, subplot_titles=["Peak Location vs L", "Peak Height vs L"])
    fig.add_trace(go.Scatter(x=sizes, y=tet_loc, mode='lines+markers', name='Tetrad',
                              marker=dict(size=8, color='#2E86AB'), line=dict(width=2)), row=1, col=1)
    fig.add_trace(go.Scatter(x=sizes, y=met_loc, mode='lines+markers', name='Metric',
                              marker=dict(size=8, color='#E63946'), line=dict(width=2)), row=1, col=1)
    fig.add_trace(go.Scatter(x=sizes, y=tet_h, mode='lines+markers', name='χ_tet peak',
                              marker=dict(size=6, color='#2E86AB'), showlegend=False), row=1, col=2)
    fig.add_trace(go.Scatter(x=sizes, y=met_h, mode='lines+markers', name='χ_met peak',
                              marker=dict(size=6, color='#E63946'), showlegend=False), row=1, col=2)
    fig.update_yaxes(title_text="Peak coupling (G/G_c)", row=1, col=1)
    fig.update_yaxes(title_text="Peak height", type="log", row=1, col=2)
    fig.update_xaxes(title_text="L", row=1, col=1)
    fig.update_xaxes(title_text="L", row=1, col=2)
    fig.update_layout(title=f"Susceptibility Peak Scaling{title_suffix}", height=450, width=1000)
    return fig


def fig_acceptance(data: dict, title_suffix: str = "") -> go.Figure:
    bc = data['binder_crossing']
    sizes = sorted(int(k) for k in bc['data'].keys())
    colors = make_color_map(sizes, BLUES)
    fig = go.Figure()
    for L in sizes:
        Ld = bc['data'][str(L)]
        fig.add_trace(go.Scatter(
            x=Ld['g_EH_values'], y=Ld['acceptance_rates'],
            mode='lines', name=f'L={L}', line=dict(color=colors[L], width=1),
        ))
    # Diagnostic: check if acceptance is suspiciously uniform
    all_acc = []
    for Ld in bc['data'].values():
        all_acc.extend(Ld.get('acceptance_rates', []))
    if all_acc:
        acc_std = np.std(all_acc)
        if acc_std < 0.02:
            fig.add_annotation(x=0.5, y=0.95, xref='paper', yref='paper',
                               text=f"⚠ Acceptance nearly uniform (std={acc_std:.4f}) — weak bond coupling?",
                               showarrow=False, font=dict(color='red', size=13), bgcolor='#fff3cd')
    fig.update_layout(title=f"Acceptance Rate vs Coupling{title_suffix}",
                      xaxis_title="Coupling", yaxis_title="Acceptance rate", legend_title="Lattice size")
    return fig


def _has_staggered_data(data: dict) -> bool:
    """Check if results contain staggered OP data."""
    bc = data.get('binder_crossing', {}).get('data', {})
    for Ld in bc.values():
        if 'binder_stag_tetrad' in Ld:
            return True
    fss = data.get('finite_size_scaling', {}).get('raw_results', [])
    if fss and 'binder_stag_tetrad' in fss[0]:
        return True
    return False


def fig_binder_staggered(data: dict, title_suffix: str = "") -> go.Figure:
    """Binder cumulant for staggered (antiferromagnetic) tetrad OP.

    This is the physically relevant OP for the NJL model. Shows the
    AF ordering transition where U4 rises from ~0 (disordered, non-Gaussian)
    to ~2/3 (ordered, Gaussian fluctuations around nonzero staggered mean).
    """
    # Try Binder section first
    bc = data.get('binder_crossing', {}).get('data', {})
    has_binder = any('binder_stag_tetrad' in Ld for Ld in bc.values())

    # Fall back to FSS raw results
    fss_raw = data.get('finite_size_scaling', {}).get('raw_results', [])
    has_fss = fss_raw and 'binder_stag_tetrad' in fss_raw[0]

    if has_binder:
        sizes = sorted(int(k) for k in bc.keys())
        colors = make_color_map(sizes, AMBERS)
        fig = go.Figure()
        for L in sizes:
            Ld = bc[str(L)]
            stag = Ld.get('binder_stag_tetrad', [])
            if not stag:
                continue
            fig.add_trace(go.Scatter(
                x=Ld['g_EH_values'], y=stag,
                mode='lines+markers', name=f'L={L}', marker=dict(size=4),
                line=dict(color=colors[L], width=1.5),
            ))
    elif has_fss:
        sizes = sorted(set(r['L'] for r in fss_raw))
        colors = make_color_map(sizes, AMBERS)
        fig = go.Figure()
        for L in sizes:
            pts = sorted([r for r in fss_raw if r['L'] == L], key=lambda r: r['ratio'])
            ratios = [r['ratio'] for r in pts]
            stag = [r.get('binder_stag_tetrad', 0) for r in pts]
            fig.add_trace(go.Scatter(
                x=ratios, y=stag,
                mode='lines+markers', name=f'L={L}', marker=dict(size=4),
                line=dict(color=colors[L], width=1.5),
            ))
    else:
        return go.Figure().update_layout(title=f"No staggered data{title_suffix}")

    fig.add_hline(y=2/3, line_dash="dash", line_color="gray", annotation_text="Gaussian (2/3)")
    fig.add_hline(y=0, line_dash="dot", line_color="lightgray")
    fig.update_layout(
        title=f"Staggered Tetrad Binder Cumulant (AF order parameter){title_suffix}",
        xaxis_title="Coupling", yaxis_title="U₄ (staggered tetrad)",
        legend_title="Lattice size",
    )
    return fig


def fig_chi_staggered(data: dict, title_suffix: str = "") -> go.Figure:
    """Staggered tetrad susceptibility vs coupling — divergence at transition."""
    fss_raw = data.get('finite_size_scaling', {}).get('raw_results', [])
    if not fss_raw or 'chi_stag_tetrad' not in fss_raw[0]:
        return go.Figure().update_layout(title=f"No staggered susceptibility data{title_suffix}")

    sizes = sorted(set(r['L'] for r in fss_raw))
    colors = make_color_map(sizes, AMBERS)

    fig = go.Figure()
    for L in sizes:
        pts = sorted([r for r in fss_raw if r['L'] == L], key=lambda r: r['ratio'])
        ratios = [r['ratio'] for r in pts]
        chi = [r.get('chi_stag_tetrad', 0) for r in pts]
        fig.add_trace(go.Scatter(
            x=ratios, y=chi,
            mode='lines+markers', name=f'L={L}', marker=dict(size=4),
            line=dict(color=colors[L], width=1.5),
        ))

    fig.update_layout(
        title=f"Staggered Tetrad Susceptibility (AF){title_suffix}",
        xaxis_title="Coupling", yaxis_title="χ_stag",
        legend_title="Lattice size",
        yaxis_type="log",
    )
    return fig


def fig_crossing_detail(data: dict, title_suffix: str = "") -> go.Figure:
    """Table of per-L-pair Binder crossings."""
    bc = data['binder_crossing']
    sizes = sorted(int(k) for k in bc['data'].keys())
    t_cross_raw = bc.get('tetrad_crossings', [])
    m_cross_raw = bc.get('metric_crossings', [])

    # Build lookup: (L_small, L_large) -> coupling value
    def _crossing_map(crossings):
        out = {}
        for c in crossings:
            if isinstance(c, dict):
                pair = tuple(c.get('L_pair', []))
                out[pair] = c.get('g_EH')
            elif isinstance(c, (int, float)):
                pass  # legacy scalar format, skip
        return out

    t_map = _crossing_map(t_cross_raw)
    m_map = _crossing_map(m_cross_raw)

    pairs = []
    t_vals = []
    m_vals = []
    window = []
    for i in range(len(sizes) - 1):
        pair = (sizes[i], sizes[i + 1])
        pairs.append(f"L={pair[0]}-{pair[1]}")
        t_val = t_map.get(pair)
        m_val = m_map.get(pair)
        t_vals.append(f"{t_val:.2f}" if t_val is not None else "—")
        m_vals.append(f"{m_val:.2f}" if m_val is not None else "—")
        if t_val is not None and m_val is not None:
            window.append(f"{t_val - m_val:.2f}")
        else:
            window.append("—")

    fig = go.Figure(data=[go.Table(
        header=dict(values=['L pair', 'Tetrad crossing', 'Metric crossing', 'Window (tet−met)'],
                    fill_color='#2E86AB', font=dict(color='white', size=13), align='center'),
        cells=dict(values=[pairs, t_vals, m_vals, window],
                   fill_color=[['white'] * len(pairs)] * 4,
                   font=dict(size=12), align='center', height=28),
    )])
    vestigial = bc.get('vestigial_detected', False)
    vw = bc.get('vestigial_window')
    status = f"Vestigial detected: {vestigial}" + (f" (window={vw:.4f})" if vw else "")
    fig.update_layout(title=f"Binder Crossing Detail{title_suffix}<br><sub>{status}</sub>", height=max(200, 60 + 30 * len(pairs)))
    return fig


# ── Summary text ──

def build_summary_text(data: dict, path: str) -> str:
    m = data.get('metadata', {})
    bc = data.get('binder_crossing', {})
    fss = data.get('finite_size_scaling', {})
    sr = data.get('sign_reweighting', [])
    model = detect_model(path, data)

    lines = []
    lines.append(f"<b>Model:</b> {model}  |  <b>File:</b> {Path(path).name}")
    lines.append(f"<b>Sizes:</b> {m.get('lattice_sizes', [])}")
    lines.append(f"<b>Sweeps:</b> {m.get('n_thermalize','?')} therm + {m.get('n_measure','?')} measure")
    lines.append(f"<b>Couplings:</b> {m.get('n_couplings','?')} points  |  <b>Cores:</b> {m.get('n_cores','?')}  |  <b>Seed:</b> {m.get('seed','?')}")
    lines.append(f"<b>Runtime:</b> {m.get('total_runtime_s',0)/3600:.1f} hours")
    lines.append("")
    lines.append(f"<b>Binder crossings:</b> tetrad={len(bc.get('tetrad_crossings',[]))}, metric={len(bc.get('metric_crossings',[]))}")
    lines.append(f"<b>Vestigial detected:</b> {bc.get('vestigial_detected', '?')}")
    if bc.get('vestigial_window'):
        lines.append(f"<b>Vestigial window:</b> {bc['vestigial_window']:.4f}")
    lines.append("")
    split = fss.get('split_transition', '?')
    lines.append(f"<b>Split transition (FSS):</b> {split}")

    peaks = fss.get('susceptibility_peaks', {})
    if peaks:
        sizes = sorted(int(k) for k in peaks.keys())
        L_max = sizes[-1]
        p = peaks[str(L_max)]
        lines.append(f"<b>Largest L={L_max}:</b> tet peak @ {p['tetrad_peak_coupling']:.2f}, met peak @ {p['metric_peak_coupling']:.2f}")

    # Staggered OP summary
    if _has_staggered_data(data):
        lines.append("")
        lines.append("<b>--- Staggered (AF) Order Parameter ---</b>")
        bc_data = bc.get('data', {})
        stag_binders = {}
        for L_str, Ld in bc_data.items():
            sb = Ld.get('binder_stag_tetrad', [])
            if sb:
                # Find max staggered Binder (near transition it's highest)
                stag_binders[int(L_str)] = max(sb) if isinstance(sb, list) else sb
        if stag_binders:
            for L in sorted(stag_binders):
                lines.append(f"  L={L}: max stag U₄ = {stag_binders[L]:.4f}")

    # Acceptance diagnostic
    all_acc = []
    for Ld in bc.get('data', {}).values():
        all_acc.extend(Ld.get('acceptance_rates', []))
    if all_acc:
        acc_mean = np.mean(all_acc)
        acc_std = np.std(all_acc)
        flag = " ⚠ UNIFORM" if acc_std < 0.02 else ""
        lines.append(f"<b>Acceptance:</b> mean={acc_mean:.3f}, std={acc_std:.4f}{flag}")

    if sr:
        max_sign = max(r['avg_sign'] for r in sr)
        lines.append(f"<b>Max ⟨sign⟩:</b> {max_sign:.2e}  |  Viable: {max_sign > 0.01}")

    return "<br>".join(lines)


# ── Dashboard builders ──

def build_single_dashboard(data: dict, path: str, output_path: str):
    from plotly.io import to_html
    model = detect_model(path, data)
    suffix = f" — {model}"

    figs = [
        ("Summary", None),
        ("Crossing Detail", fig_crossing_detail(data, suffix)),
        ("Binder — Tetrad", fig_binder_tetrad(data, suffix)),
        ("Binder — Metric", fig_binder_metric(data, suffix)),
    ]
    if _has_staggered_data(data):
        figs.append(("Binder — Staggered Tetrad (AF)", fig_binder_staggered(data, suffix)))
        figs.append(("Susceptibility — Staggered (AF)", fig_chi_staggered(data, suffix)))
    figs.extend([
        ("Susceptibility", fig_susceptibility(data, suffix)),
        ("Susceptibility (log)", fig_susceptibility(data, suffix, log_scale=True)),
        ("Peak Scaling", fig_peak_scaling(data, suffix)),
        ("Acceptance Rates", fig_acceptance(data, suffix)),
    ])

    summary_html = build_summary_text(data, path)
    title = f"Vestigial MC — {model} — {Path(path).stem}"
    _write_html(figs, summary_html, title, output_path)


def build_comparison_dashboard(data_a: dict, path_a: str, data_b: dict, path_b: str, output_path: str):
    from plotly.io import to_html
    model_a = detect_model(path_a, data_a)
    model_b = detect_model(path_b, data_b)

    figs = [
        ("Summary", None),
        (f"Crossing Detail — {model_a}", fig_crossing_detail(data_a, f" — {model_a}")),
        (f"Crossing Detail — {model_b}", fig_crossing_detail(data_b, f" — {model_b}")),
        (f"Binder Tetrad — {model_a}", fig_binder_tetrad(data_a, f" — {model_a}")),
        (f"Binder Tetrad — {model_b}", fig_binder_tetrad(data_b, f" — {model_b}")),
        (f"Binder Metric — {model_a}", fig_binder_metric(data_a, f" — {model_a}")),
        (f"Binder Metric — {model_b}", fig_binder_metric(data_b, f" — {model_b}")),
    ]
    for label, d in [(model_a, data_a), (model_b, data_b)]:
        if _has_staggered_data(d):
            figs.append((f"Staggered Binder (AF) — {label}", fig_binder_staggered(d, f" — {label}")))
            figs.append((f"Staggered χ (AF) — {label}", fig_chi_staggered(d, f" — {label}")))
    figs.extend([
        (f"Susceptibility — {model_a}", fig_susceptibility(data_a, f" — {model_a}")),
        (f"Susceptibility — {model_b}", fig_susceptibility(data_b, f" — {model_b}")),
        (f"Peak Scaling — {model_a}", fig_peak_scaling(data_a, f" — {model_a}")),
        (f"Peak Scaling — {model_b}", fig_peak_scaling(data_b, f" — {model_b}")),
        (f"Acceptance — {model_a}", fig_acceptance(data_a, f" — {model_a}")),
        (f"Acceptance — {model_b}", fig_acceptance(data_b, f" — {model_b}")),
    ])

    summary_a = build_summary_text(data_a, path_a)
    summary_b = build_summary_text(data_b, path_b)
    summary_html = (f'<div style="display:flex;gap:20px;">'
                    f'<div style="flex:1;padding:10px;border-right:2px solid #eee;">{summary_a}</div>'
                    f'<div style="flex:1;padding:10px;">{summary_b}</div></div>')

    title = f"Vestigial MC Comparison — {model_a} vs {model_b}"
    _write_html(figs, summary_html, title, output_path)


def _write_html(figs: list, summary_html: str, title: str, output_path: str):
    from plotly.io import to_html

    html_parts = [f"""<!DOCTYPE html>
<html><head>
<title>{title}</title>
<script src="https://cdn.plot.ly/plotly-latest.min.js"></script>
<style>
  body {{ font-family: -apple-system, BlinkMacSystemFont, sans-serif; margin: 20px; background: #fafafa; }}
  h1 {{ color: #1a1a2e; }}
  .summary {{ background: white; padding: 20px; border-radius: 8px;
             box-shadow: 0 1px 3px rgba(0,0,0,0.1); margin-bottom: 20px;
             font-size: 14px; line-height: 1.8; }}
  .fig-container {{ background: white; padding: 10px; border-radius: 8px;
                   box-shadow: 0 1px 3px rgba(0,0,0,0.1); margin-bottom: 20px; }}
  h2 {{ color: #2E86AB; margin-top: 30px; }}
  nav {{ position: sticky; top: 0; background: #1a1a2e; padding: 10px 20px;
        border-radius: 8px; margin-bottom: 20px; z-index: 100; display: flex; flex-wrap: wrap; gap: 5px; }}
  nav a {{ color: #4ECDC4; text-decoration: none; font-size: 13px; padding: 2px 8px; }}
  nav a:hover {{ text-decoration: underline; }}
</style>
</head><body>
<h1>{title}</h1>
<nav>"""]

    for i, (name, _) in enumerate(figs):
        html_parts.append(f'<a href="#fig{i}">{name}</a>')
    html_parts.append("</nav>")

    for i, (name, fig) in enumerate(figs):
        html_parts.append(f'<h2 id="fig{i}">{name}</h2>')
        if fig is None:
            html_parts.append(f'<div class="summary">{summary_html}</div>')
        else:
            fig_html = to_html(fig, full_html=False, include_plotlyjs=False)
            html_parts.append(f'<div class="fig-container">{fig_html}</div>')

    html_parts.append("</body></html>")

    with open(output_path, 'w') as f:
        f.write("\n".join(html_parts))
    print(f"Dashboard written to {output_path}")


# ── CLI ──

def main():
    parser = argparse.ArgumentParser(
        description="View vestigial MC results — single file or side-by-side comparison",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="Examples:\n"
               "  view_vestigial_mc.py                    # latest file\n"
               "  view_vestigial_mc.py --latest njl        # latest NJL\n"
               "  view_vestigial_mc.py --compare-models    # latest ADW vs NJL\n"
               "  view_vestigial_mc.py --compare A.json B.json\n"
               "  view_vestigial_mc.py --list              # show all results\n",
    )
    parser.add_argument('file', nargs='?', default=None, help='Path to vestigial_mc_*.json')
    parser.add_argument('--latest', choices=['njl', 'adw'], default=None,
                        help='View latest results for a specific model')
    parser.add_argument('--compare', nargs=2, metavar=('FILE_A', 'FILE_B'),
                        help='Compare two results files side-by-side')
    parser.add_argument('--compare-models', action='store_true',
                        help='Compare latest ADW vs latest NJL')
    parser.add_argument('--list', action='store_true', help='List all available results')
    parser.add_argument('--no-open', action='store_true', help='Do not auto-open in browser')
    args = parser.parse_args()

    Path("figures").mkdir(exist_ok=True)

    if args.list:
        list_results()
        return

    if args.compare_models:
        path_a = find_latest('adw')
        path_b = find_latest('njl')
        print(f"Comparing:\n  A: {path_a}\n  B: {path_b}")
        data_a = load_results(path_a)
        data_b = load_results(path_b)
        output = "figures/vestigial_mc_comparison.html"
        build_comparison_dashboard(data_a, path_a, data_b, path_b, output)
        if not args.no_open:
            import webbrowser
            webbrowser.open(f"file://{Path(output).resolve()}")
        return

    if args.compare:
        path_a, path_b = args.compare
        print(f"Comparing:\n  A: {path_a}\n  B: {path_b}")
        data_a = load_results(path_a)
        data_b = load_results(path_b)
        output = "figures/vestigial_mc_comparison.html"
        build_comparison_dashboard(data_a, path_a, data_b, path_b, output)
        if not args.no_open:
            import webbrowser
            webbrowser.open(f"file://{Path(output).resolve()}")
        return

    # Single file mode
    if args.latest:
        path = find_latest(args.latest)
    elif args.file:
        path = args.file
    else:
        path = find_latest()

    print(f"Loading: {path}")
    data = load_results(path)
    model = detect_model(path, data)
    timestamp = data.get('metadata', {}).get('timestamp', 'results')
    output = f"figures/vestigial_mc_dashboard_{model.lower()}_{timestamp}.html"

    build_single_dashboard(data, path, output)

    if not args.no_open:
        import webbrowser
        webbrowser.open(f"file://{Path(output).resolve()}")


if __name__ == '__main__':
    main()
