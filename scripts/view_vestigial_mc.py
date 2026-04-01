#!/usr/bin/env python3
"""Interactive viewer for vestigial MC results.

Generates Plotly HTML dashboard from any vestigial_mc_*.json results file.
Opens in browser automatically.

Usage:
  python scripts/view_vestigial_mc.py docs/vestigial_mc_results/vestigial_mc_20260330T164110.json
  python scripts/view_vestigial_mc.py  # uses latest file in results dir
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


def load_results(path: str) -> dict:
    with open(path) as f:
        return json.load(f)


def find_latest_results() -> str:
    results_dir = Path("docs/vestigial_mc_results")
    files = sorted(results_dir.glob("vestigial_mc_*.json"), key=lambda p: p.stat().st_mtime)
    if not files:
        print("No results files found in docs/vestigial_mc_results/")
        sys.exit(1)
    return str(files[-1])


def make_color_map(sizes: list[int], palette: list[str]) -> dict[int, str]:
    """Map lattice sizes to colors, cycling through palette."""
    return {L: palette[i % len(palette)] for i, L in enumerate(sizes)}


def fig_binder_tetrad(data: dict) -> go.Figure:
    """Binder cumulant U4 for tetrad order parameter vs g_EH, one trace per L."""
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
    fig.add_hline(y=2/3, line_dash="dash", line_color="gray",
                  annotation_text="Gaussian (2/3)")
    fig.update_layout(
        title="Binder Cumulant — Tetrad Order Parameter",
        xaxis_title="g_EH", yaxis_title="U₄ (tetrad)",
        legend_title="Lattice size",
    )
    return fig


def fig_binder_metric(data: dict) -> go.Figure:
    """Binder cumulant U4 for metric order parameter vs g_EH, one trace per L."""
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
    fig.add_hline(y=2/3, line_dash="dash", line_color="gray",
                  annotation_text="Gaussian (2/3)")
    fig.update_layout(
        title="Binder Cumulant — Metric Order Parameter",
        xaxis_title="g_EH", yaxis_title="U₄ (metric)",
        legend_title="Lattice size",
    )
    return fig


def fig_susceptibility(data: dict) -> go.Figure:
    """Susceptibility (tetrad and metric) vs G/G_c from FSS raw results."""
    fss = data['finite_size_scaling']
    raw = fss.get('raw_results', [])
    if not raw:
        return go.Figure().update_layout(title="No FSS raw_results available")

    sizes = sorted(set(r['L'] for r in raw))
    colors_t = make_color_map(sizes, BLUES)
    colors_m = make_color_map(sizes, REDS)

    fig = make_subplots(rows=2, cols=1, shared_xaxes=True,
                        subplot_titles=["Tetrad Susceptibility χ_tet",
                                        "Metric Susceptibility χ_met"])
    for L in sizes:
        pts = sorted([r for r in raw if r['L'] == L], key=lambda r: r['ratio'])
        ratios = [r['ratio'] for r in pts]
        chi_t = [r['chi_tetrad'] for r in pts]
        chi_m = [r['chi_metric'] for r in pts]

        fig.add_trace(go.Scatter(
            x=ratios, y=chi_t, mode='lines+markers', name=f'L={L}',
            marker=dict(size=4), line=dict(color=colors_t[L], width=1.5),
            legendgroup=f'L{L}', showlegend=True,
        ), row=1, col=1)
        fig.add_trace(go.Scatter(
            x=ratios, y=chi_m, mode='lines+markers', name=f'L={L}',
            marker=dict(size=4), line=dict(color=colors_m[L], width=1.5),
            legendgroup=f'L{L}', showlegend=False,
        ), row=2, col=1)

    fig.update_xaxes(title_text="G / G_c", row=2, col=1)
    fig.update_yaxes(title_text="χ_tet", row=1, col=1)
    fig.update_yaxes(title_text="χ_met", row=2, col=1)
    fig.update_layout(title="Susceptibility vs Coupling (FSS)", height=700,
                      legend_title="Lattice size")
    return fig


def fig_susceptibility_log(data: dict) -> go.Figure:
    """Same as susceptibility but log scale on y-axis to see all sizes."""
    fss = data['finite_size_scaling']
    raw = fss.get('raw_results', [])
    if not raw:
        return go.Figure().update_layout(title="No FSS raw_results available")

    sizes = sorted(set(r['L'] for r in raw))
    colors_t = make_color_map(sizes, BLUES)
    colors_m = make_color_map(sizes, REDS)

    fig = make_subplots(rows=2, cols=1, shared_xaxes=True,
                        subplot_titles=["Tetrad Susceptibility χ_tet (log)",
                                        "Metric Susceptibility χ_met (log)"])
    for L in sizes:
        pts = sorted([r for r in raw if r['L'] == L], key=lambda r: r['ratio'])
        ratios = [r['ratio'] for r in pts]
        chi_t = [max(r['chi_tetrad'], 1e-10) for r in pts]
        chi_m = [max(r['chi_metric'], 1e-10) for r in pts]

        fig.add_trace(go.Scatter(
            x=ratios, y=chi_t, mode='lines+markers', name=f'L={L}',
            marker=dict(size=4), line=dict(color=colors_t[L], width=1.5),
            legendgroup=f'L{L}', showlegend=True,
        ), row=1, col=1)
        fig.add_trace(go.Scatter(
            x=ratios, y=chi_m, mode='lines+markers', name=f'L={L}',
            marker=dict(size=4), line=dict(color=colors_m[L], width=1.5),
            legendgroup=f'L{L}', showlegend=False,
        ), row=2, col=1)

    fig.update_yaxes(type="log", row=1, col=1)
    fig.update_yaxes(type="log", row=2, col=1)
    fig.update_xaxes(title_text="G / G_c", row=2, col=1)
    fig.update_layout(title="Susceptibility vs Coupling — Log Scale (FSS)", height=700,
                      legend_title="Lattice size")
    return fig


def fig_peak_locations(data: dict) -> go.Figure:
    """Susceptibility peak coupling vs L — shows whether peaks converge or drift."""
    fss = data['finite_size_scaling']
    peaks = fss.get('susceptibility_peaks', {})
    if not peaks:
        return go.Figure().update_layout(title="No susceptibility peaks available")

    sizes = sorted(int(k) for k in peaks.keys())
    tet_peaks = [peaks[str(L)]['tetrad_peak_coupling'] for L in sizes]
    met_peaks = [peaks[str(L)]['metric_peak_coupling'] for L in sizes]

    fig = go.Figure()
    fig.add_trace(go.Scatter(
        x=sizes, y=tet_peaks, mode='lines+markers', name='Tetrad peak',
        marker=dict(size=8, color='#2E86AB'), line=dict(width=2),
    ))
    fig.add_trace(go.Scatter(
        x=sizes, y=met_peaks, mode='lines+markers', name='Metric peak',
        marker=dict(size=8, color='#E63946'), line=dict(width=2),
    ))
    # Coupling range boundaries
    cr = fss.get('coupling_range', [0.5, 5.0])
    fig.add_hline(y=cr[1], line_dash="dot", line_color="gray",
                  annotation_text=f"Scan boundary ({cr[1]})")
    fig.update_layout(
        title="Susceptibility Peak Location vs Lattice Size",
        xaxis_title="L", yaxis_title="Peak coupling (G/G_c)",
        yaxis_range=[cr[0] - 0.1, cr[1] + 0.3],
    )
    return fig


def fig_peak_heights(data: dict) -> go.Figure:
    """Susceptibility peak height vs L^4 — volume scaling check."""
    fss = data['finite_size_scaling']
    peaks = fss.get('susceptibility_peaks', {})
    if not peaks:
        return go.Figure().update_layout(title="No susceptibility peaks available")

    sizes = sorted(int(k) for k in peaks.keys())
    tet_h = [peaks[str(L)]['tetrad_peak_height'] for L in sizes]
    met_h = [peaks[str(L)]['metric_peak_height'] for L in sizes]
    volumes = [L**4 for L in sizes]

    fig = make_subplots(rows=1, cols=2,
                        subplot_titles=["Peak Height vs L", "Peak Height / Volume vs L"])

    fig.add_trace(go.Scatter(
        x=sizes, y=tet_h, mode='lines+markers', name='χ_tet peak',
        marker=dict(size=6, color='#2E86AB'),
    ), row=1, col=1)
    fig.add_trace(go.Scatter(
        x=sizes, y=met_h, mode='lines+markers', name='χ_met peak',
        marker=dict(size=6, color='#E63946'),
    ), row=1, col=1)

    # Normalize by volume — if ~constant, it's trivial volume scaling (disordered)
    # If diverging, it's a real phase transition
    fig.add_trace(go.Scatter(
        x=sizes, y=[h / v for h, v in zip(tet_h, volumes)],
        mode='lines+markers', name='χ_tet / V',
        marker=dict(size=6, color='#2E86AB'), showlegend=False,
    ), row=1, col=2)
    fig.add_trace(go.Scatter(
        x=sizes, y=[h / v for h, v in zip(met_h, volumes)],
        mode='lines+markers', name='χ_met / V',
        marker=dict(size=6, color='#E63946'), showlegend=False,
    ), row=1, col=2)

    fig.update_yaxes(type="log", row=1, col=1, title_text="Peak height")
    fig.update_yaxes(type="log", row=1, col=2, title_text="Peak height / L⁴")
    fig.update_xaxes(title_text="L", row=1, col=1)
    fig.update_xaxes(title_text="L", row=1, col=2)
    fig.update_layout(title="Susceptibility Peak Heights — Volume Scaling Check",
                      height=450, width=900)
    return fig


def fig_fss_binder(data: dict) -> go.Figure:
    """Binder cumulant from FSS section vs G/G_c, one trace per L."""
    fss = data['finite_size_scaling']
    raw = fss.get('raw_results', [])
    if not raw:
        return go.Figure().update_layout(title="No FSS raw_results available")

    sizes = sorted(set(r['L'] for r in raw))
    colors = make_color_map(sizes, BLUES)

    fig = make_subplots(rows=2, cols=1, shared_xaxes=True,
                        subplot_titles=["FSS Binder — Tetrad", "FSS Binder — Metric"])
    for L in sizes:
        pts = sorted([r for r in raw if r['L'] == L], key=lambda r: r['ratio'])
        ratios = [r['ratio'] for r in pts]
        bt = [r.get('binder_tetrad', 0) for r in pts]
        bm = [r.get('binder_metric', 0) for r in pts]

        fig.add_trace(go.Scatter(
            x=ratios, y=bt, mode='lines+markers', name=f'L={L}',
            marker=dict(size=4), line=dict(color=colors[L], width=1.5),
            legendgroup=f'L{L}', showlegend=True,
        ), row=1, col=1)
        fig.add_trace(go.Scatter(
            x=ratios, y=bm, mode='lines+markers', name=f'L={L}',
            marker=dict(size=4), line=dict(color=colors[L], width=1.5),
            legendgroup=f'L{L}', showlegend=False,
        ), row=2, col=1)

    fig.add_hline(y=2/3, line_dash="dash", line_color="gray", row=1, col=1)
    fig.add_hline(y=2/3, line_dash="dash", line_color="gray", row=2, col=1)
    fig.update_xaxes(title_text="G / G_c", row=2, col=1)
    fig.update_layout(title="FSS Binder Cumulants vs Coupling", height=700,
                      legend_title="Lattice size")
    return fig


def fig_sign_reweighting(data: dict) -> go.Figure:
    """Average sign vs coupling for each L."""
    sr = data.get('sign_reweighting', [])
    if not sr:
        return go.Figure().update_layout(title="No sign reweighting data")

    sizes = sorted(set(r['L'] for r in sr))
    colors = make_color_map(sizes, BLUES)

    fig = go.Figure()
    for L in sizes:
        pts = sorted([r for r in sr if r['L'] == L], key=lambda r: r['coupling'])
        couplings = [r['coupling'] for r in pts]
        signs = [r['avg_sign'] for r in pts]
        errs = [r['avg_sign_err'] for r in pts]

        fig.add_trace(go.Scatter(
            x=couplings, y=signs, mode='lines+markers', name=f'L={L}',
            marker=dict(size=6, color=colors[L]),
            error_y=dict(type='data', array=errs, visible=True),
        ))

    fig.add_hline(y=0.5, line_dash="dash", line_color="gray",
                  annotation_text="Viability threshold")
    fig.update_layout(
        title="Sign Reweighting: ⟨sign⟩ vs G/G_c",
        xaxis_title="G / G_c", yaxis_title="⟨sign⟩",
        legend_title="Lattice size",
    )
    return fig


def fig_acceptance(data: dict) -> go.Figure:
    """Acceptance rate vs coupling for Binder section."""
    bc = data['binder_crossing']
    sizes = sorted(int(k) for k in bc['data'].keys())
    colors = make_color_map(sizes, BLUES)

    fig = go.Figure()
    for L in sizes:
        Ld = bc['data'][str(L)]
        fig.add_trace(go.Scatter(
            x=Ld['g_EH_values'], y=Ld['acceptance_rates'],
            mode='lines', name=f'L={L}',
            line=dict(color=colors[L], width=1),
        ))
    fig.update_layout(
        title="Metropolis Acceptance Rate vs Coupling (Binder Section)",
        xaxis_title="g_EH", yaxis_title="Acceptance rate",
        legend_title="Lattice size",
    )
    return fig


def build_summary_text(data: dict) -> str:
    """Generate text summary of key results."""
    m = data.get('metadata', {})
    bc = data.get('binder_crossing', {})
    fss = data.get('finite_size_scaling', {})
    sr = data.get('sign_reweighting', [])

    lines = []
    lines.append(f"<b>Run:</b> {m.get('timestamp', '?')}")
    lines.append(f"<b>Sizes:</b> {m.get('lattice_sizes', [])}")
    lines.append(f"<b>Sweeps:</b> {m.get('n_thermalize','?')} therm + {m.get('n_measure','?')} measure")
    lines.append(f"<b>Couplings:</b> {m.get('n_couplings','?')} points")
    lines.append(f"<b>Cores:</b> {m.get('n_cores','?')}  |  <b>Seed:</b> {m.get('seed','?')}")
    lines.append(f"<b>Runtime:</b> {m.get('total_runtime_s',0)/3600:.1f} hours")
    lines.append("")

    # Binder
    lines.append(f"<b>Binder crossings:</b> tetrad={len(bc.get('tetrad_crossings',[]))}, "
                 f"metric={len(bc.get('metric_crossings',[]))}")
    lines.append(f"<b>Vestigial detected:</b> {bc.get('vestigial_detected', '?')}")
    if bc.get('vestigial_window'):
        lines.append(f"<b>Vestigial window:</b> {bc['vestigial_window']:.4f}")
    lines.append("")

    # FSS
    split = fss.get('split_transition', {})
    if isinstance(split, dict):
        lines.append(f"<b>Split transition:</b> {split.get('detected', split)}")
    else:
        lines.append(f"<b>Split transition:</b> {split}")
    cr = fss.get('coupling_range', [])
    lines.append(f"<b>FSS coupling range:</b> {cr}")
    lines.append("")

    # Peak summary
    peaks = fss.get('susceptibility_peaks', {})
    if peaks:
        sizes = sorted(int(k) for k in peaks.keys())
        L_max = sizes[-1]
        p = peaks[str(L_max)]
        lines.append(f"<b>Largest L={L_max} peaks:</b>")
        lines.append(f"  Tetrad: G/Gc={p['tetrad_peak_coupling']:.3f} (height={p['tetrad_peak_height']:.1f})")
        lines.append(f"  Metric: G/Gc={p['metric_peak_coupling']:.3f} (height={p['metric_peak_height']:.1e})")
        boundary = cr[1] if cr else 5.0
        at_boundary = p['metric_peak_coupling'] >= boundary - 0.15
        lines.append(f"  <b>Metric peak at scan boundary:</b> {'YES' if at_boundary else 'No'}")

    # Sign
    if sr:
        max_sign = max(r['avg_sign'] for r in sr)
        lines.append("")
        lines.append(f"<b>Max ⟨sign⟩:</b> {max_sign:.6f}")
        lines.append(f"<b>Sign viable (>0.01):</b> {max_sign > 0.01}")

    return "<br>".join(lines)


def build_dashboard(data: dict, output_path: str):
    """Build full HTML dashboard with all figures."""
    from plotly.io import to_html

    figs = [
        ("Summary", None),
        ("Binder — Tetrad", fig_binder_tetrad(data)),
        ("Binder — Metric", fig_binder_metric(data)),
        ("Susceptibility (linear)", fig_susceptibility(data)),
        ("Susceptibility (log)", fig_susceptibility_log(data)),
        ("Peak Locations vs L", fig_peak_locations(data)),
        ("Peak Heights / Volume Scaling", fig_peak_heights(data)),
        ("FSS Binder Cumulants", fig_fss_binder(data)),
        ("Sign Reweighting", fig_sign_reweighting(data)),
        ("Acceptance Rates", fig_acceptance(data)),
    ]

    summary_html = build_summary_text(data)
    timestamp = data.get('metadata', {}).get('timestamp', 'unknown')

    html_parts = [f"""<!DOCTYPE html>
<html><head>
<title>Vestigial MC Results — {timestamp}</title>
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
        border-radius: 8px; margin-bottom: 20px; z-index: 100; }}
  nav a {{ color: #4ECDC4; text-decoration: none; margin-right: 15px; font-size: 13px; }}
  nav a:hover {{ text-decoration: underline; }}
</style>
</head><body>
<h1>Vestigial MC Results — {timestamp}</h1>
<nav>"""]

    for i, (name, _) in enumerate(figs):
        anchor = f"fig{i}"
        html_parts.append(f'<a href="#{anchor}">{name}</a>')

    html_parts.append("</nav>")

    for i, (name, fig) in enumerate(figs):
        anchor = f"fig{i}"
        html_parts.append(f'<h2 id="{anchor}">{name}</h2>')
        if fig is None:
            html_parts.append(f'<div class="summary">{summary_html}</div>')
        else:
            fig_html = to_html(fig, full_html=False, include_plotlyjs=False)
            html_parts.append(f'<div class="fig-container">{fig_html}</div>')

    html_parts.append("</body></html>")

    with open(output_path, 'w') as f:
        f.write("\n".join(html_parts))

    print(f"Dashboard written to {output_path}")


def main():
    parser = argparse.ArgumentParser(description="View vestigial MC results")
    parser.add_argument('file', nargs='?', default=None,
                        help='Path to vestigial_mc_*.json (default: latest)')
    parser.add_argument('--no-open', action='store_true',
                        help='Do not auto-open in browser')
    args = parser.parse_args()

    path = args.file or find_latest_results()
    print(f"Loading: {path}")
    data = load_results(path)

    timestamp = data.get('metadata', {}).get('timestamp', 'results')
    output = f"figures/vestigial_mc_dashboard_{timestamp}.html"
    Path("figures").mkdir(exist_ok=True)

    build_dashboard(data, output)

    if not args.no_open:
        import webbrowser
        webbrowser.open(f"file://{Path(output).resolve()}")


if __name__ == '__main__':
    main()
