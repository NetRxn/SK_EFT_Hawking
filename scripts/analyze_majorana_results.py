#!/usr/bin/env python3
"""Analyze Majorana 8×8 production MC results.

Reads JSON output from run_majorana_production.py and produces:
1. Binder cumulant plots (U₄ vs g) for tetrad and metric
2. Order parameter magnitude vs coupling
3. Acceptance rates and autocorrelation diagnostics
4. Error bars from jackknife resampling
5. Summary table

Usage:
  uv run python scripts/analyze_majorana_results.py [path_to_json]
  uv run python scripts/analyze_majorana_results.py --latest
"""

import argparse
import json
import sys
import numpy as np
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))


def load_latest():
    """Find most recent majorana_8x8_*.json file."""
    data_dir = Path("docs/vestigial_mc_results")
    files = sorted(data_dir.glob("majorana_8x8_*.json"),
                   key=lambda p: p.stat().st_mtime)
    if not files:
        print("No majorana_8x8_*.json files found.")
        sys.exit(1)
    return files[-1]


def jackknife_error(samples, func=np.mean):
    """Jackknife estimate of standard error for func(samples)."""
    n = len(samples)
    if n < 2:
        return 0.0
    full = func(samples)
    jk = np.array([func(np.delete(samples, i)) for i in range(n)])
    return np.sqrt((n - 1) / n * np.sum((jk - full)**2))


def binder_from_history(tetrad_hist):
    """Compute Binder cumulant with jackknife error from raw measurements.

    For a d-component order parameter:
      U₄ = 1 - d/(d+2) · ⟨|φ|⁴⟩/⟨|φ|²⟩²

    Tetrad has d=16 → coefficient = 8/9
    """
    tet = np.array(tetrad_hist)
    m2_vals = tet**2  # |E|² per measurement
    m4_vals = tet**4  # |E|⁴ per measurement

    m2 = np.mean(m2_vals)
    m4 = np.mean(m4_vals)
    if m2 == 0:
        return 0.0, 0.0
    u4 = 1.0 - (8.0/9.0) * m4 / m2**2

    # Jackknife error
    def u4_func(x):
        m2_j = np.mean(x**2)
        m4_j = np.mean(x**4)
        if m2_j == 0:
            return 0.0
        return 1.0 - (8.0/9.0) * m4_j / m2_j**2
    err = jackknife_error(tet, u4_func)
    return u4, err


def metric_binder_from_history(metric_hist):
    """Metric Binder cumulant with jackknife error.

    Metric order parameter is traceless-symmetric 4×4 → d=9 → coefficient = 9/11
    """
    met = np.array(metric_hist)
    m2 = np.mean(met)
    m4 = np.mean(met**2)
    if m2 == 0:
        return 0.0, 0.0
    u4 = 1.0 - (9.0/11.0) * m4 / m2**2

    def u4_func(x):
        m2_j = np.mean(x)
        m4_j = np.mean(x**2)
        if m2_j == 0:
            return 0.0
        return 1.0 - (9.0/11.0) * m4_j / m2_j**2
    err = jackknife_error(met, u4_func)
    return u4, err


def analyze(data_path):
    """Analyze a single production result file."""
    with open(data_path) as f:
        data = json.load(f)

    print(f"File: {data_path}")
    print(f"Algorithm: {data.get('algorithm', 'unknown')}")
    print(f"Sign-free: {data.get('sign_free', 'unknown')}")
    print(f"Timestamp: {data.get('timestamp', 'unknown')}")
    print()

    params = data.get('parameters', {})
    print(f"Parameters: β={params.get('beta')}, "
          f"therm={params.get('n_therm')}, measure={params.get('n_measure')}, "
          f"skip={params.get('n_skip')}")
    print()

    for L_str, size_data in data.get('sizes', {}).items():
        L = int(L_str)
        elapsed = size_data.get('elapsed_seconds', 0)
        n_pts = size_data.get('n_points', 0)

        print(f"{'='*80}")
        print(f"  L={L}: {n_pts} coupling points, {elapsed:.0f}s ({elapsed/60:.1f} min)")
        print(f"{'='*80}")
        print()

        # Header
        print(f"{'g':>6} {'tet_m2':>10} {'U4_tet':>10} {'±err':>8} "
              f"{'met_m2':>10} {'U4_met':>10} {'±err':>8} "
              f"{'plaq':>8} {'acc_f':>7} {'acc_g':>7}")
        print(f"{'-'*90}")

        g_values = []
        u4_tet_values = []
        u4_tet_errors = []
        u4_met_values = []
        u4_met_errors = []
        tet_m2_values = []
        met_m2_values = []

        for pt in size_data.get('points', []):
            g = pt['g']
            g_values.append(g)

            # Recompute Binder with jackknife from full history
            tet_hist = pt.get('tetrad_magnitude_history', [])
            met_hist = pt.get('metric_trace_sq_history', [])

            if tet_hist:
                u4_t, u4_t_err = binder_from_history(tet_hist)
            else:
                u4_t = pt.get('binder_tetrad', 0)
                u4_t_err = 0

            if met_hist:
                u4_m, u4_m_err = metric_binder_from_history(met_hist)
            else:
                u4_m = pt.get('binder_metric', 0)
                u4_m_err = 0

            u4_tet_values.append(u4_t)
            u4_tet_errors.append(u4_t_err)
            u4_met_values.append(u4_m)
            u4_met_errors.append(u4_m_err)
            tet_m2_values.append(pt.get('tetrad_m2', 0))
            met_m2_values.append(pt.get('metric_m2', 0))

            print(f"{g:6.2f} {pt.get('tetrad_m2', 0):10.6f} "
                  f"{u4_t:10.6f} {u4_t_err:8.6f} "
                  f"{pt.get('metric_m2', 0):10.6f} "
                  f"{u4_m:10.6f} {u4_m_err:8.6f} "
                  f"{pt.get('avg_plaquette', 0):8.4f} "
                  f"{pt.get('acceptance_fermion', 0):7.3f} "
                  f"{pt.get('acceptance_gauge', 0):7.3f}")

        print()

        # Physics summary
        g_arr = np.array(g_values)
        u4t = np.array(u4_tet_values)
        u4m = np.array(u4_met_values)
        tm2 = np.array(tet_m2_values)
        mm2 = np.array(met_m2_values)

        print(f"  Tetrad U₄ range: [{u4t.min():.6f}, {u4t.max():.6f}]")
        print(f"  Metric U₄ range: [{u4m.min():.6f}, {u4m.max():.6f}]")
        print(f"  Tetrad ⟨m²⟩ range: [{tm2.min():.6f}, {tm2.max():.6f}]")
        print(f"  Metric ⟨trQ²⟩ range: [{mm2.min():.6f}, {mm2.max():.6f}]")

        # Check for ordering signal
        if u4t.max() - u4t.min() > 0.01:
            print(f"  ** TETRAD ORDERING SIGNAL: ΔU₄ = {u4t.max()-u4t.min():.4f}")
            # Estimate crossing from max gradient
            du4 = np.diff(u4t) / np.diff(g_arr)
            i_max = np.argmax(np.abs(du4))
            g_cross = 0.5 * (g_arr[i_max] + g_arr[i_max+1])
            print(f"    Steepest change at g ≈ {g_cross:.2f}")
        else:
            print(f"  Tetrad: weak signal (ΔU₄ = {u4t.max()-u4t.min():.6f})")

        if u4m.max() - u4m.min() > 0.01:
            print(f"  ** METRIC ORDERING SIGNAL: ΔU₄ = {u4m.max()-u4m.min():.4f}")
            du4 = np.diff(u4m) / np.diff(g_arr)
            i_max = np.argmax(np.abs(du4))
            g_cross = 0.5 * (g_arr[i_max] + g_arr[i_max+1])
            print(f"    Steepest change at g ≈ {g_cross:.2f}")
        else:
            print(f"  Metric: weak signal (ΔU₄ = {u4m.max()-u4m.min():.6f})")

        # Vestigial phase check
        if (u4t.max() - u4t.min() > 0.01 and u4m.max() - u4m.min() > 0.01):
            du4t = np.diff(u4t) / np.diff(g_arr)
            du4m = np.diff(u4m) / np.diff(g_arr)
            i_tet = np.argmax(np.abs(du4t))
            i_met = np.argmax(np.abs(du4m))
            g_tet = 0.5 * (g_arr[i_tet] + g_arr[i_tet+1])
            g_met = 0.5 * (g_arr[i_met] + g_arr[i_met+1])
            if abs(g_tet - g_met) > 0.3:
                print(f"\n  ** VESTIGIAL PHASE CANDIDATE **")
                print(f"    Tetrad transition: g ≈ {g_tet:.2f}")
                print(f"    Metric transition: g ≈ {g_met:.2f}")
                print(f"    Split: Δg ≈ {abs(g_tet-g_met):.2f}")
            else:
                print(f"\n  Single transition at g ≈ {0.5*(g_tet+g_met):.2f}")

        print()


def main():
    parser = argparse.ArgumentParser(description="Analyze Majorana 8x8 MC results")
    parser.add_argument("path", nargs="?", help="Path to JSON results file")
    parser.add_argument("--latest", action="store_true", help="Use most recent file")
    args = parser.parse_args()

    if args.path:
        path = Path(args.path)
    else:
        path = load_latest()

    analyze(path)


if __name__ == "__main__":
    main()
