#!/usr/bin/env python3
"""Production vestigial MC runs: 4D fermion-bag finite-size scaling.

Runs the go/no-go analysis for the vestigial metric phase:
  - L=4, 6, 8 lattice sizes (4D hypercubic)
  - Binder cumulant crossing analysis
  - Susceptibility peak analysis
  - Sign reweighting check (verifies no sign problem)
  - Finite-size scaling to determine if vestigial phase survives

Uses multiprocessing to parallelize across coupling points (16 cores).
Vectorized MC inner loops for ~10-50× speedup per core.

Expected runtime (with optimizations, 16 cores):
  L=4,6: ~10-30 min
  L=4,6,8: ~1-4 hours

Usage:
  # Quick test (L=4 only, reduced statistics)
  python scripts/run_vestigial_production.py --quick

  # Production run (L=4,6,8, full statistics, 16 cores)
  python scripts/run_vestigial_production.py --production

  # Custom
  python scripts/run_vestigial_production.py --sizes 4 6 --sweeps 2000 --cores 8

Output: results saved to docs/vestigial_mc_results/ as JSON + real-time log.
"""

import argparse
import json
import time
import sys
import os
import logging
from datetime import datetime
from pathlib import Path
from multiprocessing import Pool, cpu_count

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent.parent))


# ── Logging setup (real-time, no buffering) ──

def setup_logging(log_dir: Path, timestamp: str) -> logging.Logger:
    """Configure logger that writes to both console and file in real-time."""
    log_dir.mkdir(parents=True, exist_ok=True)
    log_file = log_dir / f"vestigial_mc_{timestamp}.log"

    logger = logging.getLogger("vestigial_mc")
    logger.setLevel(logging.INFO)

    # File handler (immediate flush)
    fh = logging.FileHandler(log_file, mode='w')
    fh.setLevel(logging.INFO)
    fh.setFormatter(logging.Formatter('%(asctime)s %(message)s', datefmt='%H:%M:%S'))

    # Console handler
    ch = logging.StreamHandler(sys.stdout)
    ch.setLevel(logging.INFO)
    ch.setFormatter(logging.Formatter('%(asctime)s %(message)s', datefmt='%H:%M:%S'))

    logger.addHandler(fh)
    logger.addHandler(ch)

    return logger


# ── Worker functions for multiprocessing ──

def _run_single_fermion_bag(args):
    """Worker: run one fermion-bag MC at a single (L, g_EH) point.

    Must be a top-level function for multiprocessing.
    """
    from src.vestigial.fermion_bag import FermionBagParams, run_fermion_bag_mc
    from src.vestigial.lattice_4d import Lattice4DParams

    L, g_cosmo, g_EH, n_thermalize, n_measure, n_skip, seed = args
    params = Lattice4DParams(L=L, g_cosmo=g_cosmo, g_EH=g_EH)
    mc_params = FermionBagParams(
        n_thermalize=n_thermalize, n_measure=n_measure,
        n_skip=n_skip, seed=seed,
    )
    result = run_fermion_bag_mc(params, mc_params)
    return {
        'L': L, 'g_EH': g_EH,
        'binder_tetrad': result.binder_tetrad,
        'binder_metric': result.binder_metric,
        'metric_correlator': result.metric_correlator,
        'phase': result.phase,
        'acceptance_rate': result.acceptance_rate,
        'action_mean': result.action_mean,
    }


def _run_single_fss_point(args):
    """Worker: run one finite-size scaling point at (L, coupling_ratio)."""
    from src.vestigial.monte_carlo import MCParams, run_monte_carlo
    from src.vestigial.lattice_model import LatticeParams
    from src.adw.gap_equation import critical_coupling
    import numpy as np

    L, ratio, n_thermalize, n_measure, n_skip, step_size, seed, N_f = args
    Lambda = 1.0
    G_c = critical_coupling(Lambda, N_f)
    lattice_params = LatticeParams(L=L, d=4, G=ratio * G_c, N_f=N_f)
    mc_params = MCParams(
        n_thermalize=n_thermalize, n_measure=n_measure,
        n_skip=n_skip, step_size=step_size, seed=seed,
    )
    mc_result = run_monte_carlo(lattice_params, mc_params)

    # Compute moments for Binder cumulants
    tetrad_mags = [m.tetrad_vev for m in mc_result.measurements]
    metric_mags = [m.metric_mag for m in mc_result.measurements]
    V = L**4

    tetrad_m2 = float(np.mean(np.array(tetrad_mags)**2))
    tetrad_m4 = float(np.mean(np.array(tetrad_mags)**4))
    metric_m2 = float(np.mean(np.array(metric_mags)**2))
    metric_m4 = float(np.mean(np.array(metric_mags)**4))

    chi_t = V * (np.mean(np.array(tetrad_mags)**2) - np.mean(np.abs(tetrad_mags))**2)
    chi_m = V * (np.mean(np.array(metric_mags)**2) - np.mean(np.abs(metric_mags))**2)

    return {
        'L': L, 'ratio': ratio,
        'tetrad_m2': tetrad_m2, 'tetrad_m4': tetrad_m4,
        'metric_m2': metric_m2, 'metric_m4': metric_m4,
        'chi_tetrad': float(chi_t), 'chi_metric': float(chi_m),
        'acceptance_rate': mc_result.overall_acceptance,
    }


def _run_sign_check(args):
    """Worker: run sign reweighting at one (L, coupling) point."""
    from src.vestigial.finite_size import sign_reweighting
    from src.vestigial.monte_carlo import MCParams

    coupling, L, n_thermalize, n_measure, n_skip, step_size, seed = args
    mc_params = MCParams(
        n_thermalize=n_thermalize, n_measure=n_measure,
        n_skip=n_skip, step_size=step_size, seed=seed,
    )
    sr = sign_reweighting(coupling, L, mc_params)
    return {
        'coupling': coupling, 'L': L,
        'avg_sign': sr.avg_sign, 'avg_sign_err': sr.avg_sign_err,
    }


# ── Main production run ──

def run_production(lattice_sizes, n_measure, n_thermalize, n_couplings, seed,
                   n_cores, log):
    """Run the full production analysis with multiprocessing."""
    import numpy as np
    from src.core.constants import ADW_4D_COUPLING_SCAN
    from src.core.formulas import binder_cumulant

    output_dir = Path("docs/vestigial_mc_results")
    output_dir.mkdir(parents=True, exist_ok=True)
    timestamp = datetime.now().strftime("%Y%m%dT%H%M%S")

    log.info("=" * 60)
    log.info("  Vestigial MC Production Run (vectorized + multiprocessing)")
    log.info(f"  Lattice sizes: {lattice_sizes}")
    log.info(f"  Sweeps: {n_thermalize} thermalize + {n_measure} measure")
    log.info(f"  Couplings: {n_couplings} points")
    log.info(f"  Cores: {n_cores}")
    log.info(f"  Seed: {seed}")
    log.info(f"  Started: {datetime.now().isoformat()}")
    log.info("=" * 60)

    results = {}
    g_cosmo = ADW_4D_COUPLING_SCAN['g_cosmo']
    g_EH_range = ADW_4D_COUPLING_SCAN['g_EH_range']
    g_values = np.linspace(g_EH_range[0], g_EH_range[1], n_couplings)

    # ── 1. 4D Binder crossing (parallelized across L × coupling) ──
    log.info("\n[1/3] 4D Binder cumulant crossing analysis...")
    t0 = time.time()

    # Build job list: all (L, g_EH) pairs
    jobs = []
    for L in lattice_sizes:
        for i, g_EH in enumerate(g_values):
            # Each job gets a unique seed to avoid correlation
            job_seed = seed + L * 1000 + i
            jobs.append((L, g_cosmo, g_EH, n_thermalize, n_measure, 5, job_seed))

    log.info(f"  Dispatching {len(jobs)} jobs across {n_cores} cores...")

    with Pool(n_cores) as pool:
        raw_results = pool.map(_run_single_fermion_bag, jobs)

    t_crossing = time.time() - t0
    log.info(f"  Completed {len(raw_results)} jobs in {t_crossing:.1f}s")

    # Assemble results by L
    crossing_data = {}
    for L in lattice_sizes:
        L_results = [r for r in raw_results if r['L'] == L]
        L_results.sort(key=lambda r: r['g_EH'])
        crossing_data[L] = {
            'g_EH_values': [r['g_EH'] for r in L_results],
            'binder_tetrad': [r['binder_tetrad'] for r in L_results],
            'binder_metric': [r['binder_metric'] for r in L_results],
            'phases': [r['phase'] for r in L_results],
            'acceptance_rates': [r['acceptance_rate'] for r in L_results],
        }
        log.info(f"  L={L}: mean acceptance={np.mean(crossing_data[L]['acceptance_rates']):.3f}")

    # Find crossings
    tetrad_crossing = None
    metric_crossing = None
    if len(lattice_sizes) >= 2:
        L_small, L_large = lattice_sizes[0], lattice_sizes[-1]
        bt_small = np.array(crossing_data[L_small]['binder_tetrad'])
        bt_large = np.array(crossing_data[L_large]['binder_tetrad'])
        bm_small = np.array(crossing_data[L_small]['binder_metric'])
        bm_large = np.array(crossing_data[L_large]['binder_metric'])

        def _find_crossing(g_vals, b1, b2):
            diff = b1 - b2
            for i in range(len(diff) - 1):
                if diff[i] * diff[i+1] < 0:
                    t = diff[i] / (diff[i] - diff[i+1])
                    return float(g_vals[i] + t * (g_vals[i+1] - g_vals[i]))
            return None

        tetrad_crossing = _find_crossing(g_values, bt_small, bt_large)
        metric_crossing = _find_crossing(g_values, bm_small, bm_large)

    vestigial_window = None
    vestigial_detected = False
    if tetrad_crossing is not None and metric_crossing is not None:
        window = abs(metric_crossing - tetrad_crossing)
        if window > 0.01:
            vestigial_window = window
            vestigial_detected = True

    log.info(f"  Tetrad crossing: {tetrad_crossing}")
    log.info(f"  Metric crossing: {metric_crossing}")
    log.info(f"  Vestigial window: {vestigial_window}")
    log.info(f"  Vestigial detected: {vestigial_detected}")

    results['binder_crossing'] = {
        'lattice_sizes': lattice_sizes,
        'tetrad_crossing': tetrad_crossing,
        'metric_crossing': metric_crossing,
        'vestigial_window': vestigial_window,
        'vestigial_detected': vestigial_detected,
        'data': {str(L): crossing_data[L] for L in lattice_sizes},
        'runtime_s': t_crossing,
    }

    # ── 2. Finite-size scaling (parallelized) ──
    log.info("\n[2/3] Finite-size scaling analysis...")
    t0 = time.time()

    coupling_range = (0.5, 2.5)
    ratios = np.linspace(coupling_range[0], coupling_range[1], n_couplings)
    N_f = 4

    fss_jobs = []
    for L in lattice_sizes:
        for i, r in enumerate(ratios):
            job_seed = seed + L * 1000 + i + 500
            fss_jobs.append((L, r, n_thermalize, n_measure, 5, 0.3, job_seed, N_f))

    log.info(f"  Dispatching {len(fss_jobs)} FSS jobs across {n_cores} cores...")

    with Pool(n_cores) as pool:
        fss_results = pool.map(_run_single_fss_point, fss_jobs)

    t_fss = time.time() - t0
    log.info(f"  Completed {len(fss_results)} FSS jobs in {t_fss:.1f}s")

    # Analyze FSS results
    fss_data = {}
    for L in lattice_sizes:
        L_results = sorted([r for r in fss_results if r['L'] == L],
                          key=lambda r: r['ratio'])
        fss_data[L] = L_results

        # Binder cumulants
        for r in L_results:
            m2, m4 = r['tetrad_m2'], r['tetrad_m4']
            r['binder_tetrad'] = binder_cumulant(m2, m4)
            m2, m4 = r['metric_m2'], r['metric_m4']
            r['binder_metric'] = binder_cumulant(m2, m4)

        log.info(f"  L={L}: {len(L_results)} points, "
                f"mean acc={np.mean([r['acceptance_rate'] for r in L_results]):.3f}")

    # Find susceptibility peaks
    susc_peaks = {}
    for L in lattice_sizes:
        L_data = fss_data[L]
        chi_t = [r['chi_tetrad'] for r in L_data]
        chi_m = [r['chi_metric'] for r in L_data]
        rats = [r['ratio'] for r in L_data]

        i_peak_t = int(np.argmax(chi_t))
        i_peak_m = int(np.argmax(chi_m))
        susc_peaks[L] = {
            'tetrad_peak_coupling': rats[i_peak_t],
            'tetrad_peak_height': chi_t[i_peak_t],
            'metric_peak_coupling': rats[i_peak_m],
            'metric_peak_height': chi_m[i_peak_m],
        }
        log.info(f"  L={L}: tetrad peak at G/Gc={rats[i_peak_t]:.2f}, "
                f"metric peak at G/Gc={rats[i_peak_m]:.2f}")

    # Check split transition
    if len(lattice_sizes) >= 2:
        L_max = max(lattice_sizes)
        peak_diff = abs(susc_peaks[L_max]['tetrad_peak_coupling'] -
                       susc_peaks[L_max]['metric_peak_coupling'])
        split = peak_diff > 0.05
    else:
        split = False

    log.info(f"  Split transition: {split}")

    results['finite_size_scaling'] = {
        'lattice_sizes': lattice_sizes,
        'coupling_range': list(coupling_range),
        'split_transition': split,
        'susceptibility_peaks': susc_peaks,
        'runtime_s': t_fss,
    }

    # ── 3. Sign reweighting (parallelized) ──
    log.info("\n[3/3] Sign reweighting check...")
    t0 = time.time()

    sign_jobs = []
    for coupling in [0.5, 1.0, 1.5, 2.0]:
        for L in lattice_sizes[:2]:  # smaller sizes only
            job_seed = seed + int(coupling * 100) + L
            sign_jobs.append((coupling, L, n_thermalize // 2, n_measure // 2,
                            5, 0.3, job_seed))

    with Pool(n_cores) as pool:
        sign_results = pool.map(_run_sign_check, sign_jobs)

    t_sign = time.time() - t0
    for sr in sign_results:
        log.info(f"  G/Gc={sr['coupling']:.1f}, L={sr['L']}: "
                f"<sign>={sr['avg_sign']:.4f} ± {sr['avg_sign_err']:.4f}")

    results['sign_reweighting'] = sign_results
    results['sign_runtime_s'] = t_sign

    # ── Summary ──
    total_time = t_crossing + t_fss + t_sign
    results['metadata'] = {
        'timestamp': timestamp,
        'lattice_sizes': lattice_sizes,
        'n_measure': n_measure,
        'n_thermalize': n_thermalize,
        'n_couplings': n_couplings,
        'n_cores': n_cores,
        'seed': seed,
        'total_runtime_s': total_time,
        'vectorized': True,
        'multiprocessing': True,
    }

    outfile = output_dir / f"vestigial_mc_{timestamp}.json"
    with open(outfile, 'w') as f:
        json.dump(results, f, indent=2, default=str)

    log.info("\n" + "=" * 60)
    log.info("  RESULTS SUMMARY")
    log.info("=" * 60)
    log.info(f"  Vestigial detected (Binder): {vestigial_detected}")
    log.info(f"  Split transition (FSS):      {split}")
    sign_ok = all(s['avg_sign'] > 0.5 for s in sign_results) if sign_results else False
    log.info(f"  Sign problem absent:         {sign_ok}")
    log.info(f"  Total runtime:               {total_time:.1f}s ({total_time/3600:.2f}h)")
    log.info(f"  Results saved to:            {outfile}")
    log.info("=" * 60)

    return results


def main():
    parser = argparse.ArgumentParser(description="Vestigial MC production runs")
    parser.add_argument('--quick', action='store_true',
                        help='Quick test: L=4 only, reduced statistics')
    parser.add_argument('--production', action='store_true',
                        help='Production: L=4,6,8, full statistics')
    parser.add_argument('--sizes', nargs='+', type=int, default=None,
                        help='Custom lattice sizes (e.g., --sizes 4 6 8)')
    parser.add_argument('--sweeps', type=int, default=None,
                        help='Measurement sweeps per coupling point')
    parser.add_argument('--couplings', type=int, default=None,
                        help='Number of coupling scan points')
    parser.add_argument('--cores', type=int, default=16,
                        help='Number of CPU cores for multiprocessing')
    parser.add_argument('--seed', type=int, default=42)
    args = parser.parse_args()

    if args.quick:
        sizes = [4]
        n_measure = 200
        n_thermalize = 100
        n_couplings = 10
    elif args.production:
        sizes = [4, 6, 8]
        n_measure = 2000
        n_thermalize = 1000
        n_couplings = 20
    else:
        sizes = args.sizes or [4, 6]
        n_measure = args.sweeps or 1000
        n_thermalize = n_measure // 2
        n_couplings = args.couplings or 15

    if args.sizes:
        sizes = args.sizes
    if args.sweeps:
        n_measure = args.sweeps
        n_thermalize = n_measure // 2
    if args.couplings:
        n_couplings = args.couplings

    n_cores = min(args.cores, cpu_count())

    timestamp = datetime.now().strftime("%Y%m%dT%H%M%S")
    log_dir = Path("logs")
    log = setup_logging(log_dir, timestamp)

    run_production(sizes, n_measure, n_thermalize, n_couplings, args.seed,
                   n_cores, log)


if __name__ == '__main__':
    main()
