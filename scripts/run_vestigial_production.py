#!/usr/bin/env python3
"""Production vestigial MC runs: 4D fermion-bag finite-size scaling.

Runs the go/no-go analysis for the vestigial metric phase:
  - L=4, 6, 8, 10, 12, 16 lattice sizes (4D hypercubic)
  - Binder cumulant crossing analysis
  - Susceptibility peak analysis
  - Sign reweighting check (verifies no sign problem)
  - Finite-size scaling to determine if vestigial phase survives

Supports incremental runs: --resume loads a prior results file and only
computes lattice sizes not already present. Previously computed data is
carried forward unchanged into the new results file.

Uses multiprocessing to parallelize across coupling points.
Vectorized MC inner loops for ~10-50× speedup per core.

Expected runtime (5000 sweeps, 40 couplings, 10 cores, vectorized):
  L=4-8:    ~5-15 min
  L=10-12:  ~30 min - 2 hrs
  L=14-16:  ~2-8 hrs
  L=17-20:  ~6-24 hrs
  Full L=4-20: ~12-36 hrs

Usage:
  # Quick test (L=4 only, reduced statistics)
  python scripts/run_vestigial_production.py --quick

  # Production run (L=4,6,8, full statistics)
  python scripts/run_vestigial_production.py --production

  # Incremental: add L=10,12 to existing results
  python scripts/run_vestigial_production.py --sizes 4 6 8 10 12 \
    --resume data/vestigial_mc/vestigial_mc_20260329T192611.json

  # Custom
  python scripts/run_vestigial_production.py --sizes 4 6 --sweeps 2000 --cores 8

Output: results saved to data/vestigial_mc/ as JSON + real-time log.
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


def _run_single_njl_binder(args):
    """Worker: run one NJL MC at a single (L, g_njl) point for Binder analysis."""
    from src.vestigial.fermion_bag import FermionBagParams
    from src.vestigial.wetterich_model import run_njl_mc
    from src.vestigial.lattice_4d import Lattice4DParams

    L, g_cosmo, g_njl, n_thermalize, n_measure, n_skip, seed = args
    params = Lattice4DParams(L=L, g_cosmo=g_cosmo, g_EH=0.0)
    mc_params = FermionBagParams(
        n_thermalize=n_thermalize, n_measure=n_measure,
        n_skip=n_skip, seed=seed,
    )
    result = run_njl_mc(params, g_njl=g_njl, mc_params=mc_params)
    return {
        'L': L, 'g_EH': g_njl,
        'binder_tetrad': result.binder_tetrad,
        'binder_metric': result.binder_metric,
        'binder_stag_tetrad': result.binder_stag_tetrad,
        'metric_correlator': result.metric_correlator,
        'phase': result.phase,
        'acceptance_rate': result.acceptance_rate,
        'action_mean': result.action_mean,
    }


def _run_single_njl_fss(args):
    """Worker: run one NJL FSS point."""
    from src.vestigial.fermion_bag import FermionBagParams
    from src.vestigial.wetterich_model import run_njl_mc
    from src.vestigial.lattice_4d import Lattice4DParams
    from src.core.formulas import binder_cumulant

    L, ratio, n_thermalize, n_measure, n_skip, step_size, seed, N_f = args
    g_cosmo = 1.0
    g_njl = ratio  # NJL: positive = attractive (no negation needed)

    params = Lattice4DParams(L=L, g_cosmo=g_cosmo, g_EH=0.0)
    mc_params = FermionBagParams(
        n_thermalize=n_thermalize, n_measure=n_measure,
        n_skip=n_skip, seed=seed,
    )
    result = run_njl_mc(params, g_njl=g_njl, mc_params=mc_params)

    return {
        'L': L, 'ratio': ratio,
        'tetrad_m2': result.tetrad_m2, 'tetrad_m4': result.tetrad_m4,
        'metric_m2': result.metric_m2, 'metric_m4': result.metric_m4,
        'chi_tetrad': result.chi_tetrad, 'chi_metric': result.chi_metric,
        'chi_stag_tetrad': result.chi_stag_tetrad,
        'acceptance_rate': result.acceptance_rate,
        'binder_tetrad': result.binder_tetrad, 'binder_metric': result.binder_metric,
        'binder_stag_tetrad': result.binder_stag_tetrad,
    }


def _run_single_fss_point(args):
    """Worker: run one FSS point using the fermion-bag MC (correct physics).

    Uses the same fermion-bag algorithm as the Binder section, ensuring
    both on-site 8-fermion vertices AND nearest-neighbor bond coupling
    are included in the acceptance criterion.
    """
    from src.vestigial.fermion_bag import FermionBagParams, run_fermion_bag_mc
    from src.vestigial.lattice_4d import Lattice4DParams
    from src.core.formulas import binder_cumulant

    L, ratio, n_thermalize, n_measure, n_skip, step_size, seed, N_f = args
    # Map coupling ratio to (g_cosmo, g_EH) using the lattice convention.
    # g_EH < 0 = attractive bonds (correct ADW physics).
    # 'ratio' is the magnitude |g_EH|; we negate it for attractive coupling.
    g_cosmo = 1.0
    g_EH = -ratio  # negative = attractive NN coupling

    params = Lattice4DParams(L=L, g_cosmo=g_cosmo, g_EH=g_EH)
    mc_params = FermionBagParams(
        n_thermalize=n_thermalize, n_measure=n_measure,
        n_skip=n_skip, seed=seed,
    )
    result = run_fermion_bag_mc(params, mc_params)

    return {
        'L': L, 'ratio': ratio,
        'tetrad_m2': result.tetrad_m2, 'tetrad_m4': result.tetrad_m4,
        'metric_m2': result.metric_m2, 'metric_m4': result.metric_m4,
        'chi_tetrad': result.chi_tetrad, 'chi_metric': result.chi_metric,
        'acceptance_rate': result.acceptance_rate,
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


# ── Incremental support ──

def load_prior_results(path: str) -> dict:
    """Load a prior results JSON file for incremental runs."""
    try:
        with open(path) as f:
            data = json.load(f)
    except FileNotFoundError:
        print(f"ERROR: Resume file not found: {path}")
        sys.exit(1)
    except json.JSONDecodeError as e:
        print(f"ERROR: Resume file is not valid JSON: {path}")
        print(f"  {e}")
        sys.exit(1)
    except (PermissionError, IsADirectoryError) as e:
        print(f"ERROR: Cannot read resume file: {path} ({e})")
        sys.exit(1)
    if not isinstance(data, dict):
        print(f"ERROR: Resume file is not a JSON object: {path}")
        sys.exit(1)
    if not {'binder_crossing', 'finite_size_scaling', 'sign_reweighting'} & data.keys():
        print(f"ERROR: Resume file missing expected sections: {sorted(data.keys())}")
        sys.exit(1)
    return data


def _prior_binder_sizes(prior: dict) -> set[int]:
    """Return set of L values already computed in the Binder crossing section."""
    bc = prior.get('binder_crossing') or {}
    data = bc.get('data') or {}
    return {int(k) for k in data.keys()}


def _prior_fss_sizes(prior: dict) -> set[int]:
    """Return set of L values already computed in FSS section."""
    fss = prior.get('finite_size_scaling') or {}
    fss_results = fss.get('raw_results') or []
    if fss_results and isinstance(fss_results, list):
        return {r['L'] for r in fss_results if isinstance(r, dict) and 'L' in r}
    peaks = fss.get('susceptibility_peaks') or {}
    return {int(k) for k in peaks.keys()}


def _prior_sign_sizes(prior: dict) -> set[int]:
    """Return set of L values already computed in sign reweighting."""
    sr = prior.get('sign_reweighting') or []
    if not isinstance(sr, list):
        return set()
    return {r['L'] for r in sr if isinstance(r, dict) and 'L' in r}


# ── Main production run ──

def run_production(lattice_sizes, n_measure, n_thermalize, n_couplings, seed,
                   n_cores, log, prior=None, model='adw'):
    """Run the full production analysis with multiprocessing.

    If prior is provided (from --resume), skips lattice sizes already computed
    and merges prior data into the new results file.

    Args:
        model: 'adw' for Weingarten ADW (Option B), 'njl' for Wetterich NJL (Option C)
    """
    import numpy as np
    from src.core.constants import ADW_4D_COUPLING_SCAN
    from src.core.formulas import binder_cumulant

    output_dir = Path("data/vestigial_mc")
    output_dir.mkdir(parents=True, exist_ok=True)
    timestamp = datetime.now().strftime("%Y%m%dT%H%M%S")

    # Determine which sizes need computing vs reusing
    prior_binder = _prior_binder_sizes(prior) if prior else set()
    prior_fss = _prior_fss_sizes(prior) if prior else set()
    prior_sign = _prior_sign_sizes(prior) if prior else set()
    new_binder_sizes = [L for L in lattice_sizes if L not in prior_binder]
    new_fss_sizes = [L for L in lattice_sizes if L not in prior_fss]
    new_sign_sizes = [L for L in lattice_sizes if L not in prior_sign]

    log.info("=" * 60)
    log.info("  Vestigial MC Production Run (vectorized + multiprocessing)")
    log.info(f"  Requested lattice sizes: {lattice_sizes}")
    if prior:
        log.info(f"  Resuming from prior run with sizes: {sorted(prior_binder)}")
        log.info(f"  New Binder sizes to compute: {new_binder_sizes}")
        log.info(f"  New FSS sizes to compute: {new_fss_sizes}")
    log.info(f"  Sweeps: {n_thermalize} thermalize + {n_measure} measure")
    log.info(f"  Couplings: {n_couplings} points")
    log.info(f"  Cores: {n_cores}")
    log.info(f"  Seed: {seed}")
    skip_table = {L: max(5, L * L // 20) for L in lattice_sizes}
    log.info(f"  n_skip (decorrelation): {skip_table}")
    log.info(f"  Started: {datetime.now().isoformat()}")
    log.info("=" * 60)

    results = {}
    if model == 'njl':
        from src.core.constants import NJL_COUPLING_SCAN
        g_cosmo = NJL_COUPLING_SCAN['g_cosmo']
        g_EH_range = NJL_COUPLING_SCAN['g_njl_range']  # positive = attractive for NJL
    else:
        g_cosmo = ADW_4D_COUPLING_SCAN['g_cosmo']
        g_EH_range = ADW_4D_COUPLING_SCAN['g_EH_range']
    g_values = np.linspace(g_EH_range[0], g_EH_range[1], n_couplings)

    # ── 1. 4D Binder crossing (parallelized across L × coupling) ──
    log.info("\n[1/3] 4D Binder cumulant crossing analysis...")
    t0 = time.time()

    # Check prior grid compatibility BEFORE building jobs — move incompatible
    # sizes from prior to new_binder_sizes so they get recomputed
    crossing_data = {}
    if prior:
        prior_bc_data = (prior.get('binder_crossing') or {}).get('data') or {}
        for L_str, Ldata in prior_bc_data.items():
            L_int = int(L_str)
            if L_int not in lattice_sizes:
                continue
            prior_g = Ldata.get('g_EH_values', [])
            if len(prior_g) != len(g_values) or (
                len(prior_g) > 0 and not np.allclose(prior_g, g_values, atol=1e-10)
            ):
                log.warning(f"  L={L_int}: prior coupling grid ({len(prior_g)} pts) "
                           f"differs from current ({len(g_values)} pts) — will recompute.")
                if L_int not in new_binder_sizes:
                    new_binder_sizes.append(L_int)
            else:
                crossing_data[L_int] = Ldata
                log.info(f"  L={L_int}: reused from prior ({len(prior_g)} points)")

    # Build job list: only sizes that need computing
    jobs = []
    for L in new_binder_sizes:
        for i, g_EH in enumerate(g_values):
            job_seed = seed + L * 1000 + i
            n_skip_L = max(5, L * L // 20)  # scale with autocorrelation ~ L^2
            jobs.append((L, g_cosmo, g_EH, n_thermalize, n_measure, n_skip_L, job_seed))

    if jobs:
        binder_worker = _run_single_njl_binder if model == 'njl' else _run_single_fermion_bag
        log.info(f"  Dispatching {len(jobs)} new jobs across {n_cores} cores (model={model})...")
        with Pool(n_cores) as pool:
            raw_results = pool.map(binder_worker, jobs)
        log.info(f"  Completed {len(raw_results)} new jobs in {time.time()-t0:.1f}s")
    else:
        raw_results = []
        log.info("  All Binder sizes already computed — reusing prior data.")

    t_crossing = time.time() - t0
    # Then, add newly computed data
    for L in new_binder_sizes:
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

    # Verify all requested sizes have Binder data
    missing_binder = [L for L in lattice_sizes if L not in crossing_data]
    if missing_binder:
        log.error(f"  Binder data missing for L={missing_binder} — results will be incomplete.")

    # Find crossings: check ALL consecutive L pairs (not just min/max)
    from src.core.constants import ADW_4D_FSS

    def _find_crossing(g_vals, b1, b2):
        diff = b1 - b2
        for i in range(len(diff) - 1):
            if diff[i] * diff[i+1] < 0:
                t = diff[i] / (diff[i] - diff[i+1])
                return float(g_vals[i] + t * (g_vals[i+1] - g_vals[i]))
        return None

    all_tetrad_crossings = []
    all_metric_crossings = []
    sorted_sizes = sorted(crossing_data.keys())
    for idx in range(len(sorted_sizes) - 1):
        L1, L2 = sorted_sizes[idx], sorted_sizes[idx + 1]
        # Use each size's stored g_vals (safe: grid compatibility already verified)
        g1 = np.array(crossing_data[L1]['g_EH_values'])
        g2 = np.array(crossing_data[L2]['g_EH_values'])
        if len(g1) != len(g2) or not np.allclose(g1, g2, atol=1e-10):
            log.warning(f"  L={L1}-{L2}: incompatible g-grids, skipping crossing.")
            continue
        bt1 = np.array(crossing_data[L1]['binder_tetrad'])
        bt2 = np.array(crossing_data[L2]['binder_tetrad'])
        bm1 = np.array(crossing_data[L1]['binder_metric'])
        bm2 = np.array(crossing_data[L2]['binder_metric'])

        tc = _find_crossing(g1, bt1, bt2)
        mc = _find_crossing(g1, bm1, bm2)
        if tc is not None:
            all_tetrad_crossings.append({'L_pair': (L1, L2), 'g_EH': tc})
        if mc is not None:
            all_metric_crossings.append({'L_pair': (L1, L2), 'g_EH': mc})
        log.info(f"  L={L1}-{L2}: tetrad crossing={tc}, metric crossing={mc}")

    # Also check min vs max for backwards compatibility
    tetrad_crossing = all_tetrad_crossings[-1]['g_EH'] if all_tetrad_crossings else None
    metric_crossing = all_metric_crossings[-1]['g_EH'] if all_metric_crossings else None

    vestigial_window = None
    vestigial_detected = False
    window_threshold = ADW_4D_FSS['vestigial_window_threshold']
    if tetrad_crossing is not None and metric_crossing is not None:
        window = abs(metric_crossing - tetrad_crossing)
        if window > window_threshold:
            vestigial_window = window
            vestigial_detected = True

    log.info(f"  Tetrad crossings found: {len(all_tetrad_crossings)}")
    log.info(f"  Metric crossings found: {len(all_metric_crossings)}")
    log.info(f"  Vestigial window: {vestigial_window}")
    log.info(f"  Vestigial detected: {vestigial_detected}")

    results['binder_crossing'] = {
        'lattice_sizes': lattice_sizes,
        'tetrad_crossings': all_tetrad_crossings,
        'metric_crossings': all_metric_crossings,
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

    coupling_range = ADW_4D_FSS['coupling_range']
    ratios = np.linspace(coupling_range[0], coupling_range[1], n_couplings)
    N_f = 4

    # Determine what to compute vs reuse
    fss_data = {}
    sizes_to_compute = list(new_fss_sizes)  # start with new sizes

    if prior:
        prior_fss_raw = prior.get('finite_size_scaling', {}).get('raw_results', [])
        if prior_fss_raw:
            # Carry forward prior FSS data from raw_results
            for L in lattice_sizes:
                if L in prior_fss and L not in new_fss_sizes:
                    L_results = sorted([r for r in prior_fss_raw if r['L'] == L],
                                      key=lambda r: r['ratio'])
                    fss_data[L] = L_results
                    log.info(f"  L={L}: reused {len(L_results)} FSS points from prior")
        elif prior_fss:
            # Prior detected sizes but has no raw_results — must recompute all
            log.info("  Prior file lacks raw_results — FSS data must be recomputed.")
            log.info("  (New runs will store raw_results for future incremental use.)")
            sizes_to_compute = list(lattice_sizes)

    # Build and dispatch jobs for sizes_to_compute
    fss_jobs = []
    for L in sizes_to_compute:
        for i, r in enumerate(ratios):
            job_seed = seed + L * 1000 + i + 500
            n_skip_L = max(5, L * L // 20)  # scale with autocorrelation ~ L^2
            fss_jobs.append((L, r, n_thermalize, n_measure, n_skip_L, 0.3, job_seed, N_f))

    if fss_jobs:
        fss_worker = _run_single_njl_fss if model == 'njl' else _run_single_fss_point
        log.info(f"  Dispatching {len(fss_jobs)} FSS jobs across {n_cores} cores (model={model})...")
        with Pool(n_cores) as pool:
            fss_results = pool.map(fss_worker, fss_jobs)
        log.info(f"  Completed {len(fss_results)} FSS jobs in {time.time()-t0:.1f}s")
    else:
        fss_results = []
        log.info("  All FSS sizes already computed — reusing prior data.")

    t_fss = time.time() - t0

    # Add computed results to fss_data
    for L in sizes_to_compute:
        L_results = sorted([r for r in fss_results if r['L'] == L],
                          key=lambda r: r['ratio'])
        fss_data[L] = L_results

    # Verify all requested sizes have FSS data
    missing_fss = [L for L in lattice_sizes if L not in fss_data]
    if missing_fss:
        log.error(f"  FSS data missing for L={missing_fss} — results will be incomplete.")

    # Compute Binder cumulants and log for ALL sizes
    for L in lattice_sizes:
        L_data = fss_data.get(L, [])
        if not L_data:
            log.warning(f"  L={L}: no FSS data, skipping Binder cumulant computation.")
            continue
        for r in L_data:
            m2, m4 = r['tetrad_m2'], r['tetrad_m4']
            r['binder_tetrad'] = binder_cumulant(m2, m4)
            m2, m4 = r['metric_m2'], r['metric_m4']
            r['binder_metric'] = binder_cumulant(m2, m4)

        log.info(f"  L={L}: {len(L_data)} points, "
                f"mean acc={np.mean([r['acceptance_rate'] for r in L_data]):.3f}")

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
        split = peak_diff > ADW_4D_FSS['split_threshold']
    else:
        split = False

    log.info(f"  Split transition: {split}")

    # Store raw FSS results for future incremental use
    all_fss_raw = []
    for L in lattice_sizes:
        all_fss_raw.extend(fss_data.get(L, []))

    results['finite_size_scaling'] = {
        'lattice_sizes': lattice_sizes,
        'coupling_range': list(coupling_range),
        'split_transition': split,
        'susceptibility_peaks': susc_peaks,
        'raw_results': all_fss_raw,
        'runtime_s': t_fss,
    }

    # ── 3. Sign reweighting (parallelized) ──
    log.info("\n[3/3] Sign reweighting check...")
    t0 = time.time()

    # Only run sign checks for new sizes (reuse prior for already-checked sizes)
    sign_jobs = []
    for coupling in ADW_4D_FSS['sign_check_couplings']:
        for L in sorted(new_sign_sizes)[:2]:  # two smallest new sizes only
            job_seed = seed + int(coupling * 100) + L
            n_skip_L = max(5, L // 2)
            sign_jobs.append((coupling, L, n_thermalize // 2, n_measure // 2,
                            n_skip_L, 0.3, job_seed))

    # Carry forward prior sign results
    prior_sign_results = []
    if prior:
        for sr in (prior.get('sign_reweighting') or []):
            if isinstance(sr, dict) and sr.get('L') in lattice_sizes:
                prior_sign_results.append(sr)
        if prior_sign_results:
            log.info(f"  Reusing {len(prior_sign_results)} sign checks from prior run")

    if sign_jobs:
        with Pool(n_cores) as pool:
            new_sign_results = pool.map(_run_sign_check, sign_jobs)
    else:
        new_sign_results = []
        if not prior_sign_results:
            log.info("  No new sign checks needed.")

    sign_results = prior_sign_results + new_sign_results

    t_sign = time.time() - t0
    for sr in new_sign_results:
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
        'incremental': prior is not None,
        'new_binder_sizes': new_binder_sizes,
        'new_fss_sizes': new_fss_sizes,
        'reused_sizes': sorted(prior_binder & set(lattice_sizes)) if prior else [],
    }

    outfile = output_dir / f"vestigial_mc_{model}_{timestamp}.json"
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
                        help='Custom lattice sizes (e.g., --sizes 4 6 8 10 12)')
    parser.add_argument('--sweeps', type=int, default=None,
                        help='Measurement sweeps per coupling point')
    parser.add_argument('--couplings', type=int, default=None,
                        help='Number of coupling scan points')
    parser.add_argument('--cores', type=int, default=16,
                        help='Number of CPU cores for multiprocessing')
    parser.add_argument('--seed', type=int, default=42)
    parser.add_argument('--resume', type=str, default=None,
                        help='Path to prior results JSON to resume from. '
                             'Skips lattice sizes already computed.')
    parser.add_argument('--njl', action='store_true',
                        help='Use Wetterich NJL model (Option C) instead of ADW Weingarten (Option B). '
                             'NJL: no gauge links, Fierz S+P channels, positive coupling = attractive.')
    args = parser.parse_args()

    if args.quick:
        sizes = [4]
        n_measure = 200
        n_thermalize = 100
        n_couplings = 10
    elif args.production:
        sizes = [4, 6, 8, 10, 12, 14, 16]
        n_measure = 5000
        n_thermalize = 2500
        n_couplings = 40
    else:
        sizes = args.sizes or [4, 6, 8]
        n_measure = args.sweeps or 5000
        n_thermalize = n_measure // 2
        n_couplings = args.couplings or 40

    if args.sizes:
        sizes = args.sizes
    if args.sweeps:
        n_measure = args.sweeps
        n_thermalize = n_measure // 2
    if args.couplings:
        n_couplings = args.couplings

    n_cores = min(args.cores, cpu_count())

    # Load prior results for incremental runs
    prior = None
    if args.resume:
        prior = load_prior_results(args.resume)
        prior_sizes = sorted(_prior_binder_sizes(prior))
        print(f"Resuming from {args.resume} (prior sizes: {prior_sizes})")

    model = 'njl' if args.njl else 'adw'
    timestamp = datetime.now().strftime("%Y%m%dT%H%M%S")
    log_dir = Path("logs")
    log = setup_logging(log_dir, f"{model}_{timestamp}")

    run_production(sizes, n_measure, n_thermalize, n_couplings, args.seed,
                   n_cores, log, prior=prior, model=model)


if __name__ == '__main__':
    main()
