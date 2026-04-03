#!/usr/bin/env python3
"""Benchmark Rust RHMC backend with multiprocessing parallelism.

Runs 14 independent coupling points in parallel (one per core) to confirm
that Rust's single-threaded design scales linearly with worker count.

Usage:
  uv run python scripts/benchmark_rust_parallel.py --l 4 --workers 14
  uv run python scripts/benchmark_rust_parallel.py --l 12 --workers 14
"""

import argparse
import multiprocessing as mp
import numpy as np
import time

from src.core.constants import MAJORANA_GAMMA_8x8, MAJORANA_J1
from src.vestigial.hs_rhmc import compute_zolotarev_coefficients


def _build_cg_entries():
    """Compute CG stencil entries from constants.py (canonical source)."""
    CG = np.array([MAJORANA_J1 @ MAJORANA_GAMMA_8x8[a] for a in range(4)])
    cg_a, cg_i, cg_j, cg_val = [], [], [], []
    for a in range(4):
        for I in range(8):
            for J in range(8):
                v = CG[a, I, J]
                if abs(v) > 1e-15:
                    cg_a.append(a); cg_i.append(I); cg_j.append(J); cg_val.append(v)
    return (np.array(cg_a, dtype=np.int64), np.array(cg_i, dtype=np.int64),
            np.array(cg_j, dtype=np.int64), np.array(cg_val, dtype=np.float64))


def _run_one_coupling(args):
    """Run RHMC at one coupling point. Designed for multiprocessing.Pool."""
    import sk_eft_rhmc  # import inside worker (fresh per process)

    L, g, n_traj, n_md_steps, tau, a0, alphas, betas, a0_hb, alphas_hb, betas_hb, seed, cg = args
    cg_a, cg_i, cg_j, cg_val = cg

    t0 = time.time()
    result = sk_eft_rhmc.run_rhmc_rust(
        l=L, g=g, n_traj=n_traj, n_therm=0, n_meas_skip=1,
        n_md_steps=n_md_steps, tau=tau,
        alpha_0=float(a0), alphas=alphas, betas=betas,
        alpha_0_hb=float(a0_hb), alphas_hb=alphas_hb, betas_hb=betas_hb,
        seed=seed, cg_a=cg_a, cg_i=cg_i, cg_j=cg_j, cg_val=cg_val,
    )
    elapsed = time.time() - t0
    return {
        'g': g, 'elapsed': elapsed, 's_per_traj': elapsed / n_traj,
        'acceptance': result['acceptance_rate'],
        'h_sq': np.mean(result['h_sq_history']) if result['h_sq_history'] else 0,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--l', type=int, default=4)
    parser.add_argument('--g-min', type=float, default=0.5)
    parser.add_argument('--g-max', type=float, default=8.0)
    parser.add_argument('--n-couplings', type=int, default=14)  # one per worker
    parser.add_argument('--n-traj', type=int, default=3)  # few for benchmark
    parser.add_argument('--n-md-steps', type=int, default=10)
    parser.add_argument('--workers', type=int, default=14)
    parser.add_argument('--seed', type=int, default=42)
    args = parser.parse_args()

    L = args.l
    g_values = np.linspace(args.g_min, args.g_max, args.n_couplings)
    cg = _build_cg_entries()

    # Spectral range via Lanczos (matrix-free, works at any L)
    # Pipeline invariant: no hardcoded spectral parameters
    import sk_eft_rhmc
    lam_min, lam_max = sk_eft_rhmc.estimate_spectral_range_py(
        L, g_values[len(g_values)//2], args.seed, 50, *cg)
    print(f'Spectral range (Lanczos): [{lam_min:.4f}, {lam_max:.1f}], κ≈{lam_max/lam_min:.0f}')

    # Action: x^{-1/4} for S_PF = Φ†(A†A)^{-1/4}Φ (complex pseudofermion convention)
    # Heatbath: x^{-3/8} for A·r_{-3/8}(A†A)·ξ trick giving (A†A)^{1/8} (Schaich-DeGrand)
    # 24 poles for ≤5e-5 relative error — critical at high acceptance (low Metropolis correction)
    a0, alphas, betas = compute_zolotarev_coefficients(24, lam_min, lam_max, -0.25)
    a0_hb, alphas_hb, betas_hb = compute_zolotarev_coefficients(24, lam_min, lam_max, -0.375)

    # Build task list
    tasks = []
    for i, g in enumerate(g_values):
        seed = args.seed + i * 1000
        tasks.append((L, g, args.n_traj, args.n_md_steps, 1.0,
                       a0, np.array(alphas), np.array(betas),
                       a0_hb, np.array(alphas_hb), np.array(betas_hb),
                       seed, cg))

    # Sequential baseline (1 coupling point)
    print(f'L={L}, dim={8*L**4:,}, {args.n_couplings} couplings × {args.n_traj} traj')
    print(f'\n--- Sequential (1 worker) ---')
    t0 = time.time()
    seq_result = _run_one_coupling(tasks[0])
    t_seq = time.time() - t0
    print(f'  1 coupling: {t_seq:.2f}s ({seq_result["s_per_traj"]:.2f}s/traj)')

    # Parallel
    print(f'\n--- Parallel ({args.workers} workers) ---')
    t0 = time.time()
    with mp.Pool(args.workers) as pool:
        results = pool.map(_run_one_coupling, tasks)
    t_par = time.time() - t0

    times = [r['elapsed'] for r in results]
    s_per_traj = [r['s_per_traj'] for r in results]
    print(f'  {args.n_couplings} couplings: {t_par:.2f}s wall')
    print(f'  Per-coupling: {np.mean(times):.2f}s avg')
    print(f'  Per-trajectory: {np.mean(s_per_traj):.2f}s avg')
    print(f'  Speedup vs sequential: {t_seq * args.n_couplings / t_par:.1f}×')
    print(f'  Parallel efficiency: {t_seq * args.n_couplings / (t_par * args.workers) * 100:.0f}%')

    # Production projection
    prod_traj = 1500 * args.n_couplings
    prod_serial_h = np.mean(s_per_traj) * prod_traj / 3600
    prod_parallel_h = prod_serial_h * t_par / (t_seq * args.n_couplings)
    # Correct: parallel wall = serial_wall / actual_speedup
    actual_speedup = t_seq * args.n_couplings / t_par
    prod_wall_h = prod_serial_h / actual_speedup
    print(f'\n--- Production projection (1500 traj × {args.n_couplings} couplings) ---')
    print(f'  Serial: {prod_serial_h:.1f}h')
    print(f'  {args.workers} workers: {prod_wall_h:.1f}h')


if __name__ == '__main__':
    mp.set_start_method('spawn')
    main()
