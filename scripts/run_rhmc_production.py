#!/usr/bin/env python3
"""Production RHMC runner with chunk-level checkpoint/resume.

Uses the Rust RHMC backend with complex pseudofermion convention
(Schaich-DeGrand, arXiv:1410.6971). Designed for long runs that can
be stopped and resumed without losing work.

Features:
  - Per-coupling .npz checkpoint files (atomic writes, Ctrl-C safe)
  - Chunk-level saves: every N trajectories, results + h-field state saved
  - Automatic resume: detects completed/partial couplings on startup
  - h-field state carried across chunks (no re-thermalization on resume)
  - Compatible with nohup for overnight runs

Note: np.savez uses numpy's own binary format (not pickle). The allow_pickle
parameter in np.load is only needed for object arrays; our data is pure float64.

Usage:
  # L=4 production (~44 min on M3 Max 16-core)
  PYTHONPATH=. .venv/bin/python scripts/run_rhmc_production.py --l 4 --n-traj 1500

  # L=8 production (~3.3 days — stop/resume anytime)
  PYTHONPATH=. .venv/bin/python scripts/run_rhmc_production.py --l 8 --n-traj 500 --n-md-steps 50

  # Resume interrupted run (auto-detects progress from data/rhmc/)
  PYTHONPATH=. .venv/bin/python scripts/run_rhmc_production.py --l 8 --n-traj 500 --n-md-steps 50

  # Background overnight run
  nohup env PYTHONPATH=. .venv/bin/python scripts/run_rhmc_production.py \\
    --l 8 --n-traj 500 --n-md-steps 50 > rhmc_l8.log 2>&1 &

Lean: HubbardStratonovichRHMC.lean (22 theorems, zero sorry)
Source: Schaich & DeGrand, CPC 190:200 (2015), Eqs. 16-20 (arXiv:1410.6971)
"""

import argparse
import atexit
import multiprocessing as mp
import numpy as np
import os
import signal
import time
from pathlib import Path

from src.core.constants import MAJORANA_GAMMA_8x8, MAJORANA_J1
from src.vestigial.hs_rhmc import compute_zolotarev_coefficients, prepare_hasenbusch_coefficients


RHMC_BASE = Path("data/rhmc")
CHUNK_SIZE = 1


def _data_dir(L):
    """Per-lattice-size data directory: data/rhmc/L{L}/"""
    return RHMC_BASE / f"L{L}"


def _build_cg_entries():
    """CG stencil entries from constants.py (pipeline invariant: canonical source)."""
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


def _coupling_path(L, g):
    return _data_dir(L) / f"g{g:.4f}.npz"


def _load_checkpoint(L, g):
    """Load existing results + h_final for resume."""
    f = _coupling_path(L, g)
    if not f.exists():
        return None, None
    data = dict(np.load(f))
    h_final = data.get('h_final', None)
    return data, h_final


def _save_checkpoint(L, g, data):
    """Atomic save: write .tmp.npz then rename (Ctrl-C safe)."""
    f = _coupling_path(L, g)
    tmp = f.with_suffix('.tmp')
    np.savez(tmp, **data)
    # np.savez auto-appends .npz to the path
    tmp_actual = tmp.with_suffix('.tmp.npz')
    tmp_actual.rename(f)


def _run_coupling_chunked(args):
    """Run one coupling point in chunks with per-chunk checkpointing."""
    import sk_eft_rhmc

    (L, g, n_traj_total, n_therm, n_md_steps, tau,
     a0, alphas, betas, a0_hb, alphas_hb, betas_hb,
     base_seed, cg, chunk_size) = args
    cg_a, cg_i, cg_j, cg_val = cg

    existing, h_resume = _load_checkpoint(L, g)
    if existing is not None:
        n_done = len(existing.get('h_sq_history', np.array([])))
        if n_done >= n_traj_total:
            return {'g': g, 'status': 'already_complete', 'n_traj': n_done}
    else:
        n_done = 0
        existing = {
            'h_sq_history': np.array([], dtype=np.float64),
            'delta_h_history': np.array([], dtype=np.float64),
            'tet_m2_history': np.array([], dtype=np.float64),
            'tr_q2_history': np.array([], dtype=np.float64),
        }

    n_remaining = n_traj_total - n_done
    t_start = time.time()

    while n_remaining > 0:
        chunk = min(chunk_size, n_remaining)
        this_therm = n_therm if (n_done == 0 and h_resume is None) else 0
        this_seed = base_seed + n_done

        h_init = np.array(h_resume, dtype=np.float64) if h_resume is not None else None

        # Clark-Kennedy 2-PF even-odd RHMC (default):
        #   det(M_e)^{1/2} = [det(M_e)^{1/4}]^2 via two independent complex
        #   pseudofermion fields, each with x^{-1/4}. Resolves x^{-1/2} |ΔH|≈2.35
        #   pathology. Half-lattice CG + reduced force variance → ~2× faster.
        #   Reference: Clark & Kennedy, PRL 98:051601 (2007)
        #
        # Full-lattice fallback (--mode full):
        #   Single complex PF with x^{-1/4} on full A†A. No EO advantage.
        result = sk_eft_rhmc.run_rhmc_rust_eo_2pf(
            l=L, g=g, n_traj=chunk + this_therm, n_therm=this_therm, n_meas_skip=1,
            n_md_steps=n_md_steps, tau=tau,
            alpha_0=float(a0), alphas=alphas, betas=betas,
            alpha_0_hb=float(a0_hb), alphas_hb=alphas_hb, betas_hb=betas_hb,
            seed=this_seed, cg_a=cg_a, cg_i=cg_i, cg_j=cg_j, cg_val=cg_val,
            h_init=h_init,
        )

        for key in ['h_sq_history', 'delta_h_history', 'tet_m2_history', 'tr_q2_history']:
            old = existing[key]
            new = np.array(result[key])
            existing[key] = np.concatenate([old, new]) if len(old) > 0 else new

        h_resume = np.array(result['h_final'], dtype=np.float64)
        existing['h_final'] = h_resume
        existing['acceptance_rate'] = np.float64(result['acceptance_rate'])
        existing['g'] = np.float64(g)
        existing['L'] = np.int64(L)
        existing['n_md_steps'] = np.int64(n_md_steps)
        _save_checkpoint(L, g, existing)

        n_done += chunk
        n_remaining -= chunk
        elapsed = time.time() - t_start
        rate = elapsed / n_done if n_done > 0 else 0
        print(f"  g={g:.3f}: {n_done}/{n_traj_total} traj "
              f"({elapsed:.0f}s, {rate:.2f}s/traj, "
              f"accept={result['acceptance_rate']:.2f})", flush=True)

    total_time = time.time() - t_start
    return {
        'g': g, 'status': 'complete', 'n_traj': n_done,
        'time': total_time,
        'h_sq': float(np.mean(existing['h_sq_history'])),
        'acceptance': float(existing.get('acceptance_rate', 0)),
    }


def _run_coupling_chunked_hasenbusch(args):
    """Run one coupling with Hasenbusch K-level mass splitting."""
    import sk_eft_rhmc

    (L, g, n_traj_total, n_therm, tau, hcoeffs,
     base_seed, cg, chunk_size) = args
    cg_a, cg_i, cg_j, cg_val = cg

    existing, h_resume = _load_checkpoint(L, g)
    if existing is not None:
        n_done = len(existing.get('h_sq_history', np.array([])))
        if n_done >= n_traj_total:
            return {'g': g, 'status': 'already_complete', 'n_traj': n_done}
    else:
        n_done = 0
        existing = {
            'h_sq_history': np.array([], dtype=np.float64),
            'delta_h_history': np.array([], dtype=np.float64),
            'tet_m2_history': np.array([], dtype=np.float64),
            'tr_q2_history': np.array([], dtype=np.float64),
        }

    n_remaining = n_traj_total - n_done
    t_start = time.time()

    while n_remaining > 0:
        chunk = min(chunk_size, n_remaining)
        this_therm = n_therm if (n_done == 0 and h_resume is None) else 0
        this_seed = base_seed + n_done

        h_init = np.array(h_resume, dtype=np.float64) if h_resume is not None else None

        result = sk_eft_rhmc.run_rhmc_rust_eo_2pf_hasenbusch(
            l=L, g=g, n_traj=chunk + this_therm, n_therm=this_therm, n_meas_skip=1,
            tau=tau,
            n_factors=hcoeffs['n_factors'],
            n_poles_per_factor=hcoeffs['n_poles_per_factor'],
            action_alpha0s=hcoeffs['action_alpha0s'],
            action_alphas=hcoeffs['action_alphas'],
            action_betas=hcoeffs['action_betas'],
            hb_alpha0s=hcoeffs['hb_alpha0s'],
            hb_alphas=hcoeffs['hb_alphas'],
            hb_betas=hcoeffs['hb_betas'],
            n_steps_per_level=hcoeffs['n_steps_per_level'],
            factor_levels_arr=hcoeffs['factor_levels'],
            is_heavy_flags=hcoeffs['is_heavy_flags'],
            mu_sq_values=hcoeffs['mu_sq_values'],
            mu_lo_values=hcoeffs['mu_lo_values'],
            mu_hi_values=hcoeffs['mu_hi_values'],
            seed=this_seed, cg_a=cg_a, cg_i=cg_i, cg_j=cg_j, cg_val=cg_val,
            h_init=h_init,
        )

        for key in ['h_sq_history', 'delta_h_history', 'tet_m2_history', 'tr_q2_history']:
            old = existing[key]
            new = np.array(result[key])
            existing[key] = np.concatenate([old, new]) if len(old) > 0 else new

        h_resume = np.array(result['h_final'], dtype=np.float64)
        existing['h_final'] = h_resume
        existing['acceptance_rate'] = np.float64(result['acceptance_rate'])
        existing['g'] = np.float64(g)
        existing['L'] = np.int64(L)
        existing['hasenbusch'] = np.int64(1)
        existing['n_factors'] = np.int64(hcoeffs['n_factors'])
        _save_checkpoint(L, g, existing)

        n_done += chunk
        n_remaining -= chunk
        elapsed = time.time() - t_start
        rate = elapsed / n_done if n_done > 0 else 0
        print(f"  g={g:.3f}: {n_done}/{n_traj_total} traj "
              f"({elapsed:.0f}s, {rate:.2f}s/traj, "
              f"accept={result['acceptance_rate']:.2f}) [Hasenbusch K={hcoeffs['n_factors']-1}]",
              flush=True)

    total_time = time.time() - t_start
    return {
        'g': g, 'status': 'complete', 'n_traj': n_done,
        'time': total_time,
        'h_sq': float(np.mean(existing['h_sq_history'])),
        'acceptance': float(existing.get('acceptance_rate', 0)),
    }


def main():
    parser = argparse.ArgumentParser(description="Production RHMC with checkpoint/resume")
    parser.add_argument('--l', type=int, required=True)
    parser.add_argument('--g-min', type=float, default=0.5)
    parser.add_argument('--g-max', type=float, default=8.0)
    parser.add_argument('--n-couplings', type=int, default=14)
    parser.add_argument('--g-critical-min', type=float, default=None,
                        help='Add fine-grained points in critical region [g-critical-min, g-critical-max].')
    parser.add_argument('--g-critical-max', type=float, default=None)
    parser.add_argument('--n-critical', type=int, default=8,
                        help='Number of extra points in critical region.')
    parser.add_argument('--n-traj', type=int, required=True)
    parser.add_argument('--n-therm', type=int, default=50)
    parser.add_argument('--n-md-steps', type=int, default=80,
                        help='MD integration steps per trajectory. '
                             'Higher = better acceptance, slower per traj. '
                             'L=4: 20, L=8: 80, L=16: 100+. Target |dH| < 1.')
    parser.add_argument('--tau', type=float, default=None,
                        help='MD trajectory length. Default: n_md_steps/160 '
                             '(preserves step size eps=1/160 from the original tuning). '
                             'Shorter tau = smaller |dH| but worse autocorrelation.')
    parser.add_argument('--n-poles', type=int, default=12,
                        help='Zolotarev poles for rational approximation. '
                             '12 = good balance of accuracy and CG cache pressure. '
                             '24 = original (slower due to L2 thrashing at L>=8).')
    parser.add_argument('--workers', type=int, default=4,
                        help='Parallel coupling workers. '
                             'Keep <= physical cores - 2 to avoid thermal throttling.')
    parser.add_argument('--seed', type=int, default=42)
    parser.add_argument('--chunk-size', type=int, default=10,
                        help='Trajectories per checkpoint write. '
                             '10 = frequent saves, minimal lost work on interrupt.')
    parser.add_argument('--hasenbusch', action='store_true',
                        help='Use Hasenbusch K=3 mass splitting (10-20× speedup at L≥8). '
                             'Splits det(M_e) into 4 factors with κ~16 each, '
                             'nested 3-level Omelyan integrator.')
    parser.add_argument('--hasenbusch-k', type=int, default=3,
                        help='Hasenbusch splitting levels (default 3). '
                             'K=3: 4 factors, κ~16/factor, 8 poles/factor.')
    parser.add_argument('--hasenbusch-poles', type=int, default=8,
                        help='Zolotarev poles per Hasenbusch factor (default 8).')
    args = parser.parse_args()

    L = args.l
    # Tau defaults to n_md_steps/160 to preserve the step size eps=1/160
    # that was tuned for L=8 acceptance. Shorter tau = fewer steps at same eps.
    tau = args.tau if args.tau is not None else args.n_md_steps / 160.0
    n_poles = args.n_poles

    g_values = np.linspace(args.g_min, args.g_max, args.n_couplings)
    # Optionally add fine-grained points in the critical region
    if args.g_critical_min is not None and args.g_critical_max is not None:
        g_critical = np.linspace(args.g_critical_min, args.g_critical_max, args.n_critical)
        g_values = np.unique(np.sort(np.concatenate([g_values, g_critical])))
    _data_dir(L).mkdir(parents=True, exist_ok=True)

    n_complete, n_partial = 0, 0
    for g in g_values:
        f = _coupling_path(L, g)
        if f.exists():
            n = len(np.load(f)['h_sq_history'])
            if n >= args.n_traj:
                n_complete += 1
            else:
                n_partial += 1

    eps = tau / args.n_md_steps
    print(f"{'='*70}")
    print(f"RHMC Production: L={L}, {len(g_values)} couplings x {args.n_traj} traj")
    print(f"  Clark-Kennedy 2-PF even-odd, {n_poles}-pole Zolotarev x^{{-1/4}}")
    print(f"  tau={tau:.3f}, eps={eps:.6f}, MD steps={args.n_md_steps}")
    print(f"  Progress: {n_complete} complete, {n_partial} partial, "
          f"{len(g_values) - n_complete - n_partial} new")
    print(f"  Workers: {args.workers}, chunk: {args.chunk_size} traj")
    print(f"  Output: {_data_dir(L)}/g*.npz")
    print(f"{'='*70}")

    if n_complete == len(g_values):
        print("All couplings already complete!")
        return

    cg = _build_cg_entries()
    import sk_eft_rhmc
    lam_min, lam_max = sk_eft_rhmc.estimate_spectral_range_py(
        L, g_values[len(g_values)//2], args.seed, 50, *cg)
    print(f"  Spectrum: [{lam_min:.3f}, {lam_max:.1f}], kappa={lam_max/lam_min:.0f}")

    # Clark-Kennedy 2-PF even-odd RHMC:
    #   Action: x^{-1/4} on M_e (each of 2 PFs contributes det(M_e)^{1/4})
    #   Heatbath: x^{-7/8} on M_e (generates M_e^{1/8} distribution for x^{-1/4} action)
    #     Derivation: η = M_e^{-7/8} ξ, Φ = M_e η = M_e^{1/8} ξ → S = Φ^T M_e^{-1/4} Φ = ξ^T ξ
    #   Physics: det(M_e)^{1/4} × det(M_e)^{1/4} = det(M_e)^{1/2} = Pf(A)
    #
    # Lean: zolotarev_exponential_convergence (HubbardStratonovichRHMC.lean)
    # Source: Clark & Kennedy, PRL 98:051601 (2007); Schaich & DeGrand, CPC 190:200 (2015)
    if args.hasenbusch:
        K = args.hasenbusch_k
        hp = args.hasenbusch_poles
        hcoeffs = prepare_hasenbusch_coefficients(K, lam_min, lam_max, n_poles=hp)
        print(f"  Hasenbusch K={K}: {hcoeffs['n_factors']} factors × {hp} poles/factor")
        print(f"  mu^2 schedule: {[f'{m:.3f}' for m in hcoeffs['mu_sq_schedule']]}")
        print(f"  Integrator levels: {hcoeffs['n_steps_per_level'].tolist()}")

        tasks = []
        for i, g in enumerate(g_values):
            tasks.append((L, g, args.n_traj, args.n_therm, tau, hcoeffs,
                           args.seed + i * 10000, cg, args.chunk_size))
    else:
        a0, alphas, betas = compute_zolotarev_coefficients(n_poles, lam_min, lam_max, -0.25)
        a0_hb, alphas_hb, betas_hb = compute_zolotarev_coefficients(n_poles, lam_min, lam_max, -0.875)

        tasks = []
        for i, g in enumerate(g_values):
            tasks.append((L, g, args.n_traj, args.n_therm, args.n_md_steps, tau,
                           a0, np.array(alphas), np.array(betas),
                           a0_hb, np.array(alphas_hb), np.array(betas_hb),
                           args.seed + i * 10000, cg, args.chunk_size))

    print(f"\n  Starting...\n", flush=True)
    t0 = time.time()

    # Write PID file so epoch script and users can find us
    pid_file = _data_dir(L) / ".rhmc.pid"
    pid_file.write_text(str(os.getpid()))

    pool = mp.Pool(args.workers)

    def _cleanup():
        """Kill all workers on ANY exit — normal, signal, or crash."""
        try:
            pool.terminate()
            pool.join(timeout=5)
        except Exception:
            pass
        pid_file.unlink(missing_ok=True)

    atexit.register(_cleanup)

    def _signal_handler(signum, frame):
        sig_name = signal.Signals(signum).name
        print(f"\n  Received {sig_name} — shutting down workers...", flush=True)
        _cleanup()
        raise SystemExit(0)

    signal.signal(signal.SIGTERM, _signal_handler)
    signal.signal(signal.SIGINT, _signal_handler)

    try:
        worker = _run_coupling_chunked_hasenbusch if args.hasenbusch else _run_coupling_chunked
        results = pool.map(worker, tasks)
    finally:
        _cleanup()

    elapsed = time.time() - t0
    print(f"\n{'='*70}")
    print(f"Complete: {elapsed:.0f}s ({elapsed/3600:.1f}h)")
    print(f"{'='*70}")

    for r in sorted(results, key=lambda x: x['g']):
        if r['status'] == 'already_complete':
            print(f"  g={r['g']:.3f}: already done ({r['n_traj']} traj)")
        else:
            print(f"  g={r['g']:.3f}: h_sq={r.get('h_sq',0):.4f}, "
                  f"accept={r.get('acceptance',0):.2f}, {r.get('time',0):.0f}s")


if __name__ == '__main__':
    mp.set_start_method('spawn')
    main()
