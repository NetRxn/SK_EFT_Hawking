#!/usr/bin/env python3
"""L=8 MD step-size (epsilon) scan for the Rust HS+RHMC backend.

Purpose: the April L=8 production stalled at ~0% acceptance because it ran at
md=30 (epsilon too large for L=8's stiffness). The integrator is correct
(verified: scripts/verify_rhmc_correctness.py), so the only open question for a
restart is *what md gives acceptable <|dH|> / acceptance at L=8*. This scans a
ladder of md values at a fixed coupling, measures <|dH|> and acceptance, fits
the <|dH|> ∝ eps^p law, and extrapolates the md needed for a target acceptance.

To fit a ~tens-of-minutes budget it (a) warm-starts from an existing L=8
configuration to skip cold-CG cost, (b) runs the md ladder across parallel
processes, (c) uses short trajectory counts (dH measures integrator error per
trajectory, which is meaningful even before full equilibration).

Records a JSON + console table under data/rhmc/stepsize_scan/.

Usage:
  PYTHONPATH=. uv run python scripts/scan_rhmc_l8_stepsize.py --probe         # 1-traj timing probe
  PYTHONPATH=. uv run python scripts/scan_rhmc_l8_stepsize.py --md 20,40,80 --n-meas 3
"""
import argparse
import json
import multiprocessing as mp
import time
from pathlib import Path

import numpy as np

from src.core.constants import MAJORANA_GAMMA_8x8, MAJORANA_J1
from src.vestigial.hs_rhmc import compute_zolotarev_coefficients

OUT_DIR = Path("data/rhmc/stepsize_scan")
DEFAULT_WARM = Path("data/rhmc/L8_v1/L8_g2.0000.npz")


def build_cg_entries():
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


def make_coeffs(L, g, seed, cg, n_poles):
    import sk_eft_rhmc
    cg_a, cg_i, cg_j, cg_val = cg
    lam_min, lam_max = sk_eft_rhmc.estimate_spectral_range_py(L, g, seed, 50, cg_a, cg_i, cg_j, cg_val)
    a0, alphas, betas = compute_zolotarev_coefficients(n_poles, lam_min, lam_max, -0.25)
    a0_hb, alphas_hb, betas_hb = compute_zolotarev_coefficients(n_poles, lam_min, lam_max, -0.875)
    return dict(a0=float(a0), alphas=np.asarray(alphas), betas=np.asarray(betas),
                a0_hb=float(a0_hb), alphas_hb=np.asarray(alphas_hb), betas_hb=np.asarray(betas_hb),
                lam_min=float(lam_min), lam_max=float(lam_max))


def _run_one(task):
    """Run one md value. Top-level for spawn picklability."""
    import sk_eft_rhmc
    (L, g, md, tau, n_meas, n_therm, seed, coeffs, cg, warm_h) = task
    cg_a, cg_i, cg_j, cg_val = cg
    t0 = time.time()
    r = sk_eft_rhmc.run_rhmc_rust_eo_2pf(
        l=L, g=g, n_traj=n_meas + n_therm, n_therm=n_therm, n_meas_skip=1,
        n_md_steps=md, tau=tau,
        alpha_0=coeffs['a0'], alphas=coeffs['alphas'], betas=coeffs['betas'],
        alpha_0_hb=coeffs['a0_hb'], alphas_hb=coeffs['alphas_hb'], betas_hb=coeffs['betas_hb'],
        seed=seed, cg_a=cg_a, cg_i=cg_i, cg_j=cg_j, cg_val=cg_val,
        h_init=warm_h,
    )
    elapsed = time.time() - t0
    dh = np.abs(np.asarray(r['delta_h_history'], dtype=float))
    n = max(1, n_meas)
    return dict(
        md=md, eps=tau / md,
        dh_mean=float(dh.mean()) if dh.size else float('nan'),
        dh_med=float(np.median(dh)) if dh.size else float('nan'),
        dh_max=float(dh.max()) if dh.size else float('nan'),
        acc_metropolis=float(np.mean(np.exp(-dh))) if dh.size else float('nan'),  # <min(1,e^-dH)> proxy
        acc_reported=float(r['acceptance_rate']),
        n_traj=int(dh.size), seconds=elapsed, sec_per_traj=elapsed / max(1, n_meas + n_therm),
    )


def load_warm(path, allow_missing=True):
    p = Path(path)
    if not p.exists():
        if allow_missing:
            print(f"  (warm-start file {p} missing — cold start)")
            return None
        raise FileNotFoundError(p)
    d = np.load(p)
    h = d.get('h_final', None)
    if h is None:
        return None
    print(f"  warm-start h_final from {p}  shape={np.asarray(h).shape}")
    return np.asarray(h, dtype=np.float64)


def extrapolate_target_md(rows, tau, target_acc=0.6):
    """Fit log<|dH|> = p*log(eps)+c, invert for the eps giving Metropolis
    acceptance ~= target_acc (i.e. <|dH|> ~= -ln(target_acc) roughly)."""
    eps = np.array([r['eps'] for r in rows])
    dh = np.array([r['dh_mean'] for r in rows])
    good = (dh > 0) & np.isfinite(dh)
    if good.sum() < 2:
        return None
    p, c = np.polyfit(np.log(eps[good]), np.log(dh[good]), 1)
    out = {'slope_p': float(p)}
    # Extrapolation is only meaningful when the integrator actually scales:
    # a correct symplectic force gives <|dH|> ∝ eps^p with p ≳ 1.5 (→0 as eps→0).
    # p ≤ 0 means <|dH|> does NOT fall with smaller steps — the signature of a
    # WRONG/non-converged force (e.g. CG hitting its cap on an ill-conditioned
    # spectrum), NOT a step-size problem. Refuse to extrapolate in that case.
    if p < 1.0:
        out['valid'] = False
        out['diagnosis'] = (
            "slope p<1: <|dH|> does not improve as eps→0. The integrator is NOT "
            "step-size-limited — the force is wrong (likely CG non-convergence on "
            "an ill-conditioned operator). Step-size tuning will NOT fix this; "
            "harden the fermion solve (deflation / spectral-range / preconditioner).")
        return out
    out['valid'] = True
    for tag, dh_target in (('dH<=1.0', 1.0), ('dH<=0.5', 0.5)):
        eps_t = np.exp((np.log(dh_target) - c) / p)
        md_t = tau / eps_t
        out[tag] = {'eps': float(eps_t), 'md': float(md_t)}
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--l', type=int, default=8)
    ap.add_argument('--g', type=float, default=2.0)
    ap.add_argument('--tau', type=float, default=1.0)
    ap.add_argument('--md', type=str, default='20,40,80', help='comma-separated md ladder')
    ap.add_argument('--n-meas', type=int, default=3)
    ap.add_argument('--n-therm', type=int, default=1)
    ap.add_argument('--n-poles', type=int, default=12)
    ap.add_argument('--workers', type=int, default=3)
    ap.add_argument('--seed', type=int, default=4242)
    ap.add_argument('--warm-from', type=str, default=str(DEFAULT_WARM))
    ap.add_argument('--probe', action='store_true',
                    help='1-trajectory timing probe at md=--probe-md, then exit (for sizing).')
    ap.add_argument('--probe-md', type=int, default=40)
    args = ap.parse_args()

    L, g, tau = args.l, args.g, args.tau
    cg = build_cg_entries()
    print(f"L={L} g={g} tau={tau}  building Zolotarev coeffs (n_poles={args.n_poles})...", flush=True)
    coeffs = make_coeffs(L, g, args.seed, cg, args.n_poles)
    print(f"  spectral range [{coeffs['lam_min']:.3f}, {coeffs['lam_max']:.1f}]  "
          f"kappa={coeffs['lam_max']/coeffs['lam_min']:.0f}", flush=True)
    warm_h = load_warm(args.warm_from)

    if args.probe:
        print(f"\nPROBE: 1 trajectory at md={args.probe_md} (warm={'yes' if warm_h is not None else 'no'})...",
              flush=True)
        res = _run_one((L, g, args.probe_md, tau, 1, 0, args.seed, coeffs, cg, warm_h))
        spt = res['sec_per_traj']
        print(f"  md={args.probe_md}: {spt:.1f} s/traj  =>  ~{spt/args.probe_md:.2f} s/MD-step  "
              f"<|dH|>={res['dh_mean']:.3f}", flush=True)
        print(f"  budget estimate for a ladder (n_traj each), parallel workers:")
        for md in [20, 40, 80, 160]:
            print(f"    md={md:<4d} ~{spt/args.probe_md*md:.0f} s/traj", flush=True)
        return 0

    md_ladder = [int(x) for x in args.md.split(',')]
    tasks = [(L, g, md, tau, args.n_meas, args.n_therm, args.seed + i, coeffs, cg, warm_h)
             for i, md in enumerate(md_ladder)]
    print(f"\nScanning md={md_ladder}  n_meas={args.n_meas} n_therm={args.n_therm}  "
          f"workers={args.workers}", flush=True)
    t0 = time.time()
    with mp.Pool(min(args.workers, len(tasks))) as pool:
        rows = pool.map(_run_one, tasks)
    rows = sorted(rows, key=lambda r: r['md'])
    wall = time.time() - t0

    print("\n" + "=" * 84)
    print(f"L={L} g={g} STEP-SIZE SCAN  (wall {wall:.0f}s)")
    print("=" * 84)
    print(f"{'md':>5} {'eps':>9} {'<|dH|>':>9} {'med':>8} {'max':>8} "
          f"{'<e^-dH>':>9} {'acc_rep':>8} {'s/traj':>8}")
    for r in rows:
        print(f"{r['md']:>5} {r['eps']:>9.5f} {r['dh_mean']:>9.3f} {r['dh_med']:>8.3f} "
              f"{r['dh_max']:>8.2f} {r['acc_metropolis']:>9.3f} {r['acc_reported']:>8.2f} "
              f"{r['sec_per_traj']:>8.0f}")
    extrap = extrapolate_target_md(rows, tau)
    if extrap:
        print(f"\n  <|dH|> ∝ eps^p  fit slope p = {extrap['slope_p']:.2f}")
        if not extrap.get('valid', True):
            print(f"  ⚠ EXTRAPOLATION INVALID: {extrap['diagnosis']}")
        else:
            for tag in ('dH<=1.0', 'dH<=0.5'):
                e = extrap[tag]
                print(f"  target {tag}: eps≈{e['eps']:.5f}  =>  md≈{e['md']:.0f}")

    OUT_DIR.mkdir(parents=True, exist_ok=True)
    stamp = time.strftime("%Y%m%dT%H%M%S")
    out = OUT_DIR / f"scan_L{L}_g{g}_{stamp}.json"
    payload = dict(
        L=L, g=g, tau=tau, n_poles=args.n_poles, n_meas=args.n_meas, n_therm=args.n_therm,
        warm_from=args.warm_from, seed=args.seed, wall_seconds=wall,
        spectral=dict(lam_min=coeffs['lam_min'], lam_max=coeffs['lam_max']),
        rows=rows, extrapolation=extrap, timestamp=stamp,
    )
    out.write_text(json.dumps(payload, indent=2))
    print(f"\n  recorded -> {out}")
    return 0


if __name__ == '__main__':
    mp.set_start_method('spawn')
    raise SystemExit(main())
