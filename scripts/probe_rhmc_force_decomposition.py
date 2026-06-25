#!/usr/bin/env python3
"""Force / spectrum decomposition probe — quantifies the payoff of the L=8
acceleration levers (multi-timescale pole-splitting, deflation) with measured
numbers instead of estimates.

Builds the SAME operator the production force uses — A†A = -A^2, where A is the
antisymmetric fermion matrix exposed as sk_eft_rhmc.apply_fermion_matrix_py —
and VALIDATES it against sk_eft_rhmc.estimate_spectral_range_py before trusting
any number. Then measures, on a representative L=8 config:

  (1) Per-Zolotarev-pole stiffness: for each rational shift sigma_k, the
      condition number (lam_max+sigma_k)/(lam_min+sigma_k), the CG iterations to
      solve (A†A+sigma_k)x=phi, and the force-norm contribution alpha_k*||x_k||.
      -> Which poles are expensive (small sigma) vs cheap (large sigma), and how
         much force each carries. Decides the multi-timescale / pole-split win.

  (2) Deflation payoff: the lowest eigenvalues of A†A. Removing the k smallest
      modes cuts the condition number from lam_max/lam_min to lam_max/lam_{k+1};
      CG iterations scale ~sqrt(kappa), so the speedup ~ sqrt(kappa_full/kappa_defl).

Read-only. Records JSON + console tables under data/rhmc/force_decomp/.

Usage:
  PYTHONPATH=. uv run python scripts/probe_rhmc_force_decomposition.py
  PYTHONPATH=. uv run python scripts/probe_rhmc_force_decomposition.py --g 2.0 --n-poles 12 --n-src 4
"""
import argparse
import json
import time
from pathlib import Path

import numpy as np
from scipy.sparse.linalg import LinearOperator, cg, eigsh

from src.core.constants import MAJORANA_GAMMA_8x8, MAJORANA_J1
from src.vestigial.hs_rhmc import compute_zolotarev_coefficients
import sk_eft_rhmc

OUT_DIR = Path("data/rhmc/force_decomp")


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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--l', type=int, default=8)
    ap.add_argument('--g', type=float, default=2.0)
    ap.add_argument('--n-poles', type=int, default=12)
    ap.add_argument('--n-src', type=int, default=3, help='random sources for force-norm averaging')
    ap.add_argument('--n-low', type=int, default=8, help='# lowest eigenvalues for deflation table')
    ap.add_argument('--warm-from', type=str, default='data/rhmc/L8_v1/L8_g2.0000.npz')
    ap.add_argument('--cg-tol', type=float, default=1e-6,
                    help='CG tol for the per-pole iteration-count diagnostic (1e-6 is plenty).')
    args = ap.parse_args()

    L, g = args.l, args.g
    V = L**4
    NF = 8 * V  # fermion vector dimension
    cg_e = build_cg_entries()
    cg_a, cg_i, cg_j, cg_val = cg_e

    d = np.load(args.warm_from)
    h = np.asarray(d['h_final'], dtype=np.float64).reshape(V, 4, 4)
    print(f"L={L} g={g} V={V}  fermion-dim={NF}  warm config from {args.warm_from}", flush=True)

    apply_count = [0]
    def A(v):
        apply_count[0] += 1
        return np.asarray(sk_eft_rhmc.apply_fermion_matrix_py(h, v, L, cg_a, cg_i, cg_j, cg_val))
    def AtA(v):  # A†A = -A^2 (A real antisymmetric)
        return -A(A(v))
    Op = LinearOperator((NF, NF), matvec=AtA, dtype=np.float64)

    # ---- validate operator against the production spectral-range estimator ----
    lo_est, hi_est = sk_eft_rhmc.estimate_spectral_range_py(L, g, 42, 60, cg_a, cg_i, cg_j, cg_val)
    t0 = time.time()
    lam_hi = float(eigsh(Op, k=1, which='LA', tol=1e-3, return_eigenvectors=False)[0])
    print(f"  validate: eigsh lam_max={lam_hi:.3f}  vs estimate {hi_est:.3f}  "
          f"(ratio {lam_hi/hi_est:.3f})", flush=True)

    # ---- low spectrum for deflation ----
    print(f"  computing {args.n_low} lowest eigenvalues (deflation table)...", flush=True)
    try:
        low = np.sort(eigsh(Op, k=args.n_low, which='SA', tol=5e-2, maxiter=2500,
                            ncv=min(NF - 1, 4 * args.n_low + 20), return_eigenvectors=False))
    except Exception as e:
        print(f"    eigsh SA failed ({e}); falling back to estimate lam_min", flush=True)
        low = np.array([lo_est])
    lam_lo = float(low[0])
    print(f"  lam_min={lam_lo:.5f} lam_max={lam_hi:.3f}  kappa={lam_hi/lam_lo:.0f}", flush=True)

    # ---- per-Zolotarev-pole stiffness + cost + force contribution ----
    a0, alphas, betas = compute_zolotarev_coefficients(args.n_poles, lo_est, hi_est, -0.25)
    alphas = np.asarray(alphas); betas = np.asarray(betas)
    rng = np.random.default_rng(7)
    srcs = [rng.standard_normal(NF) for _ in range(args.n_src)]

    pole_rows = []
    order = np.argsort(betas)  # smallest shift (stiffest) first
    for rank, k in enumerate(order):
        sig = float(betas[k]); al = float(alphas[k])
        cond = (hi_est + sig) / (lo_est + sig)
        iters_list, fnorm_list = [], []
        ShiftOp = LinearOperator((NF, NF), matvec=lambda v, s=sig: AtA(v) + s * v, dtype=np.float64)
        for phi in srcs:
            it = [0]
            x, info = cg(ShiftOp, phi, rtol=args.cg_tol, atol=0.0, maxiter=5000,
                         callback=lambda xk: it.__setitem__(0, it[0] + 1))
            iters_list.append(it[0])
            fnorm_list.append(al * float(np.linalg.norm(x)))
        pole_rows.append(dict(
            rank=rank, sigma=sig, alpha=al, cond=cond,
            cg_iters=float(np.mean(iters_list)), cg_iters_max=int(np.max(iters_list)),
            force_norm=float(np.mean(fnorm_list)),
        ))
        print(f"    pole[{rank:2d}] sigma={sig:11.4f} cond={cond:9.1f} "
              f"cg_iters={np.mean(iters_list):6.1f} force~{np.mean(fnorm_list):.3e}", flush=True)

    # ---- summarize payoff factors ----
    total_force = sum(r['force_norm'] for r in pole_rows) or 1.0
    # smallest-3 shifts = the "expensive/light" group
    light = pole_rows[:3]
    heavy = pole_rows[3:]
    light_force_frac = sum(r['force_norm'] for r in light) / total_force
    light_iter_share = sum(r['cg_iters'] for r in light) / (sum(r['cg_iters'] for r in pole_rows) or 1)
    # multishift cost is set by the smallest shift; pole-split coarse cost ~ smallest light shift
    iters_full = pole_rows[0]['cg_iters']          # multishift ≈ smallest-shift CG
    iters_heavy_only = heavy[0]['cg_iters'] if heavy else iters_full

    print("\n" + "=" * 78)
    print("MEASURED PAYOFF FACTORS")
    print("=" * 78)
    print(f"  multishift CG cost is set by the smallest shift: ~{iters_full:.0f} iters")
    print(f"  light (3 smallest-shift) poles carry {100*light_force_frac:.1f}% of the force")
    print(f"     and {100*light_iter_share:.1f}% of the per-pole CG cost.")
    print(f"  -> multi-timescale / pole-split: put the {len(light)} light poles on the COARSE")
    print(f"     timescale (m_outer evals), the {len(heavy)} heavy poles (cheap, "
          f"~{iters_heavy_only:.0f} iters) on the FINE timescale.")
    print(f"     Naive win ~ md/m_outer if the light-pole force ({100*light_force_frac:.0f}% of total) is soft.")
    # deflation
    print(f"\n  DEFLATION: kappa_full = {lam_hi/lam_lo:.0f}")
    defl_rows = []
    for kk in [1, 2, 4, 8, min(args.n_low - 1, 11)]:
        if kk < len(low):
            kdefl = lam_hi / low[kk]
            speed = np.sqrt((lam_hi / lam_lo) / kdefl)
            defl_rows.append(dict(k=kk, lam_kp1=float(low[kk]), kappa_defl=float(kdefl),
                                  cg_speedup=float(speed)))
            print(f"    deflate {kk:2d} modes -> lam_{{k+1}}={low[kk]:.4f} "
                  f"kappa={kdefl:8.0f}  CG speedup ~{speed:.2f}x")

    OUT_DIR.mkdir(parents=True, exist_ok=True)
    stamp = time.strftime("%Y%m%dT%H%M%S")
    out = OUT_DIR / f"force_decomp_L{L}_g{g}_{stamp}.json"
    out.write_text(json.dumps(dict(
        L=L, g=g, n_poles=args.n_poles, n_src=args.n_src,
        lam_min=lam_lo, lam_max=lam_hi, kappa=lam_hi / lam_lo,
        low_eigs=[float(x) for x in low],
        poles=pole_rows, deflation=defl_rows,
        light_force_frac=light_force_frac, light_iter_share=light_iter_share,
        total_A_applies=apply_count[0], timestamp=stamp,
    ), indent=2))
    print(f"\n  total A-applies: {apply_count[0]}   recorded -> {out}")
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
