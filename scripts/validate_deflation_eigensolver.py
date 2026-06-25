#!/usr/bin/env python3
"""Acceptance test for the deflation eigensolver.

Deflation needs the k smallest eigenpairs of M_e. The SHIFT-INVERT solver
(sk_eft_rhmc.shift_invert_smallest_eigenpairs_eo_py) runs Lanczos on (M_e+σ)^-1
so the near-zero modes converge first.

The right quality metric for a κ~1e7 operator is NOT ‖M_e v - λv‖/λ (which is
huge for any vector because λ_max amplifies tiny contamination), but:
  - eigenvalue agreement with the independent scipy reference (λ_min ~5.7e-5), and
  - the high-mode CONTAMINATION amplitude  ‖M_e v - λv‖ / λ_max  (≪1 ⇒ the vector
    lies in the low-mode subspace ⇒ good for deflation).

PASS = λ_min within 2x of reference AND max contamination < 5e-3.

The legacy plain-Lanczos solver (lanczos_smallest_eigenpairs_eo_py) FAILS this
(it converges largest-first); shift-invert PASSES.

Usage:
  PYTHONPATH=. uv run python scripts/validate_deflation_eigensolver.py
  PYTHONPATH=. uv run python scripts/validate_deflation_eigensolver.py --config data/rhmc/L8_v1/L8_g0.5000.npz --ref-lam-min 2.7e-5
"""
import argparse
import time
import numpy as np

from src.core.constants import MAJORANA_GAMMA_8x8, MAJORANA_J1
import sk_eft_rhmc


def build_cg():
    CG = np.array([MAJORANA_J1 @ MAJORANA_GAMMA_8x8[a] for a in range(4)])
    a_, i_, j_, v_ = [], [], [], []
    for a in range(4):
        for I in range(8):
            for J in range(8):
                v = CG[a, I, J]
                if abs(v) > 1e-15:
                    a_.append(a); i_.append(I); j_.append(J); v_.append(v)
    return (np.array(a_, np.int64), np.array(i_, np.int64),
            np.array(j_, np.int64), np.array(v_, np.float64))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--l', type=int, default=8)
    ap.add_argument('--config', type=str, default='data/rhmc/L8_v1/L8_g2.0000.npz')
    ap.add_argument('--ref-lam-min', type=float, default=5.7e-5)
    ap.add_argument('--ladder', type=str, default='16:0.1:48,32:0.1:96',
                    help='comma list of k:sigma:m')
    ap.add_argument('--cg-tol', type=float, default=1e-8)
    ap.add_argument('--cg-max', type=int, default=2000)
    args = ap.parse_args()

    if not hasattr(sk_eft_rhmc, 'shift_invert_smallest_eigenpairs_eo_py'):
        print("shift_invert_smallest_eigenpairs_eo_py MISSING — rebuild the Rust ext.")
        return 2

    L = args.l
    cg_a, cg_i, cg_j, cg_val = build_cg()
    h = np.asarray(np.load(args.config)['h_final'], dtype=np.float64)
    print(f"L={L}  config {args.config}  ||h||={np.linalg.norm(h):.2f}  "
          f"ref λ_min≈{args.ref_lam_min:.1e}")

    overall = False
    for spec in args.ladder.split(','):
        k, sigma, m = spec.split(':')
        k, sigma, m = int(k), float(sigma), int(m)
        t0 = time.time()
        evals, resids = sk_eft_rhmc.shift_invert_smallest_eigenpairs_eo_py(
            h, L, k, sigma, m, args.cg_tol, args.cg_max, 42, cg_a, cg_i, cg_j, cg_val)
        evals = np.asarray(evals); resids = np.asarray(resids)
        lam_max_ref = 6.0e2  # ~λ_max of M_e at L=8
        contam = resids / lam_max_ref
        lam_min = float(evals.min())
        ok = (lam_min < 2 * args.ref_lam_min) and (contam.max() < 5e-3)
        overall = overall or ok
        print(f"\n  k={k} σ={sigma} m={m}  ({time.time()-t0:.0f}s, {len(evals)} pairs)")
        print(f"    λ: {', '.join(f'{e:.2e}' for e in evals[:6])} ...")
        print(f"    λ_min={lam_min:.3e} (ref {args.ref_lam_min:.1e})  "
              f"max contamination={contam.max():.1e}  -> {'PASS' if ok else 'FAIL'}")
    print(f"\nOVERALL: {'PASS — shift-invert resolves the near-zero modes (deflation foundation ready)' if overall else 'FAIL'}")
    return 0 if overall else 1


if __name__ == '__main__':
    raise SystemExit(main())
