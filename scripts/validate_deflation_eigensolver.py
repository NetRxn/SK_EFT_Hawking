#!/usr/bin/env python3
"""Acceptance test for the deflation eigensolver (sk_eft_rhmc.lanczos_smallest_eigenpairs_eo_py).

Deflation needs the k smallest eigenpairs of M_e to small residual. This checks
whether the Rust eigensolver actually resolves the clustered near-zero modes on a
real L=8 config, by computing relative residuals ‖M_e v - λ v‖ / λ and comparing
the smallest eigenvalue to the independently-measured lam_min (~5.7e-5 at g=2.0).

PASS = max relative residual < 1e-4 and smallest λ within ~2x of the reference.

Current status (2026-06-25, plain-Lanczos eigensolver): FAIL — plain Lanczos
converges largest-first, so the smallest Ritz values have O(1-20) relative
residuals. The fix is a shift-invert (or LOBPCG) smallest-eigenvalue method.
This script is the gate for that rebuild.

Usage:
  PYTHONPATH=. uv run python scripts/validate_deflation_eigensolver.py
  PYTHONPATH=. uv run python scripts/validate_deflation_eigensolver.py --config data/rhmc/L8_v1/L8_g0.5000.npz
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
    ap.add_argument('--ladder', type=str, default='8:24:10,16:48:12,16:96:20',
                    help='comma list of k:m:restarts')
    args = ap.parse_args()

    if not hasattr(sk_eft_rhmc, 'lanczos_smallest_eigenpairs_eo_py'):
        print("sk_eft_rhmc.lanczos_smallest_eigenpairs_eo_py MISSING — rebuild the Rust ext.")
        return 2

    L = args.l
    cg_a, cg_i, cg_j, cg_val = build_cg()
    h = np.asarray(np.load(args.config)['h_final'], dtype=np.float64)
    print(f"L={L}  config {args.config}  ||h||={np.linalg.norm(h):.2f}  "
          f"ref lam_min≈{args.ref_lam_min:.1e}")

    overall_pass = False
    for spec in args.ladder.split(','):
        k, m, restarts = (int(x) for x in spec.split(':'))
        t0 = time.time()
        evals, resids = sk_eft_rhmc.lanczos_smallest_eigenpairs_eo_py(
            h, L, k, m, 1e-6, restarts, 42, cg_a, cg_i, cg_j, cg_val)
        evals = np.asarray(evals); resids = np.asarray(resids)
        rel = resids / np.maximum(evals, 1e-30)
        lam_min = float(evals.min())
        max_rel = float(rel.max())
        ok = max_rel < 1e-4 and lam_min < 2 * args.ref_lam_min
        overall_pass = overall_pass or ok
        print(f"\n  k={k} m={m} r={restarts} ({time.time()-t0:.0f}s): "
              f"lam_min={lam_min:.3e}  max_rel_resid={max_rel:.1e}  "
              f"-> {'PASS' if ok else 'FAIL'}")
    print(f"\nOVERALL: {'PASS — eigensolver resolves the near-zero modes' if overall_pass else 'FAIL — needs shift-invert/LOBPCG rebuild'}")
    return 0 if overall_pass else 1


if __name__ == '__main__':
    raise SystemExit(main())
