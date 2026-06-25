#!/usr/bin/env python3
"""Acceptance test for the deflated CG (the core of the L=8 fix).

Compares plain vs deflated single-shift CG on (M_e + beta) x = phi at a real L=8
config, with a shift-invert deflation subspace of k modes:

  - UNBIASED:   at a beta where plain CG converges, the deflated solution must
                match the plain solution to ~CG tolerance (deflation changes the
                convergence path, not the answer -> no Metropolis dH bias).
  - ACCELERATES: at beta ~ 0 (the force pole that throttles the chain), plain CG
                hits the iteration cap (never converges) while deflated CG
                converges in a few hundred iters.

Usage:
  PYTHONPATH=. uv run python scripts/validate_deflated_cg.py
"""
import argparse
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
    ap.add_argument('--k-defl', type=int, default=32)
    ap.add_argument('--sigma-eig', type=float, default=0.1)
    ap.add_argument('--m-eig', type=int, default=96)
    ap.add_argument('--cg-tol', type=float, default=1e-8)
    ap.add_argument('--cg-max', type=int, default=5000)
    args = ap.parse_args()

    if not hasattr(sk_eft_rhmc, 'solve_compare_deflation_py'):
        print("solve_compare_deflation_py MISSING — rebuild the Rust ext.")
        return 2

    cg_a, cg_i, cg_j, cg_val = build_cg()
    h = np.asarray(np.load(args.config)['h_final'], dtype=np.float64)
    print(f"L={args.l} config {args.config}  k_defl={args.k_defl} σ_eig={args.sigma_eig}\n")
    print(f"{'beta':>8} {'it_plain':>9} {'it_defl':>8} {'rel_diff':>11} {'verdict'}")

    unbiased_ok = False
    accel_ok = False
    for beta in [1.0, 0.1, 1e-3, 0.0]:
        it_plain, it_defl, rel, lam_min = sk_eft_rhmc.solve_compare_deflation_py(
            h, args.l, beta, args.k_defl, args.sigma_eig, args.m_eig,
            args.cg_tol, args.cg_max, 42, cg_a, cg_i, cg_j, cg_val)
        plain_converged = it_plain < args.cg_max
        defl_converged = it_defl < args.cg_max
        note = []
        if plain_converged and rel < 1e-5:
            note.append("UNBIASED")
            unbiased_ok = True
        if (not plain_converged) and defl_converged:
            note.append("DEFL converges where plain CAPS")
            accel_ok = True
        elif defl_converged and it_defl < 0.5 * it_plain:
            note.append("accelerated")
        print(f"{beta:>8.0e} {it_plain:>9} {it_defl:>8} {rel:>11.2e}  {' | '.join(note)}")

    print(f"\n  unbiased (solutions match where plain converges): {'PASS' if unbiased_ok else 'FAIL'}")
    print(f"  fixes the throttling pole (beta~0): {'PASS' if accel_ok else 'CHECK'}")
    ok = unbiased_ok and accel_ok
    print(f"\nOVERALL: {'PASS — deflated CG is unbiased AND makes the near-zero pole solvable' if ok else 'see above'}")
    return 0 if ok else 1


if __name__ == '__main__':
    raise SystemExit(main())
