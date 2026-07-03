#!/usr/bin/env python3
"""CUDA validation gate for the eo stencil RHMC — RUN THIS ON THE 3090 BEFORE any
production `run_rhmc_gpu_production.py --device cuda` run.

The parallel CPU runner (`run_rhmc_parallel.py`) is process-parallel and CPU-only.
The GPU path is the BATCHED driver (`run_rhmc_gpu_production.py --device cuda`), which
was never exercised on real CUDA hardware in development. This script certifies it before
you trust a multi-day run:

  1. CORRECTNESS (device-independence): with identical FP64 inputs, apply_Me / eo_action /
     eo_compute_force must agree between CPU and CUDA to CG-tolerance. This checks the
     operator, the solve, and the force — i.e. the factor-2 fix and eo reduction hold on GPU.
  2. UNBIASEDNESS: run a short mixed-precision (FP32 MD + FP64 accept) chain on CUDA and
     check the Creutz identity ⟨exp(−ΔH)⟩ ≈ 1 and sane acceptance — the production path is
     exact-Metropolis on GPU.
  3. THROUGHPUT: measure s/traj on CUDA → real ETA for a 450-traj production chain.

Usage (on the 3090 box):
  PYTHONPATH=. python scripts/validate_cuda_rhmc.py
  PYTHONPATH=. python scripts/validate_cuda_rhmc.py --l 8 --mass 0.1 --g 3.0 --n-traj 6
"""
import argparse
import time

import torch

import src.vestigial.hs_rhmc_stencil as st
from scripts.run_rhmc_gpu_production import build_coeffs

P = lambda *a: print(*a, flush=True)


def maxrel(a, b):
    a = a.detach().to("cpu", torch.float64)
    b = b.detach().to("cpu", torch.float64)
    denom = b.abs().max().clamp_min(1e-30)
    return float((a - b).abs().max() / denom)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--l", type=int, default=8)
    ap.add_argument("--mass", type=float, default=0.1)
    ap.add_argument("--g", type=float, default=3.0)
    ap.add_argument("--replicas", type=int, default=4)
    ap.add_argument("--n-md", type=int, default=17)
    ap.add_argument("--eps", type=float, default=0.03)
    ap.add_argument("--n-poles", type=int, default=14)
    ap.add_argument("--n-traj", type=int, default=6, help="mixed-chain trajectories to time/unbias-check")
    ap.add_argument("--tol", type=float, default=1e-8, help="parity CG tolerance")
    ap.add_argument("--rtol", type=float, default=1e-5, help="max acceptable CPU↔CUDA relative diff")
    args = ap.parse_args()

    torch.set_default_dtype(torch.float64)
    if not torch.cuda.is_available():
        P("CUDA not available on this machine — run this ON the 3090 box. ABORT.")
        return 2
    dev = torch.device("cuda")
    P(f"CUDA device: {torch.cuda.get_device_name(0)}")
    L, msq, g, R = args.l, args.mass ** 2, args.g, args.replicas
    V = L ** 4
    cpu = torch.device("cpu")

    # identical FP64 inputs on both devices
    gen = torch.Generator().manual_seed(20260702)
    h = (2.0 * g) ** 0.5 * torch.randn(R, V, 4, 4, generator=gen)
    pe = torch.randn(R, V // 2, 8, generator=gen)
    coeffs, lam = build_coeffs(L, g, msq, args.n_poles, 1)
    P(f"L={L} m={args.mass} g={g} R={R}  range[{msq:.4g},{lam+msq:.1f}] κ={(lam+msq)/msq:.0f}\n")

    fwd_c, back_c = st.neighbor_tables(L, cpu); eo_c = st.eo_tables(L, cpu)
    fwd_d, back_d = st.neighbor_tables(L, dev); eo_d = st.eo_tables(L, dev)
    blk_c = st.hopping_blocks(h, L)
    hd, ped = h.to(dev), pe.to(dev)
    blk_d = st.hopping_blocks(hd, L, device=dev, dtype=torch.float64)

    # ---- 1. CORRECTNESS: FP64 device-independence -----------------------------------------
    P("[1] CORRECTNESS — FP64 CPU vs CUDA (want < %.0e):" % args.rtol)
    d_mv = maxrel(st.apply_Me(ped, blk_d, eo_d, shift=msq), st.apply_Me(pe, blk_c, eo_c, shift=msq))
    d_ac = maxrel(st.eo_action(hd, ped, g, msq, eo_d, fwd_d, back_d, L, tol=args.tol),
                  st.eo_action(h, pe, g, msq, eo_c, fwd_c, back_c, L, tol=args.tol))
    d_fr = maxrel(st.eo_compute_force(hd, ped, g, msq, eo_d, fwd_d, back_d, L, tol=args.tol),
                  st.eo_compute_force(h, pe, g, msq, eo_c, fwd_c, back_c, L, tol=args.tol))
    for name, d in (("apply_Me", d_mv), ("eo_action", d_ac), ("eo_compute_force", d_fr)):
        P(f"    {name:18s} rel-diff = {d:.2e}   {'PASS' if d < args.rtol else 'FAIL'}")
    correctness_ok = max(d_mv, d_ac, d_fr) < args.rtol

    # ---- 2. UNBIASEDNESS + 3. THROUGHPUT: mixed chain on CUDA -----------------------------
    P(f"\n[2/3] UNBIASEDNESS + THROUGHPUT — {args.n_traj} mixed-precision trajectories on CUDA:")
    gen_dev = torch.Generator(device=dev).manual_seed(7)
    gen_cpu = torch.Generator().manual_seed(7)
    hc = h.clone()
    dHs, accs, dt = [], [], []
    for t in range(args.n_traj):
        torch.cuda.synchronize(); t0 = time.time()
        hc, dH, acc = st.eo_rhmc_trajectory_mixed(hc, g, msq, coeffs, eo_c, fwd_c, back_c,
                                                  eo_d, fwd_d, back_d, L, args.eps, args.n_md,
                                                  dev, gen_dev, gen_cpu)
        torch.cuda.synchronize(); dt.append(time.time() - t0)
        dHs.append(float(dH.mean())); accs.append(float(acc.float().mean()))
        P(f"    traj {t}: {dt[-1]:.1f}s  acc={accs[-1]:.2f}  dH={dHs[-1]:+.3f}"
          f"{'  (incl warmup)' if t == 0 else ''}")
    creutz = float(torch.exp(-torch.tensor(dHs)).mean())
    s_traj = sum(dt[1:]) / max(len(dt) - 1, 1)   # drop warmup
    P(f"\n    ⟨exp(−ΔH)⟩ = {creutz:.3f}  (want ≈1 within small-sample bias)  mean acc = {sum(accs)/len(accs):.2f}")
    P(f"    steady s/traj = {s_traj:.1f}s → 450-traj production chain ≈ {450*s_traj/3600:.1f} h "
      f"(all replicas batched in ONE process — raise --replicas to saturate the GPU)")

    P(f"\n{'='*60}")
    unbiased_ok = 0.8 < creutz < 1.25
    ok = correctness_ok and unbiased_ok
    P(f"VERDICT: {'PASS — CUDA path certified, safe to launch production' if ok else 'FAIL — do NOT run production; investigate above'}")
    if not correctness_ok:
        P("  ✗ FP64 CPU/CUDA mismatch → the operator/force differs on GPU (a real bug, not tolerance).")
    if not unbiased_ok:
        P("  ✗ Creutz off → mixed-precision chain may be biased; check FP32 MD / FP64 accept split.")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
