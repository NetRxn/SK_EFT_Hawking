#!/usr/bin/env python3
"""Brick 6 — certify the GPU (MPS/FP32) stencil RHMC against FP64.

Runs the SAME `hs_rhmc_stencil.rhmc_trajectory` in two regimes and compares:
  * FP64 on CPU  — the trusted reference (Creutz-validated, brick 5)
  * FP32 on MPS  — the GPU production path

Gates:
  1. Both chains satisfy the Creutz identity ⟨exp(−ΔH)⟩ ≈ 1 (unbiased).
  2. FP32 observables ⟨tet_m2⟩, ⟨tr_q2⟩ agree with FP64 within statistics
     (⟹ FP32 does not bias the physics — the "does precision cost quality?" gate).
  3. Sanity vs the production L=4 baseline band (g=0.5: tet_m2≈0.079, tr_q2≈0.44).
  4. Per-trajectory wall-clock MPS-vs-CPU (the real end-to-end speedup).

If gate 1/2 FAILS for FP32-only, the mixed scheme (FP32 MD + FP64 accept/reject)
is the fix — but we test FP32-only first rather than assume it's needed.

Usage:
  PYTHONPATH=. uv run python scripts/validate_rhmc_gpu.py --l 4 --g 0.5 --mass 0.1 \
      --n-therm 50 --n-meas 250 --n-md 8 --eps 0.1 --n-poles 12
"""
import argparse
import time

import numpy as np
import torch

import src.vestigial.hs_rhmc_stencil as st


def _iat_err(x):
    x = np.asarray(x, float)
    n = len(x)
    if n < 4 or x.std() == 0:
        return x.mean(), 0.0
    c = x - x.mean()
    c0 = np.dot(c, c) / n
    tau = 0.5
    for t in range(1, n // 2):
        rho = np.dot(c[:-t], c[t:]) / ((n - t) * c0)
        tau += rho
        if t > 6 * tau:
            break
    neff = n / (2 * max(tau, 0.5))
    return x.mean(), x.std(ddof=1) / np.sqrt(max(neff, 1.0))


def run_chain(mode, h0, g, msq, coeffs, L, eps, n_md, n_therm, n_meas, seed, R, device=None):
    """Batched ensemble of R replicas. mode ∈ {'fp64','fp32','mixed'}:
      fp64  — pure FP64 on CPU (reference)
      fp32  — pure FP32 on `device` (GPU)
      mixed — FP32 MD on `device` + FP64 accept/reject on CPU (production path)."""
    cpu = torch.device('cpu')
    fwd_c, back_c = st.neighbor_tables(L, cpu)
    if mode == 'fp64':
        dev, dtype, tol = cpu, torch.float64, 1e-10
    elif mode == 'fp32':
        dev, dtype, tol = device, torch.float32, 1e-5
    else:  # mixed
        dev, dtype, tol = device, torch.float32, None
        fwd_d, back_d = st.neighbor_tables(L, device)
    gen_cpu = torch.Generator().manual_seed(seed)
    try:
        gen_dev = torch.Generator(device=dev).manual_seed(seed) if dev != cpu else gen_cpu
    except Exception:
        gen_dev = None

    h = h0.to(dtype=torch.float64 if mode == 'mixed' else dtype, device=cpu if mode == 'mixed' else dev)
    tets, trqs, dHs = [], [], []
    nacc, ntot = 0, 0
    total = n_therm + n_meas
    t0 = time.time()
    for t in range(total):
        if mode == 'mixed':
            h, dH, acc = st.rhmc_trajectory_mixed(h, g, msq, coeffs, fwd_c, back_c, fwd_d, back_d,
                                                  L, eps, n_md, device, gen_dev, gen_cpu)
        else:
            h, dH, acc = st.rhmc_trajectory(h, g, msq, coeffs, fwd_c if dev == cpu else st.neighbor_tables(L, dev)[0],
                                            back_c if dev == cpu else st.neighbor_tables(L, dev)[1],
                                            L, eps, n_md, gen_dev, tol=tol, max_iter=4000)
        nacc += int(acc.sum()); ntot += acc.numel()
        if t >= n_therm:
            tet, trq, _, _ = st.measure_observables(h, L)
            tets.append(tet.cpu().numpy()); trqs.append(trq.cpu().numpy())
            dHs.append(dH.cpu().numpy())
        if (t + 1) % max(1, total // 6) == 0:
            print(f"    [{mode:5}] {t+1}/{total}  acc={nacc/ntot:.2f}  "
                  f"<dH>={float(dH.mean()):+.3f}  {(time.time()-t0)/(t+1)*1000:.0f} ms/traj", flush=True)
    dt = (time.time() - t0) / total
    return dict(tet=np.mean(tets, axis=1), trq=np.mean(trqs, axis=1),
                dH=np.concatenate(dHs), acc=nacc / ntot, s_per_traj=dt, R=R)


def summarize(name, r):
    tet, tet_e = _iat_err(r['tet'])
    trq, trq_e = _iat_err(r['trq'])
    creutz = float(np.mean(np.exp(-r['dH'])))
    print(f"  {name:10}  <tet_m2>={tet:.4f}±{tet_e:.4f}  <tr_q2>={trq:.3f}±{trq_e:.3f}  "
          f"acc={r['acc']:.2f}  <e^-dH>={creutz:.3f}  {r['s_per_traj']*1000:.0f} ms/traj")
    return tet, tet_e, trq, trq_e, creutz


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--l', type=int, default=4)
    ap.add_argument('--g', type=float, default=0.5)
    ap.add_argument('--mass', type=float, default=0.1)
    ap.add_argument('--n-therm', type=int, default=50)
    ap.add_argument('--n-meas', type=int, default=250)
    ap.add_argument('--n-md', type=int, default=20)
    ap.add_argument('--eps', type=float, default=0.03)
    ap.add_argument('--n-poles', type=int, default=14)
    ap.add_argument('--replicas', type=int, default=16, help='batched independent chains')
    ap.add_argument('--seed', type=int, default=12345)
    ap.add_argument('--fp64', action='store_true', help='also run the slow FP64/CPU reference')
    ap.add_argument('--pure-fp32', action='store_true', help='GPU path = pure FP32 (default: mixed FP32-MD/FP64-accept)')
    ap.add_argument('--smoke', action='store_true', help='quick run')
    args = ap.parse_args()
    if args.smoke:
        args.n_therm, args.n_meas = 8, 12

    L, V, R = args.l, args.l ** 4, args.replicas
    msq = args.mass ** 2
    print(f"GPU-RHMC validation: L={L} g={args.g} m={args.mass} R={R} "
          f"n_md={args.n_md} eps={args.eps} n_poles={args.n_poles} "
          f"({args.n_therm}+{args.n_meas} traj × {R} replicas)")

    # Spectral range from EQUILIBRIUM-amplitude configs (⟨h²⟩~2g per component),
    # not an inflated random config — over-wide range ruins the Zolotarev fit.
    rng = np.random.default_rng(args.seed)
    amp = np.sqrt(2.0 * args.g)                 # equilibrium amplitude
    h0 = torch.tensor(amp * rng.standard_normal((R, V, 4, 4)), dtype=torch.float64)  # warm start
    fwd, back = st.neighbor_tables(L, torch.device('cpu'))
    lam_est = max(float(st.estimate_lambda_max(
        st.hopping_blocks(torch.tensor(1.3 * amp * rng.standard_normal((V, 4, 4))), L,
                          device=torch.device('cpu'), dtype=torch.float64),
        fwd, back, V, n_iter=300, seed=s)) for s in range(3))
    lam_max = 1.25 * lam_est
    coeffs = st.make_rhmc_coeffs(lam_max, msq, args.n_poles)
    print(f"  spectral range [{msq:.4g}, {lam_max + msq:.1f}]  κ={ (lam_max+msq)/msq if msq>0 else float('inf'):.0f}\n")

    s64 = None
    if args.fp64:
        r64 = run_chain('fp64', h0, args.g, msq, coeffs, L, args.eps, args.n_md,
                        args.n_therm, args.n_meas, args.seed, R)
        s64 = summarize('fp64', r64)

    mps_ok = torch.backends.mps.is_available()
    if mps_ok:
        gpu_mode = 'mixed' if not args.pure_fp32 else 'fp32'
        r32 = run_chain(gpu_mode, h0, args.g, msq, coeffs, L, args.eps, args.n_md,
                        args.n_therm, args.n_meas, args.seed, R, device=torch.device('mps'))
        s32 = summarize(gpu_mode, r32)
    else:
        print("  (MPS unavailable — skipping FP32 path)")
        return 0

    print("\n  GATES:")
    print(f"   Creutz FP32 ⟨e^-dH⟩={s32[4]:.3f}  {'PASS' if abs(s32[4]-1)<0.05 else 'CHECK'}")
    if s64 is not None:
        dtet = abs(s64[0] - s32[0]); etet = 2 * np.hypot(s64[1], s32[1])
        dtrq = abs(s64[2] - s32[2]); etrq = 2 * np.hypot(s64[3], s32[3])
        print(f"   Creutz FP64 ⟨e^-dH⟩={s64[4]:.3f}  {'PASS' if abs(s64[4]-1)<0.05 else 'CHECK'}")
        print(f"   FP32≡FP64 tet_m2: Δ={dtet:.4f} vs 2σ={etet:.4f}  {'PASS' if dtet<etet else 'CHECK'}")
        print(f"   FP32≡FP64 tr_q2 : Δ={dtrq:.3f} vs 2σ={etrq:.3f}  {'PASS' if dtrq<etrq else 'CHECK'}")
        print(f"   speedup MPS/CPU: {r64['s_per_traj']/r32['s_per_traj']:.1f}x")
    if L == 4 and abs(args.g - 0.5) < 1e-6:
        print(f"   baseline band (massless): tet_m2≈0.079, tr_q2≈0.44 "
              f"(this run m={args.mass}, expect mild suppression)")
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
