#!/usr/bin/env python3
"""GPU production driver for the certified stencil HS+RHMC engine.

Runs the full coupling scan on the mixed-precision GPU path (FP32 MD on MPS +
FP64 accept/reject — certified unbiased in validate_rhmc_gpu.py). Each coupling
is a batched ENSEMBLE of R independent replicas (the GPU saturation + the
statistics), advanced with its own per-g Zolotarev coefficients (spectral range
from that coupling's equilibrium amplitude).

Output npz per coupling is compatible with scripts/rhmc_monitor.py (live
early-stop) and scripts/analyze_rhmc_vestigial.py, plus per-trajectory m_h/Q
instrumentation for the noise-immune Binder/shuffle detectors. Atomic save +
resume (reseeds RNG — a statistically valid continuation).

Usage:
  PYTHONPATH=. uv run python scripts/run_rhmc_gpu_production.py \
      --l 8 --mass 0.1 --replicas 16 --n-therm 100 --n-meas 400 --n-md 16 --eps 0.03
  # monitor in another terminal:
  PYTHONPATH=. uv run python scripts/rhmc_monitor.py data/rhmc/L8gpu_m0.1 --watch 300
"""
import argparse
import os
import time

import numpy as np
import torch

import src.vestigial.hs_rhmc_stencil as st


def coupling_grid(n, g_lo, g_hi):
    return np.linspace(g_lo, g_hi, n)


def build_coeffs(L, g, msq, n_poles, seed):
    """Per-coupling coeffs: spectral range from g's EQUILIBRIUM amplitude (√2g)."""
    V = L ** 4
    rng = np.random.default_rng(seed)
    cpu = torch.device('cpu')
    fwd, back = st.neighbor_tables(L, cpu)
    amp = 1.3 * np.sqrt(2.0 * g)                # bound the equilibrium amplitude
    lam = max(float(st.estimate_lambda_max(
        st.hopping_blocks(torch.tensor(amp * rng.standard_normal((V, 4, 4))), L,
                          device=cpu, dtype=torch.float64), fwd, back, V, n_iter=250, seed=s))
        for s in range(3))
    return st.make_rhmc_coeffs(1.25 * lam, msq, n_poles), 1.25 * lam


def atomic_savez(path, **data):
    base = path[:-4] if path.endswith('.npz') else path
    tmp = base + '.tmp'                      # np.savez appends '.npz' → base+'.tmp.npz'
    np.savez(tmp, **data)
    os.replace(tmp + '.npz', path)


def run_coupling(path, g, L, msq, coeffs, R, eps, n_md, n_meas, n_therm, device, seed,
                 solver='refined', engine='full', chrono=False):
    """Run/extend one coupling's batched-replica mixed chain; save npz. Returns summary.

    engine='full': the rational (power −1/2) full-operator RHMC. solver='refined' offloads
    the FP64-exact accept/reject to FP32-inner refinement on `device` (≈the dominant cost on
    a device that can't run FP64, e.g. MPS); 'mixed' keeps it as a pure-FP64 CPU solve.
    engine='eo': the even-odd-reduced RHMC — a SINGLE (M_e+m²)⁻¹ solve replaces the 12-pole
    multishift in both the MD force and the accept/reject (same target density, proven
    identical: det(A†A+m²)^{1/4}=det(M_e+m²)^{1/2}); ~1–2 orders of magnitude cheaper at L=8.
    All paths are FP64-exact Metropolis."""
    V = L ** 4
    cpu = torch.device('cpu')
    fwd_c, back_c = st.neighbor_tables(L, cpu)
    fwd_d, back_d = st.neighbor_tables(L, device)
    if engine == 'eo':
        eo_c, eo_d = st.eo_tables(L, cpu), st.eo_tables(L, device)
        if device.type == 'cpu':
            # CPU: pure-FP64 eo (FP32 gives NO CPU speedup + cast overhead). Loose MD tol,
            # tight accept — exact Metropolis. This is the practical fast path (MPS/CUDA are
            # launch-bound for this Python-loop CG until it's restructured).
            def trajectory(h, g, msq, coeffs, fc, bc, fd, bd, L, eps, n_md, device, gen_dev, gen_cpu):
                return st.eo_rhmc_trajectory(h, g, msq, coeffs, eo_c, fc, bc, L, eps, n_md,
                                             gen_cpu, tol=1e-8, tol_md=1e-4, chrono=chrono)
        else:
            # GPU (MPS/CUDA): FP32 MD on device + FP64 accept/reject on CPU.
            def trajectory(h, g, msq, coeffs, fc, bc, fd, bd, L, eps, n_md, device, gen_dev, gen_cpu):
                return st.eo_rhmc_trajectory_mixed(h, g, msq, coeffs, eo_c, fc, bc, eo_d, fd, bd,
                                                   L, eps, n_md, device, gen_dev, gen_cpu, chrono=chrono)
    else:
        trajectory = st.rhmc_trajectory_refined if solver == 'refined' else st.rhmc_trajectory_mixed

    # resume
    hist = {k: [] for k in ('h_sq', 'dH', 'tet', 'trq')}
    mh_hist, Q_hist = [], []
    n_done = 0
    if os.path.exists(path):
        d = np.load(path)
        for k, kk in (('h_sq_history', 'h_sq'), ('delta_h_history', 'dH'),
                      ('tet_m2_history', 'tet'), ('tr_q2_history', 'trq')):
            hist[kk] = list(np.asarray(d[k]))
        mh_hist = list(np.asarray(d['m_h_history'])) if 'm_h_history' in d else []
        Q_hist = list(np.asarray(d['Q_history'])) if 'Q_history' in d else []
        n_done = len(hist['tet'])
        h = torch.tensor(np.asarray(d['h_state']), dtype=torch.float64) if 'h_state' in d \
            else torch.tensor(np.sqrt(2 * g) * np.random.default_rng(seed).standard_normal((R, V, 4, 4)))
        therm_left = 0
    else:
        h = torch.tensor(np.sqrt(2 * g) * np.random.default_rng(seed).standard_normal((R, V, 4, 4)))
        therm_left = n_therm

    gen_cpu = torch.Generator().manual_seed(seed + n_done)
    try:
        gen_dev = torch.Generator(device=device).manual_seed(seed + n_done) if device.type != 'cpu' else gen_cpu
    except Exception:
        gen_dev = None

    nacc, ntot = 0, 0
    target = n_meas - n_done
    t0 = time.time()
    for t in range(therm_left + max(target, 0)):
        h, dH, acc = trajectory(h, g, msq, coeffs, fwd_c, back_c, fwd_d, back_d,
                                L, eps, n_md, device, gen_dev, gen_cpu)
        nacc += int(acc.sum()); ntot += acc.numel()
        if t >= therm_left:
            h_sq = float((h * h).mean())
            tet, trq, m_h, Q = st.measure_observables(h, L)        # (R,), (R,), (R,4,4), (R,4,4)
            hist['h_sq'].append(h_sq); hist['dH'].append(float(dH.mean()))
            hist['tet'].append(float(tet.mean())); hist['trq'].append(float(trq.mean()))
            mh_hist.append(m_h.cpu().numpy()); Q_hist.append(Q.cpu().numpy())
            if len(hist['tet']) % 20 == 0:
                atomic_savez(path,
                             h_sq_history=np.array(hist['h_sq']), delta_h_history=np.array(hist['dH']),
                             tet_m2_history=np.array(hist['tet']), tr_q2_history=np.array(hist['trq']),
                             m_h_history=np.array(mh_hist), Q_history=np.array(Q_hist),
                             h_final=h[0].cpu().numpy(), h_state=h.cpu().numpy(),
                             acceptance_rate=np.float64(nacc / max(ntot, 1)),
                             g=np.float64(g), L=np.int64(L), mass=np.float64(np.sqrt(msq)),
                             replicas=np.int64(R))
                print(f"    g={g:.3f}: {len(hist['tet'])}/{n_meas}  acc={nacc/ntot:.2f}  "
                      f"<tet>={np.mean(hist['tet'][-20:]):.4f}  {(time.time()-t0)/(t+1)*1000:.0f} ms/traj",
                      flush=True)
    atomic_savez(path,
                 h_sq_history=np.array(hist['h_sq']), delta_h_history=np.array(hist['dH']),
                 tet_m2_history=np.array(hist['tet']), tr_q2_history=np.array(hist['trq']),
                 m_h_history=np.array(mh_hist), Q_history=np.array(Q_hist),
                 h_final=h[0].cpu().numpy(), h_state=h.cpu().numpy(),
                 acceptance_rate=np.float64(nacc / max(ntot, 1)),
                 g=np.float64(g), L=np.int64(L), mass=np.float64(np.sqrt(msq)), replicas=np.int64(R))
    return dict(g=g, acc=nacc / max(ntot, 1), tet=np.mean(hist['tet']) if hist['tet'] else float('nan'),
                n=len(hist['tet']), s_per_traj=(time.time() - t0) / max(therm_left + max(target, 0), 1))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--l', type=int, default=8)
    ap.add_argument('--mass', type=float, required=True)
    ap.add_argument('--n-couplings', type=int, default=14)
    ap.add_argument('--g-lo', type=float, default=0.5)
    ap.add_argument('--g-hi', type=float, default=8.0)
    ap.add_argument('--replicas', type=int, default=16)
    ap.add_argument('--n-therm', type=int, default=100)
    ap.add_argument('--n-meas', type=int, default=400)
    ap.add_argument('--n-md', type=int, default=16)
    ap.add_argument('--eps', type=float, default=0.03)
    ap.add_argument('--n-poles', type=int, default=14)
    ap.add_argument('--seed', type=int, default=2026)
    ap.add_argument('--outdir', type=str, default=None)
    ap.add_argument('--device', type=str, default='mps', choices=['mps', 'cpu'])
    ap.add_argument('--engine', type=str, default='full', choices=['full', 'eo'],
                    help="'eo' = even-odd-reduced (single-solve; ~1-2 orders faster at L=8, "
                         "proven identical target density); 'full' = 12-pole rational (default).")
    ap.add_argument('--solver', type=str, default='refined', choices=['refined', 'mixed'],
                    help='refined = FP32-inner/FP64-residual accept/reject on device (fast); '
                         'mixed = pure-FP64 CPU accept/reject (slower fallback). Both FP64-exact.')
    ap.add_argument('--couplings-only', type=float, nargs='*', help='run only these g values')
    ap.add_argument('--no-compile', dest='compile', action='store_false',
                    help='disable torch.compile of the stencil matvecs (default: enabled, EXACT '
                         '~1.6x/traj on CPU, CUDA-graphs on CUDA).')
    ap.add_argument('--chrono', action='store_true',
                    help='chronological inversion (CG warm-start, ~1.8x MD; controlled O(tol) '
                         'reversibility — certified unbiased by Creutz; default off = exactly reversible).')
    ap.set_defaults(compile=True)
    args = ap.parse_args()

    L, msq = args.l, args.mass ** 2
    device = torch.device(args.device if (args.device != 'mps' or torch.backends.mps.is_available()) else 'cpu')
    if args.compile:
        st.enable_matvec_compile(mode='reduce-overhead' if device.type == 'cuda' else 'default')
    tag = 'eo' if args.engine == 'eo' else 'gpu'
    outdir = args.outdir or f"data/rhmc/L{L}{tag}_m{args.mass:g}"
    os.makedirs(outdir, exist_ok=True)
    gs = args.couplings_only if args.couplings_only else coupling_grid(args.n_couplings, args.g_lo, args.g_hi)

    print(f"GPU production: L={L} m={args.mass} engine={args.engine} device={device.type} solver={args.solver} "
          f"R={args.replicas} n_md={args.n_md} eps={args.eps} n_poles={args.n_poles}  "
          f"{len(gs)} couplings × {args.n_meas} traj × {args.replicas} replicas → {outdir}", flush=True)
    for i, g in enumerate(gs):
        g = float(g)
        path = os.path.join(outdir, f"g{g:.4f}.npz")
        coeffs, lam = build_coeffs(L, g, msq, args.n_poles, args.seed + i)
        print(f"\n[{i+1}/{len(gs)}] g={g:.3f}  range[{msq:.4g},{lam+msq:.1f}] κ={(lam+msq)/msq:.0f}", flush=True)
        s = run_coupling(path, g, L, msq, coeffs, args.replicas, args.eps, args.n_md,
                         args.n_meas, args.n_therm, device, args.seed + i,
                         solver=args.solver, engine=args.engine, chrono=args.chrono)
        print(f"  → done g={g:.3f}: acc={s['acc']:.2f} <tet>={s['tet']:.4f} "
              f"n={s['n']} {s['s_per_traj']*1000:.0f} ms/traj", flush=True)
    print(f"\nComplete → {outdir}  (monitor: rhmc_monitor.py {outdir} --watch 300)", flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
