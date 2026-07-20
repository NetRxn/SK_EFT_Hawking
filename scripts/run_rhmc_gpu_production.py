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

Backends: --backend torch (default; Rust/torch stencil engine) or --backend mlx
(the MLX engine, Metal on macOS / CUDA via mlx[cuda] on Linux). The mlx backend
defaults to --mlx-solver refined (FP32 GPU inner + FP64 CPU residual → FP64-exact
Metropolis at GPU speed; ~20x the naive MLX path at L=8). It is a SINGLE
GPU-bound process (~0.3 CPU cores) — tolerant of CPU-heavy work alongside, but
keep the GPU free of other heavy Metal/CUDA jobs. Long runs: launch under
`caffeinate -is`, lid open, on AC (macOS sleep silently suspends them).

  >>> Operator guide (resource profile, the m->0 targeting plan tying back to the
  >>> prior L=8 m=0.1 null, and copy-paste recipes): docs/RHMC_MLX_RUNBOOK.md

Usage:
  # torch (default):
  PYTHONPATH=. uv run python scripts/run_rhmc_gpu_production.py \
      --l 8 --mass 0.1 --replicas 16 --n-therm 100 --n-meas 400 --n-md 16 --eps 0.03
  # mlx (Metal/CUDA), refined solver is the default:
  caffeinate -is env PYTHONPATH=. uv run python scripts/run_rhmc_gpu_production.py \
      --backend mlx --l 8 --mass 0.05 --replicas 16 --couplings-only 3.0 4.0 5.0 6.0 8.0
  # monitor in another terminal:
  PYTHONPATH=. uv run python scripts/rhmc_monitor.py data/rhmc/L8mlx_m0.05 --watch 300
"""
import argparse
import os
import sys
import time

import numpy as np

try:                                    # absent on an MLX-only box (Linux + mlx[cuda])
    import torch
    import src.vestigial.hs_rhmc_stencil as st
except ImportError:
    torch = None
    st = None


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


class _Tee:
    """Duplicate a stream's writes into a log file; everything else delegates."""
    def __init__(self, stream, log):
        self._stream, self._log = stream, log

    def write(self, s):
        self._stream.write(s)
        self._log.write(s)

    def flush(self):
        self._stream.flush()
        self._log.flush()

    def __getattr__(self, name):
        return getattr(self._stream, name)


def setup_run_log(outdir):
    """Tee stdout+stderr into <outdir>/run.log so a detached run (stdout at /dev/null)
    keeps an on-disk record. Append mode: a checkpoint-resumed run continues the same
    log. Console output is unchanged; stderr is included so a crash traceback survives."""
    log = open(os.path.join(outdir, 'run.log'), 'a', buffering=1, encoding='utf-8')
    log.write(f"--- run.log opened {time.strftime('%Y-%m-%d %H:%M:%S %z')}  "
              f"argv: {' '.join(sys.argv)} ---\n")
    sys.stdout = _Tee(sys.stdout, log)
    sys.stderr = _Tee(sys.stderr, log)
    return log


def atomic_savez(path, **data):
    base = path[:-4] if path.endswith('.npz') else path
    tmp = base + '.tmp'                      # np.savez appends '.npz' → base+'.tmp.npz'
    np.savez(tmp, **data)
    os.replace(tmp + '.npz', path)


def _fresh_config(seed, g, shape):
    """Initial h configuration: √(2g)·N(0,1) from a per-coupling seed."""
    return np.sqrt(2 * g) * np.random.default_rng(seed).standard_normal(shape)


def _trajectory_rng(seed, n_done):
    """RNG for a chain's trajectory noise (heatbath ξ, momenta π, Metropolis u).

    Uses a distinct SeedSequence child (spawn_key=(1, n_done)) so the stream is
    DECORRELATED from the initial-config RNG (`default_rng(seed)` in `_fresh_config`,
    spawn_key=()) — otherwise a fresh run (n_done=0) would reuse the exact normals that
    built the starting config, correlating the first trajectory's noise with it (review
    finding 2). n_done parameterizes the stream so a resumed chunk is an independent,
    valid continuation. (A plain `[seed, n_done]` seed does NOT work: numpy folds a
    trailing zero, so [seed, 0] collides with `seed`.)"""
    return np.random.default_rng(np.random.SeedSequence(seed, spawn_key=(1, n_done)))


def build_coeffs_mlx(L, g, msq, n_poles, seed, hb_relerr_tol=1e-3, n_poles_cap=80):
    """`build_coeffs` on the MLX engine (torch-free): spectral range from g's
    equilibrium amplitude (√2g), WITH a heatbath-quality pre-flight gate.

    λmax is estimated by power iteration in FP32 on the default device (Metal/CUDA) —
    ~20× the f64-CPU path, and re-run every resume, so it must be cheap. FP32 is safe:
    the estimate is only an under-approximation from below that the 1.25× padding
    absorbs; the 3-seed max guards against a start vector missing the top eigenvalue
    (an under-estimate would shrink the Zolotarev range → reject-all).

    GATE (m→0 correctness): the eo heatbath's Zolotarev r_{-1/2} fit degrades as m→0
    (κ=λmax/m²), and a poor fit makes the heatbath sample a biased fermion weight the
    Metropolis test CANNOT correct (uncorrectable heatbath bias). So `n_poles` is a FLOOR:
    it is auto-bumped (step 4) until the UNSIGNED max relative error of r_{-1/2} over
    [m², λmax+m²] is ≤ `hb_relerr_tol`, and raises (fail-closed) if `n_poles_cap` cannot
    meet it. Gate on the unsigned max relerr, NOT the S_PF=½‖ξ‖² consistency ratio — the
    latter is a signed spectral average that hides the error via equioscillation
    cancellation (measured 0.955 where the true max error is 15% at m=0.05, np=14). Extra
    poles cost only the once-per-trajectory heatbath: the action + MD force are single-pole
    exact and do not use the rational set."""
    import mlx.core as mx
    import src.vestigial.hs_rhmc_mlx as me
    V = L ** 4
    rng = np.random.default_rng(seed)
    fwd, back = me.neighbor_tables(L)
    amp = 1.3 * np.sqrt(2.0 * g)
    lam = 1.25 * max(float(me.estimate_lambda_max(
        me.hopping_blocks(mx.array(amp * rng.standard_normal((V, 4, 4)), dtype=mx.float32), L),
        fwd, back, V, n_iter=150, seed=s)) for s in range(3))
    lo, hi = (msq if msq > 0 else max(lam * 1e-7, 1e-12)), lam + msq
    npu = n_poles
    while True:
        # np.errstate: the Remez solve in compute_zolotarev_coefficients can transiently
        # overflow exp() at wide spectral ranges (κ~1e6); the returned coeffs are finite
        # (verified) and a genuinely non-finite coeff fails the relerr gate below anyway.
        with np.errstate(over='ignore', invalid='ignore'):
            coeffs = me.make_rhmc_coeffs(lam, msq, npu)
        relerr = me.zolotarev_max_relerr(coeffs['a0'], coeffs['alphas'], coeffs['betas'],
                                         lo, hi, power=-0.5)
        if relerr <= hb_relerr_tol:
            if npu > n_poles:
                print(f"    build_coeffs: heatbath n_poles {n_poles}→{npu} "
                      f"(Zolotarev relerr {relerr:.1e} ≤ {hb_relerr_tol:.0e}; κ={hi/lo:.1e})",
                      flush=True)
            return coeffs, lam
        if npu >= n_poles_cap:
            raise ValueError(
                f"heatbath Zolotarev relerr={relerr:.2e} > tol={hb_relerr_tol:.0e} even at "
                f"n_poles={npu} (cap; κ={hi/lo:.1e}, m={msq ** 0.5:.3g}) — the heatbath would "
                f"sample a biased fermion weight (uncorrectable by Metropolis). Raise the mass "
                f"or n_poles_cap.")
        npu = min(npu + 4, n_poles_cap)


def build_hasenbusch_coeffs_mlx(L, g, msq, n_poles, seed, musq=None,
                                hb_relerr_tol=1e-3, n_poles_cap=80):
    """Coefficient bundle for the Hasenbusch(K=1) trajectory (mlx backend).

    HEAVY PF at μ² reuses the existing r_{-1/2} machinery (make_rhmc_coeffs with
    μ² in place of m² — κ=λmax/μ² is small, few poles); the RATIO PF uses the
    Möbius-transformed Zolotarev of ((x+m²)/(x+μ²))^{1/2} (make_eo_ratio_sqrt_coeffs).
    BOTH rationals are quality-gated on their UNSIGNED max relerr with the same
    auto-bump / fail-closed contract as build_coeffs_mlx (heatbath bias is
    uncorrectable by Metropolis regardless of which PF mis-samples).

    musq=None picks the balanced split μ² = √(m²·λmax) — both factors then carry
    κ ≈ √(λmax/m²). Returns (hb_coeffs, ratio_coeffs, musq, lam)."""
    import mlx.core as mx
    import src.vestigial.hs_rhmc_mlx as me
    V = L ** 4
    rng = np.random.default_rng(seed)
    fwd, back = me.neighbor_tables(L)
    amp = 1.3 * np.sqrt(2.0 * g)
    lam = 1.25 * max(float(me.estimate_lambda_max(
        me.hopping_blocks(mx.array(amp * rng.standard_normal((V, 4, 4)), dtype=mx.float32), L),
        fwd, back, V, n_iter=150, seed=s)) for s in range(3))
    if musq is None:
        musq = float(np.sqrt(max(msq, 1e-12) * lam))

    npu = n_poles                                  # heavy PF gate (existing machinery @ μ²)
    while True:
        with np.errstate(over='ignore', invalid='ignore'):
            hb = me.make_rhmc_coeffs(lam, musq, npu)
        relerr = me.zolotarev_max_relerr(hb['a0'], hb['alphas'], hb['betas'],
                                         musq, lam + musq, power=-0.5)
        if relerr <= hb_relerr_tol:
            break
        if npu >= n_poles_cap:
            raise ValueError(f"heavy-PF Zolotarev relerr={relerr:.2e} > {hb_relerr_tol:.0e} "
                             f"at n_poles={npu} (cap) — biased heatbath, fail-closed.")
        npu = min(npu + 4, n_poles_cap)

    npr = n_poles                                  # ratio PF gate (κ_t = μ²/m²)
    while True:
        with np.errstate(over='ignore', invalid='ignore'):
            rc = me.make_eo_ratio_sqrt_coeffs(msq, musq, lam, npr)
        relerr_r = me.eo_ratio_sqrt_max_relerr(rc, lam)
        if relerr_r <= hb_relerr_tol:
            break
        if npr >= n_poles_cap:
            raise ValueError(f"ratio-PF rational relerr={relerr_r:.2e} > {hb_relerr_tol:.0e} "
                             f"at n_poles={npr} (cap) — biased heatbath, fail-closed.")
        npr = min(npr + 4, n_poles_cap)

    print(f"    build_hasenbusch: μ²={musq:.3g} (κ_H={lam/musq + 1:.0f}, κ_R={musq/msq:.0f})  "
          f"heavy poles {npu} (relerr {relerr:.1e})  ratio poles {npr} (relerr {relerr_r:.1e})",
          flush=True)
    return hb, rc, musq, lam


def _load_checkpoint(path, seed, g, shape, n_therm):
    """Resume state from an existing npz, or a fresh-run state.

    Returns a dict with: h_np (config), hist (per-observable history lists), mh/Q lists,
    n_done (measured trajectories), n_therm_done (thermalization trajectories completed),
    therm_left, and cumulative accept counters nacc/ntot. Backward compatible: an old
    checkpoint without `n_therm_done` is treated as fully thermalized (it was a
    measurement run, so we must NOT re-thermalize it); without nacc/ntot the cumulative
    counters start at 0."""
    hist = {k: [] for k in ('h_sq', 'dH', 'tet', 'trq')}
    if not os.path.exists(path):
        return dict(h_np=_fresh_config(seed, g, shape), hist=hist, mh=[], Q=[],
                    n_done=0, n_therm_done=0, therm_left=n_therm, nacc=0, ntot=0)
    d = np.load(path)
    for k, kk in (('h_sq_history', 'h_sq'), ('delta_h_history', 'dH'),
                  ('tet_m2_history', 'tet'), ('tr_q2_history', 'trq')):
        hist[kk] = list(np.asarray(d[k]))
    mh = list(np.asarray(d['m_h_history'])) if 'm_h_history' in d else []
    Q = list(np.asarray(d['Q_history'])) if 'Q_history' in d else []
    n_done = len(hist['tet'])
    n_therm_done = int(d['n_therm_done']) if 'n_therm_done' in d else n_therm   # old npz: assume done
    nacc = int(d['nacc']) if 'nacc' in d else 0
    ntot = int(d['ntot']) if 'ntot' in d else 0
    h_np = np.asarray(d['h_state']) if 'h_state' in d else _fresh_config(seed, g, shape)
    return dict(h_np=h_np, hist=hist, mh=mh, Q=Q, n_done=n_done, n_therm_done=n_therm_done,
                therm_left=max(n_therm - n_therm_done, 0), nacc=nacc, ntot=ntot)


def run_coupling_mlx(path, g, L, msq, coeffs, R, eps, n_md, n_meas, n_therm, seed,
                     chrono=False, mlx_solver='refined', checkpoint_every=10,
                     hasenbusch=None):
    """MLX twin of `run_coupling`, eo path (FP32 MD on the MLX default device — Metal or
    CUDA). Identical npz schema (+ n_therm_done/nacc/ntot for resume) → rhmc_monitor.py /
    analyze_rhmc_vestigial.py compatible. Same target density as the torch engines;
    FP64-exact Metropolis.

    mlx_solver='refined' (default): heatbath + accept/reject FP64 solves offloaded to the
    device via FP32-inner refinement — the fast path. 'mixed': FP64 accept/reject on the
    CPU stream (portable fallback; slow where the MLX CPU backend is weak).

    Checkpoints every `checkpoint_every` trajectories through BOTH thermalization and
    measurement, so a stop/restart resumes the remaining thermalization (not restart it)
    and loses at most `checkpoint_every` trajectories of work."""
    import mlx.core as mx
    import src.vestigial.hs_rhmc_mlx as me
    V = L ** 4
    fwd, back = me.neighbor_tables(L)
    eo = me.eo_tables(L)
    device = mx.default_device()

    st = _load_checkpoint(path, seed, g, (R, V, 4, 4), n_therm)
    hist, mh_hist, Q_hist = st['hist'], st['mh'], st['Q']
    n_done, n_therm_done, therm_left = st['n_done'], st['n_therm_done'], st['therm_left']
    nacc, ntot = st['nacc'], st['ntot']
    h = mx.array(st['h_np'], dtype=mx.float64)
    rng = _trajectory_rng(seed, n_done + n_therm_done)   # decorrelated; independent per resume point

    # provenance: record the sampler variant (identical target density either way, but
    # the npz should say how it was produced)
    extra = {} if hasenbusch is None else dict(hb_mu_sq=np.float64(hasenbusch['musq']),
                                               hb_n_inner=np.int64(hasenbusch['n_inner']))

    def save():
        h_state = np.array(h)                       # eval only — no new f64 op on the GPU stream
        atomic_savez(path,
                     h_sq_history=np.array(hist['h_sq']), delta_h_history=np.array(hist['dH']),
                     tet_m2_history=np.array(hist['tet']), tr_q2_history=np.array(hist['trq']),
                     m_h_history=np.array(mh_hist), Q_history=np.array(Q_hist),
                     h_final=h_state[0], h_state=h_state,
                     acceptance_rate=np.float64(nacc / max(ntot, 1)),
                     nacc=np.int64(nacc), ntot=np.int64(ntot), n_therm_done=np.int64(n_therm_done),
                     g=np.float64(g), L=np.int64(L), mass=np.float64(np.sqrt(msq)),
                     replicas=np.int64(R), **extra)

    def trajectory():
        if hasenbusch is not None:
            # Hasenbusch(K=1): coeffs is the heavy-PF bundle; `hasenbusch` carries the
            # ratio coeffs + split mass + fine-step count. n_md = coarse (outer) steps.
            return me.eo_rhmc_trajectory_hasenbusch_refined(
                h, g, msq, hasenbusch['musq'], coeffs, hasenbusch['ratio_coeffs'],
                eo, fwd, back, L, eps, n_md, hasenbusch['n_inner'], rng, device,
                tol_md=1e-4, inner_tol=3e-4, max_outer=20, chrono=chrono)
        if mlx_solver == 'refined':
            return me.eo_rhmc_trajectory_refined(h, g, msq, coeffs, eo, fwd, back, L,
                                                 eps, n_md, rng, device, tol_md=1e-4,
                                                 inner_tol=3e-4, max_outer=20, chrono=chrono)
        return me.eo_rhmc_trajectory_mixed(h, g, msq, coeffs, eo, fwd, back, L,
                                           eps, n_md, rng, tol_md=1e-4, tol_acc=1e-10, chrono=chrono)

    ran = 0
    t0 = time.time()
    # --- thermalization (checkpointed so a stop mid-therm resumes, not restarts) ---
    for _ in range(therm_left):
        h, dH, acc = trajectory()
        acc_np = np.array(acc); nacc += int(acc_np.sum()); ntot += acc_np.size
        n_therm_done += 1; ran += 1
        if n_therm_done % checkpoint_every == 0:
            save()
            print(f"    g={g:.3f}: therm {n_therm_done}/{n_therm}  acc={nacc/max(ntot,1):.2f}  "
                  f"{(time.time()-t0)/ran*1000:.0f} ms/traj", flush=True)

    # --- measurement ---
    target = max(n_meas - n_done, 0)
    for _ in range(target):
        h, dH, acc = trajectory()
        acc_np = np.array(acc); nacc += int(acc_np.sum()); ntot += acc_np.size; ran += 1
        with mx.stream(mx.cpu):                      # f64 arithmetic stays off the GPU stream
            h_sq = float(mx.mean(h * h))
        tet, trq, m_h, Q = me.measure_observables(h, L)
        hist['h_sq'].append(h_sq); hist['dH'].append(float(np.array(dH).mean()))
        hist['tet'].append(float(np.array(tet).mean())); hist['trq'].append(float(np.array(trq).mean()))
        mh_hist.append(np.array(m_h)); Q_hist.append(np.array(Q))
        if len(hist['tet']) % checkpoint_every == 0:
            save()
            print(f"    g={g:.3f}: {len(hist['tet'])}/{n_meas}  acc={nacc/max(ntot,1):.2f}  "
                  f"<tet>={np.mean(hist['tet'][-checkpoint_every:]):.4f}  "
                  f"{(time.time()-t0)/ran*1000:.0f} ms/traj", flush=True)

    if ran > 0:                                      # no-op resume must NOT clobber acceptance_rate
        save()
    return dict(g=g, acc=nacc / max(ntot, 1), tet=np.mean(hist['tet']) if hist['tet'] else float('nan'),
                n=len(hist['tet']), s_per_traj=(time.time() - t0) / ran if ran else float('nan'))


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


def chrono_for_kappa(user_chrono, kappa, kappa_max, hasenbusch=False):
    """Resolve whether to use chronological inversion for a coupling of condition number
    κ=(λmax+m²)/m². Chrono warm-starting speeds the MD force solves (~1.4× on MD) but SOFTENS
    reversibility. Measured (L=8, 2026-07-16): across the whole stiff m=0.05 range the roundtrip
    |Δh| is ~2.6–4.0e-4 chrono-on vs ~3–5e-5 chrono-off — chrono-on is above the ~1e-4 clean-HMC
    reversibility bar at EVERY m=0.05 coupling. The tax is set by the stiffness regime (small m ⇒
    large κ), roughly flat across couplings within a mass, so κ acts as a stiffness proxy: above
    `kappa_max` chrono is auto-disabled to run at the clean fp32-reversibility floor; below (milder
    masses) the ~1.4× MD win is kept. An explicit --no-chrono always wins; `kappa_max<=0` disables
    the gate (honor user_chrono as-is).

    `hasenbusch=True` forces chrono OFF unconditionally: the Hasenbusch trajectory with chrono
    warm-starting is UNVALIDATED (⟨e^-ΔH⟩ certified only chrono-off), so we never default into it.
    Its 2-level force is already exact + well-mixing chrono-off, so there is nothing to reclaim."""
    if not user_chrono:
        return False
    if hasenbusch:
        return False
    if kappa_max and kappa_max > 0 and kappa > kappa_max:
        return False
    return True


def resolve_working_point(hasenbusch, n_md, eps):
    """Pick the MD working point (n_md, eps) for the selected engine when the user did not
    override it. Hasenbusch's mass-preconditioned 2-level force tolerates FEWER, BIGGER coarse
    steps than single-PF: measured at the stiffest planned mass (L=8 m=0.05 g=8) the tuned
    point is (n_outer=16, eps=0.031, τ_traj≈0.5) at acc 0.97 / ⟨e^-ΔH⟩ 0.997 — 1.6× faster
    than the single-PF (33, 0.015) and safe for milder masses (less stiff ⇒ higher acc). Any
    explicit --n-md / --eps wins; for m<0.05 or new corners still scan (eps shrinks as m→0)."""
    if hasenbusch:
        n_md = 16 if n_md is None else n_md
        eps = 0.031 if eps is None else eps
    else:
        n_md = 33 if n_md is None else n_md
        eps = 0.015 if eps is None else eps
    return n_md, eps


def build_parser():
    ap = argparse.ArgumentParser()
    ap.add_argument('--l', type=int, default=8)
    ap.add_argument('--mass', type=float, required=True)
    ap.add_argument('--n-couplings', type=int, default=14)
    ap.add_argument('--g-lo', type=float, default=0.5)
    ap.add_argument('--g-hi', type=float, default=8.0)
    ap.add_argument('--replicas', type=int, default=16)
    ap.add_argument('--n-therm', type=int, default=100)
    ap.add_argument('--n-meas', type=int, default=400)
    ap.add_argument('--n-md', type=int, default=None,
                    help='MD steps per trajectory (τ=eps·n_md≈0.5). Default is ENGINE-resolved '
                         '(resolve_working_point): single-PF → 33, Hasenbusch → 16 (its 2-level '
                         'force tolerates fewer/bigger coarse steps). Both are the stiffest-mass '
                         '(m=0.05) working point; milder masses tolerate them. Override to tune.')
    ap.add_argument('--eps', type=float, default=None,
                    help='MD step size. The eo single-pole fermion force is STIFF and stiffness '
                         'grows as m→0, so eps must SHRINK with the mass: eps=0.03 reject-alls at '
                         'm=0.05 single-PF (measured). Default is ENGINE-resolved: single-PF → '
                         '0.015, Hasenbusch → 0.031 (both acc≈1.0/0.97 at the stiffest corner '
                         'm=0.05, g=8). For m<0.05 or new corners, scan first. Watch rhmc_monitor.py.')
    ap.add_argument('--n-poles', type=int, default=24,
                    help='Zolotarev pole count FLOOR for the heatbath rational (mlx backend). '
                         'Auto-bumped by build_coeffs_mlx until the heatbath fit meets '
                         '--hb-relerr-tol (κ=λmax/m² grows as m→0, so the fit needs more poles '
                         'there). The action + MD force are single-pole exact, so poles cost only '
                         'the once-per-trajectory heatbath.')
    ap.add_argument('--hb-relerr-tol', type=float, default=1e-3,
                    help='mlx backend: max relative error the heatbath Zolotarev r_{-1/2} fit must '
                         'reach over [m²,λmax+m²] (auto-bumping n_poles). Below the signal/floor '
                         'scale so the uncorrectable heatbath sampling bias stays negligible. '
                         'Gated on the UNSIGNED max error, not the S_PF=½‖ξ‖² consistency ratio '
                         '(a signed average that hides the error via equioscillation cancellation).')
    ap.add_argument('--n-poles-cap', type=int, default=80,
                    help='mlx backend: hard cap for the heatbath n_poles auto-bump; build_coeffs '
                         'RAISES (fail-closed) if the cap cannot meet --hb-relerr-tol rather than '
                         'run an under-resolved (biased) heatbath.')
    ap.add_argument('--checkpoint-every', type=int, default=10,
                    help='save an atomic checkpoint every N trajectories (through both '
                         'thermalization and measurement) — mlx backend. A stop/restart '
                         'loses at most this many trajectories; smaller = safer, more I/O.')
    ap.add_argument('--seed', type=int, default=2026)
    ap.add_argument('--outdir', type=str, default=None)
    ap.add_argument('--device', type=str, default='mps', choices=['mps', 'cpu'])
    ap.add_argument('--backend', type=str, default='torch', choices=['torch', 'mlx'],
                    help="mlx = the torch-free MLX engine (hs_rhmc_mlx): eo path, FP32 MD on the "
                         "MLX default device (Metal on macOS, CUDA via mlx[cuda] on Linux). "
                         "--device/--engine/--no-compile are torch-only and ignored with mlx.")
    ap.add_argument('--mlx-solver', type=str, default='refined', choices=['refined', 'mixed'],
                    help="mlx backend only. refined (default) = FP64 heatbath + accept/reject "
                         "offloaded to the device via FP32-inner refinement (fast; the FP64-CPU "
                         "stages are ~97%% of the trajectory on the MLX CPU backend). mixed = "
                         "FP64 accept/reject on the CPU stream (portable fallback).")
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
    ap.add_argument('--hasenbusch', action=argparse.BooleanOptionalAction, default=False,
                    help='mlx backend: Hasenbusch(K=1) mass-preconditioned trajectory — exact '
                         'det split det(M+m²)^½ = det(M+μ²)^½·det[(M+m²)/(M+μ²)]^½ with a '
                         '2-level nested Omelyan (hard (M+m²)⁻¹ force on the coarse level, '
                         '~2·n_md evals/traj instead of ~3·n_md·n_inner). With it, --eps is '
                         'the COARSE step and --n-md the coarse step count (τ=eps·n_md); pair '
                         'with --hb-n-inner. Both PF rationals are quality-gated (auto-bump).')
    ap.add_argument('--mu-sq', type=float, default=None,
                    help='Hasenbusch split mass μ² (default: balanced √(m²·λmax) per coupling).')
    ap.add_argument('--hb-n-inner', type=int, default=4,
                    help='Hasenbusch: fine (heavy-PF + aux) 2MN steps per coarse position '
                         'block (DR Phase-5s §3 starting point: 4).')
    ap.add_argument('--chrono', action=argparse.BooleanOptionalAction, default=True,
                    help='chronological inversion (CG warm-start of the MD force solves; measured '
                         '1.43x on MD at m=0.05). Reversibility softens from the cold O(tol) '
                         'stopping-boundary level to a larger-but-controlled O(tol) history '
                         'dependence — certified unbiased at chain level by Creutz (fast + slow '
                         'gates in test_hs_rhmc_mlx). --no-chrono restores cold starts for '
                         'strict-reversibility studies.')
    ap.add_argument('--chrono-kappa-max', type=float, default=5.0e5,
                    help='mlx backend: auto-disable chrono for any coupling whose fermion-matrix '
                         'condition number κ=(λmax+m²)/m² exceeds this. Chrono softens MD '
                         'reversibility to |Δh|≈3–4e-4 across the whole stiff m=0.05 range '
                         '(vs ≈3–5e-5 chrono-off), above the ~1e-4 clean-HMC bar; the tax tracks '
                         'the stiffness (mass) regime, so κ is the proxy. Default 5e5 disables '
                         'chrono for m=0.05 (κ≥6.5e5) and keeps the ~1.4× MD win for milder masses '
                         '(m≥0.1, κ≲4e5). NOTE: m≥0.1 chrono reversibility not yet measured — '
                         'verify (or --no-chrono) before those production runs. Set 0 to disable '
                         'the gate (honor --chrono/--no-chrono verbatim).')
    ap.set_defaults(compile=True)
    return ap


def main():
    args = build_parser().parse_args()

    L, msq = args.l, args.mass ** 2
    use_hasenbusch = args.backend == 'mlx' and args.hasenbusch
    n_md, eps = resolve_working_point(use_hasenbusch, args.n_md, args.eps)
    if args.backend == 'mlx':
        import mlx.core as mx
        tag, dev_desc = 'mlx', str(mx.default_device())
    else:
        if torch is None:
            raise SystemExit("torch not installed — use --backend mlx or install the gpu extra")
        device = torch.device(args.device if (args.device != 'mps' or torch.backends.mps.is_available()) else 'cpu')
        if args.compile:
            st.enable_matvec_compile(mode='reduce-overhead' if device.type == 'cuda' else 'default')
        tag, dev_desc = ('eo' if args.engine == 'eo' else 'gpu'), device.type
    outdir = args.outdir or f"data/rhmc/L{L}{tag}_m{args.mass:g}"
    os.makedirs(outdir, exist_ok=True)
    setup_run_log(outdir)
    gs = args.couplings_only if args.couplings_only else coupling_grid(args.n_couplings, args.g_lo, args.g_hi)

    # backend-correct engine/solver labels (mlx always runs eo + reads --mlx-solver;
    # the torch --engine/--solver are ignored under mlx, so don't advertise them)
    if args.backend == 'mlx':
        engine_desc, solver_desc = 'eo', args.mlx_solver
    else:
        engine_desc, solver_desc = args.engine, args.solver
    print(f"GPU production: L={L} m={args.mass} backend={args.backend} engine={engine_desc} "
          f"device={dev_desc} solver={solver_desc} "
          f"R={args.replicas} n_md={n_md} eps={eps} n_poles={args.n_poles}  "
          f"{len(gs)} couplings × {args.n_meas} traj × {args.replicas} replicas → {outdir}", flush=True)
    for i, g in enumerate(gs):
        g = float(g)
        path = os.path.join(outdir, f"g{g:.4f}.npz")
        hasenbusch = None
        if use_hasenbusch:
            coeffs, rc, musq_g, lam = build_hasenbusch_coeffs_mlx(
                L, g, msq, args.n_poles, args.seed + i, musq=args.mu_sq,
                hb_relerr_tol=args.hb_relerr_tol, n_poles_cap=args.n_poles_cap)
            hasenbusch = dict(ratio_coeffs=rc, musq=musq_g, n_inner=args.hb_n_inner)
        elif args.backend == 'mlx':
            coeffs, lam = build_coeffs_mlx(L, g, msq, args.n_poles, args.seed + i,
                                           hb_relerr_tol=args.hb_relerr_tol, n_poles_cap=args.n_poles_cap)
        else:
            coeffs, lam = build_coeffs(L, g, msq, args.n_poles, args.seed + i)
        kappa = (lam + msq) / msq
        print(f"\n[{i+1}/{len(gs)}] g={g:.3f}  range[{msq:.4g},{lam+msq:.1f}] κ={kappa:.0f}", flush=True)
        if args.backend == 'mlx':
            chrono_g = chrono_for_kappa(args.chrono, kappa, args.chrono_kappa_max,
                                        hasenbusch=use_hasenbusch)
            if args.chrono and not chrono_g:
                reason = ("Hasenbusch trajectory (chrono-on unvalidated)" if use_hasenbusch
                          else f"κ={kappa:.3g} > {args.chrono_kappa_max:.3g} "
                               f"(reversibility floor > chrono speed at this stiffness)")
                print(f"    chrono auto-OFF: {reason}", flush=True)
            s = run_coupling_mlx(path, g, L, msq, coeffs, args.replicas, eps, n_md,
                                 args.n_meas, args.n_therm, args.seed + i, chrono=chrono_g,
                                 mlx_solver=args.mlx_solver, checkpoint_every=args.checkpoint_every,
                                 hasenbusch=hasenbusch)
        else:
            s = run_coupling(path, g, L, msq, coeffs, args.replicas, eps, n_md,
                             args.n_meas, args.n_therm, device, args.seed + i,
                             solver=args.solver, engine=args.engine, chrono=args.chrono)
        print(f"  → done g={g:.3f}: acc={s['acc']:.2f} <tet>={s['tet']:.4f} "
              f"n={s['n']} {s['s_per_traj']*1000:.0f} ms/traj", flush=True)
    print(f"\nComplete → {outdir}  (monitor: rhmc_monitor.py {outdir} --watch 300)", flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
