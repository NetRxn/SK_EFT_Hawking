"""Process-parallel CPU RHMC runner — fills all physical cores by mapping the INDEPENDENT
(coupling, replica) Markov chains onto a process pool, ONE thread per worker.

Why this exists (measured, 2026-07-01, L=8 m=0.1 on a 16-core Mac):
  The batched driver (run_rhmc_gpu_production.py) batches R replicas into one tensor and
  runs couplings sequentially. Its hot op is a batched pile of tiny 8x8 matvecs that is
  MEMORY-BANDWIDTH-BOUND: it saturates at ~3 cores (K=1 solve) / ~1.5 cores (K=14 heatbath)
  no matter how many threads exist. Result: ~3 of 16 cores ever work; a full probe ~ days.
  A single chain at num_threads=1 solves in 2.3s on 1.0 core — FASTER per-chain than the
  batched 2.6s/chain, and it scales linearly across independent processes. 16 procs x 1
  thread  ->  ~18x throughput, full 16-core utilization, L=8 tractable on the Mac.

Correctness: each worker runs the EXACT run_coupling code path with R=1 (bit-identical per
chain); torch.set_num_threads(1) removes the intra-op contention. Per-(coupling,replica)
seeds are distinct + reproducible. After the pool drains, per-replica npz files are
aggregated into the SAME per-coupling schema the batched driver wrote (replica-mean series
+ stacked h_state), so rhmc_monitor.py / the analyzer are unchanged.

torch.compile is DISABLED here: it single-threads per-shape codegen on CPU (measured net
LOSS in the full-trajectory context) and fights the 1-thread-per-worker design.
"""
import argparse
import os
import sys

import numpy as np

# Must cap threads BEFORE torch is imported anywhere in the worker (BLAS reads env at init).
os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")
os.environ.setdefault("VECLIB_MAXIMUM_THREADS", "1")

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def _run_one_chain(task):
    """Worker: run ONE (coupling g, replica r) chain at R=1, num_threads=1. Writes its own
    npz at <outdir>/g{g}_r{r}.npz. Returns (g, r, summary) for the aggregation/report."""
    import time
    import torch
    torch.set_num_threads(1)
    torch.set_default_dtype(torch.float64)
    from scripts.run_rhmc_gpu_production import run_coupling, build_coeffs

    (g, r, L, msq, n_poles, eps, n_md, n_meas, n_therm, seed, outdir,
     engine, solver) = task
    cpu = torch.device("cpu")
    coeffs, lam = build_coeffs(L, g, msq, n_poles, seed)
    path = os.path.join(outdir, f"g{g:.4f}_r{r}.npz")
    t0 = time.time()
    s = run_coupling(path, g, L, msq, coeffs, 1, eps, n_md, n_meas, n_therm,
                     cpu, seed, solver=solver, engine=engine, chrono=False)
    s["wall"] = time.time() - t0
    s["kappa"] = (lam + msq) / msq
    return (g, r, s)


def aggregate_coupling(outdir, g, n_replicas, L, mass):
    """Combine g{g}_r0..r{R-1}.npz  ->  g{g}.npz in the batched-driver schema (replica-mean
    per-trajectory series; stacked h_state). No-op-safe if some replicas are missing."""
    files = [os.path.join(outdir, f"g{g:.4f}_r{r}.npz") for r in range(n_replicas)]
    files = [f for f in files if os.path.exists(f)]
    if not files:
        return None
    ds = [np.load(f) for f in files]
    n = min(len(d["tet_m2_history"]) for d in ds)          # align to shortest chain
    def stack_mean(key):
        return np.mean([np.asarray(d[key])[:n] for d in ds], axis=0)
    out = dict(
        h_sq_history=stack_mean("h_sq_history"),
        delta_h_history=stack_mean("delta_h_history"),
        tet_m2_history=stack_mean("tet_m2_history"),
        tr_q2_history=stack_mean("tr_q2_history"),
        m_h_history=stack_mean("m_h_history"),
        Q_history=stack_mean("Q_history"),
        h_final=np.asarray(ds[0]["h_final"]),
        h_state=np.stack([np.asarray(d["h_state"])[0] for d in ds]),   # (R, V, 4, 4)
        acceptance_rate=np.mean([float(d["acceptance_rate"]) for d in ds]),
        g=np.float64(g), L=np.int64(L), mass=np.float64(mass), replicas=np.int64(len(ds)),
    )
    agg = os.path.join(outdir, f"g{g:.4f}.npz")
    np.savez(agg, **out)
    return dict(g=g, n=n, acc=out["acceptance_rate"], tet=float(np.mean(out["tet_m2_history"])))


def main():
    import multiprocessing as mp

    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--l", type=int, default=8)
    ap.add_argument("--mass", type=float, required=True)
    ap.add_argument("--couplings", type=float, nargs="+", required=True)
    ap.add_argument("--replicas", type=int, default=4)
    ap.add_argument("--n-therm", type=int, default=100)
    ap.add_argument("--n-meas", type=int, default=400)
    ap.add_argument("--n-md", type=int, default=16)
    ap.add_argument("--eps", type=float, default=0.03)
    ap.add_argument("--n-poles", type=int, default=14)
    ap.add_argument("--seed", type=int, default=2026)
    ap.add_argument("--engine", type=str, default="eo", choices=["full", "eo"])
    ap.add_argument("--solver", type=str, default="refined", choices=["refined", "mixed"])
    ap.add_argument("--outdir", type=str, default=None)
    ap.add_argument("--workers", type=int, default=None,
                    help="pool size (default: physical cores). Total chains = couplings x replicas.")
    args = ap.parse_args()

    L, msq = args.l, args.mass ** 2
    outdir = args.outdir or f"data/rhmc/L{L}eo_m{args.mass:g}"
    os.makedirs(outdir, exist_ok=True)
    gs = [float(g) for g in args.couplings]

    # distinct, reproducible per-(coupling,replica) seed; 10000 stride avoids collisions
    tasks = []
    for ci, g in enumerate(gs):
        for r in range(args.replicas):
            seed = args.seed + ci * 10000 + r
            tasks.append((g, r, L, msq, args.n_poles, args.eps, args.n_md,
                          args.n_meas, args.n_therm, seed, outdir, args.engine, args.solver))

    ncpu = os.cpu_count() or 8
    try:
        import subprocess
        phys = int(subprocess.check_output(["sysctl", "-n", "hw.physicalcpu"]).strip())
    except Exception:
        phys = ncpu
    workers = args.workers or min(phys, len(tasks))

    print(f"PARALLEL RHMC: L={L} m={args.mass} engine={args.engine} "
          f"{len(gs)} couplings x {args.replicas} replicas = {len(tasks)} chains "
          f"on {workers} single-thread workers (phys cores={phys}) -> {outdir}", flush=True)
    print(f"  per chain: {args.n_therm} therm + {args.n_meas} meas, n_md={args.n_md} eps={args.eps}",
          flush=True)

    ctx = mp.get_context("spawn")            # macOS-safe; each worker re-inits torch @ 1 thread
    import time
    t0 = time.time()
    done = 0
    with ctx.Pool(processes=workers, maxtasksperchild=1) as pool:
        for (g, r, s) in pool.imap_unordered(_run_one_chain, tasks):
            done += 1
            print(f"  [{done}/{len(tasks)}] g={g:.3f} r={r}: acc={s['acc']:.2f} "
                  f"<tet>={s['tet']:.4f} n={s['n']} κ={s['kappa']:.0f} "
                  f"{s['wall']:.0f}s ({s['wall']/max(s['n']+args.n_therm,1):.1f}s/traj)", flush=True)

    print(f"\nall chains done in {(time.time()-t0)/60:.1f} min; aggregating per coupling...", flush=True)
    for g in gs:
        a = aggregate_coupling(outdir, g, args.replicas, L, args.mass)
        if a:
            print(f"  g={g:.3f}: <tet>={a['tet']:.4f} acc={a['acc']:.2f} n={a['n']} "
                  f"-> g{g:.4f}.npz", flush=True)
    print(f"\nComplete -> {outdir}  (monitor: rhmc_monitor.py {outdir})", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
