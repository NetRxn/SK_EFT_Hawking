"""Benchmark: MLX vs torch RHMC stencil engines — the MLX-adoption decision gate.

Like-for-like timings of the three production-relevant layers, FP32 (the MD
precision), on every available backend:

  1. matvec   — apply_AtA at L, wide batch (couplings x replicas fused; the
                historical torch-MPS measured point is L=8, batch 168)
  2. eo CG    — single-shift (M_e+m^2)^-1 solve (the eo-path unit of work)
  3. traj     — one eo mixed-precision trajectory (FP32 MD + FP64 accept/reject),
                the actual production path, R replicas   [--traj to enable]

Backends auto-detected: torch-cpu, torch-mps / torch-cuda, mlx-cpu, mlx-gpu
(Metal here, CUDA on a Linux box with mlx[cuda] — same script, no changes).

Usage:
  PYTHONPATH=. uv run python scripts/benchmark_mlx_stencil.py            # matvec + CG
  PYTHONPATH=. uv run python scripts/benchmark_mlx_stencil.py --traj    # + trajectory
  PYTHONPATH=. uv run python scripts/benchmark_mlx_stencil.py --l 4 --batch 32
"""
import argparse
import time

import numpy as np

G_COUPLING = 2.0          # equilibrium amplitude ~ sqrt(2g) — lambda_max must be
MSQ = 0.01                # estimated from an equilibrium-scale config (per the
N_POLES = 12              # 2026-06-30 reject-all lesson), not an inflated one.


class _Rows(list):
    """Row sink that prints each result as it lands — a late crash can't lose
    minutes of earlier timings."""

    def append(self, row):
        name, bench, batch, t = row
        print(f"  [{name}] {bench} batch={batch}: {t:.4f}s", flush=True)
        super().append(row)


def _timeit(fn, sync, n_warm=2, n_rep=5):
    for _ in range(n_warm):
        sync(fn())
    ts = []
    for _ in range(n_rep):
        t0 = time.perf_counter()
        sync(fn())
        ts.append(time.perf_counter() - t0)
    return min(ts)


def bench_torch(device, L, batch, replicas, n_md, do_traj, rows):
    import torch
    import src.vestigial.hs_rhmc_stencil as st

    dev = torch.device(device)
    name = f"torch-{device}"

    def sync(out):
        if device == "mps":
            torch.mps.synchronize()
        elif device == "cuda":
            torch.cuda.synchronize()
        return out

    V = L ** 4
    rng = np.random.default_rng(0)
    amp = (2.0 * G_COUPLING) ** 0.5
    h32 = torch.tensor(amp * rng.standard_normal((batch, V, 4, 4)),
                       dtype=torch.float32, device=dev)
    psi = torch.tensor(rng.standard_normal((batch, V, 8)), dtype=torch.float32, device=dev)
    fwd, back = st.neighbor_tables(L, dev)
    blocks = st.hopping_blocks(h32, L, device=dev, dtype=torch.float32)
    rows.append((name, "matvec", batch,
                 _timeit(lambda: st.apply_AtA(psi, blocks, fwd, back), sync)))

    eo = st.eo_tables(L, dev)
    hR = h32[:replicas]
    blocksR = st.hopping_blocks(hR, L, device=dev, dtype=torch.float32)
    b_e = torch.tensor(rng.standard_normal((replicas, V // 2, 8)),
                       dtype=torch.float32, device=dev)
    rows.append((name, "eo-CG", replicas,
                 _timeit(lambda: st.eo_multishift_cg(b_e, blocksR, eo, [MSQ],
                                                     tol=1e-5, max_iter=2000), sync, n_warm=1, n_rep=3)))

    if do_traj:
        cpu = torch.device("cpu")
        fwd64, back64 = st.neighbor_tables(L, cpu)
        eo64 = st.eo_tables(L, cpu)
        h64 = torch.tensor(amp * rng.standard_normal((replicas, V, 4, 4)), dtype=torch.float64)
        lam = float(st.estimate_lambda_max(
            st.hopping_blocks(h64[0], L, device=cpu, dtype=torch.float64),
            fwd64, back64, V, n_iter=100, seed=1))
        coeffs = st.make_rhmc_coeffs(1.3 * lam, MSQ, n_poles=N_POLES)
        gen = torch.Generator().manual_seed(0)
        t0 = time.perf_counter()
        st.eo_rhmc_trajectory_mixed(h64, G_COUPLING, MSQ, coeffs, eo64, fwd64, back64,
                                    eo, fwd, back, L, 0.03, n_md, dev, gen, gen,
                                    tol_md=1e-4, tol_acc=1e-10, chrono=True)
        rows.append((name, f"eo-traj(nmd={n_md})", replicas, time.perf_counter() - t0))


def bench_mlx(device, L, batch, replicas, n_md, do_traj, rows):
    import mlx.core as mx
    import src.vestigial.hs_rhmc_mlx as me

    mx.set_default_device(mx.gpu if device == "gpu" else mx.cpu)
    name = f"mlx-{device}"

    def sync(out):
        mx.eval(out) if isinstance(out, mx.array) else mx.eval(*out)
        return out

    V = L ** 4
    rng = np.random.default_rng(0)
    amp = (2.0 * G_COUPLING) ** 0.5
    h32 = mx.array(amp * rng.standard_normal((batch, V, 4, 4)), dtype=mx.float32)
    psi = mx.array(rng.standard_normal((batch, V, 8)), dtype=mx.float32)
    fwd, back = me.neighbor_tables(L)
    blocks = me.hopping_blocks(h32, L)
    mx.eval(blocks, psi)
    rows.append((name, "matvec", batch,
                 _timeit(lambda: me.apply_AtA(psi, blocks, fwd, back), sync)))

    eo = me.eo_tables(L)
    blocksR = me.hopping_blocks(h32[:replicas], L)
    b_e = mx.array(rng.standard_normal((replicas, V // 2, 8)), dtype=mx.float32)
    mx.eval(blocksR, b_e)
    rows.append((name, "eo-CG", replicas,
                 _timeit(lambda: me.eo_multishift_cg(b_e, blocksR, eo, [MSQ],
                                                     tol=1e-5, max_iter=2000), sync, n_warm=1, n_rep=3)))

    if do_traj:
        h64 = mx.array(amp * rng.standard_normal((replicas, V, 4, 4)), dtype=mx.float64)
        with mx.stream(mx.cpu):                    # raw f64 slice must stay off the GPU stream
            h0 = h64[0]
        lam = float(me.estimate_lambda_max(me.hopping_blocks(h0, L), fwd, back, V,
                                           n_iter=100, seed=1))
        coeffs = me.make_rhmc_coeffs(1.3 * lam, MSQ, n_poles=N_POLES)
        rng_t = np.random.default_rng(0)
        t0 = time.perf_counter()
        me.eo_rhmc_trajectory_mixed(h64, G_COUPLING, MSQ, coeffs, eo, fwd, back, L,
                                    0.03, n_md, rng_t, tol_md=1e-4, tol_acc=1e-10, chrono=True)
        rows.append((name, f"eo-traj(nmd={n_md})", replicas, time.perf_counter() - t0))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--l", type=int, default=8)
    ap.add_argument("--batch", type=int, default=168, help="matvec batch (couplings x replicas)")
    ap.add_argument("--replicas", type=int, default=4, help="CG/trajectory replica batch")
    ap.add_argument("--n-md", type=int, default=4, help="MD steps for the trajectory bench")
    ap.add_argument("--traj", action="store_true", help="include the trajectory benchmark")
    ap.add_argument("--engines", default=None,
                    help="comma list: torch-cpu,torch-mps,torch-cuda,mlx-cpu,mlx-gpu (default: auto)")
    args = ap.parse_args()

    engines = args.engines.split(",") if args.engines else None
    rows = _Rows()

    def want(e):
        return engines is None or e in engines

    try:
        import torch
        if want("torch-cpu"):
            bench_torch("cpu", args.l, args.batch, args.replicas, args.n_md, args.traj, rows)
        if want("torch-mps") and torch.backends.mps.is_available():
            bench_torch("mps", args.l, args.batch, args.replicas, args.n_md, args.traj, rows)
        if want("torch-cuda") and torch.cuda.is_available():
            bench_torch("cuda", args.l, args.batch, args.replicas, args.n_md, args.traj, rows)
    except ImportError:
        print("torch not installed — skipping torch backends")

    try:
        import mlx.core as mx
        if want("mlx-cpu"):
            bench_mlx("cpu", args.l, args.batch, args.replicas, args.n_md, args.traj, rows)
        if want("mlx-gpu") and (mx.metal.is_available() or getattr(mx, "cuda", None)
                                and mx.cuda.is_available()):
            bench_mlx("gpu", args.l, args.batch, args.replicas, args.n_md, args.traj, rows)
    except ImportError:
        print("mlx not installed — skipping mlx backends")

    print(f"\nL={args.l} (V={args.l ** 4}), fp32 kernels, best-of-reps wall time")
    print(f"{'backend':<12} {'bench':<18} {'batch':>5} {'seconds':>12}")
    base = {}
    for name, bench, batch, t in rows:
        base.setdefault(bench, t)
        rel = base[bench] / t if t > 0 else float("inf")
        print(f"{name:<12} {bench:<18} {batch:>5} {t:>12.4f}   ({rel:.2f}x vs first)")


if __name__ == "__main__":
    main()
