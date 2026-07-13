# RHMC GPU runbook — MLX backend (Metal + CUDA)

Operator guide for the MLX port of the HS+RHMC vestigial-lattice engine
(`src/vestigial/hs_rhmc_mlx.py`, driven by `scripts/run_rhmc_gpu_production.py
--backend mlx`). One source runs on Apple-Silicon **Metal** (macOS) and on
**CUDA** (Linux, via the `mlx[cuda]` extra — the 3090). It replaces the
torch-MPS GPU path.

The MLX engine samples the **identical target density** as the Rust and torch
engines (`det(A†A+m²)^{1/4} = det(M_e+m²)^{1/2}`, proven), with an FP64-exact
Metropolis test, so every downstream tool — `rhmc_monitor.py` (early-stop),
`analyze_rhmc_vestigial.py` (m→0 extrapolation + noise-floor detectors) — works
unchanged on its output.

---

## 1. Default behavior (what changed)

- `--backend torch` (default, unchanged) → the Rust/torch stencil engine.
- `--backend mlx` → the MLX engine. **`--mlx-solver` defaults to `refined`.**

**The `refined` solver is the fast path and the default.** Metal is FP32-only,
so the exact-Metropolis FP64 stages (heatbath + accept/reject) cannot run on the
GPU directly. The refined solver does the heavy conjugate-gradient work in FP32
on the GPU and corrects the residual in FP64 on the CPU stream (~3–4 cheap outer
passes) — recovering a **bit-exact FP64 Metropolis test at GPU speed**. Without
it, those FP64 solves fall back to the MLX CPU backend and dominate the
trajectory (they are ~97% of the wall time). `--mlx-solver mixed` keeps the FP64
accept/reject on the CPU stream — a portable fallback only; do not use it for
production on the Mac.

Certification (all green, `tests/test_hs_rhmc_mlx.py`): refined solve == pure
FP64 to 1e-8; refined action == FP64 to 1e-7; heatbath `S_PF = ½‖ξ‖²`
(one-Majorana); reversibility to 1e-9; and the chain-level Creutz gate
`⟨e^-ΔH⟩ = 1` running the FP32 inner solves **on Metal**.

**Measured (M3 Max, L=8, R=4, n_md=4):** refined trajectory **~27 s** vs the
naive MLX-CPU-FP64 path 550 s (20×) and vs torch-MPS 399 s (~15×).

---

## 2. Does the Mac need to be clear of other processes?

**No — this is the big operational change from the Rust/torch path.** The MLX
refined run is a **single process, GPU-bound**, not the Rust engine's 14–16
single-threaded worker pool.

Measured resource profile of a production L=8 R=4 run (`/usr/bin/time -l`, 3
trajectories):

| Resource | Usage | Implication |
|---|---|---|
| CPU | **~0.3 cores average** (27 s user + 4 s sys over 100 s wall) | Runs happily alongside CPU-heavy work |
| GPU (Metal) | Heavy — the trajectory's real workload | **The one shared resource to protect** |
| RAM (RSS) | ~0.8 GB at L=8 (sparse stencil, no dense build) | Negligible on 128 GB |
| File descriptors | one process | No ENFILE risk (unlike the 16-worker Rust path) |

**Practical guidance:**

- **CPU-heavy work alongside is fine.** The old Rust/torch path needed the whole
  box (and the memory note warned it "cannot share with 3-worktree Lean dev —
  cores + duration + ENFILE"). The MLX refined path uses ~0.3 cores, so the Lean
  MCP swarm, `lake build`, editors, browsers, etc. do **not** contend.
- **Keep the GPU relatively free.** The GPU is now the bottleneck resource. A
  *second* heavy Metal/GPU job — another ML training run, GPU video render, a
  big Blender/Metal task — will contend for the GPU queue and unified-memory
  bandwidth and slow the run. Ordinary desktop GPU use (browser compositing, a
  video call) is not a problem.
- **Prevent sleep on long runs.** A run suspended by macOS sleep looks "running"
  but makes no progress (documented footgun). Launch under `caffeinate -is`,
  lid **open** (single internal display ⟹ no clamshell), on AC:

  ```bash
  caffeinate -is env PYTHONPATH=. uv run python scripts/run_rhmc_gpu_production.py \
      --backend mlx ... > logs/rhmc_mlx.log 2>&1 &
  ```

- **`--replicas` is the GPU-saturation knob**, not process parallelism: replicas
  batch into one wide tensor in the single GPU context. More replicas = better
  GPU utilization *and* more independent chains (directly fixes the high-g
  thin-statistics problem, see §3). Do **not** launch multiple driver processes
  to parallelize — one GPU, they would serialize and contend.

---

## 3. Narrowing on the areas the previous run identified

The prior L=8 **m=0.1** campaign (Rust 2026-06-30, torch 2026-07-02) returned a
**proven null** — both order-parameter channels sit at the finite-V noise floor
at every coupling. Do **not** simply re-run m=0.1; that only sharpens a null. The
MLX engine reproduces the identical physics, so the previously-decided targeting
plan carries over verbatim:

1. **Build the m→0 set.** m=0.1 is the most chirally-*suppressed* point; run the
   other two masses **m=0.05 and m=0.2**, then extrapolate m→0. The γ5 mass is a
   chiral regulator, so the m→0 extrapolation *is* the deliverable.
2. **Weight the high-g region.** The calibrated monitor read the m=0.1 run as
   `RED_NULL` at low/mid g but **`YELLOW` (thin, N_eff 5–9) at high g** — where
   any real signal would most likely appear. Put more replicas / trajectories
   there, not uniformly across g.
3. **Use the noise-immune detectors, not the raw curves.** The raw `<tet>` rise
   is an artifact (it just tracks `⟨h²⟩ ∝ g²`). `analyze_rhmc_vestigial.py`
   applies the floor-subtracted / shuffle-floor / Binder-cumulant detectors and
   the m→0 extrapolation across the mass directories.
4. **Watch the early-stop monitor live.** `rhmc_monitor.py <dir> --watch 300`
   emits per-coupling `RED_NULL` (stop — compute wasted here) vs `YELLOW`
   (more stats productive) vs `GREEN` (signal). This is what tells you where to
   stop rather than grinding a null.

The driver **default** (`--n-couplings 14 --g-lo 0.5 --g-hi 8.0`) is the *broad*
scan — it does not encode this targeting. Narrow it explicitly with
`--couplings-only` or a tighter `--g-lo/--g-hi`, as in the recipes below.

---

## 4. Recipes

**Mac — m→0 set, high-g focus (the recommended next physics):**

```bash
# m = 0.05 and m = 0.2 (m = 0.1 already done, null). High-g window, more replicas
# where the signal would appear. Refined solver is the default.
for M in 0.05 0.2; do
  caffeinate -is env PYTHONPATH=. uv run python scripts/run_rhmc_gpu_production.py \
      --backend mlx --l 8 --mass $M --replicas 16 \
      --couplings-only 3.0 4.0 5.0 6.0 8.0 \
      --n-therm 100 --n-meas 400 --n-md 16 --eps 0.03 \
      > logs/rhmc_mlx_l8_m$M.log 2>&1
done

# Live early-stop while running (separate terminal):
PYTHONPATH=. uv run python scripts/rhmc_monitor.py data/rhmc/L8mlx_m0.05 --watch 300

# m→0 extrapolation + noise-immune detectors once ≥2 masses exist:
PYTHONPATH=. uv run python scripts/analyze_rhmc_vestigial.py data/rhmc/L8mlx_m0.05 \
    data/rhmc/L8mlx_m0.1 data/rhmc/L8mlx_m0.2
```

**3090 (Linux) — same command, CUDA:** install with the CUDA extra
(`uv sync --extra mlx` picks `mlx[cuda]` on Linux; on CUDA-13 use
`mlx[cuda13]`), then run the identical command — MLX's default device is the
GPU, so `--backend mlx` targets CUDA with no other change. This is the path for
**L=10/12** (cost grows ∝ L⁶; L=12 wants the 3090 regardless of backend).

**Smoke test (either platform, ~1 min):**

```bash
PYTHONPATH=. uv run python scripts/run_rhmc_gpu_production.py --backend mlx \
    --l 4 --mass 0.1 --replicas 4 --n-therm 3 --n-meas 20 --n-md 4 \
    --n-couplings 2 --g-lo 1.5 --g-hi 3.0 --outdir data/rhmc/L4mlx_smoke
PYTHONPATH=. uv run python scripts/rhmc_monitor.py data/rhmc/L4mlx_smoke
```

---

## 5. Notes / gotchas for anyone extending the engine

- **Metal is FP32-only.** Every op with a float64 operand — including casts and
  array slices `x[0]` — must run on the CPU stream (`with mx.stream(mx.cpu)`),
  or MLX raises `float64 is not supported on the GPU`. The test suite pins the
  default device to CPU (autouse fixture), which *masks* these seams, so verify
  any new FP64 path under the GPU default device separately.
- `mx.einsum` does not broadcast mismatched ellipsis batch dims (blocks
  `(B,1,…)` vs psi `(B,K,…)`) — use `@`/matmul.
- Call trajectory functions with an `mx.eval` barrier between independent runs;
  the production loop already evaluates observables each trajectory so this is a
  test-only concern.
