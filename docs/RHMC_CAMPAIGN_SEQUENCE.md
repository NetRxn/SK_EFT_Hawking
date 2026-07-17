# RHMC vestigial campaign — the correct remaining run sequence

**Purpose.** The single authoritative walk-through of the runs still needed to settle
the vestigial-condensate question on the HS+RHMC lattice. This is the *scientific*
sequence (what to run, in what order, and the decision gate after each); the engine
mechanics, resource profile, and per-op flags live in the companion
[`RHMC_MLX_RUNBOOK.md`](RHMC_MLX_RUNBOOK.md) — read that for *how* the engine runs, this
for *what* to run next.

**The physics question.** Is there a genuine vestigial (nematic-metric) ordering of the
auxiliary field `h`, surviving the thermodynamic (L→∞) and chiral (m→0) limits — or is
every apparent signal a finite-volume noise-floor artifact? The deliverable is a
*defensible* answer either way. A literature-grade null at the reference point is fine to
ship first; the full sequence below is what makes the answer complete.

**"Done" =** the noise-subtracted order parameters (tetrad vs 16⟨h²⟩/V floor; Tr Q̃² vs
spatial-shuffle floor) and the FSS discriminants (connected susceptibility χ, Binder
cumulant) are resolved across the (L, m) grid, and the m→0 / L→∞ trends give a
consistent verdict — with the Metropolis certification ⟨e^-ΔH⟩ = 1 holding at every point.

---

## Settled decisions (do not re-derive these each session)

1. **Engine = Hasenbusch(K=1), chrono-OFF, refined solver.** At the stiff reference point
   (L=8, m=0.05, g=8) this is exact (⟨e^-ΔH⟩ = 1.0000 over 140×16), and it *dominates* the
   single-PF engine on both axes we care about: faster per trajectory (73 vs 96 s/traj,
   both chrono-off) **and** ~5× shorter autocorrelation (τ(tet) ≈ 6–8 vs ~34). Both engines
   are exact; Hasenbusch simply produces far more independent samples per hour, which is
   what makes the g≥5 region trustworthy.
2. **chrono is OFF for this campaign — the driver enforces it under `--hasenbusch`.** chrono
   (MD-force warm-starting) softens reversibility and biases ⟨e^-ΔH⟩ to ~0.92 in the stiff
   (small-m, high-κ) regime. As of 2026-07-17 `--hasenbusch` forces chrono OFF in code
   (`chrono_for_kappa(..., hasenbusch=True)` → always False), because Hasenbusch-chrono-on is
   unvalidated — so you pass nothing. (The single-PF engine still relies on the κ-gate, which
   is only in the unmerged `mlx-rhmc-hikappa-chrono` branch; if you ever run single-PF from
   `main` at small m, pass `--no-chrono` until that merges.)
3. **Certification gate is non-negotiable.** Every coupling must hold ⟨e^-ΔH⟩ ≈ 1
   (`rhmc_monitor` RED_BIAS = stop and diagnose). This is the correctness guarantee; a
   biased point cannot be salvaged by more statistics.
4. **Thermalization is single-cut (the driver does it; the analysis no longer re-cuts).**
   The driver's saved `*_history` is **measurement-only** (it discards `--n-therm` before
   recording, marking `n_therm_done` in the npz). As of 2026-07-17 `analyze_rhmc_vestigial.py`
   auto-detects that and defaults its extra cut to 0 (no double-cut) — so run the driver with a
   real `--n-therm` and analyze with no `--therm` flag. Still verify equilibration post-hoc (no
   trend in the first ~30 saved `<tet>`); bump `--n-therm` and resume if there is one.
5. **Homogeneous engine for any extrapolation.** m→0 and L→∞ fits must use data generated
   by the *same* engine. Historical Rust/torch m=0.1 nulls corroborate but are **not** part
   of the primary MLX-Hasenbusch dataset — regenerate m=0.1 here rather than mixing.

---

## Working points (per mass; τ_traj = eps·n_md ≈ 0.5)

Hasenbusch working point, measured at the worst-case g=8 (milder couplings are safer). The
fermion force stiffens as m→0, so **eps shrinks with m** — never reuse a lighter-mass eps at
a stiffer mass. For any new (L, m) corner, confirm acc ≳ 0.90 and ⟨e^-ΔH⟩ ≈ 1 with a short
scan first (`scratchpad/hasenbusch_workingpoint_scan.py`, or `scripts/scan_rhmc_l8_stepsize.py`).

| mass | `--n-md` (n_outer) | `--eps` | `--hb-n-inner` | acc (g=8) | status |
|---|---|---|---|---|---|
| **0.05** | **16** | **0.031** | **4** | **0.97** | measured (this session, tuning-scan winner) |
| 0.1 | ~16–20 | ~0.035 | 4 | — | **scan before use** (less stiff → expect ≥ m=0.05 eps) |
| 0.2 | ~16–20 | ~0.04 | 4 | — | **scan before use** |

The **m=0.05 row (16, 0.031, 4) is the built-in `--hasenbusch` default** (`resolve_working_point`)
— you don't pass it. Override `--n-md/--eps/--hb-n-inner` only for other masses, after scanning.
μ² (Hasenbusch split mass) defaults to the balanced √(m²·λmax) per coupling — leave it.
`--n-poles 24` is a floor that auto-bumps to hold the heatbath fit (≤ `--hb-relerr-tol` 1e-3).

---

## The sequence

Each phase writes to `data/rhmc/L{L}mlx_m{mass}` (or an explicit `--outdir`), is
checkpoint-resumable, and is followed by an **analysis gate** that decides whether to
proceed, expand, or ship. Statistics target: **n_meas = 400** gives displayed
neff = n_meas/(2τ) ≈ 28 at τ≈7 — comfortably past run #2's marginal ~7. (The 16 replicas
are averaged per trajectory before the autocorrelation analysis, so they sharpen the error
bar but do not raise the *displayed* neff — τ is what gates it. This is why the τ reduction,
not raw speed, is the real win.)

### Phase 1 — reference null: L=8, m=0.05  *(ready to run)*
The literature-grade starting point. Couplings g = 3,4,5,6,8 (weighted to high-g, where a
signal would first appear). Run from the `mlx-hikappa` worktree (which carries the validated
engine); writes to the main checkout's gitignored `data/`:

```bash
cd /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.claude/worktrees/mlx-hikappa
OUT=/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/data/rhmc/L8mlx_m0.05_hasenbusch
caffeinate -is env PYTHONUNBUFFERED=1 uv run --no-sync python scripts/run_rhmc_gpu_production.py \
  --backend mlx --hasenbusch \
  --mass 0.05 --l 8 --replicas 16 \
  --couplings-only 3 4 5 6 8 \
  --n-therm 150 --n-meas 400 \
  --outdir "$OUT" >> "$OUT/run.log" 2>&1 &
```
`--hasenbusch` auto-selects chrono-off and the tuned working point (n_md=16, eps=0.031,
hb-n-inner=4) — nothing else to pass. (`uv run --no-sync` uses the worktree venv as-is; a
bare `uv sync --extra mlx` drops torch.)

- **Gate:** `analyze_rhmc_vestigial.py "$OUT"` (therm-cut auto) → both channels at floor
  (ratio ≈ 1) and χ flat ⟹ null confirmed at the reference point. A significant floor-excess
  ⟹ a candidate signal: densify couplings around it and add statistics before believing it.

### Phase 2 — mass axis at L=8: add m=0.1 and m=0.2  (→ m→0 extrapolation)
Complete the chiral axis under this engine. m→0 *is* the deliverable (the γ5 mass is a
chiral regulator). Scan each mass's working point first (table above), then run g = 3,4,5,6,8.
- **Gate:** `analyze_rhmc_vestigial.py data/rhmc/L8mlx_m0.05 …_m0.1 …_m0.2` →
  the m→0 extrapolation of the noise-subtracted order params. Extrapolates to floor ⟹
  no condensate in the chiral limit at L=8. Extrapolates *above* floor ⟹ escalate to Phase 3
  focused on the couplings/masses that survive.

### Phase 3 — volume axis (FSS): L=10, 12 at m=0.05, matched couplings
The thermodynamic-limit test. Run the *same* couplings at larger L so the Binder cumulants
are comparable. Cost ∝ L⁴ (see runbook table: ~2.9 min/traj at L=10, ~6 min/traj at L=12 on
the Mac) — this is where the 3090 or patience is required.
- **Gate (built into the analysis):** the "FSS-gate observables" block —
  χ growing/peaking as V↑, or Binder curves **crossing** across L=8/10/12 ⟹ a real
  transition (expand the grid around it). Flat χ + no Binder crossing ⟹ **ship the null**
  (and Phase 4 is unnecessary). A single-L Binder ≈ 0.6 is the disordered baseline, not order.

### Phase 4 — only if Phases 2–3 show a surviving signal
Densify couplings around the candidate transition, add L (and possibly smaller m), and
push statistics where τ has blown up (critical slowing is worst exactly there). This phase
is data-driven: the gates above define its scope. If Phases 2–3 are null, there is no Phase 4.

---

## Gotchas & unknowns for the real-physics piece

- **chrono** — fixed in code: `--hasenbusch` forces chrono-off, so the campaign is safe by
  default. The only residual: the *single-PF* engine on `main` still defaults chrono-on and
  relies on the κ-gate (unmerged) to disable it at small m — so if you ever run single-PF from
  `main` at m≤0.05, pass `--no-chrono`. Merging `mlx-rhmc-hikappa-chrono` closes that too.
- **Analysis therm double-cut** — fixed: `analyze_rhmc_vestigial.py` auto-detects
  driver-thermalized data (`n_therm_done`) and no longer re-cuts. No flag needed.
- **Larger-L / CUDA reality:** the fused Metal hop kernel is **Metal-only**; on the 3090 the
  engine auto-falls-back to the (slower) einsum path, so the 3090's per-traj advantage is
  *not* realized until a CUDA fused kernel exists — L=12 is multi-day on either box. The
  Metal→CUDA FP32 ratio (~3.5×) is unpinned, so 3090 timings are estimates. **Validate the
  CUDA path (`scripts/validate_cuda_rhmc.py`) before trusting any 3090 result** — Metal is
  FP32-only, so the refined solver's FP32/FP64 seam behaves differently on native-FP64 CUDA.
- **Deflation is not built.** The heatbath's ~m² Zolotarev tail is "deflation territory at
  larger volumes." The current engine's practical envelope is **L ≤ 12, m ≥ 0.05**; L=16 or
  much smaller m needs solver work first (do not silently run outside this and trust it).
- **Critical slowing at a transition.** If the FSS gate fires, τ spikes exactly where the
  physics is — Hasenbusch helps but may not fully cure it; budget extra statistics there.
- **Per-corner working-point validation.** Never blind-reuse a working point at a stiffer
  mass or larger L; a 5-point scan (~30 min) confirms acc + ⟨e^-ΔH⟩ first.
- **Optional writeup rigor:** the τ≈5× reduction is measured against run #2's estimator
  (unmatched). A matched single-PF chrono-off τ(tet) arm from the same config (~2.7 h,
  same estimator) turns "≈5×" into a clean, referee-proof number. Not decision-critical
  (Hasenbusch already dominates), but worth it for the methods section.

## Operational (true for every phase, stated once)
- **Resume is lossless.** Re-run the identical command; the driver reloads each coupling's
  npz, skips completed couplings, continues a partially-thermalized chain, and preserves
  acceptance counters. Run in whatever chunks suit the machine's availability — the science
  above does not depend on the chunking.
- **Monitor:** `scripts/rhmc_monitor.py <dir>` (add `--watch 300` to poll). Expect
  ⟨e^-ΔH⟩ ≈ 1.00, τ ≈ 6–10 (not ~34), per-coupling RED_NULL / GREEN / YELLOW.
- **One GPU.** Do not launch parallel driver processes — they serialize and contend.
  `caffeinate -is` on AC, lid open, to prevent sleep-stall.

## Open engineering items (tracked; not blockers for Phases 1–3)
- Merge `mlx-rhmc-hikappa-chrono` (κ-gate) → main so the chrono default is safe repo-wide.
- CUDA fused hop kernel (unlocks the 3090 for L≥12).
- Heatbath deflation (unlocks L≥16 / m<0.05).
- Optional matched single-PF τ arm for the methods claim.
