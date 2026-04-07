# RHMC Production Guide

## Quick Start

```bash
# Standard L=8 production with critical region focus (recommended):
nohup ./scripts/run_rhmc_epochs.sh --l 8 \
  --g-critical-min 3.0 --g-critical-max 5.0 \
  > data/rhmc/rhmc_l8.log 2>&1 &

# Check progress:
tail -20 data/rhmc/rhmc_l8.log

# Check data:
ls -lh data/rhmc/L8_g*.npz
```

**Always use `run_rhmc_epochs.sh`**, not `run_rhmc_production.py` directly. The epoch wrapper prevents thermal throttling and memory degradation that cause 5-8x slowdowns in long runs.

The `--g-critical-min/max` flags add 8 extra fine-grained coupling points in the critical region (g=3-5, where the gap equation predicts G_c ≈ 4.0). These are merged with the 14 uniform points for a total of ~22 couplings.

## How It Works

```
run_rhmc_epochs.sh
  └─ calls run_rhmc_production.py N times (default: 5 × 100 traj)
       └─ each invocation resumes from .npz checkpoints
            └─ checkpoints save every 10 trajectories (atomic write)
                 └─ h-field state carried across invocations
```

The checkpoint system makes this fully restartable:
- Kill anytime (Ctrl-C, kill, reboot) — at most 10 trajectories lost
- Resume by re-running the same command — it detects partial runs
- No re-thermalization on resume (h-field state saved in .npz)

## Recommended Settings by Lattice Size

| Parameter | L=4 | L=8 | L=16 |
|-----------|-----|-----|------|
| `--n-md-steps` | 20 | **160** | 200+ |
| `--workers` | 6 | **4** | 2 |
| `EPOCHS` | 5 | **5** | 10 |
| `TRAJ_PER_EPOCH` | 100 | **100** | 50 |
| `COOLDOWN` | 10 | **30** | 60 |
| Target acceptance | >60% | >50% | >30% |
| Time/traj (est.) | 1-3s | 30-60s | 200-500s |

The production script defaults (`--n-md-steps 60`, `--workers 4`, `--chunk-size 10`) are tuned for L=8.

**Important: n_md_steps scales with coupling stiffness.** At low coupling (g<2), the fermion matrix condition number is large, requiring smaller MD steps. Empirical findings from L=8 production:
- n_md_steps=30: |ΔH|>1 everywhere, acceptance <40% — **unusable**
- n_md_steps=80: |ΔH|~2-4 at g<2 (acceptance 0-20%), |ΔH|~1-2 at g>3 (acceptance 30-60%) — **marginal in critical region**
- n_md_steps=160: expected |ΔH|~1-2 at g<2, |ΔH|<1 at g>3 — **recommended for full coupling range**

Use `--n-md-steps 160` for L=8 production spanning the critical region g=2-6.

## Why Epochs (Not One Long Run)

Running `run_rhmc_production.py` directly for 500 trajectories works but degrades:

| Hours | Traj/s | Cause |
|-------|--------|-------|
| 0-2 | ~23s | Fresh process, cool CPU |
| 4-6 | ~60s | Thermal throttling begins |
| 8-12 | ~120s | Memory fragmentation + sustained throttle |
| 14+ | ~180s | Full throttle + heap bloat |

Epoch cycling (5 × 100 traj with 30s cooldown) keeps each process under 2 hours:
- CPU cools during 30s gaps → no thermal throttle
- Fresh Python/Rust process → no memory fragmentation
- Checkpoint/resume → zero lost work

## Acceptance Rate Diagnostics

The RHMC acceptance rate depends on `|ΔH|` (MD energy violation):

| |ΔH| | Accept rate | Assessment |
|------|-------------|------------|
| < 0.5 | > 70% | Excellent |
| 0.5-1.0 | 40-70% | Good |
| 1.0-2.0 | 15-40% | Marginal — increase n_md_steps |
| > 2.0 | < 15% | Poor — double n_md_steps |

If acceptance is consistently below 30%, increase `--n-md-steps`. The cost is linear (2x steps → 2x time/traj) but the effective statistics improve faster because fewer trajectories are wasted.

## Data Format

Each coupling produces `data/rhmc/L{L}_g{g:.4f}.npz` containing:

| Key | Shape | Description |
|-----|-------|-------------|
| `h_sq_history` | (N,) | ⟨h²⟩ per accepted trajectory |
| `delta_h_history` | (M,) | |ΔH| per proposed trajectory (M ≥ N) |
| `tet_m2_history` | (N,) | Tetrad order parameter m² |
| `tr_q2_history` | (N,) | Tr(Q²) gauge observable |
| `h_final` | (L⁴,) | Final h-field configuration (for resume) |
| `acceptance_rate` | scalar | Last chunk's acceptance rate |
| `g` | scalar | Coupling value |
| `L` | scalar | Lattice size |
| `n_md_steps` | scalar | MD steps used |

## Analysis Pipeline

After production, analyze with verified statistics:

```bash
# Preliminary 4-panel diagnostic:
uv run python -c "
from src.core.visualizations import fig_rhmc_l8_preliminary
fig = fig_rhmc_l8_preliminary()
fig.write_html('figures/fig_rhmc_l8_preliminary.html')
fig.show()
"

# Full analysis with verified estimators:
uv run python -c "
from src.vestigial.verified_analysis import analyze_rhmc_scan
results = analyze_rhmc_scan('data/rhmc', lattice_size=8)
for r in results:
    print(f'g={r[\"coupling\"]:.2f}: mean={r[\"mean\"]:.4f} ± {r[\"jackknife_error\"]:.4f}, '
          f'tau_int={r[\"tau_int\"]:.1f}, N_eff={r[\"n_eff\"]:.0f}, U4={r[\"binder_U4\"]:.3f}')
"
```

The verified analysis uses `jackknife_variance`, `autocovariance`, `integrated_autocorrelation_time`, and `effective_sample_size` from `formulas.py`, all with Lean theorem references (VerifiedJackknife.lean, VerifiedStatistics.lean).

## Roadmap References

- **Phase 5d Wave 3**: MC production scoped, MF-guided scan parameters
- **Phase 5f Waves 5-6**: L=8 analysis + L=6 finite-size scaling
- **Paper 5**: ADW gap equation + MC results
- **Paper 6**: Vestigial metric phase (Binder crossing, phase boundary)
