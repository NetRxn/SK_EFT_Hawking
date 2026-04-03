# Phase 6: Collaboration + HPC (Deferred)

## Items Requiring External Resources

*Prepared 2026-03-28 | Items deferred from Phase 5 because they require HPC access, experimental collaboration, or external triggers.*

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
> 1. Read [`/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/CLAUDE.md`](../../../CLAUDE.md) — project conventions, build commands, mandatory references
> 2. Read [`/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/WAVE_EXECUTION_PIPELINE.md`](../WAVE_EXECUTION_PIPELINE.md) — 12-stage execution process, pipeline invariants, no skipping
> 3. Read [`/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/SK_EFT_Hawking_Inventory_Index.md`](../../SK_EFT_Hawking_Inventory_Index.md) — module map, Lean map, current counts

---

## Execution Process

**All Phase 6 work follows the [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md).** 12 stages in strict order.

---

## 1. HPC-Dependent Items

### 6A. Vestigial MC Production at Scale (L=12-20)

**Trigger:** Phase 5 Wave 7C confirms vestigial phase at L=4-8 via HS+RHMC.

**What:** Scale HS+RHMC to L=12-20 for precision finite-size scaling. Extract critical exponents. Continuum-limit extrapolation. Compare with analytical G_ves prediction from Wave 6.

**Status update (2026-04-02):** The algorithm is HS+RHMC (not fermion-bag — fermion-bag hits O(V⁴) percolation wall). The fermion matrix A[h,U] is **physically sparse** (nearest-neighbor, 0.2% fill at L=8). Two implementation paths:

**Path A: Sparse CG on Apple Silicon (workstation, no HPC)**
- Implement sparse matrix builder + sparse CG in PyTorch torch backend
- Fermion matrix A has ~256 nonzeros per row (4 directions × 8×8 blocks)
- Sparse CG reads 2600× less data than dense at L=12 → feasible on 128GB machine
- Projected: L=12 in ~1-3 days, L=16 in ~5 days, L=20 in ~4-11 days
- Bottleneck: Python loop overhead in CG (~1ms per iteration dispatch)
- This path is Phase 5 scope (next session) — NOT deferred to Phase 6

**Path B: Custom Metal matrix-free CG (Apple Silicon GPU acceleration)**
- Matrix-free: compute A@v on-the-fly from h-field using stencil operation, never store A
- Encode entire CG iteration body into single MTLCommandBuffer (eliminates 100-350μs dispatch overhead)
- Uses PyObjC `Metal` framework to write Metal compute shaders called from Python
- Stencil computation has higher arithmetic intensity (~0.8 FLOP/byte) than sparse matvec (0.17)
- Would bring genuine GPU benefit: Apple GPU has 2-6× compute advantage for stencil ops
- Estimated development: 2-4 weeks. Speedup: potentially 3-10× over sparse CPU CG
- This is the "HPC-equivalent" path for Apple Silicon — avoids need for external cluster

**Path C: External HPC (NVIDIA CUDA)**
- Traditional approach: port to CUDA, use QUDA or Grid lattice QCD libraries
- Advantages: mature ecosystem, float64 hardware, HBM bandwidth (3.35 TB/s on H100 vs 273 GB/s)
- ~100K core-hours ALCC allocation for L=12-20 production
- Only necessary if Path A/B insufficient for publication precision

**Recommendation:** Path A first (sparse CG, ~1 session), Path B if throughput insufficient, Path C only for L≥20 or extreme precision.

**Deep research:**
- `Lit-Search/Phase-5/5W7C/GPU-accelerated CG on Apple Silicon.md` — GPU vs CPU analysis, Metal kernel roadmap
- `Lit-Search/Phase-5/5W7C/JAX on Apple Silicon- closing the 2.7× gap with PyTorch for RHMC.md` — JAX vs PyTorch analysis
- `Lit-Search/Phase-5/Hybrid fermion-bag + gauge-link Monte Carlo for ADW tetrad condensation.md` — original scoping

**Key Phase 5 findings informing this:**
- HS+RHMC replaces fermion-bag (O(V·√κ) vs O(V⁴)). Sign-problem-free via Kramers.
- GPU acceleration is a dead end on Apple Silicon for Python-framework iterative solvers (unified memory, kernel launch overhead). Custom Metal is the GPU path.
- PyTorch CPU with Accelerate BLAS (AMX) is the best Python framework. JAX routes matmul through Eigen/NEON bypassing AMX.
- Sparse matrix storage is the critical unlock: 2600× less memory/bandwidth at L=12.

**Production projections (128 GB Apple Silicon, sparse CG once implemented):**

| L | s/traj | 24K traj | Path |
|---|--------|----------|------|
| 12 | ~3-10s | 1-3 days | A (sparse CG) |
| 14 | ~5-15s | 1-4 days | A |
| 16 | ~7-30s | 2-8 days | A or B |
| 18 | ~10-40s | 3-11 days | B recommended |
| 20 | ~15-60s | 4-17 days | B or C |

---

### 6B. Walker-Wang Z₂ Transport Program (Strategy A)

**Trigger:** HPC access.

**What:** First computation of any transport coefficient (eta/s) for any emergent gauge theory. 3D toric code (Z₂ Walker-Wang) via ParaToric QMC + T^{mu nu} correlator construction. Tests Svetitsky-Yaffe universality at transport level.

**Resources:** ~500K GPU-hours over 3 years. ALCC-scale allocation (64-128 A100/H100 for 18 months). 2-3 FTE code development.
**Scoping:** `Lit-Search/Phase-5/Walker-Wang finite-temperature eta-s simulation.md`

---

### ~~6C. 4D ATRG for Vestigial Gravity~~ → MOVED TO PHASE 5 WAVE 8

**Status:** Moved to Phase 5 (Section 12, Wave 8) on 2026-04-01. Reassessment: D=8-12 workstation-tractable (128MB-3.4GB per tensor), O(D⁹) at D=12 for L=4 is ~1.5h. Reference implementations exist. The "9-14 month" estimate was academic pace — our pipeline compresses to ~6 weeks. Only D=16+ scale-up would return to Phase 6.

---

### 6D. Walker-Wang TRG for Non-Abelian (Strategy B)

**Trigger:** Strategy A (6B) successful + INCITE-scale allocation.

**What:** Tensor renormalization group for SU(2)_k Walker-Wang. Targets thermodynamic observables (critical exponents) rather than transport. Sign-problem-free but computationally demanding.

**Resources:** 2-5M GPU-hours. INCITE-scale.

---

## 2. Collaboration-Dependent Items

### 6E. BEC Experimental Engagement

**Platforms (ranked by EFT testing capability):**
1. **Trento spin-sonic** (Carusotto-Ferrari) — Best for EFT testing. Two-branch dispersion control. ERC funded (QFIELBS, 2026). Timeline: 2028-31.
2. **Paris polaritons** (Bramati-Jacquet) — Most active. Stimulated Hawking possible 2026-27. Driven-dissipative corrections complicate comparison.
3. **Heidelberg K-39** (Oberthaler) — Best apparatus for kappa-scaling test (Feshbach + DMD). Not currently pursuing Hawking. Would need redirection.

**Action:** Share prediction tables, kappa-scaling analysis, polariton Tier 1 predictions. QSimFP consortium and JILA Heising-Simons provide funding frameworks.

---

### 6F. Polariton Tier 2-3 EFT Predictions

**Trigger:** Polariton stimulated Hawking observed + Tier 1 predictions validated.

**What:** Full non-equilibrium SK-EFT with complex coupling constants (SBD framework). Independent noise vertex. Requires rewriting scattering theory, not just patching. Needed when Gamma_pol/kappa ~ O(1).

**Scoping:** `Lit-Search/Phase-5/Extending Schwinger-Keldysh EFT to driven-dissipative polariton condensates.md`

---

## 3. Trigger-Dependent Items (from Phase 5 conditional)

| Item | Trigger | Status |
|------|---------|--------|
| Emergent gravity UV completion (5A) | TPF gapped interface proven | `conditional` — chirality wall cracking |
| BEC replication response (5D) | Independent Hawking measurement | `blocked` — earliest ~2026-27 (Paris stimulated) |
| Wallstrom resolution (5C) | Distributional breakthrough | `blocked` — Reddiger pivoted |

---

*Phase 6 roadmap. Items requiring resources beyond the LLM + Lean + Aristotle pipeline (HPC, collaboration, or multi-month development). 6A: HS+RHMC production at L=12-20 — THREE PATHS: (A) sparse CG on Apple Silicon (days per L, Phase 5 scope), (B) custom Metal matrix-free CG (3-10× over sparse, 2-4 weeks dev), (C) external HPC/CUDA (only for L≥20). 6B: Walker-Wang Z₂ transport. Former 6C (4D ATRG) MOVED to Phase 5 Wave 8. Updated 2026-04-02.*
