# Aristotle Batch Submission Plan

## Overview

33 sorry gaps across 11 modules, organized into 4 priority batches.
(4 sorry are private relation-respect proofs + 1 public S² theorem in Uqsl3Hopf;
4 defs carry transitive sorry and auto-resolve when the theorems are proved.)
Submit sequentially — one batch at a time, wait for completion before next.

**Rule:** Never submit overlapping jobs. Each batch sends the entire Lean project.
**Rule:** Manual review of ALL results before integration. No blind `--integrate`.

**Updated:** April 6, 2026. Batch 2 IN FLIGHT. Uqsl3.lean (21 relations) ZERO sorry.
Uqsl3Hopf.lean adds 4 new sorry (relation-respect + S²). Project builds clean.

## Current Status

| Batch | Priority | Sorry | Modules | Status |
|-------|----------|-------|---------|--------|
| 1 | P1 | ~~8~~ 0 | ~~SU2kMTC (5), FibonacciMTC (3)~~ | **DONE** (native_decide) |
| 2 | P1 | 7 | Uqsl2AffineHopf (3), CoidealEmbedding (4) | **IN FLIGHT** (91434dbd) |
| 3 | P2 | 17 | StimulatedHawking (7), VerifiedStatistics (4), RepUqFusion (2), Uqsl3Hopf (4) | Ready — submit after Batch 2 |
| 4 | P3 | 8 | CenterFunctor (5), KerrSchild (1), EmergentGravityBounds (2), TetradGapEquation (1) | Ready — submit after Batch 3 |

## Batch Details

### Batch 1 — COMPLETED
Pentagon equations and F-symbol verification for Ising and Fibonacci MTCs.
Resolved manually: convention mismatch identified via brute-force search over
Q(√2)/Q(√5), corrected F-symbol admissibility conditions, pentagon proved
by native_decide. Zero sorry remaining in SU2kMTC and FibonacciMTC.

### Batch 2 (Priority 1) — Affine Quantum Group
**Submit now.** Unblocks Phase 5e Track C (full affine HopfAlgebra instance).

| Module | Sorry | Key Theorems | Difficulty |
|--------|-------|-------------|------------|
| Uqsl2AffineHopf | 3 | affComul/Counit/Antipode_respects_rel | HARD (Serre coproduct) |
| CoidealEmbedding | 4 | coideal_B0/B1, counit_B0/B1 | MODERATE (tensor product expansion) |

**PROVIDED SOLUTION hints are in each sorry stub.** Key strategies:
- Coproduct: 4-phase tactic (same as Uqsl2Hopf which Aristotle proved in run 79e07d55)
- Counit: trivial (all E/F map to 0)
- Coideal: expand B_i = F_i + E_iK_i^{-1}, apply linearity of Δ
- **No heartbeat overrides needed** — project builds clean at default limits

**Submission prompt:**
```
Fill the sorry gaps in Uqsl2AffineHopf.lean and CoidealEmbedding.lean.

For Uqsl2AffineHopf.lean:
- affComulFreeAlg_respects_rel: Factor into per-relation cases. Use the same
  4-phase simp/rewrite strategy that worked for Uqsl2Hopf (already proved in
  this project). KK⁻¹ and KE/KF cases are mechanical. Counit is trivial
  (all generators map to 0 or 1). Serre cases expand via coproduct linearity.
  See PROVIDED SOLUTION hints in each theorem docstring.

For CoidealEmbedding.lean:
- coideal_B0/B1: Expand B_i = F_i + E_i·K_i⁻¹, apply Δ by linearity,
  use K_i·K_i⁻¹ = 1 to simplify. See PROVIDED SOLUTION for step-by-step.
- counit_B0/B1: Apply ε by linearity. ε(E_i) = ε(F_i) = 0, ε(K_i) = 1.

Do NOT add set_option maxHeartbeats or synthInstance.maxHeartbeats overrides.
The project builds clean at default limits.
```

### Batch 3 (Priority 2) — Paper Verification + Uqsl3 Hopf
**Submit when:** Batch 2 completes
**Why P2:** Completes Lean backing for Papers 11, 12, MC analysis, and rank-2 quantum group

| Module | Sorry | Key Theorems | Difficulty |
|--------|-------|-------------|------------|
| StimulatedHawking | 7 | BE monotonicity, limits, sqrt scaling, dispersive bound, detection threshold | MODERATE (real analysis) |
| VerifiedStatistics | 4 | Cauchy-Schwarz, jackknife mean-case, ρ≤1, N_eff≤N | MODERATE (finite sums) |
| RepUqFusion | 2 | fusion commutativity, Peter-Weyl sum of squares | EASY (Nat arithmetic) |
| Uqsl3Hopf | 4 | comul/counit/antipode_respects_rel, S²=Ad(K₁K₂) | HARD (Serre Δ: 24 terms) |

### Batch 4 (Priority 3) — Hard / Less Urgent
**Submit when:** Batch 3 completes

| Module | Sorry | Key Theorems | Difficulty |
|--------|-------|-------------|------------|
| CenterFunctor | 5 | functor_exists, faithful, full, essSurj, equivalence | VERY HARD (categorical) |
| KerrSchild | 1 | ks_inverse_formula (Sherman-Morrison 4×4) | MODERATE |
| EmergentGravityBounds | 2 | coupling_deficit, coupling_ratio_small (need π bounds) | EASY |
| TetradGapEquation | 1 | gap_solution_bounded (corrected, with coupling bound) | MODERATE |

## Submission Commands

```bash
# Check current Aristotle status:
source .env && export ARISTOTLE_API_KEY && uv run aristotle list --limit 5

# Submit Batch 2 (from SK_EFT_Hawking/lean/):
cd lean
source ../.env && export ARISTOTLE_API_KEY
uv run aristotle submit "[prompt text]" --project-dir .

# Retrieve results:
uv run python scripts/submit_to_aristotle.py --retrieve <UUID>

# Integrate (after review):
uv run python scripts/submit_to_aristotle.py --retrieve <UUID> --integrate
```
