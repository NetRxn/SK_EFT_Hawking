# Aristotle Batch Submission Plan

## Overview

36 sorry gaps across 10 modules, organized into 4 priority batches.
Submit sequentially — one batch at a time, wait for completion before next.

**Rule:** Never submit overlapping jobs. Each batch sends the entire Lean project.

## Current Status

| Batch | Priority | Sorry | Modules | Status |
|-------|----------|-------|---------|--------|
| 1 | P1 | 8 | SU2kMTC (5), FibonacciMTC (3) | **IN FLIGHT** (3b356975, 20%) |
| 2 | P1 | 7 | Uqsl2AffineHopf (3), CoidealEmbedding (4) | Ready — submit after Batch 1 |
| 3 | P2 | 13 | StimulatedHawking (7), VerifiedStatistics (4), RepUqFusion (2) | Ready — submit after Batch 2 |
| 4 | P3 | 8 | CenterFunctor (5), KerrSchild (1), EmergentGravityBounds (2) | Ready — submit after Batch 3 |

## Batch Details

### Batch 1 (IN FLIGHT) — MTC Instances
**Aristotle job:** 3b356975 (submitted ~18h ago, 20% progress)
**Content:** Pentagon equations, F-symbol involutory, twist factors, global dimension

| Module | Sorry | Key Theorems |
|--------|-------|-------------|
| SU2kMTC | 5 | isingF_involutory (×2), ising_pentagon, ising_twist_unitary, ising_twist_psi |
| FibonacciMTC | 3 | fib_pentagon_all_tau, fib_global_dim, fib_dim_consistency |

**What it unblocks:** Complete fusion category instances (F-symbols verified). Phase 5d Wave 4 completion.

### Batch 2 (Priority 1) — Affine Quantum Group
**Submit when:** Batch 1 completes (or fails and is retrieved)
**Why P1:** Unblocks Phase 5e Track C (full affine HopfAlgebra instance)

| Module | Sorry | Key Theorems | Difficulty |
|--------|-------|-------------|------------|
| Uqsl2AffineHopf | 3 | affComul/Counit/Antipode_respects_rel | HARD (Serre coproduct = 64 terms) |
| CoidealEmbedding | 4 | coideal_B0/B1, counit_B0/B1 | MODERATE (tensor product expansion) |

**Strategy hints in sorry stubs:** Per-relation factoring, 4-phase tactic, maxHeartbeats 800000 for Serre.
**Deep research available:** Phase-5e/U_q(ŝl₂) Hopf algebra proof strategy.

**Prompt for submission:**
```
Fill the sorry gaps in Uqsl2AffineHopf.lean and CoidealEmbedding.lean.
For Uqsl2AffineHopf: factor into per-relation lemmas. The counit proof is
trivial (all E/F map to 0). The coproduct Serre relation expands to 64
tensor terms — use the 4-phase strategy from the PROVIDED SOLUTION hints.
For CoidealEmbedding: expand B_i = F_i + E_iK_i^{-1}, apply linearity of Δ.
Priority: --priority 1
```

### Batch 3 (Priority 2) — Paper Verification
**Submit when:** Batch 2 completes
**Why P2:** Completes Lean backing for Papers 11, 12 and the MC analysis pipeline

| Module | Sorry | Key Theorems | Difficulty |
|--------|-------|-------------|------------|
| StimulatedHawking | 7 | BE monotonicity, limits, sqrt scaling, dispersive bound, detection threshold | MODERATE (real analysis) |
| VerifiedStatistics | 4 | Cauchy-Schwarz, jackknife mean-case, ρ≤1, N_eff≤N | MODERATE (finite sums) |
| RepUqFusion | 2 | fusion commutativity, Peter-Weyl sum of squares | EASY (Nat arithmetic) |

**Prompt for submission:**
```
Fill sorry gaps in StimulatedHawking.lean, VerifiedStatistics.lean, and
RepUqFusion.lean. These are real analysis and finite arithmetic proofs.
See PROVIDED SOLUTION hints in each theorem docstring.
Priority: --priority 2
```

### Batch 4 (Priority 3) — Hard / Less Urgent
**Submit when:** Batch 3 completes
**Why P3:** CenterFunctor is heavy categorical plumbing, others are niche

| Module | Sorry | Key Theorems | Difficulty |
|--------|-------|-------------|------------|
| CenterFunctor | 5 | functor_exists, faithful, full, essSurj, equivalence | VERY HARD (categorical) |
| KerrSchild | 1 | ks_inverse_formula (Sherman-Morrison 4×4) | MODERATE |
| EmergentGravityBounds | 2 | coupling_deficit, coupling_ratio_small (need π bounds) | EASY |

**Prompt for submission:**
```
Fill sorry gaps in CenterFunctor.lean, KerrSchild.lean, and
EmergentGravityBounds.lean. CenterFunctor uses Path B
(ofFullyFaithfullyEssSurj) — see deep research hints.
KerrSchild: Sherman-Morrison for null vector. EmergentGravityBounds:
need Real.pi_gt_three for π > 3.
Priority: --priority 3
```

## Submission Commands

```bash
# Check current Aristotle status:
source .env && export ARISTOTLE_API_KEY && uv run aristotle list --limit 5

# Submit a batch (from SK_EFT_Hawking/lean/):
cd lean
source ../.env && export ARISTOTLE_API_KEY
uv run aristotle submit "Fill sorry gaps: [batch description]" \
  --project-dir . --priority [1|2|3]

# Retrieve results:
uv run python scripts/submit_to_aristotle.py --retrieve <UUID>

# Integrate (after review):
uv run python scripts/submit_to_aristotle.py --retrieve <UUID> --integrate
```

## Dependency Graph

```
Batch 1 (MTC instances)
    ↓ completes fusion categories
Batch 2 (Affine Hopf + Coideal)
    ↓ unblocks Phase 5e Track C
Batch 3 (Paper verification)
    ↓ completes Papers 11, 12 Lean backing
Batch 4 (Hard / less urgent)
    ↓ completes CenterFunctor equivalence
```

Batches 2-4 are submitted sequentially but are NOT dependency-ordered
(they're independent modules). The sequencing is by priority: submit
the most impactful batch first so it starts processing while lower-priority
batches wait.

## Monitoring

After each submission, monitor with:
```bash
source .env && export ARISTOTLE_API_KEY && uv run aristotle list --limit 5
```

Expected turnaround: 4-24 hours per batch depending on difficulty.
Batch 2 (Serre coproduct) will likely take the longest.
