# Phase 5q: Ext Computation over A(1) — The Algebraic Core of Spin Bordism

## Technical Roadmap — April 2026

*Prepared 2026-04-08 | Updated 2026-04-08 (deep research complete — resolution data extracted, brute-force approach confirmed) | Follows Phase 5p (Muger center, FP dimension). Addresses the deepest open hypothesis in the generation constraint chain.*

**Entry state:** 124 Lean modules, ~21 sorry (RingQuot blocker), 1 axiom (gapped_interface_axiom). The spin bordism isomorphism Omega^Spin_4 = Z enters as a HYPOTHESIS in SpinBordism.lean. The A(1) Steenrod algebra is formalized (SteenrodA1.lean, 17 theorems, zero sorry). The generation constraint N_f = 0 mod 3 is proved with zero axioms, conditional on 24 | 8N_f.

**Goal:** Machine-check the algebraic core of the spin bordism computation: build the explicit minimal free resolution of F_2 over A(1) through degree 5 and compute the Ext groups Ext^n_{A(1)}(F_2, F_2) for n = 0..5 as F_2-vector spaces. Then decompose the single opaque spin bordism hypothesis into 4 minimal, independently verifiable topological hypotheses.

**Why this matters:** The generation constraint traces through Rokhlin -> modular invariance -> 3 | N_f. Rokhlin is currently a single opaque hypothesis. The Ext computation machine-checks all the ALGEBRA underneath it (the resolution, exactness, dimensions) and isolates the genuinely TOPOLOGICAL content into clean, minimal hypotheses. This transforms the generation constraint from "proved modulo one opaque topological claim" to "proved with machine-checked algebra plus 4 specific, textbook-verifiable topological inputs."

**Sorry impact: ZERO new sorry. ZERO new axioms.** The Tier 1 computation is entirely native_decide on F_2 matrices. The hypothesis decomposition replaces 1 opaque hypothesis with 4 focused hypotheses — a strictly better epistemic position.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
> 1. Read CLAUDE.md, WAVE_EXECUTION_PIPELINE.md, Inventory Index
> 2. Read this roadmap for wave assignments
> 3. Read deep research results:
>    - `Lit-Search/Phase-5q/The minimal free resolution of F₂ over A(1) and its formalization.md`
>    - `Lit-Search/Phase-5q/Mathlib4 homological algebra- a practical infrastructure audit.md`
> 4. Read Aristotle reference: `docs/references/Theorm_Proving_Aristotle_Lean.md`
> 5. Read existing: SteenrodA1.lean, SpinBordism.lean, AlgebraicRokhlin.lean, E8Lattice.lean

---

## Deep Research Findings (Complete)

### Key correction: Ext^4 is F_2^3, not Z/16

The additive structure of Ext^4_{A(1)}(F_2, F_2) is **F_2^3** (3-dimensional, 8 elements), with basis {h_0^4, h_0*v, w_1}. The number 16 enters through the infinite h_0-tower in stem 4 assembling to Z_2 (2-adic integers) via Adams spectral sequence extensions — NOT through Ext^4 being Z/16 as a group. No cup product computation is needed for our goal.

The full Ext algebra is: F_2[h_0, h_1, v, w_1] / (h_0*h_1, h_1^3, h_1*v, v^2 + h_0^2*w_1)

### Brute-force approach confirmed

Both deep research reports agree: Mathlib's entire homology pipeline is `noncomputable`. No concrete Ext computation has ever been done in Lean 4. The brute-force matrix approach with native_decide is the ONLY viable path. It is also very tractable — the largest matrix is 24x32 over F_2.

### Resolution data extracted

The minimal free resolution through degree 5 has explicit generator counts and differential matrices. The differentials have an elegant bidiagonal structure: Sq^1 on the diagonal, Sq(2,1) on the superdiagonal, with periodic structure driven by w_1. All d^2 = 0 verifications have been checked by hand. SageMath (SteenrodFPModule with profile=(2,1)) can independently generate and verify all matrices.

### Exactness verification strategy

The deep research recommends the **RREF witness approach**: compute reduced row echelon form externally (SageMath), provide transformation matrices P, P^{-1} as Lean literals, verify P*d = RREF and P*P^{-1} = I via native_decide, read off ranks from RREF. This avoids the noncomputable `Matrix.rank`.

---

## Track A: The Free Resolution and Ext Computation

### Wave 1 — Deep Research [COMPLETE]

**Deliverables:**
- [x] `Lit-Search/Phase-5q/The minimal free resolution of F₂ over A(1) and its formalization.md`
- [x] `Lit-Search/Phase-5q/Mathlib4 homological algebra- a practical infrastructure audit.md`

**Decision: Brute-force matrix approach.** All computation via `Matrix (Fin m) (Fin n) (ZMod 2)` with native_decide. No Mathlib abstract homological algebra.

**Status: COMPLETE.**

---

### Wave 2 — A(1) Ring Instance + SageMath Cross-Validation [Pipeline: Stages 1-3]

**Goal:** (a) Upgrade A(1) from a lookup table to a proper Lean Ring, and (b) generate all resolution matrices from SageMath for cross-validation.

**2A. A(1) Ring instance:**
- [ ] Define `A1` as a newtype wrapper around `Fin 8 -> ZMod 2` (avoids Pi.instMul typeclass diamond — same pattern as DrinfeldDoubleRing.lean's DG wrapper)
- [ ] Define convolution multiplication from the existing `a1_mul` table (512 structure constants over F_2)
- [ ] Prove Ring axioms: mul_assoc, left_distrib, right_distrib, mul_one, one_mul via native_decide
- [ ] Prove `Algebra (ZMod 2) A1` instance
- [ ] Define the augmentation as a RingHom: `A1 ->+* ZMod 2`

**2B. SageMath matrix generation:**
- [ ] Python script using `SteenrodAlgebra(2, profile=(2,1))` and `SteenrodFPModule`
- [ ] Generate F_2-expanded differential matrices d_1 through d_5 (A(1)-element matrices -> F_2 block matrices)
- [ ] Generate RREF transformation matrices P_n and P_n^{-1} for each differential
- [ ] Cross-validate: verify d^2 = 0 and rank conditions in Python before encoding in Lean
- [ ] Export matrices as Lean literal syntax (`!![a, b; c, d]` format)

**Matrix sizes (from deep research):**

| Differential | A(1)-matrix | F_2-matrix | d^2=0 check size |
|---|---|---|---|
| d_1 | 1x2 | 8x16 | 8x16 (trivial) |
| d_2 | 2x2 | 16x16 | 8x16 |
| d_3 | 2x2 | 16x16 | 16x16 |
| d_4 | 2x3 | 16x24 | 16x24 |
| d_5 | 3x4 | 24x32 | 16x32 |

All trivially within native_decide budget.

**Deliverables:**
- [ ] `lean/SKEFTHawking/A1Ring.lean` — A(1) as a Ring (~10-15 theorems, zero sorry)
- [ ] `scripts/generate_a1_resolution.py` — SageMath matrix generation + Lean export
- [ ] `tests/test_a1_resolution.py` — Python cross-validation of resolution data

**Estimated LOE:** 1 week
**Risk:** Medium (typeclass diamond on function type — mitigated by newtype wrapper pattern).

---

### Wave 3 — Resolution + Exactness in Lean [Pipeline: Stages 1-5]

**Goal:** Encode the resolution in Lean as explicit F_2-matrices and machine-check d^2 = 0 and exactness at every degree.

**Prerequisites:** Wave 2 (A(1) Ring instance + SageMath-generated matrices).

**Resolution structure (from deep research):**

| Module | Rank | Generator degrees | Ext classes |
|--------|------|-------------------|-------------|
| P_0 | 1 | {0} | 1 |
| P_1 | 2 | {1, 2} | h_0, h_1 |
| P_2 | 2 | {2, 4} | h_0^2, h_1^2 |
| P_3 | 2 | {3, 7} | h_0^3, v |
| P_4 | 3 | {4, 8, 12} | h_0^4, h_0*v, w_1 |
| P_5 | 4 | {5, 9, 13, 14} | h_0^5, h_0^2*v, h_0*w_1, h_1*w_1 |

**Differentials (A(1)-element matrices):**

```
d_1 = [ Sq^1   Sq^2 ]

d_2 = | Sq^1    Sq^3    |
      |  0      Sq^2    |

d_3 = | Sq^1    Sq(2,1) |
      |  0      Sq^3    |

d_4 = | Sq^1    Sq(2,1)    0      |
      |  0       Sq^1    Sq(2,1)  |

d_5 = | Sq^1    Sq(2,1)    0        0   |
      |  0       Sq^1    Sq(2,1)    0   |
      |  0        0        Sq^1    Sq^2 |
```

**Verification strategy:**

1. **d^2 = 0:** Define each d_n as `Matrix (Fin m) (Fin n) (ZMod 2)` (F_2-expanded). Prove `d_{n-1} * d_n = 0` via `native_decide`. Five proofs, all trivial.

2. **Exactness via RREF witnesses:** For each d_n:
   - Provide invertible P_n and P_n^{-1} (from SageMath) as Lean matrix literals
   - Prove `P_n * d_n = RREF_n` via `native_decide`
   - Prove `P_n * P_n_inv = 1` via `native_decide`
   - Read off rank(d_n) from RREF (count nonzero rows, verified as a `Nat` literal)
   - Prove exactness: `rank(d_n) + rank(d_{n+1}) = dim(P_n)` via `norm_num`

3. **A(1)-linearity:** For generators Sq^1 and Sq^2, encode left-multiplication as block-diagonal matrices. Prove `d_n * blockDiag(Sq) = blockDiag(Sq) * d_n` via `native_decide`.

**Deliverables:**
- [ ] `lean/SKEFTHawking/A1Resolution.lean` — resolution + chain complex property (~20-30 theorems):
  - Differential matrices d_1 through d_5 as explicit F_2-matrix literals
  - `d_sq_zero_1` through `d_sq_zero_4` — d_{n-1} * d_n = 0 (native_decide)
  - RREF witness matrices P_n, P_n^{-1} as literals
  - `rref_valid_1` through `rref_valid_5` — P_n * d_n = RREF_n (native_decide)
  - `rref_inv_1` through `rref_inv_5` — P_n * P_n^{-1} = I (native_decide)
  - `exact_at_0` through `exact_at_4` — rank(d_n) + rank(d_{n+1}) = dim (norm_num)
  - `a1_linear_sq1_1` through `a1_linear_sq1_5` — Sq^1 linearity (native_decide)
  - `a1_linear_sq2_1` through `a1_linear_sq2_5` — Sq^2 linearity (native_decide)
  - Augmentation exactness

**Estimated LOE:** 1-2 weeks
**Risk:** Low. All computation is finite F_2 matrix arithmetic. native_decide handles everything. The main work is encoding the matrices as Lean literals.

---

### Wave 4 — Ext Dimensions [Pipeline: Stages 1-5]

**Goal:** Apply Hom_{A(1)}(-, F_2) to the resolution and compute Ext^n dimensions as F_2-vector spaces.

**Prerequisites:** Wave 3 (verified resolution).

**The computation:**
1. For a free A(1)-module P_n of rank r_n: Hom_{A(1)}(P_n, F_2) = F_2^{r_n} (free modules, Hom determined by generator images)
2. The coboundary delta^n : F_2^{r_n} -> F_2^{r_{n+1}} is the transpose of the A(1)-element differential d_{n+1} restricted to the augmentation component
3. For minimal resolutions: ALL coboundaries are zero (differentials map into the augmentation ideal, so applying Hom(-, F_2) annihilates them)
4. Therefore: **Ext^n = Hom_{A(1)}(P_n, F_2) = F_2^{r_n}** directly

This is the key simplification from minimality: dim(Ext^n) = rank(P_n). No kernel/image computation needed for the Ext DIMENSIONS. The resolution ranks directly give:

| n | rank(P_n) | dim(Ext^n) | Basis |
|---|-----------|-----------|-------|
| 0 | 1 | 1 | {1} |
| 1 | 2 | 2 | {h_0, h_1} |
| 2 | 2 | 2 | {h_0^2, h_1^2} |
| 3 | 2 | 2 | {h_0^3, v} |
| 4 | 3 | 3 | {h_0^4, h_0*v, w_1} |
| 5 | 4 | 4 | {h_0^5, h_0^2*v, h_0*w_1, h_1*w_1} |

**Proving minimality:** A resolution is minimal iff all differentials map into I*P_{n-1} where I = ker(epsilon) is the augmentation ideal. Equivalently: applying the augmentation to each column of d_n gives zero. This is a finite F_2 check — apply the augmentation map (project onto the "1" basis component of A(1)) to each differential matrix column.

**Deliverables:**
- [ ] `lean/SKEFTHawking/A1Ext.lean` — Ext computation (~15-20 theorems):
  - `resolution_minimal` — differentials map into augmentation ideal (native_decide)
  - `ext_dim_0` through `ext_dim_5` — dim(Ext^n) = rank(P_n) (from minimality)
  - `ext_total_dim_4` — dim(Ext^4) = 3 (norm_num)
  - Bridge theorems to SpinBordism.lean: the infinite h_0-tower in stem 4 (v, h_0*v, h_0^2*v, ...) detects Z in pi_4(ko)
  - Bridge to Z16Classification.lean and RokhlinBridge.lean
  - `ext_computation_summary` — master theorem collecting all dimensions

**Estimated LOE:** 3-5 days
**Risk:** Low. Minimality is a finite check. Dimensions follow directly.

---

### Wave 5 — Hypothesis Decomposition [Pipeline: Stages 1-5]

**Goal:** Replace the single opaque hypothesis in SpinBordism.lean with 4 focused, independently verifiable topological hypotheses.

**Prerequisites:** Wave 4 (Ext computation provides the algebraic content to separate).

**The 4 hypotheses (from deep research Q4):**

```lean
-- H1: ko cohomology factors through A(1)
-- "H*(ko; F_2) = A tensor_{A(1)} F_2"
-- Standard result (Stong). Topological — requires spectrum theory.

-- H2: Change-of-rings isomorphism
-- "Ext_A(A tensor_{A(1)} F_2, F_2) = Ext_{A(1)}(F_2, F_2)"
-- ALGEBRAIC — follows from Hom-tensor adjunction. 
-- Potentially provable in Lean (Phase 5r), but initially stated as hypothesis.

-- H3: Adams spectral sequence collapses at E_2 for ko
-- "No differentials in the ASS for ko"
-- Topological — comparison with Bott periodicity.

-- H4: Anderson-Brown-Peterson splitting
-- "pi_n(MSpin) = pi_n(ko) for n < 8"
-- Topological — the ABP splitting theorem (1967).
```

**What this achieves:**
- H1 is a specific fact about one spectrum's cohomology (textbook: Adams Ch. 16)
- H2 is pure algebra (Shapiro's lemma) — potentially dischargeable in Phase 5r
- H3 is comparison with known homotopy groups (textbook: Bott periodicity)  
- H4 is the ABP theorem (original paper: Ann. Math. 86, 1967)
- Each independently verifiable by any topologist

**Chain with hypothesis decomposition:**

```
Ext^n_{A(1)}(F_2, F_2) computed    [MACHINE-CHECKED, native_decide]
      |
      v  (H2: change-of-rings)
Ext^n_A(H*(ko), F_2) = Ext^n_{A(1)}(F_2, F_2)  [HYPOTHESIS, algebraic]
      |
      v  (H1: ko cohomology)
ASS E_2 page for ko computed       [from H1 + H2]
      |
      v  (H3: ASS collapses)
pi_n(ko) determined                [from E_2 collapse]
      |
      v  (H4: ABP splitting)
Omega^Spin_4 = pi_4(ko) = Z       [from ABP in degree 4]
      |
      v  (Rokhlin, already proved conditionally)
16 | sigma                         [from Omega^Spin_4 = Z, K3 has sigma=-16]
      |
      v  (Wang bridge, already machine-checked)
c_- = 8*N_f, 24 | c_- => 3 | N_f [MACHINE-CHECKED, zero axioms]
```

**Deliverables:**
- [ ] Updated `lean/SKEFTHawking/SpinBordism.lean` — 4 structured hypotheses replacing 1 opaque
- [ ] Bridge theorems connecting machine-checked Ext to topological conclusions
- [ ] Updated HYPOTHESIS_REGISTRY in constants.py with eliminability assessments
- [ ] Circularity documentation for each hypothesis

**Estimated LOE:** 1 week
**Risk:** Low. Restructuring existing proofs, not proving new mathematics.

---

### Wave 6 — Pipeline Integration [Pipeline: Stages 6-12]

**Goal:** Tests, figures, paper updates, document sync.

**Prerequisites:** Waves 4-5.

**Deliverables:**
- [ ] `tests/test_a1_ext.py` — Python cross-validation against SageMath
- [ ] `formulas.py` — resolution dimension formulas, Ext dimension formulas
- [ ] Figures: resolution structure diagram, Ext chart (stem vs filtration)
- [ ] Notebook: Phase5q_ExtComputation_Technical.ipynb + _Stakeholder.ipynb
- [ ] Paper 10 update: reference the machine-checked Ext computation
- [ ] RESEARCH_STATUS_OVERVIEW.md update
- [ ] Document sync: Inventory Index, README, counts

**Estimated LOE:** 1 week
**Risk:** Low.

---

## Dependencies

```
Wave 1 (deep research) ──COMPLETE──→ Wave 2 (A(1) Ring + SageMath)
                                          ↓
                                    Wave 3 (resolution + exactness)
                                          ↓
                                    Wave 4 (Ext dimensions)
                                       ↓        ↓
                                 Wave 5       Wave 6
                              (hypotheses)  (pipeline)
```

---

## Timeline

| Wave | Scope | LOE | Dependencies | Status |
|------|-------|-----|-------------|--------|
| Wave 1 | Deep research | 1-2 days | None | **COMPLETE** |
| Wave 2 | A(1) Ring + SageMath matrices | 1 week | Wave 1 | **COMPLETE** (A1Ring.lean, generate_a1_resolution.py) |
| Wave 3 | Resolution + exactness (native_decide) | 1-2 weeks | Wave 2 | **COMPLETE** (A1Resolution.lean, d²=0 all levels) |
| Wave 4 | Ext dimensions (minimality) | 3-5 days | Wave 3 | **COMPLETE** (A1Ext.lean, dims 1,2,2,2,3,4) |
| Wave 5 | Hypothesis decomposition | 1 week | Wave 4 | **COMPLETE** (ExtBordismBridge.lean, 4 hypotheses) |
| Wave 6 | Pipeline integration | 1 week | Wave 4 | **COMPLETE** (26 tests, 2 figures, Paper 10 updated, notebook updated, formulas.py, constants.py, review_figures.py, RESEARCH_STATUS_OVERVIEW, SteenrodA1.lean + RokhlinBridge.lean docstrings corrected) |

**Total actual LOE:** ~4 hours (Waves 2-6 in single session, April 8 2026).
**Original estimate:** 4-6 weeks.

**Critical path:** A(1) Ring instance -> SageMath matrix generation -> Lean encoding -> native_decide verification.

---

## Deep Research

| # | Topic | File | Status |
|---|-------|------|--------|
| 1 | A(1) free resolution + Ext computation | Lit-Search/Phase-5q/The minimal free resolution of F₂ over A(1) and its formalization.md | **COMPLETE** |
| 2 | Mathlib homological algebra assessment | Lit-Search/Phase-5q/Mathlib4 homological algebra- a practical infrastructure audit.md | **COMPLETE** |

---

## What Success Looks Like

**Minimum viable (Tier 1):** The minimal free resolution of F_2 over A(1) through degree 5 is machine-checked: d^2 = 0 at every level, exactness verified via RREF witnesses, A(1)-linearity verified, minimality proved, Ext dimensions computed (1, 2, 2, 2, 3, 4). Zero sorry. Zero axioms. First formalized Ext computation in any proof assistant.

**Stretch (Tier 2):** The opaque spin bordism hypothesis decomposed into 4 focused topological hypotheses. The chain from Ext -> ko homotopy -> MSpin -> Rokhlin -> generation constraint is fully documented with each link's status (machine-checked vs hypothesis).

**Impact on sorry inventory:** Zero new sorry. The hypothesis decomposition replaces 1 opaque hypothesis with 4 focused ones — net improvement in transparency and eliminability tracking.

**Impact on the generation constraint:** N_f = 0 mod 3 backed by machine-checked algebra (Ext computation) plus 4 specific textbook-verifiable topological inputs, each tracked in HYPOTHESIS_REGISTRY with eliminability assessment.

**Novelty:** First formalized Ext computation over any Steenrod subalgebra in any proof assistant. First machine-checked piece of the Adams spectral sequence computation. Unprecedented.

---

*Phase 5q roadmap. Created 2026-04-08. Updated 2026-04-08 (deep research COMPLETE — brute-force approach confirmed, resolution data extracted, key correction: Ext^4 = F_2^3 not Z/16, minimality simplifies Ext dimension computation, RREF witness approach for exactness). All waves follow [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md).*
