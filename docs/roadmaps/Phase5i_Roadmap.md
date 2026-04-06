# Phase 5i: Higher-Rank Quantum Groups — U_q(sl_3) + Color Group

## Technical Roadmap — April 2026

*Prepared 2026-04-06 | Follows successful U_q(sl_2) formalization (66 thms, 0 sorry)*

**Entry state:** 2023 theorems (1949 substantive + 74 placeholder), 1 axiom, 88 modules, 28 sorry. W1-4: NOT STARTED. W4 (number field consolidation) BLOCKS Mathlib PR (Phase 5g Track B).

---

## 0. Motivation

U_q(sl_2) is complete: definition, Hopf algebra, affine extension, restricted quotient, fusion rules, S-matrices, braided MTCs, knot invariants. The natural extension is U_q(sl_3) — the quantum group of the color gauge group SU(3). This connects to:
- Color confinement (SU(3) Chern-Simons)
- Non-Abelian gauge emergence (the gauge wall)
- Higher-rank fusion categories

**Deep research COMPLETE:** `Lit-Search/Phase-5j/U_q(sl_3) complete technical specification for Lean 4 formalization.md` (note: filed under Phase-5j/ due to submission timing)

**KEY FINDINGS from deep research:**
1. Scale: 8 generators, 21 relations (vs 4/5 for sl₂). ~140 proof obligations for Hopf.
2. 4 cubic Serre relations are the bottleneck (24 terms each in tensor product)
3. SU(3)₁: 3 simple objects (Z₃ cyclic), S-matrix in Q(ζ₃)
4. SU(3)₂: 6 objects with golden-ratio dimensions, τ⊗τ = 1+τ (FIBONACCI fusion!)
5. SU(3)₂ S-matrix requires Q(ζ₁₅) (degree 8 over ℚ)
6. All fusion multiplicities are 0 or 1 — native_decide feasible
7. No existing U_q(sl_N) formalization in ANY proof assistant for N>2
8. Hybrid file structure recommended: ~5000 lines for Hopf core, ~10000 with MTC

---

## Track A: U_q(sl_3) Definition + Hopf Structure

### Wave 1 — Chevalley Relations and Definition
**Goal:** U_q(sl_3) via FreeAlgebra/RingQuot (same pattern as sl_2).

- [ ] 8 generators: E₁, E₂, F₁, F₂, K₁, K₁⁻¹, K₂, K₂⁻¹
- [ ] Cartan matrix A = [[2,-1],[-1,2]]
- [ ] Relations: K-invertibility, KE/KF commutation, EF commutation, Serre (degree 3)
- [ ] `lean/SKEFTHawking/Uqsl3.lean`

### Wave 2 — Hopf Algebra Structure
**Goal:** Bialgebra + HopfAlgebra instances (reuse architecture from Uqsl2Hopf).

- [ ] Coproduct, counit, antipode on 8 generators
- [ ] Relation-respect proofs (factored per-relation, Aristotle targets)
- [ ] Bialgebra + HopfAlgebra typeclasses

### Wave 3 — SU(3)_k Fusion Rules
**Goal:** Fusion rules at roots of unity via native_decide.

- [ ] Restricted quantum group ū_q(sl_3)
- [ ] SU(3)_1 and SU(3)_2 fusion rules
- [ ] Verify by native_decide (need appropriate number field)

### Wave 4 — Unified Algebraic Number Field Infrastructure
**Goal:** Consolidate custom number fields into a generic framework.

**Context:** The project currently has 6 hand-written number field types (QSqrt2, QSqrt3, QSqrt5, QCyc5, QCyc16, QLevel3), each with manually defined arithmetic and DecidableEq. SU(3)₂ requires Q(ζ₁₅) (degree 8 over ℚ). This pattern does not scale.

**Deliverables:**
- [ ] Generic `CyclotomicField n` or `AdjoinRoot` type with DecidableEq
- [ ] Refactor existing types as instances of the generic construction
- [ ] Q(ζ₁₅) for SU(3)₂ S-matrix verification
- [ ] **BLOCKS**: Mathlib PR for categorical infrastructure (Phase 5g Track B)
  - Mathlib reviewers will reject 6 hand-written number types
  - Generic construction is prerequisite for upstreaming

---

## Deep Research

| # | Topic | File | Status |
|---|-------|------|--------|
| 1 | U_q(sl_3) relations + fusion data | Lit-Search/Phase-5j/U_q(sl_3) complete technical specification for Lean 4 formalization.md | **COMPLETE** (filed under Phase-5j/ due to submission timing) |

---

*Phase 5i roadmap. Updated 2026-04-06 (W1-4 NOT STARTED. Deep research COMPLETE. W4 number field consolidation BLOCKS Mathlib PR). 2023 theorems, 88 modules, 28 sorry, 1 axiom. Extends the quantum group chain to the color gauge group. Same proven architecture (FreeAlgebra/RingQuot/liftAlgHom), higher rank.*
