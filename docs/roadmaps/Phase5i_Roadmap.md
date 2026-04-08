# Phase 5i: Higher-Rank Quantum Groups — U_q(sl_3) + Color Group

## Technical Roadmap — April 2026

*Prepared 2026-04-06 | Updated 2026-04-08 | Follows successful U_q(sl_2) formalization (66 thms, 0 sorry)*

**Entry state:** 2232 theorems (2150 substantive + 82 placeholder), 1 axiom, 94 modules, **17 sorry** project-wide (Uqsl2AffineHopf **12**, Uqsl3Hopf 3, CenterFunctor 2). 4 KE/KF antipode cases proved manually this session (K₁E₀, K₀F₀, K₁F₁, K₁F₀). Aristotle 6dbc9447 submitted with all 17 sorry + RingQuot workaround hints. **W1 COMPLETE** (0 sorry). **W2 Stage 3** (3 sorry — counit proved; comul_respect + antipode_respect + S² remain; RingQuot typeclass divergence blocks). **W3 COMPLETE** (0 sorry). **W4 partial** (PolyQuotQ.lean, 15 thms, 0 sorry). W4 remainder BLOCKS Mathlib PR (Phase 5g Track B).

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

### Wave 1 — Chevalley Relations and Definition — **COMPLETE**
**Goal:** U_q(sl_3) via FreeAlgebra/RingQuot (same pattern as sl_2).

- [x] 8 generators: E₁, E₂, F₁, F₂, K₁, K₁⁻¹, K₂, K₂⁻¹
- [x] Cartan matrix A = [[2,-1],[-1,2]]
- [x] 21 Chevalley relations: K-invertibility (4), K-commutativity (1), KE/KF conjugation (8), EF commutation (4), quantum Serre (4)
- [x] ALL 21 relation theorems PROVED (zero sorry, zero axioms)
- [x] K₁, K₂ invertible (unit instances)
- [x] Quantum Serre proved via `simp [map_mul, map_add, AlgHom.commutes] at h ⊢`
- [x] `lean/SKEFTHawking/Uqsl3.lean` — first rank-2 quantum group in any proof assistant
- [x] Builds in 6.4s at default heartbeat limits

### Wave 2 — Hopf Algebra Structure — **Stage 3 COMPLETE** (3 sorry remain)
**Goal:** Bialgebra + HopfAlgebra instances (reuse architecture from Uqsl2Hopf).

- [x] Coproduct Δ defined on 8 generators via FreeAlgebra.lift + RingQuot.liftAlgHom
- [x] Counit ε defined and descended to quotient
- [x] Antipode S defined as anti-homomorphism via MulOpposite
- [x] S² = Ad(K₁K₂) stated
- [x] `lean/SKEFTHawking/Uqsl3Hopf.lean` — builds in 5.6s
- [x] Counit respect proof PROVED (both manually and Aristotle; counit now 0 sorry)
- [ ] 3 sorry remain: Δ-respect (comul_respect), S-respect (antipode_respect), S² proof — blocked by RingQuot typeclass divergence. Aristotle 6dbc9447 submitted with workaround hints (letI, erw, op_mul, Algebra.smul_def)
- [ ] Bialgebra + HopfAlgebra typeclass wiring (after relation-respect proofs filled)

### Wave 3 — SU(3)_k Fusion Rules — **COMPLETE**
**Goal:** Fusion rules at roots of unity via native_decide.

- [x] `lean/SKEFTHawking/SU3kFusion.lean` — first SU(3)_k fusion in any proof assistant
- [x] SU(3)_1: Z₃ fusion ring, 3 objects, commutativity + associativity PROVED
- [x] SU(3)_2: 6 anyons, Fibonacci subcategory (τ⊗τ = 1+τ)
- [x] SU(3)_2: commutativity + associativity PROVED by native_decide
- [x] Charge conjugation involution PROVED for both levels
- [x] Z₃ simple current group {vac, s, s̄} PROVED
- [x] ALL verified by native_decide — zero sorry, zero axioms
- [x] Builds in 3.8s
- [ ] Restricted quantum group ū_q(sl_3) (deferred — not needed for fusion verification)
- [ ] S-matrix verification (requires Q(ζ₃) and Q(ζ₁₅) — Wave 4 blocker)

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

*Phase 5i roadmap. Updated 2026-04-08 (W1 COMPLETE: Uqsl3.lean, 21 relations, 0 sorry. W2 Stage 3: Uqsl3Hopf.lean, Δ/ε/S defined, 3 sorry — counit proved (manually + Aristotle), comul_respect + antipode_respect + S² remain; RingQuot typeclass divergence blocks. Aristotle 6dbc9447 submitted with all 17 sorry + workaround hints. W3 COMPLETE: SU3kFusion.lean, SU(3)₁+SU(3)₂ fusion, 99 thms, 0 sorry. W4 partial: PolyQuotQ.lean, 15 thms, 0 sorry; generic CyclotomicField remainder BLOCKS Mathlib PR). 2232 theorems, 94 modules, 17 sorry total project-wide (Uqsl2AffineHopf 12, Uqsl3Hopf 3, CenterFunctor 2), 1 axiom. First rank-2 quantum group + first SU(3)_k fusion in any proof assistant.*
