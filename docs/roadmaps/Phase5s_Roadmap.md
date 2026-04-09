# Phase 5s: Obstacle Decomposition — Attacking "Impossible" Targets

## Technical Roadmap — April 2026

*Prepared 2026-04-08 | Follows the Phase 5q/5r pattern: decompose "15-25 person-year" problems into tractable finite computations.*

**Entry state:** 128 Lean modules, 17 sorry, 1 axiom. Phase 5q proved the "impossible" Ext computation in ~5 hours. Phase 5r discharged hypothesis H2 in ~1 hour. This phase applies the same decomposition strategy to remaining obstacles.

**Strategy:** For each "impossible" obstacle, ask: "Is there a finite matrix computation hidden inside this problem that native_decide can verify?" The Phase 5q pattern — deep research extracts explicit data, Python cross-validates, Lean native_decide machine-checks — has proven extraordinarily effective.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
> 1. Read CLAUDE.md, WAVE_EXECUTION_PIPELINE.md, Inventory Index
> 2. Read this roadmap for wave assignments
> 3. Read deep research results in `Lit-Search/Phase-5s/` as they arrive
> 4. Read the obstacle analysis in docs/RESEARCH_STATUS_OVERVIEW.md

---

## Track A: Strengthen the Only Axiom (HIGHEST VALUE)

### Motivation

The gapped_interface_axiom is the project's single load-bearing assumption. We proved the 1+1D analog (VillainHamiltonian.lean). If we can prove the 2+1D analog via Fidkowski-Kitaev, we build a machine-checked LADDER: proved in 1D, proved in 2D, axiomatized in 3D. This is the single highest-value target in the project.

### Wave 1 — Deep Research: FK Hamiltonian Data [MANUAL — John]

**Task:** `Lit-Search/Tasks/Phase5s_fidkowski_kitaev_2plus1D_gapped_interface.md`

**Goal:** Extract the explicit 16×16 FK Hamiltonian, symmetry matrices, eigenvalues, and spectral gap. Assess native_decide feasibility.

**Status:** Prompt written. Ready for execution.

---

### Wave 2 — Majorana Representation [Pipeline: Stages 1-5]

**Goal:** Define 8 Majorana operators as 16×16 matrices in Lean. Reuse PauliMatrices.lean infrastructure.

**Prerequisites:** Wave 1 deep research.

**Deliverables:**
- [ ] `lean/SKEFTHawking/FKGappedInterface.lean` — Majorana matrices, FK Hamiltonian
- [ ] Symmetry matrices (T, (-1)^F)
- [ ] Connection to existing PauliMatrices.lean and MajoranaKramers.lean

**Estimated LOE:** 1 week
**Risk:** Low (16×16 matrices, same scale as A(1) computation)

---

### Wave 3 — Spectral Gap Verification [Pipeline: Stages 1-5]

**Goal:** Machine-check that the FK Hamiltonian has a unique gapped ground state.

**Prerequisites:** Wave 2 (Hamiltonian defined).

**Verification strategy:**
- Characteristic polynomial det(H - λI) factored over ℚ or an algebraic extension
- Ground state eigenvalue identified, multiplicity 1 verified
- Spectral gap Δ = E₁ - E₀ > 0 verified
- All via native_decide on 16×16 matrix arithmetic

**Deliverables:**
- [ ] `FKGappedInterface.lean` extended — spectral gap theorem
- [ ] Symmetry commutator verification: [H, T] = 0, [H, (-1)^F] = 0
- [ ] Ground state symmetry representation

**Estimated LOE:** 1-2 weeks
**Risk:** Medium (depends on eigenvalue complexity — may need custom number field if irrational)

---

### Wave 4 — Bridge Theorem [Pipeline: Stages 1-12]

**Goal:** Connect the FK 2D result to the 3D axiom via a bridge theorem.

**Deliverables:**
- [ ] Bridge theorem: FK 2D + dimensional reduction → evidence for 3D conjecture
- [ ] Update SPTClassification.lean with FK 2D as independent evidence
- [ ] Update AXIOM_METADATA: add FK 2D evidence to eliminability assessment
- [ ] Tests, figures, paper update, notebook
- [ ] RESEARCH_STATUS_OVERVIEW update

**Estimated LOE:** 1 week

---

## Track B: General Muger-Modularity Theorem (MEDIUM VALUE)

### Wave 5 — S-matrix → Muger Triviality (Direction 1) [Pipeline: Stages 1-5]

**Goal:** Prove the GENERAL theorem: det(S) ≠ 0 → Z₂(B) = Vec for any finite braided fusion category with S-matrix. This replaces 3 case-by-case native_decide proofs with one abstract result.

**Deep research:** `Lit-Search/Tasks/Phase5s_muger_smatrix_general_theorem.md`

**The argument (pure linear algebra):**
1. X transparent ⟹ row X proportional to row 0 in S
2. Proportional rows ⟹ linearly dependent ⟹ det = 0
3. Contrapositive: det ≠ 0 ⟹ no proportional rows ⟹ no transparent objects ⟹ Z₂ = Vec

**Prerequisites:** Deep research (verify Mathlib has `det = 0` from linearly dependent rows).

**Deliverables:**
- [ ] `lean/SKEFTHawking/ModularityTheorem.lean` — abstract theorem (~5-10 theorems)
- [ ] Replace case-by-case Muger proofs with instantiation of general theorem
- [ ] Update MugerCenter.lean to reference the general result

**Estimated LOE:** 1 week
**Risk:** Low (standard linear algebra, likely in Mathlib)

---

## Track C: KL Data Verification (MEDIUM VALUE)

### Wave 6 — SU(2)_k Fusion + S-matrix for k=3,4,5 [Pipeline: Stages 1-5]

**Goal:** Extend the data-level verification of the Kazhdan-Lusztig equivalence from k=1,2 to k=3,4,5.

**Deep research:** `Lit-Search/Tasks/Phase5s_kl_data_verification_k3_k4_k5.md`

**Prerequisites:** Deep research (number fields for k=3,4,5 S-matrices).

**Deliverables:**
- [ ] Fusion rule verification for k=4,5 (native_decide)
- [ ] S-matrix unitarity for k=3 (already done in QLevel3.lean), k=4 (QSqrt3.lean), k=5 (new)
- [ ] Data-level KL matching theorem for k ≤ 5

**Estimated LOE:** 2-3 weeks
**Risk:** Medium (k=5 number field may be complex)

---

## Track D: Instanton Mechanism Assessment (RESEARCH ONLY)

### Wave 7 — Instanton Coupling Formalizability [Research]

**Goal:** Determine whether the Csáki et al. instanton mechanism for bridging the Wen-ADW coupling deficit is formalizable.

**Deep research:** `Lit-Search/Tasks/Phase5s_instanton_adw_coupling.md`

**Decision gate:** If the instanton contribution is a sharp computable number → formalize. If order-of-magnitude only → document as physics argument, don't formalize.

**Estimated LOE:** Deep research only (1-2 days). Implementation conditional on results.

---

## Track E: Sorry Closure — q-Serre Coproduct & Antipode

### Wave 8 — q-Serre Coproduct Proofs (8 sorry) [Lean]

**Goal:** Close 8 q-Serre sorry in Uqsl2AffineHopf (4 comul + 4 antipode) and 3 in Uqsl3Hopf.

**Current state (April 9, 2026):** Phases 1-3 of the 4-phase strategy are **SOLVED in working code** (E10 case in Uqsl2AffineHopf.lean). Phase 4 (coefficient cancellation) is the sole remaining blocker. Aristotle cannot solve these — responsibility is ours.

**Working Phase 1-3 tactic sequence:**
```lean
erw [map_zero]
simp only [map_sub, map_add, map_mul, AlgHom.commutes]
erw [affComulFreeAlg_ι k E0, affComulFreeAlg_ι k E1]
simp only [affComulOnGen]
-- Combined expansion + K-E normalization (KEY: no ← Algebra.smul_def here)
set_option maxHeartbeats 1600000 in
simp only [mul_add, add_mul,
           Algebra.TensorProduct.tmul_mul_tmul,
           Algebra.TensorProduct.algebraMap_apply,
           mul_one, one_mul, mul_assoc,
           uqAff_K0E0, uqAff_K0E1, uqAff_K1E0, uqAff_K1E1, uqAff_K0K1_comm]
-- Deeper K-E via one alternation
simp only [← mul_assoc]
simp only [uqAff_K0E0, uqAff_K0E1, uqAff_K1E0, uqAff_K1E1, uqAff_K0K1_comm, mul_assoc]
-- Convert to smul
simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, mul_assoc, one_smul]
-- Phase 4: sorry — coefficient cancellation in LaurentPolynomial
sorry
```

**Key insights:**
- `Algebra.TensorProduct.algebraMap_apply` normalizes `algebraMap R (A⊗A) r` → `(algebraMap R A r) ⊗ₜ 1` — essential for [3]_q coefficient expansion
- Do NOT include `← Algebra.smul_def` in the expansion simp — smul wrappers block `mul_assoc` iterations
- `noncomm_ring` exceeds recursion depth on ~128 terms; `module` fails because `ring` can't handle `T(n)` in LaurentPolynomial
- `match_scalars` decomposes correctly but coefficient subgoals need Laurent polynomial-specific tactics, not `ring`

**Phase 4 next steps (ordered by likelihood of success):**
1. Pre-prove Laurent polynomial coefficient identities as standalone lemmas: `ext n; simp [LaurentPolynomial.T, Finsupp.single_apply]; omega`
2. Feed pre-proved identities into `match_scalars` for coefficient decomposition
3. OR: hierarchical `← tmul_add` grouping with `abel` for term permutation, then Serre + coefficient lemmas per group
4. Antipode q-Serre: try palindromic reversal trick (Phase-5e research) — only 4 terms after K-normalization, NOT 64. Likely closeable independently.

**Deep research (read in this order):**
1. `Lit-Search/Phase-5s/Mathlib4 tensor product algebra API and q-Serre tactic strategies.md` — **MOST ACTIONABLE**: algebraMap_apply, match_scalars, Laurent ext, hierarchical grouping
2. `Lit-Search/Phase-5e/U_q(ŝl₂) Hopf algebra proof strategy for Lean 4.md` — 64-term bidegree analysis, palindromic reversal for antipode
3. `Lit-Search/Phase-5d/Tensor product algebra rewriting for Hopf coproduct proofs in Lean 4.md` — 4-phase strategy, RingQuot.liftAlgHom pattern
4. `Lit-Search/Phase-5s/Lean 4 proof strategies for non-commutative tensor product normalization.md` — conv, noncomm_ring, grind
5. `Lit-Search/Tasks/qSerre_algebraMap_tensor_expansion.md` — updated prompt with working code + precise Phase 4 blocker
6. `Lit-Search/Tasks/complete/qSerre_coproduct_tensor_expansion_lean4.md` — original problem formulation

**Deliverables:**
- [ ] Pre-proved Laurent polynomial coefficient identities
- [ ] All 8 Uqsl2AffineHopf sorry closed (4 comul + 4 antipode q-Serre)
- [ ] All 3 Uqsl3Hopf sorry closed (same q-Serre pattern)
- [ ] Sorry count: 11 → 0 (CenterFunctor has 0 sorry, 2 hypotheses)

**Estimated LOE:** 2-5 days once Phase 4 approach validated
**Risk:** Medium (Phase 4 is a proof engineering problem, not a mathematical one — cancellation verified algebraically)

### Wave 9 — CenterFunctor Hypothesis Elimination (OPTIONAL)

**Goal:** Eliminate 2 tracked hypotheses (H_CF1, H_CF2) by constructing the concrete Z/2 functor.

**Deep research:** `Lit-Search/Phase-5s/CenterFunctor Z2 finite matrix feasibility.md`

**Approach:** Module.compHom + algebra map DG→End, ~400-600 lines, Z/2 case only.

**Estimated LOE:** ~1 week
**Risk:** Low (algebraic, finite-dimensional)

---

## Dependencies

```
Wave 1 (FK research) → Wave 2 (Majorana) → Wave 3 (spectral gap) → Wave 4 (bridge)

Wave 5 (Muger general) — independent

Wave 6 (KL data) — independent, needs number field research

Wave 7 (instanton) — independent, research only

Wave 8 (sorry closure) — independent, depends on Aristotle results
```

All tracks are independent. Maximum parallelism possible.

---

## Timeline

| Wave | Scope | LOE | Dependencies | Priority |
|------|-------|-----|-------------|----------|
| Wave 1 | FK deep research | 1-2 days | None | **COMPLETE** — explicit 16×16 integer matrix extracted |
| Wave 2 | FK Majorana representation | 1 week | Wave 1 | **COMPLETE** — FKGappedInterface.lean, 1.4s build |
| Wave 3 | FK spectral gap verification | 1-2 weeks | Wave 2 | **COMPLETE** — E₀=-7 unique, Δ=2, eigenvector proof |
| Wave 4 | FK bridge theorem + pipeline | 1 week | Wave 3 | Next — pipeline stages 6-12 |
| Wave 5 | Muger general theorem | 1 week | Deep research | **COMPLETE** — ModularityTheorem.lean, abstract proof |
| Wave 6 | KL data k=3,4,5 | 2-3 weeks | Deep research | **PARTIAL** — k=4 already done, k=5 fusion COMPLETE (comm + assoc, 4.2s). S-matrix k=5 pending (needs Q(cos(2π/7)) field). |
| Wave 7 | Instanton zero-mode counting | 1-2 days | None | **COMPLETE** — RED→GREEN. 4D index theorem BYPASSED via separation of variables. InstantonZeroModes.lean: 9 theorems, 0 sorry, 1.5s. Clifford decomposition + 6×6 angular kernel + polynomial dim → 2|qn|=4. |
| Wave 8 | q-Serre sorry closure | 2-5 days | Phase 4 approach | **IN PROGRESS** — Phases 1-3 working, Phase 4 (Laurent poly coefficients) blocks. 7 deep research results available. |
| Wave 9 | CenterFunctor hypotheses | 1 week | None | Optional — 2 hypotheses, 0 sorry |

**Total estimated LOE:** 7-11 weeks across all tracks, but most are parallelizable.

---

## Deep Research

| # | Topic | File | Status |
|---|-------|------|--------|
| 1 | FK 2+1D gapped interface | Lit-Search/Tasks/Phase5s_fidkowski_kitaev_2plus1D_gapped_interface.md | **READY** |
| 2 | S-matrix → Muger general theorem | Lit-Search/Tasks/Phase5s_muger_smatrix_general_theorem.md | **READY** |
| 3 | Instanton ADW coupling | Lit-Search/Tasks/Phase5s_instanton_adw_coupling.md | **READY** |
| 4 | KL data verification k=3,4,5 | Lit-Search/Tasks/Phase5s_kl_data_verification_k3_k4_k5.md | **READY** |

---

## What Success Looks Like

**Track A (FK gapped interface):** The project's only axiom is strengthened by a machine-checked proof of the 2+1D analog. First formalized Fidkowski-Kitaev interacting SPT classification in any proof assistant. The 3+1D conjecture becomes "proved in 1D, proved in 2D, conjectured in 3D."

**Track B (Muger general):** One abstract linear algebra theorem replaces all case-by-case Muger triviality proofs. Every future MTC gets modularity for free from its S-matrix determinant.

**Track C (KL data):** "For k ≤ 5, quantum group representations match MTC fusion data" — machine-checked. Strongest computational evidence for the categorical equivalence.

**Track D (instanton):** Clear assessment of whether the coupling deficit is formally bridgeable or inherently non-perturbative.

**Track E (sorry):** 11 → 0 sorry. Zero-sorry project (CenterFunctor has 2 tracked hypotheses, not sorry). First formalization of quantum group Hopf algebra compatibility in any proof assistant.

---

*Phase 5s roadmap. Created 2026-04-08. All deep research prompts written and ready. All waves follow [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md).*
