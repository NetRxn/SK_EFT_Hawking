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

## Track E: Sorry Closure (MECHANICAL)

### Wave 8 — RingQuot Workaround [Lean]

**Goal:** Close the remaining 15 RingQuot-blocked sorry using the manual workaround pattern (letI + NonUnitalNonAssocRing + op_mul).

**Prerequisites:** Aristotle 6dbc9447 results (may resolve some or all). If Aristotle fails, manual application.

**The pattern (proven for 4 cases this session):**
```lean
letI : NonUnitalNonAssocRing (Uqsl2Aff k) := inferInstance
-- Then neg_mul, mul_neg, etc. fire correctly
```

**Deliverables:**
- [ ] All 12 Uqsl2AffineHopf sorry closed
- [ ] All 3 Uqsl3Hopf sorry closed
- [ ] Sorry count: 17 → 2 (only CenterFunctor remains)

**Estimated LOE:** 1-3 days (mechanical once pattern confirmed)
**Risk:** Low (pattern proven, just repetitive)

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
| Wave 7 | Instanton assessment | 1-2 days | None | **ASSESSED** — RED for formalizability. Index theorem doesn't exist in mathematics. O(1) coupling is real physics but not machine-checkable. |
| Wave 8 | Sorry closure | 1-3 days | Aristotle results | Aristotle 6dbc9447 in flight |

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

**Track E (sorry):** 17 → 2 sorry. Near-zero sorry project.

---

*Phase 5s roadmap. Created 2026-04-08. All deep research prompts written and ready. All waves follow [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md).*
