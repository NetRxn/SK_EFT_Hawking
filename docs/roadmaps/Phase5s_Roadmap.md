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

**Current state (April 10, 2026):** Phases 1-3 SOLVED. Phase 4 FULLY DIAGNOSED — three approaches tried and ruled out. Deep research filed for CAS-assisted approach. 4 new q-commutation lemmas proved as building blocks.

**Phase 1-3 (WORKING):** Combined simp expands coproduct + applies K-E commutation in one pass. Uses `algebraMap_apply` (not `← Algebra.smul_def`) during expansion. One round of `← mul_assoc` + K-E alternation for deeper pairs. Produces ~128 normalized terms.

**Phase 4 diagnostic results (April 10):**

Three approaches systematically tested and ruled out:

1. **match_scalars (WRONG):** Decomposes by tensor atom, but the Serre cancellation is NOT coefficient-wise. In the non-commutative algebra, `E₁²E₀` and `E₁E₀E₁` are different atoms — the Serre relation combines ACROSS different E-orderings. `match_scalars` correctly produces `⊢ 1 = 0` because individual atoms don't cancel.

2. **Brute-force 128-term normalization (HEARTBEAT LIMIT):** Full expansion works at 1.6M heartbeats. But subsequent normalization (interleaved smul extraction + K-E rounds + smul-to-outer via `tmul_smul`/`smul_tmul'`) exceeds limits even at 6.4M. The expression is simply too large for repeated simp.

3. **Kitchen-sink simp (NON-TERMINATING):** Including both `mul_add` (distribute) and `← tmul_add` (factor) creates infinite rewrite loops.

**Root causes:**
- 128-term expression too large for repeated normalization passes
- algebraMap scalars from K-E commutation block deeper K-E passes (need interleaved smul extraction)
- Serre cancellation is inter-atomic: different non-commutative E-orderings must combine via the Serre relation itself

**New infrastructure (4 proved lemmas, zero sorry):**
```lean
deltaE1_q_comm : (E₁⊗K₁)*(1⊗E₁) = T(2) • (1⊗E₁)*(E₁⊗K₁)
deltaE1_cross_comm_E0 : (E₁⊗K₁)*(1⊗E₀) = T(-2) • (1⊗E₀)*(E₁⊗K₁)
deltaE0_cross_comm_E1 : (E₀⊗K₀)*(1⊗E₁) = T(-2) • (1⊗E₁)*(E₀⊗K₀)
deltaE0_q_comm : (E₀⊗K₀)*(1⊗E₀) = T(2) • (1⊗E₀)*(E₀⊗K₀)
```
These encode how the two summands of Δ(Eᵢ) q-commute in A⊗A via K-E relations.

**Phase 4 viable approaches (in priority order):**

1. **CAS-assisted tactic generation (RECOMMENDED):** Use SageMath/Mathematica to pre-compute the symbolic expansion, K-E normalization, and bidegree grouping offline. Output a Lean tactic script (~50-200 lines) that uses calc blocks with intermediate `have` lemmas, staying within default heartbeat limits per step. Deep research filed: `Lit-Search/Tasks/qSerre_coproduct_CAS_tactic_generation.md`.

2. **q-adjoint action (ELEGANT, HIGH INFRASTRUCTURE COST):** Kassel Ch.V proof: define `ad_q(E)(x) = Ex - q^{⟨α,wt(x)⟩}xE`, prove `Δ(ad_q(a)) = ad_q(Δ(a))`, then `Δ(Serre) = Δ(ad_q³(E₀)) = ad_q(Δ(E₁))³(Δ(E₀)) = 0`. Requires ~500 lines of q-adjoint infrastructure not in Mathlib.

3. **Partial expansion with bidegree calc blocks (MANUAL, MODERATE):** Don't fully expand. Keep `(x+y)` factored, expand only enough to separate bidegrees, close each with Serre. Uses the 4 q-commutation lemmas. ~100-200 lines, no heartbeat issues, but highly manual.

**Deep research (read in this order — UPDATED April 10):**
1. `Lit-Search/Tasks/qSerre_coproduct_CAS_tactic_generation.md` — **NEW, MOST ACTIONABLE**: complete problem spec for CAS approach
2. `Lit-Search/Phase-5s/Mathlib4 tensor product algebra API and q-Serre tactic strategies.md` — algebraMap_apply, match_scalars (proven wrong but documents why), Laurent ext, hierarchical grouping
3. `Lit-Search/Phase-5e/U_q(ŝl₂) Hopf algebra proof strategy for Lean 4.md` — 64-term bidegree analysis, palindromic reversal for antipode
4. `Lit-Search/Phase-5d/Tensor product algebra rewriting for Hopf coproduct proofs in Lean 4.md` — 4-phase strategy, RingQuot.liftAlgHom pattern
5. `Lit-Search/Phase-5s/Lean 4 proof strategies for non-commutative tensor product normalization.md` — conv, noncomm_ring, grind (all tested, all insufficient alone)
6. `Lit-Search/Phase-5i/Proving q-Serre cubic coproduct compatibility in Lean 4.md` — bidegree decomposition strategy
7. `Lit-Search/Tasks/complete/qSerre_algebraMap_tensor_expansion.md` — documents the algebraMap blocker + working Phase 1-3

**Deliverables:**
- [x] q-commutation infrastructure (4 lemmas)
- [x] CAS-generated tactic script for E10 coproduct
- [x] All 8 Uqsl2AffineHopf sorry closed (4 comul + 4 antipode q-Serre) — **DONE April 2026**
- [x] All Uqsl3Hopf sorry closed — **DONE 2026-04-14** (all 4 antipode q-Serre cubics E12/E21/F12/F21 proven; commits `bf2989d` SerreE12, `912c495` SerreE21, `fad0edb` SerreF12, `619dd37` SerreF21; atom-bridge for palindromic Serre resolved via per-generator eval lemmas)
- [x] Sorry count: 11 → 0 — **DONE 2026-04-14**. Uqsl3Hopf.lean builds clean (0 sorry, 0 errors); full SKEFTHawking package builds clean no-cache (8396 jobs, 131 oleans).
- [x] Bialgebra + HopfAlgebra typeclass instances wired for U_q(sl_3) — **DONE 2026-04-14** (Tranche E, commits `dadce3e` per-generator eval lemmas + Bialgebra instance; `bdf0ee9` HopfAlgebra typeclass complete). Includes S² = Ad(K₁²K₂²) per generator (Drinfeld theorem), all 21 relation-respect proofs for Δ/ε/S, 24 per-generator evaluation lemmas, 3 coalgebra axioms (coassoc, rTensor_counit, lTensor_counit).

**Estimated LOE:** Days (F01 is last remaining q-Serre proof, same pattern as completed E10)
**Risk:** Low — the mathematical structure is identical to the solved cases

**Wave 8 status: COMPLETE 2026-04-14.** All q-Serre sorry across Uqsl2AffineHopf and Uqsl3Hopf closed. Phase 5s success criterion ("11 → 0 sorry; First formalization of quantum group Hopf algebra compatibility in any proof assistant") achieved for the q-Serre track.

### Wave 9 — CenterFunctor Hypothesis Elimination (OPTIONAL)

**Goal:** Eliminate 2 tracked hypotheses (H_CF1, H_CF2) by constructing the concrete Z/2 functor.

**Deep research:** `Lit-Search/Phase-5s/CenterFunctor Z2 finite matrix feasibility.md`

**Approach:** Module.compHom + algebra map DG→End, ~400-600 lines, Z/2 case only.

**Estimated LOE:** ~1 week
**Risk:** Low (algebraic, finite-dimensional)

**Progress:**

- [x] **Wave 9 scaffold — the 4 character AlgHoms** (2026-04-15, commit `642eb8d`).
  `CenterFunctorZ2.lean` (394 lines) builds the 4 simple `D(ℤ/2)`-modules as
  explicit characters `DG k G2 →ₐ[k] k` where `G2 := Multiplicative (ZMod 2)`:
    - `chiTrivTriv(f) = f(e,e) + f(e,a)` (trivial × trivial)
    - `chiTrivSign(f) = f(e,e) − f(e,a)` (trivial × sign)
    - `chiFlipTriv(f) = f(a,e) + f(a,a)` (flip × trivial)
    - `chiFlipSign(f) = f(a,e) − f(a,a)` (flip × sign)
  Each verified as a full `AlgHom` (map_one, map_mul, map_zero, map_add,
  commutes). Key helper `DG_mul_coeff_G2` expands `ddAlgMul` over G2's
  2-element group using abelian-group simplifications
  (`g1⁻¹·x·g1 = x`, `a·a = e`, `a⁻¹ = a`). 18 theorems, 0 sorry.
  `simpleChi : DZ2Simple → (DG k G2 →ₐ[k] k)` packages the 4 characters
  aligning with the `CenterEquivalenceZ2` bijection.
- [ ] **Wave 9 continuation — Module instances + functor + equivalence**
  (estimated 300-400 LOC more):
    - Wrapper types for the 4 simple modules (distinct from each other and
      from plain `k`)
    - `Module (DG k G2)` instances via `Module.compHom` + the 4 characters
    - Functor `centerToRepZ2 : Center (VecG_Cat k G2) ⥤ ModuleCat (DG k G2)`
      via pattern match on toric anyons
    - Full + Faithful + EssSurj via finite case analysis (4 objects)
    - Assemble `Equivalence.ofFullyFaithfulEssSurj` → discharge
      `H_CF1_center_functor` and `H_CF2_center_equivalence` in `CenterFunctor.lean`

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
| Wave 8 | q-Serre sorry closure | 3-7 days | CAS deep research | **COMPLETE 2026-04-14** — Uqsl2AffineHopf: 0 sorry. Uqsl3Hopf: 0 sorry (all 4 antipode Serre cubics E12/E21/F12/F21 closed; Bialgebra + HopfAlgebra typeclass instances wired). Full SKEFTHawking package builds clean no-cache. |
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
