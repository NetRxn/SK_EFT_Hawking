# Phase 5r: Change-of-Rings and the Full Bordism Chain

## Technical Roadmap — April 2026

*Prepared 2026-04-08 | Follows Phase 5q (Ext computation over A(1)). Connects A(1) computation to the full spin bordism isomorphism.*

**Current entry state:** genuine native A(1) ring/augmentation, projective terms, chain identities, finite exactness and dual cohomology remain. Generic balanced induction/infinite splice and the [accepted actual global Milnor successor](../audits/2026-10-17-publication-substance-construction/B4_GLOBAL_MILNOR_BASIS.md), with their full reviews, establish the complete MANUAL full A/source-compatible inclusion/all-degree LEFT and RIGHT B-bases/compatible involutive antipodes and BOTH-sided derived/internally graded Ext comparison. The native actual algebra/module objects, typed categorical infinite splice/isoExt/graded consumers and original H2 source bindings remain OPEN. F₂ Ext is not ℤ/16; H1/H3/H4/Adams/topology and physical generation require their original evidence.

**Goal:** Attack the change-of-rings isomorphism Ext_A ≅ Ext_{A(1)} and the ASS convergence claim, potentially discharging hypotheses T2 and T3 from the 5q decomposition.

**Prerequisite deep research:**
- Phase 5q deep research results (Mathlib assessment determines approach)
- Additional deep research as specified below

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
> 1. Read CLAUDE.md, WAVE_EXECUTION_PIPELINE.md, Inventory Index
> 2. Read this roadmap for wave assignments
> 3. Read deep research results in `Lit-Search/Phase-5q/` and `Lit-Search/Phase-5r/`
> 4. Read Phase 5q roadmap (prerequisite)

---

## Track A: Change-of-Rings (Discharging Hypothesis T2)

### Wave 1 — Deep Research: A over A(1) Freeness

**Goal:** implement the independently accepted MANUAL full A/inclusion/all-degree left/right basis/antipode construction in native objects for original H2. Source RIGHT resolution uses the constructed LEFT basis; original LEFT H2 uses the RIGHT basis or compatible anti-automorphism twist.

For the actual RIGHT A(1) resolution, induction is P tensor_{A(1)} A and now has the constructed all-degree LEFT-B basis. Original LEFT H2 uses the constructed RIGHT basis or compatible involutive antipodes. The generic conditional theorem remains exact; the [accepted actual global Milnor successor](../audits/2026-10-17-publication-substance-construction/B4_GLOBAL_MILNOR_BASIS.md) supplies the actual MANUAL hypotheses and both-sided derived/graded comparison. Native actual objects/typed splice/isoExt/consumers and H1/H3/H4/topology remain owed.

**Completed mathematical answer:** full polynomial coalgebra/graded dual, actual source-compatible embedding, corrected cofree inverse and all-degree finite-support coordinates prove both module bases, with compatible antipodes and derived/graded comparison. Full independent review is linked in the global note. Next build native maps/interfaces; low-degree checks remain convention controls.

**Deep research task:**
- [ ] `Lit-Search/Tasks/Phase5r_steenrod_algebra_A1_freeness.md`

**Deliverables:**
- `Lit-Search/Phase-5r/Steenrod algebra as free A(1)-module in low degrees.md`

**Status:** **DR returned**, with original Phase5s deliverable and its historical abstract-bypass/API advice retained as context, not proof authority. Generic [B4](../audits/2026-10-17-publication-substance-construction/B4_BALANCED_INDUCTION_CHANGE_OF_RINGS.md) and the [accepted actual global Milnor successor](../audits/2026-10-17-publication-substance-construction/B4_GLOBAL_MILNOR_BASIS.md) independently complete the MANUAL full A/source-compatible inclusion/all-degree LEFT and RIGHT B-bases/compatible involutive antipodes and BOTH-sided derived/internally graded Ext comparison. Native actual objects, typed splice/isoExt/consumers remain OPEN.

---

### Wave 2 — Steenrod Algebra A in Low Degrees [Pipeline: Stages 1-5]

**Goal:** natively realize the accepted full A/inclusion/all-degree bases/antipodes and derived/graded comparison, preserving actual source convention e3=beta30+beta01. Low-degree exploration remains a convention control; infinite typed continuation/isoExt/graded consumers remain to build.

**Prerequisites:** Wave 1 deep research.

**What's needed:**
- A has generators Sq¹, Sq², Sq⁴, Sq⁸, ... (the Milnor primitives). For degree ≤ 8, we need Sq¹, Sq², Sq⁴, and products up to degree 8.
- The Adem relations constrain these products to a finite-dimensional space at each degree
- In degree ≤ 8: dim A₀ = 1, A₁ = 1, A₂ = 1, A₃ = 1, A₄ = 2, A₅ = 2, A₆ = 3, A₇ = 3, A₈ = 4

**Deliverables:**
- [ ] `lean/SKEFTHawking/SteenrodAlgebra.lean` — A in degrees ≤ 8 (~15-25 theorems):
  - Generators Sq¹, Sq², Sq⁴ with Adem relations
  - Explicit basis in each degree through 8
  - `A_free_over_A1_low` — explicit free basis of A over A(1) in degrees ≤ 8 (native_decide)
- [ ] Tests, formulas

**Construction boundary:** actual all-degree sided bases/antipodes and derived comparison are independently accepted manually; construct their native objects and exact consumers. A finite degree check or freeness axiom cannot replace the construction or weaken H2.

**Estimated LOE:** 2-3 weeks
**Risk:** Medium. The Steenrod algebra in degree 8 is manageable (dim 4) but the Adem relations generate many cross-terms.

---

### Wave 3 — Change-of-Rings Verification in Degree 4 [Pipeline: Stages 1-5]

**Goal:** Prove (or verify computationally) that Ext⁴_A(A ⊗_{A(1)} F₂, F₂) ≅ Ext⁴_{A(1)}(F₂, F₂) in degree 4.

**Prerequisites:** Wave 2 (Steenrod algebra in low degrees), Phase 5q Wave 4 (Ext over A(1)).

**Two approaches:**

**Approach A (algebraic):** natively instantiate the accepted generic and actual global constructions. For the source right resolution use P tensor_{A(1)} A with the constructed LEFT basis; implement typed infinite splice, exactness and categorical/graded Ext. Constructed RIGHT basis and compatible antipodes supply the original LEFT-module route.

**Approach B (direct resolution):** construct a genuine augmented A-projective resolution, exact in every required degree with a valid infinite continuation, and compare actual Hom/cohomology maps. No ℤ/16 conclusion follows from an F₂-vector-space rank; the internal grading/Adams/topological steps remain separate.

**Deliverables:**
- [ ] `lean/SKEFTHawking/ChangeOfRings.lean` — verification (~10-20 theorems)
  - Either: abstract isomorphism proved from freeness
  - Or: explicit Ext_A computation matching Ext_{A(1)}
- [ ] Discharge hypothesis T2 from SpinBordism.lean

**Estimated LOE:** 2-4 weeks (depends on approach)
**Risk:** Medium-High. This is the most uncertain phase. If neither approach is tractable, T2 remains as a hypothesis — which is still better than the monolithic Ω^Spin_4 ≅ ℤ.

---

## Track B: Adams Spectral Sequence Convergence (Discharging Hypothesis T3)

### Wave 4 — ASS Collapse Assessment

**Goal:** Determine whether the Adams spectral sequence collapse in total degree 4 can be verified in Lean.

The claim (T3) is: there are no ASS differentials d_r for r ≥ 2 that hit E_r^{s,t} with t - s = 4. In practice, this is checked by:
1. Listing all possible source/target pairs for d_r in bidegrees near total degree 4
2. Showing each potential differential is zero (by sparsity, degree constraints, or explicit computation)

For MSpin in total degree 4, the relevant E₂ page is sparse — there simply aren't enough non-zero groups to support differentials. This is a finite check.

**Deep research task:**
- [ ] `Lit-Search/Tasks/Phase5r_ASS_collapse_degree_4.md` — enumerate all potential differentials, verify they're zero

**Decision gate:** If the collapse can be stated as a finite list of "group X is zero, therefore d_r = 0" statements, we formalize. If it requires spectral sequence infrastructure beyond Mathlib, we leave T3 as a hypothesis.

**Estimated LOE:** Deep research 1-2 days, formalization 1-2 weeks if tractable
**Risk:** High. Spectral sequences are not in Mathlib. But the SPECIFIC check (no differentials hitting degree 4) might be statable without the full spectral sequence machinery.

---

## Track C: K3 Surface (Hypothesis T4 — Assessment Only)

### Wave 5 — K3 Formalizability Assessment

**Goal:** Assess whether the existence of K3 (a spin 4-manifold with σ = -16) can be formalized in Lean, or whether it should remain as a hypothesis.

K3 is a quartic surface in CP³: the zero locus of a degree-4 polynomial in 4 homogeneous coordinates. Its topological properties (simply connected, spin, χ = 24, σ = -16) are classical results.

**Assessment questions:**
- Does Mathlib have smooth manifolds or algebraic varieties?
- Can we define CP³ and hypersurfaces?
- Can we compute the signature of a quartic surface from its Hodge diamond?

**Expected answer:** This is almost certainly a hypothesis for now. Algebraic geometry in Lean is nascent. But the assessment is worth doing to understand the gap.

**Deep research task:**
- [ ] `Lit-Search/Tasks/Phase5r_K3_surface_formalizability.md`

**Estimated LOE:** Deep research only (1 day). No implementation expected.
**Risk:** None. Assessment only.

---

## Dependencies

```
Phase 5q (Ext computation) ──→ Wave 1 (freeness research) ──→ Wave 2 (Steenrod A)
                                                                    ↓
                                                              Wave 3 (change-of-rings)
                                                                    ↓
                                                        Discharge T2 in SpinBordism.lean

Phase 5q (Ext computation) ──→ Wave 4 (ASS collapse) ──→ Potentially discharge T3

Phase 5q (Ext computation) ──→ Wave 5 (K3 assessment) ──→ T4 stays as hypothesis (expected)
```

Tracks A, B, C are independent after Phase 5q completes. Track A is highest value.

---

## Timeline

| Wave | Scope | LOE | Dependencies | Status |
|------|-------|-----|-------------|--------|
| Wave 1 | Deep research: A/A(1) freeness | 1-2 days | Phase 5q complete | DR returned; full all-degree MANUAL witness independently accepted; native continuation owed |
| Wave 2 | Steenrod algebra / actual inclusion and sided basis | 2-3 weeks | Wave 1 | Full actual MANUAL construction accepted; native algebra/module/graded objects OPEN |
| Wave 3 | Change-of-rings in degree4 | 2-4 weeks | Wave 2 + 5q W4 | Actual BOTH-sided derived/graded MANUAL comparison accepted; native H2/consumers OPEN |
| Wave 4 | ASS collapse assessment | 1-3 weeks | Phase 5q complete | **ASSESSED** — genuinely topological, cannot be discharged algebraically. Potential d₃(h₁²) → v requires Bott periodicity to rule out. H3 stays as hypothesis. |
| Wave 5 | K3 formalizability assessment | 1 day | None | **ASSESSED** — Mathlib lacks smooth manifolds/algebraic geometry. H4 stays as hypothesis. |

**Historical abstract-bypass estimate:** the earlier approximately one-hour Track A record concerned free-Hom dimensions, not native H2. Generic balanced and full actual global constructions now have independent manual acceptance. Current continuation is native actual algebra/module objects, typed categorical infinite splice/isoExt/graded consumers and original H2 source bindings. No estimate/library gap establishes infeasibility or authorizes deferral.

---

## Deep Research

| # | Topic | File | Status |
|---|-------|------|--------|
| 1 | A over A(1) freeness | Lit-Search/Tasks/Phase5r_steenrod_algebra_A1_freeness.md | Returned; actual all-degree left/right basis/antipode MANUAL witness accepted; native integration OPEN |
| 2 | ASS collapse in total degree 4 | Lit-Search/Tasks/Phase5r_ASS_collapse_degree_4.md | Not yet written (would discharge H3) |
| 3 | K3 surface formalizability | Lit-Search/Tasks/Phase5r_K3_surface_formalizability.md | Not yet written |

---

## What Success Looks Like

**Minimum viable:** original actual H2 native change of rings with full objects/interfaces, independently verified. Generic and actual full global algebraic proofs are completed manual prerequisites; this source candidate does not install a native theorem.

**Stretch:** discharge H3 by actual Adams/sparsity mathematics. Actual H2 algebraic mathematics is manually accepted; native realization/consumers remain open. H1 ko-cohomology and H4 ABP remain separate; neither accepted algebraic note supplies those identifications.

**Current status:** full actual B4 algebraic milestone is independently accepted MANUALLY: full A/source-compatible inclusion/all-degree LEFT and RIGHT B-bases/compatible involutive antipodes and BOTH-sided derived/internally graded Ext comparison, together with generic balanced induction. The native actual algebra/module objects, typed categorical infinite splice/isoExt/graded consumers and original H2 source bindings remain OPEN. Original H1/H3/H4/topology remain owed.

**Combined with Phase 5q:** retain genuine ring, Hom, finite exactness/cohomology and independent divisibility arithmetic. These do not yet instantiate the full generation/bordism chain; no Ext⁴=ℤ/16, topological realization or physical generation result is inferred from those F₂ calculations.

---

*Phase 5r roadmap. Created 2026-04-08. Blocked on Phase 5q completion. All waves follow [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md).*
