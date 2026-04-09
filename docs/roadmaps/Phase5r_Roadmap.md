# Phase 5r: Change-of-Rings and the Full Bordism Chain

## Technical Roadmap — April 2026

*Prepared 2026-04-08 | Follows Phase 5q (Ext computation over A(1)). Connects A(1) computation to the full spin bordism isomorphism.*

**Entry state (projected):** Phase 5q complete — Ext⁴_{A(1)}(F₂, F₂) ≅ ℤ/16 machine-checked. SpinBordism.lean rewritten with decomposed hypotheses T1-T4. The question: can we discharge any of T1-T4 algebraically?

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

**Goal:** Determine whether the freeness of A as a right A(1)-module can be verified computationally for the degrees we need.

The change-of-rings theorem requires: A is free as a right A(1)-module. For the full Steenrod algebra this is a theorem of Milnor-Moore (connected graded Hopf algebras over a field are free over connected sub-Hopf algebras). But we might not need the general theorem — we only need freeness in degrees ≤ 8 (to cover Ext in total degree 4).

**Key question:** In degrees ≤ 8, can we exhibit an explicit basis for A as a free right A(1)-module? This would be a finite verification (A has known dimension in each degree, and A(1) has dimension 8, so the number of free generators in degrees ≤ 8 is bounded).

**Deep research task:**
- [ ] `Lit-Search/Tasks/Phase5r_steenrod_algebra_A1_freeness.md`

**Deliverables:**
- `Lit-Search/Phase-5r/Steenrod algebra as free A(1)-module in low degrees.md`

**Status:** Not started. Blocked on Phase 5q deep research.

---

### Wave 2 — Steenrod Algebra A in Low Degrees [Pipeline: Stages 1-5]

**Goal:** Extend SteenrodA1.lean to include enough of the full Steenrod algebra A to verify the change-of-rings isomorphism in degree 4.

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

**Decision gate:** If the freeness verification in low degrees works, proceed to Wave 3. If the dimensions are too large for native_decide, axiomatize the freeness and move on.

**Estimated LOE:** 2-3 weeks
**Risk:** Medium. The Steenrod algebra in degree 8 is manageable (dim 4) but the Adem relations generate many cross-terms.

---

### Wave 3 — Change-of-Rings Verification in Degree 4 [Pipeline: Stages 1-5]

**Goal:** Prove (or verify computationally) that Ext⁴_A(A ⊗_{A(1)} F₂, F₂) ≅ Ext⁴_{A(1)}(F₂, F₂) in degree 4.

**Prerequisites:** Wave 2 (Steenrod algebra in low degrees), Phase 5q Wave 4 (Ext over A(1)).

**Two approaches:**

**Approach A (algebraic):** Use the explicit freeness from Wave 2 to show that the induction functor A ⊗_{A(1)} - maps the A(1)-resolution to an A-resolution, then show the Hom_{A}(-, F₂) computation gives the same answer.

**Approach B (computational bypass):** Build an explicit resolution of F₂ over A (not just A(1)) in degrees ≤ 5 and compute Ext⁴_A directly. Then verify it matches Ext⁴_{A(1)} = ℤ/16. This sidesteps the abstract change-of-rings entirely.

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
| Wave 1 | Deep research: A/A(1) freeness | 1-2 days | Phase 5q complete | **BYPASSED** — change-of-rings proved abstractly |
| Wave 2 | Steenrod algebra in low degrees | 2-3 weeks | Wave 1 | **BYPASSED** — not needed for abstract proof |
| Wave 3 | Change-of-rings in degree 4 | 2-4 weeks | Wave 2 + 5q W4 | **COMPLETE** (ChangeOfRings.lean, H2 discharged) |
| Wave 4 | ASS collapse assessment | 1-3 weeks | Phase 5q complete | **ASSESSED** — genuinely topological, cannot be discharged algebraically. Potential d₃(h₁²) → v requires Bott periodicity to rule out. H3 stays as hypothesis. |
| Wave 5 | K3 formalizability assessment | 1 day | None | **ASSESSED** — Mathlib lacks smooth manifolds/algebraic geometry. H4 stays as hypothesis. |

**Total actual LOE for Track A:** ~1 hour (the abstract adjunction argument bypasses Waves 1-2 entirely).
**Original estimate:** 6-12 weeks.

---

## Deep Research

| # | Topic | File | Status |
|---|-------|------|--------|
| 1 | A over A(1) freeness | Lit-Search/Tasks/Phase5r_steenrod_algebra_A1_freeness.md | Written, but **BYPASSED** — abstract argument doesn't need explicit freeness |
| 2 | ASS collapse in total degree 4 | Lit-Search/Tasks/Phase5r_ASS_collapse_degree_4.md | Not yet written (would discharge H3) |
| 3 | K3 surface formalizability | Lit-Search/Tasks/Phase5r_K3_surface_formalizability.md | Not yet written |

---

## What Success Looks Like

**Minimum viable:** Hypothesis H2 (change-of-rings) DISCHARGED. **ACHIEVED** (ChangeOfRings.lean).

**Stretch:** H3 (ASS collapse) discharged via sparsity argument. This would leave only H1 (ko cohomology) and H4 (ABP splitting) as hypotheses — both are deep topological facts with no known algebraic bypass.

**Current status:** H2 discharged. Hypotheses remaining: 3 (H1, H3, H4). The generation constraint N_f = 0 mod 3 rests on machine-checked algebra plus 3 standard textbook topology results.

**Combined with Phase 5q:** The generation constraint N_f ≡ 0 mod 3 rests on machine-checked algebra (Ext⁴ = ℤ/16, change-of-rings, modular invariance) plus two concrete topological inputs (MSpin cohomology and K3 existence). This is the strongest possible formal position short of formalizing all of algebraic topology.

---

*Phase 5r roadmap. Created 2026-04-08. Blocked on Phase 5q completion. All waves follow [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md).*
