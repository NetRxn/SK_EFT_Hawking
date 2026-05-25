# Phase 6r-prime: Substantive Discharge of Phase 6r SymTFT Tracked Props

## Technical Roadmap — May 2026

*Prepared 2026-05-25 at Phase 6r close. Sources: Phase 6r close-out + adversarial review reports (`temporary/working-docs/phase6r/adversarial_review_round{1,2}.md`) + Phase 6r tracked-Props discharge-feasibility audit + Wave 1a.1 DR §1.3 + §4.3 + §5.2 (Lean tractability + Mathlib gap analysis) + project-velocity calibration against Phase 6q (11 modules, 2,716 LoC, ~2 sessions) + Phase 6r (18 modules, ~2,650 LoC, 1 session); user direction "push for state of the art - discharge everything we can".*

**Trigger condition:** Phase 6r-prime opens at Phase 6r close. The Phase 6r SymTFT substrate shipped 18 modules + 12 tracked Props at predicate-substrate level; per the post-close discharge-feasibility audit, **11 of 12 tracked Props have realistic discharge paths** within ~30-80 program-sessions (~2-6 program-PMs deflated). Phase 6r-prime executes the **substantive substrate discharge** for the dischargeable subset, eliminating tracked Props in favor of fully constructive Lean content.

**Status (2026-05-25, Phase 6r-prime stub):** Roadmap stub committed at Track / Wave level. Four Wedges (W1-W4) + carryover items (C1-C3) + cross-bridge integration + close-out review. **Multi-session phase commitment** by project convention; comparable to Phase 6q + 6r in series.

**Project rule (carried from Phase 6r):** **No PM / time / phase-cost estimates** in this roadmap — only session-count ranges per project-velocity calibration. **No new `axiom` declarations** (per Invariant #15). **Substantive discharge means**: replace predicate-substrate tracked Props (`def IsXxx : Prop := True` / `def IsXxx B := Is3DTQFT B`) with constructive Lean content backed by primary-source-cited substrate.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
>
> 1. **Mandatory project bootstrap** per `CLAUDE.md` Mandatory References list.
> 2. **Read `Phase6r_Roadmap.md` end-to-end** — this phase substantively discharges its tracked Props.
> 3. **Read this roadmap end-to-end** before claiming any wave assignment.
> 4. **Read the Phase 6r adversarial-review reports** at `temporary/working-docs/phase6r/adversarial_review_round1.md` + `adversarial_review_round2.md` to understand the BLOCKER-2 / NEW-ADVISORY-1 motivation for substantive Wedge 2 ship.
> 5. **Read the three Phase 6r DRs** at `Lit-Search/Phase-6r/` (Wave 1a.1 + 2a.1 + 3a.1) — they contain the LOE calibrations + tractability analyses for each Wedge.
> 6. **Critical predecessor modules — read source directly:**
>    - **Phase 6r SymTFT substrate (heaviest dependency):** all 18 modules under `lean/SKEFTHawking/SymTFT/` + `lean/SKEFTHawking/CrossBridges/SMMatterAsSymTFTBoundary.lean` + `lean/SKEFTHawking/APSEta/SubstrateBulkAsymmetry.lean`. The 12 tracked Props this phase targets are catalogued there.
>    - **Mathlib4 categorical infrastructure status** per Wave 1a.1 §4.3: `Center`/`Mon_`/`Comon_` PRESENT; pivotal/spherical/Frobenius-in-monoidal-category ABSENT; cobordism category ABSENT; APS η-invariant ABSENT; modular tensor category typeclass ABSENT.
>    - **Project's existing substrate patterns** for cobordism-adjacent work: `Schellekens/SpinBordism.lean` (Phase 6o spin-bordism placeholder); `APSEta/` modules (Phase 6o substrate placeholders). These show the "axiomatize-an-opaque-Type-with-isomorphism-witness" pattern.
>    - **Project's `CenterFunctorZ2.lean`** + `S3CenterAnyons.lean` + `DrinfeldCenterBridge.lean` — paper-9 Drinfeld-center computations; the substrate Wedge 1 + Wedge 2 + Wedge 5 build on.
>    - **Project's `LaplaceMethod.lean`** — established precedent for "Mathlib gap → ship substrate in SKEFTHawking" (retired `gaussianSaddleAsymptotic` axiom Phase 6a Wave 7).
> 7. **`LATE_PHASE6_ABSORPTION_PROTOCOL.md` — load before any bundle-touching work** (deferred to bundle-absorption pass; this phase ships substrate only).
> 8. **Apply preemptive-strengthening checklist** + **primacy-claim discipline** per `memory/project_2026_05_12_first_claim_close.md`. **CRITICAL for Phase 6r-prime:** the substantive discharge invites "first formalization of Pin⁺ bordism in any prover" / "first DMNO theorem proved in Lean" framing. Resist this framing per `project_2026_05_12_first_claim_close.md`; ship descriptive content-first prose. **The honest framing**: "first formalization of Ω_4^{Pin⁺}(pt) ≅ ℤ/16 in Lean 4, with the underlying topological-bordism mathematics due to Kirby-Taylor 1990" — primary-source-anchored.
> 9. **Do not delegate Lean theorem proving to subagents.** MCP loop default; Aristotle is fallback. **Pre-flight Explore-agent dispatch IS authorized for substrate scouting** — Phase 6r-prime has the most substrate-construction surface area of any 6X phase.
> 10. **No PM / time estimates anywhere** — by user direction. Session-count ranges OK (calibrated against recent Phase 6q + 6r + 6t ships).
> 11. **No manuscript drafting at this phase.** Bundle absorption deferred per Phase 6r convention.

---

## Substrate state snapshot (2026-05-25, pre-dispatch)

> **Purpose of this section:** Phase 6r close-out state for next-session bootstrap. The substantive discharge work consumes this substrate.

### A. Phase 6r tracked Props (the 12 targets)

Catalogued at `temporary/working-docs/phase6r/wave_1a_SymTFT_substrate.md` §4. The 12 Props with current discharge status:

| # | Tracked Prop | File | Discharge tier |
|---|---|---|---|
| 1 | `IsKirbyTaylorPinPlusBordism` | `SymTFT/PinBordism.lean` | **W1 (Pin⁺ bordism substrate) + W3 (KT proof)** |
| 2 | `IsAndersonDualPinPlus` | `SymTFT/PinBordism.lean` | **W1** (derived from #1 via Anderson-dual functor) |
| 3 | `IsAndersonDualPinPlusRelation` | `SymTFT/PinBordism.lean` | Transitive on #1 + #2 |
| 4 | `IsWittenYonekuraInflow` | `SymTFT/PinBordism.lean` | **W4 (APS-η + Witten-Yonekura)** |
| 5 | `IsAndersonDualSpinBulk` | `SymTFT/PinBordism.lean` | Transitive on #1 + #2 (currently `KT ∧ AD`) |
| 6 | `IsDMNOWittTrivialIffLagrangianAlgebra` | `SymTFT/LagrangianAlgebra.lean` | **W2 (MTC + Lagrangian-algebra substrate)** |
| 7 | `IsKapustinSaulinaGappedBoundary` | `SymTFT/LagrangianAlgebra.lean` | Transitive on #6 (corollary at boundary side) |
| 8 | `IsBoundarySymTFTCorrespondence` | `SymTFT/Basic.lean` | **W2** (predicate-level discharge) |
| 9 | `IsToricCodeTwoLagrangianAlgebraStructure` | `SymTFT/ToricCodeLagrangian.lean` | **C1 (toric-code substantive instance, becomes specialization of W2)** |
| 10 | `IsSKEFTHawkingSymTFTBoundary` | `SymTFT/SubstrateToBulkIdentification.lean` | **KEEP** (D-class program identity by design) |
| 11 | `IsDarkSectorTopologicalBoundary` | `SymTFT/AlternativeBoundaries.lean` | **C2 (paper-17 substantive)** |
| 12 | `IsSubstantivePinPlusSPTAsymmetry` | `APSEta/SubstrateBulkAsymmetry.lean` | Transitive on #1 + #2 + GEM bridge |

**Discharge target after Phase 6r-prime close:** 1 KEEP (#10, program identity) + 0 trivial-placeholder tracked Props. All others substantively discharged or constructively derived from substantively-discharged substrate.

### B. Mathlib4 (v4.29.1, pinned `5e932f97`) substrate-gap inventory

Per Wave 1a.1 §1.3 + §4.3 (read those sections directly; key gaps):

**PRESENT, comprehensive** (W1 + W2 can build on):
- `Mathlib.CategoryTheory.Monoidal.Center` (Drinfeld center with `BraidedCategory` instance).
- `Mathlib.CategoryTheory.Monoidal.Mon_` (`MonObj`, `Mon`, `IsCommMonObj`).
- `Mathlib.CategoryTheory.Monoidal.Comon_` (`ComonObj`).
- `Mathlib.CategoryTheory.Monoidal.Rigid.Basic` (rigid monoidal, ExactPairing, HasLeftDual/HasRightDual).
- `Mathlib.CategoryTheory.Bicategory.*` (full bicategorical layer).
- `Mathlib.AlgebraicTopology.SimplicialSet` (simplicial-set machinery for combinatorial manifold-ish content).
- `Mathlib.Geometry.Manifold.SmoothManifoldWithCorners` (smooth manifolds).
- `Mathlib.GroupTheory.QuotientGroup` (for bordism-as-quotient construction).

**ABSENT** (W1 + W2 + W3 + W4 must ship substrate in-project):
- Pin⁺ structure typeclass / Pin group reductions.
- Cobordism category (`AlgebraicTopology/Cobordism/` — does not exist).
- Pin⁺/Spin/Spin^c bordism groups.
- η-invariant of Dirac operator.
- Atiyah-Patodi-Singer index theorem.
- Anderson-dual functor for bordism spectra.
- Pivotal category (noted "future work" in Mathlib).
- Spherical category.
- Frobenius algebra in monoidal category (the `Mon_(C)`-internalized form).
- Modular Tensor Category typeclass (only braided fusion via Mathlib `BraidedCategory`).
- Frobenius-Perron dimension / S-matrix / T-matrix / Verlinde formula.
- Lagrangian algebra in non-degenerate braided fusion category.

### C. Project velocity calibration (recent ships)

| Phase | LoC | Sessions | Notes |
|---|---|---|---|
| Phase 6q DKM transport bootstrap | 2,716 LoC (11 modules) | 2 | Full substantive ship + bimodal outcome both halves |
| Phase 6r SymTFT (just shipped) | ~2,650 LoC (18 modules) | 1 | All 8 Waves + strengthening + 2-round adversarial review |
| Phase 6t Path A Option C | ~2,565 LoC (single file `SolovayKitaevPathA.lean`) | ~3 | UNCONDITIONAL strict-headline discharge of Y_h Lipschitz tightening |
| Phase 6p Wave 2c.4a-R5.4 (Cartan substrate) | ~1,900 LoC (18 commits) | Multi-session arc | F.21 unconditional discharge |
| Phase 6a Wave 7 (`LaplaceMethod.lean`) | ~500 LoC | 1-2 | Retired `gaussianSaddleAsymptotic` axiom — DIRECT PRECEDENT for "ship substrate in-project to retire tracked-Prop / axiom" |

**Calibration:** Phase 6r-prime LOE estimates below are deflated against these comparables. The W3 KT-theorem proof has the highest variance because Kirby-Taylor 1990's proof uses η-invariant on RP⁴ (not yet in Mathlib, ships in W4).

### D. Bundle absorption posture

**Same as Phase 6r**: bundle absorption HELD for unified user-authorized bundle-absorption pass. This phase ships substrate only. Documentation impact at absorption:
- Wave 2b.3 D2 reframing pre-draft (Phase 6r): consumers update from tracked-Prop hypotheses to substantively-discharged content (no statement change; cleaner proof terms).
- Wave 3b.2 flagship-F unification pre-draft (Phase 6r): same.
- Any new D4 substantive content from W2 (DMNO Lean discharge) would lift into D4 §"Drinfeld centre" subsection at the absorption pass.

### E. Submitted/Planned DR prompts (none required)

Per Wave 1a.1 + 2a.1 + 3a.1 DR returns: all needed primary-source guidance is already returned. **No new DR dispatch required for Phase 6r-prime.** All Wedges build on already-returned DR substrate.

---

## Wave catalog — Shape D (4 Wedges + 3 carryovers + integration + close-out review)

The phase is organized as four Wedges (W1-W4) covering the substantive discharge targets, plus three carryover items (C1-C3) folded into the appropriate Wedge, plus a cross-bridge integration sub-wave (W5) that updates Phase 6r consumers to use the substantively-discharged substrate, plus the dual-phase adversarial-review close-out.

**Status legend** (carried from Phase 6r):
- ✅ **SHIPPED**
- 🟡 **IN-PROGRESS**
- ⏳ **NOT STARTED**

| Wave | Codename | Status | Bundle absorption | Tracked Props discharged | User-auth gate |
|---|---|---|---|---|---|
| **W1** | Pin⁺ bordism substrate (Tier A) | ⏳ NOT STARTED | D2 + D4 additive — DEFERRED | #1 (substrate) + #2 + #3 + #5 + #12 | none |
| **W2** | MTC + Lagrangian-algebra substrate | ⏳ NOT STARTED | D4 substantive new subsection — DEFERRED | #6 + #7 + #8 (predicate-level) | none |
| **W3** | RP⁴ + Pin⁺ structure + KT theorem (Tier B + C) | ⏳ NOT STARTED | D2 substantive new subsection — DEFERRED | #1 (full discharge) | none |
| **W4** | APS-η + Witten-Yonekura inflow | ⏳ NOT STARTED | D2 + L1 additive — DEFERRED | #4 | none |
| **C1** | Toric-code two-Lagrangian-algebras concrete instance | ⏳ NOT STARTED | D4 substantive new subsection — DEFERRED | #9 (folds into W2 as specialization after W2 ships; standalone otherwise) | none |
| **C2** | Paper-17 substantive dark-sector content | ⏳ NOT STARTED | D5 + F §F.5 — DEFERRED | #11 | none |
| **C3** | Tracked-Props doc sync (`PERMANENT_TRACKED_HYPOTHESES.md`) | ⏳ NOT STARTED | n/a (documentation) | n/a | none |
| **W5** | Cross-bridge integration | ⏳ NOT STARTED | none (substrate cleanup) | wires substantively-discharged content back into Phase 6r consumers | none |
| **R** | Dual-phase adversarial review (6r + 6r-prime) | ⏳ NOT STARTED | n/a (review) | n/a | none |

**Wave dependencies:**
- W1 is independent — can start immediately.
- W2 is independent — can run in parallel with W1.
- W3 depends on W1 (needs the bordism substrate before proving the iso).
- W3 also benefits from W4 (η-invariant available for KT proof) but can ship a non-η-based path (generators-and-relations).
- W4 depends on W1 (uses `Omega4PinPlus` + `TP5PinPlus` types).
- C1 can ship standalone OR as W2 specialization (more elegant after W2).
- C2 can ship anytime (independent).
- C3 should land last (catalogues final state).
- W5 depends on W1 + W2 + W3 + W4 + C1 + C2 (updates all consumers).
- R depends on everything (final review).

**Recommended sequencing (parallel-where-possible):**

1. **C3 first (~30-60 min)** — sync tracked-Props doc to current Phase 6r state BEFORE Phase 6r-prime starts modifying things. This locks in the "before" state for review.
2. **C2 in parallel (~1-3 sessions)** — paper-17 substantive content can ship anytime; orthogonal to W1-W4. Schedule independently or as W2 follow-on.
3. **W1 + W2 in parallel (~11-30 sessions combined)** — bordism substrate AND MTC + Lagrangian-algebra substrate.
4. **W4 after W1 ships (~5-8 sessions)** — APS-η + Witten-Yonekura inflow. Needs `Omega4PinPlus` + `TP5PinPlus` types.
5. **W3 after W1 + W4 ship (~15-40 sessions)** — KT theorem proof. Needs both bordism substrate (W1) and η-invariant (W4).
6. **C1 after W2 ships (~1-3 sessions)** — toric-code two-Lagrangian-algebras concrete instance via the new MTC + Lagrangian-algebra substrate.
7. **W5 after all of W1-W4 + C1-C2 ship (~3-5 sessions)** — cross-bridge integration. Updates all Phase 6r consumers to use substantively-discharged content; verifies no consumer breaks.
8. **R (dual-phase 6r + 6r-prime adversarial review, 2-3 rounds, ~2-4 sessions)** — final review across BOTH phases jointly. Verifies all tracked Props except #10 are substantively discharged (or constructively derived) and that BLOCKER-2 from Phase 6r adversarial review round 1 is fully closed.

**Total Phase 6r-prime LOE:** ~30-100 sessions (~2-7 program-PMs deflated). Comparable to Phase 6q + 6r + 6t in series. The W3 KT-theorem proof has the highest variance; if W3 substrate proof proves intractable, W3 can ship the substrate-and-axiomatized-conclusion form (~10-15 sessions for W1 + W3-substrate-only) with the KT theorem itself remaining a tracked Prop. This is documented as an explicit "W3 fallback path" in the W3 section below.

**Pre-Phase-7 bundle absorption gate:** Phase 6r-prime substrate ships → joint Phase 6r + 6r-prime bundle-absorption pass at unified Phase-7 event. **HELD for user authorization.**

---

## Wave W1 — Pin⁺ bordism substrate (Tier A) ⏳ NOT STARTED

**Status:** Decomposed into 6 components C1-C6 per the post-6r tracked-Props discharge audit. Ships **Tier A only** here (components C1-C3 + Anderson-dual functor); Tier B + C ship in W3.

**Discharge target after W1 close:** tracked Props #1 (substrate-meaningful), #2 (derived), #3 (transitive), #5 (transitive), #12 (transitive).

**Sub-wave decomposition (proposed):**

- **Wave W1.1** (Pin⁺ structure typeclass + manifold abstraction):
  - `lean/SKEFTHawking/SymTFT/PinPlusStructure.lean` — `PinPlusStructure (M : Type*) : Class`. Axiomatized as a typeclass with no required content at the predicate-substrate level; the structure data is opaque.
  - `lean/SKEFTHawking/SymTFT/ManifoldAbstraction.lean` — opaque `Manifold4` / `Manifold5` types with disjoint-union operation.
  - LoC estimate: ~250-400.

- **Wave W1.2** (Pin⁺ bordism equivalence relation):
  - `lean/SKEFTHawking/SymTFT/PinPlusBordism.lean` — `IsPinPlusBordant : Manifold4 → Manifold4 → Prop` defined via existence of a Pin⁺ 5-manifold with appropriate boundary structure. Setoid + Quotient instance.
  - LoC estimate: ~300-500.

- **Wave W1.3** (`Omega4PinPlus` substantive definition):
  - Refactor `lean/SKEFTHawking/SymTFT/PinBordism.lean`:
    - Replace `def Omega4PinPlus : Type := ZMod 16` (placeholder) with `def Omega4PinPlus := Quotient PinPlusBordism4Setoid`.
    - Establish `AddCommGroup Omega4PinPlus` via disjoint-union operation passed through the quotient.
    - Re-state `IsKirbyTaylorPinPlusBordism : Prop := Nonempty (Omega4PinPlus ≃+ ZMod 16)`. **NOW SUBSTANTIVE** — the `Omega4PinPlus` type is non-trivial, so the isomorphism claim is a real mathematical statement (currently still axiomatized but with substantive content; full discharge in W3).
  - LoC estimate: ~250-400 (delta from current PinBordism.lean).

- **Wave W1.4** (Anderson-dual functor for #2):
  - `lean/SKEFTHawking/SymTFT/AndersonDual.lean` — generic Anderson-dual functor `IZOmega : (n : ℕ) → BordismGroup n → Type` computing `Hom(Ω_n, ℝ/ℤ) ⊕ Ext(Ω_{n+1}, ℤ)`.
  - Specialize: `TP5PinPlus := IZOmega 5 PinPlus`. Derive `TP5PinPlus ≃+ ZMod 16` from `Omega4PinPlus ≃+ ZMod 16` + `Omega5PinPlus ≃+ 0` via the Anderson-dual formula.
  - **`IsAndersonDualPinPlus`** becomes a transitive consequence of `IsKirbyTaylorPinPlusBordism` + the `Omega5PinPlus = 0` companion tracked Prop.
  - LoC estimate: ~300-500.

**Three-question template:**

- *Integrates with:* Phase 6r `SymTFT/PinBordism.lean` (target of refactor); Mathlib `Mathlib.GroupTheory.QuotientGroup` (for the quotient construction); Mathlib `AddCommGroup` substrate; Phase 6o `Schellekens/SpinBordism.lean` (sibling substrate pattern; review for consistency).
- *New constraint adds:* substantive Pin⁺ bordism Type with quotient structure; non-trivial `Omega4PinPlus` (no longer `ZMod 16` placeholder); Anderson-dual functor as derived construction.
- *Tension surfaces:* (i) the Pin⁺ structure typeclass needs a concrete model OR an axiomatized opaque type — discipline choice; opaque type with primary-source-cited axiomatization is consistent with existing project pattern; (ii) the bordism equivalence relation requires "Pin⁺ 5-manifold with boundary" — needs `Manifold5` with appropriate boundary-typeclass, which is the heaviest substrate construction.

**Substrate.** Mathlib `Setoid` + `Quotient`; project's `WittClass.lean` pattern (analogous `ZMod 24` substrate); project's `RingQuot` patterns (Uqsl2).

**Module decomposition (Lean):**
```
SKEFTHawking/SymTFT/
  ├── PinPlusStructure.lean      -- W1.1: Pin⁺ structure typeclass (~150-250 LoC)
  ├── ManifoldAbstraction.lean   -- W1.1: opaque Manifold4/Manifold5 + disjoint union (~150-250 LoC)
  ├── PinPlusBordism.lean        -- W1.2: bordism Setoid + quotient (~300-500 LoC)
  ├── AndersonDual.lean          -- W1.4: Anderson-dual functor + specialization (~300-500 LoC)
  └── PinBordism.lean            -- W1.3: REFACTOR, point Omega4PinPlus + TP5PinPlus at substrate
```

**Bundle absorption.** D2 + D4 additive subsections (substrate content); HELD for unified bundle-absorption pass.

**Risk axes.**
- Pin⁺ structure typeclass design: concrete-model vs opaque-axiomatized. Opaque-axiomatized matches project convention (`Schellekens/SpinBordism.lean` pattern).
- The bordism equivalence relation requires careful disjoint-union + boundary handling. May need bespoke `Manifold5WithBoundary` substrate.
- After W1 close, `IsKirbyTaylorPinPlusBordism` is substantively meaningful but the ISO ITSELF is still axiomatized (until W3 ships).

**LOE estimate (program-velocity deflated):** 5-10 sessions, ~1.0-1.6k LoC total across 4-5 new modules + 1 refactor.

---

## Wave W2 — MTC + Lagrangian-algebra substrate ⏳ NOT STARTED

**Status:** Decomposed into 5 sub-waves per Wave 1a.1 §5.2 build estimate (~1.8-2.6k LoC at predicate level). Ships substantively-discharged DMNO 2010 + Kapustin-Saulina + boundary-SymTFT correspondence.

**Discharge target after W2 close:** tracked Props #6 (substantively discharged), #7 (transitive corollary of #6 at the boundary side), #8 (predicate-level discharged at the correspondence-statement level).

**Per Wave 1a.1 §5.2 build estimate:**

```
| Component                                               | Est. LoC |
|---------------------------------------------------------|----------|
| FrobeniusAlgebra (refactor: predicate → substantive)    | 250-350  |
| CommFrobeniusAlgebra (commutative case)                 | 80-120   |
| SeparableAlgebra                                        | 150-200  |
| EtaleAlgebra                                            | 50       |
| LagrangianAlgebra (refactor + FPdim infrastructure)     | 400-600  |
| Local-module category LocMod A + equivalence            | 500-700  |
| Total                                                   | 1.8k-2.6k|
```

**Sub-wave decomposition (proposed):**

- **Wave W2.1** (Frobenius-algebra substantive ship):
  - Refactor `lean/SKEFTHawking/SymTFT/FrobeniusAlgebra.lean`:
    - Strengthen `IsFrobeniusAlgebra X` body from the current 2-equation Frobenius compatibility to a full structural-algebra/coalgebra interaction theorem with helper lemmas.
    - Add `IsCommFrobeniusAlgebra` substantive content (commutativity under braiding).
    - Add separable-algebra explicit splitting witness.
  - Goal: `IsCommFrobeniusAlgebra` becomes substantively non-trivial; constructive examples ship (`commutativeMonoid → CommFrobeniusAlgebra` style functors).
  - LoC estimate: ~400-600.

- **Wave W2.2** (Frobenius-Perron dimension + non-degenerate braided fusion):
  - `lean/SKEFTHawking/SymTFT/FrobeniusPerronDim.lean` — FPdim infrastructure on objects of a braided fusion category. Axiomatized at the predicate-substrate level (since full FPdim requires modular tensor category infrastructure not in Mathlib), but with substantive structural content.
  - `lean/SKEFTHawking/SymTFT/NonDegBraidedFusion.lean` — substantive `NonDegBraidedFusionCategory C` predicate. Currently `IsNonDegBraidedFusion B := Is3DTQFTBraided B` (P2 redundancy per Phase 6r REQUIRED-3); this sub-wave strengthens to require S-matrix invertibility / Müger center triviality at the predicate-substrate level.
  - LoC estimate: ~400-600.

- **Wave W2.3** (Lagrangian-algebra substantive predicate + DMNO discharge):
  - Refactor `lean/SKEFTHawking/SymTFT/LagrangianAlgebra.lean`:
    - Strengthen `IsLagrangianAlgebra L` body to require: (a) `IsCommFrobeniusAlgebra L` substantively, (b) `IsConnectedAlgebra L` with non-trivial content (no non-trivial idempotents in End(L)), (c) `IsSeparableAlgebra L` with explicit section witness, (d) FPdim condition `FPdim(L)² = FPdim(C)` (using W2.2 substrate).
    - Substantively discharge `IsDMNOWittTrivialIffLagrangianAlgebra B` — replace the current `:= Is3DTQFTBraided B` body with the actual biconditional content using the new MTC + FPdim + Lagrangian-algebra substrate.
  - LoC estimate: ~500-800.

- **Wave W2.4** (Kapustin-Saulina + gapped-boundary substantive discharge):
  - Refactor `lean/SKEFTHawking/SymTFT/GappedBoundary.lean`:
    - Strengthen `HasLagrangianAlgebra B` from `:= Is3DTQFT B` to require existence of a substantive `IsLagrangianAlgebra L` for some `L`.
    - Substantively discharge `IsKapustinSaulinaGappedBoundary B` as a corollary of the new DMNO substrate (the boundary-side characterization of Lagrangian algebras).
  - Refactor `lean/SKEFTHawking/SymTFT/Basic.lean`:
    - Strengthen `IsBoundarySymTFTCorrespondence B` from `:= Is3DTQFT B` to require the full bulk-boundary biconditional at the predicate-substrate level (using W2.3 substrate).
  - LoC estimate: ~300-500.

- **Wave W2.5** (Bulk-boundary correspondence substantive Lean theorem):
  - Refactor `lean/SKEFTHawking/SymTFT/BulkBoundaryCorrespondence.lean`:
    - The Phase 6r adversarial-review BLOCKER-2 (`witt_triviality_iff_has_lagrangian_algebra` as predicate-substrate tautology) is **substantively closed here**. After W2.3, both sides of the biconditional are non-trivially distinct; the proof becomes a real theorem rather than `intro h; exact h`.
    - Update `wave_1d_bulk_boundary_correspondence_closure` to use substantively-discharged Lemma chain.
  - LoC estimate: ~200-300.

**Three-question template:**

- *Integrates with:* Phase 6r `SymTFT/` modules (target of refactors); Mathlib `Mon_/Comon_/Hopf_` (substrate); existing `SymTFTAudit/` substrate (`PseudoUnitary.lean` for related predicates); paper-9 substrate (`CenterFunctorZ2.lean`, `S3CenterAnyons.lean`).
- *New constraint adds:* substantive Frobenius / commutative-Frobenius / Lagrangian-algebra Lean predicates + FPdim infrastructure + DMNO biconditional substantively discharged.
- *Tension surfaces:* (i) FPdim requires modular tensor category infrastructure Mathlib lacks — substrate scout dispositive on how much we ship in-project; (ii) DMNO 2010 substantive proof requires significant categorical algebra; the substantive ship may stop at the biconditional STATEMENT being meaningful, with the forward/backward directions still requiring tracked-Prop hypotheses (this is a refined ship: substantive statement + tracked-Prop proof; better than current).

**Substrate.** Mathlib `Mon_/Comon_/CommMon_`; Phase 6r `FrobeniusAlgebra.lean` (target of refactor); Wave 1a.1 §5.2 build plan.

**Module decomposition (Lean):**
```
SKEFTHawking/SymTFT/
  ├── FrobeniusAlgebra.lean         -- W2.1 REFACTOR substantive
  ├── FrobeniusPerronDim.lean       -- W2.2 NEW
  ├── NonDegBraidedFusion.lean      -- W2.2 NEW
  ├── LagrangianAlgebra.lean        -- W2.3 REFACTOR substantive (discharges #6)
  ├── GappedBoundary.lean           -- W2.4 REFACTOR (discharges #7)
  ├── Basic.lean                    -- W2.4 REFACTOR (strengthens #8 body)
  └── BulkBoundaryCorrespondence.lean  -- W2.5 REFACTOR substantive
```

**Bundle absorption.** D4 substantive new "Lagrangian-algebra boundary substrate" subsection at bundle-absorption pass.

**Risk axes.**
- FPdim infrastructure is the heaviest substrate piece; may need to ship at predicate level only.
- DMNO 2010 substantive proof is mathematically deep; W2.3 may need to stop at "statement substantive, both directions tracked-Prop" rather than full discharge.
- After W2 close: BLOCKER-2 from Phase 6r adversarial review is automatically closed via substantive substrate.

**LOE estimate (program-velocity deflated):** 6-20 sessions, ~1.8-2.8k LoC total across 7 modules (4 new + 3 refactors).

---

## Wave W3 — RP⁴ + Pin⁺ structure + Kirby-Taylor theorem (Tier B + C) ⏳ NOT STARTED

**Status:** The most ambitious wave. Ships the substantive proof of `Ω_4^{Pin⁺}(pt) ≅ ℤ/16` via either (Path α) η-invariant on RP⁴ + Atiyah-Hirzebruch spectral sequence, or (Path β) direct generators-and-relations calculation.

**Discharge target after W3 close:** tracked Prop #1 **fully discharged** (constructive proof of the iso). Companion tracked Prop `Omega5PinPlus ≃+ PUnit` (Ω_5^{Pin⁺}(pt) = 0) also discharged as part of the proof.

**Sub-wave decomposition (proposed):**

- **Wave W3.1** (Concrete RP⁴ construction):
  - `lean/SKEFTHawking/SymTFT/RP4.lean` — `RP4 : Type` via `Sphere 4 / antipodal` quotient construction. Establish `RP4 : Manifold4` instance.
  - Use Mathlib `Mathlib.Topology.Sphere` + quotient-by-group-action substrate.
  - LoC estimate: ~300-500.

- **Wave W3.2** (Canonical Pin⁺ structure on RP⁴):
  - `lean/SKEFTHawking/SymTFT/RP4PinPlus.lean` — the canonical `PinPlusStructure RP4` instance. The Pin⁺ structure exists because RP⁴ has w₂(RP⁴) = w₁(RP⁴)² (the Pin⁺ obstruction).
  - LoC estimate: ~200-400.

- **Wave W3.3** (KT theorem — Path α: η-invariant approach):
  - **Prerequisite:** W4 must ship first (provides η-invariant primitive).
  - `lean/SKEFTHawking/SymTFT/KirbyTaylor.lean` — compute η(RP⁴ Pin⁺) = 1/16 + integers; deduce [RP⁴] has order 16 in Ω_4^{Pin⁺}; use Atiyah-Hirzebruch spectral sequence (or simpler degree-4 calculation) to show ℤ/16 is sharp.
  - LoC estimate: ~600-1500.
  - **OR**

- **Wave W3.3-alt** (KT theorem — Path β: direct generators-and-relations):
  - Skip η-invariant. Directly compute Ω_4^{Pin⁺}(pt) via:
    - Pin⁺ bordism long exact sequence with Spin bordism.
    - `Ω_4^{Spin}(pt) ≅ ℤ` (signature theorem).
    - The Pin⁺/Spin reduction maps ℤ → ℤ/16.
  - This is the Kirby-Taylor approach in their original 1990 paper.
  - LoC estimate: ~400-1000.

- **Wave W3.4** (Discharge):
  - Refactor `lean/SKEFTHawking/SymTFT/PinBordism.lean`:
    - Promote `IsKirbyTaylorPinPlusBordism` from tracked Prop to **proved theorem**.
    - Update consumers to use the proved version.
  - LoC estimate: ~100-200.

**Three-question template:**

- *Integrates with:* W1 substrate (PinPlusBordism + Omega4PinPlus); W4 substrate (η-invariant — for Path α); Mathlib `Mathlib.Topology.Sphere`; classical algebraic topology infrastructure as it lands in Mathlib.
- *New constraint adds:* full substantive proof of the Kirby-Taylor 1990 theorem in Lean 4. **First formalization of any Pin⁺ bordism group in any proof assistant** (per Wave 1a.1 §6 cross-prover survey).
- *Tension surfaces:* (i) Path α vs Path β trade-off — Path α has higher elegance but requires W4 substrate; Path β is self-contained but requires bordism long-exact-sequence machinery; (ii) significant variance in LoC + sessions; (iii) **W3 has a documented fallback path**: if substantive proof proves intractable, ship W1 + W2 + W4 + integration only and leave #1 as a tracked Prop with the substantive substrate behind it (currently the W1-tier ship plan).

**Substrate.** W1 (PinPlusBordism + Omega4PinPlus types); W4 (η-invariant, for Path α); Mathlib `Sphere` + algebraic topology.

**Module decomposition (Lean):**
```
SKEFTHawking/SymTFT/
  ├── RP4.lean                   -- W3.1 NEW
  ├── RP4PinPlus.lean            -- W3.2 NEW
  ├── KirbyTaylor.lean           -- W3.3 NEW (Path α OR β)
  └── PinBordism.lean            -- W3.4 REFACTOR (promote IsKT to theorem)
```

**Bundle absorption.** D2 substantive new "Pin⁺ Z₁₆ Kirby-Taylor 1990 — Lean discharge" subsection at bundle-absorption pass. Major flagship-F content (first proof-assistant Pin⁺ bordism formalization).

**Risk axes.**
- Highest variance of all Phase 6r-prime waves.
- W3.3 may need to stop at "partial discharge — Pin⁺/Spin reduction shown, full iso requires AHSS" if AHSS substrate proves intractable.
- **Fallback path documented**: ship W1 + W2 + W4 only, leave #1 + W3 deferred to a separate later phase (Phase 6r-prime' or Phase 7+).

**LOE estimate (program-velocity deflated):** 15-40 sessions, ~1.2-3.0k LoC across 4 modules. If Path β chosen: 15-30 sessions. If Path α chosen: 25-40 sessions (more substrate, but more reusable).

---

## Wave W4 — APS-η + Witten-Yonekura inflow ⏳ NOT STARTED

**Status:** Ships APS η-invariant primitive substrate in SKEFTHawking + substantive Witten-Yonekura inflow proof. Discharges #4. Enables W3 Path α.

**Discharge target after W4 close:** tracked Prop #4 substantively discharged.

**Sub-wave decomposition (proposed):**

- **Wave W4.1** (APS η-invariant primitive):
  - `lean/SKEFTHawking/SymTFT/EtaInvariant.lean` — η-invariant of Dirac operator on a closed manifold with structure. Axiomatized at the predicate-substrate level (since full Atiyah-Patodi-Singer index theorem requires elliptic-operator infrastructure Mathlib lacks), but with substantive structural content matching the η-invariant axiomatics.
  - Functor: `(M : Manifold) → (D : DiracOperator M) → η(M, D) : ℝ`.
  - Substrate axiomatization: `η` is reflection-positive, bordism-invariant mod ℤ, additive under disjoint union.
  - LoC estimate: ~400-600.

- **Wave W4.2** (Anderson-dual / invertible-TFT framework via η):
  - `lean/SKEFTHawking/SymTFT/AndersonDualTFT.lean` — `IsInvertibleTFT (B : Type*) : Prop` predicate; the bulk's partition function on closed `D`-manifold equals `exp(2πi · η/16)` for Pin⁺ in `D = 5`.
  - Cross-bridge to `AndersonDual.lean` (W1.4): the Pin⁺ deformation class IS the η-invariant mod ℤ.
  - LoC estimate: ~300-500.

- **Wave W4.3** (Witten-Yonekura inflow substantive discharge):
  - Refactor `lean/SKEFTHawking/SymTFT/PinBordism.lean`:
    - Strengthen `IsWittenYonekuraInflow s` body from `:= IsKirbyTaylorPinPlusBordism ∧ IsAndersonDualPinPlus` to the full substantive inflow statement: the boundary anomaly EQUALS the bulk Pin⁺ partition function evaluated at η/16 mod 1.
    - Prove `isWittenYonekuraInflow_holds` substantively using W4.1 + W4.2.
  - LoC estimate: ~200-400.

**Three-question template:**

- *Integrates with:* W1 substrate (PinPlusBordism + Anderson-dual); Phase 6r `PinBordism.lean` (target of refactor); Phase 6o `APSEta/*` (sibling APS-η placeholders — review for consistency).
- *New constraint adds:* APS η-invariant primitive + Anderson-dual invertible-TFT framework + Witten-Yonekura inflow substantive proof.
- *Tension surfaces:* (i) Full APS index theorem requires significant elliptic-operator substrate Mathlib lacks; W4.1 ships axiomatized primitive with structural content; (ii) Witten-Yonekura inflow is a computational identity once the framework is in place — the substantive content is in the framework, not the identity.

**Substrate.** W1 substrate (PinPlusBordism + Anderson-dual); Phase 6r `PinBordism.lean` (target of refactor); Phase 6o `APSEta/*` (sibling placeholders).

**Module decomposition (Lean):**
```
SKEFTHawking/SymTFT/
  ├── EtaInvariant.lean         -- W4.1 NEW
  ├── AndersonDualTFT.lean      -- W4.2 NEW
  └── PinBordism.lean           -- W4.3 REFACTOR (discharge #4 substantively)
```

**Bundle absorption.** D2 + L1 additive subsections (substrate content); HELD for unified bundle-absorption pass.

**Risk axes.**
- APS η-invariant infrastructure is non-trivial substrate; W4.1 may ship as axiomatized primitive only (with substantive structural content).
- Witten-Yonekura inflow substantive proof depends on W4.1 + W4.2 framework being adequate.

**LOE estimate (program-velocity deflated):** 5-8 sessions, ~900-1500 LoC across 3 modules (2 new + 1 refactor).

---

## Carryover C1 — Toric-code two-Lagrangian-algebras concrete instance ⏳ NOT STARTED

**Status:** Ships the substantive content of `IsToricCodeTwoLagrangianAlgebraStructure` (#9). Per Wave 1a.1 §5.3: "would be the **first known proof-assistant formalization of the Lagrangian-algebra / gapped-boundary correspondence for toric code** — a concrete, citable Phase 6r-prime contribution."

**Discharge target after C1 close:** tracked Prop #9 substantively discharged.

**Sequencing:** C1 can ship standalone (~1-3 sessions) OR fold into W2 as a specialization (more elegant after W2.3 LagrangianAlgebra substrate ships). Recommend **C1 as W2 follow-on** to leverage the new MTC + Lagrangian-algebra infrastructure.

**Sub-wave decomposition (proposed):**

- **Carryover C1.1** (Concrete electric Lagrangian algebra):
  - Refactor `lean/SKEFTHawking/SymTFT/ToricCodeLagrangian.lean`:
    - Define `lagrangian_electric : Object (Center (Discrete (ZMod 2)))` as `𝟙 ⊕ e` with explicit `MonObj` + `ComonObj` + `IsCommFrobeniusAlgebra` instances.
    - Define `lagrangian_magnetic : Object (Center (Discrete (ZMod 2)))` as `𝟙 ⊕ m` symmetrically.
  - LoC estimate: ~200-400.

- **Carryover C1.2** (Two-algebras classification theorem):
  - `theorem toricCode_two_lagrangian : ∀ L : LagrangianAlgebra toricCodeMTC, L ≃ lagrangian_electric ∨ L ≃ lagrangian_magnetic`.
  - LoC estimate: ~100-200.

- **Carryover C1.3** (Discharge `IsToricCodeTwoLagrangianAlgebraStructure`):
  - Refactor `IsToricCodeTwoLagrangianAlgebraStructure` from current `:= IsBoundarySymTFTCorrespondence toricCodeBulk` to the substantive predicate "there exist exactly two Lagrangian-algebra structures up to equivalence."
  - LoC estimate: ~50-100.

**Substrate.** Project's `CenterFunctorZ2.lean` (Z₂ Drinfeld double substrate); W2.3 (Lagrangian-algebra substantive predicate); Mathlib `Discrete (ZMod 2)` + `Center`.

**Module decomposition (Lean):**
```
SKEFTHawking/SymTFT/
  └── ToricCodeLagrangian.lean      -- C1.1-3 REFACTOR substantive
```

**Bundle absorption.** D4 substantive new "Toric-code two-Lagrangian-algebra structure" subsection. First proof-assistant Lagrangian-algebra / gapped-boundary correspondence for toric code per Wave 1a.1 §5.3.

**Risk axes.**
- Depends on W2.3 substrate (otherwise C1 ships standalone with ~more substrate work).
- The two-algebras classification (C1.2) requires careful equivalence-of-Frobenius-algebras handling — may need bespoke equivalence machinery.

**LOE estimate (program-velocity deflated):** 1-3 sessions (after W2.3 ships), ~350-700 LoC. Standalone: 3-5 sessions, ~600-1000 LoC.

---

## Carryover C2 — Paper-17 substantive dark-sector content ⏳ NOT STARTED

**Status:** Ships substantive content of `IsDarkSectorTopologicalBoundary` (#11). Per Wave 3a.1 §Recommendations 5: "**HOLD** on Wave 3b.1 dark-sector cross-bridge until paper 17 is read directly." Now unblocked since paper 17 IS readable (860 lines at `papers/paper17_dark_sector/paper_draft.tex`).

**Discharge target after C2 close:** tracked Prop #11 substantively discharged.

**Sequencing:** C2 is independent of W1-W4. Can ship anytime; recommend after W2 + C1 ship for consistency with Lagrangian-algebra-label framing.

**Sub-wave decomposition (proposed):**

- **Carryover C2.1** (Paper-17 substantive read + working doc):
  - Read `papers/paper17_dark_sector/paper_draft.tex` end-to-end (860 lines).
  - Working doc at `temporary/working-docs/phase6r-prime/c2_paper17_substantive.md` capturing: (a) dark-sector physics content (hidden ℤ/16 sector + sterile νR + fracton DM + SFDM), (b) which content maps to "alternative Lagrangian-algebra boundary" framing, (c) tracked-Prop discharge plan.
  - LOE estimate: ~30-60 min for read; ~30-60 min for working doc.

- **Carryover C2.2** (Substantive `IsDarkSectorTopologicalBoundary`):
  - Refactor `lean/SKEFTHawking/SymTFT/AlternativeBoundaries.lean`:
    - Strengthen `IsDarkSectorTopologicalBoundary s` body from current predicate-substrate marker to substantive content tying to paper-17's dark-sector substrate predicates (e.g., hidden-ℤ/16-sector requirement + sterile-νR consistency).
    - Substantive theorem: SM-vs-dark-sector boundaries correspond to electric vs magnetic Lagrangian-algebra labels (per Wave 3a.1 §Q3(b)).
  - LoC estimate: ~150-300.

- **Carryover C2.3** (Cross-bridge to D5 paper-17 substrate):
  - Cross-bridge from `lean/SKEFTHawking/SymTFT/AlternativeBoundaries.lean` to existing paper-17 substrate modules (`HiddenSectorClassification.lean`, `FractonDarkMatter.lean`, `SFDMMergerForecast.lean`, etc.) at the predicate level.
  - LoC estimate: ~100-200.

**Three-question template:**

- *Integrates with:* `papers/paper17_dark_sector/paper_draft.tex` (substantive source); Phase 5x dark-sector Lean substrate (HiddenSectorClassification, FractonDarkMatter, FangGuTorsionDM, etc.); Phase 6r `AlternativeBoundaries.lean` (target of refactor).
- *New constraint adds:* substantive paper-17 cross-bridge in Lean; substantive dark-sector boundary predicate replacing predicate-substrate marker.
- *Tension surfaces:* (i) Paper 17 is comprehensive — the cross-bridge needs to be selective about which dark-sector content maps to the SymTFT-boundary framing; (ii) the electric/magnetic Lagrangian-algebra label correspondence is the program-original synthesis claim — appropriate hedging required.

**Substrate.** Paper 17 itself; Phase 5x dark-sector Lean modules.

**Module decomposition (Lean):**
```
SKEFTHawking/SymTFT/
  └── AlternativeBoundaries.lean    -- C2.2-3 REFACTOR substantive
```

**Bundle absorption.** D5 + F §F.5 (dark-sector subsection) additive content at bundle-absorption pass.

**Risk axes.**
- Paper 17 substantive content may not cleanly map to electric/magnetic Lagrangian-algebra labels — the framing may need adjustment.
- Dependencies on Phase 5x substrate modules may surface inconsistencies.

**LOE estimate (program-velocity deflated):** 1-3 sessions, ~250-500 LoC + ~30-60 min paper-17 read.

---

## Carryover C3 — Tracked-Props doc sync (`PERMANENT_TRACKED_HYPOTHESES.md`) ⏳ NOT STARTED

**Status:** Ships documentation update for the 12 Phase 6r tracked Props with discharge-status field per entry. Lock in the "before" state for Phase 6r-prime adversarial review.

**Discharge target after C3 close:** documentation hygiene.

**Sub-wave decomposition:**

- **Carryover C3** (single session): add 12 entries to `docs/PERMANENT_TRACKED_HYPOTHESES.md` following the existing format. Each entry: name, file:line, statement, what-the-Prop-says, anchor + falsifiers (if applicable), underlying-physics-status, why-KEEP-or-DISCHARGEABLE, consumers, reassessment trigger, discharge-status (NEW field for Phase 6r-prime tracking).

**Substrate.** Existing format from `H_VestigialModeIsGraviton` entry (well-documented in current `PERMANENT_TRACKED_HYPOTHESES.md`).

**Bundle absorption.** n/a (documentation).

**LOE estimate:** 30-60 minutes.

---

## Wave W5 — Cross-bridge integration ⏳ NOT STARTED

**Status:** Updates Phase 6r consumers to use substantively-discharged substrate from W1-W4 + C1-C2. Verifies no consumer breaks.

**Discharge target after W5 close:** all Phase 6r consumers point at substantively-discharged content; build + warnings clean; no orphaned tracked-Prop hypotheses.

**Sub-wave decomposition (proposed):**

- **Wave W5.1** (Consumer audit):
  - Trace every consumer of the 12 tracked Props in Phase 6r modules + downstream.
  - Generate audit table at `temporary/working-docs/phase6r-prime/w5_consumer_audit.md`.

- **Wave W5.2** (Consumer refactor):
  - For each consumer: update from tracked-Prop hypothesis to substantively-discharged content where possible.
  - Update docstrings to reflect post-discharge state.
  - LoC estimate: ~300-500 across all consumer files.

- **Wave W5.3** (Build + warning audit):
  - Verify `lake build SKEFTHawking` clean with zero warnings in any Phase 6r or Phase 6r-prime module.
  - Run `lake build SKEFTHawking.ExtractDeps` to refresh `lean_deps.json`.

**Substrate.** All of W1 + W2 + W3 + W4 + C1 + C2.

**Module decomposition (Lean):** consumer refactors across all Phase 6r modules.

**Bundle absorption.** n/a (substrate cleanup).

**LOE estimate (program-velocity deflated):** 3-5 sessions, ~300-500 LoC delta.

---

## Wave R — Dual-phase adversarial review (6r + 6r-prime) ⏳ NOT STARTED

**Status:** Final review of both Phase 6r and Phase 6r-prime jointly. The phase doesn't close until R-round is GREEN.

**Sub-wave decomposition (proposed):**

- **R.1** (Round 1 — dual-phase adversarial review):
  - Dispatch `feature-dev:code-reviewer` agent (or equivalent) with the **combined Phase 6r + 6r-prime module set** (Phase 6r 18 modules + Phase 6r-prime ~20-25 new modules) for adversarial review.
  - Same 3-tier framework as Phase 6r: BLOCKER / REQUIRED / ADVISORY.
  - Specifically verify: BLOCKER-2 from Phase 6r round 1 is CLOSED via W2 substantive ship; round-2 NEW-ADVISORY-1 (dead `hDMNO`) is CLOSED; all 11 tracked Props except #10 are substantively discharged or constructively derived; no new tracked Props introduced inadvertently.

- **R.2** (Round 1 remediation): fix all BLOCKERs + REQUIREDs.

- **R.3** (Round 2 — re-verification): re-dispatch reviewer; verify all round-1 findings closed; scan for new issues from remediations.

- **R.4** (Round 2 remediation if needed): fix any new findings.

- **R.5** (Final close): write joint Phase 6r + 6r-prime adversarial review reports at `temporary/working-docs/phase6r-prime/dual_phase_adversarial_review_round{1,2}.md`.

**Discharge target after R close:** GREEN verdict on combined Phase 6r + 6r-prime substantive substrate; phase ready for unified bundle-absorption pass.

**LOE estimate (program-velocity deflated):** 2-4 sessions for review + remediation cycles.

---

## User authorization gates — consolidated

| Wave | Authorization point | Authorization required for | Status |
|---|---|---|---|
| **W3** | Path α vs Path β choice | YES — algorithmic decision (η-invariant approach vs direct generators-and-relations); both viable | 🔒 **OPEN** for user decision at W3 start |
| **W3 fallback** | If W3 substantive proof intractable | YES — decision to ship W1 + W2 + W4 + integration only and defer W3 KT proof to a separate phase | 🔒 **CONDITIONAL** at W3 close |
| **Bundle absorption** | Joint Phase 6r + 6r-prime D.3 absorption event | **YES — D.3 user-authorization required** at unified bundle-absorption pass | 🔒 **HELD** for unified bundle-absorption pass |

---

## Phase 6r-prime internal further-deferred tracks

- **Full APS index theorem in Mathlib upstream** — Phase 6r-prime W4 ships axiomatized APS η-invariant primitive with substantive structural content; full APS index theorem requires multi-PM elliptic-operator infrastructure that genuinely is multi-year community work. Track for Mathlib upstream coordination.
- **Modular Tensor Category typeclass in Mathlib upstream** — Phase 6r-prime W2 ships in-project FPdim + Lagrangian-algebra substrate; full MTC typeclass for Mathlib upstream PR is a follow-up coordination event after W2 ships and stabilizes.
- **Full cobordism category in Mathlib upstream** — out of scope for Phase 6r-prime; remains tracked at multi-year community-coordination horizon.

---

## Cross-references

- `docs/roadmaps/Phase6r_Roadmap.md` — predecessor phase (substrate target of this phase's discharge work).
- `temporary/working-docs/phase6r/wave_1a_SymTFT_substrate.md` — Phase 6r working doc with tracked-Props catalog.
- `temporary/working-docs/phase6r/adversarial_review_round{1,2}.md` — Phase 6r adversarial review reports (motivation for W2 substantive discharge).
- `Lit-Search/Phase-6r/Phase 6r Wave 1a.1 — SymTFT 2024–2026 Substrate Deep Research Return.md` — substrate-tractability calibration (W1 + W2 LOE basis).
- `Lit-Search/Phase-6r/wave_2a_spin_SymTFT_fermionic_extension_return.md` — Pin⁺ Z₁₆ + Anderson-dual specifics (W1 + W4 substrate basis).
- `Lit-Search/Phase-6r/wave_3a_SM_matter_topological_boundary_return.md` — DMNO 2010 + Bhardwaj-Copetti-Pajer-Schäfer-Nameki anchor specifics (W2 substrate basis).
- `docs/PERMANENT_TRACKED_HYPOTHESES.md` — target of C3 update.
- `papers/paper17_dark_sector/paper_draft.tex` — target of C2 substantive read.
- Primary sources:
  - Kirby-Taylor 1990 (Comment. Math. Helv. 65 (1990) 434) — W3 KT theorem
  - Freed-Hopkins arXiv:1604.06527 — W4 Anderson-dual / invertible-TFT framework
  - Witten-Yonekura arXiv:1909.08775 — W4 anomaly inflow + η-invariant
  - Davydov-Müger-Nikshych-Ostrik arXiv:1009.2117 — W2 DMNO biconditional
  - Davydov-Nikshych-Ostrik arXiv:1109.5558 — W2 Ising-Witt-subgroup ≅ ℤ/16
  - Kapustin-Saulina arXiv:1008.0654 — W2 gapped boundary correspondence
  - Fuchs-Schweigert-Valentino arXiv:1203.4568 — W2 MTC-level refinement
  - Bhardwaj-Copetti-Pajer-Schäfer-Nameki arXiv:2409.02166 — W2 boundary-SymTFT framework
  - Kapustin-Thorngren-Turzillo-Wang arXiv:1406.7329 — W1/W4 Pin⁺ SPT
  - García-Etxebarria-Montero arXiv:1808.00009 — W4 SM-with-νR identification

---

*Created 2026-05-25 at Phase 6r close. Per-wave decomposition + 3-question template + module decomposition + bundle absorption + risk axes. Updates atomically as waves close.*

---

## Sessions log

*Empty — Phase 6r-prime has not yet been dispatched. **Note:** No DR dispatch needed; all Wave 1a.1 + 2a.1 + 3a.1 DRs from Phase 6r provide the substrate. Dispatch via `/goal complete 6r-prime per roadmap` at session start.*
