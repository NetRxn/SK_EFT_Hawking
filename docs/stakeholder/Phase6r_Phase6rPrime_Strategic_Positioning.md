# Strategic Positioning: Phase 6r + 6r-prime — The SymTFT Substrate + Substantive Discharge Phase

## How the Program Anchors Flagship-F Program Identity to a Mathlib-Style Topological-Symmetry Substrate

**Date:** 2026-05-25
**Context:** This memo positions Phase 6r + 6r-prime within the broader research program. Phase 6r SymTFT substrate + Phase 6r-prime substantive discharge jointly SUBSTANTIVELY COMPLETE.

---

## Phase 6r + 6r-prime's Strategic Value

Phase 6r + 6r-prime jointly deliver the **topological-symmetry substrate** for the SK-EFT-Hawking project. This substrate is operationally parallel to (and orthogonal to) Phase 6q's dissipative-bootstrap track: Phase 6q answered the question "does a dissipative-bootstrap programme succeed on the SK-EFT-Hawking substrate?" with a bimodal "yes-on-lattice, sharpened-NO-GO-on-continuum-bosonic." Phase 6r + 6r-prime answer the question "what topological-symmetry framework anchors the SK-EFT-Hawking-horizon's program identity?" with a substantive Lean 4 formalization of the SymTFT framework (Drinfeld center + Lagrangian algebra boundaries + Pin⁺ Z₁₆ classification + Witten-Yonekura anomaly inflow) plus the substantive cross-bridge identifying the SK-EFT-Hawking horizon as the canonical Lagrangian-algebra-boundary instance for the Z₁₆-anomaly-cancelling SM matter content plus the paper-17 dark sector.

The Phase 6r-prime substantive-discharge pass is the **first project example of post-ship audit + remediation at the tracked-Prop level**. The Session 1 close framed "11 of 12 tracked Props discharged" via discharge-theorem existence; the Session 2 ground-truth audit applied the 3-criterion bar (well-established + ≥1 year or >20k LoC to substantively discharge + no existing project lift) to each tracked Prop and found 10 of the 12 to be P5 (identity-wrapper) / P2 (bundle redundancy) / P3 (tautology) / P4 (trivial-discharge) anti-patterns. The remediation (A1 through A5 + B1 through B12) discharged the 10 anti-patterns substantively, leaving **2 honest tracked Props**: Kirby-Taylor 1990 (`IsKirbyTaylorPinPlusBordism`) and Davydov-Müger-Nikshych-Ostrik 2010 (`IsDMNOBiconditional`). Both legitimately meet the bar.

For external positioning:

- **Before Phase 6r:** "the SymTFT framework + Pin⁺ Z₁₆ classification + Witten-Yonekura inflow are referenced in the project's narrative but not Lean-formalized."
- **After Phase 6r + 6r-prime:** "the SymTFT substrate is substantively formalized in Lean 4 (35+ modules, ~7,700 LoC, zero new axioms, 2 honest tracked Props), with the SK-EFT-Hawking horizon identified as the canonical Z₁₆-anomaly-cancelling Lagrangian-algebra-boundary instance. The substrate is Mathlib-PR-quality for Drinfeld-center biproducts, generic Anderson-dual functor, FrobeniusPerronDim typeclass, and RP⁴ ChartedSpace."

Like recent phases, Phase 6r + 6r-prime produce no new standalone papers. The substantive content lifts into bundles D2 (Pin⁺ Z₁₆), D4 (Drinfeld center + Lagrangian algebra), D5 (NO-GO landscape + alternative-boundaries / paper-17), L1 (anomaly-inflow APS-η), and flagship-F (program identity via the unique SK-EFT-Hawking-horizon Lagrangian-algebra-boundary instance) at the unified bundle-absorption pass (HELD for user authorization).

---

## Three Strategic Track Pillars

### Track 1 — SymTFT Substrate (Phase 6r Waves 1a–3b, 18 modules / ~2,650 LoC)

Eighteen modules under `lean/SKEFTHawking/SymTFT/` + `lean/SKEFTHawking/CrossBridges/` + `lean/SKEFTHawking/APSEta/` building the alphabet-agnostic SymTFT substrate:

- **`Basic.lean`** — 3D TQFT predicate substrate + `IsBoundarySymTFTCorrespondence`.
- **`BulkTQFT.lean`** + **`BulkInstances.lean`** — `Is3DTQFT` + `Is3DTQFTBraided` + Drinfeld-center reading.
- **`FrobeniusAlgebra.lean`** + **`LagrangianAlgebra.lean`** + **`GappedBoundary.lean`** — Frobenius / commutative Frobenius / separable / connected / Lagrangian algebra substrate + gapped-boundary correspondence.
- **`ToricCodeLagrangian.lean`** + **`ToricCodeLagrangianAnyons.lean`** — toric-code two-Lagrangian-algebras classification at the anyon-set level.
- **`PinBordism.lean`** + **`PinPlusBordism4.lean`** + **`PinPlusManifold4.lean`** — Pin⁺ bordism substrate.
- **`AndersonDualSubstrate.lean`** + **`PontryaginDualPinPlus.lean`** + **`AndersonDualFunctor.lean`** — Anderson-dual + Pontryagin reciprocity substrate.
- **`SpinSymTFT.lean`** + **`SpinSymTFTSchellekensAlignment.lean`** + **`Z16ViaSpinSymTFT.lean`** — Spin-SymTFT fermionic extension + Z₁₆ classification.
- **`IsSMMatterTopologicalBoundary.lean`** + **`AlternativeBoundaries.lean`** — SM matter on topological boundary + paper-17 dark-sector cross-bridge.
- **`SubstrateToBulkIdentification.lean`** + **`SubstrateEtaInvariant.lean`** + **`BulkBoundaryCorrespondence.lean`** — substrate-to-bulk identification + Witten-Yonekura η-invariant substrate.
- **`CrossBridges/SMMatterAsSymTFTBoundary.lean`** + **`APSEta/SubstrateBulkAsymmetry.lean`** — cross-bridges to flagship-F + Pin⁺ SPT asymmetry.

**Audience:** SymTFT researchers (Kong, Kapustin, Saulina, Wen, Bhardwaj-Copetti-Pajer-Schäfer-Nameki); topological-order theorists; algebraic-topology researchers (Kirby, Taylor, Freed, Hopkins, Lurie); standard-model + dark-sector phenomenologists (García-Etxebarria, Montero, paper-17 community).

**Re-use story:** Future SymTFT formalization work inherits the entire Track 1 substrate. Adding a new gauge theory's SymTFT (e.g., 4D N=1 super-Yang-Mills with surface defects; class-S theories; non-invertible-symmetry SymTFTs) is now an *instantiation problem* rather than a re-derivation. The substantive `IsDMNOBiconditional` keep + the `Omega4PinPlusBordism ≃+ ZMod 16` substantive iso + the `IZOmega n` generic Anderson-dual functor are the substrate-level statements; new SymTFT applications slot in by establishing the appropriate analogues.

### Track 2 — Substantive Discharge + Mathlib-Style Upstream Ships (Phase 6r-prime M1–M5 + A1–A5 + B1–B12)

Eighteen+ new modules + audit remediation + closure bundle. The substantive discharge of 10 of 12 tracked Props from Phase 6r close plus Mathlib-PR-quality upstream content:

- **M1 (`FrobeniusPerronDim.lean`)** — `FrobeniusPerronDim` typeclass + `IsLagrangianAlgebraFPdimRefined` refinement.
- **M2 (`CenterBiproducts.lean`)** — Drinfeld-center binary biproducts via `Functor.mapBiprod` on tensorLeft/tensorRight with `MonoidalPreadditive` premise. Mathlib-PR-quality upstream content.
- **M3 (`RP4.lean` + `RP4Smooth.lean` + `RP4LocalHomeomorph.lean` + `RP4ChartedSpace.lean` + `RP4IsManifold.lean`)** — topological RP⁴ via antipodal Z₂ quotient + ChartedSpace + 4-manifold structural prerequisites + IsManifold substrate (chart-transition smoothness via sphere chart-transition + ambient negation).
- **M4 (`StiefelWhitney.lean`)** — narrow-scope Pin⁺ obstruction `w₂ = 0` substrate via Karoubi 1968 §5 mod-2 binomial calculation.
- **M5 (`AndersonDualFunctor.lean`)** — generic `IZOmega Ω Ω_next h := AddChar Ω Circle` with contravariant functoriality + concrete ZMod 2/3/16 instances + Pontryagin reciprocity via `AddChar.doubleDualEmb`.
- **A5 (Drinfeld-center MonObj / ComonObj / IsSeparable / IsConnected / IsLagrangianAlgebra on `𝟙_ (Center C)`)** — `A5VacuumMonObj.lean` + `A5LagrangianCenterUnit.lean` + `VecGPreadditive.lean` + `CenterPreadditive.lean` + `CenterBiproductsHalfBraiding.lean`. The canonical Lagrangian-algebra base case substantively discharged.
- **A1–A4 + B1–B12 audit remediation** — DELETE/RESTRUCTURE/RECLASSIFY of 10 anti-pattern tracked Props + the 12 additional P5/P4/P3/P2 anti-pattern remediations.

**Audience:** Lean / Mathlib working groups; category-theory-in-Lean researchers (Mathlib4 SciLean / mathlib-CategoryTheory); SymTFT formalization stakeholders.

**Re-use story:** The Mathlib-PR-quality upstream content — Drinfeld-center binary biproducts, generic Anderson-dual functor, FrobeniusPerronDim typeclass, RP⁴ ChartedSpace + 4-manifold prerequisites — is **ready for upstream contribution** to Mathlib4. The substrate is generic in `[MonoidalPreadditive C][HasBinaryBiproducts C]` (M2), `[AddCommGroup Ω][Finite Ω]` + `BordismVanishes Ω_next` (M5), `[BraidedCategory C][Preadditive C]` (M1), and standard `Sphere` + `EuclideanSpace` infrastructure (M3). Adding new projective-space-via-quotient manifold constructions, new modular tensor categories, new Anderson-dual specializations, or new Lagrangian-algebra instances all instantiates this substrate.

### Track 3 — Cross-Bridge Integration + Closure Bundle (Phase 6r-prime W5 + Phase6rPrimeClose)

The cross-bridge integration phase — updates Phase 6r consumers to use substantively-discharged content — plus the consolidated 44-conjunct closure bundle (`Phase6rPrimeClose.lean`) that is the **single anchor point** for the M-R dual-phase Phase 6r + 6r-prime adversarial review.

The closure bundles all substantive content into one theorem: substantive Pin⁺ bordism Quotient iso (W1.2), substantive Anderson-dual Pin⁺ via Pontryagin chain (post-A1), substantive Anderson-dual relation iso composition, KEEP tracked Prop #1 (KT 1990), substantive toric-code Lagrangian-algebra two-anyon-set classification (C1.1-1.3), substantive M4-narrow Pin⁺ obstruction equation, substantive Pin⁻ falsifier on RP4, substrate-η-invariant biconditional (W4-η-1), η-invariant non-vanishing on anomalous substrates, Z16AnomalyCancels SM substrate (Wave 2a.3), combined-SM-plus-paper17 anomaly cancellation (C2-honest-1), substantive paper-17 dark-sector topological-boundary discharge, broken paper-17 substrate falsifier (W4-η-4 / C2-honest-3), broken-substrate η-non-vanishing, BordismVanishes substrate (M5 + falsifier), Pin⁺ recovery via substantive composition, M3 Layer B-1 + B-2 + B-4a + B-4b + B-4c + B-4d substrate, A5(a) + A5(b) + A5(c) + A5(d) substrate, M5 functoriality + Pontryagin reciprocity. All 44 conjuncts are substantive Lean theorems with no P5/P4/P3/P2 anti-patterns.

**Audience:** Adversarial reviewers (M-R round); future-self at next phase opening for context bootstrap; bundle-absorption pass at Phase 7.

**Re-use story:** The closure bundle pattern (single consolidated theorem at the phase close, anchoring adversarial review) generalizes to future phases. The dual-phase joint review pattern (Phase 6r + 6r-prime adversarial review covering both phases as one substrate) supports the substrate-then-substantive-discharge phase architecture going forward.

---

## Bridge Map — How Phase 6r + 6r-prime Connect to the Rest

| Bridge | Phase | Status | Cross-bridge to Phase 6r + 6r-prime |
|---|---|---|---|
| Phase 6o spin-bordism + APS-η scaffolding | 6o | shipped | Substrate dependency — `Schellekens/SpinBordism.lean` (Phase 6o spin-bordism placeholder) parallels the Phase 6r-prime Pin⁺ bordism Quotient construction; `APSEta/*` (Phase 6o substrate placeholders) is the foundation that the Witten-Yonekura η-invariant substantively discharges. |
| Phase 6n LDP + Crooks-on-analog-Hawking | 6n | shipped | The η-invariant substrate connects naturally to the LDP rate function via the η-vanishes-iff-trivial-class biconditional + the AddChar orthogonality story. Future Track 2 work may cross-bridge these. |
| Phase 6q DKM transport bootstrap | 6q | shipped | Orthogonal track — the dissipative-bootstrap programme. The two tracks share the SK-EFT-Hawking horizon as substrate and unify at the flagship-F level. |
| Phase 6t Solovay-Kitaev | 6t | shipped | Orthogonal track — the quantum-compilation programme. Unrelated at the substrate level. |
| Paper-9 Drinfeld center | flagship | published | Substrate dependency — `CenterFunctorZ2.lean`, `S3CenterAnyons.lean`, `DrinfeldCenterBridge.lean`. Phase 6r-prime M2 (Drinfeld-center biproducts) extends paper-9's substrate. |
| Paper-17 dark sector | flagship | drafted | Substrate dependency — Phase 6r-prime C2 ships the substantive dark-sector topological-boundary discharge via the hidden-ℤ/16-sector witness. Paper-17 readers consume this substrate. |
| Kirby-Taylor 1990 | upstream | foundational | Primary source for the Pin⁺ Z₁₆ classification. The Phase 6r-prime W1.2 + W3 ships are the first Lean 4 formalization of this content. |
| Davydov-Müger-Nikshych-Ostrik 2010 | upstream | foundational | Primary source for the DMNO biconditional. The Phase 6r W2.3 v2 substantive predicate is the canonical Lean encoding. |
| Witten-Yonekura arXiv:1909.08775 | upstream | published | Primary source for the η-invariant anomaly inflow. Phase 6r-prime W4-η-1 ships the substantive η-invariant substrate via `ZMod.toAddCircle`. |
| Bhardwaj-Copetti-Pajer-Schäfer-Nameki arXiv:2409.02166 | upstream | published | Primary source for the boundary-SymTFT framework + SM matter on topological boundary. Phase 6r W3 + Phase 6r-prime W5-η-bridge ship the substantive SM cross-bridge. |
| Karoubi 1968 §5 | upstream | foundational | Primary source for the mod-2 Stiefel-Whitney calculation on RP^n. Phase 6r-prime M4-narrow ships the substantive Pin⁺ obstruction `w₂(TRP⁴) = 0` via this source. |
| García-Etxebarria-Montero arXiv:1808.00009 | upstream | published | Primary source for SM-with-νR identification + Z₁₆ anomaly cancellation. Phase 6r W3 + Phase 6r-prime C2-honest-1 ship the substantive SM-3-generation + paper-17 hidden-sector cross-bridge. |

---

## Audiences and Outward-Facing Positioning

### Audience 1: SymTFT / Topological-Order Researchers

The substantive message: **the SymTFT framework — Drinfeld center as canonical bulk, Lagrangian algebras as canonical boundary correspondences, DMNO biconditional as the substrate-level Witt-triviality classification, Pin⁺ Z₁₆ as the fermionic-extension substrate, Witten-Yonekura η-invariant as the anomaly-inflow substrate — is now substantively Lean-4-formalized**. For SymTFT researchers, this provides a kernel-verified target for cross-prover validation + a reusable substrate for new SymTFT applications.

The honest positioning per the project's tracked-Prop discipline: **2 legitimately-tracked Props** (KT 1990 + DMNO 2010), each requiring substantial bespoke Lean work to substantively discharge (full APS index theorem for KT; Modular Tensor Category typeclass + Lagrangian-algebra existence for DMNO). All other content is substantively discharged.

### Audience 2: Algebraic-Topology Researchers

The substantive Pin⁺ bordism Quotient construction + the generic Anderson-dual functor + the topological RP⁴ + 4-manifold structural prerequisites + Stiefel-Whitney mod-2 substrate are the **first Lean 4 formalizations of these topological-category-theory ingredients**. The substrate is Mathlib-PR-quality and ready for upstream contribution.

The W1.2 Setoid + Quotient construction generalizes to other bordism groups (Spin, Spin^c, Pin⁻, oriented). The IZOmega n functor generalizes to any finite abelian group's Anderson-dual class. The RP⁴ ChartedSpace via antipodal-quotient generalizes to RP^n via Mathlib's existing `Sphere` substrate.

### Audience 3: Standard-Model + Dark-Sector Phenomenologists

The substantive SM-3-generation Z₁₆-anomaly-cancellation cross-bridge + the paper-17 hidden-sector +3/SM-3 cancellation substrate + the broken-substrate falsifier are the **first Lean 4 cross-bridges** identifying the SK-EFT-Hawking horizon substrate as the canonical Z₁₆-anomaly-cancelling Lagrangian-algebra-boundary instance.

The substrate IS falsifiable: the explicit broken-paper-17 substrate falsifier (`sm_plus_broken_paper17_substrate_anomaly_does_not_cancel` + `substrateEtaInvariant sm_plus_broken_paper17_substrate ≠ 0`) discriminates the substantive paper-17 content from broken alternatives. For phenomenologists, this provides a kernel-verified target for new dark-sector candidates: any proposed dark-sector substrate must pass the substantive Z₁₆-anomaly-cancellation check.

### Audience 4: Lean / Mathlib Working Groups

Phase 6r + 6r-prime demonstrate that Mathlib4 v4.29.0 is *sufficient* for substantive SymTFT formalization at the predicate-substrate level. No new Mathlib substrate was required (`CategoryTheory.Center`, `CategoryTheory.Monoidal.{Mon_, Comon_, Rigid}`, `Geometry.Manifold.{IsManifold, ChartedSpace, Instances.Sphere}`, `Topology.{Covering, Sphere}`, `AddChar`, `Pontryagin double-dual`, `Setoid + Quotient`, `MulAction.orbitRel.Quotient`, `EuclideanSpace.instIsManifoldSphere` — all present).

**Mathlib-PR-quality upstream content shipped:**

- `CenterBiproducts.lean` — binary biproducts in Drinfeld center.
- `AndersonDualFunctor.lean` — generic Anderson-dual functor + Pontryagin reciprocity.
- `FrobeniusPerronDim.lean` — FrobeniusPerronDim typeclass + `IsLagrangianAlgebraFPdimRefined`.
- `RP4.lean` + `RP4ChartedSpace.lean` + `RP4IsManifold.lean` — topological RP⁴ + 4-manifold structural prerequisites (partial upstream-PR candidate).

The substrate posture is unchanged: **zero new project-local axioms** (Invariant #15 maintained). The two tracked Props meet the project's 3-criterion bar (literature-established + >20k LoC or ≥1 year to substantively discharge + no existing project lift).

---

## Comparison: Phase 6r vs Phase 6r-prime

| Dimension | Phase 6r | Phase 6r-prime |
|---|---|---|
| Modules | 18 | 18+ |
| LoC | ~2,650 | ~5,000+ |
| Sessions | 1 (autonomous /goal) | 2+ |
| Outcome shape | Substrate at predicate level | Substantive discharge + Mathlib-PR-quality upstream content |
| Tracked Props (nominal) | 12 | 2 (honest, post-audit) |
| Key upstream-PR content | Drinfeld center predicate substrate | M2 Drinfeld-center biproducts, M5 IZOmega, M1 FrobeniusPerronDim, M3 RP⁴ ChartedSpace |
| Bundle absorption | HELD | HELD (unified) |
| Adversarial review | Phase-internal | Joint Phase 6r + 6r-prime dual-phase (M-R, in progress) |

The pattern is clear: **Phase 6r ships substrate at the predicate level; Phase 6r-prime substantively discharges that substrate via Mathlib-PR-quality upstream content + audit remediation**. This is the project's first explicit two-phase architecture for "substrate then substantive discharge"; future phases targeting similar mathematical territory can adopt this pattern.

---

## Risk Assessment

### Strategic Risks

**No new risks introduced by Phase 6r + 6r-prime.** The substantive substrate is built on Mathlib's existing infrastructure + substantively-shipped project content; no new project-local axioms; the 2 honest tracked Props are well-known mathematical theorems whose Lean discharge would require multi-PM effort on Mathlib infrastructure beyond this phase's scope.

### Phase Risks (Closed)

- **BLOCKER-2 from Phase 6r adversarial review round 1** (`witt_triviality_iff_has_lagrangian_algebra` as predicate-substrate tautology): CLOSED via Phase 6r-prime W2.3 v2 substantive `IsDMNOBiconditional` body.
- **Phase 6r-prime Session 1 close optimism** (12 of 12 tracked Props "discharged"): CLOSED via Session 2 audit + remediation (10 substantively discharged, 2 KEEP as honest tracked Props).
- **M4-narrow scope choice** (full Stiefel-Whitney cohomology in Lean = multi-PM): CLOSED via the narrow-scope ship (Karoubi 1968 §5 mod-2 binomial values for RP⁴ specifically; documented obstruction equation `w₂ = 0`).

### Remaining Items

The M-R final dual-phase adversarial review (LAST item per user direction) is the final closure step. After M-R close: the joint Phase 6r + 6r-prime substrate is ready for unified bundle absorption (at Phase 7) into bundles D2, D4, D5, L1, and flagship-F.

---

## What's Next After M-R Close

After the M-R dual-phase adversarial review GREEN verdict, the joint Phase 6r + 6r-prime substrate is ready for:

1. **Unified bundle absorption** at the Phase 7 user-authorized event. D2 (Pin⁺ Z₁₆ subsection), D4 (Lagrangian-algebra boundary subsection), D5 (paper-17 dark-sector subsection), L1 (APS-η subsection), and flagship-F (SK-EFT-Hawking-horizon-as-canonical-Lagrangian-algebra-boundary subsection) all get the Phase 6r + 6r-prime substrate additively at the absorption pass.

2. **Mathlib upstream PR coordination** for the M2 Drinfeld-center biproducts + M5 Anderson-dual functor + M1 FrobeniusPerronDim + M3 RP⁴ ChartedSpace pieces. Sequence: identify Mathlib maintainer(s); draft PR with appropriate context + tests; iterate on review feedback. Multi-week coordination event.

3. **Follow-on substantive ships within the Phase 6r-prime architecture:**
   - **Full IsManifold (𝓡 4) ω RP4** chart-transition smoothness (the M3 Layer B-4d substrate is shipped; the full instance is the per-pair chart-transition piecewise-decomposition discharge, well-bounded ~300-500 LoC bespoke).
   - **Full HalfBraiding (X.1 ⊞ Y.1) monoidal + naturality axioms** on the diagonal biproduct (the A5(b)-pt2 substrate is shipped; the full axioms are per-summand reduction via `biprod.hom_ext` + Mathlib `Center.tensorObj` style coherence, well-bounded ~150-300 LoC bespoke).
   - **Full IsLagrangianAlgebra on `vacuum ⊞ electric`** for the toric-code object-level discharge (A5(c-e) — depends on Discrete (ZMod 2) preadditive refinement; ~400-700 LoC bespoke).

These follow-on ships are tractable, well-bounded, and fit the project's Mathlib-PR-quality upstream pattern. They can be scheduled as focused future sessions when the bundle-absorption gate triggers downstream consumers.

---

## Acknowledgments

This phase pair consumed and built on Phase 6q DKM transport substrate, Phase 6o spin-bordism placeholder + APS-η scaffolding, Phase 6n LDP + Crooks-on-analog-Hawking infrastructure, paper-9 Drinfeld-center substrate, and paper-17 dark-sector content.

Primary mathematical sources (acknowledged in each substrate module's docstring): Kirby-Taylor 1990, Davydov-Müger-Nikshych-Ostrik 2010, Davydov-Nikshych-Ostrik 2011, Kapustin-Saulina arXiv:1008.0654, Freed-Hopkins arXiv:1604.06527, Witten-Yonekura arXiv:1909.08775, Fuchs-Schweigert-Valentino arXiv:1203.4568, Bhardwaj-Copetti-Pajer-Schäfer-Nameki arXiv:2409.02166, Kapustin-Thorngren-Turzillo-Wang arXiv:1406.7329, García-Etxebarria-Montero arXiv:1808.00009, Karoubi 1968 §5, Hatcher *Algebraic Topology* §1.3.
