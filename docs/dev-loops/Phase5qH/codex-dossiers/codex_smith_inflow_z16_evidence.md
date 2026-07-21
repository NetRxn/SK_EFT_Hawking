**§1 WHAT THE NODE ACTUALLY IS.**

### Literal atlas object

`smith_inflow_z16` is not the name of a Lean declaration. It is a Python registry key: `src/core/constants.py:2926` begins the entry, `src/core/constants.py:2962` assigns `eliminability: 'very_hard'`, and `src/core/constants.py:2983-2996` supplies a hand-written list of twelve “dependent theorems.” The generated atlas repeats that metadata as an `UNKNOWN`, `PLANNED` node with `frontier_impact: 12` at `lean/atlas_view.json:211703-211724` and places it first in the frontier at `lean/atlas_view.json:212614-212619`. The twelve `ASSUMED_BY` edges are registry-derived annotations at `lean/atlas_view.json:212282-212339`; they are not evidence that Lean found twelve theorem signatures containing one common hypothesis.

The standing handoff's actual project objective is stronger and carrier-specific: an unconditional iso on a faithful T2, smooth, structure-extension bordism carrier, with computed rather than posited invariant (`docs/dev-loops/Phase5qH/HANDOFF_16_CONVERGENCE.md:31-43`). That objective is not the type of the atlas key described below.

The entry says that its Lean carrier is `CommonOrigin.SmithInflow` (`src/core/constants.py:2928-2931`). The actual declaration is:

```lean
structure SmithInflow where
  smith : ZMod 16 ≃+ Omega4PinPlusBordism
  smith_gen : smith 1 = Omega4PinPlusBordism.mk pinPlusRP4
```

(`lean/SKEFTHawking/CommonOrigin.lean:83-87`.) Thus:

- it is a structure in `Type`, not a `Prop` field and not a project `axiom`;
- a theorem binder `(S : SmithInflow)` discloses data consisting of an additive equivalence plus a generator equality; for example `sixteen_convergence_common_origin` has exactly that binder at `lean/SKEFTHawking/CommonOrigin.lean:181-191`;
- but the same file already defines `substrateSmithInflow : SmithInflow` from `omega4PinPlusBordismEquivZMod16.symm` at `lean/SKEFTHawking/CommonOrigin.lean:89-96`, then proves the purported downstream capstone without a binder at `lean/SKEFTHawking/CommonOrigin.lean:193-202`;
- it also proves a constructed-Smith version whose statement has only `(N_f : ℕ)` and no `SmithInflow` input at `lean/SKEFTHawking/CommonOrigin.lean:245-254`.

This is a statement/docstring discrepancy with direct atlas consequences. The docstring calls `SmithInflow` “the disclosed geometric input” and says the construction is Mathlib-absent (`lean/SKEFTHawking/CommonOrigin.lean:77-82`), but the theorem statement contains only a thin `ZMod 16 ≃+ Omega4PinPlusBordism`, and that structure is inhabited in the next declaration (`lean/SKEFTHawking/CommonOrigin.lean:83-96`). Likewise, the atlas says `sixteen_convergence_common_origin_via_constructed_smith` is `ASSUMED_BY` this node (`lean/atlas_view.json:212292-212295`), while its actual theorem statement has no such binder (`lean/SKEFTHawking/CommonOrigin.lean:245-251`). Therefore the literal atlas node is already discharged at the substrate level; its `PLANNED`/`very_hard` state is not a faithful description of an open Lean proposition.

### The three different objects that the record calls the “same node”

They are not the same Lean statement.

1. **`smith_inflow_z16` (registry/intended Smith form).** The historical E3 route intended the source-side computation `Nonempty (A ≃+ ZMod 16)` for a faithful `A = Ω₆^{Pin⁻}`, together with a geometric Smith homomorphism `sm : A →+ B` and two exactness hypotheses. The actual generic theorem is:

   ```lean
   theorem omega4PinPlusGMData_ext_equiv_zmod16_via_smith_les_neighbor
       (sm : A →+ B)
       (hL : Function.Exact (0 : PUnit →+ A) sm)
       (hR : Function.Exact sm (0 : B →+ PUnit))
       (hA : Nonempty (A ≃+ ZMod 16)) :
       Nonempty (B ≃+ ZMod 16)
   ```

   (`lean/SKEFTHawking/PinPlusGMDataZ16.lean:249-256`.) This declaration is algebra over arbitrary additive groups `A` and `B`; it does not instantiate a faithful dimension-six bordism carrier.

2. **`hbound` (retired tied-carrier grade-zero injectivity).** Its exact type is

   ```lean
   ∀ x : DataBordismGrp (pinPlusGMTiedData (k := 0) (𝓡 4)),
     abkGMTied16 x = 0 → x = 0
   ```

   as a theorem parameter at `lean/SKEFTHawking/PinPlusGMWitness.lean:431-436`. It speaks about the old dimension-four tied `DataBordismGrp`; it is neither an `Ω₆^{Pin⁻}` computation nor a geometric Smith map.

3. **`hexact` (retired tied-carrier KT/σ-route equality).** Its exact type is

   ```lean
   ker (reduce16to8 ∘ abkGMTied16) = range (forgetGen F g)
   ```

   at `lean/SKEFTHawking/SpinSigmaRouteDoor.lean:47-58`. `forgetGen_hexact_of_grade0` proves the one-way implication `hbound + habk8 → hexact` at `lean/SKEFTHawking/SpinSigmaExactness.lean:114-124`. No reverse implication is stated there. The surrounding prose calls this “apex-equivalent” (`lean/SKEFTHawking/SpinSigmaExactness.lean:109-113`), but the theorem statement only proves one direction. That difference is load-bearing.

The current faithful-carrier completeness statement is a fourth object: `KernelReducesToSpin prov`, meaning every `charPairBrown`-zero class in `T2DataBordismGrp (pinPlusCharPairData prov)` has a rank-zero representative (`lean/SKEFTHawking/PinPlusKTKernelSector.lean:223-225`). It is not definitionally any of the preceding three.

There is also a current regularity mismatch independent of Smith naming. The handoff requires smooth `k ≥ 1` data (`docs/dev-loops/Phase5qH/HANDOFF_16_CONVERGENCE.md:31-37`), but the canonical provider used by the authoritative KT assembly is declared at `k := 0` (`lean/SKEFTHawking/PinPlusKTAssemblyResiduals.lean:65-72`), and the capstone conclusion is consequently an iso on `pinPlusCharPairData residualProv` (`lean/SKEFTHawking/PinPlusKTSphereProdCohomology.lean:194-215`). The source proves a result about that `k = 0` carrier if its residual row is supplied; it does not, in those statements, transport the result to a `k ≥ 1` carrier. Thus “current faithful carrier” below means T2/tether-faithful in the source's own sense, not a verified completion of the handoff's smoothness requirement.

### What an honest discharge would require

There are two possible meanings, and they have very different obligations.

- **Literal atlas meaning:** nothing further is needed to inhabit `SmithInflow`; `substrateSmithInflow` already does so (`lean/SKEFTHawking/CommonOrigin.lean:92-96`). The atlas node should therefore be retired or retyped.
- **Intended direct-Smith geometric meaning:** build a faithful smooth/T2 dimension-six `Pin⁻` bordism carrier `A`; prove `Nonempty (A ≃+ ZMod 16)` from a genuine Pontryagin–Thom/ABP/Adams or AHSS computation; build the codimension-two geometric Smith map `sm : A →+ B` on the faithful dimension-four carrier; and prove the left/right exactness hypotheses consumed by `PinPlusGMDataZ16.lean:249-256`. The historical route dossier itemizes precisely these missing S1–S6 pieces at `docs/dev-loops/Phase5qH/W_D_ROUTE_DOSSIER.md:65-82`.

`UNVERIFIED (external mathematics)`: the registry and notebooks say the literature proves `Ω₆^{Pin⁻} ≅ ℤ/16` and Smith iso-ness (`src/core/constants.py:3000-3009`; `docs/dev-loops/Phase5qH/W_D_ROUTE_DOSSIER.md:67-82`). I verified that this is what the repository records, not the external papers themselves.

**§2 WHAT HAS BEEN TRIED.**

### 2026-06-14: thin Smith-inflow and finite-abutment waves

The registry preserves the W5/W6 sequence. W6 replaced an abstract binder by a thin quotient and constructed Smith map, but explicitly says this was “HYPOTHESIS-level only” and that geometric `Ω₅`, eta, and Smith/Dai–Freed constructions remained (`src/core/constants.py:2968-2982`). The corresponding source confirms the distinction: the no-binder theorem is real (`lean/SKEFTHawking/CommonOrigin.lean:245-254`), but its preceding docstring warns that geometric faithfulness remains tracked (`lean/SKEFTHawking/CommonOrigin.lean:240-244`). What landed was a substrate-level map-composition, not a faithful manifold-bordism discharge.

The W5+W8 registry update then built the finite column-four calculation (`src/core/constants.py:2940-2950`). The actual theorem `col4_height_eq_four` is a finite `by decide` survivor count (`lean/SKEFTHawking/PinPlusHeight4.lean:54-61`), and `adamsAbutmentEquivZMod16` proves an iso only after defining `adamsAbutment := ZMod (2 ^ height4)` (`lean/SKEFTHawking/PinPlusAdamsAbutment.lean:66-74`, `lean/SKEFTHawking/PinPlusAdamsAbutment.lean:86-98`). It stopped before the geometric PT/convergence identification. `pin4_abutment` states that identification as `Nonempty (Omega4PinPlusBordism ≃+ ZMod (2 ^ height4))` (`lean/SKEFTHawking/PinPlusDischarge.lean:48-67`), but `pin4_abutment_substrate` immediately proves it using the already-posited thin iso (`lean/SKEFTHawking/PinPlusDischarge.lean:69-75`). The E5 audit later described this accurately: “finite Adams abutment done, geometric faithfulness open” (`docs/dev-loops/Phase5qH/E5_SubstrateS_Spectral/LAB_NOTEBOOK_INDEX.md:18-26`).

### 2026-07-04: E3 geometric Smith/LES architecture

E3 landed the generic algebraic half and the eight-torsion no-go. The notebook records:

> “The genuine mod-8 GM carrier `pinPlusGMData` is **8-torsion**, so it provably canNOT itself carry the ℤ/16 odd bit”

(`docs/dev-loops/Phase5qH/E3_SmithMap_Exactness/LAB_NOTEBOOK.md:11-21`). It then landed the extension theorem consuming `sm`, `hL`, `hR`, and the neighbor iso (`docs/dev-loops/Phase5qH/E3_SmithMap_Exactness/LAB_NOTEBOOK.md:23-33`; actual statement `lean/SKEFTHawking/PinPlusGMDataZ16.lean:249-294`).

It stopped exactly at geometry: the zero-locus map, sphere-bundle surjectivity, interval-bundle injectivity, and delta-model remained unchecked (`docs/dev-loops/Phase5qH/E3_SmithMap_Exactness/LAB_NOTEBOOK_INDEX.md:27-44`). The notebook says the next brick required E1 sphere/disk-bundle and PD-with-boundary primitives (`docs/dev-loops/Phase5qH/E3_SmithMap_Exactness/LAB_NOTEBOOK.md:43-54`). It also explicitly rejects `smithDataHom` as the genuine solution: “grade-transport shortcut only” (`docs/dev-loops/Phase5qH/E3_SmithMap_Exactness/LAB_NOTEBOOK_INDEX.md:46-48`). The source bears that out: `smithDataHom` sends every source manifold to `emptySM` and transports only the grade (`lean/SKEFTHawking/SmithIsomorphism.lean:193-220`).

### 2026-07-04 to 2026-07-05: E5 audit and cardinality sharpening

E5 did not begin a direct spectral construction. Its active notebook still says, “**No bricks yet — Option A build not started**” (`docs/dev-loops/Phase5qH/E5_SubstrateS_Spectral/LAB_NOTEBOOK.md:1-4`). Its audit found that `smith_inflow_z16` was a registry entry, not a Lean declaration, and that only the finite abutment had landed (`docs/dev-loops/Phase5qH/E5_SubstrateS_Spectral/LAB_NOTEBOOK_INDEX.md:17-24`).

On 2026-07-05, `PinPlusFaithfulnessCardBridge` sharpened the old tied-carrier question to a cardinality inequality (`docs/dev-loops/Phase5qH/E5_SubstrateS_Spectral/LAB_NOTEBOOK_INDEX.md:28-30`). The source theorem actually says, under a `Finite` instance,

```lean
Nonempty (oldCarrier ≃+ ZMod 16) ↔ Nat.card oldCarrier ≤ Nat.card adamsAbutment
```

(`lean/SKEFTHawking/PinPlusFaithfulnessCardBridge.lean:119-126`). This was a statement-layer reduction, not the `≤` proof. Moreover, it targeted the old `pinPlusGMTiedData (k := 0)` carrier (`lean/SKEFTHawking/PinPlusFaithfulnessCardBridge.lean:102-108`), which the later soundness wave vacated.

### 2026-07-06: strategic re-examination demoted Smith

The execution map is explicitly retired/frozen historical rationale (`docs/dev-loops/Phase5qH/PHASE5QH_EXECUTION_MAP.md:3-15`), but it records the 2026-07-06 user-directed re-anchor after reading the KT route: “the keystone is the KT GEOMETRIC exact-sequence close, NOT the spectral `smith_inflow_z16` / ABP tower” (`docs/dev-loops/Phase5qH/PHASE5QH_EXECUTION_MAP.md:43-45`). It also warns that the atlas ranking reflects what was wired, not the required route (`docs/dev-loops/Phase5qH/PHASE5QH_EXECUTION_MAP.md:173-179`). `SETTLED_FORKS` likewise says Smith was demoted to an alternative, with KT assembling `16 = 2 × 8` from below (`docs/dev-loops/SETTLED_FORKS.md:200-218`). Thus the repository did re-examine the early “required spectral” classification, and the strategic verdict changed before the atlas metadata did.

### 2026-07-13: Opus decomposition, then the dedicated large-model attack

Two Opus workers proved useful statement reductions. One proved `hbound → hexact`; another identified the concrete `forgetGen` map with the existing `g8` bridge (`docs/dev-loops/Phase5qH/LAB_NOTEBOOK_W1.md:87-105`). What landed was decomposition around the old tied carrier, not a proof of faithful completeness. The notebook then made the stronger claim `hbound ⟺ card ≤ 16 ⟺ smith_inflow_z16` and escalated the combined node to a Fable worker with “WIDE latitude” (`docs/dev-loops/Phase5qH/LAB_NOTEBOOK_W1.md:102-110`). Of those displayed equivalences, the source checked here proves `hbound → hexact` (`lean/SKEFTHawking/SpinSigmaExactness.lean:114-124`) and the finite-cardinality equivalence for the old carrier (`lean/SKEFTHawking/PinPlusFaithfulnessCardBridge.lean:119-126`); it does not contain a theorem equating the registry key or a faithful Smith input with `hbound`.

The dedicated large-model wave did **not** prove completeness. Its recorded conclusion is explicit:

> “The `hbound` keystone attack did NOT close completeness — it found a kernel-proven SOUNDNESS BUG in the substrate + shipped the repair.”

(`docs/dev-loops/Phase5qH/LAB_NOTEBOOK_W1.md:169-171`.) It found that the old bordism relation admitted non-Hausdorff bordisms, proved the carrier collapsed, and proved `hbound` vacuously (`docs/dev-loops/Phase5qH/LAB_NOTEBOOK_W1.md:172-188`). The actual collapse theorems are `bordismGrp_subsingleton` (`lean/SKEFTHawking/NonHausdorffBordismCollapse.lean:138-146`), `grade0_eq_zero_of_nonHausdorff` (`lean/SKEFTHawking/NonHausdorffBordismCollapse.lean:181-199`), and the unconditional old-carrier iso obtained from that collapse (`lean/SKEFTHawking/NonHausdorffBordismCollapse.lean:226-234`). It also shipped a T2 restatement, but the smoothness warning is only a docstring: the file itself labels the `k = 0` topological-vs-smooth claim “record, not proven here” (`lean/SKEFTHawking/T2TangentialBordism.lean:20-30`). `UNVERIFIED (external mathematics)`: the Kirby–Siebenmann/E8 explanation in that docstring was not independently checked.

### 2026-07-13 onward: faithful-carrier rebase and KT selection

The post-mortem found a third problem: even T2 was insufficient because the tied `Bor` relation only compared a carried grade (`docs/dev-loops/Phase5qH/LAB_NOTEBOOK_W1.md:197-219`). The route dossier therefore compared the rebuilt dimension-four carrier against a fresh dimension-six Smith program. It found Smith missing a faithful `Ω₆^{Pin⁻}` carrier, the geometric map, both exactness constructions, and the external source computation (`docs/dev-loops/Phase5qH/W_D_ROUTE_DOSSIER.md:65-82`); it recommended KT because Smith would be “a second W-A-scale construction” (`docs/dev-loops/Phase5qH/W_D_ROUTE_DOSSIER.md:101-109`, `docs/dev-loops/Phase5qH/W_D_ROUTE_DOSSIER.md:186-215`). The live notebook records that decision on 2026-07-13 and says the in-tree Smith statement was already vacuous on the vacated carrier (`docs/dev-loops/Phase5qH/LAB_NOTEBOOK_W1.md:563-578`).

Subsequent work has therefore not been another Smith discharge attempt. It has built the current faithful characteristic-pair carrier and KT completeness machinery. The live master index says the faithful target is T2 + smooth + structure-extension and that the old `hbound` door is vacated (`docs/dev-loops/Phase5qH/LAB_NOTEBOOK_INDEX.md:115-124`). This matters for difficulty reassessment in §4.

The history records the 2026-07-18 re-scope explicitly: the faithful completeness summit became a universal supply of one ambient surgery datum per positive-rank Brown-zero representative, and it warns to “steer clear of the vacated `smith_inflow_z16`/σ-route completeness” (`docs/dev-loops/Phase5qH/LAB_NOTEBOOK_HISTORY.md:548-549`). By 2026-07-20 the algebraic head had been absorbed and the remaining hypothesis sharpened to a purely geometric `IsotropicSurgeryTrace` supply (`docs/dev-loops/Phase5qH/LAB_NOTEBOOK_HISTORY.md:569-571`). These were real advances, but on the re-anchored KT lane.

**§3 WHAT SUBSTRATE EXISTS.**

The labels below describe theorem statements, not their docstrings.

### PROVED: thin/substrate Smith layer

- `substrateSmithInflow : SmithInflow` constructs the literal structure (`lean/SKEFTHawking/CommonOrigin.lean:92-96`).
- `sixteen_convergence_common_origin_substrate` proves the five-facet conjunction on that substrate (`lean/SKEFTHawking/CommonOrigin.lean:193-202`).
- `sixteen_convergence_common_origin_via_constructed_smith` proves a no-binder conjunction for the constructed thin Smith map (`lean/SKEFTHawking/CommonOrigin.lean:245-254`).
- `smithDataHom` is a genuine `AddMonoidHom` between two `DataBordismGrp` types, but its actual map is `[M,σ] ↦ [emptySM,(σ,0)]` (`lean/SKEFTHawking/SmithIsomorphism.lean:207-245`). It is grade transport, not a zero-locus Smith map.
- `smithQuotientEquiv` proves an equivalence only after quotienting both carriers by the kernels of their grade maps (`lean/SKEFTHawking/SmithIsomorphism.lean:284-301`). `FaithfulSixteenCapstone.smithFaithfulQuotientEquiv` has the same quotient-by-kernel shape (`lean/SKEFTHawking/FaithfulSixteenCapstone.lean:38-45`). These do not prove full-carrier faithfulness.

### PROVED: finite Adams-chart algebra

- `col4_survivors` and `col4_height_eq_four` compute the four surviving filtrations by `decide` (`lean/SKEFTHawking/PinPlusHeight4.lean:54-61`).
- `adamsAbutment` is **defined** to be `ZMod (2 ^ height4)`, not proved to be a geometric spectrum abutment (`lean/SKEFTHawking/PinPlusAdamsAbutment.lean:66-74`). `adamsAbutmentEquivZMod16` and `adamsAbutment_card` then follow (`lean/SKEFTHawking/PinPlusAdamsAbutment.lean:86-98`). This is the clearest docstring/statement boundary in the spectral lane.
- `pin4_abutment` is the disclosed proposition `Nonempty (Omega4PinPlusBordism ≃+ ZMod (2 ^ height4))` (`lean/SKEFTHawking/PinPlusDischarge.lean:48-67`), and `pin4_abutment_substrate` proves it from the already-built thin iso (`lean/SKEFTHawking/PinPlusDischarge.lean:69-75`). It does not prove Pontryagin–Thom or Adams convergence, despite the docstring assigning that interpretation.

### PROVED: generic Smith LES and partial geometric ingredients

- `smith_les_segment_iso` proves that a homomorphism with exact `0 → A → B → 0` is an equivalence (`lean/SKEFTHawking/PinPlusSmithLES.lean:33-50`).
- `pinPlus_zmod16_of_smith_les` transports `A ≃+ ZMod 16` across that exact segment (`lean/SKEFTHawking/PinPlusSmithLES.lean:52-64`).
- `omega4PinPlusGMData_ext_equiv_zmod16_via_smith_les_neighbor` is the same result at E3's generic extension boundary (`lean/SKEFTHawking/PinPlusGMDataZ16.lean:242-256`), and `ext_grade_ker_eq_bot_of_smith_les` adds finite-group counting (`lean/SKEFTHawking/PinPlusGMDataZ16.lean:258-294`). None of these fixes `A` to a geometric bordism group.
- `mLevelSetIsManifold` proves a regular-value level set is a smooth manifold, and `mLevelSetSingularManifold` packages it as a `SingularManifold` (`lean/SKEFTHawking/ManifoldRegularValue.lean:647-665`). This is real input for a zero-locus construction, but it does not supply a global line-bundle section, compact bordism functoriality, Pin-structure transfer, or Smith exactness.

### PROVED, but only on the retired carrier

- `spin_range_ge_of_grade0_inj` proves old `hbound →` the KT kernel inclusion (`lean/SKEFTHawking/PinPlusGMWitness.lean:366-383`).
- `omega4PinPlusGMTied_equiv_zmod16_via_kt_of_grade0` proves old `hbound → Nonempty (oldCarrier ≃+ ZMod 16)` (`lean/SKEFTHawking/PinPlusGMWitness.lean:390-394`).
- `grade0_bounds_of_thom` proves `hthom →` old grade-zero vanishing (`lean/SKEFTHawking/UnorientedThomCapstone.lean:40-57`).
- `forgetGen_hexact_of_grade0` proves `hbound + habk8 → hexact` (`lean/SKEFTHawking/SpinSigmaExactness.lean:114-124`).
- `iso_iff_card_le_abutment` proves old-carrier iso iff a finite cardinality bound (`lean/SKEFTHawking/PinPlusFaithfulnessCardBridge.lean:119-126`).

All five statements are genuine one-way or conditional theorems. None proves a three-way equivalence involving a faithful dimension-six Smith computation. More seriously, `dataBordismGMTied_mk_eq_iff_grade16_eq` proves that the retired carrier remembers only its grade (`lean/SKEFTHawking/NonHausdorffBordismCollapse.lean:201-224`), so old `hbound` is now evidence of a bad statement shape, not a usable faithful completion.

### PROVED: current faithful dimension-four substrate

- `pinPlusCharPairData prov` is a `T2TangentialData` whose `Bor` field is the tethered, realized characteristic-pair relation (`lean/SKEFTHawking/PinPlusCharPairCarrier.lean:65-93`).
- `charPairBrown : T2DataBordismGrp (...) →+ ZMod 8` is computed from the carried quadratic enhancement and is shown well-defined on that relation (`lean/SKEFTHawking/PinPlusCharPairCarrier.lean:103-123`).
- `charPairBrown_rp4_eq_one`, `charPairBrown_surjective`, and `charPairBrown_rp4_ne_zero` prove the real mod-eight door and noncollapse of the RP4 class (`lean/SKEFTHawking/RP4CharPairWitness.lean:120-151`). These prove a quotient-level lower bound, not the missing `{0,8}` distinction.
- `exists_isotropicClass_of_charPairBrown_zero` and `exists_reducedForm_of_charPairBrown_zero` prove the algebraic isotropic-class and reduced-form pieces for positive-rank Brown-zero representatives (`lean/SKEFTHawking/KTCompletenessProvider.lean:225-246`).
- `IsotropicSurgeryTrace` names the remaining geometric output—reduced representative, rank drop, T2 surgery trace, and tether (`lean/SKEFTHawking/KTCompletenessProvider.lean:261-279`). A universal supply implies `KernelReducesToSpin` (`lean/SKEFTHawking/KTCompletenessProvider.lean:303-318`).
- The newer tether interface states `BrownZeroHasIsotropicFramedAttachment` and `IsotropicSurgeryOutputSupply` (`lean/SKEFTHawking/KTCompletenessTether.lean:232-255`), and proves output supply implies `KernelReducesToSpin` (`lean/SKEFTHawking/KTCompletenessTether.lean:261-270`). These are consumers/interfaces; no source-faithful producer of the supply is proved there.
- The current full assembly is still conditional. `kt_equiv_zmod16_of_residuals_freezeAtoms_ofReducedAtoms` consumes a `KRSResidualRow` supply, a spin presentation row, handle/base atoms, a concrete bordism plus homological/Poincare–Lefschetz data, a rank-zero collapse, and two kernel/bridge hypotheses (`lean/SKEFTHawking/PinPlusKTSphereProdCohomology.lean:194-218`).

### DISCLOSED/HYPOTHESIS interfaces still open

- `KernelReducesToSpin prov` is the current completeness proposition (`lean/SKEFTHawking/PinPlusKTKernelSector.lean:223-225`).
- `SpinImageIsTwo prov` and `KummerWitness prov` are separately stated interfaces (`lean/SKEFTHawking/PinPlusKTKernelSector.lean:242-257`).
- `KTNonSplit prov := ktKernelRep prov ≠ 0` is the missing non-split bit (`lean/SKEFTHawking/PinPlusKTExtension.lean:109-116`).
- `PinPlusBordismLandmark` discloses, as structure fields, a faithful datum, finiteness, an order-sixteen generator, and `card ≤ 16` (`lean/SKEFTHawking/PinPlusGenuineCarrierIso.lean:148-175`); `pinPlus_genuine_carrier_iso_zmod16` only derives the iso from those fields (`lean/SKEFTHawking/PinPlusGenuineCarrierIso.lean:177-187`). It is not an unconditional bordism computation.
- `SpinBordismData` discloses an abstract group, `Bordism ≃+ ℤ`, signature, and a generator signature equation (`lean/SKEFTHawking/SpinBordism.lean:44-56`); `rokhlin_from_bordism` is conditional on that package (`lean/SKEFTHawking/SpinBordism.lean:69-85`).

### PROVED spin-side arithmetic, not a spin-bordism computation

- `k3Form`, `k3Form_isEvenUnimodular`, and `k3Form_latticeSig` build the rank-22 lattice and compute signature `-16` (`lean/SKEFTHawking/SpinSigmaGenerator.lean:119-150`).
- `sig_neg16_of_form_congr_k3` says a structured manifold realizing that form has signature `-16` (`lean/SKEFTHawking/SpinSigmaGenerator.lean:177-188`). The existence of the required structured K3 manifold is not in this statement.

The Novikov opener also contains useful but abstract statement-layer machinery. `interFormInt_isotropic_of_pullback` proves isotropy from an explicit boundary-evaluation hypothesis (`lean/SKEFTHawking/PinPlusKTSpinSigmaNovikovOpener.lean:85-91`). `NovikovBoundaryRestriction` then carries cup functoriality, boundary vanishing, Gram identification, and half-dimensionality as structure fields (`lean/SKEFTHawking/PinPlusKTSpinSigmaNovikovOpener.lean:114-144`), while `NovikovHalfDimAtom` merely asks for a nonempty such structure (`lean/SKEFTHawking/PinPlusKTSpinSigmaNovikovOpener.lean:176-188`). The two conversion theorems between this atom and an abstract Lagrangian atom are proved (`lean/SKEFTHawking/PinPlusKTSpinSigmaNovikovOpener.lean:191-241`), but the reverse construction takes the Lagrangian itself as input and synthesizes abstract cohomology carriers; it does not construct the actual bounding manifold `W`. Thus the docstring's “faithful re-expression” is accurate only as equivalence of two abstract interface Props, not as a geometric Novikov discharge.

### Aspirational ABP apparatus

`ExtBordismBridge` documents four substantial topological hypotheses, but the actual declarations are all `True`: `H1_ko_cohomology` (`lean/SKEFTHawking/ExtBordismBridge.lean:55-68`), `H2_change_of_rings` (`lean/SKEFTHawking/ExtBordismBridge.lean:70-83`), `H3_ass_collapses` (`lean/SKEFTHawking/ExtBordismBridge.lean:85-97`), and `H4_abp_splitting` (`lean/SKEFTHawking/ExtBordismBridge.lean:99-116`). `generation_constraint_chain` clears all four before an arithmetic proof (`lean/SKEFTHawking/ExtBordismBridge.lean:151-168`). Therefore this file proves none of the spectrum/cohomology/change-of-rings/collapse/splitting statements described in its docstrings. This is a direct docstring/theorem-statement mismatch and cannot be counted as substrate for the intended direct Smith computation.

**§4 IS THE DIFFICULTY REAL?**

### Verdict

**The `very_hard` tag is not supported for the literal atlas node; it is supported for one possible honest retyping of the intended geometric Smith route.** The tag currently conflates:

1. an already inhabited thin structure (`lean/SKEFTHawking/CommonOrigin.lean:83-96`);
2. a vacated old-carrier completeness statement (`lean/SKEFTHawking/NonHausdorffBordismCollapse.lean:181-234`);
3. a genuinely large, never-yet-stated faithful theorem requiring a dimension-six carrier, geometric Smith map/exactness, and real spectral-to-bordism identification (`docs/dev-loops/Phase5qH/W_D_ROUTE_DOSSIER.md:65-82`).

For (3), the difficulty evidence is strong: the July E3 attempt stopped at missing bundle/PD/bordism geometry (`docs/dev-loops/Phase5qH/E3_SmithMap_Exactness/LAB_NOTEBOOK_INDEX.md:27-44`); the E5 lane never started the full spectral build (`docs/dev-loops/Phase5qH/E5_SubstrateS_Spectral/LAB_NOTEBOOK.md:1-4`); the route dossier found a second faithful-carrier program plus three geometric constructions and an external source computation (`docs/dev-loops/Phase5qH/W_D_ROUTE_DOSSIER.md:73-82`); and the dedicated large-model attack discovered that the then-current target was unsound rather than proving it (`docs/dev-loops/Phase5qH/LAB_NOTEBOOK_W1.md:169-195`). But these facts support “very hard direct Smith formalization,” not “open literal key with twelve real Lean dependents.”

### (a) Are all routes kernel-proved equivalent, making this node unavoidable?

No—not in the strong form stated by the no-go prose. `KernelNoGos.lean` says the three Thom/KT/Smith routes “all reduce canonically” to one node (`lean/SKEFTHawking/KernelNoGos.lean:232-241`), and the registry repeats that claim (`src/core/constants.py:3898-3916`). The actual backing declarations are only:

- `hbound → hle` (`lean/SKEFTHawking/PinPlusGMWitness.lean:366-383`);
- `hbound → old-carrier iso via KT` (`lean/SKEFTHawking/PinPlusGMWitness.lean:390-394`);
- `hthom → hbound` (`lean/SKEFTHawking/UnorientedThomCapstone.lean:40-57`).

There is no reverse implication among those statements and no theorem there with a faithful Smith hypothesis in its type. `SETTLED_FORKS` itself identifies the “killed_by” evidence as those one-way implications (`docs/dev-loops/SETTLED_FORKS.md:185-199`), then explicitly demotes Smith to an alternative route (`docs/dev-loops/SETTLED_FORKS.md:200-218`). Accordingly:

- kernel-checked source shows that **old `hbound` is sufficient** to feed several old capstones;
- it does **not** show full logical equivalence of Thom, KT, and faithful Smith routes;
- it does **not** show `smith_inflow_z16` is unavoidable;
- even a true equivalence would show common terminal strength, not intrinsic proof difficulty.

This is another docstring/registry-overstatement finding, not merely an absence of convenient naming.

### (b) Has new infrastructure landed since the last serious attempt?

Yes, materially. The serious direct attack was 2026-07-13 (`docs/dev-loops/Phase5qH/LAB_NOTEBOOK_W1.md:169-195`). Since the rebase, the project has built:

- the tethered T2 characteristic-pair carrier and computed mod-eight map (`lean/SKEFTHawking/PinPlusCharPairCarrier.lean:65-123`);
- a nonzero RP4 generator and surjectivity (`lean/SKEFTHawking/RP4CharPairWitness.lean:120-151`);
- unconditional algebraic isotropic-class/reduced-form existence (`lean/SKEFTHawking/KTCompletenessProvider.lean:225-246`);
- exact geometric residual interfaces and their consumers (`lean/SKEFTHawking/KTCompletenessProvider.lean:261-318`; `lean/SKEFTHawking/KTCompletenessTether.lean:232-270`);
- a general smooth regular-value level-set package (`lean/SKEFTHawking/ManifoldRegularValue.lean:647-665`).

The standing handoff independently describes the present architecture as the faithful char-pair carrier plus a proved conditional KT assembly and a named residual row (`docs/dev-loops/Phase5qH/HANDOFF_16_CONVERGENCE.md:58-98`, `docs/dev-loops/Phase5qH/HANDOFF_16_CONVERGENCE.md:102-117`). Its queued work is surgery/Novikov, KRS, handle, collapse, and spin/K3 geometry (`docs/dev-loops/Phase5qH/HANDOFF_16_CONVERGENCE.md:154-236`), not a resumption of E5's direct Smith spectrum computation.

This changes the KT route substantially and gives one genuine ingredient for a Smith zero locus. It does not supply a faithful dimension-six `Pin⁻` carrier, a bundle-valued global Smith construction, exactness, Pontryagin–Thom, Adams convergence, or ABP splitting; the source declarations inventoried in §3 remain conditional/modeling at those points. The current master index therefore reanchors the keystone to KT rather than Smith (`docs/dev-loops/Phase5qH/LAB_NOTEBOOK_INDEX.md:115-124`).

### (c) What kind of blocker is it?

It is first a **statement-shape/atlas-integrity blocker**: there is no honest open Lean proposition named `smith_inflow_z16`, while the registry mixes several historical meanings (`src/core/constants.py:2926-3030`). This must be fixed before difficulty or impact can be measured reliably.

The same audit should resolve the regularity target: the standing goal says `k ≥ 1` (`docs/dev-loops/Phase5qH/HANDOFF_16_CONVERGENCE.md:35-37`), while the current canonical KT provider is at `k = 0` (`lean/SKEFTHawking/PinPlusKTAssemblyResiduals.lean:65-72`). No declaration cited in this dossier proves that the resulting bordism groups are equivalent. That is a source-level statement-shape gap, regardless of the mathematical relationship one ultimately intends.

For the direct Smith interpretation, the blocker is mainly **missing geometric and stable-homotopy infrastructure**, not difficult finite algebra. The finite height-four calculation is already proved (`lean/SKEFTHawking/PinPlusHeight4.lean:54-61`), and the generic exact-segment algebra is already proved (`lean/SKEFTHawking/PinPlusSmithLES.lean:33-64`). Missing are a faithful source carrier, global geometric map, structure transfer, sphere/interval exactness witnesses, and a real PT/ABP/Adams bridge (`docs/dev-loops/Phase5qH/W_D_ROUTE_DOSSIER.md:71-82`). `ExtBordismBridge` does not fill that gap because its topological “hypotheses” are literally `True` (`lean/SKEFTHawking/ExtBordismBridge.lean:67-116`).

For the currently selected KT interpretation, the blocker is **concrete smooth bordism/surgery geometry** plus remaining spin/non-split rows, not the old Smith source computation. `KernelReducesToSpin`, `SpinImageIsTwo`, and `KummerWitness` remain stated interfaces (`lean/SKEFTHawking/PinPlusKTKernelSector.lean:223-257`), and the current assembly still consumes multiple residuals (`lean/SKEFTHawking/PinPlusKTSphereProdCohomology.lean:194-218`).

The evidence is therefore sufficient for a qualified answer: the intended direct-Smith project really is very hard in the present library, but the atlas classification is stale and cannot be used as evidence that this literal node is hard, open, necessary, or the unique keystone.

**§5 CONCRETE NEXT MOVES, RANKED.**

### 1. Retype or retire the atlas node before doing more proof work — confidence: very high

**Build:** replace the registry-only key by one or more honest typed propositions, or retire it as a strategic keystone. At minimum distinguish:

- `SmithInflow` substrate inhabitation (already done);
- faithful `Ω₆^{Pin⁻} ≃+ ZMod 16`;
- a geometric Smith hom on named faithful source/target carriers;
- its two exactness legs;
- the PT/Adams/ABP identification, if that direct route is retained.
- the required regularity level (`k = 0` versus the handoff's `k ≥ 1`) for the actual capstone carrier.

**Reuse:** the generic consumer already has the right four-binder shape (`lean/SKEFTHawking/PinPlusGMDataZ16.lean:249-256`), and the current target carrier is explicit (`lean/SKEFTHawking/PinPlusCharPairCarrier.lean:65-93`). The atlas mismatch is concretely visible because it marks a no-binder theorem as assumed (`lean/atlas_view.json:212292-212295`; theorem at `lean/SKEFTHawking/CommonOrigin.lean:245-251`).

**Genuinely missing:** a source carrier, typed geometric claims, and an explicit smoothness-level transport or a capstone stated directly at the intended regularity. No registry prose can substitute for them. This move does not prove convergence, but it prevents the project from treating an inhabited thin structure as a twelve-edge geometric keystone.

### 2. Continue the selected faithful KT lane by producing tethered surgery outputs — confidence: medium

**Build:** first inhabit `BrownZeroHasIsotropicFramedAttachment`; then construct the H-2 producer `IsotropicFramedAttachingDatum → IsotropicSurgeryOutput`, giving `IsotropicSurgeryOutputSupply` and hence `KernelReducesToSpin`.

**Reuse:** the algebraic isotropic class and reduced form are already proved (`lean/SKEFTHawking/KTCompletenessProvider.lean:225-246`); the source-faithful H-1/H-2 interfaces are stated (`lean/SKEFTHawking/KTCompletenessTether.lean:232-255`); and the consumer to `KernelReducesToSpin` is proved (`lean/SKEFTHawking/KTCompletenessTether.lean:261-270`). This path works on the hardened carrier (`lean/SKEFTHawking/PinPlusCharPairCarrier.lean:65-123`) and follows the repository's recorded route selection (`docs/dev-loops/Phase5qH/LAB_NOTEBOOK_W1.md:563-578`).

**Genuinely missing:** embedded-circle realization with framing, the actual surgery trace, membrane/weld packaging, and the exact quadratic identification. Completing `KernelReducesToSpin` will still leave other assembly residuals such as the spin image/non-split and row/collapse/bridge inputs (`lean/SKEFTHawking/PinPlusKTKernelSector.lean:227-257`; `lean/SKEFTHawking/PinPlusKTSphereProdCohomology.lean:194-218`). Confidence is medium that this is the best mathematical next step, not that it alone closes the theorem.

### 3. If direct Smith is mandated, start with the faithful dimension-six source and map—not more finite charts — confidence: low

**Build:** a smooth/T2/structure-tethered `Ω₆^{Pin⁻}` carrier; a codimension-two Smith hom to the current dimension-four carrier; sphere-bundle and interval-bundle bordisms proving the two exactness legs; then a genuine source iso `Ω₆^{Pin⁻} ≃+ ZMod 16` through PT plus ABP/Adams/AHSS.

**Reuse:** `mLevelSetSingularManifold` supplies a local regular-value manifold package (`lean/SKEFTHawking/ManifoldRegularValue.lean:647-665`); `smith_les_segment_iso` and `pinPlus_zmod16_of_smith_les` supply all generic algebra (`lean/SKEFTHawking/PinPlusSmithLES.lean:33-64`); the finite height is already known (`lean/SKEFTHawking/PinPlusHeight4.lean:54-61`).

**Genuinely missing:** all S1–S6 faithful geometry/source items listed in the route dossier (`docs/dev-loops/Phase5qH/W_D_ROUTE_DOSSIER.md:71-82`). `UNVERIFIED (external mathematics)`: the recorded ABP/literature computation is the needed external mathematical input; this dossier did not independently verify the cited papers. It can in principle be formalized in-tree, but the repository contains no theorem that turns the finite chart into the required geometric dimension-six bordism computation. Confidence is low because this route deliberately recreates a second faithful-carrier program and substantial stable-homotopy infrastructure.

### 4. Do not revive old `hbound`/cardinality work except as a template — confidence: high

**Build:** only port a counting lemma after a finite/cardinality theorem exists for the current faithful carrier; do not attempt to discharge old `hbound` again.

**Reuse:** the generic finite counting pattern at `lean/SKEFTHawking/PinPlusFaithfulnessCardBridge.lean:102-126` may be reusable after retyping.

**Genuinely missing:** finiteness and an upper bound for `T2DataBordismGrp (pinPlusCharPairData prov)`. The old theorem is tied to `pinPlusGMTiedData (k := 0)` (`lean/SKEFTHawking/PinPlusFaithfulnessCardBridge.lean:102-122`), and that carrier's geometry is proved to collapse to grade bookkeeping (`lean/SKEFTHawking/NonHausdorffBordismCollapse.lean:201-234`). Re-proving it there would add no evidence toward the current goal.
