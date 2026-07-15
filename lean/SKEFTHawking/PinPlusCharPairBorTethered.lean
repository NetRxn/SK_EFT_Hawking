/-
# Phase 5q.H W-A arm 4 — ROUND 6 SPEC BUILD: the ιW W-TETHER + Q manifold discipline + per-op provider

GATE ROUND 6 (`PinPlusCharPairFlipGate`) failed the flipped carrier on **F4 — the membrane is
UNTETHERED to the bordism** (`GeoRealizationTied.Q` is an arbitrary compact-T2 `TopCat` with NO tie to
`b.W`), which lets `CharPairBorRealized.transport` move a witness to ANY other bordism between the same
ends, and lets `isT2DataBordant_pinPlusCharPair_factors` FACTOR the structured relation into an
ends-only condition. This module discharges the frozen round-6 spec (`untethered-membrane-factors-relation`):

* **Item 1 — THE W-TETHER (primary).** `CharPairBorRealizedTethered` strengthens `CharPairBorRealized`
  with a closed embedding `ιW : C(↑real.Q, b.W)` of the realized membrane INTO the bordism carrier,
  plus the COMMUTING GLUE (`glueσ`/`glueτ`) that ties `ιW ∘ real.ι` on each boundary component to the
  bordism's boundary map `b.e` through the ends' embeddings `σ.emb`/`τ.emb` and the clopen-split
  identifications `homσ`/`homτ`. After the tether the e₈ exploit demands an e₈-kernel membrane INSIDE
  the specific `b.W` (e.g. `(ℝP⁴)⁴ × I` for the doubling) — the genuinely geometric content the §5
  banner claimed. `transport` to a different `b'` no longer type-checks (`ιW`'s target is `b.W`,
  `b`-specific), and the factorization cannot re-derive (`mk` REQUIRES the tether, not synthesizable
  from `real` alone). See §7 for the F4-dead self-tests.

* **Item 2 — manifold discipline on `Q`.** `chartQ` carries a `ChartedSpace` over the 3-dim membrane
  model `ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1)` (2 for the characteristic
  surface + 1 for the collar), pinning `dim Q = 3` and ruling out the CW pathologies an abstract
  compact-T2 admits. JUDGMENT (recorded): full `IsManifold` (smooth-structure compatibility across the
  disjoint-union realization) is disproportionate given the abstract `Q` and the missing sum-`IsManifold`
  glue; a charted-space + dimension certificate is the honest form the gate authorizes.

* **Item 3 — the per-op provider (kills F6).** `CharPairWProviderPerOp` supplies `WAdmPinned` for
  EXACTLY the op-bordism family the eight ops consume — `reflCylinder`, `doublingBordism`, the three
  `mapCylinder`s, and a `add`-closure — instead of the uninhabitable `∀ b, WAdmPinned b`. Every field
  is a product-cylinder admissibility, so a Track-2 `CylinderWAdmPinned`-family deliverable discharges
  the whole family (the plug-in seam is documented in §6; the sole missing wire is the abstract-`I` ↔
  concrete-`cylW`/`cylModel` bridge, a named Track-2 residual).

SCOPE: the tethered structure is a NEW structure `extends CharPairBorRealized`, so the round-6 gate
(`PinPlusCharPairFlipGate`, which references the OLD `mkCharPairBorRealized`) and the still-flipped
carrier keep compiling in-slot. The lead's round-7 re-flip re-points the carrier `Bor` at
`CharPairBorRealizedTethered` and re-parameterizes it by `CharPairWProviderPerOp`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusCharPairAddRealization

open scoped Manifold
open Topology
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.BordismTheory
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.SingularCohomologyDisjointSum
open SKEFTHawking.SingularKroneckerBasisBridge
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularCohomologyPairRestrict
open SKEFTHawking.PinPlusCharPairSurfaceTie
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairMembraneGeoRealization
open SKEFTHawking.PinPlusCharPairRealizationTied
open SKEFTHawking.PinPlusCharPairCylRealization
open SKEFTHawking.PinPlusCharPairNegRealization
open SKEFTHawking.PinPlusCharPairMapCylRealization
open SKEFTHawking.PinPlusCharPairBorRealizedOps
open SKEFTHawking.PinPlusCharPairAddRealization
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.PinPlusCharPairBorRealized

namespace SKEFTHawking.PinPlusCharPairBorTethered

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]
variable {s t u : SingularManifold.{0} PUnit.{1} k I}

/-- The 3-dim membrane model: `EuclideanSpace ℝ (Fin 2)` (the characteristic surface) ⊕ collar
`EuclideanHalfSpace 1` (the `[0,1]` factor). The tethered membrane `Q = Σ × [0,1]` (or disjoint unions
thereof) charts over this model, pinning `dim Q = 3`. -/
abbrev MembraneModel : Type := ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1)

/-! ## §1. The base helper `mkCharPairBorRealizedOfWAdm` — item-1 admissibility from a single
`WAdmPinned b` (not the `∀`-provider), so the per-op provider (§3) can feed it directly. -/

/-- Assemble a `CharPairBorRealized` from a SINGLE `WAdmPinned b` (per-op admissibility) plus the
concretely-buildable data. `mkCharPairBorRealized prov b … = mkCharPairBorRealizedOfWAdm (prov.wadm b) …`. -/
noncomputable def mkCharPairBorRealizedOfWAdm {s t : SingularManifold.{0} PUnit.{1} k I}
    {b : Bordism (I.prod (𝓡∂ 1)) s t} {σ : CharPairStrBundled I s} {τ : CharPairStrBundled I t}
    (wadmP : WAdmPinned b) (hWT2 : T2Space b.W)
    (real : GeoRealizationTied (TopCat.of σ.surf.M) (TopCat.of τ.surf.M) σ.basis τ.basis)
    (htaylor : TaylorLegVanishes σ.q τ.q (real.toMembrane σ.q τ.q).L)
    (hlag : JointLagrangian σ.q τ.q (real.toMembrane σ.q τ.q).L) :
    CharPairBorRealized b σ τ where
  hWT2 := hWT2
  P14 := wadmP.wadm.P14
  P23 := wadmP.wadm.P23
  hwu := wadmP.wadm.hwu
  pin14 := wadmP.pin14
  pin23 := wadmP.pin23
  real := real
  htaylor := htaylor
  hlag := hlag

/-! ## §2. THE TETHERED `Bor` structure — the W-tether + manifold discipline on top of the realized
`Bor`. -/

/-- **THE W-TETHERED realized+pinned characteristic-pair bordism datum** (round-6 Item 1+2). Extends
`CharPairBorRealized` with the membrane→bordism tether and a charted-space certificate on `Q`:

* `ιW : C(↑real.Q, b.W)` — a **closed embedding** of the realized membrane INTO the bordism carrier
  `b.W` (F4 fix: `Q ⊆ W` at the type level);
* `glueσ`/`glueτ` — the **commuting glue**: `ιW ∘ real.ι` on each boundary component factors through
  `b`'s boundary map `b.e` via the ends' embeddings `σ.emb`/`τ.emb` and the clopen-split
  identifications `homσ`/`homτ`. This is what forces the e₈ membrane (if any) to sit inside THIS `b.W`
  specifically;
* `chartQ` — the manifold-discipline certificate (Item 2): `Q` charts over the 3-dim membrane model.

`transport` (a `b`-independent witness move) and `isT2DataBordant_…_factors` (the ends-only
factorization) CANNOT re-derive against this shape — see §7. -/
structure CharPairBorRealizedTethered {s t : SingularManifold.{0} PUnit.{1} k I}
    (b : Bordism (I.prod (𝓡∂ 1)) s t) (σ : CharPairStrBundled I s) (τ : CharPairStrBundled I t)
    extends CharPairBorRealized b σ τ where
  /-- **THE W-TETHER**: a closed embedding of the realized membrane `Q` into the bordism carrier `W`. -/
  ιW : C(↑real.Q, b.W)
  /-- the tether is a closed embedding (`Q ⊆ W` faithfully). -/
  hιWce : IsClosedEmbedding ιW
  /-- **glue (σ-end)**: `ιW ∘ real.ι` on the σ-boundary component `Σ_σ = sub real.U` factors through
  `b.e ∘ Sum.inl ∘ σ.emb` read via the identification `homσ`. -/
  glueσ : ∀ x : ↑(sub real.U),
    ιW (real.ι (subInclCM real.U x)) = b.e (Sum.inl (σ.emb (real.homσ x)))
  /-- **glue (τ-end)**: `ιW ∘ real.ι` on the τ-boundary component `Σ_τ = sub real.Uᶜ` factors through
  `b.e ∘ Sum.inr ∘ τ.emb` read via the identification `homτ`. -/
  glueτ : ∀ x : ↑(sub real.Uᶜ),
    ιW (real.ι (subInclCM real.Uᶜ x)) = b.e (Sum.inr (τ.emb (real.homτ x)))
  /-- **Item 2 (manifold discipline)**: `Q` charts over the 3-dim membrane model — a charted-space +
  dimension certificate ruling out CW pathologies. -/
  chartQ : ChartedSpace MembraneModel ↑real.Q

/-! ## §3. THE PER-OP PROVIDER (Item 3, kills F6) — `WAdmPinned` for EXACTLY the op-bordism family. -/

/-- **The per-op W-admissibility provider** — supplies `WAdmPinned` for the FINITE op-bordism family
the eight ops consume, NOT the uninhabitable `∀ b, WAdmPinned b` (F6 fix). Every field is a
product-cylinder admissibility (`W = M × [0,1]` up to the defining diffeos / disjoint unions), so a
Track-2 `CylinderWAdmPinned`-family deliverable discharges the whole family (§6 plug-in seam). -/
structure CharPairWProviderPerOp (I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2))))
    [I.Boundaryless] (k : WithTop ℕ∞) : Type (u_1 + 1) where
  /-- reflexive-cylinder admissibility (`cylBor`, `revBor` end-reversals reuse the input's).
  **F7-A (round 7): quantified over the BUNDLED end** — the provider need only serve
  cert-carrying structured manifolds (`w₂`-controlled), making the family honest-inhabitable;
  the bare-`s` form was mathematically uninhabitable (any `w₂(s.M) ≠ 0` emptied it). -/
  cyl : ∀ {s : SingularManifold.{0} PUnit.{1} k I},
    CharPairStrBundled I s → WAdmPinned (reflCylinder s)
  /-- doubling-bordism admissibility (`negBor`) — bundled-end quantified (F7-A). -/
  doubling : ∀ {s : SingularManifold.{0} PUnit.{1} k I},
    CharPairStrBundled I s → WAdmPinned (doublingBordism s)
  /-- mapping-cylinder admissibility (`unitBor`/`commBor`/`assocBor`, each a `mapCylinder` of a
  diffeo) — bundled-ends quantified (F7-A). -/
  mapCyl : ∀ {s t : SingularManifold.{0} PUnit.{1} k I} (φ : Diffeomorph I I s.M t.M k)
    (hf : t.f ∘ φ = s.f), CharPairStrBundled I s → CharPairStrBundled I t →
    WAdmPinned (mapCylinder φ hf)
  /-- **the `add`-closure**: disjoint union of two admissibilities (`addBor`). -/
  addClosure : ∀ {s₁ t₁ s₂ t₂ : SingularManifold.{0} PUnit.{1} k I}
    {b₁ : Bordism (I.prod (𝓡∂ 1)) s₁ t₁} {b₂ : Bordism (I.prod (𝓡∂ 1)) s₂ t₂},
    WAdmPinned b₁ → WAdmPinned b₂ → WAdmPinned (b₁.add b₂)

/-- Reconstruct a `WAdmPinned b` from a realized+pinned witness — its item-1 block IS a pinned
W-admissibility datum. Used by `addBorTethered` (the `add`-closure consumes the two inputs' pins). -/
def CharPairBorRealized.toWAdmPinned {s t : SingularManifold.{0} PUnit.{1} k I}
    {b : Bordism (I.prod (𝓡∂ 1)) s t} {σ : CharPairStrBundled I s} {τ : CharPairStrBundled I t}
    (β : CharPairBorRealized b σ τ) : WAdmPinned b :=
  ⟨⟨β.P14, β.P23, β.hwu⟩, β.pin14, β.pin23⟩

/-! ## §4. The eight TETHERED op realizations. Each reuses its base realization/Taylor-leg/Lagrangian
and adds the concrete geometric tether `ιW` (a product/sum closed embedding) + the commuting glue. -/

/-- **`cylBor` TETHERED** — the reflexive cylinder `Q = Σ_σ × [0,1]` embeds into `W = s.M × [0,1]` by
`σ.emb × id` (a product of closed embeddings); the glue is the two-slice commuting square
`(x,0)/(x,1) ↦ (emb x, ⊥)/(emb x, ⊤)`. -/
noncomputable def cylBorTethered (prov : CharPairWProviderPerOp I k) (σ : CharPairStrBundled I s) :
    CharPairBorRealizedTethered (reflCylinder s) σ σ :=
  haveI := σ.surfT2
  haveI := σ.t2
  { hWT2 := inferInstanceAs (T2Space (s.M × Set.Icc (0 : ℝ) 1))
    P14 := (prov.cyl σ).wadm.P14
    P23 := (prov.cyl σ).wadm.P23
    hwu := (prov.cyl σ).wadm.hwu
    pin14 := (prov.cyl σ).pin14
    pin23 := (prov.cyl σ).pin23
    real := cylRealizationTied (TopCat.of σ.surf.M) σ.basis
    htaylor := by rw [cylRealizationTied_toMembrane_L]; exact taylorLeg_cyl σ.q
    hlag := by rw [cylRealizationTied_toMembrane_L]; exact lagrangian_cyl σ.q
    ιW := ⟨Prod.map σ.emb id, σ.embSmooth.continuous.prodMap continuous_id⟩
    hιWce := (σ.embSmooth.continuous.prodMap continuous_id).isClosedEmbedding
      (σ.embInj.prodMap Function.injective_id)
    glueσ := by
      rintro ⟨_, y, rfl⟩
      show Prod.map σ.emb id (cylBdryIncl (TopCat.of σ.surf.M) (Sum.inl y))
          = (reflCylinder s).e (Sum.inl (σ.emb
              (IsClosedEmbedding.inl.isEmbedding.toHomeomorph.symm ⟨Sum.inl y, y, rfl⟩)))
      rw [IsEmbedding.toHomeomorph_symm_apply]
      rfl
    glueτ := by
      rintro ⟨(a | y), hp⟩
      · exact absurd ⟨a, rfl⟩ hp
      · show Prod.map σ.emb id (cylBdryIncl (TopCat.of σ.surf.M) (Sum.inr y))
            = (reflCylinder s).e (Sum.inr (σ.emb
                (((Homeomorph.setCongr Set.compl_range_inl).trans
                  IsClosedEmbedding.inr.isEmbedding.toHomeomorph.symm) ⟨Sum.inr y, hp⟩)))
        rw [Homeomorph.trans_apply,
          show (Homeomorph.setCongr Set.compl_range_inl) ⟨Sum.inr y, hp⟩
              = ⟨Sum.inr y, ⟨y, rfl⟩⟩ from rfl,
          IsEmbedding.toHomeomorph_symm_apply]
        rfl
    chartQ := by
      show ChartedSpace MembraneModel (↑(TopCat.of σ.surf.M) × ↑(TopCat.of unitInterval))
      infer_instance }

/-- **`revBor` TETHERED** — end-reversal keeps the SAME surface/basis/embedding (only `q` negates), so
the SAME membrane `Q`, tether `ιW`, and glue transport unchanged (`(charPairBundledRevStr σ).emb = σ.emb`,
`(charPairBundledRevStr σ).surf = σ.surf`). -/
noncomputable def revBorTethered {b : Bordism (I.prod (𝓡∂ 1)) s t}
    {σ : CharPairStrBundled I s} {τ : CharPairStrBundled I t}
    (β : CharPairBorRealizedTethered b σ τ) :
    CharPairBorRealizedTethered b (charPairBundledRevStr σ) (charPairBundledRevStr τ) :=
  { toCharPairBorRealized := revBorRealized β.toCharPairBorRealized
    ιW := β.ιW
    hιWce := β.hιWce
    glueσ := β.glueσ
    glueτ := β.glueτ
    chartQ := β.chartQ }

/-- **`symmBor` TETHERED** — bordism reversal swaps the ends; the realization transports by the
end-swap `GeoRealizationTied.swap` (same `Q`/`ι`, complemented clopen split), and `b.symm.W = b.W`,
so the tether `ιW` is reused. The glue transposes: `b.symm.e = b.e ∘ Sum.swap` turns the swapped
σ-end's glue into `β.glueτ` and the swapped τ-end's into `β.glueσ` (routed through `compl_compl`). -/
noncomputable def symmBorTethered {b : Bordism (I.prod (𝓡∂ 1)) s t}
    {σ : CharPairStrBundled I s} {τ : CharPairStrBundled I t}
    (β : CharPairBorRealizedTethered b σ τ) :
    CharPairBorRealizedTethered b.symm τ σ :=
  { toCharPairBorRealized := symmBorRealized β.toCharPairBorRealized
    ιW := β.ιW
    hιWce := β.hιWce
    glueσ := β.glueτ
    glueτ := fun x => β.glueσ ((Homeomorph.setCongr (compl_compl β.real.U)) x)
    chartQ := β.chartQ }

/-- **`negBor` TETHERED** — the doubling op `(M,σ̄) ⊔ (M,σ) → ∅`. Same cylinder membrane
`Q = Σ_σ × [0,1]` embedded into `W = s.M × [0,1]` by `σ.emb × id`; the σ-end is the WHOLE boundary
(`U = univ`), so the glue routes both slices through `(doublingBordism s).e` and the τ-end is empty. -/
noncomputable def negBorTethered (prov : CharPairWProviderPerOp I k) (σ : CharPairStrBundled I s) :
    CharPairBorRealizedTethered (doublingBordism s)
      (charPairBundledSumStr (charPairBundledRevStr σ) σ) charPairBundledEmpty :=
  haveI := σ.surfT2
  haveI hIE : IsEmpty ((charPairBundledEmpty
      : CharPairStrBundled I (emptySM : SingularManifold.{0} PUnit.{1} k I)).surf.M) :=
    inferInstanceAs (IsEmpty PEmpty)
  have hSe : IsMetabolic (Z4Quadratic.neg (stdQuadratic 0))
      (⊤ : Submodule (ZMod 2) (Fin 0 → ZMod 2)) :=
    ⟨fun l _ => by rw [Subsingleton.elim l 0]; exact (Z4Quadratic.neg (stdQuadratic 0)).q_zero,
     fun _ _ => Submodule.mem_top⟩
  have hSs : IsMetabolic (charPairSumStr (charPairRevStr σ.toCharPairStr) σ.toCharPairStr).q
      ((cylLagrangian σ.n).comap (LinearMap.funLeft (ZMod 2) (ZMod 2) finSumFinEquiv)) :=
    (diag_metabolic (neg σ.q) σ.q (fun a => neg_add_cancel _) rfl).reindex finSumFinEquiv
  have hmeta := hSs.orthSum hSe
  { hWT2 := by
      haveI := σ.t2
      exact inferInstanceAs (T2Space (s.M × Set.Icc (0 : ℝ) 1))
    P14 := (prov.doubling σ).wadm.P14
    P23 := (prov.doubling σ).wadm.P23
    hwu := (prov.doubling σ).wadm.hwu
    pin14 := (prov.doubling σ).pin14
    pin23 := (prov.doubling σ).pin23
    real := doublingRealizationTied (TopCat.of σ.surf.M) σ.basis
      (TopCat.of (charPairBundledEmpty (I := I) (k := k)).surf.M)
      (charPairBundledEmpty (I := I) (k := k)).basis
    htaylor := by
      show TaylorLegVanishes _ _ (LinearMap.ker (transportedBInc
        (doublingRealizationTied (TopCat.of σ.surf.M) σ.basis
          (TopCat.of (charPairBundledEmpty (I := I) (k := k)).surf.M)
          (charPairBundledEmpty (I := I) (k := k)).basis).toData))
      rw [doublingRealizationTied_transportedBInc]
      show TaylorLegVanishes _ _ (LinearMap.ker (negBorBInc σ.n))
      rw [negBorBInc_ker]
      exact hmeta.1
    hlag := by
      show JointLagrangian _ _ (LinearMap.ker (transportedBInc
        (doublingRealizationTied (TopCat.of σ.surf.M) σ.basis
          (TopCat.of (charPairBundledEmpty (I := I) (k := k)).surf.M)
          (charPairBundledEmpty (I := I) (k := k)).basis).toData))
      rw [doublingRealizationTied_transportedBInc]
      show JointLagrangian _ _ (LinearMap.ker (negBorBInc σ.n))
      rw [negBorBInc_ker]
      exact hmeta.2
    ιW := ⟨Prod.map σ.emb id, σ.embSmooth.continuous.prodMap continuous_id⟩
    hιWce := by
      haveI := σ.t2
      exact (σ.embSmooth.continuous.prodMap continuous_id).isClosedEmbedding
        (σ.embInj.prodMap Function.injective_id)
    glueσ := by
      rintro ⟨(y | y), _⟩
      · show Prod.map σ.emb id (cylBdryIncl (TopCat.of σ.surf.M) (Sum.inl y))
            = (doublingBordism s).e (Sum.inl (Sum.map σ.emb σ.emb
                (Homeomorph.Set.univ ((σ.surf.M) ⊕ (σ.surf.M)) ⟨Sum.inl y, trivial⟩)))
        rfl
      · show Prod.map σ.emb id (cylBdryIncl (TopCat.of σ.surf.M) (Sum.inr y))
            = (doublingBordism s).e (Sum.inl (Sum.map σ.emb σ.emb
                (Homeomorph.Set.univ ((σ.surf.M) ⊕ (σ.surf.M)) ⟨Sum.inr y, trivial⟩)))
        rfl
    glueτ := by
      rintro ⟨v, hv⟩
      exact (hv (Set.mem_univ v)).elim
    chartQ := by
      show ChartedSpace MembraneModel (↑(TopCat.of σ.surf.M) × ↑(TopCat.of unitInterval))
      infer_instance }

/-- **`unitBor` TETHERED** — the `σ ⊔ ∅ → σ` unit, twisted cylinder `Q = Σ_{σ⊔∅} × [0,1]` embedded
into `W = (s.M ⊕ ∅) × [0,1]` by `(σ⊔∅).emb × id`; the τ-end is retargeted through the sum-with-empty
homeomorphism, matching the mapping cylinder's `φ.symm` slice. -/
noncomputable def unitBorTethered (prov : CharPairWProviderPerOp I k) (σ : CharPairStrBundled I s) :
    CharPairBorRealizedTethered (mapCylinder (Diffeomorph.sumEmpty I s.M k (M' := emptySM.M))
      (by funext z; cases z with | inl m => rfl | inr e => exact (IsEmpty.false e).elim))
      (charPairBundledSumStr σ charPairBundledEmpty) σ :=
  haveI := σ.surfT2
  haveI := (charPairBundledSumStr σ charPairBundledEmpty).surfT2
  haveI : IsEmpty ((charPairBundledEmpty
      : CharPairStrBundled I (emptySM : SingularManifold.{0} PUnit.{1} k I)).surf.M) :=
    inferInstanceAs (IsEmpty PEmpty)
  have hqS : (charPairSumStr σ.toCharPairStr charPairEmptyStr).q
      = σ.q.reindex ((Equiv.sumEmpty (Fin σ.n) (Fin 0)).symm.trans finSumFinEquiv) := by
    show (Z4Quadratic.orthSum σ.q (stdQuadratic 0)).reindex finSumFinEquiv = _
    rw [orthSum_stdZero_eq, reindex_trans]
  have hmeta : IsMetabolic (jointEnhancement (charPairBundledSumStr σ charPairBundledEmpty).q σ.q)
      (graphSub (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (unitReindex σ).symm)) := by
    show IsMetabolic (jointEnhancement (charPairSumStr σ.toCharPairStr charPairEmptyStr).q σ.q) _
    rw [show jointEnhancement (charPairSumStr σ.toCharPairStr charPairEmptyStr).q σ.q
        = Z4Quadratic.orthSum (charPairSumStr σ.toCharPairStr charPairEmptyStr).q (Z4Quadratic.neg σ.q)
        from rfl, hqS]
    exact commonReindex_metabolic σ.q ((Equiv.sumEmpty (Fin σ.n) (Fin 0)).symm.trans finSumFinEquiv)
      (Equiv.refl (Fin σ.n))
  have hnat : transportBasisChange (TopCat.of (charPairBundledSumStr σ charPairBundledEmpty).surf.M)
      (charPairBundledSumStr σ charPairBundledEmpty).basis (TopCat.of σ.surf.M) σ.basis
      (unitEndHomeo σ)
        = LinearMap.funLeft (ZMod 2) (ZMod 2) ((unitReindex σ) : Fin (σ.n + 0) → Fin σ.n) := by
    refine transportBasisChange_eq_funLeft _ _ _ _ _ ((unitReindex σ) : Fin (σ.n + 0) → Fin σ.n) ?_
    intro i
    show cohomologyPullback (inlMap (TopCat.of σ.surf.M)
        (TopCat.of (charPairBundledEmpty
          : CharPairStrBundled I (emptySM : SingularManifold.{0} PUnit.{1} k I)).surf.M)) 1
        ((sumBasis σ.basis (charPairBundledEmpty
          : CharPairStrBundled I (emptySM : SingularManifold.{0} PUnit.{1} k I)).basis).symm
          (Pi.single i 1))
      = σ.basis.symm (Pi.single ((unitReindex σ) i) 1)
    rw [pullback_inlMap_sumBasis_symm]
    congr 1
    funext j
    rw [Pi.single_apply, Pi.single_apply,
      show (unitReindex σ) i = (Equiv.sumEmpty (Fin σ.n) (Fin 0)) (finSumFinEquiv.symm i) from rfl]
    rcases hw : finSumFinEquiv.symm i with a | b
    · have hi : i = finSumFinEquiv (Sum.inl a) := by rw [← hw, Equiv.apply_symm_apply]
      rw [hi, Equiv.sumEmpty_apply_inl]
      have hcond : (finSumFinEquiv (Sum.inl j : Fin σ.n ⊕ Fin 0) = finSumFinEquiv (Sum.inl a))
          ↔ (j = a) :=
        ⟨fun hc => Sum.inl_injective (finSumFinEquiv.injective hc), fun hc => by rw [hc]⟩
      exact if_congr hcond rfl rfl
    · exact b.elim0
  have wadmP : WAdmPinned (mapCylinder (Diffeomorph.sumEmpty I s.M k (M' := emptySM.M))
      (show (s : SingularManifold PUnit k I).f ∘ ⇑(Diffeomorph.sumEmpty I s.M k (M' := emptySM.M))
          = (s.sum (emptySM : SingularManifold.{0} PUnit.{1} k I)).f by
        funext z; cases z with | inl m => rfl | inr e => exact (IsEmpty.false e).elim)) :=
    prov.mapCyl _ _ (charPairBundledSumStr σ charPairBundledEmpty) σ
  { hWT2 := by
      haveI := σ.t2
      haveI : T2Space (emptySM (X := PUnit) (k := k) (I := I)).M := ⟨fun x => isEmptyElim x⟩
      exact inferInstanceAs (T2Space ((s.M ⊕ emptySM.M) × Set.Icc (0 : ℝ) 1))
    P14 := wadmP.wadm.P14
    P23 := wadmP.wadm.P23
    hwu := wadmP.wadm.hwu
    pin14 := wadmP.pin14
    pin23 := wadmP.pin23
    real := mapCylRealizationTied (TopCat.of (charPairBundledSumStr σ charPairBundledEmpty).surf.M)
      (charPairBundledSumStr σ charPairBundledEmpty).basis (TopCat.of σ.surf.M) σ.basis
      (unitEndHomeo σ)
    htaylor := by
      show TaylorLegVanishes _ _ (LinearMap.ker (transportedBInc
        (mapCylRealizationTied (TopCat.of (charPairBundledSumStr σ charPairBundledEmpty).surf.M)
          (charPairBundledSumStr σ charPairBundledEmpty).basis (TopCat.of σ.surf.M) σ.basis
          (unitEndHomeo σ)).toData))
      rw [mapCylRealizationTied_transportedBInc, hnat]
      erw [ker_mapCylBd_funLeft (unitReindex σ)]
      exact hmeta.1
    hlag := by
      show JointLagrangian _ _ (LinearMap.ker (transportedBInc
        (mapCylRealizationTied (TopCat.of (charPairBundledSumStr σ charPairBundledEmpty).surf.M)
          (charPairBundledSumStr σ charPairBundledEmpty).basis (TopCat.of σ.surf.M) σ.basis
          (unitEndHomeo σ)).toData))
      rw [mapCylRealizationTied_transportedBInc, hnat]
      erw [ker_mapCylBd_funLeft (unitReindex σ)]
      exact hmeta.2
    ιW := ⟨Prod.map (charPairBundledSumStr σ charPairBundledEmpty).emb id,
      (charPairBundledSumStr σ charPairBundledEmpty).embSmooth.continuous.prodMap continuous_id⟩
    hιWce := by
      haveI := σ.t2
      haveI : T2Space (emptySM (X := PUnit) (k := k) (I := I)).M := ⟨fun x => isEmptyElim x⟩
      haveI : T2Space (s.sum (emptySM : SingularManifold.{0} PUnit.{1} k I)).M :=
        inferInstanceAs (T2Space (s.M ⊕ emptySM.M))
      exact ((charPairBundledSumStr σ charPairBundledEmpty).embSmooth.continuous.prodMap
        continuous_id).isClosedEmbedding
        ((charPairBundledSumStr σ charPairBundledEmpty).embInj.prodMap Function.injective_id)
    glueσ := by
      rintro ⟨_, w, rfl⟩
      show Prod.map (charPairBundledSumStr σ charPairBundledEmpty).emb id
          (cylBdryIncl (TopCat.of (charPairBundledSumStr σ charPairBundledEmpty).surf.M) (Sum.inl w))
          = (mapCylinder (Diffeomorph.sumEmpty I s.M k (M' := emptySM.M))
              (by funext z; cases z with | inl m => rfl | inr e => exact (IsEmpty.false e).elim)).e
              (Sum.inl ((charPairBundledSumStr σ charPairBundledEmpty).emb
                (IsClosedEmbedding.inl.isEmbedding.toHomeomorph.symm ⟨Sum.inl w, w, rfl⟩)))
      rw [IsEmbedding.toHomeomorph_symm_apply]
      rfl
    glueτ := by
      rintro ⟨(a | w), hp⟩
      · exact absurd ⟨a, rfl⟩ hp
      · rcases w with a | e
        · show Prod.map (charPairBundledSumStr σ charPairBundledEmpty).emb id
              (cylBdryIncl (TopCat.of (charPairBundledSumStr σ charPairBundledEmpty).surf.M)
                (Sum.inr (Sum.inl a)))
              = (mapCylinder (Diffeomorph.sumEmpty I s.M k (M' := emptySM.M))
                  (by funext z; cases z with | inl m => rfl | inr e => exact (IsEmpty.false e).elim)).e
                  (Sum.inr (σ.emb
                    ((((Homeomorph.setCongr Set.compl_range_inl).trans
                        IsClosedEmbedding.inr.isEmbedding.toHomeomorph.symm).trans
                        (unitEndHomeo σ).symm) ⟨Sum.inr (Sum.inl a), hp⟩)))
          rw [Homeomorph.trans_apply, Homeomorph.trans_apply]
          erw [IsEmbedding.toHomeomorph_symm_apply]
          show Prod.map (charPairBundledSumStr σ charPairBundledEmpty).emb id
              (cylBdryIncl (TopCat.of (charPairBundledSumStr σ charPairBundledEmpty).surf.M)
                (Sum.inr (Sum.inl a)))
              = (mapCylinder (Diffeomorph.sumEmpty I s.M k (M' := emptySM.M))
                  (by funext z; cases z with | inl m => rfl | inr e => exact (IsEmpty.false e).elim)).e
                  (Sum.inr (σ.emb (Homeomorph.sumEmpty σ.surf.M
                    (charPairBundledEmpty
                      : CharPairStrBundled I (emptySM : SingularManifold.{0} PUnit.{1} k I)).surf.M
                    (Sum.inl a))))
          rfl
        · exact e.elim
    chartQ := by
      show ChartedSpace MembraneModel
        (↑(TopCat.of (charPairBundledSumStr σ charPairBundledEmpty).surf.M)
          × ↑(TopCat.of unitInterval))
      infer_instance }

/-- **`commBor` TETHERED** — the `σ ⊔ τ → τ ⊔ σ` commutativity, twisted cylinder over `Σ_{σ⊔τ}`
embedded into `W = (s.M ⊕ t.M) × [0,1]` by `(σ⊔τ).emb × id`; the τ-end is retargeted through the
surface swap, matching the mapping cylinder's `(sumComm).symm` slice. -/
noncomputable def commBorTethered (prov : CharPairWProviderPerOp I k)
    (σ : CharPairStrBundled I s) (τ : CharPairStrBundled I t) :
    CharPairBorRealizedTethered (mapCylinder (Diffeomorph.sumComm I s.M k t.M)
      (by funext z; rcases z with z | z <;> rfl))
      (charPairBundledSumStr σ τ) (charPairBundledSumStr τ σ) :=
  haveI := (charPairBundledSumStr σ τ).surfT2
  haveI := (charPairBundledSumStr τ σ).surfT2
  have hmeta : IsMetabolic
      (jointEnhancement (charPairBundledSumStr σ τ).q (charPairBundledSumStr τ σ).q)
      (graphSub (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (commReindex σ τ).symm)) := by
    show IsMetabolic (Z4Quadratic.orthSum (charPairSumStr σ.toCharPairStr τ.toCharPairStr).q
      (Z4Quadratic.neg (charPairSumStr τ.toCharPairStr σ.toCharPairStr).q)) _
    rw [show (charPairSumStr σ.toCharPairStr τ.toCharPairStr).q
          = (Z4Quadratic.orthSum σ.q τ.q).reindex finSumFinEquiv from rfl,
        show (charPairSumStr τ.toCharPairStr σ.toCharPairStr).q
          = (Z4Quadratic.orthSum σ.q τ.q).reindex
              ((Equiv.sumComm (Fin σ.n) (Fin τ.n)).trans finSumFinEquiv) from by
          show (Z4Quadratic.orthSum τ.q σ.q).reindex finSumFinEquiv = _
          rw [orthSum_comm_eq σ.q τ.q, reindex_trans]]
    exact commonReindex_metabolic (Z4Quadratic.orthSum σ.q τ.q) finSumFinEquiv
      ((Equiv.sumComm (Fin σ.n) (Fin τ.n)).trans finSumFinEquiv)
  have hnat : transportBasisChange (TopCat.of (charPairBundledSumStr σ τ).surf.M)
      (charPairBundledSumStr σ τ).basis (TopCat.of (charPairBundledSumStr τ σ).surf.M)
      (charPairBundledSumStr τ σ).basis (commEndHomeo σ τ)
        = LinearMap.funLeft (ZMod 2) (ZMod 2)
            ((commReindex σ τ) : Fin (σ.n + τ.n) → Fin (τ.n + σ.n)) := by
    refine transportBasisChange_eq_funLeft _ _ _ _ _
      ((commReindex σ τ) : Fin (σ.n + τ.n) → Fin (τ.n + σ.n)) ?_
    intro i
    show cohomologyPullback (⟨Homeomorph.sumComm (τ.surf.M) (σ.surf.M),
        (Homeomorph.sumComm (τ.surf.M) (σ.surf.M)).continuous⟩ :
        C(↑(sumSpace (TopCat.of τ.surf.M) (TopCat.of σ.surf.M)),
          ↑(sumSpace (TopCat.of σ.surf.M) (TopCat.of τ.surf.M)))) 1
        ((sumBasis σ.basis τ.basis).symm (Pi.single i 1))
      = (sumBasis τ.basis σ.basis).symm (Pi.single ((commReindex σ τ) i) 1)
    erw [pullback_sumComm_sumBasis_symm]
    rfl
  have wadmP := prov.mapCyl (s := s.sum t) (t := t.sum s) (Diffeomorph.sumComm I s.M k t.M)
    (by funext z; rcases z with z | z <;> rfl)
    (charPairBundledSumStr σ τ) (charPairBundledSumStr τ σ)
  { hWT2 := by
      haveI := σ.t2; haveI := τ.t2
      exact inferInstanceAs (T2Space ((s.M ⊕ t.M) × Set.Icc (0 : ℝ) 1))
    P14 := wadmP.wadm.P14
    P23 := wadmP.wadm.P23
    hwu := wadmP.wadm.hwu
    pin14 := wadmP.pin14
    pin23 := wadmP.pin23
    real := mapCylRealizationTied (TopCat.of (charPairBundledSumStr σ τ).surf.M)
      (charPairBundledSumStr σ τ).basis (TopCat.of (charPairBundledSumStr τ σ).surf.M)
      (charPairBundledSumStr τ σ).basis (commEndHomeo σ τ)
    htaylor := by
      show TaylorLegVanishes _ _ (LinearMap.ker (transportedBInc
        (mapCylRealizationTied (TopCat.of (charPairBundledSumStr σ τ).surf.M)
          (charPairBundledSumStr σ τ).basis (TopCat.of (charPairBundledSumStr τ σ).surf.M)
          (charPairBundledSumStr τ σ).basis (commEndHomeo σ τ)).toData))
      rw [mapCylRealizationTied_transportedBInc, hnat]
      erw [ker_mapCylBd_funLeft (commReindex σ τ)]
      exact hmeta.1
    hlag := by
      show JointLagrangian _ _ (LinearMap.ker (transportedBInc
        (mapCylRealizationTied (TopCat.of (charPairBundledSumStr σ τ).surf.M)
          (charPairBundledSumStr σ τ).basis (TopCat.of (charPairBundledSumStr τ σ).surf.M)
          (charPairBundledSumStr τ σ).basis (commEndHomeo σ τ)).toData))
      rw [mapCylRealizationTied_transportedBInc, hnat]
      erw [ker_mapCylBd_funLeft (commReindex σ τ)]
      exact hmeta.2
    ιW := ⟨Prod.map (charPairBundledSumStr σ τ).emb id,
      (charPairBundledSumStr σ τ).embSmooth.continuous.prodMap continuous_id⟩
    hιWce := by
      haveI := σ.t2; haveI := τ.t2
      haveI : T2Space (s.sum t).M := inferInstanceAs (T2Space (s.M ⊕ t.M))
      exact ((charPairBundledSumStr σ τ).embSmooth.continuous.prodMap
        continuous_id).isClosedEmbedding
        ((charPairBundledSumStr σ τ).embInj.prodMap Function.injective_id)
    glueσ := by
      rintro ⟨_, w, rfl⟩
      show Prod.map (charPairBundledSumStr σ τ).emb id
          (cylBdryIncl (TopCat.of (charPairBundledSumStr σ τ).surf.M) (Sum.inl w))
          = (mapCylinder (s := s.sum t) (t := t.sum s) (Diffeomorph.sumComm I s.M k t.M)
              (by funext z; rcases z with z | z <;> rfl)).e
              (Sum.inl ((charPairBundledSumStr σ τ).emb
                (IsClosedEmbedding.inl.isEmbedding.toHomeomorph.symm ⟨Sum.inl w, w, rfl⟩)))
      rw [IsEmbedding.toHomeomorph_symm_apply]
      rfl
    glueτ := by
      rintro ⟨(a | w), hp⟩
      · exact absurd ⟨a, rfl⟩ hp
      · rcases w with a | b
        · show Prod.map (charPairBundledSumStr σ τ).emb id
              (cylBdryIncl (TopCat.of (charPairBundledSumStr σ τ).surf.M) (Sum.inr (Sum.inl a)))
              = (mapCylinder (s := s.sum t) (t := t.sum s) (Diffeomorph.sumComm I s.M k t.M)
                  (by funext z; rcases z with z | z <;> rfl)).e
                  (Sum.inr ((charPairBundledSumStr τ σ).emb
                    ((((Homeomorph.setCongr Set.compl_range_inl).trans
                        IsClosedEmbedding.inr.isEmbedding.toHomeomorph.symm).trans
                        (commEndHomeo σ τ).symm) ⟨Sum.inr (Sum.inl a), hp⟩)))
          rw [Homeomorph.trans_apply, Homeomorph.trans_apply]
          erw [IsEmbedding.toHomeomorph_symm_apply]
          rfl
        · show Prod.map (charPairBundledSumStr σ τ).emb id
              (cylBdryIncl (TopCat.of (charPairBundledSumStr σ τ).surf.M) (Sum.inr (Sum.inr b)))
              = (mapCylinder (s := s.sum t) (t := t.sum s) (Diffeomorph.sumComm I s.M k t.M)
                  (by funext z; rcases z with z | z <;> rfl)).e
                  (Sum.inr ((charPairBundledSumStr τ σ).emb
                    ((((Homeomorph.setCongr Set.compl_range_inl).trans
                        IsClosedEmbedding.inr.isEmbedding.toHomeomorph.symm).trans
                        (commEndHomeo σ τ).symm) ⟨Sum.inr (Sum.inr b), hp⟩)))
          rw [Homeomorph.trans_apply, Homeomorph.trans_apply]
          erw [IsEmbedding.toHomeomorph_symm_apply]
          rfl
    chartQ := by
      show ChartedSpace MembraneModel
        (↑(TopCat.of (charPairBundledSumStr σ τ).surf.M) × ↑(TopCat.of unitInterval))
      infer_instance }

/-- **`assocBor` TETHERED** — the `(σ ⊔ τ) ⊔ ρ → σ ⊔ (τ ⊔ ρ)` associativity, twisted cylinder over
`Σ_{(σ⊔τ)⊔ρ}` embedded into `W = ((s.M ⊕ t.M) ⊕ u.M) × [0,1]` by `((σ⊔τ)⊔ρ).emb × id`; the τ-end is
retargeted through the surface reassociation, matching the mapping cylinder's `(sumAssoc).symm` slice. -/
noncomputable def assocBorTethered (prov : CharPairWProviderPerOp I k)
    (σ : CharPairStrBundled I s) (τ : CharPairStrBundled I t) (ρ : CharPairStrBundled I u) :
    CharPairBorRealizedTethered (mapCylinder (Diffeomorph.sumAssoc I s.M k t.M u.M)
      (by funext w; rcases w with (w | w) | w <;> rfl))
      (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ)
      (charPairBundledSumStr σ (charPairBundledSumStr τ ρ)) :=
  haveI := (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).surfT2
  haveI := (charPairBundledSumStr σ (charPairBundledSumStr τ ρ)).surfT2
  have hqS : (charPairSumStr (charPairSumStr σ.toCharPairStr τ.toCharPairStr) ρ.toCharPairStr).q
      = (Z4Quadratic.orthSum (Z4Quadratic.orthSum σ.q τ.q) ρ.q).reindex
          ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin ρ.n))).trans finSumFinEquiv) := by
    show (Z4Quadratic.orthSum ((Z4Quadratic.orthSum σ.q τ.q).reindex finSumFinEquiv) ρ.q).reindex
        finSumFinEquiv = _
    conv_lhs => rw [← reindex_refl ρ.q]
    rw [orthSum_reindex, reindex_trans]
  have hqT : (charPairSumStr σ.toCharPairStr (charPairSumStr τ.toCharPairStr ρ.toCharPairStr)).q
      = (Z4Quadratic.orthSum (Z4Quadratic.orthSum σ.q τ.q) ρ.q).reindex
          ((Equiv.sumAssoc (Fin σ.n) (Fin τ.n) (Fin ρ.n)).trans
            ((Equiv.sumCongr (Equiv.refl (Fin σ.n)) finSumFinEquiv).trans finSumFinEquiv)) := by
    show (Z4Quadratic.orthSum σ.q ((Z4Quadratic.orthSum τ.q ρ.q).reindex finSumFinEquiv)).reindex
        finSumFinEquiv = _
    conv_lhs => rw [← reindex_refl σ.q]
    rw [orthSum_reindex, reindex_trans, orthSum_assoc_eq, reindex_trans]
  have hmeta : IsMetabolic
      (jointEnhancement (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).q
        (charPairBundledSumStr σ (charPairBundledSumStr τ ρ)).q)
      (graphSub (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (assocReindex σ τ ρ).symm)) := by
    show IsMetabolic (Z4Quadratic.orthSum
      (charPairSumStr (charPairSumStr σ.toCharPairStr τ.toCharPairStr) ρ.toCharPairStr).q
      (Z4Quadratic.neg
        (charPairSumStr σ.toCharPairStr (charPairSumStr τ.toCharPairStr ρ.toCharPairStr)).q)) _
    rw [hqS, hqT]
    exact commonReindex_metabolic (Z4Quadratic.orthSum (Z4Quadratic.orthSum σ.q τ.q) ρ.q)
      ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin ρ.n))).trans finSumFinEquiv)
      ((Equiv.sumAssoc (Fin σ.n) (Fin τ.n) (Fin ρ.n)).trans
        ((Equiv.sumCongr (Equiv.refl (Fin σ.n)) finSumFinEquiv).trans finSumFinEquiv))
  have hnat : transportBasisChange
      (TopCat.of (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).surf.M)
      (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).basis
      (TopCat.of (charPairBundledSumStr σ (charPairBundledSumStr τ ρ)).surf.M)
      (charPairBundledSumStr σ (charPairBundledSumStr τ ρ)).basis (assocEndHomeo σ τ ρ)
        = LinearMap.funLeft (ZMod 2) (ZMod 2)
            ((assocReindex σ τ ρ) : Fin (σ.n + τ.n + ρ.n) → Fin (σ.n + (τ.n + ρ.n))) := by
    refine transportBasisChange_eq_funLeft _ _ _ _ _
      ((assocReindex σ τ ρ) : Fin (σ.n + τ.n + ρ.n) → Fin (σ.n + (τ.n + ρ.n))) ?_
    intro i
    show cohomologyPullback (⟨(Homeomorph.sumAssoc σ.surf.M τ.surf.M ρ.surf.M).symm,
        (Homeomorph.sumAssoc σ.surf.M τ.surf.M ρ.surf.M).symm.continuous⟩ :
        C(↑(sumSpace (TopCat.of σ.surf.M) (sumSpace (TopCat.of τ.surf.M) (TopCat.of ρ.surf.M))),
          ↑(sumSpace (sumSpace (TopCat.of σ.surf.M) (TopCat.of τ.surf.M)) (TopCat.of ρ.surf.M)))) 1
        ((sumBasis (sumBasis σ.basis τ.basis) ρ.basis).symm (Pi.single i 1))
      = (sumBasis σ.basis (sumBasis τ.basis ρ.basis)).symm
          (Pi.single ((assocReindex σ τ ρ) i) 1)
    erw [pullback_sumAssoc_sumBasis_symm]
    rfl
  have wadmP := prov.mapCyl (s := (s.sum t).sum u) (t := s.sum (t.sum u))
    (Diffeomorph.sumAssoc I s.M k t.M u.M) (by funext w; rcases w with (w | w) | w <;> rfl)
    (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ)
    (charPairBundledSumStr σ (charPairBundledSumStr τ ρ))
  { hWT2 := by
      haveI := σ.t2; haveI := τ.t2; haveI := ρ.t2
      exact inferInstanceAs (T2Space (((s.M ⊕ t.M) ⊕ u.M) × Set.Icc (0 : ℝ) 1))
    P14 := wadmP.wadm.P14
    P23 := wadmP.wadm.P23
    hwu := wadmP.wadm.hwu
    pin14 := wadmP.pin14
    pin23 := wadmP.pin23
    real := mapCylRealizationTied (TopCat.of (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).surf.M)
      (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).basis
      (TopCat.of (charPairBundledSumStr σ (charPairBundledSumStr τ ρ)).surf.M)
      (charPairBundledSumStr σ (charPairBundledSumStr τ ρ)).basis (assocEndHomeo σ τ ρ)
    htaylor := by
      show TaylorLegVanishes _ _ (LinearMap.ker (transportedBInc
        (mapCylRealizationTied
          (TopCat.of (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).surf.M)
          (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).basis
          (TopCat.of (charPairBundledSumStr σ (charPairBundledSumStr τ ρ)).surf.M)
          (charPairBundledSumStr σ (charPairBundledSumStr τ ρ)).basis (assocEndHomeo σ τ ρ)).toData))
      rw [mapCylRealizationTied_transportedBInc, hnat]
      erw [ker_mapCylBd_funLeft (assocReindex σ τ ρ)]
      exact hmeta.1
    hlag := by
      show JointLagrangian _ _ (LinearMap.ker (transportedBInc
        (mapCylRealizationTied
          (TopCat.of (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).surf.M)
          (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).basis
          (TopCat.of (charPairBundledSumStr σ (charPairBundledSumStr τ ρ)).surf.M)
          (charPairBundledSumStr σ (charPairBundledSumStr τ ρ)).basis (assocEndHomeo σ τ ρ)).toData))
      rw [mapCylRealizationTied_transportedBInc, hnat]
      erw [ker_mapCylBd_funLeft (assocReindex σ τ ρ)]
      exact hmeta.2
    ιW := ⟨Prod.map (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).emb id,
      (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).embSmooth.continuous.prodMap
        continuous_id⟩
    hιWce := by
      haveI := σ.t2; haveI := τ.t2; haveI := ρ.t2
      haveI : T2Space ((s.sum t).sum u).M := inferInstanceAs (T2Space ((s.M ⊕ t.M) ⊕ u.M))
      exact ((charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).embSmooth.continuous.prodMap
        continuous_id).isClosedEmbedding
        ((charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).embInj.prodMap
          Function.injective_id)
    glueσ := by
      rintro ⟨_, w, rfl⟩
      show Prod.map (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).emb id
          (cylBdryIncl (TopCat.of (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).surf.M)
            (Sum.inl w))
          = (mapCylinder (s := (s.sum t).sum u) (t := s.sum (t.sum u))
              (Diffeomorph.sumAssoc I s.M k t.M u.M)
              (by funext w; rcases w with (w | w) | w <;> rfl)).e
              (Sum.inl ((charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).emb
                (IsClosedEmbedding.inl.isEmbedding.toHomeomorph.symm ⟨Sum.inl w, w, rfl⟩)))
      rw [IsEmbedding.toHomeomorph_symm_apply]
      rfl
    glueτ := by
      rintro ⟨(a | w), hp⟩
      · exact absurd ⟨a, rfl⟩ hp
      · show Prod.map (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).emb id
            (cylBdryIncl (TopCat.of (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).surf.M)
              (Sum.inr w))
            = (mapCylinder (s := (s.sum t).sum u) (t := s.sum (t.sum u))
                (Diffeomorph.sumAssoc I s.M k t.M u.M)
                (by funext w; rcases w with (w | w) | w <;> rfl)).e
                (Sum.inr ((charPairBundledSumStr σ (charPairBundledSumStr τ ρ)).emb
                  ((((Homeomorph.setCongr Set.compl_range_inl).trans
                      IsClosedEmbedding.inr.isEmbedding.toHomeomorph.symm).trans
                      (assocEndHomeo σ τ ρ).symm) ⟨Sum.inr w, hp⟩)))
        rw [Homeomorph.trans_apply, Homeomorph.trans_apply]
        erw [IsEmbedding.toHomeomorph_symm_apply]
        rcases w with (a | b) | c <;> rfl
    chartQ := by
      show ChartedSpace MembraneModel
        (↑(TopCat.of (charPairBundledSumStr (charPairBundledSumStr σ τ) ρ).surf.M)
          × ↑(TopCat.of unitInterval))
      infer_instance }

/-! ### Pointwise block-homeomorphism reductions for the disjoint-union realization's boundary
identifications (`homσ`/`homτ` on each `Sum.inl`/`Sum.inr` block) — the `add` glue's workhorse. -/

section SumGlue
variable {nσ₁ nτ₁ nσ₂ nτ₂ : ℕ} {Sσ₁ Sτ₁ Sσ₂ Sτ₂ : TopCat}
  {bσ₁ : Cohomology Sσ₁ 1 ≃ₗ[ZMod 2] (Fin nσ₁ → ZMod 2)}
  {bτ₁ : Cohomology Sτ₁ 1 ≃ₗ[ZMod 2] (Fin nτ₁ → ZMod 2)}
  {bσ₂ : Cohomology Sσ₂ 1 ≃ₗ[ZMod 2] (Fin nσ₂ → ZMod 2)}
  {bτ₂ : Cohomology Sτ₂ 1 ≃ₗ[ZMod 2] (Fin nτ₂ → ZMod 2)}
  (d₁ : GeoRealizationTied Sσ₁ Sτ₁ bσ₁ bτ₁) (d₂ : GeoRealizationTied Sσ₂ Sτ₂ bσ₂ bτ₂)

theorem sum_homσ_inl_pt (v : ↑d₁.bdry) (hv₁ : v ∈ d₁.U)
    (hv : Sum.inl v ∈ (GeoRealizationTied.sum d₁ d₂).U) :
    (GeoRealizationTied.sum d₁ d₂).homσ ⟨Sum.inl v, hv⟩ = Sum.inl (d₁.homσ ⟨v, hv₁⟩) := by
  haveI := d₁.bdryCompact; haveI := d₂.bdryCompact; haveI := d₁.bdryT2; haveI := d₂.bdryT2
  show (d₁.homσ.sumCongr d₂.homσ)
      ((blockSubHomeo d₁.U d₂.U d₁.hU.1 d₂.hU.1).symm ⟨Sum.inl v, hv⟩) = _
  rw [show (blockSubHomeo d₁.U d₂.U d₁.hU.1 d₂.hU.1).symm ⟨Sum.inl v, hv⟩ = Sum.inl ⟨v, hv₁⟩ from
    (Homeomorph.symm_apply_eq _).mpr (Subtype.ext (blockSubHomeo_inl _ _ _ _ ⟨v, hv₁⟩).symm)]
  rfl

theorem sum_homσ_inr_pt (v : ↑d₂.bdry) (hv₂ : v ∈ d₂.U)
    (hv : Sum.inr v ∈ (GeoRealizationTied.sum d₁ d₂).U) :
    (GeoRealizationTied.sum d₁ d₂).homσ ⟨Sum.inr v, hv⟩ = Sum.inr (d₂.homσ ⟨v, hv₂⟩) := by
  haveI := d₁.bdryCompact; haveI := d₂.bdryCompact; haveI := d₁.bdryT2; haveI := d₂.bdryT2
  show (d₁.homσ.sumCongr d₂.homσ)
      ((blockSubHomeo d₁.U d₂.U d₁.hU.1 d₂.hU.1).symm ⟨Sum.inr v, hv⟩) = _
  rw [show (blockSubHomeo d₁.U d₂.U d₁.hU.1 d₂.hU.1).symm ⟨Sum.inr v, hv⟩ = Sum.inr ⟨v, hv₂⟩ from
    (Homeomorph.symm_apply_eq _).mpr (Subtype.ext (blockSubHomeo_inr _ _ _ _ ⟨v, hv₂⟩).symm)]
  rfl

theorem sum_homτ_inl_pt (v : ↑d₁.bdry) (hv₁ : v ∈ d₁.Uᶜ)
    (hv : Sum.inl v ∈ (GeoRealizationTied.sum d₁ d₂).Uᶜ) :
    (GeoRealizationTied.sum d₁ d₂).homτ ⟨Sum.inl v, hv⟩ = Sum.inl (d₁.homτ ⟨v, hv₁⟩) := by
  haveI := d₁.bdryCompact; haveI := d₂.bdryCompact; haveI := d₁.bdryT2; haveI := d₂.bdryT2
  show (d₁.homτ.sumCongr d₂.homτ)
      ((blockSubHomeo d₁.Uᶜ d₂.Uᶜ d₁.hU.compl.1 d₂.hU.compl.1).symm
        ((Homeomorph.setCongr (compl_block d₁.U d₂.U)) ⟨Sum.inl v, hv⟩)) = _
  rw [show (blockSubHomeo d₁.Uᶜ d₂.Uᶜ d₁.hU.compl.1 d₂.hU.compl.1).symm
        ((Homeomorph.setCongr (compl_block d₁.U d₂.U)) ⟨Sum.inl v, hv⟩) = Sum.inl ⟨v, hv₁⟩ from
    (Homeomorph.symm_apply_eq _).mpr (Subtype.ext (blockSubHomeo_inl _ _ _ _ ⟨v, hv₁⟩).symm)]
  rfl

theorem sum_homτ_inr_pt (v : ↑d₂.bdry) (hv₂ : v ∈ d₂.Uᶜ)
    (hv : Sum.inr v ∈ (GeoRealizationTied.sum d₁ d₂).Uᶜ) :
    (GeoRealizationTied.sum d₁ d₂).homτ ⟨Sum.inr v, hv⟩ = Sum.inr (d₂.homτ ⟨v, hv₂⟩) := by
  haveI := d₁.bdryCompact; haveI := d₂.bdryCompact; haveI := d₁.bdryT2; haveI := d₂.bdryT2
  show (d₁.homτ.sumCongr d₂.homτ)
      ((blockSubHomeo d₁.Uᶜ d₂.Uᶜ d₁.hU.compl.1 d₂.hU.compl.1).symm
        ((Homeomorph.setCongr (compl_block d₁.U d₂.U)) ⟨Sum.inr v, hv⟩)) = _
  rw [show (blockSubHomeo d₁.Uᶜ d₂.Uᶜ d₁.hU.compl.1 d₂.hU.compl.1).symm
        ((Homeomorph.setCongr (compl_block d₁.U d₂.U)) ⟨Sum.inr v, hv⟩) = Sum.inr ⟨v, hv₂⟩ from
    (Homeomorph.symm_apply_eq _).mpr (Subtype.ext (blockSubHomeo_inr _ _ _ _ ⟨v, hv₂⟩).symm)]
  rfl

end SumGlue

/-- **`addBor` TETHERED** — the genuine `⊔` of two tethered witnesses. The membrane is the honest
`Q₁ ⊔ Q₂` embedded into `W₁ ⊔ W₂ = (b₁.add b₂).W` by `Sum.map β₁.ιW β₂.ιW` (a sum of closed
embeddings); the block clopen split routes each block's glue through the corresponding component's
glue and `(b₁.add b₂).e`'s block structure. The admissibility is the per-op `addClosure` of the two
inputs' pins (F6-inhabitable, NOT the `∀ b`-provider). -/
noncomputable def addBorTethered (prov : CharPairWProviderPerOp I k)
    {s₁ t₁ s₂ t₂ : SingularManifold.{0} PUnit.{1} k I}
    {b₁ : Bordism (I.prod (𝓡∂ 1)) s₁ t₁} {b₂ : Bordism (I.prod (𝓡∂ 1)) s₂ t₂}
    {σ₁ : CharPairStrBundled I s₁} {τ₁ : CharPairStrBundled I t₁}
    {σ₂ : CharPairStrBundled I s₂} {τ₂ : CharPairStrBundled I t₂}
    (β₁ : CharPairBorRealizedTethered b₁ σ₁ τ₁) (β₂ : CharPairBorRealizedTethered b₂ σ₂ τ₂) :
    CharPairBorRealizedTethered (b₁.add b₂)
      (charPairBundledSumStr σ₁ σ₂) (charPairBundledSumStr τ₁ τ₂) :=
  haveI := (charPairBundledSumStr σ₁ σ₂).surfT2
  haveI := (charPairBundledSumStr τ₁ τ₂).surfT2
  have hblock : IsMetabolic
      (Z4Quadratic.orthSum (Z4Quadratic.orthSum σ₁.q (Z4Quadratic.neg τ₁.q))
        (Z4Quadratic.orthSum σ₂.q (Z4Quadratic.neg τ₂.q)))
      (blockSub (β₁.real.toMembrane σ₁.q τ₁.q).L (β₂.real.toMembrane σ₂.q τ₂.q).L) :=
    IsMetabolic.orthSum ⟨β₁.htaylor, β₁.hlag⟩ ⟨β₂.htaylor, β₂.hlag⟩
  have hregroup : Z4Quadratic.orthSum (Z4Quadratic.orthSum σ₁.q σ₂.q)
        (Z4Quadratic.neg (Z4Quadratic.orthSum τ₁.q τ₂.q))
      = (Z4Quadratic.orthSum (Z4Quadratic.orthSum σ₁.q (Z4Quadratic.neg τ₁.q))
          (Z4Quadratic.orthSum σ₂.q (Z4Quadratic.neg τ₂.q))).reindex
          (Equiv.sumSumSumComm (Fin σ₁.n) (Fin τ₁.n) (Fin σ₂.n) (Fin τ₂.n)) := by
    rw [neg_orthSum, orthSum_regroup]
  have hbase' := hblock.reindex (Equiv.sumSumSumComm (Fin σ₁.n) (Fin τ₁.n) (Fin σ₂.n) (Fin τ₂.n))
  have hbase : IsMetabolic (Z4Quadratic.orthSum (Z4Quadratic.orthSum σ₁.q σ₂.q)
        (Z4Quadratic.neg (Z4Quadratic.orthSum τ₁.q τ₂.q)))
      ((blockSub (β₁.real.toMembrane σ₁.q τ₁.q).L (β₂.real.toMembrane σ₂.q τ₂.q).L).comap
        (LinearMap.funLeft (ZMod 2) (ZMod 2)
          (Equiv.sumSumSumComm (Fin σ₁.n) (Fin τ₁.n) (Fin σ₂.n) (Fin τ₂.n)))) := by
    rw [hregroup]; exact hbase'
  have hform : jointEnhancement (charPairBundledSumStr σ₁ σ₂).q (charPairBundledSumStr τ₁ τ₂).q
      = (Z4Quadratic.orthSum (Z4Quadratic.orthSum σ₁.q σ₂.q)
          (Z4Quadratic.neg (Z4Quadratic.orthSum τ₁.q τ₂.q))).reindex
          (Equiv.sumCongr finSumFinEquiv finSumFinEquiv) :=
    jointEnhancement_reindex (orthSum σ₁.q σ₂.q) (orthSum τ₁.q τ₂.q) finSumFinEquiv finSumFinEquiv
  have hmeta : IsMetabolic
      (jointEnhancement (charPairBundledSumStr σ₁ σ₂).q (charPairBundledSumStr τ₁ τ₂).q)
      (((blockSub (β₁.real.toMembrane σ₁.q τ₁.q).L (β₂.real.toMembrane σ₂.q τ₂.q).L).comap
          (LinearMap.funLeft (ZMod 2) (ZMod 2)
            (Equiv.sumSumSumComm (Fin σ₁.n) (Fin τ₁.n) (Fin σ₂.n) (Fin τ₂.n)))).comap
        (LinearMap.funLeft (ZMod 2) (ZMod 2) (Equiv.sumCongr finSumFinEquiv finSumFinEquiv))) := by
    rw [hform]; exact hbase.reindex (Equiv.sumCongr finSumFinEquiv finSumFinEquiv)
  have wadmP := prov.addClosure (CharPairBorRealized.toWAdmPinned β₁.toCharPairBorRealized)
    (CharPairBorRealized.toWAdmPinned β₂.toCharPairBorRealized)
  { hWT2 := by
      haveI : T2Space b₁.W := β₁.hWT2; haveI : T2Space b₂.W := β₂.hWT2
      exact inferInstanceAs (T2Space (b₁.W ⊕ b₂.W))
    P14 := wadmP.wadm.P14
    P23 := wadmP.wadm.P23
    hwu := wadmP.wadm.hwu
    pin14 := wadmP.pin14
    pin23 := wadmP.pin23
    real := GeoRealizationTied.sum β₁.real β₂.real
    htaylor := by
      show TaylorLegVanishes _ _ (LinearMap.ker (transportedBInc
        (GeoRealizationTied.sum β₁.real β₂.real).toData))
      rw [sum_ker_transportedBInc]
      exact hmeta.1
    hlag := by
      show JointLagrangian _ _ (LinearMap.ker (transportedBInc
        (GeoRealizationTied.sum β₁.real β₂.real).toData))
      rw [sum_ker_transportedBInc]
      exact hmeta.2
    ιW := ⟨Sum.map β₁.ιW β₂.ιW, β₁.ιW.continuous.sumMap β₂.ιW.continuous⟩
    hιWce := by
      haveI := β₁.real.QCompact; haveI := β₂.real.QCompact
      haveI : T2Space b₁.W := β₁.hWT2; haveI : T2Space b₂.W := β₂.hWT2
      exact (β₁.ιW.continuous.sumMap β₂.ιW.continuous).isClosedEmbedding
        (β₁.hιWce.injective.sumMap β₂.hιWce.injective)
    glueσ := by
      rintro ⟨(v | v), hv⟩
      · have hv₁ : v ∈ β₁.real.U := by
          rcases hv with ⟨w, hw, hwv⟩ | ⟨w, _, hwv⟩
          · exact (Sum.inl_injective hwv) ▸ hw
          · exact absurd hwv (by simp)
        erw [sum_homσ_inl_pt β₁.real β₂.real v hv₁ hv]
        show Sum.inl (β₁.ιW (β₁.real.ι v))
            = Sum.inl (b₁.e (Sum.inl (σ₁.emb (β₁.real.homσ ⟨v, hv₁⟩))))
        exact congrArg Sum.inl (β₁.glueσ ⟨v, hv₁⟩)
      · have hv₂ : v ∈ β₂.real.U := by
          rcases hv with ⟨w, _, hwv⟩ | ⟨w, hw, hwv⟩
          · exact absurd hwv (by simp)
          · exact (Sum.inr_injective hwv) ▸ hw
        erw [sum_homσ_inr_pt β₁.real β₂.real v hv₂ hv]
        show Sum.inr (β₂.ιW (β₂.real.ι v))
            = Sum.inr (b₂.e (Sum.inl (σ₂.emb (β₂.real.homσ ⟨v, hv₂⟩))))
        exact congrArg Sum.inr (β₂.glueσ ⟨v, hv₂⟩)
    glueτ := by
      rintro ⟨(v | v), hv⟩
      · have hv₁ : v ∈ β₁.real.Uᶜ := fun hv1 => hv (Or.inl ⟨v, hv1, rfl⟩)
        erw [sum_homτ_inl_pt β₁.real β₂.real v hv₁ hv]
        show Sum.inl (β₁.ιW (β₁.real.ι v))
            = Sum.inl (b₁.e (Sum.inr (τ₁.emb (β₁.real.homτ ⟨v, hv₁⟩))))
        exact congrArg Sum.inl (β₁.glueτ ⟨v, hv₁⟩)
      · have hv₂ : v ∈ β₂.real.Uᶜ := fun hv2 => hv (Or.inr ⟨v, hv2, rfl⟩)
        erw [sum_homτ_inr_pt β₁.real β₂.real v hv₂ hv]
        show Sum.inr (β₂.ιW (β₂.real.ι v))
            = Sum.inr (b₂.e (Sum.inr (τ₂.emb (β₂.real.homτ ⟨v, hv₂⟩))))
        exact congrArg Sum.inr (β₂.glueτ ⟨v, hv₂⟩)
    chartQ := by
      haveI := β₁.chartQ; haveI := β₂.chartQ
      show ChartedSpace MembraneModel (↑β₁.real.Q ⊕ ↑β₂.real.Q)
      infer_instance }

/-! ## §5. The assembly helper `mkCharPairBorRealizedTethered` — the tether IS a required input.

This constructor makes the F4 fix mechanical: a tethered witness is assembled from a single
`WAdmPinned b` (per-op admissibility), the realization + its Taylor/Lagrangian data, AND the W-tether
`ιW`/glue + the chart. The tether cannot be omitted or synthesized from `real` — it is a formal
argument of THIS constructor, tied to THIS `b`. This is the type-level statement that the round-6
gate's F4 exploits (`transport`, `factors`) can no longer re-derive (§7). -/
noncomputable def mkCharPairBorRealizedTethered {s t : SingularManifold.{0} PUnit.{1} k I}
    {b : Bordism (I.prod (𝓡∂ 1)) s t} {σ : CharPairStrBundled I s} {τ : CharPairStrBundled I t}
    (wadmP : WAdmPinned b) (hWT2 : T2Space b.W)
    (real : GeoRealizationTied (TopCat.of σ.surf.M) (TopCat.of τ.surf.M) σ.basis τ.basis)
    (htaylor : TaylorLegVanishes σ.q τ.q (real.toMembrane σ.q τ.q).L)
    (hlag : JointLagrangian σ.q τ.q (real.toMembrane σ.q τ.q).L)
    (ιW : C(↑real.Q, b.W)) (hιWce : IsClosedEmbedding ιW)
    (glueσ : ∀ x : ↑(sub real.U),
      ιW (real.ι (subInclCM real.U x)) = b.e (Sum.inl (σ.emb (real.homσ x))))
    (glueτ : ∀ x : ↑(sub real.Uᶜ),
      ιW (real.ι (subInclCM real.Uᶜ x)) = b.e (Sum.inr (τ.emb (real.homτ x))))
    (chartQ : ChartedSpace MembraneModel ↑real.Q) :
    CharPairBorRealizedTethered b σ τ where
  hWT2 := hWT2
  P14 := wadmP.wadm.P14
  P23 := wadmP.wadm.P23
  hwu := wadmP.wadm.hwu
  pin14 := wadmP.pin14
  pin23 := wadmP.pin23
  real := real
  htaylor := htaylor
  hlag := hlag
  ιW := ιW
  hιWce := hιWce
  glueσ := glueσ
  glueτ := glueτ
  chartQ := chartQ

/-! ## §6. The Track-2 plug-in seam for the per-op provider.

The per-op provider's `cyl`/`doubling`/`mapCyl` fields are ALL `WAdmPinned` of **product cylinders**
`W = M × [0,1]` over a closed 4-manifold `M` (`reflCylinder s`, `doublingBordism s`, and every
`mapCylinder φ hf` share `W = s.M × Set.Icc 0 1`). Track 2's `CylinderWAdmPinned M`
(`PinPlusCylinderWAdmPinned`, engines `ofClosedPD`/`ofBasePD`) is EXACTLY the `WAdmPinned`-shaped
consolidation for that `W` — it derives `P14`/`P23`/`pin14`/`pin23` and the honest `hwu`. So a single
`CylinderWAdmPinned s.M` deliverable discharges `cyl`, `doubling`, AND `mapCyl` for that `s`.

**The one missing wire (a named Track-2 residual, NOT built here):** `CylinderWAdmPinned M` produces a
`LefschetzWuDatum (TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) …`, whereas the per-op
provider's fields need `LefschetzWuDatum (TopCat.of (reflCylinder s).W) ((I.prod (𝓡∂ 1)).boundary
(reflCylinder s).W) …`. These agree only through the **abstract-`I` ↔ concrete-`𝓡 4` bridge**
(`cylW M ≃ (reflCylinder s).W`, `cylModel 2 = I.prod (𝓡∂ 1)`) that `PinPlusCylinderWAdmPinned`'s
header explicitly declines to force ("does NOT depend on the abstract-`I` ↔ concrete-`𝓡 4` bridge").
The missing transport lemma is therefore a `WAdmPinned`-transport across that model/carrier
identification — `CylinderWAdmPinned M → WAdmPinned (reflCylinder s)` (and the `mapCylinder`/`doubling`
variants), plus a `sum`-closure `WAdmPinned b₁ → WAdmPinned b₂ → WAdmPinned (b₁.add b₂)` for
`addClosure`. The `add`-closure is the only field NOT a bare cylinder; it is a genuine disjoint-union
admissibility (`b₁.W ⊕ b₂.W`), for which the Lefschetz–Wu data assemble block-diagonally.

Once those transports land, `CharPairWProviderPerOp` is inhabited from Track-2 data alone — the F6
vacuity of the old `∀ b, WAdmPinned b` provider is gone (this finite family IS inhabitable). -/

/-! ## §7. F4-DEAD self-tests — why `transport` and the factorization cannot re-derive. -/

variable {b : Bordism (I.prod (𝓡∂ 1)) s t}
  {σ : CharPairStrBundled I s} {τ : CharPairStrBundled I t}

/-- **Forgetful**: a tethered witness IS a realized+pinned witness (the tether is a genuine
refinement, not a re-shape). -/
def CharPairBorRealizedTethered.toRealized (β : CharPairBorRealizedTethered b σ τ) :
    CharPairBorRealized b σ τ := β.toCharPairBorRealized

/-- **The geometric content the round-6 §5 banner claimed, now TRUE**: the realized membrane `Q`
closed-embeds into the bordism carrier `b.W`. So an e₈-kernel membrane on the doubling ends would have
to sit INSIDE the doubling bordism's `W = (ℝP⁴)⁴ × I` specifically — no longer a free abstract
compact-T2 space (`GeoRealizationTied.Q` bordism-blindness, F4). -/
theorem CharPairBorRealizedTethered.membrane_closedEmbeds_in_W
    (β : CharPairBorRealizedTethered b σ τ) : IsClosedEmbedding β.ιW := β.hιWce

/-- **The commuting glue is real, not vacuous**: on the σ-boundary component `Σ_σ`, the membrane's
image in `b.W` (through `ιW ∘ real.ι`) IS the σ-end's image through `b`'s boundary map `b.e ∘ Sum.inl`
composed with `σ.emb` and the identification `homσ`. This is the tie that makes `ιW`'s target
`b`-specific — the mechanism that kills `transport` (below). -/
theorem CharPairBorRealizedTethered.glue_σ (β : CharPairBorRealizedTethered b σ τ)
    (x : ↑(sub β.real.U)) :
    β.ιW (β.real.ι (subInclCM β.real.U x)) = b.e (Sum.inl (σ.emb (β.real.homσ x))) := β.glueσ x

/-
**Why `CharPairBorRealized.transport` (round-6 F4) CANNOT re-derive against this shape.**
The pre-tether `transport` moved a witness on `b` to ANY other bordism `b'` between the same ends via
`mkCharPairBorRealized prov b' hT2' β.real β.htaylor β.hlag` — every non-provider field was
`b`-independent. Against `CharPairBorRealizedTethered` this is a TYPE ERROR: the tether field
`ιW : C(↑real.Q, b.W)` has target `b.W`, and `mkCharPairBorRealizedTethered` (§5) REQUIRES it (together
with `glueσ`/`glueτ`, which mention `b.e`). To land a `CharPairBorRealizedTethered b' σ τ` one would
need `ιW' : C(↑real.Q, b'.W)` — but `β.ιW : C(↑real.Q, b.W)` gives NO map into `b'.W` (there is no
continuous `b.W → b'.W`), and `β.real`/`β.htaylor`/`β.hlag` (all `HasEndsRealization` supplies) carry
no `b'`-membrane. So there is no `b`-uniform `transport` — the membrane genuinely sits inside `b.W`.

**Why `isT2DataBordant_…_factors` (round-6 F4) CANNOT re-derive.**
The factorization's backward direction rebuilt a witness from `(∃ b, T2Space b.W) ∧ HasEndsRealization`
via `mkCharPairBorRealized prov b hT2 real ht hl`. Against the tethered shape,
`mkCharPairBorRealizedTethered` additionally consumes `ιW`/`glueσ`/`glueτ` — data NOT contained in
`HasEndsRealization σ τ` (which is only `∃ real, TaylorLegVanishes ∧ JointLagrangian`). An arbitrary
`b` with `T2Space b.W` plus an ends-realization does NOT supply a closed embedding of that particular
`real.Q` into that particular `b.W` compatible with `b.e`. So the structured relation no longer factors
as "some-T2-bordism ∧ ends-algebra" — the bordism and the tangential-membrane data are now coupled
through `ιW`/glue. (If either mechanism DID reproduce, the eight op realizations above would be the
witnesses — they are NOT `transport`s of a single ends-realization; each supplies its OWN geometric
`ιW` sitting inside its OWN `b.W`: `σ.emb × id ⊆ s.M × I`, `Sum.map β₁.ιW β₂.ιW ⊆ b₁.W ⊕ b₂.W`, etc.)
-/

end SKEFTHawking.PinPlusCharPairBorTethered
