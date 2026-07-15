/-
# Phase 5q.H W-D — THE SURGERY FOUNDATION (opener wave): the handle-attachment `Bordism`

The convergence finding (`PinPlusKTFreezeAssembly.lean`, `PinPlusKTSurgeryTrace.lean`,
`HandleTradeSurgery.lean`): the phase's two deepest remaining leaves —
`SpinSigmaPresentation.HandleTradeCobordism` (needs a raw `IsDataBordant ξ p ((S²×S²) ⊔ p')`) and
`PinPlusKTSurgeryTrace.AmbientSurgeryDatum` (needs a `Bordism … p'.1 p.1` with a tethered membrane) —
bottom out in the SAME missing foundation: **attach a handle to `M × I` along framed embedded data in
`M × {1}` and package the result as a project `Bordism`** (`BordismGroup.lean`). Every existing
nontrivial-`W` precedent (`reflCylinder`, `mapCylinder`, `doublingBordism`, `Bordism.add`) builds `W`
as a *product* `M × Icc` and reads its boundary off Mathlib's `boundary_product`. A surgery trace is
NOT a product — it is an **adjunction space** `(M × I) ∪_φ (handle)`. This module is the opener: the
reusable topological foundation for that adjunction space.

## What a handle-attachment `Bordism` is, formally
Given a compact Hausdorff *cylinder* `B` (the `M × I` end of the trace), a compact Hausdorff *handle*
`Ha`, a **closed** attaching region `S ⊆ Ha`, and a continuous **injective** attaching map
`φ : S → B` (the framed embedding of `Sʳ × D^{n−r}` into `M × {1}`), the surgery-trace carrier is the
**adjunction space** `W = B ⊔_φ Ha`: the quotient of `B ⊕ Ha` identifying `Sum.inl (φ a)` with
`Sum.inr a` for every `a ∈ S`. As a project `Bordism` this `W` needs (`Bordism`): a
`TopologicalSpace` (the quotient), `CompactSpace` (quotient of a compact `⊕`), a `ChartedSpace`/
`IsManifold` (the seam/handle charts — THE HARD PART, staged to the next wave), and the boundary
identification `e`. This module ships the **topological floor**: the carrier, its `CompactSpace` +
`T2Space` instances, and the boundary *set* identification, with the chart stack named as the next
wave. That is the mission's explicit WIN condition for the opener.

## §-map
* **§1 — the reusable Mathlib-grade T2 engine.** `t2Space_quotient_of_isClosed_rel`: a quotient of a
  compact Hausdorff space by a setoid whose relation is a *closed* subset of the product is Hausdorff
  (the classical compact-Hausdorff-quotient theorem; Mathlib has the ingredients, not the package).
* **§2 — the adjunction setoid.** For compact Hausdorff `B`/`Ha`, closed `S ⊆ Ha`, injective
  continuous `φ : S → B`, the explicit two-point-class equivalence on `B ⊕ Ha` and the proof its
  relation is closed.
* **§3 — the adjunction space `HandleAttachment.carrier`.** `W = Quotient` of the setoid; the two
  structure maps `fromCyl`/`fromHandle`, `CompactSpace`, `T2Space`, and the glue equation.
* **§4 — the boundary set, and the packaging targets stated for the next (chart) wave.**

Additive module. Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib

namespace SKEFTHawking.SurgeryFoundation

open Topology

/-! ## §1. The reusable Mathlib-grade T2 engine.

A quotient of a compact Hausdorff space by a setoid whose relation is a **closed** subset of the
product is again Hausdorff. This is the classical fact that a compact Hausdorff space modulo a closed
equivalence relation is compact Hausdorff; Mathlib ships the ingredients
(`isClosedMap_fst_of_compactSpace`, `NormalSpace.of_compactSpace_r1Space`) but not the package. The
whole surgery foundation's `T2Space` rests on this, so we prove it once, generically. -/

variable {X : Type*} [TopologicalSpace X]

/-- **The quotient map onto a setoid quotient is a closed map when the relation is closed** (on a
compact domain). For a closed `C`, the saturation `q⁻¹(q C) = {x | ∃ c ∈ C, x ≈ c}` is the image of
the closed set `{p | p.1 ≈ p.2} ∩ (X × C)` under `Prod.fst`, which is a closed map because the second
factor is compact (`isClosedMap_fst_of_compactSpace`); hence `q C` is closed. -/
theorem isClosedMap_quotient_mk_of_isClosed_rel [CompactSpace X] (s : Setoid X)
    (hrel : IsClosed {p : X × X | s p.1 p.2}) :
    IsClosedMap (Quotient.mk s) := by
  have hqm : IsQuotientMap (Quotient.mk s) := isQuotientMap_quotient_mk'
  intro C hC
  rw [← hqm.isClosed_preimage]
  have hsat : Quotient.mk s ⁻¹' (Quotient.mk s '' C)
      = Prod.fst '' ({p : X × X | s p.1 p.2} ∩ Prod.snd ⁻¹' C) := by
    ext x
    constructor
    · rintro ⟨c, hc, hqc⟩
      exact ⟨(x, c), ⟨Quotient.eq.mp hqc.symm, hc⟩, rfl⟩
    · rintro ⟨⟨a, c⟩, ⟨hac, hc⟩, rfl⟩
      exact ⟨c, hc, Quotient.eq.mpr (Setoid.symm hac)⟩
  rw [hsat]
  exact isClosedMap_fst_of_compactSpace _ (hrel.inter (hC.preimage continuous_snd))

/-- **The compact-Hausdorff-quotient theorem.** A quotient of a compact Hausdorff space by a setoid
whose relation `{p | p.1 ≈ p.2}` is closed in the product is Hausdorff. The T2 engine of the surgery
foundation. -/
theorem t2Space_quotient_of_isClosed_rel [CompactSpace X] [T2Space X] (s : Setoid X)
    (hrel : IsClosed {p : X × X | s p.1 p.2}) :
    T2Space (Quotient s) := by
  have hclosed : IsClosedMap (Quotient.mk s) :=
    isClosedMap_quotient_mk_of_isClosed_rel s hrel
  have hsurj : Function.Surjective (Quotient.mk s) := Quotient.mk_surjective
  refine ⟨fun a b hab => ?_⟩
  obtain ⟨x, rfl⟩ := hsurj a
  obtain ⟨y, rfl⟩ := hsurj b
  -- the two fibers are closed and disjoint
  have hAcl : IsClosed (Quotient.mk s ⁻¹' {Quotient.mk s x}) := by
    have : Quotient.mk s ⁻¹' {Quotient.mk s x} = (fun z => (z, x)) ⁻¹' {p : X × X | s p.1 p.2} := by
      ext z; simp [Quotient.eq]
    rw [this]; exact hrel.preimage (by fun_prop)
  have hBcl : IsClosed (Quotient.mk s ⁻¹' {Quotient.mk s y}) := by
    have : Quotient.mk s ⁻¹' {Quotient.mk s y} = (fun z => (z, y)) ⁻¹' {p : X × X | s p.1 p.2} := by
      ext z; simp [Quotient.eq]
    rw [this]; exact hrel.preimage (by fun_prop)
  have hdisj : Disjoint (Quotient.mk s ⁻¹' {Quotient.mk s x}) (Quotient.mk s ⁻¹' {Quotient.mk s y}) := by
    rw [Set.disjoint_left]
    intro z hzx hzy
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hzx hzy
    exact hab (hzx ▸ hzy)
  -- normality separates them by disjoint opens
  obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ := normal_separation hAcl hBcl hdisj
  -- saturate: q(Uᶜ), q(Vᶜ) are closed, so their complements are open, saturated, and separate
  refine ⟨(Quotient.mk s '' Uᶜ)ᶜ, (Quotient.mk s '' Vᶜ)ᶜ,
    (hclosed _ hU.isClosed_compl).isOpen_compl, (hclosed _ hV.isClosed_compl).isOpen_compl, ?_, ?_, ?_⟩
  · -- Quotient.mk s x ∈ (q '' Uᶜ)ᶜ
    rintro ⟨z, hzU, hzx⟩
    exact hzU (hAU (by simp only [Set.mem_preimage, Set.mem_singleton_iff]; exact hzx))
  · rintro ⟨z, hzV, hzy⟩
    exact hzV (hBV (by simp only [Set.mem_preimage, Set.mem_singleton_iff]; exact hzy))
  · rw [Set.disjoint_left]
    intro w hwU hwV
    obtain ⟨z, rfl⟩ := hsurj w
    have hzU : z ∈ U := by
      by_contra hz; exact hwU ⟨z, hz, rfl⟩
    have hzV : z ∈ V := by
      by_contra hz; exact hwV ⟨z, hz, rfl⟩
    exact (Set.disjoint_left.mp hUV) hzU hzV

/-! ## §2. The adjunction setoid on `B ⊕ Ha`.

For a compact Hausdorff cylinder `B`, a compact Hausdorff handle `Ha`, a closed attaching region
`S ⊆ Ha`, and a continuous **injective** attaching map `φ : S → B`, the surgery trace identifies
`Sum.inl (φ a)` with `Sum.inr a` for every `a ∈ S`. Because `φ` is injective the resulting
equivalence classes have at most two elements, so the relation can be written *explicitly* (no
`EqvGen` closure): `adjRel`. Injectivity is exactly what makes it transitive; closedness of the
region + compactness make its graph a closed subset of the product (via §1's T2 engine). -/

section Adjunction

variable {B : Type*} {Ha : Type*} {S : Set Ha} {φ : ↥S → B}

/-- **The explicit adjunction relation** on `B ⊕ Ha`: identify `Sum.inl (φ a)` with `Sum.inr a` for
`a ∈ S`, and nothing else. With `φ` injective this is already an equivalence (classes have ≤ 2
elements) — no `EqvGen` closure needed. -/
def adjRel (φ : ↥S → B) : (B ⊕ Ha) → (B ⊕ Ha) → Prop
  | Sum.inl b, Sum.inl b' => b = b'
  | Sum.inr a, Sum.inr a' => a = a'
  | Sum.inl b, Sum.inr a => ∃ h : a ∈ S, φ ⟨a, h⟩ = b
  | Sum.inr a, Sum.inl b => ∃ h : a ∈ S, φ ⟨a, h⟩ = b

@[refl] theorem adjRel_refl (x : B ⊕ Ha) : adjRel φ x x := by cases x <;> rfl

theorem adjRel_symm {x y : B ⊕ Ha} (h : adjRel φ x y) : adjRel φ y x := by
  cases x <;> cases y <;> first | exact h.symm | exact h

theorem adjRel_trans (hφinj : Function.Injective φ) {x y z : B ⊕ Ha}
    (hxy : adjRel φ x y) (hyz : adjRel φ y z) : adjRel φ x z := by
  cases x <;> cases y <;> cases z <;> simp only [adjRel] at hxy hyz ⊢
  case inl.inl.inl => exact hxy.trans hyz
  case inl.inl.inr => obtain ⟨h, e⟩ := hyz; exact ⟨h, e.trans hxy.symm⟩
  case inl.inr.inl => obtain ⟨_, e1⟩ := hxy; obtain ⟨_, e2⟩ := hyz; exact e1.symm.trans e2
  case inl.inr.inr => obtain ⟨h, e⟩ := hxy; subst hyz; exact ⟨h, e⟩
  case inr.inl.inl => obtain ⟨h, e⟩ := hxy; exact ⟨h, e.trans hyz⟩
  case inr.inl.inr =>
    obtain ⟨_, e1⟩ := hxy; obtain ⟨_, e2⟩ := hyz
    exact congrArg Subtype.val (hφinj (e1.trans e2.symm))
  case inr.inr.inl => subst hxy; exact hyz
  case inr.inr.inr => exact hxy.trans hyz

/-- The adjunction setoid: `adjRel` as an `Equivalence` (transitivity uses injectivity of `φ`). -/
def adjSetoid (hφinj : Function.Injective φ) : Setoid (B ⊕ Ha) where
  r := adjRel φ
  iseqv := ⟨adjRel_refl, adjRel_symm, adjRel_trans hφinj⟩

variable [TopologicalSpace B] [TopologicalSpace Ha]

/-- **The adjunction relation's graph is closed** in `(B ⊕ Ha) × (B ⊕ Ha)`. Decomposed as a union of
four closed pieces, each the *range* of a continuous map out of a compact space (`B`, `Ha`, and twice
the compact `↥S` — closed in the compact `Ha`) into the Hausdorff `(B ⊕ Ha) × (B ⊕ Ha)`: the two
diagonals and the two copies of the attaching graph `{(φ a, a) | a ∈ S}`. -/
theorem isClosed_adjRel [CompactSpace B] [CompactSpace Ha] [T2Space B] [T2Space Ha]
    (hS : IsClosed S) (hφ : Continuous φ) :
    IsClosed {p : (B ⊕ Ha) × (B ⊕ Ha) | adjRel φ p.1 p.2} := by
  haveI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS.isCompact
  have hset : {p : (B ⊕ Ha) × (B ⊕ Ha) | adjRel φ p.1 p.2} =
      Set.range (fun b : B => ((Sum.inl b, Sum.inl b) : (B ⊕ Ha) × (B ⊕ Ha))) ∪
      Set.range (fun a : Ha => ((Sum.inr a, Sum.inr a) : (B ⊕ Ha) × (B ⊕ Ha))) ∪
      Set.range (fun a : ↥S => ((Sum.inl (φ a), Sum.inr (a : Ha)) : (B ⊕ Ha) × (B ⊕ Ha))) ∪
      Set.range (fun a : ↥S => ((Sum.inr (a : Ha), Sum.inl (φ a)) : (B ⊕ Ha) × (B ⊕ Ha))) := by
    ext ⟨u, v⟩
    cases u <;> cases v <;>
      simp only [adjRel, Set.mem_setOf_eq, Set.mem_union, Set.mem_range, Prod.mk.injEq,
        Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and, and_false] <;>
      aesop
  rw [hset]
  exact ((((isCompact_range (by fun_prop)).isClosed).union
    ((isCompact_range (by fun_prop)).isClosed)).union
    ((isCompact_range (by fun_prop)).isClosed)).union
    ((isCompact_range (by fun_prop)).isClosed)

end Adjunction

/-! ## §3. The adjunction space `HandleAttachment.carrier` — the surgery-trace carrier.

`HandleAttachment` bundles the framed-embedding datum (the mission's "parameterize the embedding +
framing as a structure field", NOT constructing a specific embedding): the compact Hausdorff cylinder
`B` (`= M × I`), the compact Hausdorff handle `Ha` (`= Dʳ⁺¹ × D^{n−r}`), the closed attaching region
`S ⊆ Ha` (`= Sʳ × D^{n−r}`), and the injective continuous attaching map `φ : S → B`. Its `carrier` is
the adjunction space `B ⊔_φ Ha`, and this section ships its full topological instance stack — the
opener's WIN condition. -/

/-- **A handle-attachment datum** — the framed-embedding parameters of a surgery trace, bundled. The
cylinder `B` (`= M × I`) and handle `Ha` (`= Dʳ⁺¹ × D^{n−r}`) are compact Hausdorff; `S ⊆ Ha` is the
closed attaching region (`= Sʳ × D^{n−r}`); `φ : S → B` is the injective continuous attaching map (the
framed embedding of the attaching region into `M × {1} ⊆ B`). No specific embedding is constructed —
this names the geometric input a future wave supplies. -/
structure HandleAttachment.{u, v} where
  /-- the cylinder end `M × I` of the trace. -/
  B : Type u
  [topB : TopologicalSpace B]
  [compactB : CompactSpace B]
  [t2B : T2Space B]
  /-- the handle `Dʳ⁺¹ × D^{n−r}`. -/
  Ha : Type v
  [topHa : TopologicalSpace Ha]
  [compactHa : CompactSpace Ha]
  [t2Ha : T2Space Ha]
  /-- the closed attaching region `Sʳ × D^{n−r} ⊆ Ha`. -/
  S : Set Ha
  /-- the attaching region is closed. -/
  hS : IsClosed S
  /-- the framed-embedding attaching map. -/
  φ : ↥S → B
  /-- the attaching map is continuous. -/
  hφ : Continuous φ
  /-- the attaching map is injective (a genuine embedding). -/
  hφinj : Function.Injective φ

namespace HandleAttachment

attribute [instance] topB compactB t2B topHa compactHa t2Ha

variable (HA : HandleAttachment)

/-- **The surgery-trace carrier** `W = B ⊔_φ Ha`: the adjunction space, the quotient of `B ⊕ Ha` by
the attaching identifications. -/
def carrier : Type _ := Quotient (adjSetoid HA.hφinj)

instance : TopologicalSpace HA.carrier :=
  inferInstanceAs (TopologicalSpace (Quotient (adjSetoid HA.hφinj)))

/-- **The carrier is compact** — a quotient of the compact `B ⊕ Ha`. -/
instance : CompactSpace HA.carrier :=
  inferInstanceAs (CompactSpace (Quotient (adjSetoid HA.hφinj)))

/-- **The carrier is Hausdorff** — the adjunction relation's graph is closed (§2), so §1's compact-
Hausdorff-quotient engine applies. This is the opener's key instance: the surgery-trace carrier is a
genuine compact Hausdorff space. -/
instance : T2Space HA.carrier :=
  t2Space_quotient_of_isClosed_rel (adjSetoid HA.hφinj) (isClosed_adjRel HA.hS HA.hφ)

/-- The inclusion of the cylinder end `B` into the carrier. -/
def fromCyl : HA.B → HA.carrier := fun b => Quotient.mk _ (Sum.inl b)

/-- The inclusion of the handle `Ha` into the carrier. -/
def fromHandle : HA.Ha → HA.carrier := fun a => Quotient.mk _ (Sum.inr a)

theorem continuous_fromCyl : Continuous HA.fromCyl :=
  continuous_quotient_mk'.comp continuous_inl

theorem continuous_fromHandle : Continuous HA.fromHandle :=
  continuous_quotient_mk'.comp continuous_inr

/-- **The glue equation**: on the attaching region the cylinder-inclusion of `φ a` and the handle-
inclusion of `a` agree in the carrier — this is exactly the surgery identification `Sum.inl (φ a) ∼
Sum.inr a`. -/
theorem glue (a : ↥HA.S) : HA.fromCyl (HA.φ a) = HA.fromHandle (a : HA.Ha) :=
  Quotient.sound ⟨a.2, rfl⟩

/-- **The carrier is covered by the two inclusions** — every point is a cylinder point or a handle
point. (The two ranges cover; their overlap is the glued attaching region.) -/
theorem range_fromCyl_union_range_fromHandle :
    Set.range HA.fromCyl ∪ Set.range HA.fromHandle = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro w
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective w
  cases x with
  | inl b => exact Or.inl ⟨b, rfl⟩
  | inr a => exact Or.inr ⟨a, rfl⟩

/-! ### §4. How the two ends sit inside `W` — the boundary-set floor.

The two inclusions are **closed embeddings** (each factor is compact and `W` is Hausdorff), so `B` and
`Ha` sit inside `W` as genuine closed subspaces, and their images overlap exactly on the glued
attaching region. This is the topological floor of the boundary identification `e` a project `Bordism`
requires: the source-manifold end and the surgered-manifold end are carved out by these two closed
embeddings, with the seam their overlap. The manifold (chart) structure on each end — turning the
boundary *set* into a `∂W ≅ M ⊔ M'` identification with `ModelWithCorners.boundary` — is the named
next wave. -/

theorem fromCyl_injective : Function.Injective HA.fromCyl :=
  fun _ _ h => Quotient.eq.mp h

theorem fromHandle_injective : Function.Injective HA.fromHandle :=
  fun _ _ h => Quotient.eq.mp h

/-- **The cylinder end is a closed embedding** — `B` (`= M × I`) sits inside `W` as a closed subspace
(`B` compact, `W` Hausdorff, `fromCyl` injective). The source-manifold boundary component lives here. -/
theorem isClosedEmbedding_fromCyl : IsClosedEmbedding HA.fromCyl :=
  HA.continuous_fromCyl.isClosedEmbedding HA.fromCyl_injective

/-- **The handle end is a closed embedding** — `Ha` (`= Dʳ⁺¹ × D^{n−r}`) sits inside `W` as a closed
subspace. The surgered-manifold boundary component is carved from this end. -/
theorem isClosedEmbedding_fromHandle : IsClosedEmbedding HA.fromHandle :=
  HA.continuous_fromHandle.isClosedEmbedding HA.fromHandle_injective

/-- **The two ends overlap exactly on the glued attaching region**: a carrier point is in both the
cylinder end and the handle end iff it is the image of an attaching-region point `a ∈ S`, glued from
its two sides `Sum.inl (φ a) ∼ Sum.inr a`. This is the seam of the surgery trace. -/
theorem range_fromCyl_inter_range_fromHandle :
    Set.range HA.fromCyl ∩ Set.range HA.fromHandle
      = Set.range (fun a : ↥HA.S => HA.fromHandle (a : HA.Ha)) := by
  ext w
  constructor
  · rintro ⟨⟨b, rfl⟩, ⟨a, ha⟩⟩
    -- ⟦inr a⟧ = ⟦inl b⟧, so adjRel gives a ∈ S with φ⟨a⟩ = b
    obtain ⟨h, _⟩ := Quotient.eq.mp ha.symm
    exact ⟨⟨a, h⟩, ha⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨HA.φ a, HA.glue a⟩, ⟨(a : HA.Ha), rfl⟩⟩

/-- **The un-attached cylinder points are disjoint from the handle end.** A cylinder point outside the
attaching image `range φ` is never a handle point. The source-manifold boundary component `M × {0}`
lives among these un-attached points, so it is cleanly separated in `W` from the surgered end carved
from the handle. -/
theorem fromCyl_image_compl_disjoint_range_fromHandle :
    Disjoint (HA.fromCyl '' (Set.range HA.φ)ᶜ) (Set.range HA.fromHandle) := by
  rw [Set.disjoint_left]
  rintro w ⟨b, hb, rfl⟩ ⟨a, ha⟩
  obtain ⟨h, hφb⟩ := Quotient.eq.mp ha
  exact hb ⟨⟨a, h⟩, hφb⟩

/-- **The interior handle points are disjoint from the cylinder end.** A handle point outside the
attaching region `S` is never a cylinder point — the surgered manifold's new `Dʳ⁺¹ × Sⁿ⁻ʳ⁻¹` cap is
carved from exactly these interior handle points. -/
theorem fromHandle_image_compl_disjoint_range_fromCyl :
    Disjoint (HA.fromHandle '' HA.Sᶜ) (Set.range HA.fromCyl) := by
  rw [Set.disjoint_left]
  rintro w ⟨a, ha, rfl⟩ ⟨b, hb⟩
  obtain ⟨h, _⟩ := Quotient.eq.mp hb
  exact ha h

end HandleAttachment

/-! ## §5. The packaging targets — what the next (chart) wave needs.

The opener delivers the **topological floor** of the surgery-trace `Bordism`: the carrier `W`
(`HandleAttachment.carrier`), its `TopologicalSpace`/`CompactSpace`/`T2Space` instances (§3), and the
boundary-set floor — the two closed-embedded ends and their seam (§4). To package a project
`Bordism` (`SKEFTHawking.BordismTheory.Bordism`) the remaining fields are exactly the **chart stack**:

* `ChartedSpace H' W` — the atlas over the collar model, built from the cylinder's interior charts
  (cf. `PinPlusCylinderInteriorChart`), the handle's disk charts (cf. `DiskManifold`/`SphereDiskJ5`),
  and the seam/collar transition charts across the glued attaching region (THE HARD PART);
* `IsManifold J k W` — smoothness of those transitions;
* the boundary map `e : sourceEnd.M ⊕ surgeredEnd.M → W` and `he_boundary : Set.range e = J.boundary W`
  — the surgered manifold `M'` (`= (M ∖ Sʳ × D̊^{n−r}) ∪ Dʳ⁺¹ × S^{n−r−1}`) as a `SingularManifold`
  carved from the handle end, and the identification of `∂W` as the two ends.

With that stack, the two convergence consumers are met directly:

* `SpinSigmaPresentation.HandleTradeCobordism` — the raw `IsDataBordant ξ p ((S²×S²) ⊔ p')`: take
  `Ha` the `S²×S²`-handle, `φ` the attaching-circle standardization, `carrier` the trace `W`, and read
  `[p] = [S²×S²] + [p']` off `mk_eq_of_bordant` (`HandleTradeSurgery.handleTradeSplit_of_cobordism`);
* `PinPlusKTSurgeryTrace.AmbientSurgeryDatum` — the `Bordism ((𝓡 4).prod (𝓡∂ 1)) p'.1 p.1` with a
  tethered membrane: take `Ha` the `D² × D³` 2-handle, `φ` the framed circle, and the tether/`T2` from
  `carrier`'s `T2Space` instance (§3, `HandleAttachment.instT2SpaceCarrier`).

Both are the SAME `HandleAttachment` shape at different `(r, Ha, φ)`. The topological floor here is
shared by both; only the chart stack and the `SingularManifold`/tangential-structure wiring differ. -/

end SKEFTHawking.SurgeryFoundation
