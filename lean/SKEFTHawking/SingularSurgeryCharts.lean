/-
# Phase 5q.H W-D — THE SURGERY FOUNDATION, WAVE 2: the chart stack + the surgered boundary

Wave-2 companion to `SingularSurgeryFoundation.lean` (namespace `SKEFTHawking.SurgeryFoundation`).
The opener shipped the adjunction-space carrier `W = B ⊔_φ Ha` with its
`TopologicalSpace`/`CompactSpace`/`T2Space` stack and the boundary-set floor (the two closed-embedded
ends + their seam). Its §5 named the remaining `Bordism` fields — the **chart stack**
(`ChartedSpace H' W` + `IsManifold J k W`) and the **boundary map** — as this wave's targets. This
module delivers the honestly-achievable floor of that stack and stages the genuinely-geometric
residual (the seam collar-smoothing) as a precise interface.

## §-map
* **§1 — the reusable keystone: assemble a `ChartedSpace` from an open cover.** `ChartedSpace H' W`
  needs, per point, ONE chart (an `OpenPartialHomeomorph W H'` whose open source contains it) — the
  transition compatibility is `IsManifold`'s job, not the `ChartedSpace`'s. So a global chart atlas
  is exactly an open cover each of whose members is charted. Mathlib has the *restriction* direction
  (`Opens.instChartedSpace`) but not this *assembly* direction; we prove it once, generically. THE
  mechanism the three-region surgery atlas (cylinder-interior ⊔ handle-interior ⊔ seam) is built by.
* **§2 — the interior-region open-embedding topology.** The two un-glued ends sit inside `W` as
  genuine OPEN subspaces: `fromCyl` restricted off the closed attaching image, and `fromHandle`
  restricted off the closed attaching region, are open embeddings; together with the seam `q(S)` they
  cover `W`. Regions (a)+(b) of §5's atlas plan, at the topological granularity the abstract carrier
  permits (the opener carries no chart data on `B`/`Ha` — that is the manifold-carrying datum below).

Additive module. Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularSurgeryFoundation

namespace SKEFTHawking.SurgeryFoundation

open Topology TopologicalSpace

/-- **A homeomorphism transports a `ChartedSpace` structure** (single global chart). Mirrors
`PinPlusCylinderWAdmPinned.chartedSpaceOfHomeomorph` / `SphereDiskJ5.chartedSpaceHB_HA`; inlined here
to avoid a heavy cross-module import. No `IsManifold`/groupoid compatibility for plain `ChartedSpace`. -/
@[reducible] def chartedSpaceOfHomeo {X H : Type*} [TopologicalSpace X] [TopologicalSpace H]
    (e : X ≃ₜ H) : ChartedSpace H X where
  atlas := {e.toOpenPartialHomeomorph}
  chartAt _ := e.toOpenPartialHomeomorph
  mem_chart_source _ := by simp [Homeomorph.toOpenPartialHomeomorph]
  chart_mem_atlas _ := rfl

/-! ## §1. The reusable keystone — assemble a `ChartedSpace` from an open cover.

A `ChartedSpace H' W` requires, for each `w : W`, a single chart: an `OpenPartialHomeomorph W H'`
whose (open) source contains `w`. There is **no** inter-chart compatibility condition at the
`ChartedSpace` level — that is exactly what `IsManifold`/`HasGroupoid` layers on top. So to endow `W`
with a chart atlas it suffices to cover it by open sets, each of which is itself a `ChartedSpace H'`:
transport each sub-atlas's chart-at-a-point through the open inclusion. Mathlib ships the reverse
(`TopologicalSpace.Opens.instChartedSpace` restricts a global atlas to an open subset) but not this
gluing direction; it is the mechanism the surgery-trace atlas (three regions covering `W`) is
assembled by. -/

/-- **Assemble a `ChartedSpace` from an open cover of charted open subsets.** If `W` is covered by
open sets `U i` (as `Opens W`), each carrying a `ChartedSpace H'` structure on its subtype, then `W`
itself is a `ChartedSpace H'`. The chart at `w` is the subtype chart at `w` in some covering `U i ∋ w`,
transported to `W` through the open inclusion `↥(U i) ↪ W`. No compatibility between the regions is
needed — that is `IsManifold`'s layer. -/
@[reducible] noncomputable def chartedSpaceOfOpensCover
    {H' W : Type*} [TopologicalSpace H'] [TopologicalSpace W]
    {ι : Type*} (U : ι → Opens W)
    (hcover : ∀ w : W, ∃ i, w ∈ U i)
    (cs : ∀ i, ChartedSpace H' (U i)) :
    ChartedSpace H' W := by
  classical
  choose idx hidx using hcover
  let chart : W → OpenPartialHomeomorph W H' := fun w =>
    letI := cs (idx w)
    haveI : Nonempty ↥(U (idx w)) := ⟨⟨w, hidx w⟩⟩
    ((U (idx w)).openPartialHomeomorphSubtypeCoe ⟨⟨w, hidx w⟩⟩).symm.trans
      (chartAt H' (⟨w, hidx w⟩ : ↥(U (idx w))))
  refine ChartedSpace.mk (Set.range chart) chart ?_ (fun w => ⟨w, rfl⟩)
  intro w
  letI := cs (idx w)
  haveI hne : Nonempty ↥(U (idx w)) := ⟨⟨w, hidx w⟩⟩
  show w ∈ (((U (idx w)).openPartialHomeomorphSubtypeCoe hne).symm.trans
      (chartAt H' (⟨w, hidx w⟩ : ↥(U (idx w))))).source
  rw [OpenPartialHomeomorph.trans_source]
  constructor
  · rw [OpenPartialHomeomorph.symm_source, Opens.openPartialHomeomorphSubtypeCoe_target]
    exact hidx w
  · rw [Set.mem_preimage]
    have hval : ((U (idx w)).openPartialHomeomorphSubtypeCoe hne) (⟨w, hidx w⟩ : ↥(U (idx w))) = w := by
      rw [Opens.openPartialHomeomorphSubtypeCoe_coe]
    have hmem : (⟨w, hidx w⟩ : ↥(U (idx w))) ∈
        ((U (idx w)).openPartialHomeomorphSubtypeCoe hne).source := by
      rw [Opens.openPartialHomeomorphSubtypeCoe_source]; trivial
    have hsymm : ((U (idx w)).openPartialHomeomorphSubtypeCoe hne).symm w
        = (⟨w, hidx w⟩ : ↥(U (idx w))) := by
      have h := OpenPartialHomeomorph.left_inv _ hmem
      rwa [hval] at h
    rw [hsymm]
    exact mem_chart_source H' (⟨w, hidx w⟩ : ↥(U (idx w)))

/-! ## §2. The interior-region open-embedding topology.

The two un-glued ends sit inside `W` as genuine OPEN subspaces. The opener (§4) showed they sit as
CLOSED embeddings and computed their overlap (the seam) and their disjointness from the opposite end;
here we upgrade the *interiors* — the cylinder off its attaching image, and the handle off its
attaching region — to OPEN subspaces. The key: each interior's preimage under the quotient map is a
*saturated* open set (a point outside the attaching data has a singleton equivalence class), so its
quotient image is open. These are regions (a) and (b) of §5's atlas plan; together with the seam
`q(S)` they cover `W`. -/

namespace HandleAttachment

variable (HA : HandleAttachment)

/-- **The cylinder-interior region** — the un-attached cylinder points `fromCyl(B ∖ range φ)`. The
source-manifold boundary `M × {0}` lives here; charted from `B`'s charts (a future manifold-carrying
datum), away from the seam. -/
def cylInteriorRegion : Set HA.carrier := HA.fromCyl '' (Set.range HA.φ)ᶜ

/-- **The handle-interior region** — the interior handle points `fromHandle(Ha ∖ S)`. The surgered
manifold's new `Dʳ⁺¹ × Sⁿ⁻ʳ⁻¹` cap is carved from exactly these points. -/
def handleInteriorRegion : Set HA.carrier := HA.fromHandle '' HA.Sᶜ

/-- The attaching image `range φ` is **closed** in the cylinder `B` (a compact-to-Hausdorff continuous
injection is a closed embedding), so its complement is open — the cylinder interior's domain. -/
theorem isClosed_range_φ : IsClosed (Set.range HA.φ) := by
  haveI : CompactSpace ↥HA.S := isCompact_iff_compactSpace.mp HA.hS.isCompact
  exact (isCompact_range HA.hφ).isClosed

/-- **The quotient preimage of the cylinder-interior region is its saturated open lift** `inl(B ∖ range φ)`.
A cylinder point off `range φ` has a singleton class, so no handle point maps into the region. -/
theorem preimage_cylInteriorRegion :
    Quotient.mk (adjSetoid HA.hφinj) ⁻¹' HA.cylInteriorRegion
      = Sum.inl '' (Set.range HA.φ)ᶜ := by
  ext x
  constructor
  · rintro ⟨b, hb, hqb⟩
    -- hqb : HA.fromCyl b = ⟦x⟧, b ∉ range φ
    cases x with
    | inl b' =>
      have hbb : b = b' := Quotient.eq.mp hqb
      exact ⟨b', hbb ▸ hb, rfl⟩
    | inr a' =>
      obtain ⟨h, hφa⟩ := Quotient.eq.mp hqb
      exact absurd ⟨⟨a', h⟩, hφa⟩ hb
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, rfl⟩

/-- **The cylinder-interior region is OPEN** in the carrier — its saturated lift `inl(B ∖ range φ)` is
open (`Sum.inl` an open embedding, `range φ` closed), and the quotient map is a quotient map. -/
theorem isOpen_cylInteriorRegion : IsOpen HA.cylInteriorRegion := by
  have hq : IsQuotientMap (Quotient.mk (adjSetoid HA.hφinj)) := isQuotientMap_quotient_mk'
  refine hq.isOpen_preimage.mp ?_
  rw [preimage_cylInteriorRegion]
  exact isOpenMap_inl _ HA.isClosed_range_φ.isOpen_compl

/-- **The quotient preimage of the handle-interior region is its saturated open lift** `inr(Ha ∖ S)`.
An interior handle point has a singleton class, so no cylinder point maps into the region. -/
theorem preimage_handleInteriorRegion :
    Quotient.mk (adjSetoid HA.hφinj) ⁻¹' HA.handleInteriorRegion
      = Sum.inr '' HA.Sᶜ := by
  ext x
  constructor
  · rintro ⟨a, ha, hqa⟩
    cases x with
    | inr a' =>
      have haa : a = a' := Quotient.eq.mp hqa
      exact ⟨a', haa ▸ ha, rfl⟩
    | inl b' =>
      obtain ⟨h, _⟩ := Quotient.eq.mp hqa
      exact absurd h ha
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

/-- **The handle-interior region is OPEN** in the carrier — its saturated lift `inr(Ha ∖ S)` is open
(`Sum.inr` an open embedding, `S` closed), and the quotient map is a quotient map. -/
theorem isOpen_handleInteriorRegion : IsOpen HA.handleInteriorRegion := by
  have hq : IsQuotientMap (Quotient.mk (adjSetoid HA.hφinj)) := isQuotientMap_quotient_mk'
  refine hq.isOpen_preimage.mp ?_
  rw [preimage_handleInteriorRegion]
  exact isOpenMap_inr _ HA.hS.isOpen_compl

/-- **The seam** `q(S)` — the glued attaching region, the image of the handle's attaching region `S`
(equivalently, via the glue, of `range φ ⊆ B`). Region (c) of the atlas: the collar-weld charts live
here (the wave's stated interface). -/
def seamRegion : Set HA.carrier := HA.fromHandle '' HA.S

/-- **The two interiors together with the seam cover the carrier.** Every carrier point is an
un-attached cylinder point, an interior handle point, or a seam point — the three-region decomposition
the surgery atlas is assembled over (`§1`). -/
theorem cylInteriorRegion_union_handleInteriorRegion_union_seamRegion :
    HA.cylInteriorRegion ∪ HA.handleInteriorRegion ∪ HA.seamRegion = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro w
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective w
  cases x with
  | inl b =>
    by_cases hb : b ∈ Set.range HA.φ
    · -- b = φ a for some a ∈ S; the point is the seam point q(inr a)
      obtain ⟨a, ha⟩ := hb
      exact Or.inr ⟨(a : HA.Ha), a.2, Quotient.sound ⟨a.2, ha⟩⟩
    · exact Or.inl (Or.inl ⟨b, hb, rfl⟩)
  | inr a =>
    by_cases ha : a ∈ HA.S
    · exact Or.inr ⟨a, ha, rfl⟩
    · exact Or.inl (Or.inr ⟨a, ha, rfl⟩)

end HandleAttachment

/-! ## §3. The interior regions are charted from the ends' charts.

Regions (a) and (b) of §5's atlas plan, discharged: once the ends `B` (cylinder) and `Ha` (handle)
carry `ChartedSpace H'` structures (their manifold-with-boundary/corners charts), the two interior
regions of `W` inherit them — each interior is homeomorphic (via the closed-embedding `fromCyl` /
`fromHandle` restricted to the open interior) to an OPEN subset of the corresponding end, self-charted
by `Opens.instChartedSpace`, transported through the homeomorphism. This is the exact meaning of
"transport `B`'s charts through the OPEN inclusion off the seam". -/

namespace HandleAttachment

variable {H' : Type*} [TopologicalSpace H'] (HA : HandleAttachment)

/-- **The cylinder interior region is homeomorphic to `B ∖ range φ`** — the closed embedding `fromCyl`
restricts to a homeomorphism of the open interior onto its image. -/
noncomputable def cylInteriorHomeo :
    ↥HA.cylInteriorRegion ≃ₜ ↥((Set.range HA.φ)ᶜ) :=
  (HA.isClosedEmbedding_fromCyl.isEmbedding.homeomorphImage (Set.range HA.φ)ᶜ).symm

/-- **The handle interior region is homeomorphic to `Ha ∖ S`** — the closed embedding `fromHandle`
restricts to a homeomorphism of the open interior onto its image. -/
noncomputable def handleInteriorHomeo :
    ↥HA.handleInteriorRegion ≃ₜ ↥(HA.Sᶜ) :=
  (HA.isClosedEmbedding_fromHandle.isEmbedding.homeomorphImage HA.Sᶜ).symm

/-- **The cylinder interior region is `H'`-charted** from the cylinder `B`'s charts: the open subset
`B ∖ range φ` is self-charted (`Opens.instChartedSpace`), transported through `cylInteriorHomeo`. -/
@[reducible] noncomputable def cylInteriorChartedSpace [ChartedSpace H' HA.B] :
    ChartedSpace H' ↥HA.cylInteriorRegion :=
  letI : ChartedSpace H' ↥((Set.range HA.φ)ᶜ) :=
    TopologicalSpace.Opens.instChartedSpace ⟨(Set.range HA.φ)ᶜ, HA.isClosed_range_φ.isOpen_compl⟩
  letI := chartedSpaceOfHomeo (H := ↥((Set.range HA.φ)ᶜ)) HA.cylInteriorHomeo
  ChartedSpace.comp H' ↥((Set.range HA.φ)ᶜ) ↥HA.cylInteriorRegion

/-- **The handle interior region is `H'`-charted** from the handle `Ha`'s charts: the open subset
`Ha ∖ S` is self-charted, transported through `handleInteriorHomeo`. -/
@[reducible] noncomputable def handleInteriorChartedSpace [ChartedSpace H' HA.Ha] :
    ChartedSpace H' ↥HA.handleInteriorRegion :=
  letI : ChartedSpace H' ↥(HA.Sᶜ) :=
    TopologicalSpace.Opens.instChartedSpace ⟨HA.Sᶜ, HA.hS.isOpen_compl⟩
  letI := chartedSpaceOfHomeo (H := ↥(HA.Sᶜ)) HA.handleInteriorHomeo
  ChartedSpace.comp H' ↥(HA.Sᶜ) ↥HA.handleInteriorRegion

end HandleAttachment

/-! ## §4. The manifold-carrying surgery-chart datum, and the carrier's chart atlas.

The honest interface + assembly for **Target 1** (`ChartedSpace H' W`), staged per §5. A
`SurgeryChartDatum` enriches a `HandleAttachment` with the chart data the atlas needs: a model `H'`,
`ChartedSpace H'` on the two ends `B`/`Ha` (their own manifold-with-boundary/corners charts, region
(a)+(b)'s source), and — the wave's genuinely-geometric input — an OPEN **collar neighborhood** of the
seam together with its `ChartedSpace H'` (region (c), the weld). Because the seam `q(S)` is CLOSED
(image of the compact attaching region), a valid chart atlas cannot use the seam *set* as a cover
member; the honest input is an open neighborhood of it — the welded collar, the union of the two
half-collars glued across the boundary face (the seam-chart design of record; see the module report).

From this datum the carrier's chart atlas is assembled by the §1 keystone over the three-region OPEN
cover {cylinder-interior, handle-interior, seam-collar}: the interiors are charted from the ends (§3),
the collar is the datum's input, and the three cover `W` (§2 + the collar containing the seam). -/

/-- **A manifold-carrying surgery-chart datum.** A `HandleAttachment` plus: a model `H'`; charts on the
cylinder end `B` and handle end `Ha`; and an OPEN collar neighborhood `seamNbhd` of the seam carrying
its own charts (the geometric weld input). The carrier's chart atlas is assembled from these
(`carrierChartedSpace`). -/
structure SurgeryChartDatum where
  /-- the underlying topological adjunction-space datum (opener). -/
  toHandleAttachment : HandleAttachment
  /-- the chart model (`= ModelProd E⁴ (half-space 1)` in the surgery-trace use). -/
  H' : Type*
  [topH' : TopologicalSpace H']
  /-- the cylinder end `B = M × I` is `H'`-charted (its manifold-with-boundary charts). -/
  [chartB : ChartedSpace H' toHandleAttachment.B]
  /-- the handle end `Ha = Dʳ⁺¹ × D^{n−r}` is `H'`-charted (its corner charts). -/
  [chartHa : ChartedSpace H' toHandleAttachment.Ha]
  /-- **the seam collar neighborhood** — an OPEN region of `W` containing the seam, the welded collar
  (union of the two half-collars glued across the boundary face). The genuinely-geometric input. -/
  seamNbhd : TopologicalSpace.Opens toHandleAttachment.carrier
  /-- the collar contains the seam (so the three regions form an OPEN cover). -/
  hseam : toHandleAttachment.seamRegion ⊆ seamNbhd
  /-- **the collar-weld charts** — `H'`-charts on the seam collar (region (c)). -/
  [chartSeam : ChartedSpace H' ↥seamNbhd]

attribute [instance] SurgeryChartDatum.topH' SurgeryChartDatum.chartB
  SurgeryChartDatum.chartHa SurgeryChartDatum.chartSeam

namespace SurgeryChartDatum

variable (D : SurgeryChartDatum)

/-- **The carrier `W = B ⊔_φ Ha` is `H'`-charted** — Target 1, assembled honestly. The §1 keystone
`chartedSpaceOfOpensCover` over the three-region OPEN cover {cylinder-interior, handle-interior,
seam-collar}: the interiors inherit `B`/`Ha`'s charts through the interior open embeddings (§3), the
collar carries the datum's weld charts, and the three cover `W` (§2 union + the collar ⊇ seam). The
per-region *smoothness/compatibility* — the `IsManifold` layer — is the next target (§5), not part of
this `ChartedSpace`. -/
@[reducible] noncomputable def carrierChartedSpace :
    ChartedSpace D.H' D.toHandleAttachment.carrier :=
  chartedSpaceOfOpensCover
    (fun i : Fin 3 =>
      ![⟨D.toHandleAttachment.cylInteriorRegion, D.toHandleAttachment.isOpen_cylInteriorRegion⟩,
        ⟨D.toHandleAttachment.handleInteriorRegion, D.toHandleAttachment.isOpen_handleInteriorRegion⟩,
        D.seamNbhd] i)
    (by
      intro w
      have hcov :=
        D.toHandleAttachment.cylInteriorRegion_union_handleInteriorRegion_union_seamRegion
      rw [Set.eq_univ_iff_forall] at hcov
      rcases hcov w with (hcyl | hhandle) | hs
      · exact ⟨0, hcyl⟩
      · exact ⟨1, hhandle⟩
      · exact ⟨2, D.hseam hs⟩)
    (fun i =>
      match i with
      | 0 => D.toHandleAttachment.cylInteriorChartedSpace
      | 1 => D.toHandleAttachment.handleInteriorChartedSpace
      | 2 => D.chartSeam)

end SurgeryChartDatum

end SKEFTHawking.SurgeryFoundation
