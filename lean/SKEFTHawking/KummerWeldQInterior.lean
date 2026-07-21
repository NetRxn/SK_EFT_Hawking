/-
# Phase 5q.H — K6′b Leg 4: the Q-piece interior is OPEN in the Kummer weld (chart family 2/3)

`KummerWeldOpenPieces` landed chart family **1 of 3** — the 16 `E`-copies' fiber interiors embed as
OPEN subspaces of `K3 = Q ∪_{16 × ℝP³} (16 × E)`. This module lands family **2 of 3**: the same
statement on the `Q` side.

**The gate that had to be discharged first.** The E-side saturation ran on `fiberNorm < 1`, an
*openly-defined* interior. The Q side has no such scalar: `interiorQ` is `∂Q`'s complement, so its
openness needs **`IsClosed boundaryQ`** — which was not banked anywhere in tree. §1 supplies it:
each boundary sphere `chartSphere c = centeredChartParam c '' {sqNorm = ρ²}` is the continuous image
of a *compact* Euclidean 3-sphere (closed + bounded in the proper space `ℝ⁴`), hence compact, hence
closed; its `Subtype.val`-preimage `boundarySphere c` is closed in the compact `↥T⁴°`, hence compact;
its `qmk`-image `boundaryComponent c` is compact, hence closed in the Hausdorff `Q`; and `∂Q` is the
union of *sixteen* of those (`fixedFinset`), a finite union of closed sets.

**Then the mirror of the E-side saturation law.** The weld's `inl` end is always a `qBdryMap c r`,
which lies in `boundaryComponent c.1 ⊆ boundaryQ` — so an `inl`-set of `interiorQ`-points is
saturated, and saturated + open upstairs ⟹ open downstairs through the quotient map `weldMk`.

**Contents.** §1 `IsClosed boundaryQ` (the named residual, discharged); §2 `interiorQ` and its
openness; §3 the saturation law; §4 the open embedding `isOpenEmbedding_qInteriorPiece`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerWeldOpenPieces

namespace SKEFTHawking.KummerWeldQInterior

open SKEFTHawking.KummerK3Base
open SKEFTHawking.KummerInvolution
open SKEFTHawking.KummerPuncturedTorus
open SKEFTHawking.KummerFreeQuotient
open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerWeld

noncomputable section

/-! ## §1. `∂Q` is closed — the residual `KummerWeldOpenPieces` named -/

/-- **The Euclidean chart 3-sphere `{sqNorm = ρ²} ⊂ ℝ⁴` is compact.** Closed (a level set of the
continuous `sqNorm`) and bounded (each coordinate satisfies `t_i² ≤ ρ²`, so `|t_i| ≤ ρ`), in the
proper space `ℝ × ℝ × ℝ × ℝ`. -/
theorem isCompact_sqNormSphere :
    IsCompact {t : ℝ × ℝ × ℝ × ℝ | sqNorm t = excisionRadius ^ 2} := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_eq sqNorm_continuous continuous_const) ?_
  refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨excisionRadius, fun t ht => ?_⟩
  have hsq : sqNorm t = excisionRadius ^ 2 := ht
  have hnn : (0 : ℝ) ≤ excisionRadius := excisionRadius_pos.le
  have h1 : |t.1| ≤ excisionRadius := by
    refine abs_le_of_sq_le_sq hnn ?_
    have := sq_nonneg t.2.1; have := sq_nonneg t.2.2.1; have := sq_nonneg t.2.2.2
    simp only [sqNorm] at hsq; linarith
  have h2 : |t.2.1| ≤ excisionRadius := by
    refine abs_le_of_sq_le_sq hnn ?_
    have := sq_nonneg t.1; have := sq_nonneg t.2.2.1; have := sq_nonneg t.2.2.2
    simp only [sqNorm] at hsq; linarith
  have h3 : |t.2.2.1| ≤ excisionRadius := by
    refine abs_le_of_sq_le_sq hnn ?_
    have := sq_nonneg t.1; have := sq_nonneg t.2.1; have := sq_nonneg t.2.2.2
    simp only [sqNorm] at hsq; linarith
  have h4 : |t.2.2.2| ≤ excisionRadius := by
    refine abs_le_of_sq_le_sq hnn ?_
    have := sq_nonneg t.1; have := sq_nonneg t.2.1; have := sq_nonneg t.2.2.1
    simp only [sqNorm] at hsq; linarith
  simp only [Metric.mem_closedBall, dist_zero_right]
  simp only [Prod.norm_def, Real.norm_eq_abs, max_le_iff]
  exact ⟨h1, h2, h3, h4⟩

/-- **Each boundary 3-sphere of `T⁴°` is compact** — the continuous `centeredChartParam c` image of
the compact Euclidean sphere. -/
theorem isCompact_chartSphere (c : TorusFour) : IsCompact (chartSphere c) :=
  isCompact_sqNormSphere.image (continuous_centeredChartParam c)

/-- **Each boundary 3-sphere is closed in `T⁴`** (compact in a Hausdorff space). -/
theorem isClosed_chartSphere (c : TorusFour) : IsClosed (chartSphere c) :=
  (isCompact_chartSphere c).isClosed

/-- **`∂B_c` is compact inside `T⁴°`** — closed (a `Subtype.val`-preimage of the closed
`chartSphere c`) in the compact `↥T⁴°`. -/
theorem isCompact_boundarySphere (c : TorusFour) : IsCompact (boundarySphere c) := by
  have hcl : IsClosed (boundarySphere c) :=
    (isClosed_chartSphere c).preimage continuous_subtype_val
  exact hcl.isCompact

/-- **Each boundary component `∂Q_c = qmk '' ∂B_c` is compact.** -/
theorem isCompact_boundaryComponent (c : TorusFour) : IsCompact (boundaryComponent c) :=
  (isCompact_boundarySphere c).image continuous_quotient_mk'

/-- **Each boundary component is closed in `Q`** (compact in the Hausdorff `FreeQuotient`). -/
theorem isClosed_boundaryComponent (c : TorusFour) : IsClosed (boundaryComponent c) :=
  (isCompact_boundaryComponent c).isClosed

/-- **`∂Q` IS CLOSED** — the residual `KummerWeldOpenPieces` named as the gate on the Q-side chart
family. A union of the *sixteen* closed components `∂Q_c`, `c ∈ fixedFinset` (finite union). -/
theorem isClosed_boundaryQ : IsClosed boundaryQ := by
  rw [boundaryQ_eq_biUnion_fixedFinset]
  exact isClosed_biUnion_finset (fun c _ => isClosed_boundaryComponent c)

/-! ## §1b. The seam exhausts `∂Q` — `range (qBdryMap c) = ∂Q_c`

`KummerWeld` banks that the Q-side seam map lands *in* the boundary component
(`qBdryMap_mem_boundaryComponent`) and is injective, but never that it is ONTO it. Surjectivity is
what makes the seam a genuine cover of `∂Q`, and it is exactly what the atlas's covering argument
needs on the Q side: a `Q`-point outside `interiorQ` must be reachable as a `qBdryMap`-image.

The content is that `scaleToChart : S³ ⊂ ℂ² → ℝ⁴` hits every chart vector of square-norm `ρ²`
(divide by `ρ` and read the four reals off as two complex numbers). -/

/-- **`scaleToChart` is onto the Euclidean chart sphere of radius `ρ`.** Every `t : ℝ⁴` with
`sqNorm t = ρ²` is `ρ ·` a unit vector of `ℂ² ≅ ℝ⁴`. -/
theorem scaleToChart_surjOn {t : ℝ × ℝ × ℝ × ℝ} (ht : sqNorm t = excisionRadius ^ 2) :
    ∃ a : S3, scaleToChart a = t := by
  have hρ : excisionRadius ≠ 0 := ne_of_gt excisionRadius_pos
  have hu : ‖(⟨t.1 / excisionRadius, t.2.1 / excisionRadius⟩ : ℂ)‖ ^ 2
      + ‖(⟨t.2.2.1 / excisionRadius, t.2.2.2 / excisionRadius⟩ : ℂ)‖ ^ 2 = 1 := by
    rw [← re_sq_add_im_sq, ← re_sq_add_im_sq]
    simp only [sqNorm] at ht
    field_simp
    linarith [ht]
  refine ⟨⟨(⟨t.1 / excisionRadius, t.2.1 / excisionRadius⟩,
    ⟨t.2.2.1 / excisionRadius, t.2.2.2 / excisionRadius⟩), hu⟩, ?_⟩
  simp only [scaleToChart]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;>
    simp only [] <;> field_simp

/-- **THE SEAM EXHAUSTS `∂Q_c`**: the Q-side seam map is ONTO the boundary component, so
`range (qBdryMap c) = ∂Q_c`. With `qBdryMap_injective` this makes `qBdryMap c` a bijection
`ℝP³ ≃ ∂Q_c` — the pinned `S³/±1` presentation is the *whole* boundary component, not a piece of
it. -/
theorem range_qBdryMap_eq_boundaryComponent (c : EIndex) :
    Set.range (qBdryMap c) = boundaryComponent c.1 := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨r, rfl⟩; exact qBdryMap_mem_boundaryComponent c r
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, ht, hteq⟩ : x.1 ∈ chartSphere c.1 := hx
    obtain ⟨a, ha⟩ := scaleToChart_surjOn (t := t) ht
    refine ⟨mkRP3 a, ?_⟩
    show s3ToQ c a = qmk x
    have hval : centeredChartParam c.1 (scaleToChart a) = x.1 := by rw [ha]; exact hteq
    exact congrArg qmk (Subtype.ext hval)

/-! ## §2. The Q-piece interior -/

/-- **The interior of the Q-piece** — the complement of the 16-component boundary `∂Q`. -/
def interiorQ : Set FreeQuotient := boundaryQᶜ

theorem isOpen_interiorQ : IsOpen interiorQ := isClosed_boundaryQ.isOpen_compl

/-- **The seam avoids the Q-interior** — the load-bearing disjointness on the Q side: every point the
weld identifies on its `inl` end is a `qBdryMap c r`, which lies in the boundary component of the
fixed point `c` (`qBdryMap_mem_boundaryComponent`), hence in `∂Q`. -/
theorem notMem_interiorQ_qBdryMap (c : EIndex) (r : RP3) : qBdryMap c r ∉ interiorQ := by
  intro h
  exact h (Set.mem_biUnion (eIndex_fixedSet c) (qBdryMap_mem_boundaryComponent c r))

/-! ## §3. Saturation: the weld does nothing to an interior `inl`-set -/

/-- **The Q-side saturation law.** For a set of `Q`-points that all miss `∂Q`, the `weldMk` preimage
of its image is the set itself: the weld's only nontrivial identifications have their `inl` end on
`∂Q`, which such a set misses. The mirror of
`KummerWeldOpenPieces.preimage_image_inr_of_interiorE`. -/
theorem preimage_image_inl_of_interiorQ {S : Set FreeQuotient} (hS : S ⊆ interiorQ) :
    weldMk ⁻¹' (weldMk '' (Sum.inl '' S)) = Sum.inl '' S := by
  refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
  rintro a ⟨b, ⟨q, hq, rfl⟩, hab⟩
  rcases Quotient.exact hab with he | ⟨c, r, h1, _⟩ | ⟨c, r, _, h2⟩
  · exact he ▸ ⟨q, hq, rfl⟩
  · -- the seam's `inl` end is `qBdryMap c r`, which is not in `interiorQ`
    have hq1 : q = qBdryMap c r := Sum.inl.inj h1
    exact absurd (hq1 ▸ hS hq) (notMem_interiorQ_qBdryMap c r)
  · exact absurd h2 (by simp)

/-- **An open `interiorQ`-set has open image in `K3`.** Saturated (§3) plus open upstairs, pushed
through the quotient map `weldMk`. -/
theorem isOpen_weldImage_inl_of_interiorQ {S : Set FreeQuotient} (hS : S ⊆ interiorQ)
    (hopen : IsOpen S) : IsOpen (weldMk '' (Sum.inl '' S)) := by
  have hqm : Topology.IsQuotientMap (weldMk : WeldCarrier → KummerK3) := isQuotientMap_quotient_mk'
  refine hqm.isOpen_preimage.mp ?_
  rw [preimage_image_inl_of_interiorQ hS]
  exact isOpenMap_inl _ hopen

/-! ## §4. The Q-interior chart family descends -/

/-- **The Q-piece's interior, as a map into `K3`.** -/
def qInteriorPiece (q : ↥interiorQ) : KummerK3 := weldMk (Sum.inl q.1)

theorem continuous_qInteriorPiece : Continuous qInteriorPiece :=
  continuous_weldMk.comp (continuous_inl.comp continuous_subtype_val)

theorem injective_qInteriorPiece : Function.Injective qInteriorPiece :=
  fun _ _ h => Subtype.ext (weldMk_inl_injective h)

/-- **THE Q-INTERIOR CHART FAMILY DESCENDS.** The free quotient's interior `Q ∖ ∂Q` embeds as an
**open** subspace of the Kummer weld `K3` — not merely as the closed subspace of
`KummerWeld.isClosedEmbedding_qImage`. So every chart of `Q` whose source lies in `interiorQ`
transports to a chart of `K3`: chart family **2 of 3** of the weld atlas, the companion of
`KummerWeldOpenPieces.isOpenEmbedding_eInteriorCopy`. -/
theorem isOpenEmbedding_qInteriorPiece : Topology.IsOpenEmbedding qInteriorPiece := by
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    continuous_qInteriorPiece injective_qInteriorPiece ?_
  intro U hU
  obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.mp hU
  have himg : qInteriorPiece '' U = weldMk '' (Sum.inl '' (V ∩ interiorQ)) := by
    ext y
    constructor
    · rintro ⟨q, hqU, rfl⟩
      have hqV : q.1 ∈ V := by
        have : q ∈ Subtype.val ⁻¹' V := by rw [hVU]; exact hqU
        exact this
      exact ⟨Sum.inl q.1, ⟨q.1, ⟨hqV, q.2⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨q, ⟨hqV, hqI⟩, rfl⟩, rfl⟩
      exact ⟨⟨q, hqI⟩, by rw [← hVU]; exact hqV, rfl⟩
  rw [himg]
  exact isOpen_weldImage_inl_of_interiorQ (fun _ hp => hp.2) (hV.inter isOpen_interiorQ)

/-! ## §5. The two open families are disjoint and their union is the seam's complement

The E-interior family (`KummerWeldOpenPieces`) and the Q-interior family (§4) miss each other, and
together they miss exactly the seam. That is the covering bookkeeping the third (seam double-collar)
family has to close. -/

/-- **The two interior families' images are disjoint in `K3`** — a `Q`-interior point and an
`E`-interior point are never welded together (the weld's only cross-piece identifications have both
ends on the seam). -/
theorem disjoint_qInterior_eInterior :
    Disjoint (Set.range qInteriorPiece)
      (weldMk '' (Sum.inr '' ((Set.univ : Set EIndex) ×ˢ KummerWeldOpenPieces.interiorE))) := by
  rw [Set.disjoint_left]
  rintro _ ⟨q, rfl⟩ ⟨_, ⟨p, -, rfl⟩, hyp⟩
  rcases Quotient.exact hyp with he | ⟨c, r, h1, -⟩ | ⟨c, r, h1, -⟩
  · exact absurd he (by simp)
  · exact absurd h1 (by simp)
  · have hq1 : q.1 = qBdryMap c r := Sum.inl.inj h1
    exact notMem_interiorQ_qBdryMap c r (hq1 ▸ q.2)

/-- **The two interior families cover exactly the seam's complement.** Every point of `K3` is either
a `Q`-interior point, an `E`-interior point, or a seam point — and the seam is precisely what the
third chart family (the double collar) must chart. -/
theorem qInterior_union_eInterior_union_seam :
    Set.range qInteriorPiece
      ∪ weldMk '' (Sum.inr '' ((Set.univ : Set EIndex) ×ˢ KummerWeldOpenPieces.interiorE))
      ∪ seam = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  obtain ⟨a, rfl⟩ := weldMk_surjective x
  cases a with
  | inl q =>
    by_cases hq : q ∈ interiorQ
    · exact Or.inl (Or.inl ⟨⟨q, hq⟩, rfl⟩)
    · -- `q ∈ ∂Q`, so `weldMk (inl q)` lies on the seam via the Q-side description
      right
      rw [seam_eq_qBoundary_image]
      have hq' : q ∈ boundaryQ := not_not.mp hq
      obtain ⟨c, hc, hqc⟩ := Set.mem_iUnion₂.mp hq'
      have hC : (⟨c, (mem_fixedFinset c).mpr hc⟩ : EIndex).1 = c := rfl
      obtain ⟨r, hr⟩ : q ∈ Set.range (qBdryMap ⟨c, (mem_fixedFinset c).mpr hc⟩) := by
        rw [range_qBdryMap_eq_boundaryComponent, hC]; exact hqc
      exact Set.mem_iUnion.mpr ⟨⟨c, (mem_fixedFinset c).mpr hc⟩, ⟨r, by simp only [hr]⟩⟩
  | inr p =>
    by_cases hp : p.2 ∈ KummerWeldOpenPieces.interiorE
    · exact Or.inl (Or.inr ⟨Sum.inr p, ⟨p, ⟨Set.mem_univ _, hp⟩, rfl⟩, rfl⟩)
    · right
      have hb : p.2 ∈ boundaryE := by
        rw [KummerWeldOpenPieces.interiorE_eq_compl_boundaryE] at hp
        exact not_not.mp hp
      obtain ⟨r, hr⟩ : p.2 ∈ Set.range bdryMapRP3 := by
        rw [range_bdryMapRP3_eq_boundaryE]; exact hb
      exact Set.mem_iUnion.mpr ⟨p.1, ⟨r, by simp only [hr]⟩⟩

end

end SKEFTHawking.KummerWeldQInterior
