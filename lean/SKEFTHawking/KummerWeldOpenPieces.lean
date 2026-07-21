/-
# Phase 5q.H — K6′b Leg 3: the E-piece interiors are OPEN in the Kummer weld

`KummerWeld` §7 lands the topological *floor* of the weld's chart descent: `Q` and each `E`-copy
embed as CLOSED subspaces of `K3 = Q ∪_{16 × ℝP³} (16 × E)` (`isClosedEmbedding_qImage` /
`isClosedEmbedding_eCopy`). A closed embedding is not enough to carry charts — an atlas needs the
piece charts to descend on an **open** set. This module supplies that on the E-side.

**The mechanism.** The weld relation only ever joins an `inl`-point to an `inr`-point, and its
`inr` end is always a seam point `bdryMapRP3 r`, which lies on `∂E` (`fiberNorm = 1`). So an
`inr`-set consisting of *fiber-interior* points (`fiberNorm < 1`) is **saturated**: `weldMk` neither
adds nor merges anything on it (`preimage_image_inr_of_interiorE`). Saturated + open upstairs
⟹ open downstairs, since `weldMk` is a quotient map. Combined with `DiscreteTopology EIndex`
(the 16 fixed points are a finite subspace of the Hausdorff `T⁴`) this makes each single copy's
interior an **open embedding** into `K3` — the first of the weld atlas's three chart families.

**Contents.** §1 the E-interior `interiorE = {fiberNorm < 1}` and its openness / disjointness from
the seam; §2 the saturation law; §3 `isOpen_weldImage_inr_of_interiorE`; §4 the per-copy open
embedding `isOpenEmbedding_eInteriorCopy` and the whole-E-part statement.

**Residuals (sharply named, NOT proved here).**
* `interiorQ` open in `K3` — needs `IsClosed boundaryQ` (equivalently: each `boundaryComponent c` is
  closed in `FreeQuotient`), which is not yet banked. Same saturation mechanism otherwise.
* **the seam double-collar** — the third chart family, charting a neighbourhood of the seam itself
  by gluing the Q-side boundary collar to the E-side boundary collar across `bdryMapRP3`. Its
  smooth-compatibility is exactly what `KummerSeamSmooth.contMDiff_bdryMapRP3` was built to feed;
  the construction itself remains open.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerWeldFiberFlow

namespace SKEFTHawking.KummerWeldOpenPieces

open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerWeld
open SKEFTHawking.KummerWeldFiberFlow
open SKEFTHawking.KummerFreeQuotient (FreeQuotient)

noncomputable section

/-! ## §1. The E-piece interior -/

/-- **The interior of the E-piece** — the fiber-interior locus `‖w‖ < 1`, the complement of the
seam `∂E` inside `ResE`. -/
def interiorE : Set ResE := {x : ResE | fiberNorm x < 1}

theorem isOpen_interiorE : IsOpen interiorE :=
  isOpen_lt continuous_fiberNorm continuous_const

/-- The E-interior is exactly the complement of the boundary — the fiber norm is `≤ 1` throughout,
so `< 1` and `≠ 1` agree. -/
theorem interiorE_eq_compl_boundaryE : interiorE = boundaryEᶜ := by
  ext x
  simp only [interiorE, Set.mem_setOf_eq, Set.mem_compl_iff, ← fiberNorm_eq_one_iff]
  exact ⟨fun h => ne_of_lt h, fun h => lt_of_le_of_ne (fiberNorm_le_one x) h⟩

/-- **The seam avoids the E-interior** — the load-bearing disjointness: every point the weld
identifies is a `bdryMapRP3`-image, hence has fiber norm exactly `1`. -/
theorem notMem_interiorE_bdryMapRP3 (r : RP3) : bdryMapRP3 r ∉ interiorE := fun h =>
  absurd (fiberNorm_bdryMapRP3 r) (ne_of_lt h)

/-! ## §2. Saturation: the weld does nothing to an interior `inr`-set -/

/-- **The saturation law.** For a set of `E`-points that are all fiber-interior, the `weldMk`
preimage of its image is the set itself: the weld's only nontrivial identifications have their
`inr` end on `∂E`, which such a set misses. This is what upgrades `KummerWeld`'s closed embedding
to an open one. -/
theorem preimage_image_inr_of_interiorE {S : Set (EIndex × ResE)}
    (hS : ∀ p ∈ S, p.2 ∈ interiorE) :
    weldMk ⁻¹' (weldMk '' (Sum.inr '' S)) = Sum.inr '' S := by
  refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
  rintro a ⟨b, ⟨p, hp, rfl⟩, hab⟩
  rcases Quotient.exact hab with he | ⟨c, r, h1, _⟩ | ⟨c, r, _, h2⟩
  · exact he ▸ ⟨p, hp, rfl⟩
  · exact absurd h1 (by simp)
  · -- the seam's `inr` end is `bdryMapRP3 r`, which is not fiber-interior
    have hp2 : p.2 = bdryMapRP3 r := congrArg Prod.snd (Sum.inr.inj h2)
    exact absurd (hp2 ▸ hS p hp) (notMem_interiorE_bdryMapRP3 r)

/-! ## §3. Openness in `K3` -/

/-- **An open, fiber-interior `inr`-set has open image in `K3`.** Saturated (§2) plus open upstairs,
pushed through the quotient map `weldMk`. -/
theorem isOpen_weldImage_inr_of_interiorE {S : Set (EIndex × ResE)}
    (hS : ∀ p ∈ S, p.2 ∈ interiorE) (hopen : IsOpen S) :
    IsOpen (weldMk '' (Sum.inr '' S)) := by
  have hqm : Topology.IsQuotientMap (weldMk : WeldCarrier → KummerK3) :=
    isQuotientMap_quotient_mk'
  refine hqm.isOpen_preimage.mp ?_
  rw [preimage_image_inr_of_interiorE hS]
  exact isOpenMap_inr _ hopen

/-! ## §4. The E-interior chart family descends -/

/-- **The `c`-th E-copy's interior, as a map into `K3`.** -/
def eInteriorCopy (c : EIndex) (e : ↥interiorE) : KummerK3 := weldMk (Sum.inr (c, e.1))

theorem continuous_eInteriorCopy (c : EIndex) : Continuous (eInteriorCopy c) :=
  continuous_weldMk.comp (continuous_inr.comp (continuous_const.prodMk continuous_subtype_val))

theorem injective_eInteriorCopy (c : EIndex) : Function.Injective (eInteriorCopy c) :=
  fun _ _ h => Subtype.ext (congrArg Prod.snd (weldMk_inr_injective h))

/-- **THE E-INTERIOR CHART FAMILY DESCENDS.** Each of the 16 `E`-copies has its fiber-interior
embedded as an **open** subspace of the Kummer weld `K3` — not merely as the closed subspace of
`KummerWeld.isClosedEmbedding_eCopy`. So every chart of `ResE` whose source lies in `interiorE`
transports to a chart of `K3`, which is the first of the weld atlas's three chart families.

The single-copy statement needs `{c}` open in `EIndex`, i.e. `DiscreteTopology EIndex` — available
because the 16 fixed points form a finite subspace of the Hausdorff `T⁴`. -/
theorem isOpenEmbedding_eInteriorCopy (c : EIndex) :
    Topology.IsOpenEmbedding (eInteriorCopy c) := by
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_eInteriorCopy c) (injective_eInteriorCopy c) ?_
  intro U hU
  obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.mp hU
  have himg : eInteriorCopy c '' U
      = weldMk '' (Sum.inr '' (({c} : Set EIndex) ×ˢ (V ∩ interiorE))) := by
    ext y
    constructor
    · rintro ⟨e, heU, rfl⟩
      have heV : e.1 ∈ V := by
        have : e ∈ Subtype.val ⁻¹' V := by rw [hVU]; exact heU
        exact this
      exact ⟨Sum.inr (c, e.1), ⟨(c, e.1), ⟨rfl, heV, e.2⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨p, ⟨hpc, hpV, hpI⟩, rfl⟩, rfl⟩
      exact ⟨⟨p.2, hpI⟩, by rw [← hVU]; exact hpV,
        by rw [eInteriorCopy, show c = p.1 from hpc.symm]⟩
  rw [himg]
  refine isOpen_weldImage_inr_of_interiorE (fun p hp => hp.2.2) ?_
  exact (isOpen_discrete _).prod (hV.inter isOpen_interiorE)

/-- **The whole E-part's interior is open in `K3`** — the union over the 16 copies, stated without
the discreteness detour. -/
theorem isOpen_eInteriorImage :
    IsOpen (weldMk '' (Sum.inr '' ((Set.univ : Set EIndex) ×ˢ interiorE))) :=
  isOpen_weldImage_inr_of_interiorE (fun _ hp => hp.2) (isOpen_univ.prod isOpen_interiorE)

end

end SKEFTHawking.KummerWeldOpenPieces
