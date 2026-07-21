/-
# Phase 5q.H — K6′b Leg 8: the seam has an OPEN two-sided neighbourhood, and the three families
form an OPEN COVER of `K3`

Leg 7 built the seam double collar `ℝP³ × [−1/8, 1/2] ↪ K3` as a homeomorphism onto its range. A
*closed* collar cannot carry charts; this module supplies the missing openness, completing the
topological layer of the weld atlas.

**The trick that makes the saturation argument work.** Doing this one seam component at a time would
require showing that `∂Q_{c'}` misses the `c`-collar for `c' ≠ c` (a separate separation argument).
Taking the neighbourhood of the WHOLE seam at once removes that obligation entirely: the weld's
`inr` end of any seam pair has `fiberNorm = 1 > 1/2`, so it lands in the E-part of the carrier *for
whatever copy index it carries*; and the weld's `inl` end is `qBdryMap c₀ r₀`, at chart radius
exactly `1/2 < 5/8`, so it lands in the Q-part *for its own* `c₀`. Both directions of the weld
relation therefore stay inside the carrier — it is saturated (§3), and a saturated open set has open
image under the quotient map `weldMk`.

**The payoff (§5).** `isOpen_cover_three_families`: the Q-interior family (chart family 2/3,
`KummerWeldQInterior`), the E-interior family (chart family 1/3, `KummerWeldOpenPieces`) and this
open seam neighbourhood (family 3/3) are three OPEN sets covering `K3`. That is the covering
condition a `ChartedSpace` on `K3` needs; what remains for family 3/3 is the transport of the
`ℝP³` atlas (`KummerRP3Smooth.isManifold_rp3`) across the double collar into `𝓡 4`, and the
transition classes.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerSeamDoubleCollar

namespace SKEFTHawking.KummerSeamOpenNbhd

open SKEFTHawking.KummerK3Base
open SKEFTHawking.KummerPuncturedTorus
open SKEFTHawking.KummerFreeQuotient
open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerWeldFiberFlow
open SKEFTHawking.KummerWeld
open SKEFTHawking.KummerSeamCollarQ (qParam qCollar qCollarS3 qCollar_half qShellPoint
  sqNorm_qShellPoint)
open SKEFTHawking.KummerSeamDoubleCollar (dblParam dblCollar clampE clampQ eBranch qBranch
  dblCollar_of_nonneg dblCollar_of_neg clampE_coe clampQ_coe)

noncomputable section

/-! ## §1. The Q-side open collar of a boundary component -/

/-- **The open chart ball of radius `5/8` around the fixed point `c`** in `T⁴`. Open because
`centeredChartParam c` is an open map. -/
def qOpenBall (c : EIndex) : Set TorusFour :=
  centeredChartParam c.1 '' {t : ℝ × ℝ × ℝ × ℝ | sqNorm t < (5 / 8) ^ 2}

theorem isOpen_qOpenBall (c : EIndex) : IsOpen (qOpenBall c) :=
  isOpenMap_centeredChartParam c.1 _ (isOpen_lt sqNorm_continuous continuous_const)

/-- The punctured-torus part of that ball — the OPEN Q-side collar shell of the boundary sphere
`∂B_c` (the excised interior is not in `T⁴°`, so this is exactly the radius-`[1/2, 5/8)` shell). -/
def qOpenShell (c : EIndex) : Set (↥puncturedTorus) := Subtype.val ⁻¹' qOpenBall c

theorem isOpen_qOpenShell (c : EIndex) : IsOpen (qOpenShell c) :=
  (isOpen_qOpenBall c).preimage continuous_subtype_val

/-- **The Q-side OPEN collar of the boundary component `∂Q_c`** — open because `qmk` is an open
map (the free `ℤˣ`-orbit quotient). -/
def qOpenCollarSet (c : EIndex) : Set FreeQuotient := qmk '' qOpenShell c

theorem isOpen_qOpenCollarSet (c : EIndex) : IsOpen (qOpenCollarSet c) :=
  isOpenMap_qmk _ (isOpen_qOpenShell c)

/-- **Every Q-collar point of radius `< 5/8` lies in the open collar.** -/
theorem qCollar_mem_qOpenCollarSet (c : EIndex) (p : RP3 × ↥qParam) (h : (p.2 : ℝ) < 5 / 8) :
    qCollar c p ∈ qOpenCollarSet c := by
  obtain ⟨r, s⟩ := p
  induction r using Quotient.inductionOn with
  | _ a =>
    refine ⟨⟨centeredChartParam c.1 (qShellPoint a (s : ℝ)),
      SKEFTHawking.KummerSeamCollarQ.qShellPoint_mem_puncturedTorus c a
        SKEFTHawking.KummerSeamCollarQ.qParam_lower
        SKEFTHawking.KummerSeamCollarQ.qParam_lt_threeQuarters⟩, ?_, rfl⟩
    refine ⟨qShellPoint a (s : ℝ), ?_, rfl⟩
    show sqNorm (qShellPoint a (s : ℝ)) < (5 / 8) ^ 2
    rw [sqNorm_qShellPoint]
    have hlow : 0 < (s : ℝ) := SKEFTHawking.KummerSeamCollarQ.qParam_pos
    nlinarith

/-- **The seam itself lies in the Q-side open collar** — `qBdryMap c` is the radius-`1/2` face. -/
theorem qBdryMap_mem_qOpenCollarSet (c : EIndex) (r : RP3) :
    qBdryMap c r ∈ qOpenCollarSet c := by
  rw [← qCollar_half c r]
  exact qCollar_mem_qOpenCollarSet c _ (by show (1 : ℝ) / 2 < 5 / 8; norm_num)

/-! ## §2. The E-side open collar -/

/-- **The E-side OPEN collar** — the fiber-radius `> 1/2` locus, the open version of
`KummerSeamCollarE.eCollarSet`. -/
def eOpenSet : Set ResE := {x : ResE | 1 / 2 < fiberNorm x}

theorem isOpen_eOpenSet : IsOpen eOpenSet := isOpen_lt continuous_const continuous_fiberNorm

theorem bdryMapRP3_mem_eOpenSet (r : RP3) : bdryMapRP3 r ∈ eOpenSet := by
  show (1 : ℝ) / 2 < fiberNorm (bdryMapRP3 r)
  rw [fiberNorm_bdryMapRP3]; norm_num

/-! ## §3. The saturated carrier of the seam neighbourhood -/

/-- **The pre-weld carrier of the seam neighbourhood** — the Q-side open collars of ALL sixteen
components, together with the E-side open collar of every copy. -/
def seamNbhdCarrier : Set WeldCarrier :=
  Sum.inl '' (⋃ c : EIndex, qOpenCollarSet c)
    ∪ Sum.inr '' ((Set.univ : Set EIndex) ×ˢ eOpenSet)

theorem isOpen_seamNbhdCarrier : IsOpen seamNbhdCarrier :=
  (isOpenMap_inl _ (isOpen_iUnion isOpen_qOpenCollarSet)).union
    (isOpenMap_inr _ (isOpen_univ.prod isOpen_eOpenSet))

/-- **THE CARRIER IS SATURATED.** Both ends of every weld pair stay inside it: the `inr` end is
`bdryMapRP3 r₀` with `fiberNorm = 1 > 1/2` (E-part, for whatever copy index), and the `inl` end is
`qBdryMap c₀ r₀` at chart radius exactly `1/2 < 5/8` (Q-part, for its own `c₀`). Taking all sixteen
components at once is what makes this work without any inter-component separation argument. -/
theorem preimage_image_seamNbhdCarrier :
    weldMk ⁻¹' (weldMk '' seamNbhdCarrier) = seamNbhdCarrier := by
  refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
  rintro a ⟨b, hb, hab⟩
  rcases Quotient.exact hab with he | ⟨c₀, r₀, _, h2⟩ | ⟨c₀, r₀, h1, _⟩
  · exact he ▸ hb
  · -- `SeamJoin b a`: `a` is the `inr` end, `bdryMapRP3 r₀`, at fiber radius `1`
    exact Or.inr ⟨(c₀, bdryMapRP3 r₀), ⟨Set.mem_univ _, bdryMapRP3_mem_eOpenSet r₀⟩, h2.symm⟩
  · -- `SeamJoin a b`: `a` is the `inl` end, `qBdryMap c₀ r₀`, at chart radius `1/2`
    exact Or.inl ⟨qBdryMap c₀ r₀,
      Set.mem_iUnion.mpr ⟨c₀, qBdryMap_mem_qOpenCollarSet c₀ r₀⟩, h1.symm⟩

/-! ## §4. The open seam neighbourhood -/

/-- **THE OPEN TWO-SIDED NEIGHBOURHOOD OF THE SEAM IN `K3`** — the weld image of the saturated
carrier. Chart family 3/3's underlying open set. -/
def seamNbhd : Set KummerK3 := weldMk '' seamNbhdCarrier

/-- **The seam neighbourhood is OPEN** — saturated (§3) plus open upstairs, through the quotient
map `weldMk`. -/
theorem isOpen_seamNbhd : IsOpen seamNbhd := by
  have hqm : Topology.IsQuotientMap (weldMk : WeldCarrier → KummerK3) := isQuotientMap_quotient_mk'
  refine hqm.isOpen_preimage.mp ?_
  show IsOpen (weldMk ⁻¹' (weldMk '' seamNbhdCarrier))
  rw [preimage_image_seamNbhdCarrier]
  exact isOpen_seamNbhdCarrier

/-- **The seam neighbourhood contains the seam.** -/
theorem seam_subset_seamNbhd : seam ⊆ seamNbhd := by
  rintro x hx
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hx
  obtain ⟨r, rfl⟩ := hc
  exact ⟨Sum.inr (c, bdryMapRP3 r),
    Or.inr ⟨(c, bdryMapRP3 r), ⟨Set.mem_univ _, bdryMapRP3_mem_eOpenSet r⟩, rfl⟩, rfl⟩

/-- **The double collar's interior lands in the open neighbourhood** — every collar point with
`−1/8 < v < 1/2` is in `seamNbhd`. So the open neighbourhood really is the double collar thickened,
not some unrelated open set: it contains the whole two-sided collar minus its two outer faces. -/
theorem dblCollar_mem_seamNbhd (c : EIndex) (p : RP3 × ↥dblParam)
    (hlo : -(1 / 8 : ℝ) < (p.2 : ℝ)) (hhi : (p.2 : ℝ) < 1 / 2) :
    dblCollar c p ∈ seamNbhd := by
  by_cases hv : (0 : ℝ) ≤ (p.2 : ℝ)
  · rw [dblCollar_of_nonneg c hv]
    refine ⟨Sum.inr (c, SKEFTHawking.KummerSeamCollarE.eCollar (p.1, clampE p.2)),
      Or.inr ⟨_, ⟨Set.mem_univ _, ?_⟩, rfl⟩, rfl⟩
    show (1 : ℝ) / 2 < fiberNorm (SKEFTHawking.KummerSeamCollarE.eCollar (p.1, clampE p.2))
    rw [SKEFTHawking.KummerSeamCollarE.fiberNorm_eCollar, clampE_coe, max_eq_left hv]
    linarith
  · rw [dblCollar_of_neg c hv]
    refine ⟨Sum.inl (qCollar c (p.1, clampQ p.2)),
      Or.inl ⟨_, Set.mem_iUnion.mpr ⟨c, qCollar_mem_qOpenCollarSet c _ ?_⟩, rfl⟩, rfl⟩
    show (clampQ p.2 : ℝ) < 5 / 8
    rw [clampQ_coe, min_eq_left (le_of_not_ge hv)]
    linarith

/-! ## §5. The three chart families form an OPEN COVER of `K3` -/

/-- **THE WELD ATLAS'S THREE FAMILIES COVER `K3` BY OPEN SETS.**

* the Q-interior family (chart family 2/3, `KummerWeldQInterior.isOpenEmbedding_qInteriorPiece`),
* the E-interior family (chart family 1/3, `KummerWeldOpenPieces.isOpenEmbedding_eInteriorCopy`),
* the open seam neighbourhood (chart family 3/3, this module).

Each is open and their union is everything. This is exactly the covering condition a
`ChartedSpace (𝓡 4) KummerK3` needs; the residual is the *chart maps* on the third family (the
transport of the `ℝP³` atlas across the double collar) and the transition classes. -/
theorem isOpen_cover_three_families :
    IsOpen (Set.range SKEFTHawking.KummerWeldQInterior.qInteriorPiece)
      ∧ IsOpen (weldMk '' (Sum.inr ''
          ((Set.univ : Set EIndex) ×ˢ SKEFTHawking.KummerWeldOpenPieces.interiorE)))
      ∧ IsOpen seamNbhd
      ∧ Set.range SKEFTHawking.KummerWeldQInterior.qInteriorPiece
          ∪ weldMk '' (Sum.inr ''
              ((Set.univ : Set EIndex) ×ˢ SKEFTHawking.KummerWeldOpenPieces.interiorE))
          ∪ seamNbhd = Set.univ := by
  refine ⟨SKEFTHawking.KummerWeldQInterior.isOpenEmbedding_qInteriorPiece.isOpen_range,
    SKEFTHawking.KummerWeldOpenPieces.isOpen_eInteriorImage, isOpen_seamNbhd, ?_⟩
  refine Set.eq_univ_of_univ_subset ?_
  rw [← SKEFTHawking.KummerWeldQInterior.qInterior_union_eInterior_union_seam]
  exact Set.union_subset_union_right _ seam_subset_seamNbhd

end

end SKEFTHawking.KummerSeamOpenNbhd
