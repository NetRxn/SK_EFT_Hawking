/-
# Phase 5q.H — the puncture Mayer–Vietoris: `H₂(Q;ℤ) ≅ ℤ⁶` and the K7 `b₂ = 22` window,
# UNCONDITIONAL

The last three hypotheses of the landed `KummerQuotientH2Solve` window — the degree-1/2
injectivity of `T⁴° ↪ T⁴` and the identification `H₂(T⁴°;ℤ) ≅ ℤ⁶` — discharged by the puncture
Mayer–Vietoris on `T⁴`:

* the outward chart flow (`KummerPunctureFlow.scaleMap`), dite-glued over the sixteen disjoint
  closed chart balls through the compact chart homeomorphisms (`puncFlow`), deformation-retracts
  the thickened complement `thickA` onto `T⁴°` (`puncIncl_mapInt_bijective`);
* the MV LES of the pair `(thickA, ballsV)` (`SingularMayerVietorisLESInt`) against the piece
  tables — `H₁ = H₂ = 0` for the sixteen `S³`-annuli (`KummerPunctureAnnulus`), `H₊ = 0` for the
  sixteen closed balls — makes `Σ₂` bijective and `Σ₁` injective, so the `thickA`-component
  `H₂(thickA) → H₂(T⁴)` is an isomorphism and `H₁(thickA) → H₁(T⁴)` is injective;
* composing: **`puncture_hX1`/`puncture_hX2`** (the injectivity hypotheses `hX1`/`hX2`) and
  **`punctureH2EquivFin6 : H₂(T⁴°;ℤ) ≅ ℤ⁶`** (the window `hiso`, via the banked
  `torusFourH2EquivFin6`);
* **`qH2EquivInt : H₂(Q;ℤ) ≅ ℤ⁶`** — the K7 `hQ` input, now hypothesis-free — and
  **`kummerK3_b2_window`** — the UNCONDITIONAL `b₂ = 22` rank window: a rank-22 free block
  `ℤ⁶ × ℤ¹⁶` embeds in `H₂(K3;ℤ)` and contains `2·H₂(K3;ℤ)`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerPunctureAnnulus
import SKEFTHawking.KummerK7MVAssembly
import SKEFTHawking.KummerQuotientH2Solve
import SKEFTHawking.KummerHomologyT4H2

namespace SKEFTHawking.KummerPuncturedMV

open SKEFTHawking.KummerK3Base (TorusFour)
open SKEFTHawking.KummerPuncturedTorus
open SKEFTHawking.KummerPunctureFlow (nrm nrm_sq nrm_nonneg lam scaleMap scaleMap_at_one
  scaleMap_of_ge scaleMap_continuousOn lam_at_zero_mul lam_mul_le le_lam_mul lam_one_le
  nrm_scaleMap)
open SKEFTHawking.KummerPunctureBalls
open SKEFTHawking.KummerPunctureAnnulus (ann4_homology_vanish d4_homology_vanish)
open SKEFTHawking.KummerQuotientCovering (PTtop Qtop)
open SKEFTHawking.KummerQuotientH2Solve (inclXC qH2EquivOfWindow kummerK3_b2_window_of_puncture)
open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt Homology.mapInt_comp)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularMayerVietorisLES (ambIncl subIncl)
open SKEFTHawking.SingularMayerVietorisLESInt
open SKEFTHawking.SingularFiniteProdDiscreteHnInt (homologyCongrInt)
open SKEFTHawking.KummerWeld (EIndex eIndex_fixedSet)

noncomputable section

/- The ℝ-arithmetic flow profile defs are consumed ONLY through their banked lemmas below;
making them locally irreducible keeps every unification structural (the friction-catalog rule —
otherwise `isDefEq` dives into the `max/min/sqrt` instance towers and hits the heartbeat wall). -/
attribute [local irreducible] SKEFTHawking.KummerPunctureFlow.scaleMap
  SKEFTHawking.KummerPunctureFlow.lam SKEFTHawking.KummerPunctureFlow.nrm

/-! ## §1. Chart-norm conversions and `scaleMap` on the closed ball -/

theorem nrm_le_half_of_D4 {t : ℝ × ℝ × ℝ × ℝ} (ht : t ∈ D4) : nrm t ≤ 1 / 2 := by
  have h1 : nrm t ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    rw [nrm_sq]
    norm_num
    exact ht
  have h2 := abs_le_of_sq_le_sq (by norm_num) h1
  rwa [abs_of_nonneg (nrm_nonneg t)] at h2

theorem quarter_le_nrm {t : ℝ × ℝ × ℝ × ℝ} (h : 1 / 16 ≤ sqNorm t) : 1 / 4 ≤ nrm t := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 : nrm t ^ 2 < (1 / 4 : ℝ) ^ 2 := by
    have := nrm_nonneg t
    nlinarith
  rw [nrm_sq] at h1
  norm_num at h1
  linarith

/-- `scaleMap` preserves the closed chart ball (`s ∈ [0,1]`): the scaled norm is
`≤ max(‖t‖, ρ) ≤ ρ`. -/
theorem scaleMap_mem_D4 {s : ℝ} (hs : 0 ≤ s) {t : ℝ × ℝ × ℝ × ℝ} (ht : t ∈ D4) :
    scaleMap s t ∈ D4 := by
  have h1 : nrm (scaleMap s t) ≤ max (nrm t) (1 / 2) := by
    rw [nrm_scaleMap]
    exact lam_mul_le hs (nrm_nonneg t)
  have h2 : nrm (scaleMap s t) ≤ 1 / 2 :=
    le_trans h1 (max_le (nrm_le_half_of_D4 ht) le_rfl)
  rw [D4, Set.mem_setOf_eq, ← nrm_sq]
  nlinarith [nrm_nonneg (scaleMap s t)]

/-- The flow never shrinks the chart norm. -/
theorem nrm_le_nrm_scaleMap (s : ℝ) (t : ℝ × ℝ × ℝ × ℝ) : nrm t ≤ nrm (scaleMap s t) := by
  rw [nrm_scaleMap]
  exact le_lam_mul (nrm_nonneg t)

/-- At `s = 0` the collar norms land exactly on the sphere radius. -/
theorem nrm_scaleMap_zero {t : ℝ × ℝ × ℝ × ℝ} (h1 : 1 / 4 ≤ nrm t) (h2 : nrm t ≤ 1 / 2) :
    nrm (scaleMap 0 t) = 1 / 2 := by
  rw [nrm_scaleMap]
  exact lam_at_zero_mul h1 h2

/-! ## §2. The glued outward flow `puncFlow` -/

open Classical in
/-- **The glued outward chart flow** `T⁴ × [0,1] → T⁴`: on each closed chart ball, the
`scaleMap`-flow through the compact chart homeomorphism; the identity elsewhere. Well-defined
because the sixteen closed balls are pairwise disjoint. -/
def puncFlow (p : TorusFour × unitInterval) : TorusFour :=
  if h : ∃ c, c ∈ fixedSet ∧ p.1 ∈ closedBallT c then
    centeredChartParam h.choose
      (scaleMap (p.2 : ℝ) ((ballHomeoT h.choose).symm ⟨p.1, h.choose_spec.2⟩).1)
  else p.1

/-- The piece formula is center-independent (proof-irrelevant in the membership). -/
theorem pieceMap_congr {x c c' : TorusFour} (h : c = c') (hx : x ∈ closedBallT c)
    (hx' : x ∈ closedBallT c') (s : ℝ) :
    centeredChartParam c (scaleMap s ((ballHomeoT c).symm ⟨x, hx⟩).1)
      = centeredChartParam c' (scaleMap s ((ballHomeoT c').symm ⟨x, hx'⟩).1) := by
  subst h
  rfl

/-- On a closed chart ball the glued flow is the chart-scale flow of THAT ball. -/
theorem puncFlow_eq_piece {x c : TorusFour} (hc : c ∈ fixedSet) (hx : x ∈ closedBallT c)
    (s : unitInterval) :
    puncFlow (x, s)
      = centeredChartParam c (scaleMap (s : ℝ) ((ballHomeoT c).symm ⟨x, hx⟩).1) := by
  have hex : ∃ c', c' ∈ fixedSet ∧ x ∈ closedBallT c' := ⟨c, hc, hx⟩
  rw [puncFlow, dif_pos hex]
  exact pieceMap_congr
    (eq_center_of_mem_closedBallT hex.choose_spec.1 hc hex.choose_spec.2 hx)
    hex.choose_spec.2 hx _

/-- Away from every closed chart ball the glued flow is the identity. -/
theorem puncFlow_of_not_mem {x : TorusFour} (hx : ∀ c ∈ fixedSet, x ∉ closedBallT c)
    (s : unitInterval) : puncFlow (x, s) = x := by
  rw [puncFlow, dif_neg]
  rintro ⟨c, hc, hxc⟩
  exact hx c hc hxc

/-- **`puncFlow` at time `1` is the identity.** -/
theorem puncFlow_one (x : TorusFour) : puncFlow (x, 1) = x := by
  by_cases hex : ∃ c, c ∈ fixedSet ∧ x ∈ closedBallT c
  · obtain ⟨c, hc, hx⟩ := hex
    rw [puncFlow_eq_piece hc hx]
    have h1 : scaleMap (((1 : unitInterval)) : ℝ) ((ballHomeoT c).symm ⟨x, hx⟩).1
        = ((ballHomeoT c).symm ⟨x, hx⟩).1 := scaleMap_at_one
    rw [h1]
    exact ballHomeoT_symm_spec c ⟨x, hx⟩
  · exact puncFlow_of_not_mem (fun c hc hxc => hex ⟨c, hc, hxc⟩) 1

/-- A `thickA`-point of a closed chart ball has chart norm `≥ ρ/2`. -/
theorem coord_norm_ge_of_thickA {x c : TorusFour} (hc : c ∈ fixedSet) (hxA : x ∈ thickA)
    (hx : x ∈ closedBallT c) : 1 / 16 ≤ sqNorm ((ballHomeoT c).symm ⟨x, hx⟩).1 := by
  by_contra h
  rw [not_le] at h
  have hmem : x ∈ halfBall c := by
    have h2 := (chart_mem_halfBall_iff c ((ballHomeoT c).symm ⟨x, hx⟩).2).mpr h
    rwa [ballHomeoT_symm_spec] at h2
  exact (mem_thickA_iff.mp hxA) c hc hmem

/-- **`puncFlow` preserves `thickA`** — the flow only moves chart norms outward. -/
theorem puncFlow_mem_thickA {x : TorusFour} (hxA : x ∈ thickA) (s : unitInterval) :
    puncFlow (x, s) ∈ thickA := by
  by_cases hex : ∃ c, c ∈ fixedSet ∧ x ∈ closedBallT c
  · obtain ⟨c, hc, hx⟩ := hex
    rw [puncFlow_eq_piece hc hx]
    set t := ((ballHomeoT c).symm ⟨x, hx⟩).1 with hxt
    have ht : t ∈ D4 := ((ballHomeoT c).symm ⟨x, hx⟩).2
    have hsD : scaleMap (s : ℝ) t ∈ D4 := scaleMap_mem_D4 s.2.1 ht
    rw [mem_thickA_iff]
    intro c' hc' hmem
    by_cases hcc : c' = c
    · subst hcc
      have h1 : sqNorm (scaleMap (s : ℝ) t) < 1 / 16 :=
        (chart_mem_halfBall_iff c' hsD).mp hmem
      have h2 : 1 / 4 ≤ nrm t := quarter_le_nrm (coord_norm_ge_of_thickA hc' hxA hx)
      have h3 : nrm t ≤ nrm (scaleMap (s : ℝ) t) := nrm_le_nrm_scaleMap _ t
      have h4 : 1 / 16 ≤ sqNorm (scaleMap (s : ℝ) t) := by
        rw [← nrm_sq]
        nlinarith
      linarith
    · exact not_mem_chartBall_of_ne hc hc' (fun h => hcc h.symm)
        ⟨scaleMap (s : ℝ) t, hsD, rfl⟩ (halfBall_subset_chartBall c' hmem)
  · rw [puncFlow_of_not_mem (fun c hc hxc => hex ⟨c, hc, hxc⟩) s]
    exact hxA

/-- **`puncFlow` at time `0` lands in `T⁴°`** — collar points are pushed onto the chart
spheres. -/
theorem puncFlow_zero_mem_punctured {x : TorusFour} (hxA : x ∈ thickA) :
    puncFlow (x, 0) ∈ puncturedTorus := by
  by_cases hex : ∃ c, c ∈ fixedSet ∧ x ∈ closedBallT c
  · obtain ⟨c, hc, hx⟩ := hex
    rw [puncFlow_eq_piece hc hx]
    set t := ((ballHomeoT c).symm ⟨x, hx⟩).1 with hxt
    have ht : t ∈ D4 := ((ballHomeoT c).symm ⟨x, hx⟩).2
    have h1 : 1 / 4 ≤ nrm t := quarter_le_nrm (coord_norm_ge_of_thickA hc hxA hx)
    have h2 : nrm t ≤ 1 / 2 := nrm_le_half_of_D4 ht
    have h3 : nrm (scaleMap (((0 : unitInterval)) : ℝ) t) = 1 / 2 := nrm_scaleMap_zero h1 h2
    have h4 : sqNorm (scaleMap (((0 : unitInterval)) : ℝ) t) = excisionRadius ^ 2 := by
      rw [← nrm_sq, h3]
      norm_num [excisionRadius]
    exact sphere_subset_puncturedTorus hc ⟨scaleMap (((0 : unitInterval)) : ℝ) t, h4, rfl⟩
  · rw [puncFlow_of_not_mem (fun c hc hxc => hex ⟨c, hc, hxc⟩) 0]
    rw [mem_puncturedTorus_iff]
    intro c hc hxc
    exact hex ⟨c, hc, chartBall_subset_closedBallT c hxc⟩

/-- **`puncFlow` fixes `T⁴°` pointwise at every time** — punctured-torus points of a closed
ball sit on the chart sphere, where the flow is stationary. -/
theorem puncFlow_of_punctured {x : TorusFour} (hxP : x ∈ puncturedTorus) (s : unitInterval) :
    puncFlow (x, s) = x := by
  by_cases hex : ∃ c, c ∈ fixedSet ∧ x ∈ closedBallT c
  · obtain ⟨c, hc, hx⟩ := hex
    rw [puncFlow_eq_piece hc hx]
    set t := ((ballHomeoT c).symm ⟨x, hx⟩).1 with hxt
    have ht : t ∈ D4 := ((ballHomeoT c).symm ⟨x, hx⟩).2
    have hnb : ¬(sqNorm t < 1 / 4) := by
      intro hlt
      have h2 := (chart_mem_chartBall_iff c ht).mpr hlt
      rw [ballHomeoT_symm_spec] at h2
      exact (mem_puncturedTorus_iff.mp hxP) c hc h2
    have hge : 1 / 2 ≤ nrm t := by
      have heq : sqNorm t = 1 / 4 := le_antisymm ht (not_lt.mp hnb)
      by_contra hlt
      rw [not_le] at hlt
      have := nrm_nonneg t
      have h3 : nrm t ^ 2 < (1 / 2 : ℝ) ^ 2 := by nlinarith
      rw [nrm_sq, heq] at h3
      norm_num at h3
    have h5 : scaleMap ((s : ℝ)) t = t := scaleMap_of_ge s.2.2 hge
    rw [h5]
    exact ballHomeoT_symm_spec c ⟨x, hx⟩
  · exact puncFlow_of_not_mem (fun c hc hxc => hex ⟨c, hc, hxc⟩) s

/-! ## §3. Continuity of the glued flow (finite closed-cover paste) -/

/-- The closed pieces of the paste: the sixteen closed chart balls and `T⁴°` (times the
interval). -/
def flowPiece : Option EIndex → Set (TorusFour × unitInterval)
  | none => puncturedTorus ×ˢ (Set.univ : Set unitInterval)
  | some c => closedBallT c.1 ×ˢ (Set.univ : Set unitInterval)

theorem flowPiece_isClosed (i : Option EIndex) : IsClosed (flowPiece i) := by
  cases i with
  | none => exact (isOpen_excisedBalls.isClosed_compl).prod isClosed_univ
  | some c => exact ((isCompact_closedBallT c.1).isClosed).prod isClosed_univ

theorem flowPiece_cover : (⋃ i : Option EIndex, flowPiece i) = Set.univ := by
  refine Set.eq_univ_of_forall fun p => ?_
  rw [Set.mem_iUnion]
  by_cases hex : ∃ c, c ∈ fixedSet ∧ p.1 ∈ closedBallT c
  · obtain ⟨c, hc, hx⟩ := hex
    exact ⟨some ⟨c, (mem_fixedFinset c).mpr hc⟩, hx, Set.mem_univ _⟩
  · refine ⟨none, ?_, Set.mem_univ _⟩
    rw [mem_puncturedTorus_iff]
    intro c hc hxc
    exact hex ⟨c, hc, chartBall_subset_closedBallT c hxc⟩

/-- The `scaleMap` flow is jointly continuous on `[0,1] × ℝ⁴` (subtype form of the banked
`scaleMap_continuousOn`). -/
theorem continuous_scaleMapUnit :
    Continuous fun q : unitInterval × (ℝ × ℝ × ℝ × ℝ) => scaleMap ((q.1 : ℝ)) q.2 :=
  scaleMap_continuousOn.comp_continuous
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    fun q => ⟨q.1.2, Set.mem_univ _⟩

/-- **Continuity of the glued flow** — pasted over the finite closed cover; each ball piece is
the composite of the compact chart homeomorphism, the jointly-continuous `scaleMap`, and the
chart. -/
theorem continuous_puncFlow : Continuous puncFlow := by
  refine LocallyFinite.continuous (f := flowPiece) (locallyFinite_of_finite _)
    flowPiece_cover flowPiece_isClosed ?_
  intro i
  cases i with
  | none =>
    refine (continuous_fst.continuousOn).congr ?_
    intro p hp
    exact puncFlow_of_punctured hp.1 p.2
  | some c =>
    rw [continuousOn_iff_continuous_restrict]
    have hmap1 : Continuous fun q : ↥(flowPiece (some c)) =>
        (⟨q.1.1, q.2.1⟩ : ↥(closedBallT c.1)) :=
      ((continuous_fst.comp continuous_subtype_val)).subtype_mk fun q => q.2.1
    have hcoord : Continuous fun q : ↥(flowPiece (some c)) =>
        ((ballHomeoT c.1).symm (⟨q.1.1, q.2.1⟩ : ↥(closedBallT c.1))).1 :=
      continuous_subtype_val.comp ((ballHomeoT c.1).symm.continuous.comp hmap1)
    have htime : Continuous fun q : ↥(flowPiece (some c)) => ((q.1.2 : unitInterval) : ℝ) :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)
    have hscale : Continuous fun q : ↥(flowPiece (some c)) =>
        scaleMap ((q.1.2 : unitInterval) : ℝ)
          ((ballHomeoT c.1).symm (⟨q.1.1, q.2.1⟩ : ↥(closedBallT c.1))).1 := by
      have hpair : Continuous fun q : ↥(flowPiece (some c)) =>
          ((q.1.2 : unitInterval),
            ((ballHomeoT c.1).symm (⟨q.1.1, q.2.1⟩ : ↥(closedBallT c.1))).1) :=
        (continuous_snd.comp continuous_subtype_val).prodMk hcoord
      exact continuous_scaleMapUnit.comp hpair
    have hcont : Continuous fun q : ↥(flowPiece (some c)) =>
        centeredChartParam c.1 (scaleMap ((q.1.2 : unitInterval) : ℝ)
          ((ballHomeoT c.1).symm (⟨q.1.1, q.2.1⟩ : ↥(closedBallT c.1))).1) :=
      (continuous_centeredChartParam c.1).comp hscale
    exact hcont.congr fun q =>
      (puncFlow_eq_piece (eIndex_fixedSet c) q.2.1 q.1.2).symm

/-! ## §4. `T⁴° ↪ thickA` is a homotopy equivalence -/

/-- The inclusion `T⁴° ↪ thickA` as a continuous map. -/
def puncInclC : C(↑PTtop, ↑(sub (X := TopCat.of TorusFour) thickA)) :=
  ⟨fun x => ⟨x.1, puncturedTorus_subset_thickA x.2⟩,
    Continuous.subtype_mk continuous_subtype_val _⟩

/-- The retraction `thickA → T⁴°` (the `s = 0` glued flow). -/
def puncRetrC : C(↑(sub (X := TopCat.of TorusFour) thickA), ↑PTtop) :=
  ⟨fun x => ⟨puncFlow (x.1, 0), puncFlow_zero_mem_punctured x.2⟩,
    (continuous_puncFlow.comp (continuous_subtype_val.prodMk continuous_const)).subtype_mk _⟩

/-- The deformation `thickA × [0,1] → thickA` (the glued flow). -/
def thickHtpyC :
    C(↑(sub (X := TopCat.of TorusFour) thickA) × unitInterval,
      ↑(sub (X := TopCat.of TorusFour) thickA)) :=
  ⟨fun p => ⟨puncFlow (p.1.1, p.2), puncFlow_mem_thickA p.1.2 p.2⟩,
    (continuous_puncFlow.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk _⟩

/-- The trivial homotopy on `T⁴°`. -/
def puncTrivHtpyC : C(↑PTtop × unitInterval, ↑PTtop) := ⟨fun p => p.1, continuous_fst⟩

/-- **The thickening is a homotopy equivalence**: `Hₙ₊₁(T⁴°) ≅ Hₙ₊₁(thickA)` via the
inclusion. -/
theorem puncIncl_mapInt_bijective (n : ℕ) :
    Function.Bijective (Homology.mapInt puncInclC (n + 1)) := by
  refine SKEFTHawking.SingularFunctorialityInt.Homology.mapInt_bijective_of_homotopyEquiv
    puncInclC puncRetrC puncTrivHtpyC ?_ ?_ thickHtpyC ?_ ?_ n
  · refine ContinuousMap.ext fun x => Subtype.ext ?_
    exact (puncFlow_of_punctured x.2 0).symm
  · exact ContinuousMap.ext fun _ => rfl
  · exact ContinuousMap.ext fun x => Subtype.ext rfl
  · refine ContinuousMap.ext fun x => Subtype.ext ?_
    exact puncFlow_one _

/-! ## §5. The 16-fold piece homology tables -/

/-- `Hₙ(thickA ∩ ballsV;ℤ) ≅ (EIndex → Hₙ(Ann⁴;ℤ))` — the sixteen annuli split. -/
def interHnEquiv (n : ℕ) :
    Homology (sub (X := TopCat.of TorusFour) (thickA ∩ ballsV)) n ≃ₗ[ℤ]
      (EIndex → Homology (TopCat.of ↥ann4) n) :=
  (homologyCongrInt (X := sub (X := TopCat.of TorusFour) (thickA ∩ ballsV))
      (Y := TopCat.of (EIndex × ↥ann4)) interSplitHomeo.symm n).trans
    (SKEFTHawking.KummerK7MVAssembly.eIndexProdHnEquivIntGen (TopCat.of ↥ann4) n)

/-- `Hₙ(ballsV;ℤ) ≅ (EIndex → Hₙ(D⁴;ℤ))` — the sixteen closed balls split. -/
def ballsVHnEquiv (n : ℕ) :
    Homology (sub (X := TopCat.of TorusFour) ballsV) n ≃ₗ[ℤ]
      (EIndex → Homology (TopCat.of ↥D4) n) :=
  (homologyCongrInt (X := sub (X := TopCat.of TorusFour) ballsV)
      (Y := TopCat.of (EIndex × ↥D4)) ballsVSplitHomeo.symm n).trans
    (SKEFTHawking.KummerK7MVAssembly.eIndexProdHnEquivIntGen (TopCat.of ↥D4) n)

/-- **`H₁(thickA ∩ ballsV;ℤ) = 0`** — `H₁(S³) = 0` on each of the sixteen annuli. -/
theorem interH1_eq_zero (x : Homology (sub (X := TopCat.of TorusFour) (thickA ∩ ballsV)) 1) :
    x = 0 :=
  (LinearEquiv.map_eq_zero_iff (interHnEquiv 1)).mp
    (funext fun _ => ann4_homology_vanish (by norm_num) (by norm_num) _)

/-- **`H₂(thickA ∩ ballsV;ℤ) = 0`** — `H₂(S³) = 0` on each of the sixteen annuli. -/
theorem interH2_eq_zero (x : Homology (sub (X := TopCat.of TorusFour) (thickA ∩ ballsV)) 2) :
    x = 0 :=
  (LinearEquiv.map_eq_zero_iff (interHnEquiv 2)).mp
    (funext fun _ => ann4_homology_vanish (by norm_num) (by norm_num) _)

/-- **`H₊(ballsV;ℤ) = 0`** — the sixteen closed balls are acyclic. -/
theorem ballsV_homology_eq_zero (k : ℕ)
    (x : Homology (sub (X := TopCat.of TorusFour) ballsV) (k + 1)) : x = 0 :=
  (LinearEquiv.map_eq_zero_iff (ballsVHnEquiv (k + 1))).mp
    (funext fun _ => d4_homology_vanish k _)

/-! ## §6. The puncture MV window -/

/-- **`Σ₁` is injective** — `H₁(collar) = 0` kills the incoming diagonal. -/
theorem puncSum1_injective :
    Function.Injective (mvHomSumInt (X := TopCat.of TorusFour) thickA ballsV 1) := by
  intro p q hpq
  have hker : mvHomSumInt (X := TopCat.of TorusFour) thickA ballsV 1 (p - q) = 0 := by
    rw [map_sub, hpq, sub_self]
  obtain ⟨w, hw⟩ :=
    (mv_exact_middleInt (X := TopCat.of TorusFour) thickA ballsV 0 punc_hcov (p - q)).mp hker
  rw [interH1_eq_zero w, map_zero] at hw
  exact sub_eq_zero.mp hw.symm

/-- **`Σ₂` is injective** — `H₂(collar) = 0` kills the incoming diagonal. -/
theorem puncSum2_injective :
    Function.Injective (mvHomSumInt (X := TopCat.of TorusFour) thickA ballsV 2) := by
  intro p q hpq
  have hker : mvHomSumInt (X := TopCat.of TorusFour) thickA ballsV 2 (p - q) = 0 := by
    rw [map_sub, hpq, sub_self]
  obtain ⟨w, hw⟩ :=
    (mv_exact_middleInt (X := TopCat.of TorusFour) thickA ballsV 1 punc_hcov (p - q)).mp hker
  rw [interH2_eq_zero w, map_zero] at hw
  exact sub_eq_zero.mp hw.symm

/-- **`Σ₂` is surjective** — `H₁(collar) = 0` kills the outgoing connecting map. -/
theorem puncSum2_surjective :
    Function.Surjective (mvHomSumInt (X := TopCat.of TorusFour) thickA ballsV 2) := fun x =>
  (mv_exact_ambientInt (X := TopCat.of TorusFour) thickA ballsV 1 punc_hcov x).mp
    (interH1_eq_zero _)

/-- The `thickA`-component of an injective `Σ` is injective. -/
theorem thickIncl_injective {k : ℕ}
    (hSig : Function.Injective (mvHomSumInt (X := TopCat.of TorusFour) thickA ballsV k)) :
    Function.Injective (Homology.mapInt (ambIncl (X := TopCat.of TorusFour) thickA) k) := by
  intro a b hab
  have h : mvHomSumInt (X := TopCat.of TorusFour) thickA ballsV k (a, 0)
      = mvHomSumInt (X := TopCat.of TorusFour) thickA ballsV k (b, 0) := by
    simp only [mvHomSumInt_apply, map_zero, sub_zero]
    exact hab
  exact congrArg Prod.fst (hSig h)

/-- **Every `H₂(T⁴;ℤ)` class comes from `thickA` alone** — the ball side is dead in degree 2. -/
theorem thickIncl2_surjective :
    Function.Surjective (Homology.mapInt (ambIncl (X := TopCat.of TorusFour) thickA) 2) := by
  intro x
  obtain ⟨⟨u, v⟩, h⟩ := puncSum2_surjective x
  rw [mvHomSumInt_apply, ballsV_homology_eq_zero 1 v, map_zero, sub_zero] at h
  exact ⟨u, h⟩

/-! ## §7. The window hypotheses, discharged -/

/-- The inclusion `T⁴° ↪ T⁴` factors through the thickening. -/
theorem inclXC_factor :
    (ambIncl (X := TopCat.of TorusFour) thickA).comp puncInclC = inclXC :=
  ContinuousMap.ext fun _ => rfl

theorem mapInt_inclXC_eq (k : ℕ) :
    Homology.mapInt inclXC k
      = (Homology.mapInt (ambIncl (X := TopCat.of TorusFour) thickA) k).comp
          (Homology.mapInt puncInclC k) := by
  rw [← inclXC_factor]
  exact Homology.mapInt_comp _ _ k

/-- **`hX1` discharged**: `H₁(T⁴°;ℤ) → H₁(T⁴;ℤ)` is injective. -/
theorem puncture_hX1 : Function.Injective (Homology.mapInt inclXC 1) := by
  rw [mapInt_inclXC_eq 1, LinearMap.coe_comp]
  exact (thickIncl_injective puncSum1_injective).comp (puncIncl_mapInt_bijective 0).injective

/-- **`hX2` discharged**: `H₂(T⁴°;ℤ) → H₂(T⁴;ℤ)` is injective. -/
theorem puncture_hX2 : Function.Injective (Homology.mapInt inclXC 2) := by
  rw [mapInt_inclXC_eq 2, LinearMap.coe_comp]
  exact (thickIncl_injective puncSum2_injective).comp (puncIncl_mapInt_bijective 1).injective

/-- **`hiso` discharged**: `H₂(T⁴°;ℤ) ≅ ℤ⁶` — through the thickening, the MV `Σ₂`
isomorphism, and the banked `torusFourH2EquivFin6`. -/
def punctureH2EquivFin6 : Homology PTtop 2 ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  ((LinearEquiv.ofBijective (Homology.mapInt puncInclC 2) (puncIncl_mapInt_bijective 1)).trans
    (LinearEquiv.ofBijective (Homology.mapInt (ambIncl (X := TopCat.of TorusFour) thickA) 2)
      ⟨thickIncl_injective puncSum2_injective, thickIncl2_surjective⟩)).trans
    SKEFTHawking.KummerHomologyT4H2.torusFourH2EquivFin6

/-! ## §8. The finale: `H₂(Q;ℤ) ≅ ℤ⁶` and the `b₂ = 22` window, UNCONDITIONAL -/

/-- **`H₂(Q;ℤ) ≅ ℤ⁶`, hypothesis-free** — the K7 `hQ` input, with the puncture-window
interface discharged by the puncture Mayer–Vietoris. -/
def qH2EquivInt : Homology Qtop 2 ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  qH2EquivOfWindow puncture_hX1 puncture_hX2 punctureH2EquivFin6

/-- **The K7 `b₂ = 22` rank window, UNCONDITIONAL**: a rank-22 free block `ℤ⁶ × ℤ¹⁶` embeds in
`H₂(K3;ℤ)` and contains `2·H₂(K3;ℤ)`. The landed `kummerK3_b2_window_of_qH2` discharged at its
single open input. -/
theorem kummerK3_b2_window :
    ∃ φ : ((Fin 6 → ℤ) × (EIndex → ℤ)) →ₗ[ℤ]
        Homology SKEFTHawking.KummerK7Opener.KummerK3top 2,
      Function.Injective φ ∧ ∀ x, ∃ v, φ v = (2 : ℤ) • x :=
  kummerK3_b2_window_of_puncture puncture_hX1 puncture_hX2 punctureH2EquivFin6

/-! ## §9. The Smith walk, unconditional — the whole conditional chain discharged -/

/-- **`ker(1−τ_*) = 0` on `H₁(T⁴°;ℤ)`, unconditional.** -/
theorem x_H1_fixed_eq_zero (y : Homology PTtop 1)
    (h : Homology.mapInt SKEFTHawking.KummerQuotientCovering.tauC 1 y = y) : y = 0 :=
  SKEFTHawking.KummerQuotientH2Solve.X_H1_fixed_eq_zero puncture_hX1 y h

/-- **`ker(1+τ_*) = 0` on `H₂(T⁴°;ℤ)`, unconditional.** -/
theorem x_H2_anti_eq_zero (y : Homology PTtop 2)
    (h : Homology.mapInt SKEFTHawking.KummerQuotientCovering.tauC 2 y = -y) : y = 0 :=
  SKEFTHawking.KummerQuotientH2Solve.X_H2_anti_eq_zero puncture_hX2 y h

/-- **`H₁(B) ↪ H₁(T⁴°)`, unconditional.** -/
theorem inclBH_one_injective :
    Function.Injective (SKEFTHawking.KummerQuotientSmithSES.inclBH 1) :=
  SKEFTHawking.KummerQuotientH2Solve.inclBH_one_injective puncture_hX1

/-- **`p̄₂ : H₂(T⁴°) → H₂(Q)` is bijective, unconditional** — the covering projection is a
degree-2 homology isomorphism. -/
theorem projH_two_bijective :
    Function.Bijective (SKEFTHawking.KummerQuotientSmithSES.projH 2) :=
  ⟨SKEFTHawking.KummerQuotientH2Solve.projH_two_injective puncture_hX2,
   SKEFTHawking.KummerQuotientH2Solve.projH_two_surjective puncture_hX1⟩

end

end SKEFTHawking.KummerPuncturedMV
