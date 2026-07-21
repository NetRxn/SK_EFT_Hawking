/-
# Phase 5q.H — the puncture Mayer–Vietoris cover: round balls, half-balls, annuli

The set-level geometry of the puncture MV pair on `T⁴` that discharges the
`KummerQuotientH2Solve` window hypotheses:

* `thickA := (⋃₁₆ halfBall)ᶜ` — the thickened punctured torus (complement of the sixteen OPEN
  chart-radius-`ρ/2` balls), a closed set containing `T⁴°` onto which the outward chart flow
  (`KummerPunctureFlow`) deformation-retracts it;
* `ballsV := ⋃₁₆ closedBallT` — the sixteen CLOSED chart-radius-`ρ` balls;
* `punc_hcov` — the interiors cover `T⁴` (the seam is thickened away, so the
  `k7-seam-cover-interior-fails` obstruction does NOT arise);
* `inter_eq` — `thickA ∩ ballsV` is the union of the sixteen closed chart annuli
  `ρ/2 ≤ ‖t‖ ≤ ρ`;
* the compact chart homeomorphisms and the 16-fold splitters
  `ballsVSplitHomeo : EIndex × D⁴ ≃ₜ ballsV`, `interSplitHomeo : EIndex × Ann⁴ ≃ₜ thickA ∩ ballsV`
  (continuous bijections from compact to `T2`, mirroring the K7 `eImageHomeo` pattern).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerShellChart
import SKEFTHawking.KummerPunctureFlow
import SKEFTHawking.KummerWeld

namespace SKEFTHawking.KummerPunctureBalls

open SKEFTHawking.KummerK3Base (TorusFour)
open SKEFTHawking.KummerPuncturedTorus
open SKEFTHawking.KummerPunctureFlow (nrm nrm_sq nrm_nonneg)
open SKEFTHawking.KummerShellChart (toE4 ofE4 norm_sq_toE4 sqNorm_ofE4 continuous_ofE4
  continuous_toE4 ofE4_toE4 toE4_ofE4)
open SKEFTHawking.KummerWeld (EIndex eIndex_fixedSet)

noncomputable section

/-! ## §1. The chart-domain sets: closed ball, open/closed half-balls, closed annulus -/

theorem excisionRadius_sq : excisionRadius ^ 2 = 1 / 4 := by norm_num [excisionRadius]

/-- The closed chart-domain ball `{‖t‖ ≤ ρ}` (`ρ = 1/2`), squared form. -/
def D4 : Set (ℝ × ℝ × ℝ × ℝ) := {t | sqNorm t ≤ 1 / 4}

/-- The open chart-domain half-ball `{‖t‖ < ρ/2}`. -/
def halfD4o : Set (ℝ × ℝ × ℝ × ℝ) := {t | sqNorm t < 1 / 16}

/-- The closed chart-domain half-ball `{‖t‖ ≤ ρ/2}`. -/
def halfD4c : Set (ℝ × ℝ × ℝ × ℝ) := {t | sqNorm t ≤ 1 / 16}

/-- The closed chart-domain annulus `{ρ/2 ≤ ‖t‖ ≤ ρ}`. -/
def ann4 : Set (ℝ × ℝ × ℝ × ℝ) := {t | 1 / 16 ≤ sqNorm t ∧ sqNorm t ≤ 1 / 4}

theorem ann4_subset_D4 : ann4 ⊆ D4 := fun _ ht => ht.2

theorem halfD4o_subset_halfD4c : halfD4o ⊆ halfD4c := fun _ ht => by
  rw [halfD4c, Set.mem_setOf_eq]
  rw [halfD4o, Set.mem_setOf_eq] at ht
  exact le_of_lt ht

/-- The chart is injective on the closed ball `D4` (the banked `centeredChartParam_injOn`,
with the radius squared normalized to `1/4`). -/
theorem injOn_D4 (c : TorusFour) : Set.InjOn (centeredChartParam c) D4 := by
  have h := centeredChartParam_injOn c
  rwa [show {t | sqNorm t ≤ excisionRadius ^ 2} = D4 by
    ext t; simp [D4, excisionRadius_sq]] at h

/-! ## §2. Compactness via the `E⁴` bridge -/

/-- `ofE4` carries the Euclidean closed ball to the chart-domain squared-norm sublevel set. -/
theorem image_ofE4_closedBall (r : ℝ) (hr : 0 ≤ r) :
    ofE4 '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) r
      = {t : ℝ × ℝ × ℝ × ℝ | sqNorm t ≤ r ^ 2} := by
  ext t
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    rw [Set.mem_setOf_eq, sqNorm_ofE4]
    nlinarith [norm_nonneg w, hw]
  · intro ht
    rw [Set.mem_setOf_eq] at ht
    refine ⟨toE4 t, ?_, ofE4_toE4 t⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : ‖toE4 t‖ ^ 2 ≤ r ^ 2 := by rw [norm_sq_toE4]; exact ht
    have h2 := abs_le_of_sq_le_sq hr h1
    rwa [abs_of_nonneg (norm_nonneg _)] at h2

theorem isCompact_D4 : IsCompact D4 := by
  have h : D4 = ofE4 '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) (1 / 2) := by
    rw [image_ofE4_closedBall (1 / 2) (by norm_num)]
    ext t; simp [D4]; norm_num
  rw [h]
  exact (isCompact_closedBall _ _).image continuous_ofE4

theorem isCompact_halfD4c : IsCompact halfD4c := by
  have h : halfD4c = ofE4 '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) (1 / 4) := by
    rw [image_ofE4_closedBall (1 / 4) (by norm_num)]
    ext t; simp [halfD4c]; norm_num
  rw [h]
  exact (isCompact_closedBall _ _).image continuous_ofE4

theorem isClosed_ann4 : IsClosed ann4 :=
  (isClosed_le continuous_const sqNorm_continuous).inter
    (isClosed_le sqNorm_continuous continuous_const)

theorem isCompact_ann4 : IsCompact ann4 :=
  IsCompact.of_isClosed_subset isCompact_D4 isClosed_ann4 ann4_subset_D4

instance : CompactSpace ↥D4 := isCompact_iff_compactSpace.mp isCompact_D4

instance : CompactSpace ↥ann4 :=
  isCompact_iff_compactSpace.mp
    (IsCompact.of_isClosed_subset isCompact_D4 isClosed_ann4 ann4_subset_D4)

/-! ## §3. The `T⁴` pieces: closed balls, half-balls, annuli around the fixed points -/

/-- The closed chart-radius-`ρ` ball at `c`. -/
def closedBallT (c : TorusFour) : Set TorusFour := centeredChartParam c '' D4

/-- The OPEN chart-radius-`ρ/2` ball at `c`. -/
def halfBall (c : TorusFour) : Set TorusFour := centeredChartParam c '' halfD4o

/-- The closed chart-radius-`ρ/2` ball at `c`. -/
def closedHalfBallT (c : TorusFour) : Set TorusFour := centeredChartParam c '' halfD4c

/-- The closed chart annulus `ρ/2 ≤ ‖t‖ ≤ ρ` at `c`. -/
def annPiece (c : TorusFour) : Set TorusFour := centeredChartParam c '' ann4

theorem isOpen_halfBall (c : TorusFour) : IsOpen (halfBall c) :=
  isOpenMap_centeredChartParam c _ (isOpen_lt sqNorm_continuous continuous_const)

theorem isCompact_closedBallT (c : TorusFour) : IsCompact (closedBallT c) :=
  isCompact_D4.image (continuous_centeredChartParam c)

theorem isCompact_closedHalfBallT (c : TorusFour) : IsCompact (closedHalfBallT c) :=
  isCompact_halfD4c.image (continuous_centeredChartParam c)

theorem halfBall_subset_chartBall (c : TorusFour) : halfBall c ⊆ chartBall c :=
  Set.image_mono fun t ht => by
    rw [Set.mem_setOf_eq, excisionRadius_sq]
    rw [halfD4o, Set.mem_setOf_eq] at ht
    linarith

theorem closedHalfBallT_subset_chartBall (c : TorusFour) : closedHalfBallT c ⊆ chartBall c :=
  Set.image_mono fun t ht => by
    rw [Set.mem_setOf_eq, excisionRadius_sq]
    rw [halfD4c, Set.mem_setOf_eq] at ht
    linarith

theorem halfBall_subset_closedHalfBallT (c : TorusFour) : halfBall c ⊆ closedHalfBallT c :=
  Set.image_mono halfD4o_subset_halfD4c

theorem chartBall_subset_closedBallT (c : TorusFour) : chartBall c ⊆ closedBallT c :=
  Set.image_mono fun t ht => by
    rw [Set.mem_setOf_eq, excisionRadius_sq] at ht
    exact le_of_lt ht

theorem annPiece_subset_closedBallT (c : TorusFour) : annPiece c ⊆ closedBallT c :=
  Set.image_mono ann4_subset_D4

/-- Every point of the closed chart ball is within metric distance `1/2` of its center. -/
theorem dist_le_of_mem_closedBallT {c x : TorusFour} (hx : x ∈ closedBallT c) :
    dist x c ≤ 1 / 2 := by
  obtain ⟨t, ht, rfl⟩ := hx
  exact dist_centeredChartParam_le c (by norm_num) (by
    rw [show ((1 : ℝ) / 2) ^ 2 = 1 / 4 by norm_num]; exact ht)

/-! ## §4. Cross-center separation and the chart injectivity across pieces -/

/-- **Chart injectivity across the sixteen pieces**: two closed-ball chart points can only agree
when both the centers and the chart coordinates agree (distinct fixed centers are `≥ 2` apart
while each closed ball has metric radius `≤ 1/2`). -/
theorem chart_inj_across {c c' : TorusFour} (hc : c ∈ fixedSet) (hc' : c' ∈ fixedSet)
    {t t' : ℝ × ℝ × ℝ × ℝ} (ht : t ∈ D4) (ht' : t' ∈ D4)
    (h : centeredChartParam c t = centeredChartParam c' t') : c = c' ∧ t = t' := by
  by_cases hcc : c = c'
  · subst hcc
    exact ⟨rfl, injOn_D4 c ht ht' h⟩
  · exfalso
    have h1 : dist (centeredChartParam c t) c ≤ 1 / 2 :=
      dist_le_of_mem_closedBallT ⟨t, ht, rfl⟩
    have h2 : dist (centeredChartParam c' t') c' ≤ 1 / 2 :=
      dist_le_of_mem_closedBallT ⟨t', ht', rfl⟩
    have hsep : (2 : ℝ) ≤ dist c c' := fixedSet_dist_ge hc hc' hcc
    have htri : dist c c' ≤ dist c (centeredChartParam c t) + dist (centeredChartParam c' t') c' := by
      calc dist c c' ≤ dist c (centeredChartParam c t) + dist (centeredChartParam c t) c' :=
            dist_triangle _ _ _
        _ = dist c (centeredChartParam c t) + dist (centeredChartParam c' t') c' := by rw [h]
    rw [dist_comm c (centeredChartParam c t)] at htri
    linarith

/-- A point of one closed chart ball belongs to no OTHER center's open chart ball. -/
theorem not_mem_chartBall_of_ne {c c' x : TorusFour} (hc : c ∈ fixedSet) (hc' : c' ∈ fixedSet)
    (hne : c ≠ c') (hx : x ∈ closedBallT c) : x ∉ chartBall c' := by
  intro hx'
  have h1 : dist x c ≤ 1 / 2 := dist_le_of_mem_closedBallT hx
  have h2 : dist x c' < 1 / 2 := by
    have := chartBall_subset_metricBall c' hx'
    rwa [Metric.mem_ball, show excisionRadius = (1 : ℝ) / 2 from rfl] at this
  have hsep : (2 : ℝ) ≤ dist c c' := fixedSet_dist_ge hc hc' hne
  have htri : dist c c' ≤ dist c x + dist x c' := dist_triangle _ _ _
  rw [dist_comm c x] at htri
  linarith

/-- Two distinct fixed centers cannot share a closed-ball point. -/
theorem eq_center_of_mem_closedBallT {c c' x : TorusFour} (hc : c ∈ fixedSet)
    (hc' : c' ∈ fixedSet) (hx : x ∈ closedBallT c) (hx' : x ∈ closedBallT c') : c = c' := by
  obtain ⟨t, ht, rfl⟩ := hx
  obtain ⟨t', ht', heq⟩ := hx'
  exact (chart_inj_across hc hc' ht ht' heq.symm).1

/-! ## §5. Membership certificates through the chart (via closed-ball injectivity) -/

/-- For a closed-ball coordinate, half-ball membership reads off the coordinate norm. -/
theorem chart_mem_halfBall_iff (c : TorusFour) {t : ℝ × ℝ × ℝ × ℝ} (ht : t ∈ D4) :
    centeredChartParam c t ∈ halfBall c ↔ sqNorm t < 1 / 16 := by
  constructor
  · rintro ⟨s, hs, heq⟩
    rw [halfD4o, Set.mem_setOf_eq] at hs
    have hsD : s ∈ D4 := by rw [D4, Set.mem_setOf_eq]; linarith
    have := injOn_D4 c hsD ht heq
    rw [← this]
    exact hs
  · intro h
    exact ⟨t, h, rfl⟩

/-- For a closed-ball coordinate, open-chart-ball membership reads off the coordinate norm. -/
theorem chart_mem_chartBall_iff (c : TorusFour) {t : ℝ × ℝ × ℝ × ℝ} (ht : t ∈ D4) :
    centeredChartParam c t ∈ chartBall c ↔ sqNorm t < 1 / 4 := by
  constructor
  · rintro ⟨s, hs, heq⟩
    rw [Set.mem_setOf_eq, excisionRadius_sq] at hs
    have hsD : s ∈ D4 := by rw [D4, Set.mem_setOf_eq]; exact le_of_lt hs
    have := injOn_D4 c hsD ht heq
    rw [← this]
    exact hs
  · intro h
    exact ⟨t, by rw [Set.mem_setOf_eq, excisionRadius_sq]; exact h, rfl⟩

/-! ## §6. The MV pair `thickA`, `ballsV` and the interior cover -/

/-- **The `A`-side of the puncture MV pair**: the complement of the sixteen open half-balls —
the thickened punctured torus. -/
def thickA : Set TorusFour := (⋃ c ∈ fixedSet, halfBall c)ᶜ

/-- **The `B`-side of the puncture MV pair**: the sixteen closed chart balls. -/
def ballsV : Set TorusFour := ⋃ c ∈ fixedSet, closedBallT c

theorem fixedSet_finite : fixedSet.Finite :=
  Set.Finite.ofFinset fixedFinset fun x => mem_fixedFinset x

theorem isClosed_thickA : IsClosed thickA :=
  (isOpen_biUnion fun c _ => isOpen_halfBall c).isClosed_compl

theorem isClosed_ballsV : IsClosed ballsV :=
  Set.Finite.isClosed_biUnion fixedSet_finite fun c _ => (isCompact_closedBallT c).isClosed

theorem mem_thickA_iff {x : TorusFour} : x ∈ thickA ↔ ∀ c ∈ fixedSet, x ∉ halfBall c := by
  simp only [thickA, Set.mem_compl_iff, Set.mem_iUnion, exists_prop, not_exists, not_and]

theorem mem_puncturedTorus_iff {x : TorusFour} :
    x ∈ puncturedTorus ↔ ∀ c ∈ fixedSet, x ∉ chartBall c := by
  simp only [puncturedTorus, excisedBalls, Set.mem_compl_iff, Set.mem_iUnion, exists_prop,
    not_exists, not_and]

/-- `T⁴° ⊆ thickA` — excising the smaller half-balls removes less. -/
theorem puncturedTorus_subset_thickA : puncturedTorus ⊆ thickA := fun x hx => by
  rw [mem_thickA_iff]
  intro c hc hxc
  exact (mem_puncturedTorus_iff.mp hx) c hc (halfBall_subset_chartBall c hxc)

theorem excisedBalls_subset_ballsV : excisedBalls ⊆ ballsV := fun x hx => by
  rw [excisedBalls] at hx
  obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_biUnion hc (chartBall_subset_closedBallT c hxc)

theorem isOpen_excisedBalls : IsOpen excisedBalls :=
  isOpen_biUnion fun c _ => isOpen_chartBall c

/-- **The interior cover** `int(thickA) ∪ int(ballsV) = T⁴` — the MV hypothesis. The seam is
thickened away (the open complement of the sixteen CLOSED half-balls sits inside `thickA`), so
the `k7-seam-cover-interior-fails` obstruction does not arise. -/
theorem punc_hcov :
    (⋃ U ∈ ({thickA, ballsV} : Set (Set TorusFour)), interior U) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  rw [Set.mem_iUnion₂]
  by_cases hx : x ∈ excisedBalls
  · exact ⟨ballsV, Or.inr rfl,
      interior_maximal excisedBalls_subset_ballsV isOpen_excisedBalls hx⟩
  · refine ⟨thickA, Or.inl rfl, ?_⟩
    have hW : IsOpen (⋃ c ∈ fixedSet, closedHalfBallT c)ᶜ :=
      (Set.Finite.isClosed_biUnion fixedSet_finite
        fun c _ => (isCompact_closedHalfBallT c).isClosed).isOpen_compl
    have hWsub : (⋃ c ∈ fixedSet, closedHalfBallT c)ᶜ ⊆ thickA := by
      intro y hy
      rw [mem_thickA_iff]
      intro c hc hyc
      exact hy (Set.mem_biUnion hc (halfBall_subset_closedHalfBallT c hyc))
    refine interior_maximal hWsub hW ?_
    intro hmem
    obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp hmem
    exact hx (Set.mem_biUnion hc (closedHalfBallT_subset_chartBall c hxc))

/-! ## §7. The intersection is the sixteen closed annuli -/

theorem annPiece_subset_inter {c : TorusFour} (hc : c ∈ fixedSet) :
    annPiece c ⊆ thickA ∩ ballsV := by
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨?_, Set.mem_biUnion hc ⟨t, ann4_subset_D4 ht, rfl⟩⟩
  rw [mem_thickA_iff]
  intro c' hc' hmem
  by_cases hcc : c' = c
  · subst hcc
    have := (chart_mem_halfBall_iff c' (ann4_subset_D4 ht)).mp hmem
    have h16 := ht.1
    linarith
  · exact not_mem_chartBall_of_ne hc hc' (fun h => hcc h.symm) ⟨t, ann4_subset_D4 ht, rfl⟩
      (halfBall_subset_chartBall c' hmem)

/-- Decomposing a point of `thickA ∩ ballsV`: it is a chart-annulus point of some fixed center. -/
theorem inter_elim {x : TorusFour} (hx : x ∈ thickA ∩ ballsV) :
    ∃ c ∈ fixedSet, ∃ t ∈ ann4, centeredChartParam c t = x := by
  obtain ⟨hxA, hxV⟩ := hx
  obtain ⟨c, hc, t, ht, rfl⟩ := Set.mem_iUnion₂.mp hxV
  refine ⟨c, hc, t, ⟨?_, ht⟩, rfl⟩
  by_contra hlt
  rw [not_le] at hlt
  exact (mem_thickA_iff.mp hxA) c hc ((chart_mem_halfBall_iff c ht).mpr hlt)

/-- **`thickA ∩ ballsV` is the disjoint union of the sixteen closed chart annuli.** -/
theorem inter_eq : thickA ∩ ballsV = ⋃ c ∈ fixedSet, annPiece c := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨c, hc, t, ht, rfl⟩ := inter_elim hx
    exact Set.mem_biUnion hc ⟨t, ht, rfl⟩
  · intro x hx
    obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp hx
    exact annPiece_subset_inter hc hxc

/-! ## §8. The compact chart homeomorphisms and the 16-fold splitters -/

/-- The centered chart is jointly continuous in the center and the coordinate. -/
theorem continuous_centeredChartParamJoint :
    Continuous fun p : TorusFour × (ℝ × ℝ × ℝ × ℝ) => centeredChartParam p.1 p.2 := by
  unfold centeredChartParam
  fun_prop

/-- The closed chart ball, parametrized: `D⁴ ≃ closedBallT c`. -/
def ballEquivT (c : TorusFour) : ↥D4 ≃ ↥(closedBallT c) :=
  Equiv.ofBijective (fun t => ⟨centeredChartParam c t.1, ⟨t.1, t.2, rfl⟩⟩)
    ⟨fun a b h => Subtype.ext (injOn_D4 c a.2 b.2 (Subtype.ext_iff.mp h)),
     fun y => by
      obtain ⟨t, ht, hy⟩ := y.2
      exact ⟨⟨t, ht⟩, Subtype.ext hy⟩⟩

/-- **The compact chart homeomorphism** `D⁴ ≃ₜ closedBallT c` — continuous bijection from a
compact space to a `T2` space. -/
def ballHomeoT (c : TorusFour) : ↥D4 ≃ₜ ↥(closedBallT c) :=
  Continuous.homeoOfEquivCompactToT2 (f := ballEquivT c)
    (((continuous_centeredChartParam c).comp continuous_subtype_val).subtype_mk _)

/-- The inverse chart homeomorphism recovers the chart presentation. -/
theorem ballHomeoT_symm_spec (c : TorusFour) (x : ↥(closedBallT c)) :
    centeredChartParam c ((ballHomeoT c).symm x).1 = x.1 :=
  congrArg Subtype.val ((ballHomeoT c).apply_symm_apply x)

/-- The inverse chart coordinate is unique. -/
theorem ballHomeoT_symm_eq (c : TorusFour) {t : ℝ × ℝ × ℝ × ℝ} (ht : t ∈ D4)
    {x : ↥(closedBallT c)} (hx : centeredChartParam c t = x.1) :
    ((ballHomeoT c).symm x).1 = t := by
  have h1 : (ballHomeoT c) ⟨t, ht⟩ = x := Subtype.ext hx
  have h2 := congrArg (ballHomeoT c).symm h1
  rw [Homeomorph.symm_apply_apply] at h2
  rw [← h2]

/-- The 16-fold closed-ball parametrization `EIndex × D⁴ ≃ ballsV`. -/
def ballsVEquiv : (EIndex × ↥D4) ≃ ↥ballsV :=
  Equiv.ofBijective
    (fun p => ⟨centeredChartParam p.1.1 p.2.1,
      Set.mem_biUnion (eIndex_fixedSet p.1) ⟨p.2.1, p.2.2, rfl⟩⟩)
    ⟨fun a b h => by
      obtain ⟨hc, ht⟩ := chart_inj_across (eIndex_fixedSet a.1) (eIndex_fixedSet b.1)
        a.2.2 b.2.2 (Subtype.ext_iff.mp h)
      exact Prod.ext (Subtype.ext hc) (Subtype.ext ht),
     fun y => by
      obtain ⟨c, hc, t, ht, hy⟩ := Set.mem_iUnion₂.mp y.2
      exact ⟨(⟨c, (mem_fixedFinset c).mpr hc⟩, ⟨t, ht⟩), Subtype.ext hy⟩⟩

/-- **The 16-fold splitter homeomorphism for the `B`-side**: `EIndex × D⁴ ≃ₜ ballsV`. -/
def ballsVSplitHomeo : (EIndex × ↥D4) ≃ₜ ↥ballsV :=
  Continuous.homeoOfEquivCompactToT2 (f := ballsVEquiv)
    ((continuous_centeredChartParamJoint.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))).subtype_mk _)

/-- The 16-fold annulus parametrization `EIndex × Ann⁴ ≃ thickA ∩ ballsV`. -/
def interEquiv : (EIndex × ↥ann4) ≃ ↥(thickA ∩ ballsV) :=
  Equiv.ofBijective
    (fun p => ⟨centeredChartParam p.1.1 p.2.1,
      annPiece_subset_inter (eIndex_fixedSet p.1) ⟨p.2.1, p.2.2, rfl⟩⟩)
    ⟨fun a b h => by
      obtain ⟨hc, ht⟩ := chart_inj_across (eIndex_fixedSet a.1) (eIndex_fixedSet b.1)
        (ann4_subset_D4 a.2.2) (ann4_subset_D4 b.2.2) (Subtype.ext_iff.mp h)
      exact Prod.ext (Subtype.ext hc) (Subtype.ext ht),
     fun y => by
      obtain ⟨c, hc, t, ht, hy⟩ := inter_elim y.2
      exact ⟨(⟨c, (mem_fixedFinset c).mpr hc⟩, ⟨t, ht⟩), Subtype.ext hy⟩⟩

/-- **The 16-fold splitter homeomorphism for the intersection**:
`EIndex × Ann⁴ ≃ₜ thickA ∩ ballsV`. -/
def interSplitHomeo : (EIndex × ↥ann4) ≃ₜ ↥(thickA ∩ ballsV) :=
  Continuous.homeoOfEquivCompactToT2 (f := interEquiv)
    ((continuous_centeredChartParamJoint.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))).subtype_mk _)

end

end SKEFTHawking.KummerPunctureBalls
