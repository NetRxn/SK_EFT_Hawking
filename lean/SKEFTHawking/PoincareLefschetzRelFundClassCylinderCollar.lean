/-
# Phase 5q.H (W-A.1g collar) — the explicit product collar discharges the cylinder collar-injectivity

The lead's collar-fork ruling in action: **no general collar theorem** — for the cylinder
`W = M × [0,1]` the collar `M × ([0,¼) ∪ (¾,1])` is *explicit*, so the collar-injectivity residual
`hinj : Injective (relIncl (∂W ⊆ Kᶜ))` of
`PoincareLefschetzRelFundClassCylinder.cylinder_determinedByInteriorPoints` is discharged directly:

* `clamp` — the explicit clamp retraction `sub Kᶜ → sub ∂W`, `(σ,t) ↦ (σ, ρ t)` with the ramp
  `ρ t = max 0 (min 1 (2t - ½))` (`= 0` for `t ≤ ¼`, `= 1` for `t ≥ ¾`), which lands in
  `∂W = M × {0,1}` on the collar `Kᶜ`;
* `collarHomotopy` — the straight-line deformation-retract homotopy `(1-s)·ρ t + s·t` of `Kᶜ` onto
  `∂W` (stays in `Kᶜ`), giving `sub ∂W ≃ sub Kᶜ` a homotopy equivalence;
* `subMap_collar_bijective` — hence `subMap (∂W ⊆ Kᶜ)` is bijective in every degree `k+1`
  (`Homology.map_bijective_of_homotopyEquiv`);
* `cylinder_collar_relIncl_injective` — feeds that into the mono four-lemma reduction
  `SingularPairLESNaturality.relIncl_injective_of_subMap` to discharge `hinj`; and
* `cylinder_determinedByInteriorPoints_of_slab` — the collar-residual-free Wall 2 for the cylinder:
  `DeterminedByInteriorPoints` from **only** the interior-slab closed-case `determinedByPoints`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassCylinder
import SKEFTHawking.SingularPairLESNaturality
import SKEFTHawking.SingularHomotopyInvariance

open scoped Manifold
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.SingularPairLESNaturality
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularManifoldFundamentalClass

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderCollar

noncomputable section

variable {m' : ℕ}
  {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M]

/-! ## §1. The ramp function `ρ t = max 0 (min 1 (2t - ½))` -/

/-- The ramp `ρ : ℝ → ℝ`, `= 0` for `t ≤ ¼`, `= 1` for `t ≥ ¾`, linear between; the interval clamp
that pushes the collar `[0,¼) ∪ (¾,1]` onto the endpoints `{0,1}`. -/
def rampR (t : ℝ) : ℝ := max 0 (min 1 (2 * t - 1 / 2))

theorem continuous_rampR : Continuous rampR := by
  unfold rampR
  fun_prop

theorem rampR_nonneg (t : ℝ) : 0 ≤ rampR t := le_max_left _ _

theorem rampR_le_one (t : ℝ) : rampR t ≤ 1 := by
  rw [rampR, max_le_iff]
  exact ⟨by norm_num, min_le_left _ _⟩

theorem rampR_eq_zero_of_le (t : ℝ) (ht : t ≤ 1 / 4) : rampR t = 0 := by
  rw [rampR, max_eq_left]
  calc min 1 (2 * t - 1 / 2) ≤ 2 * t - 1 / 2 := min_le_right _ _
    _ ≤ 0 := by linarith

theorem rampR_eq_one_of_ge (t : ℝ) (ht : 3 / 4 ≤ t) : rampR t = 1 := by
  rw [rampR, min_eq_left (by linarith), max_eq_right (by norm_num)]

theorem rampR_zero : rampR 0 = 0 := rampR_eq_zero_of_le 0 (by norm_num)

theorem rampR_one : rampR 1 = 1 := rampR_eq_one_of_ge 1 (by norm_num)

/-- The ramp as an endomap of `[0,1]`. -/
def rampIcc (u : Set.Icc (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨rampR (u : ℝ), rampR_nonneg _, rampR_le_one _⟩

theorem continuous_rampIcc : Continuous rampIcc :=
  Continuous.subtype_mk (continuous_rampR.comp continuous_subtype_val) _

/-! ## §2. The cylinder boundary as `M × {0,1}`, and the collar dichotomy -/

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- The cylinder boundary as an explicit condition on the interval coordinate. -/
theorem mem_cylBoundary (p : cylW M) :
    p ∈ (cylModel m').boundary (cylW M) ↔ (p.2 = ⊥ ∨ p.2 = ⊤) := by
  rw [cyl_boundary_eq, Set.mem_prod, Set.mem_insert_iff, Set.mem_singleton_iff]
  simp

omit [T2Space M] [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M] in
/-- A point of the collar `Kᶜ = (interiorSlab)ᶜ` has its interval coordinate off `[¼,¾]`. -/
theorem collar_cases {p : cylW M} (hp : p ∈ (interiorSlab M)ᶜ) :
    (p.2 : ℝ) < 1 / 4 ∨ 3 / 4 < (p.2 : ℝ) := by
  simp only [interiorSlab, Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or, not_le] at hp
  exact hp

/-! ## §3. The clamp retraction `sub Kᶜ → sub ∂W` -/

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- The clamp of an interval coordinate on the collar lands on an endpoint `{⊥,⊤}`. -/
theorem rampIcc_mem_boundary {p : cylW M} (hp : p ∈ (interiorSlab M)ᶜ) :
    rampIcc p.2 = ⊥ ∨ rampIcc p.2 = ⊤ := by
  rcases collar_cases hp with h | h
  · exact Or.inl (Subtype.ext (by
      show rampR (p.2 : ℝ) = ((⊥ : Set.Icc (0 : ℝ) 1) : ℝ)
      rw [rampR_eq_zero_of_le _ (le_of_lt h)]; rfl))
  · exact Or.inr (Subtype.ext (by
      show rampR (p.2 : ℝ) = ((⊤ : Set.Icc (0 : ℝ) 1) : ℝ)
      rw [rampR_eq_one_of_ge _ (le_of_lt h)]; rfl))

/-- **The clamp retraction** `sub Kᶜ → sub ∂W`, `(σ,t) ↦ (σ, ρ t)` — pushes the collar onto the
boundary `M × {0,1}`. -/
def clamp : C(↑(sub (X := TopCat.of (cylW M)) ((interiorSlab M)ᶜ)),
    ↑(sub (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M)))) where
  toFun q := ⟨(q.1.1, rampIcc q.1.2), (mem_cylBoundary _).mpr (rampIcc_mem_boundary q.2)⟩
  continuous_toFun :=
    Continuous.subtype_mk
      ((continuous_fst.comp continuous_subtype_val).prodMk
        (continuous_rampIcc.comp (continuous_snd.comp continuous_subtype_val))) _

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- `∂W ⊆ Kᶜ`, ascribed to the ambient `TopCat.of (cylW M)` so `subMap`/`relIncl` infer `X`. -/
theorem hsub : ((cylModel m').boundary (cylW M) : Set ↑(TopCat.of (cylW M))) ⊆ (interiorSlab M)ᶜ :=
  boundary_subset_compl_interiorSlab

omit [T2Space M] [CompactSpace M] [Nonempty M] in
theorem rampIcc_bot : rampIcc (⊥ : Set.Icc (0 : ℝ) 1) = ⊥ :=
  Subtype.ext (by show rampR (0 : ℝ) = 0; exact rampR_zero)

omit [T2Space M] [CompactSpace M] [Nonempty M] in
theorem rampIcc_top : rampIcc (⊤ : Set.Icc (0 : ℝ) 1) = ⊤ :=
  Subtype.ext (by show rampR (1 : ℝ) = 1; exact rampR_one)

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- **The clamp splits the collar inclusion**: `clamp ∘ (∂W ↪ Kᶜ) = id` on `∂W` (endpoints are
fixed by `ρ`). This is the strict `g ∘ f = id` half of the homotopy equivalence. -/
theorem clamp_comp_subInclMap :
    clamp.comp (subInclMap (hsub (m' := m') (M := M))) = ContinuousMap.id _ := by
  refine ContinuousMap.ext fun q => Subtype.ext ?_
  show ((q.1.1, rampIcc q.1.2) : cylW M) = q.1
  refine Prod.ext rfl ?_
  rcases (mem_cylBoundary q.1).mp q.2 with h | h <;> rw [h]
  · exact rampIcc_bot
  · exact rampIcc_top

/-! ## §4. The straight-line deformation-retract homotopy of `Kᶜ` onto `∂W` -/

/-- The interpolation `(1-s)·ρ(u) + s·u` from the clamp (`s=0`) to the identity (`s=1`). -/
def interpR (s u : ℝ) : ℝ := (1 - s) * rampR u + s * u

theorem interpR_zero (u : ℝ) : interpR 0 u = rampR u := by simp [interpR]

theorem interpR_one (u : ℝ) : interpR 1 u = u := by simp [interpR]

theorem continuous_interpR : Continuous (fun p : ℝ × ℝ => interpR p.1 p.2) := by
  unfold interpR
  exact ((continuous_const.sub continuous_fst).mul (continuous_rampR.comp continuous_snd)).add
    (continuous_fst.mul continuous_snd)

theorem interpR_nonneg {s u : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hu0 : 0 ≤ u) : 0 ≤ interpR s u :=
  add_nonneg (mul_nonneg (by linarith) (rampR_nonneg u)) (mul_nonneg hs0 hu0)

theorem interpR_le_one {s u : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hu1 : u ≤ 1) :
    interpR s u ≤ 1 := by
  have h1 : (1 - s) * rampR u ≤ (1 - s) * 1 := mul_le_mul_of_nonneg_left (rampR_le_one u) (by linarith)
  have h2 : s * u ≤ s * 1 := mul_le_mul_of_nonneg_left hu1 hs0
  simp only [interpR]; nlinarith [h1, h2]

theorem interpR_off_slab {s u : ℝ} (hs1 : s ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hoff : u < 1 / 4 ∨ 3 / 4 < u) : interpR s u < 1 / 4 ∨ 3 / 4 < interpR s u := by
  rcases hoff with h | h
  · left
    have hr : rampR u = 0 := rampR_eq_zero_of_le u (le_of_lt h)
    have hsu : s * u ≤ u := mul_le_of_le_one_left hu0 hs1
    simp only [interpR, hr, mul_zero, zero_add]
    linarith
  · right
    have hr : rampR u = 1 := rampR_eq_one_of_ge u (le_of_lt h)
    have hsu : s * (1 - u) ≤ 1 - u := mul_le_of_le_one_left (by linarith) hs1
    have : interpR s u = 1 - s * (1 - u) := by simp only [interpR, hr, mul_one]; ring
    rw [this]; linarith

/-- The interpolated interval coordinate stays in `[0,1]`. -/
theorem interpIcc_mem (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (u : Set.Icc (0 : ℝ) 1) :
    interpR s (u : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨interpR_nonneg hs.1 hs.2 u.2.1, interpR_le_one hs.1 hs.2 u.2.2⟩

omit [T2Space M] [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M] in
/-- The interpolated point stays in the collar `Kᶜ`. -/
theorem interp_pt_mem_collar {p : cylW M} (hp : p ∈ (interiorSlab M)ᶜ) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hmem : interpR s (p.2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    ((p.1, ⟨interpR s (p.2 : ℝ), hmem⟩) : cylW M) ∈ (interiorSlab M)ᶜ := by
  simp only [interiorSlab, Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or, not_le]
  exact interpR_off_slab hs.2 p.2.2.1 p.2.2.2 (collar_cases hp)

/-- **The deformation-retract homotopy** `H((σ,t), s) = (σ, (1-s)·ρ t + s·t)` of the collar `Kᶜ`
onto `∂W`: `H(·, 0) = (∂W ↪ Kᶜ) ∘ clamp` and `H(·, 1) = id`. -/
def collarHomotopy :
    C(↑(sub (X := TopCat.of (cylW M)) ((interiorSlab M)ᶜ)) × unitInterval,
      ↑(sub (X := TopCat.of (cylW M)) ((interiorSlab M)ᶜ))) where
  toFun p :=
    ⟨(p.1.1.1, ⟨interpR (p.2 : ℝ) (p.1.1.2 : ℝ), interpIcc_mem _ p.2.2 p.1.1.2⟩),
      interp_pt_mem_collar p.1.2 p.2.2 (interpIcc_mem _ p.2.2 p.1.1.2)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.prodMk
      (continuous_fst.comp (continuous_subtype_val.comp continuous_fst))
      (Continuous.subtype_mk (continuous_interpR.comp (Continuous.prodMk
        (continuous_subtype_val.comp continuous_snd)
        (continuous_subtype_val.comp (continuous_snd.comp
          (continuous_subtype_val.comp continuous_fst))))) _)) _

/-- The constant homotopy on `∂W` (projection to the point coordinate) — the trivial `g∘f ≃ id`
witness (the split is strict). -/
def constHomotopy :
    C(↑(sub (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M))) × unitInterval,
      ↑(sub (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M)))) :=
  ⟨fun p => p.1, continuous_fst⟩

/-! ## §5. The homotopy equivalence, `subMap` bijectivity, and the discharged Wall 2 -/

omit [T2Space M] [CompactSpace M] [Nonempty M] in
theorem slice_collarHomotopy_zero :
    slice collarHomotopy 0 = (subInclMap (hsub (m' := m') (M := M))).comp clamp := by
  refine ContinuousMap.ext fun q => Subtype.ext (Prod.ext rfl (Subtype.ext ?_))
  show interpR ((0 : unitInterval) : ℝ) (q.1.2 : ℝ) = rampR (q.1.2 : ℝ)
  simp [interpR]

omit [T2Space M] [CompactSpace M] [Nonempty M] in
theorem slice_collarHomotopy_one :
    slice collarHomotopy 1
      = ContinuousMap.id ↑(sub (X := TopCat.of (cylW M)) ((interiorSlab M)ᶜ)) := by
  refine ContinuousMap.ext fun q => Subtype.ext (Prod.ext rfl (Subtype.ext ?_))
  show interpR ((1 : unitInterval) : ℝ) (q.1.2 : ℝ) = (q.1.2 : ℝ)
  simp [interpR]

omit [T2Space M] [CompactSpace M] [Nonempty M] in
theorem slice_constHomotopy (r : unitInterval) :
    slice constHomotopy r
      = ContinuousMap.id ↑(sub (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M))) :=
  ContinuousMap.ext fun _ => rfl

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- **The collar inclusion `∂W ↪ Kᶜ` is a homology iso** in every degree `k+1`: `subMap` is bijective,
because `Kᶜ` deformation-retracts onto `∂W` through the explicit product collar (clamp `ρ`). -/
theorem subMap_collar_bijective (k : ℕ) :
    Function.Bijective
      (subMap (X := TopCat.of (cylW M)) (hsub (m' := m') (M := M)) (k + 1)) :=
  Homology.map_bijective_of_homotopyEquiv
    (subInclMap (X := TopCat.of (cylW M)) (hsub (m' := m') (M := M))) clamp
    constHomotopy ((slice_constHomotopy 0).trans (clamp_comp_subInclMap).symm)
    (slice_constHomotopy 1) collarHomotopy slice_collarHomotopy_zero slice_collarHomotopy_one k

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- **The cylinder collar-injectivity residual is discharged**: `relIncl (∂W ⊆ Kᶜ)` is injective at the
top degree `m'+3`. The mono four-lemma reduction (`relIncl_injective_of_subMap`) fed the two collar
homology isos (`subMap_collar_bijective` in degrees `m'+3` and `m'+2`). This is exactly the `hinj`
hypothesis of `cylinder_determinedByInteriorPoints`, now supplied by the explicit product collar. -/
theorem cylinder_collar_relIncl_injective :
    Function.Injective (relIncl (M := TopCat.of (cylW M)) (hsub (m' := m') (M := M)) (m' + 1 + 2)) :=
  relIncl_injective_of_subMap (X := TopCat.of (cylW M)) (hsub (m' := m') (M := M)) (m' + 2)
    (subMap_collar_bijective (m' + 2)).surjective (subMap_collar_bijective (m' + 1)).injective

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- **Wall 2 for the cylinder, collar-residual-free.** `DeterminedByInteriorPoints` for the pair
`(W, ∂W)` at the top degree `m'+3` from **only** the interior-slab closed-case `determinedByPoints` —
the collar-injectivity `hinj` of `cylinder_determinedByInteriorPoints` is discharged internally by the
explicit product collar (`cylinder_collar_relIncl_injective`). The remaining input `hdet` is the
closed-case degree-`(m'+3)` determination on the compact interior slab `K = M × [¼,¾]`. -/
theorem cylinder_determinedByInteriorPoints_of_slab
    (hdet : determinedByPoints (X := TopCat.of (cylW M)) (m' + 1 + 2) (interiorSlab M)) :
    DeterminedByInteriorPoints (X := TopCat.of (cylW M))
      ((cylModel m').boundary (cylW M)) (m' + 1 + 2) :=
  cylinder_determinedByInteriorPoints hdet cylinder_collar_relIncl_injective

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderCollar
