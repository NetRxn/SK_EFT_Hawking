/-
# `Hₚ(T⁴ ∖ {16 two-torsion points}; ℤ) = 0` for `p ≥ 4` — the punctured-torus top-degree vanishing

The `orientInput` residual bottoms out in two **top-degree vanishing statements for the punctured
4-torus**, `H₄(T⁴°;ℤ) = H₅(T⁴°;ℤ) = 0` (`KummerQuotientTransferSequence`, §3–§4). "True by
dimension" is only a heuristic in a singular-homology substrate: the `ℝP³` analogue needed a genuine
good-cover Mayer–Vietoris telescope (`KummerRP3GoodCoverTelescope`). This module supplies the
punctured-torus telescope — and it is *not* a chart telescope, it is a **two-set peel run up the
circle tower**, one level per circle factor.

## The peel step

Write the next torus as `Y × S¹` and let `{v, −v} ⊆ S¹` be the two-point 2-torsion of the new circle
factor (`dpc v = S¹ ∖ {v, −v}`). If `S ⊆ Y` is the already-punctured previous level, the next level
is the two-set open cover

    `S⁺ = (S × S¹) ∪ (Y × (S¹ ∖ {v,−v}))`

whose pieces are covered by *banked* machinery:

* `S × S¹` is a circle product over `S` — its vanishing threshold rises by exactly one under
  `KummerTorusHighVanish.tor_high` (the circle-peel vanishing step);
* `Y × (S¹∖{v,−v})` is literally the polar Mayer–Vietoris intersection `covA ∩ covB` of
  `KummerTorusStep`, whose homology is `Hₖ(Y) ⊕ Hₖ(Y)` (`interArcSplitEquivInt`, the two-arc split);
* the seam `S × (S¹∖{v,−v})` is the same two-arc split over `S`.

The ambient-generic sandwich `SingularSubVanishMV.vanish_union` then raises the threshold by one
(`punc_step`). Starting from `S¹ ∖ {v,−v} ≃ ℝ∖0 ≃ S⁰` (threshold `0`) and peeling three times up the
banked tower `S¹ → T² → T³ → T⁴` gives

    **`torusFourPunctured_high : Hₚ(T⁴ ∖ fixedSet; ℤ) = 0` for every `p ≥ 4`**,

on the actual `TorusFour = Circle⁴` carrier and its `fixedSet` of 16 `τ`-fixed points, transported
across the banked reassociation homeomorphism `KummerHomologyT4H2.fourStepHomeoTorusFour`.

## Sharpness / vacuity attack

The threshold is sharp and the statement is nowhere vacuous: `H₃(T⁴ ∖ 16 pts; ℤ)` is *not* zero (it
surjects onto `H₃(T⁴;ℤ) ≅ ℤ⁴`, `KummerPunctureH3.thickIncl3_surjective`), so `p ≥ 4` cannot be
weakened to `p ≥ 3`. Nor may the punctures be dropped: `H₄(T⁴;ℤ) ≅ ℤ ≠ 0`
(`KummerHomologyT4Full.torusFourH4EquivInt`), so the puncture set is load-bearing, and `punc_step`
is false without its `hS`/`hY` hypotheses.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.KummerTorusHighVanish
import SKEFTHawking.SingularSubVanishMV
import SKEFTHawking.SingularEuclideanSphereInt
import SKEFTHawking.KummerPuncturedTorus

namespace SKEFTHawking.KummerPuncturedTorusHighVanish

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularSphereAcyclic (Sph antipode)
open SKEFTHawking.SingularProdContractibleInt (ProdSp homeoHomologyEquivInt)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularPuncturedRetract (Punc)
open SKEFTHawking.SingularSubVanishMV (vanish_union)
open SKEFTHawking.KummerTorusStep (Tor covA covB covAB_inter interArcSplitEquivInt)
open SKEFTHawking.KummerTorusHighVanish (tor_high circle_high twoTorus_high threeTorus_high)
open SKEFTHawking.KummerHomologyT2 (TwoTorus dpcHomeo)

noncomputable section

/-! ## §1. Product-subset reassociation homeomorphisms -/

/-- `S × C ⊆ Y × C`, as a space, **is** the product `(sub S) × C`. -/
def prodSubFstUniv (Y C : TopCat) (S : Set ↑Y) :
    ↑(sub (X := ProdSp Y C) (S ×ˢ (Set.univ : Set ↑C))) ≃ₜ ↑(ProdSp (sub S) C) where
  toFun p := (⟨p.1.1, p.2.1⟩, p.1.2)
  invFun q := ⟨(q.1.1, q.2), ⟨q.1.2, Set.mem_univ _⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _

/-- `S × T ⊆ Y × C`, as a space, **is** `univ × T ⊆ (sub S) × C` — the first factor absorbed into
the ambient. -/
def prodSubFstSet (Y C : TopCat) (S : Set ↑Y) (T : Set ↑C) :
    ↑(sub (X := ProdSp Y C) (S ×ˢ T))
      ≃ₜ ↑(sub (X := ProdSp (sub S) C) ((Set.univ : Set ↑(sub S)) ×ˢ T)) where
  toFun p := ⟨(⟨p.1.1, p.2.1⟩, p.1.2), ⟨Set.mem_univ _, p.2.2⟩⟩
  invFun q := ⟨(q.1.1.1, q.1.2), ⟨q.1.1.2, q.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun :=
    (((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _

/-! ## §2. The doubly-punctured circle factor -/

/-- The doubly-punctured circle `S¹ ∖ {v, −v}` — the two-torsion complement of a circle factor. -/
def dpc (v : ↑(Sph 1)) : Set ↑(Sph 1) := ({v}ᶜ : Set ↑(Sph 1)) ∩ ({antipode v}ᶜ)

/-- `S¹ ∖ {v, −v}` is open. -/
theorem isOpen_dpc (v : ↑(Sph 1)) : IsOpen (dpc v) :=
  isOpen_compl_singleton.inter isOpen_compl_singleton

/-- **The peel base** `Hₚ(S¹∖{v,−v};ℤ) = 0` for `p ≥ 1` — the doubly-punctured circle is `ℝ∖0`
(`dpcHomeo`), which deformation-retracts onto the two-point sphere `S⁰`
(`homology_mapInt_normalize_bijective`). -/
theorem dpc_vanish (v : ↑(Sph 1)) (p : ℕ) (hp : 0 < p) (x : Homology (sub (dpc v)) p) : x = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  refine (homeoHomologyEquivInt (X := sub (dpc v)) (Y := Punc 1) (dpcHomeo v)
    (k + 1)).map_eq_zero_iff.mp ?_
  refine (SKEFTHawking.SingularPuncturedRetractInt.homology_mapInt_normalize_bijective
    1 k).injective ?_
  rw [map_zero]
  exact SKEFTHawking.SingularSphereHighDegreeInt.sphere0_homology_high k _

/-! ## §3. The peel step -/

/-- The next punctured level over `Y`: `(S × S¹) ∪ (Y × (S¹∖{v,−v})) ⊆ Y × S¹`. -/
def puncStep (Y : TopCat) (v : ↑(Sph 1)) (S : Set ↑Y) : Set ↑(Tor Y) :=
  (S ×ˢ (Set.univ : Set ↑(Sph 1))) ∪ ((Set.univ : Set ↑Y) ×ˢ dpc v)

/-- Membership in the next level: the base coordinate is already punctured, or the new circle
coordinate avoids `{v, −v}`. -/
theorem mem_puncStep (Y : TopCat) (v : ↑(Sph 1)) (S : Set ↑Y) (x : ↑Y) (y : ↑(Sph 1)) :
    ((x, y) : ↑(Tor Y)) ∈ puncStep Y v S ↔ x ∈ S ∨ y ∈ dpc v := by
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ⟨h, Set.mem_univ _⟩
    · exact Or.inr ⟨Set.mem_univ _, h⟩

/-- The next level is open. -/
theorem isOpen_puncStep (Y : TopCat) (v : ↑(Sph 1)) {S : Set ↑Y} (hS : IsOpen S) :
    IsOpen (puncStep Y v S) :=
  (hS.prod isOpen_univ).union (isOpen_univ.prod (isOpen_dpc v))

/-- The `Y × (S¹∖{v,−v})` piece: its homology is `Hₖ(Y) ⊕ Hₖ(Y)` (the two-arc split of the
doubly-punctured circle factor), so it vanishes wherever `Y` does. -/
theorem univProd_dpc_vanish (Y : TopCat) (v : ↑(Sph 1)) (k : ℕ)
    (hY : ∀ x : Homology Y (k + 1), x = 0)
    (x : Homology (sub (X := ProdSp Y (Sph 1)) ((Set.univ : Set ↑Y) ×ˢ dpc v)) (k + 1)) :
    x = 0 := by
  revert x
  rw [show ((Set.univ : Set ↑Y) ×ˢ dpc v) = covA Y v ∩ covB Y v from (covAB_inter Y v).symm]
  intro x
  exact (interArcSplitEquivInt Y v k).map_eq_zero_iff.mp (Prod.ext_iff.mpr ⟨hY _, hY _⟩)

/-- The seam `S × (S¹∖{v,−v})`: absorb the first factor into the ambient, then the same two-arc
split over `sub S`. -/
theorem prodSet_dpc_vanish (Y : TopCat) (v : ↑(Sph 1)) (S : Set ↑Y) (k : ℕ)
    (hS : ∀ x : Homology (sub S) (k + 1), x = 0)
    (x : Homology (sub (X := ProdSp Y (Sph 1)) (S ×ˢ dpc v)) (k + 1)) : x = 0 := by
  refine (homeoHomologyEquivInt (prodSubFstSet Y (Sph 1) S (dpc v)) (k + 1)).map_eq_zero_iff.mp ?_
  exact univProd_dpc_vanish (sub S) v k hS _

/-- **THE PEEL STEP.** If the previous punctured level `S ⊆ Y` is homologically `d`-dimensional and
the new torus `Y` is homologically `(d+1)`-dimensional, then the next punctured level
`(S × S¹) ∪ (Y × (S¹∖{v,−v})) ⊆ Y × S¹` is homologically `(d+1)`-dimensional. Two-set Mayer–Vietoris
sandwich (`SingularSubVanishMV.vanish_union`) over the banked circle-peel machinery. -/
theorem punc_step (Y : TopCat) (v : ↑(Sph 1)) (S : Set ↑Y) (d : ℕ) (hSopen : IsOpen S)
    (hS : ∀ q, d < q → ∀ z : Homology (sub S) q, z = 0)
    (hY : ∀ q, d + 1 < q → ∀ z : Homology Y q, z = 0)
    (p : ℕ) (hp : d + 1 < p) (x : Homology (sub (puncStep Y v S)) p) : x = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, p = j + 2 := ⟨p - 2, by omega⟩
  have hU : IsOpen (S ×ˢ (Set.univ : Set ↑(Sph 1))) := hSopen.prod isOpen_univ
  have hV : IsOpen ((Set.univ : Set ↑Y) ×ˢ dpc v) := isOpen_univ.prod (isOpen_dpc v)
  -- Piece 1: `S × S¹` — a circle product over `S`.
  have hUv : ∀ y : Homology (sub (X := ProdSp Y (Sph 1))
      (S ×ˢ (Set.univ : Set ↑(Sph 1)))) (j + 2), y = 0 := by
    intro y
    refine (homeoHomologyEquivInt (prodSubFstUniv Y (Sph 1) S) (j + 2)).map_eq_zero_iff.mp ?_
    exact tor_high (sub S) d (fun q hq z => hS q hq z) (j + 2) (by omega) _
  -- Piece 2: `Y × (S¹∖{v,−v})` — the two-arc split over `Y`.
  have hVv : ∀ y : Homology (sub (X := ProdSp Y (Sph 1))
      ((Set.univ : Set ↑Y) ×ˢ dpc v)) (j + 2), y = 0 :=
    fun y => univProd_dpc_vanish Y v (j + 1) (fun z => hY (j + 2) (by omega) z) y
  -- The seam `S × (S¹∖{v,−v})` — the two-arc split over `S`.
  have hIv : ∀ y : Homology (sub (X := ProdSp Y (Sph 1))
      ((S ×ˢ (Set.univ : Set ↑(Sph 1))) ∩ ((Set.univ : Set ↑Y) ×ˢ dpc v))) (j + 1), y = 0 := by
    have hset : (S ×ˢ (Set.univ : Set ↑(Sph 1))) ∩ ((Set.univ : Set ↑Y) ×ˢ dpc v)
        = S ×ˢ dpc v := by
      rw [Set.prod_inter_prod, Set.univ_inter, Set.inter_univ]
    rw [hset]
    exact fun y => prodSet_dpc_vanish Y v S j (fun z => hS (j + 1) (by omega) z) y
  exact vanish_union hU hV hUv hVv hIv x

/-! ## §4. The concrete tower `S¹ → T² → T³ → T⁴` -/

open SKEFTHawking.KummerK3Base (TorusFour)
open SKEFTHawking.KummerInvolution (negOne)
open SKEFTHawking.KummerPuncturedTorus (fixedSet mem_fixedSet_iff)
open SKEFTHawking.KummerHomologyT4 (circleHomeoSph1 complexEuclidLI)
open SKEFTHawking.KummerHomologyT4H2 (fourStepHomeoTorusFour)

/-- The chosen circle puncture: the image of `1 : Circle` in the `Sph 1` model. -/
def v0 : ↑(Sph 1) := circleHomeoSph1 1

/-- The punctured `T²` — `T²` minus its four 2-torsion points. -/
def punc2 : Set ↑TwoTorus := puncStep (Sph 1) v0 (dpc v0)

/-- The punctured `T³` — `T³` minus its eight 2-torsion points. -/
def punc3 : Set ↑(Tor TwoTorus) := puncStep TwoTorus v0 punc2

/-- The punctured `T⁴` — `T⁴` minus its sixteen 2-torsion points, on the step-tower carrier. -/
def punc4 : Set ↑(Tor (Tor TwoTorus)) := puncStep (Tor TwoTorus) v0 punc3

theorem isOpen_punc2 : IsOpen punc2 := isOpen_puncStep _ _ (isOpen_dpc v0)

theorem isOpen_punc3 : IsOpen punc3 := isOpen_puncStep _ _ isOpen_punc2

/-- `Hₚ(T² ∖ 4 pts;ℤ) = 0` for `p ≥ 2` — one peel off the doubly-punctured circle. -/
theorem punc2_vanish (p : ℕ) (hp : 1 < p) (x : Homology (sub punc2) p) : x = 0 :=
  punc_step (Sph 1) v0 (dpc v0) 0 (isOpen_dpc v0) (fun q hq z => dpc_vanish v0 q hq z)
    (fun q hq z => circle_high q hq z) p hp x

/-- `Hₚ(T³ ∖ 8 pts;ℤ) = 0` for `p ≥ 3`. -/
theorem punc3_vanish (p : ℕ) (hp : 2 < p) (x : Homology (sub punc3) p) : x = 0 :=
  punc_step TwoTorus v0 punc2 1 isOpen_punc2 (fun q hq z => punc2_vanish q hq z)
    (fun q hq z => twoTorus_high q hq z) p hp x

/-- **`Hₚ(T⁴ ∖ 16 pts;ℤ) = 0` for `p ≥ 4`** on the step-tower carrier — the punctured 4-torus is
homologically 3-dimensional. -/
theorem punc4_vanish (p : ℕ) (hp : 3 < p) (x : Homology (sub punc4) p) : x = 0 :=
  punc_step (Tor TwoTorus) v0 punc3 2 isOpen_punc3 (fun q hq z => punc3_vanish q hq z)
    (fun q hq z => threeTorus_high q hq z) p hp x

/-! ## §5. Transport onto the actual `TorusFour = Circle⁴` and its `fixedSet` -/

/-- The circle's *other* square root of unity lands on the antipode of `v0` — the `Circle`-side
2-torsion `{1, negOne}` is exactly the `Sph 1`-side antipodal pair `{v0, −v0}`. -/
theorem circleHomeoSph1_negOne : circleHomeoSph1 negOne = antipode v0 := by
  refine Subtype.ext ?_
  show complexEuclidLI ((negOne : Circle) : ℂ) = -(complexEuclidLI (((1 : Circle) : ℂ)))
  rw [SKEFTHawking.KummerInvolution.coe_negOne, Circle.coe_one, ← map_neg]

/-- A `Sph 1` point avoids `{v0, −v0}` iff its `Circle` preimage is not a square root of unity. -/
theorem mem_dpc_iff (w : ↑(Sph 1)) :
    w ∈ dpc v0 ↔ ¬(circleHomeoSph1.symm w = 1 ∨ circleHomeoSph1.symm w = negOne) := by
  have e1 : circleHomeoSph1.symm w = 1 ↔ w = v0 := Homeomorph.symm_apply_eq _
  have e2 : circleHomeoSph1.symm w = negOne ↔ w = antipode v0 := by
    rw [Homeomorph.symm_apply_eq, circleHomeoSph1_negOne]
  simp only [dpc, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff, e1, e2]
  tauto

/-- The reassociation homeomorphism, applied: four independent `circleHomeoSph1.symm`s. -/
theorem fourStepHomeoTorusFour_apply (a b c d : ↑(Sph 1)) :
    fourStepHomeoTorusFour (((a, b), c), d)
      = (circleHomeoSph1.symm a, circleHomeoSph1.symm b, circleHomeoSph1.symm c,
          circleHomeoSph1.symm d) := rfl

/-- Unfolded membership at the top of the tower: some circle coordinate avoids `{v0, −v0}`. -/
theorem mem_punc4 (a b c d : ↑(Sph 1)) :
    ((((a, b), c), d) : ↑(Tor (Tor TwoTorus))) ∈ punc4
      ↔ ((a ∈ dpc v0 ∨ b ∈ dpc v0) ∨ c ∈ dpc v0) ∨ d ∈ dpc v0 := by
  rw [punc4, mem_puncStep, punc3, mem_puncStep, punc2, mem_puncStep]

/-- **The tower's top punctured level is the complement of `fixedSet`.** `punc4 ⊆ T⁴` is exactly
`fourStepHomeoTorusFour ⁻¹' (fixedSetᶜ)`: "some circle coordinate avoids `{v0, −v0}`" is the De
Morgan dual of "every coordinate is a square root of unity", which is the banked coordinatewise
description `mem_fixedSet_iff` of the 16 `τ`-fixed points. -/
theorem punc4_eq_preimage :
    punc4 = fourStepHomeoTorusFour ⁻¹' ((fixedSet : Set TorusFour)ᶜ) := by
  have hfix : ∀ y : TorusFour, y ∈ (fixedSet : Set TorusFour) ↔
      (y.1 = 1 ∨ y.1 = negOne) ∧ (y.2.1 = 1 ∨ y.2.1 = negOne) ∧
        (y.2.2.1 = 1 ∨ y.2.2.1 = negOne) ∧ (y.2.2.2 = 1 ∨ y.2.2.2 = negOne) :=
    fun y => mem_fixedSet_iff y
  ext p
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := p
  rw [Set.mem_preimage, Set.mem_compl_iff, fourStepHomeoTorusFour_apply, hfix, mem_punc4,
    mem_dpc_iff a, mem_dpc_iff b, mem_dpc_iff c, mem_dpc_iff d]
  tauto

/-- Pointwise form of `punc4_eq_preimage` (no motive obstruction under a subtype). -/
theorem mem_punc4_iff (q : ↑(Tor (Tor TwoTorus))) :
    q ∈ punc4 ↔ fourStepHomeoTorusFour q ∈ ((fixedSet : Set TorusFour)ᶜ) := by
  rw [punc4_eq_preimage]
  exact Iff.rfl

/-- The tower's punctured carrier, transported onto the actual punctured `T⁴ = Circle⁴`. -/
def punc4Homeo : ↥punc4 ≃ₜ ↥((fixedSet : Set TorusFour)ᶜ) where
  toFun p := ⟨fourStepHomeoTorusFour p.1, (mem_punc4_iff p.1).mp p.2⟩
  invFun q := ⟨fourStepHomeoTorusFour.symm q.1, (mem_punc4_iff _).mpr (by
    rw [Homeomorph.apply_symm_apply]; exact q.2)⟩
  left_inv p := Subtype.ext (fourStepHomeoTorusFour.symm_apply_apply p.1)
  right_inv q := Subtype.ext (fourStepHomeoTorusFour.apply_symm_apply q.1)
  continuous_toFun := (fourStepHomeoTorusFour.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (fourStepHomeoTorusFour.symm.continuous.comp continuous_subtype_val).subtype_mk _

/-- **`Hₚ(T⁴ ∖ {16 two-torsion points}; ℤ) = 0` for every `p ≥ 4`** — the open punctured 4-torus is
homologically 3-dimensional, on the actual `TorusFour = Circle⁴` carrier. This is the geometric
termination input the punctured-torus top-degree arguments need (the `T⁴°` analogue of
`KummerRP3GoodCoverTelescope.rp3E_homology_high`), and it is *sharp*: `H₃` does not vanish (it
surjects onto `H₃(T⁴;ℤ) ≅ ℤ⁴`, `KummerPunctureH3.thickIncl3_surjective`). -/
theorem torusFourPunctured_high (p : ℕ) (hp : 3 < p)
    (x : Homology (sub (X := TopCat.of TorusFour) ((fixedSet : Set TorusFour)ᶜ)) p) : x = 0 := by
  refine (homeoHomologyEquivInt (X := sub (X := TopCat.of TorusFour)
    ((fixedSet : Set TorusFour)ᶜ)) (Y := sub (X := Tor (Tor TwoTorus)) punc4)
    punc4Homeo.symm p).map_eq_zero_iff.mp ?_
  exact punc4_vanish p hp _

end

end SKEFTHawking.KummerPuncturedTorusHighVanish
