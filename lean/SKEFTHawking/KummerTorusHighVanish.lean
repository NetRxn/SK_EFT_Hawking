/-
# The circle-peel **vanishing** step and the torus high-degree table `Hₚ(Tⁿ;ℤ) = 0` for `p > n`

`KummerTorusStep` abstracted the `T²` Mayer–Vietoris chase over a variable first factor `Y` and
delivered the *free-finite/rank* form of the circle-product step
(`stepPos_free_finrank : finrank Hₖ₊₂(Y×S¹) = finrank Hₖ₊₂(Y) + finrank Hₖ₊₁(Y)`). That form needs
`Module.Free`/`Module.Finite` instances at both input degrees, so it does not directly give the
*vanishing* statement one degree above the top — which is what every top-degree argument on the
`T⁴` tower actually consumes.

This module ships the missing **vanishing** form of the same step, off the same banked polar MV
cover:

    `Hₖ₊₂(Y;ℤ) = 0` and `Hₖ₊₁(Y;ℤ) = 0`  ⟹  `Hₖ₊₂(Y × S¹;ℤ) = 0`   (`torVanish`)

The proof is three lines of the MV LES: the connecting map lands in `Hₖ₊₁(covA∩covB) ≅ Hₖ₊₁(Y)²`
(`interArcSplitEquivInt`, the two-arc split of the doubly-punctured circle factor) which vanishes,
so the class comes from `Hₖ₊₂(covA) ⊕ Hₖ₊₂(covB) ≅ Hₖ₊₂(Y)²` (`legAEquivInt`/`legBEquivInt`, the
punctured-circle leg collapses) which also vanishes.

Iterating up the banked tower `S¹ → T² → T³ → T⁴` (each step raising the vanishing threshold by
exactly one) gives the **torus high-degree table**

    `Hₚ(Sph 1) = 0` for `p > 1`, `Hₚ(T²) = 0` for `p > 2`, `Hₚ(T³) = 0` for `p > 3`,
    `Hₚ(T⁴) = 0` for `p > 4`   (`torusFour_homology_high`, on the actual `TorusFour = Circle⁴`).

`Hₚ(T⁴;ℤ) = 0` for `p ≥ 5` is the input the punctured-torus top-degree arguments need and which
the banked `KummerHomologyT4Full` table (Betti numbers only up to degree 4) did not supply.

Vacuity attack: `torVanish`'s conclusion is false without its hypotheses — take `Y = S¹` and
`k = 0`: `H₁(S¹) ≅ ℤ ≠ 0` (`circleH1EquivInt`) forces `H₂(S¹ × S¹) ≅ ℤ ≠ 0` through
`stepPos_free_finrank`, so no hypothesis-free version exists. The threshold arithmetic is sharp:
`torusFour_homology_high` is stated for `p > 4` and `H₄(T⁴) ≅ ℤ ≠ 0`
(`KummerHomologyT4Full.torusFourH4EquivInt`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.KummerHomologyT4H2

namespace SKEFTHawking.KummerTorusHighVanish

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.SingularProdContractibleInt (ProdSp homeoHomologyEquivInt)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularSphereBottom (basePoint)
open SKEFTHawking.SingularMayerVietorisLESInt (mvDeltaInt mv_exact_ambientInt)
open SKEFTHawking.KummerTorusStep (Tor covA covB covAB_cover legAEquivInt legBEquivInt
  interArcSplitEquivInt)
open SKEFTHawking.KummerHomologyT2 (TwoTorus)
open SKEFTHawking.KummerHomologyT4H2 (fourStepHomeoTorusFour)
open SKEFTHawking.KummerK3Base (TorusFour)

noncomputable section

/-! ## §1. The circle-peel vanishing step -/

/-- **The circle-product vanishing step.** If `Hₖ₊₂(Y;ℤ)` and `Hₖ₊₁(Y;ℤ)` both vanish, so does
`Hₖ₊₂(Y × S¹;ℤ)`. The vanishing companion of `KummerTorusStep.stepPos_free_finrank`, off the same
banked polar Mayer–Vietoris cover `covA = Y×(S¹∖{v})`, `covB = Y×(S¹∖{−v})`: the MV connecting map
lands in `Hₖ₊₁(covA∩covB) ≅ Hₖ₊₁(Y) × Hₖ₊₁(Y) = 0`, so the class lifts to
`Hₖ₊₂(covA) ⊕ Hₖ₊₂(covB) ≅ Hₖ₊₂(Y) × Hₖ₊₂(Y) = 0`. -/
theorem torVanish (Y : TopCat) (k : ℕ) (h2 : ∀ x : Homology Y (k + 2), x = 0)
    (h1 : ∀ x : Homology Y (k + 1), x = 0) (x : Homology (Tor Y) (k + 2)) : x = 0 := by
  set v : ↑(Sph 1) := basePoint 1 with hv
  have hcov := covAB_cover Y v
  have h0 : mvDeltaInt (covA Y v) (covB Y v) (k + 1) hcov x = 0 := by
    refine (interArcSplitEquivInt Y v k).map_eq_zero_iff.mp ?_
    exact Prod.ext_iff.mpr ⟨h1 _, h1 _⟩
  obtain ⟨p, hp⟩ := (mv_exact_ambientInt (covA Y v) (covB Y v) (k + 1) hcov x).mp h0
  have hp0 : p = 0 :=
    Prod.ext_iff.mpr ⟨(legAEquivInt Y v (k + 1)).map_eq_zero_iff.mp (h2 _),
      (legBEquivInt Y v (k + 1)).map_eq_zero_iff.mp (h2 _)⟩
  rw [← hp, hp0, map_zero]

/-- **Threshold form of the step**: if `Y`'s integral homology vanishes strictly above degree `d`,
then `Y × S¹`'s vanishes strictly above degree `d + 1`. This is the induction step of the torus
tower — each circle factor raises the vanishing threshold by exactly one. -/
theorem tor_high (Y : TopCat) (d : ℕ) (hY : ∀ p, d < p → ∀ x : Homology Y p, x = 0)
    (p : ℕ) (hp : d + 1 < p) (x : Homology (Tor Y) p) : x = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 2 := ⟨p - 2, by omega⟩
  exact torVanish Y k (hY (k + 2) (by omega)) (hY (k + 1) (by omega)) x

/-! ## §2. The torus tower `S¹ → T² → T³ → T⁴` -/

/-- `Hₚ(S¹;ℤ) = 0` for `p > 1` — the tower base (banked `sphere_homology_high` at `n = 1`). -/
theorem circle_high (p : ℕ) (hp : 1 < p) (x : Homology (Sph 1) p) : x = 0 :=
  SKEFTHawking.SingularSphereHighDegreeInt.sphere_homology_high 1 p hp x

/-- **`Hₚ(T²;ℤ) = 0` for `p > 2`** — one circle peel off the base. -/
theorem twoTorus_high (p : ℕ) (hp : 2 < p) (x : Homology TwoTorus p) : x = 0 :=
  tor_high (Sph 1) 1 circle_high p hp x

/-- **`Hₚ(T³;ℤ) = 0` for `p > 3`**. -/
theorem threeTorus_high (p : ℕ) (hp : 3 < p) (x : Homology (Tor TwoTorus) p) : x = 0 :=
  tor_high TwoTorus 2 twoTorus_high p hp x

/-- **`Hₚ(T⁴;ℤ) = 0` for `p > 4`** on the step-tower carrier `Tor (Tor T²) = ((S¹×S¹)×S¹)×S¹`. -/
theorem fourStep_high (p : ℕ) (hp : 4 < p) (x : Homology (Tor (Tor TwoTorus)) p) : x = 0 :=
  tor_high (Tor TwoTorus) 3 threeTorus_high p hp x

/-- **`Hₚ(T⁴;ℤ) = 0` for every `p ≥ 5`, on the actual `TorusFour = Circle⁴`** — the step-tower
vanishing transported across the banked reassociation homeomorphism `fourStepHomeoTorusFour`.
Complements the banked degree-`≤ 4` Betti table (`KummerHomologyT4Full.torusFour_betti`), whose top
entry `finrank H₄(T⁴) = 1` shows the threshold `p > 4` is sharp. -/
theorem torusFour_homology_high (p : ℕ) (hp : 4 < p) (x : Homology (TopCat.of TorusFour) p) :
    x = 0 := by
  set e := homeoHomologyEquivInt (X := TopCat.of TorusFour) (Y := Tor (Tor TwoTorus))
    fourStepHomeoTorusFour.symm p with he
  exact e.map_eq_zero_iff.mp (fourStep_high p hp (e x))

end

end SKEFTHawking.KummerTorusHighVanish
