/-
# Phase 5q.H — Kummer K1-a: `H₂(T⁴;ℤ) ≅ ℤ⁶` (the K3 generator's degree-2 Künneth)

The K3 (= Kummer) generator needs `H₂(T⁴;ℤ) ≅ ℤ⁶` for the project's custom
`SingularHomologyInt.Homology`. This module assembles it by **iterating the reusable circle-product
step lemma** (`KummerTorusStep`) up the tower `T² → T³ → T⁴`, seeded by the banked `T² = S¹ × S¹`
homology (`KummerHomologyT2`):

* `T² = Sph1²`: `H₀ ≅ ℤ`, `H₁ ≅ ℤ²`, `H₂ ≅ ℤ` (banked, `torusTwo…EquivIntSph`).
* `T³ = T² × S¹` (`stepDeg1` / `stepPos` at `Y = T²`): `H₁(T³) ≅ ℤ³`, `H₂(T³) ≅ ℤ³`.
* `T⁴ = T³ × S¹` (`stepPos` at `Y = T³`): `H₂(T⁴) ≅ ℤ⁶`  =  `finrank H₂(T³) + finrank H₁(T³)
  = 3 + 3`  =  the `6` generators `dxᵢ ∧ dxⱼ`, `C(4,2) = 6`.

The result is transported onto the *actual* `TorusFour = Circle⁴` across the reassociation +
`circleHomeoSph1` product homeomorphism, and tied to the banked degree-2 Künneth-index bijection
`KummerHomologyT4.hTwoIndexEquivFin6 : {s : Finset (Fin 4) // s.card = 2} ≃ Fin 6` (each of the six
`ℤ` summands is labelled by the pair of circle factors its class comes from).

This is a genuine rank-6 `≃ₗ[ℤ]` on the actual `Homology (TopCat.of TorusFour) 2`, computed through
the honest Mayer–Vietoris circle-product step — not a defined-to-be-`ℤ⁶` shell.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.KummerTorusStep
import SKEFTHawking.KummerHomologyT4

namespace SKEFTHawking.KummerHomologyT4H2

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.SingularProdContractibleInt (ProdSp homeoHomologyEquivInt)
open SKEFTHawking.KummerTorusStep (Tor stepPos_free_finrank stepDeg1_free_finrank)
open SKEFTHawking.KummerHomologyT2 (TwoTorus)
open SKEFTHawking.KummerHomologyT4 (circleHomeoSph1 hTwoIndexEquivFin6)
open SKEFTHawking.KummerK3Base (TorusFour)

/-! ## §1. The `T² = Sph1 × Sph1` base instances (from the banked homology) -/

/-- `T² = Sph1 × Sph1` is path-connected (product of path-connected circles). -/
instance pathConnected_twoTorus : PathConnectedSpace ↑TwoTorus := by
  haveI := KummerHomologyT2.pathConnected_sph1
  exact SKEFTHawking.SphereProdHOneInt.pathConnectedSpace_prod

noncomputable instance : Module.Free ℤ (Homology TwoTorus 2) :=
  Module.Free.of_equiv KummerHomologyT2.torusTwoH2EquivIntSph.symm

noncomputable instance : Module.Finite ℤ (Homology TwoTorus 2) :=
  Module.Finite.equiv KummerHomologyT2.torusTwoH2EquivIntSph.symm

noncomputable instance : Module.Free ℤ (Homology TwoTorus 1) :=
  Module.Free.of_equiv KummerHomologyT2.torusTwoH1EquivIntSph.symm

noncomputable instance : Module.Finite ℤ (Homology TwoTorus 1) :=
  Module.Finite.equiv KummerHomologyT2.torusTwoH1EquivIntSph.symm

/-- `finrank H₂(T²) = 1`. -/
theorem finrank_twoTorus_two : Module.finrank ℤ (Homology TwoTorus 2) = 1 := by
  rw [KummerHomologyT2.torusTwoH2EquivIntSph.finrank_eq]; exact Module.finrank_self ℤ

/-- `finrank H₁(T²) = 2`. -/
theorem finrank_twoTorus_one : Module.finrank ℤ (Homology TwoTorus 1) = 2 := by
  rw [KummerHomologyT2.torusTwoH1EquivIntSph.finrank_eq, Module.finrank_prod, Module.finrank_self]

/-- The banked `H₂(T³)` step result (`stepPos` at `Y = T²`), with the base free-finite facts. -/
theorem step_threeTorus_two :
    Module.Free ℤ (Homology (Tor TwoTorus) 2) ∧ Module.Finite ℤ (Homology (Tor TwoTorus) 2) ∧
      Module.finrank ℤ (Homology (Tor TwoTorus) 2)
        = Module.finrank ℤ (Homology TwoTorus 2) + Module.finrank ℤ (Homology TwoTorus 1) :=
  stepPos_free_finrank TwoTorus 0
    (inferInstanceAs (Module.Free ℤ (Homology TwoTorus 2)))
    (inferInstanceAs (Module.Finite ℤ (Homology TwoTorus 2)))
    (inferInstanceAs (Module.Free ℤ (Homology TwoTorus 1)))
    (inferInstanceAs (Module.Finite ℤ (Homology TwoTorus 1)))

/-! ## §2. `T³ = T² × S¹`: `H₂(T³) ≅ ℤ³` and `H₁(T³) ≅ ℤ³` -/

noncomputable instance : Module.Free ℤ (Homology (Tor TwoTorus) 2) := step_threeTorus_two.1

noncomputable instance : Module.Finite ℤ (Homology (Tor TwoTorus) 2) := step_threeTorus_two.2.1

noncomputable instance : Module.Free ℤ (Homology (Tor TwoTorus) 1) :=
  (stepDeg1_free_finrank TwoTorus).1

noncomputable instance : Module.Finite ℤ (Homology (Tor TwoTorus) 1) :=
  (stepDeg1_free_finrank TwoTorus).2.1

/-- **`finrank H₂(T³) = 3`** — `finrank H₂(T²) + finrank H₁(T²) = 1 + 2`. -/
theorem finrank_threeTorus_two : Module.finrank ℤ (Homology (Tor TwoTorus) 2) = 3 := by
  rw [step_threeTorus_two.2.2, finrank_twoTorus_two, finrank_twoTorus_one]

/-- **`finrank H₁(T³) = 3`** — `finrank H₁(T²) + 1 = 2 + 1` (the reduced-`H₀` degree-1 step). -/
theorem finrank_threeTorus_one : Module.finrank ℤ (Homology (Tor TwoTorus) 1) = 3 := by
  rw [(stepDeg1_free_finrank TwoTorus).2.2, finrank_twoTorus_one]

/-! ## §3. `T⁴ = T³ × S¹`: `H₂(T⁴) ≅ ℤ⁶` (on the step-tower carrier `Tor (Tor T²)`) -/

/-- The `H₂(T⁴)` step result (`stepPos` at `Y = T³`), fed the `T³` free-finite facts. -/
theorem step_fourTorus_two :
    Module.Free ℤ (Homology (Tor (Tor TwoTorus)) 2)
      ∧ Module.Finite ℤ (Homology (Tor (Tor TwoTorus)) 2)
      ∧ Module.finrank ℤ (Homology (Tor (Tor TwoTorus)) 2)
        = Module.finrank ℤ (Homology (Tor TwoTorus) 2)
          + Module.finrank ℤ (Homology (Tor TwoTorus) 1) :=
  stepPos_free_finrank (Tor TwoTorus) 0
    (inferInstanceAs (Module.Free ℤ (Homology (Tor TwoTorus) 2)))
    (inferInstanceAs (Module.Finite ℤ (Homology (Tor TwoTorus) 2)))
    (inferInstanceAs (Module.Free ℤ (Homology (Tor TwoTorus) 1)))
    (inferInstanceAs (Module.Finite ℤ (Homology (Tor TwoTorus) 1)))

noncomputable instance : Module.Free ℤ (Homology (Tor (Tor TwoTorus)) 2) := step_fourTorus_two.1

noncomputable instance : Module.Finite ℤ (Homology (Tor (Tor TwoTorus)) 2) := step_fourTorus_two.2.1

/-- **`finrank H₂(T⁴) = 6`** — `finrank H₂(T³) + finrank H₁(T³) = 3 + 3`, the `C(4,2) = 6`
generators `dxᵢ ∧ dxⱼ` (on the step-tower carrier). -/
theorem finrank_fourTorus_two : Module.finrank ℤ (Homology (Tor (Tor TwoTorus)) 2) = 6 := by
  rw [step_fourTorus_two.2.2, finrank_threeTorus_two, finrank_threeTorus_one]

/-- **`H₂(T⁴;ℤ) ≅ ℤ⁶`** on the step-tower carrier `Tor (Tor T²)` — a genuine rank-6 `≃ₗ[ℤ]`, the
free-finite basis of the honestly-computed degree-2 homology. -/
noncomputable def fourStepH2EquivFin6 : Homology (Tor (Tor TwoTorus)) 2 ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  ((Module.finBasis ℤ (Homology (Tor (Tor TwoTorus)) 2)).reindex
    (finCongr finrank_fourTorus_two)).equivFun

/-! ## §4. Transport onto the actual `TorusFour = Circle⁴` -/

/-- The reassociation + `circleHomeoSph1` product homeomorphism identifying the step-tower carrier
`((S¹×S¹)×S¹)×S¹` (left-associated `Sph 1` factors) with the actual `TorusFour = Circle⁴`
(right-associated `Circle` factors): apply `Circle ≃ₜ Sph 1` to each factor, then reassociate. -/
noncomputable def fourStepHomeoTorusFour : ↑(Tor (Tor TwoTorus)) ≃ₜ TorusFour :=
  (((circleHomeoSph1.symm.prodCongr circleHomeoSph1.symm).prodCongr
      circleHomeoSph1.symm).prodCongr circleHomeoSph1.symm).trans
    ((Homeomorph.prodAssoc (Circle × Circle) Circle Circle).trans
      (Homeomorph.prodAssoc Circle Circle (Circle × Circle)))

/-- **`H₂(T⁴;ℤ) ≅ ℤ⁶` — the K1-a headline, on the actual `TorusFour = Circle⁴`.** A genuine rank-6
`≃ₗ[ℤ]` carrying the six `dxᵢ ∧ dxⱼ` classes (`C(4,2) = 6`), transported from the step-tower
carrier across `fourStepHomeoTorusFour`. Computed through the honest Mayer–Vietoris circle-product
step — not a defined-to-be-`ℤ⁶` shell. -/
noncomputable def torusFourH2EquivFin6 : Homology (TopCat.of TorusFour) 2 ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  (homeoHomologyEquivInt (X := TopCat.of TorusFour) (Y := Tor (Tor TwoTorus))
    fourStepHomeoTorusFour.symm 2).trans fourStepH2EquivFin6

/-- **`finrank H₂(TorusFour) = 6`** — the honest rank pin on the actual `T⁴ = Circle⁴`, matching
the `C(4,2) = 6` count `KummerHomologyT4.hTwoIndex_card` and the arithmetic form `torusFourForm`. -/
theorem finrank_torusFour_two : Module.finrank ℤ (Homology (TopCat.of TorusFour) 2) = 6 := by
  rw [torusFourH2EquivFin6.finrank_eq, Module.finrank_pi]; simp

/-- **`H₂(T⁴;ℤ) ≅ ⊕_{|s|=2} ℤ`, indexed by pairs of circle factors.** The same rank-6 iso, reindexed
along the banked degree-2 Künneth-index bijection `hTwoIndexEquivFin6` so each `ℤ` summand is
labelled by *which pair `{i,j}` of the four circle factors* its class `dxᵢ ∧ dxⱼ` comes from. -/
noncomputable def torusFourH2EquivPairs :
    Homology (TopCat.of TorusFour) 2 ≃ₗ[ℤ] ({s : Finset (Fin 4) // s.card = 2} → ℤ) :=
  torusFourH2EquivFin6.trans
    (LinearEquiv.piCongrLeft' ℤ (fun _ : {s : Finset (Fin 4) // s.card = 2} => ℤ)
      hTwoIndexEquivFin6).symm

end SKEFTHawking.KummerHomologyT4H2
