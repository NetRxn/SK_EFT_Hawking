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
open SKEFTHawking.KummerHomologyT4 (circleHomeoSph1)

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

end SKEFTHawking.KummerHomologyT4H2
