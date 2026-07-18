/-
# Phase 5q.H — Kummer full integral homology of `T⁴` + the orientation class

Completes the integral homology `H_*(T⁴;ℤ)` for the project's custom `SingularHomologyInt.Homology`,
extending the banked degree-0 (`KummerH0T4.torusFourH0EquivInt : H₀ ≅ ℤ`) and degree-2
(`KummerHomologyT4H2.torusFourH2EquivFin6 : H₂ ≅ ℤ⁶`) with the remaining three groups and the
top/orientation class, all by iterating the reusable circle-product step lemmas of `KummerTorusStep`
up the tower `T² → T³ → T⁴` (`Tor Y := ProdSp Y (Sph 1)`, `TwoTorus = Tor (Sph 1)` definitionally):

* `H₁(T⁴;ℤ) ≅ ℤ⁴`  (`C(4,1) = 4`) — the degree-1 step iterated (`H₁(T²)=2 → H₁(T³)=3 → H₁(T⁴)=4`).
* `H₃(T⁴;ℤ) ≅ ℤ⁴`  (`C(4,3) = 4`) — the positive step at `k=1` (`H₃(Y×S¹)=H₃(Y)+H₂(Y)`).
* `H₄(T⁴;ℤ) ≅ ℤ`   (`C(4,4) = 1`) — the top class, the positive step at `k=2`.
* the **fundamental / orientation class** `[T⁴]` — the chosen generator `torusFourH4EquivInt.symm 1`
  of the rank-1 `H₄`, nonzero and generating (`= ⊤`).

The seed for the higher T² groups is the circle's vanishing above degree 1
(`KummerHomologyT4.circleH_high : H_{k+2}(S¹) = 0`), packaged here as the trivial-module facts
`free_finite_rank_zero_of_subsingleton`. All isos are genuine `≃ₗ[ℤ]` of the honest rank
(free-finite bases of the Mayer–Vietoris-computed homology), transported onto the actual
`TorusFour = Circle⁴` across the banked reassociation homeomorphism
`KummerHomologyT4H2.fourStepHomeoTorusFour` — not defined-to-be-`ℤⁿ` shells.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.KummerHomologyT4H2
import SKEFTHawking.KummerH0T4

namespace SKEFTHawking.KummerHomologyT4Full

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.SingularProdContractibleInt (homeoHomologyEquivInt)
open SKEFTHawking.KummerTorusStep (Tor stepPos_free_finrank stepDeg1_free_finrank)
open SKEFTHawking.KummerHomologyT2 (TwoTorus)
open SKEFTHawking.KummerHomologyT4 (circleH_high circleHomeoSph1)
open SKEFTHawking.KummerHomologyT4H2 (fourStepHomeoTorusFour)
open SKEFTHawking.KummerK3Base (TorusFour)

/-! ## §0. The trivial (subsingleton) `ℤ`-module: free, finite, rank 0 -/

/-- A subsingleton `ℤ`-module is free and finite of rank `0` — the trivial module, realized as the
empty-index free module `Fin 0 → ℤ`. The seed for every vanishing homology group used below. -/
theorem free_finite_rank_zero_of_subsingleton (M : Type) [AddCommGroup M] [Module ℤ M]
    [Subsingleton M] :
    Module.Free ℤ M ∧ Module.Finite ℤ M ∧ Module.finrank ℤ M = 0 := by
  have e : M ≃ₗ[ℤ] (Fin 0 → ℤ) :=
    LinearEquiv.ofBijective (0 : M →ₗ[ℤ] (Fin 0 → ℤ))
      ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  refine ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, Module.finrank_fin_fun]

/-- **The circle's high homology is a trivial module** — `H_{k+2}(S¹;ℤ)` is free finite of rank `0`
(everything is `0` by `circleH_high`). The seed for `H₃(T²) = H₄(T²) = 0`. -/
theorem circle_high_free_finite (k : ℕ) :
    Module.Free ℤ (Homology (Sph 1) (k + 2)) ∧ Module.Finite ℤ (Homology (Sph 1) (k + 2)) ∧
      Module.finrank ℤ (Homology (Sph 1) (k + 2)) = 0 := by
  haveI : Subsingleton (Homology (Sph 1) (k + 2)) :=
    ⟨fun a b => by rw [circleH_high k a, circleH_high k b]⟩
  exact free_finite_rank_zero_of_subsingleton _

/-! ## §1. `T²` high degrees: `H₃(T²) = H₄(T²) = 0` (via the circle step on `Sph 1`) -/

/-- **`H₃(T²;ℤ) = 0`** (free finite rank `0`) — `TwoTorus = Tor (Sph 1)`, so the positive step at
`k=1` gives `H₃(T²) = H₃(S¹) + H₂(S¹) = 0 + 0`. -/
theorem twoTorus_three_free_finite :
    Module.Free ℤ (Homology TwoTorus 3) ∧ Module.Finite ℤ (Homology TwoTorus 3) ∧
      Module.finrank ℤ (Homology TwoTorus 3) = 0 := by
  have h := stepPos_free_finrank (Sph 1) 1
    (circle_high_free_finite 1).1 (circle_high_free_finite 1).2.1
    (circle_high_free_finite 0).1 (circle_high_free_finite 0).2.1
  have hfree : Module.Free ℤ (Homology TwoTorus 3) := h.1
  have hfin : Module.Finite ℤ (Homology TwoTorus 3) := h.2.1
  have hrank : Module.finrank ℤ (Homology TwoTorus 3)
      = Module.finrank ℤ (Homology (Sph 1) 3) + Module.finrank ℤ (Homology (Sph 1) 2) := h.2.2
  refine ⟨hfree, hfin, ?_⟩
  rw [hrank, (circle_high_free_finite 1).2.2, (circle_high_free_finite 0).2.2]

/-- **`H₄(T²;ℤ) = 0`** (free finite rank `0`) — the positive step at `k=2` gives
`H₄(T²) = H₄(S¹) + H₃(S¹) = 0 + 0`. -/
theorem twoTorus_four_free_finite :
    Module.Free ℤ (Homology TwoTorus 4) ∧ Module.Finite ℤ (Homology TwoTorus 4) ∧
      Module.finrank ℤ (Homology TwoTorus 4) = 0 := by
  have h := stepPos_free_finrank (Sph 1) 2
    (circle_high_free_finite 2).1 (circle_high_free_finite 2).2.1
    (circle_high_free_finite 1).1 (circle_high_free_finite 1).2.1
  have hfree : Module.Free ℤ (Homology TwoTorus 4) := h.1
  have hfin : Module.Finite ℤ (Homology TwoTorus 4) := h.2.1
  have hrank : Module.finrank ℤ (Homology TwoTorus 4)
      = Module.finrank ℤ (Homology (Sph 1) 4) + Module.finrank ℤ (Homology (Sph 1) 3) := h.2.2
  refine ⟨hfree, hfin, ?_⟩
  rw [hrank, (circle_high_free_finite 2).2.2, (circle_high_free_finite 1).2.2]

/-! ## §2. `T³ = T² × S¹` high degrees: `H₃(T³) ≅ ℤ`, `H₄(T³) = 0` -/

/-- **`H₃(T³;ℤ) ≅ ℤ`** (free finite rank `1`) — the positive step at `k=1`,
`H₃(T³) = H₃(T²) + H₂(T²) = 0 + 1`. -/
theorem threeTorus_three_free_finite :
    Module.Free ℤ (Homology (Tor TwoTorus) 3) ∧ Module.Finite ℤ (Homology (Tor TwoTorus) 3) ∧
      Module.finrank ℤ (Homology (Tor TwoTorus) 3) = 1 := by
  have h := stepPos_free_finrank TwoTorus 1
    twoTorus_three_free_finite.1 twoTorus_three_free_finite.2.1
    (inferInstanceAs (Module.Free ℤ (Homology TwoTorus 2)))
    (inferInstanceAs (Module.Finite ℤ (Homology TwoTorus 2)))
  have hfree : Module.Free ℤ (Homology (Tor TwoTorus) 3) := h.1
  have hfin : Module.Finite ℤ (Homology (Tor TwoTorus) 3) := h.2.1
  have hrank : Module.finrank ℤ (Homology (Tor TwoTorus) 3)
      = Module.finrank ℤ (Homology TwoTorus 3) + Module.finrank ℤ (Homology TwoTorus 2) := h.2.2
  refine ⟨hfree, hfin, ?_⟩
  rw [hrank, twoTorus_three_free_finite.2.2, KummerHomologyT4H2.finrank_twoTorus_two]

/-- **`H₄(T³;ℤ) = 0`** (free finite rank `0`) — the positive step at `k=2`,
`H₄(T³) = H₄(T²) + H₃(T²) = 0 + 0`. -/
theorem threeTorus_four_free_finite :
    Module.Free ℤ (Homology (Tor TwoTorus) 4) ∧ Module.Finite ℤ (Homology (Tor TwoTorus) 4) ∧
      Module.finrank ℤ (Homology (Tor TwoTorus) 4) = 0 := by
  have h := stepPos_free_finrank TwoTorus 2
    twoTorus_four_free_finite.1 twoTorus_four_free_finite.2.1
    twoTorus_three_free_finite.1 twoTorus_three_free_finite.2.1
  have hfree : Module.Free ℤ (Homology (Tor TwoTorus) 4) := h.1
  have hfin : Module.Finite ℤ (Homology (Tor TwoTorus) 4) := h.2.1
  have hrank : Module.finrank ℤ (Homology (Tor TwoTorus) 4)
      = Module.finrank ℤ (Homology TwoTorus 4) + Module.finrank ℤ (Homology TwoTorus 3) := h.2.2
  refine ⟨hfree, hfin, ?_⟩
  rw [hrank, twoTorus_four_free_finite.2.2, twoTorus_three_free_finite.2.2]

/-! ## §3. `H₄(T⁴;ℤ) ≅ ℤ` — the top class, and the fundamental / orientation class `[T⁴]` -/

/-- The `H₄(T⁴)` step result (`stepPos` at `Y = T³`, `k = 2`), `H₄(T⁴) = H₄(T³) + H₃(T³) = 0 + 1`. -/
theorem fourTorus_four_free_finite :
    Module.Free ℤ (Homology (Tor (Tor TwoTorus)) 4)
      ∧ Module.Finite ℤ (Homology (Tor (Tor TwoTorus)) 4)
      ∧ Module.finrank ℤ (Homology (Tor (Tor TwoTorus)) 4) = 1 := by
  have h := stepPos_free_finrank (Tor TwoTorus) 2
    threeTorus_four_free_finite.1 threeTorus_four_free_finite.2.1
    threeTorus_three_free_finite.1 threeTorus_three_free_finite.2.1
  have hfree : Module.Free ℤ (Homology (Tor (Tor TwoTorus)) 4) := h.1
  have hfin : Module.Finite ℤ (Homology (Tor (Tor TwoTorus)) 4) := h.2.1
  have hrank : Module.finrank ℤ (Homology (Tor (Tor TwoTorus)) 4)
      = Module.finrank ℤ (Homology (Tor TwoTorus) 4)
        + Module.finrank ℤ (Homology (Tor TwoTorus) 3) := h.2.2
  refine ⟨hfree, hfin, ?_⟩
  rw [hrank, threeTorus_four_free_finite.2.2, threeTorus_three_free_finite.2.2]

noncomputable instance : Module.Free ℤ (Homology (Tor (Tor TwoTorus)) 4) :=
  fourTorus_four_free_finite.1

noncomputable instance : Module.Finite ℤ (Homology (Tor (Tor TwoTorus)) 4) :=
  fourTorus_four_free_finite.2.1

/-- **`finrank H₄(T⁴) = 1`** on the step-tower carrier `Tor (Tor T²)` — the `C(4,4) = 1` top class. -/
theorem finrank_fourStep_four : Module.finrank ℤ (Homology (Tor (Tor TwoTorus)) 4) = 1 :=
  fourTorus_four_free_finite.2.2

/-- **`H₄(T⁴;ℤ) ≅ ℤ`** on the step-tower carrier `Tor (Tor T²)` — a genuine rank-1 `≃ₗ[ℤ]`, the
free-finite basis of the honestly-computed degree-4 homology (the top / orientation line). -/
noncomputable def fourStepH4EquivInt : Homology (Tor (Tor TwoTorus)) 4 ≃ₗ[ℤ] ℤ :=
  ((Module.finBasis ℤ (Homology (Tor (Tor TwoTorus)) 4)).reindex
    (finCongr finrank_fourStep_four)).equivFun.trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ)

/-- **`H₄(T⁴;ℤ) ≅ ℤ` — on the actual `TorusFour = Circle⁴`.** A genuine rank-1 `≃ₗ[ℤ]` (the top
class), transported from the step-tower carrier across the banked reassociation homeomorphism
`fourStepHomeoTorusFour`. -/
noncomputable def torusFourH4EquivInt : Homology (TopCat.of TorusFour) 4 ≃ₗ[ℤ] ℤ :=
  (homeoHomologyEquivInt (X := TopCat.of TorusFour) (Y := Tor (Tor TwoTorus))
    fourStepHomeoTorusFour.symm 4).trans fourStepH4EquivInt

/-- **`finrank H₄(TorusFour) = 1`** — the honest rank pin on the actual `T⁴ = Circle⁴`, matching
`C(4,4) = 1`. -/
theorem finrank_torusFour_four : Module.finrank ℤ (Homology (TopCat.of TorusFour) 4) = 1 := by
  rw [torusFourH4EquivInt.finrank_eq, Module.finrank_self]

/-- **The fundamental / orientation class `[T⁴]`** — the chosen generator of `H₄(T⁴;ℤ) ≅ ℤ`, the
preimage of `1 : ℤ` under `torusFourH4EquivInt`. The oriented top class the Kummer quotient /
resolution needs. -/
noncomputable def torusFourFundamentalClass : Homology (TopCat.of TorusFour) 4 :=
  torusFourH4EquivInt.symm 1

/-- The fundamental class reads `1` under the degree-4 iso — the defining normalization of `[T⁴]`. -/
theorem torusFourH4EquivInt_fundamentalClass :
    torusFourH4EquivInt torusFourFundamentalClass = 1 := by
  rw [torusFourFundamentalClass, LinearEquiv.apply_symm_apply]

/-- **`[T⁴] ≠ 0`** — the orientation class is nontrivial (it reads `1 ≠ 0`). -/
theorem torusFourFundamentalClass_ne_zero : torusFourFundamentalClass ≠ 0 := by
  intro h0
  have h1 := torusFourH4EquivInt_fundamentalClass
  rw [h0, map_zero] at h1
  exact one_ne_zero h1.symm

/-- **`[T⁴]` generates `H₄(T⁴;ℤ)`** — it spans the whole rank-1 group (`= ⊤`), so it is a genuine
orientation generator, not merely a nonzero class. -/
theorem torusFourFundamentalClass_generates :
    Submodule.span ℤ {torusFourFundamentalClass} = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  rw [Submodule.mem_span_singleton]
  refine ⟨torusFourH4EquivInt x, ?_⟩
  rw [torusFourFundamentalClass, ← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]

/-! ## §4. `H₃(T⁴;ℤ) ≅ ℤ⁴`  (`C(4,3) = 4`) -/

/-- The `H₃(T⁴)` step result (`stepPos` at `Y = T³`, `k = 1`), `H₃(T⁴) = H₃(T³) + H₂(T³) = 1 + 3`. -/
theorem fourTorus_three_free_finite :
    Module.Free ℤ (Homology (Tor (Tor TwoTorus)) 3)
      ∧ Module.Finite ℤ (Homology (Tor (Tor TwoTorus)) 3)
      ∧ Module.finrank ℤ (Homology (Tor (Tor TwoTorus)) 3) = 4 := by
  have h := stepPos_free_finrank (Tor TwoTorus) 1
    threeTorus_three_free_finite.1 threeTorus_three_free_finite.2.1
    (inferInstanceAs (Module.Free ℤ (Homology (Tor TwoTorus) 2)))
    (inferInstanceAs (Module.Finite ℤ (Homology (Tor TwoTorus) 2)))
  have hfree : Module.Free ℤ (Homology (Tor (Tor TwoTorus)) 3) := h.1
  have hfin : Module.Finite ℤ (Homology (Tor (Tor TwoTorus)) 3) := h.2.1
  have hrank : Module.finrank ℤ (Homology (Tor (Tor TwoTorus)) 3)
      = Module.finrank ℤ (Homology (Tor TwoTorus) 3)
        + Module.finrank ℤ (Homology (Tor TwoTorus) 2) := h.2.2
  refine ⟨hfree, hfin, ?_⟩
  rw [hrank, threeTorus_three_free_finite.2.2, KummerHomologyT4H2.finrank_threeTorus_two]

noncomputable instance : Module.Free ℤ (Homology (Tor (Tor TwoTorus)) 3) :=
  fourTorus_three_free_finite.1

noncomputable instance : Module.Finite ℤ (Homology (Tor (Tor TwoTorus)) 3) :=
  fourTorus_three_free_finite.2.1

/-- **`finrank H₃(T⁴) = 4`** on the step-tower carrier — the `C(4,3) = 4` classes. -/
theorem finrank_fourStep_three : Module.finrank ℤ (Homology (Tor (Tor TwoTorus)) 3) = 4 :=
  fourTorus_three_free_finite.2.2

/-- **`H₃(T⁴;ℤ) ≅ ℤ⁴`** on the step-tower carrier `Tor (Tor T²)` — a genuine rank-4 `≃ₗ[ℤ]`. -/
noncomputable def fourStepH3EquivFin4 : Homology (Tor (Tor TwoTorus)) 3 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  ((Module.finBasis ℤ (Homology (Tor (Tor TwoTorus)) 3)).reindex
    (finCongr finrank_fourStep_three)).equivFun

/-- **`H₃(T⁴;ℤ) ≅ ℤ⁴` — on the actual `TorusFour = Circle⁴`.** A genuine rank-4 `≃ₗ[ℤ]` (`C(4,3) = 4`
classes `dxᵢ∧dxⱼ∧dxₖ`), transported across the banked reassociation homeomorphism. -/
noncomputable def torusFourH3EquivFin4 : Homology (TopCat.of TorusFour) 3 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  (homeoHomologyEquivInt (X := TopCat.of TorusFour) (Y := Tor (Tor TwoTorus))
    fourStepHomeoTorusFour.symm 3).trans fourStepH3EquivFin4

/-- **`finrank H₃(TorusFour) = 4`** — the honest rank pin on the actual `T⁴ = Circle⁴`. -/
theorem finrank_torusFour_three : Module.finrank ℤ (Homology (TopCat.of TorusFour) 3) = 4 := by
  rw [torusFourH3EquivFin4.finrank_eq, Module.finrank_pi]; simp

/-- **The degree-3 Künneth index count `C(4,3) = 4`** — the summands of `H₃((S¹)⁴)` are indexed by
the `3`-element subsets of `{1,2,3,4}` (the three circle factors contributing their `H₁ = ℤ`). -/
theorem hThreeIndex_card : Fintype.card {s : Finset (Fin 4) // s.card = 3} = 4 := by decide

/-- **The degree-3 Künneth-summand index bijection `{3-subsets of Fin 4} ≃ Fin 4`.** -/
noncomputable def hThreeIndexEquivFin4 : {s : Finset (Fin 4) // s.card = 3} ≃ Fin 4 :=
  Fintype.equivFinOfCardEq hThreeIndex_card

/-- **`H₃(T⁴;ℤ) ≅ ⊕_{|s|=3} ℤ`, indexed by triples of circle factors** — each `ℤ` summand labelled
by *which triple `{i,j,k}` of the four circle factors* its class `dxᵢ∧dxⱼ∧dxₖ` comes from. -/
noncomputable def torusFourH3EquivTriples :
    Homology (TopCat.of TorusFour) 3 ≃ₗ[ℤ] ({s : Finset (Fin 4) // s.card = 3} → ℤ) :=
  torusFourH3EquivFin4.trans
    (LinearEquiv.piCongrLeft' ℤ (fun _ : {s : Finset (Fin 4) // s.card = 3} => ℤ)
      hThreeIndexEquivFin4).symm

/-! ## §5. `H₁(T⁴;ℤ) ≅ ℤ⁴`  (`C(4,1) = 4`) -/

/-- `T³ = T² × S¹` is path-connected (product of the path-connected `T²` and `S¹`). -/
instance instPathConnectedThreeTorus : PathConnectedSpace ↑(Tor TwoTorus) := by
  haveI : PathConnectedSpace ↑(Sph 1) := KummerHomologyT2.pathConnected_sph1
  exact SKEFTHawking.SphereProdHOneInt.pathConnectedSpace_prod

/-- The `H₁(T⁴)` step result (`stepDeg1` at `Y = T³`), `H₁(T⁴) = H₁(T³) + 1 = 3 + 1`. -/
theorem fourTorus_one_free_finite :
    Module.Free ℤ (Homology (Tor (Tor TwoTorus)) 1)
      ∧ Module.Finite ℤ (Homology (Tor (Tor TwoTorus)) 1)
      ∧ Module.finrank ℤ (Homology (Tor (Tor TwoTorus)) 1) = 4 := by
  have h := stepDeg1_free_finrank (Tor TwoTorus)
  have hfree : Module.Free ℤ (Homology (Tor (Tor TwoTorus)) 1) := h.1
  have hfin : Module.Finite ℤ (Homology (Tor (Tor TwoTorus)) 1) := h.2.1
  have hrank : Module.finrank ℤ (Homology (Tor (Tor TwoTorus)) 1)
      = Module.finrank ℤ (Homology (Tor TwoTorus) 1) + 1 := h.2.2
  refine ⟨hfree, hfin, ?_⟩
  rw [hrank, KummerHomologyT4H2.finrank_threeTorus_one]

noncomputable instance : Module.Free ℤ (Homology (Tor (Tor TwoTorus)) 1) :=
  fourTorus_one_free_finite.1

noncomputable instance : Module.Finite ℤ (Homology (Tor (Tor TwoTorus)) 1) :=
  fourTorus_one_free_finite.2.1

/-- **`finrank H₁(T⁴) = 4`** on the step-tower carrier — the `C(4,1) = 4` classes `dxᵢ`. -/
theorem finrank_fourStep_one : Module.finrank ℤ (Homology (Tor (Tor TwoTorus)) 1) = 4 :=
  fourTorus_one_free_finite.2.2

/-- **`H₁(T⁴;ℤ) ≅ ℤ⁴`** on the step-tower carrier `Tor (Tor T²)` — a genuine rank-4 `≃ₗ[ℤ]`. -/
noncomputable def fourStepH1EquivFin4 : Homology (Tor (Tor TwoTorus)) 1 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  ((Module.finBasis ℤ (Homology (Tor (Tor TwoTorus)) 1)).reindex
    (finCongr finrank_fourStep_one)).equivFun

/-- **`H₁(T⁴;ℤ) ≅ ℤ⁴` — on the actual `TorusFour = Circle⁴`.** A genuine rank-4 `≃ₗ[ℤ]` (the four
generating loops `dxᵢ`, `C(4,1) = 4`), transported across the banked reassociation homeomorphism. -/
noncomputable def torusFourH1EquivFin4 : Homology (TopCat.of TorusFour) 1 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  (homeoHomologyEquivInt (X := TopCat.of TorusFour) (Y := Tor (Tor TwoTorus))
    fourStepHomeoTorusFour.symm 1).trans fourStepH1EquivFin4

/-- **`finrank H₁(TorusFour) = 4`** — the honest rank pin on the actual `T⁴ = Circle⁴`. -/
theorem finrank_torusFour_one : Module.finrank ℤ (Homology (TopCat.of TorusFour) 1) = 4 := by
  rw [torusFourH1EquivFin4.finrank_eq, Module.finrank_pi]; simp

/-- **The degree-1 Künneth index count `C(4,1) = 4`** — the summands of `H₁((S¹)⁴)` are indexed by
the `1`-element subsets of `{1,2,3,4}` (the single circle factor contributing its `H₁ = ℤ`). -/
theorem hOneIndex_card : Fintype.card {s : Finset (Fin 4) // s.card = 1} = 4 := by decide

/-- **The degree-1 Künneth-summand index bijection `{1-subsets of Fin 4} ≃ Fin 4`.** -/
noncomputable def hOneIndexEquivFin4 : {s : Finset (Fin 4) // s.card = 1} ≃ Fin 4 :=
  Fintype.equivFinOfCardEq hOneIndex_card

/-- **`H₁(T⁴;ℤ) ≅ ⊕_{|s|=1} ℤ`, indexed by the single circle factors** — each `ℤ` summand labelled
by *which factor `{i}`* its generating loop `dxᵢ` comes from. -/
noncomputable def torusFourH1EquivSingles :
    Homology (TopCat.of TorusFour) 1 ≃ₗ[ℤ] ({s : Finset (Fin 4) // s.card = 1} → ℤ) :=
  torusFourH1EquivFin4.trans
    (LinearEquiv.piCongrLeft' ℤ (fun _ : {s : Finset (Fin 4) // s.card = 1} => ℤ)
      hOneIndexEquivFin4).symm

/-! ## §6. The full integral homology of `T⁴` — the Betti row `(1,4,6,4,1)` -/

/-- **`finrank H₀(TorusFour) = 1`** — from the banked degree-0 iso `KummerH0T4.torusFourH0EquivInt`
(`T⁴` is path-connected, one component). -/
theorem finrank_torusFour_zero : Module.finrank ℤ (Homology (TopCat.of TorusFour) 0) = 1 := by
  rw [KummerH0T4.torusFourH0EquivInt.finrank_eq, Module.finrank_self]

/-- **The full integral homology of `T⁴ = Circle⁴`, as its Betti row `(b₀,…,b₄) = (1,4,6,4,1)`** —
the row of binomials `C(4,k)`. Consolidates the five degree-wise honest rank pins (`H₀` banked in
`KummerH0T4`, `H₂` banked in `KummerHomologyT4H2`, `H₁`/`H₃`/`H₄` here) into one falsifiable
statement; every `H_k` above is a genuine `≃ₗ[ℤ]` of the stated rank, not a defined-to-be-`ℤⁿ`
shell. -/
theorem torusFour_betti :
    Module.finrank ℤ (Homology (TopCat.of TorusFour) 0) = 1 ∧
      Module.finrank ℤ (Homology (TopCat.of TorusFour) 1) = 4 ∧
        Module.finrank ℤ (Homology (TopCat.of TorusFour) 2) = 6 ∧
          Module.finrank ℤ (Homology (TopCat.of TorusFour) 3) = 4 ∧
            Module.finrank ℤ (Homology (TopCat.of TorusFour) 4) = 1 :=
  ⟨finrank_torusFour_zero, finrank_torusFour_one, KummerHomologyT4H2.finrank_torusFour_two,
    finrank_torusFour_three, finrank_torusFour_four⟩

end SKEFTHawking.KummerHomologyT4Full
