/-
# Phase 5q.H (E1 CSC-PD tower) — integral relative cohomology rel the empty subspace

`RelativeCohomologyInt (∅ : Set X) n ≃ₗ[ℤ] Cohomology X n`: the cohomology dual of
`SingularRelativeEmptyInt.relHomologyEmptyEquivInt`, the bridge `Hⁱ(M|M) = Hⁱ(M,∅;ℤ) ≅ Hⁱ(M;ℤ)` under
which `D_univ` becomes `capHInt · [M]`. Mechanism: `subspaceChainsInt ∅ n = ⊥`, so `relCochainsInt ∅ n
= ⊤`, and `relCoboundaryIntₗ ↔ coboundaryₗ` (`relCoboundaryIntₗ_coe`), so cocycles/coboundaries
correspond and the cohomology subquotients are linearly equivalent. Integral mirror of
`SingularRelativeCohomologyEmpty`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularEuclideanCapIsoInt
import SKEFTHawking.SingularRelativeEmptyInt

open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularRelativeEmptyInt

namespace SKEFTHawking.SingularRelativeCohomologyEmptyInt

variable {X : TopCat}

/-! ## §1. Every cochain is a relative `∅`-cochain: `relCochainsInt ∅ n = ⊤` -/

/-- **Key fact**: `relCochainsInt (∅ : Set X) n = ⊤` — every cochain vanishes on
`subspaceChainsInt ∅ n = ⊥`. -/
theorem relCochainsInt_empty_eq_top (n : ℕ) : relCochainsInt (∅ : Set X) n = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro f c hc
  rw [subspaceChainsInt_empty_eq_bot, Submodule.mem_bot] at hc
  subst hc
  simp

/-- The relative cochains rel the empty subspace are the absolute cochains: `Cⁿ(X, ∅;ℤ) ≃ Cⁿ(X;ℤ)`. -/
noncomputable def cochainEmptyEquivInt (n : ℕ) :
    relCochainsInt (∅ : Set X) n ≃ₗ[ℤ] SingularCochainInt X n :=
  (LinearEquiv.ofEq _ _ (relCochainsInt_empty_eq_top n)).trans Submodule.topEquiv

@[simp] theorem cochainEmptyEquivInt_apply (n : ℕ) (f : relCochainsInt (∅ : Set X) n) :
    cochainEmptyEquivInt n f = (f : SingularCochainInt X n) :=
  rfl

/-- The coboundary intertwiner: `cochainEmptyEquivInt` carries the relative coboundary to the absolute
coboundary, `e ∘ δ_rel = δ ∘ e` (both restrict the absolute `coboundaryₗ`, `relCoboundaryIntₗ_coe`). -/
theorem cochainEmptyEquivInt_relCoboundary (n : ℕ) (f : relCochainsInt (∅ : Set X) n) :
    cochainEmptyEquivInt (n + 1) (relCoboundaryIntₗ (∅ : Set X) n f)
      = coboundaryₗ X n (cochainEmptyEquivInt n f) := by
  rw [cochainEmptyEquivInt_apply, cochainEmptyEquivInt_apply, relCoboundaryIntₗ_coe]
  rfl

/-! ## §2. Cocycles and coboundaries correspond; the cohomology equivalence -/

/-- `cochainEmptyEquivInt` carries the relative cocycles onto the absolute cocycles. -/
theorem map_cochainEmptyEquivInt_ker (n : ℕ) :
    Submodule.map (cochainEmptyEquivInt (X := X) n).toLinearMap
        (LinearMap.ker (relCoboundaryIntₗ (∅ : Set X) n))
      = LinearMap.ker (coboundaryₗ X n) := by
  ext f
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [← cochainEmptyEquivInt_relCoboundary, hg, map_zero]
  · intro hf
    refine ⟨(cochainEmptyEquivInt n).symm f, ?_, by simp⟩
    apply (cochainEmptyEquivInt (n + 1)).injective
    rw [cochainEmptyEquivInt_relCoboundary, map_zero, LinearEquiv.apply_symm_apply, hf]

/-- `cochainEmptyEquivInt` carries the relative coboundary range onto the absolute coboundary range. -/
theorem map_cochainEmptyEquivInt_coboundaryRange (n : ℕ) :
    Submodule.map (cochainEmptyEquivInt (X := X) n).toLinearMap (relCoboundaryRangeInt (∅ : Set X) n)
      = coboundaryRange X n := by
  cases n with
  | zero =>
    rw [show relCoboundaryRangeInt (∅ : Set X) 0 = (⊥ : Submodule ℤ (relCochainsInt (∅ : Set X) 0))
        from rfl,
      show coboundaryRange X 0 = (⊥ : Submodule ℤ (SingularCochainInt X 0)) from rfl,
      Submodule.map_bot]
  | succ m =>
    ext f
    simp only [show relCoboundaryRangeInt (∅ : Set X) (m + 1) = LinearMap.range (relCoboundaryIntₗ (∅ : Set X) m)
        from rfl,
      show coboundaryRange X (m + 1) = LinearMap.range (coboundaryₗ X m) from rfl,
      Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨cochainEmptyEquivInt m g, (cochainEmptyEquivInt_relCoboundary m g).symm⟩
    · rintro ⟨g, rfl⟩
      exact ⟨relCoboundaryIntₗ (∅ : Set X) m ((cochainEmptyEquivInt m).symm g),
        ⟨(cochainEmptyEquivInt m).symm g, rfl⟩,
        by rw [cochainEmptyEquivInt_relCoboundary, LinearEquiv.apply_symm_apply]⟩

/-- The restriction of `cochainEmptyEquivInt` to the cocycles:
`ker (relCoboundaryIntₗ ∅ n) ≃ₗ ker (coboundaryₗ X n)`. -/
noncomputable def cocyclesEmptyEquivInt (n : ℕ) :
    LinearMap.ker (relCoboundaryIntₗ (∅ : Set X) n) ≃ₗ[ℤ] LinearMap.ker (coboundaryₗ X n) :=
  ((cochainEmptyEquivInt (X := X) n).submoduleMap
      (LinearMap.ker (relCoboundaryIntₗ (∅ : Set X) n))).trans
    (LinearEquiv.ofEq _ _ (map_cochainEmptyEquivInt_ker n))

theorem cocyclesEmptyEquivInt_coe (n : ℕ) (z : LinearMap.ker (relCoboundaryIntₗ (∅ : Set X) n)) :
    (cocyclesEmptyEquivInt n z : SingularCochainInt X n)
      = cochainEmptyEquivInt n (z : relCochainsInt (∅ : Set X) n) :=
  rfl

/-- **`RelativeCohomologyInt (∅ : Set X) n ≃ₗ[ℤ] Cohomology X n`** — integral relative singular
cohomology rel the empty subspace equals absolute cohomology. The cohomology dual of
`relHomologyEmptyEquivInt`; the bridge `Hⁱ(M|M) ≅ Hⁱ(M)` under which `D_univ` becomes `capHInt · [M]`. -/
noncomputable def relCohomologyEmptyEquivInt (n : ℕ) :
    RelativeCohomologyInt (∅ : Set X) n ≃ₗ[ℤ] Cohomology X n :=
  Submodule.Quotient.equiv
    ((relCoboundaryRangeInt (∅ : Set X) n).submoduleOf
      (LinearMap.ker (relCoboundaryIntₗ (∅ : Set X) n)))
    ((coboundaryRange X n).submoduleOf (LinearMap.ker (coboundaryₗ X n)))
    (cocyclesEmptyEquivInt n)
    (by
      ext z
      simp only [Submodule.mem_map, Submodule.submoduleOf, Submodule.mem_comap,
        Submodule.coe_subtype]
      constructor
      · rintro ⟨w, hw, rfl⟩
        show cochainEmptyEquivInt n (w : relCochainsInt (∅ : Set X) n) ∈ coboundaryRange X n
        have hmap : cochainEmptyEquivInt n (w : relCochainsInt (∅ : Set X) n)
            ∈ Submodule.map (cochainEmptyEquivInt (X := X) n).toLinearMap
                (relCoboundaryRangeInt (∅ : Set X) n) :=
          ⟨_, hw, rfl⟩
        rwa [map_cochainEmptyEquivInt_coboundaryRange] at hmap
      · intro hz
        refine ⟨(cocyclesEmptyEquivInt n).symm z, ?_, by simp⟩
        show ((cocyclesEmptyEquivInt n).symm z : relCochainsInt (∅ : Set X) n)
          ∈ relCoboundaryRangeInt (∅ : Set X) n
        have hzc : (z : SingularCochainInt X n) ∈ coboundaryRange X n := hz
        rw [← map_cochainEmptyEquivInt_coboundaryRange] at hzc
        obtain ⟨w, hw, hwz⟩ := hzc
        have heq : ((cocyclesEmptyEquivInt n).symm z : relCochainsInt (∅ : Set X) n) = w := by
          apply (cochainEmptyEquivInt n).injective
          show cochainEmptyEquivInt n ((cocyclesEmptyEquivInt n).symm z : relCochainsInt (∅ : Set X) n)
            = cochainEmptyEquivInt n w
          have h1 : (cochainEmptyEquivInt n) w = (z : SingularCochainInt X n) := hwz
          rw [h1]
          exact congrArg Subtype.val (LinearEquiv.apply_symm_apply (cocyclesEmptyEquivInt n) z)
        rw [heq]; exact hw)

/-- The computation rule: `relCohomologyEmptyEquivInt` sends the relative class of a relative cocycle
`z` to the absolute class of the corresponding absolute cocycle `cocyclesEmptyEquivInt n z`. -/
theorem relCohomologyEmptyEquivInt_mk (n : ℕ) (z : LinearMap.ker (relCoboundaryIntₗ (∅ : Set X) n)) :
    relCohomologyEmptyEquivInt n (RelativeCohomologyInt.mk (∅ : Set X) n z)
      = Cohomology.mk X n (cocyclesEmptyEquivInt n z) :=
  rfl

end SKEFTHawking.SingularRelativeCohomologyEmptyInt
