import Mathlib
import SKEFTHawking.SingularCapHomology
import SKEFTHawking.SingularCapChainIncl

/-!
# The general homology-level cup–cap adjunction

`PoincareDualityConstruct.fundamentalFunctional_cupH24` is the `m = 2`, `z = [M]`-specific case
`⟨a ∪ b, [M]⟩ = ⟨b, a ⌢ [M]⟩` of the cup–cap adjunction. This file generalizes it to an **arbitrary
homology class** `z` and arbitrary degrees `k, m`:

    ⟨a ∪ b, z⟩ = ⟨b, a ⌢ z⟩,    for a : Hᵏ, b : H^{m+1}, z : H_{k+m+1}.

The chain-level identity `kronecker (cup a b) z = kronecker b (cap a z)`
(`SingularCapChainIncl.kronecker_cup_cap`) is the engine; here it is descended to (co)homology
classes.

## The general right cup `cupRightGeneralH`

The descended cup `cupH`/`cupH24` available on `main` are degree-specific (`(1,1) → 2`, `(2,2) → 4`)
because the *left*-argument descent (`cup_coboundary_left_deg0`, `cup_coboundary_left_1_2`) is only
proven at fixed degrees. The adjunction, however, only needs the cup descended in the *right*
(homology-paired) argument, with the left cohomology class carried as a fixed cocycle representative
— and the right-argument descent (`cup_coboundary_right`) is general in `(p, q)`. So we build a
general `cupRightGeneralH (a : ker δₖ) : H^{m} → H^{k+m}` (mirroring `cupRightH`) and state the
headline with the left class as `Cohomology.mk X k a`. This is fully general in `k` and `m`.
-/

open SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularCapHomology
open SKEFTHawking.SingularCapChainIncl

namespace SKEFTHawking.SingularCupCapHomology

variable {X : TopCat}

/-- For a fixed `k`-**cocycle** `a` (`δa = 0`), cup-with-`a` descends to a linear map
`Hᵐ → H^{k+m}`. The cup lands in cocycles (`cup_cocycle`); it kills `Hᵐ`-coboundaries because
`a ⌣ δb = δ(a ⌣ b)` (`cup_coboundary_right`, general in the degrees). The general (in `k, m`)
right-argument analogue of `cupRightH`/`cupRightH24`. -/
noncomputable def cupRightGeneralH {k m : ℕ} (a : LinearMap.ker (coboundaryₗ X k)) :
    Cohomology X m →ₗ[ZMod 2] Cohomology X (k + m) :=
  Submodule.liftQ _
    ((Submodule.mkQ _).comp
      (((cupₗ k m a.1).domRestrict (LinearMap.ker (coboundaryₗ X m))).codRestrict
        (LinearMap.ker (coboundaryₗ X (k + m))) fun gc => by
          rw [LinearMap.mem_ker]
          exact cup_cocycle a.1 gc.1 (LinearMap.mem_ker.mp a.2) (LinearMap.mem_ker.mp gc.2)))
    (by
      intro gc hgc
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at hgc
      rw [LinearMap.mem_ker]
      change Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
        LinearMap.codRestrict_apply, LinearMap.domRestrict_apply, cupₗ_apply]
      cases m with
      | zero =>
          rw [show coboundaryRange X 0 = (⊥ : Submodule (ZMod 2) (SingularCochain X 0)) from rfl,
            Submodule.mem_bot] at hgc
          rw [show (gc.1 : SingularCochain X 0) = 0 from hgc, ← cupₗ_apply, map_zero]
          exact Submodule.zero_mem _
      | succ j =>
          rw [show coboundaryRange X (j + 1) = LinearMap.range (coboundaryₗ X j) from rfl] at hgc
          obtain ⟨b, hb⟩ := hgc
          rw [show coboundaryRange X (k + (j + 1)) = LinearMap.range (coboundaryₗ X (k + j)) from rfl]
          refine ⟨cup a.1 b, ?_⟩
          rw [cup_coboundary_right a.1 b (LinearMap.mem_ker.mp a.2), hb])

/-- The computation rule for `cupRightGeneralH` on a representative cocycle `gc`. -/
@[simp] theorem cupRightGeneralH_apply_mk {k m : ℕ}
    (a : LinearMap.ker (coboundaryₗ X k)) (gc : LinearMap.ker (coboundaryₗ X m)) :
    cupRightGeneralH a (Cohomology.mk X m gc)
      = Cohomology.mk X (k + m) (⟨cup a.1 gc.1, cup_cocycle a.1 gc.1
          (LinearMap.mem_ker.mp a.2) (LinearMap.mem_ker.mp gc.2)⟩ :
          LinearMap.ker (coboundaryₗ X (k + m))) :=
  rfl

/-- **The general homology-level cup–cap adjunction** `⟨a ∪ b, z⟩ = ⟨b, a ⌢ z⟩`. -/
theorem kroneckerH_capH_cupRightGeneralH {k m : ℕ}
    (a : LinearMap.ker (coboundaryₗ X k)) (b : Cohomology X (m + 1))
    (z : Homology X (k + m + 1)) :
    kroneckerH (X := X) (m + 1) b (capH k m (Cohomology.mk X k a) z)
      = kroneckerH (X := X) (k + (m + 1)) (cupRightGeneralH a b) z := by
  obtain ⟨fb, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  obtain ⟨zc, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  -- Both `capH` and `cupRightGeneralH` compute on representatives (`capH_mk_mk`,
  -- `cupRightGeneralH_apply_mk` are `rfl`); after `kroneckerH_mk_mk` and `capCyclesₗ_coe` the
  -- goal is the chain-level adjunction `kronecker (cup a b) z = kronecker b (cap a z)`.
  show kroneckerH (m + 1) (Cohomology.mk X (m + 1) fb) (Homology.mk X (m + 1) (capCyclesₗ a zc))
      = kroneckerH (k + (m + 1)) (Cohomology.mk X (k + (m + 1))
          ⟨cup a.1 fb.1, cup_cocycle a.1 fb.1
            (LinearMap.mem_ker.mp a.2) (LinearMap.mem_ker.mp fb.2)⟩) (Homology.mk X (k + m + 1) zc)
  simp only [Cohomology.mk, Homology.mk, kroneckerH_mk_mk, capCyclesₗ_coe]
  exact (kronecker_cup_cap a.1 fb.1 zc.1).symm

end SKEFTHawking.SingularCupCapHomology
