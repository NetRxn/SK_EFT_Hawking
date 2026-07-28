/-
# The pair-restriction leg vanishes on the subspace: `ι_S* ∘ j* = 0` over `ℤ`

`SingularRelativeCohomDeltaInt.relToAbsInt` is the forgetful leg `j* : Hᵐ(X, S; ℤ) → Hᵐ(X; ℤ)` of
the pair long exact sequence. This module supplies the *other half* of exactness at `Hᵐ(X;ℤ)` that
support arguments actually consume: **the composite with restriction to `S` is zero**.

It is elementary and entirely cochain-level: a relative cochain is by definition one that kills every
chain supported in `S` (`relCochainsInt S n = {f | ∀ c ∈ subspaceChainsInt S n, ⟨f, c⟩ = 0}`), and a
singular cochain *is* a function on simplices, so killing all the single-simplex chains of `S` is the
same as being the zero function after pullback along `S ↪ X`.

Consumed by `KummerK3ExceptionalRestriction`: a class supplied as a *relative* class on
`(K3, K3 ∖ E_d)` — which is what a Thom class of the `d`-th resolution piece is — automatically
satisfies the support hypothesis of `restrictToPiece_eq_zero_of_vanishes_off`, so the whole
off-diagonal of the `⟨−2⟩¹⁶` block follows with no further input.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.SingularRelativeCohomDeltaInt
import SKEFTHawking.SingularCohomologyFunctorialityInt

namespace SKEFTHawking.SingularRelativeVanishOnSubspace

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularCohomologyFunctorialityInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularRelativeCohomDeltaInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub inclMap simplexIncl)

noncomputable section

variable {X : TopCat} (S : Set ↑X)

/-- The subspace inclusion as a `ContinuousMap` — the shape `cochainPullbackInt` consumes. -/
def inclCM : C(↑(sub S), ↑X) := ⟨Subtype.val, continuous_subtype_val⟩

/-- **A relative cochain pulls back to `0` on the subspace.** A singular cochain is a function on
simplices, and every simplex of `S` pushes to a single-simplex chain lying in `subspaceChainsInt S`,
which a relative cochain kills by definition. -/
theorem cochainPullbackInt_eq_zero_of_mem_relCochainsInt {n : ℕ} (f : SingularCochainInt X n)
    (hf : f ∈ relCochainsInt S n) :
    cochainPullbackInt (inclCM S) n f = 0 := by
  funext σ
  have hmem : chainIncl S n (Finsupp.single σ (1 : ℤ)) ∈ subspaceChainsInt S n :=
    ⟨Finsupp.single σ 1, rfl⟩
  have := hf _ hmem
  rw [chainIncl, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single] at this
  simpa [kronecker, Finsupp.sum_single_index] using this

/-- **`ι_S* ∘ j* = 0`.** Every class in the image of the pair-restriction leg
`j* : Hᵐ(X, S; ℤ) → Hᵐ(X; ℤ)` restricts to `0` on `S`. This is the half of exactness at `Hᵐ(X;ℤ)`
that support arguments consume: a class supplied *relatively* automatically vanishes on the
subspace, with nothing further to check. -/
theorem cohomologyPullbackInt_relToAbsInt {m : ℕ} (x : RelativeCohomologyInt S m) :
    cohomologyPullbackInt (inclCM S) m (relToAbsInt x) = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [show (Submodule.Quotient.mk a : RelativeCohomologyInt S m)
      = RelativeCohomologyInt.mk S m a from rfl, relToAbsInt_mk, cohomologyPullbackInt_mk]
  have hz : cochainPullbackInt (inclCM S) m
      ((relToAbsCocycleIntₗ a : LinearMap.ker (coboundaryₗ X m)) : SingularCochainInt X m) = 0 := by
    rw [relToAbsCocycleIntₗ_coe]
    exact cochainPullbackInt_eq_zero_of_mem_relCochainsInt S a.1.1 a.1.2
  have hzero : (⟨cochainPullbackInt (inclCM S) m
      ((relToAbsCocycleIntₗ a : LinearMap.ker (coboundaryₗ X m)) : SingularCochainInt X m),
      cochainPullbackInt_mem_ker (inclCM S) (relToAbsCocycleIntₗ a)⟩ :
        LinearMap.ker (coboundaryₗ (sub S) m)) = 0 := Subtype.ext hz
  rw [hzero]
  exact Submodule.Quotient.mk_zero _

end

end SKEFTHawking.SingularRelativeVanishOnSubspace
