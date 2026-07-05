/-
# Phase 5q.H (E1 integral topology) — the relative Kronecker pairing is an ISO `relCochains ≅ Hom(RC,ℤ)`

The integral relative Kronecker pairing `relKroneckerIntₗ : relCochainsInt S n →ₗ (RelativeChainInt S n
→ₗ ℤ)` (wt1's `SingularRelativeUCInt`) is a **linear isomorphism**: SURJECTIVE (`exists_relCochainInt_of_
functional` — every relative-chain functional is realized by a relative cochain, unconditional) and
INJECTIVE (a relative cochain pairing to `0` with every relative chain is `0`, since a cochain is
determined by its values on the basis simplices, `kronecker f (single σ 1) = f σ`).

This identifies the relative COchain complex with `Hom(RC, ℤ)`, the input to the field-UC-free
Hom-dualization of the (split, `SingularRelativeMVSplitInt`) relative-homology MV chain SES → the
relative-cohomology Mayer–Vietoris.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularRelativeUCInt

open SKEFTHawking.SingularHomologyInt SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularRelativeUCInt

namespace SKEFTHawking.SingularRelativeKroneckerEquivInt

variable {X : TopCat} (S : Set X)

/-- **The relative Kronecker pairing is injective**: a relative cochain pairing to `0` with every
relative chain is `0` (a cochain is determined by its values on the basis simplices). -/
theorem relKroneckerIntₗ_injective {n : ℕ} :
    Function.Injective (relKroneckerIntₗ S (n := n)) := by
  intro a b hab
  apply Subtype.ext
  funext σ
  have h := LinearMap.congr_fun hab (RelativeChainInt.mk S n (Finsupp.single σ 1))
  simp only [relKroneckerIntₗ, LinearMap.coe_mk, AddHom.coe_mk, relKroneckerInt_mk,
    kronecker_single, one_mul] at h
  exact h

/-- **The relative Kronecker pairing is surjective** (wt1's unconditional realization lemma). -/
theorem relKroneckerIntₗ_surjective {n : ℕ} :
    Function.Surjective (relKroneckerIntₗ S (n := n)) := by
  intro φ
  obtain ⟨a, ha⟩ := exists_relCochainInt_of_functional S φ
  exact ⟨a, ha⟩

/-- **The relative Kronecker pairing as a linear equivalence** `relCochainsInt S n ≃ₗ Hom(RC(S) n, ℤ)`. -/
noncomputable def relKroneckerIntEquiv {n : ℕ} :
    relCochainsInt S n ≃ₗ[ℤ] (RelativeChainInt S n →ₗ[ℤ] ℤ) :=
  LinearEquiv.ofBijective (relKroneckerIntₗ S)
    ⟨relKroneckerIntₗ_injective S, relKroneckerIntₗ_surjective S⟩

end SKEFTHawking.SingularRelativeKroneckerEquivInt
