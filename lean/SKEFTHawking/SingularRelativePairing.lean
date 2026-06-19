import Mathlib
import SKEFTHawking.SingularRelativeCohomologyMod2

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD4b) — the relative Kronecker pairing

The Kronecker pairing descends to relative (co)homology: a **relative cochain** `a` (vanishing on the
subspace chains `subspaceChains S`) pairs with a **relative chain** `[c] ∈ RelativeChain S n` via
`⟨a, [c]⟩ = ⟨a, c⟩`, well-defined because `a` kills the subspace chains. This is the relative analogue of
`kroneckerH` and the pairing that exhibits `Hᵏ(M, S)` as dual to `Hₙ(M, S)` (relative universal
coefficients), used for the local cohomology `Hⁿ(M|x) ≅ ℤ/2` in the Poincaré-duality base case.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2

namespace SKEFTHawking.SingularRelativePairing

variable {X : TopCat} (S : Set X)

/-- **The relative Kronecker pairing on relative chains** `relKronecker a : RelativeChain S n → ℤ/2`,
`[c] ↦ ⟨a, c⟩` for a relative cochain `a` (`a ∈ relCochains S n`, i.e. `a` vanishes on `subspaceChains S`).
Well-defined: `a` kills the subspace chains, so `kronecker a.1 ·` descends through `RelativeChain`. -/
noncomputable def relKronecker {n : ℕ} (a : relCochains S n) :
    RelativeChain S n →ₗ[ZMod 2] ZMod 2 :=
  Submodule.liftQ (subspaceChains S n) (kroneckerₗ n a.1) (fun c hc => a.2 c hc)

@[simp] theorem relKronecker_mk {n : ℕ} (a : relCochains S n) (c : SingularChain X n) :
    relKronecker S a (RelativeChain.mk S n c) = kronecker a.1 c := rfl

/-- **The relative Kronecker pairing is `ℤ/2`-bilinear** `relCochains S n →ₗ (RelativeChain S n →ₗ ℤ/2)`
(linear in the relative chain by construction, in the relative cochain since `kroneckerₗ` is). -/
noncomputable def relKroneckerₗ {n : ℕ} :
    relCochains S n →ₗ[ZMod 2] RelativeChain S n →ₗ[ZMod 2] ZMod 2 where
  toFun := relKronecker S
  map_add' a b := by
    ext q
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    show kronecker (↑(a + b)) c = kronecker (↑a) c + kronecker (↑b) c
    rw [Submodule.coe_add, kronecker_add_left]
  map_smul' s a := by
    ext q
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    show kronecker (↑(s • a)) c = s * kronecker (↑a) c
    rw [SetLike.val_smul, kronecker_smul_left, smul_eq_mul]

end SKEFTHawking.SingularRelativePairing
