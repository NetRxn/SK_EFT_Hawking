/-
# Phase 5q.H (E1 · integral PD tower) — the dual cochain operator (transpose of a chain map)

Reusable homological infrastructure for the small-chains cohomology surjectivity (`(B)`, the last node of
the integral relative-cohomology Mayer–Vietoris middle exactness): the **ℤ-transpose** `dualCochainInt T` of
an integral chain map `T : Cₙ → Cₘ`, characterised by the Kronecker adjunction
  `⟨dualCochainInt T f, c⟩ = ⟨f, T c⟩`.
It generalises the coboundary (`coboundary = dualCochainInt chainBoundary`, the on-main
`kronecker_coboundary_chainBoundary`), is additive and CONTRAVARIANT-functorial
(`dualCochainInt (S ∘ T) = dualCochainInt T ∘ dualCochainInt S`), and dualises the iterated-subdivision
chain homotopy `1 − Sdᵐ = ∂Dₘ + Dₘ∂` into a cochain homotopy — the mechanism that lifts a `Hom(Q)` cocycle
to `relCochainsInt (U ∪ V)`. Not specific to the MV chase — dualises ANY integral chain map.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `native_decide`, no `maxHeartbeats`, no axiom.
-/

import Mathlib
import SKEFTHawking.SingularExcisionInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt

namespace SKEFTHawking.SingularDualCochainInt

variable {X : TopCat}

/-- The **dual cochain operator** of an integral chain map. For `T : Cₙ → Cₘ`, `dualCochainInt T` sends a
cochain `f ∈ Cochainᵐ` to the cochain `σ ↦ ⟨f, T (single σ 1)⟩ ∈ Cochainⁿ` — the ℤ-transpose of `T` under
the Kronecker pairing (`kronecker_dualCochainInt`). -/
noncomputable def dualCochainInt {n m : ℕ}
    (T : SingularChainInt X n →ₗ[ℤ] SingularChainInt X m) (f : SingularCochainInt X m) :
    SingularCochainInt X n :=
  fun σ => kronecker f (T (Finsupp.single σ 1))

/-- **The transpose adjunction** `⟨dualCochainInt T f, c⟩ = ⟨f, T c⟩` — the defining property. Proved by
`Finsupp` induction on `c`, using linearity of `T` and of the pairing in the chain slot. -/
theorem kronecker_dualCochainInt {n m : ℕ}
    (T : SingularChainInt X n →ₗ[ℤ] SingularChainInt X m) (f : SingularCochainInt X m)
    (c : SingularChainInt X n) :
    kronecker (dualCochainInt T f) c = kronecker f (T c) := by
  induction c using Finsupp.induction with
  | zero => simp only [map_zero, kronecker_apply, Finsupp.sum_zero_index]
  | single_add σ a c' _ _ ih =>
    rw [kronecker_add_right, kronecker_single, map_add, kronecker_add_right, ih,
      show (Finsupp.single σ a : SingularChainInt X n) = a • Finsupp.single σ 1 from by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one],
      map_smul, kronecker_smul_right, dualCochainInt, smul_eq_mul]

/-- **The coboundary is the transpose of the chain boundary**: `dualCochainInt (chainBoundary) = coboundary`
— identifying the on-main `coboundary` as a special case of the general transpose (via the adjunction
`kronecker_coboundary_chainBoundary`). The bridge that lets the dual homotopy speak in terms of `coboundary`. -/
theorem dualCochainInt_chainBoundary {n : ℕ} (f : SingularCochainInt X n) :
    dualCochainInt (chainBoundary X n) f = coboundary X n f := by
  funext σ
  rw [dualCochainInt, ← kronecker_coboundary_chainBoundary, kronecker_single, one_mul]

end SKEFTHawking.SingularDualCochainInt
