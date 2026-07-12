/-
# Phase 5q.H (E1) — reduction naturality of the Kronecker pairing (`ℤ → ℤ/2`)

The ONE lemma between the in-tree pieces and `SpinWuDatum` at a general closed oriented spin
4-manifold (E1 shard, arm-2 turn 6): the ℤ→ℤ/2 coefficient reduction intertwines the integral and
mod-2 Kronecker evaluations,
`((⟨b, h⟩_ℤ : ℤ) : ZMod 2) = ⟨redH b, redHomology h⟩₂`.
Both pairings are the same `Finsupp` evaluation sum (`c.sum fun σ a => a * f σ`) over their
coefficient rings, and both reduction maps are pointwise `Int.cast` — so the bridge is the cast ring
hom mapped through the sum. Consumers: the `eval_compat` field of `SpinWuDatum` (via
`spinWuDatum_of_pd4Mid`) with `mu := fundamentalFunctional` and the integral evaluation against an
`IntOrientation`'s fundamental class (`intOrientation_redHomology_fundClass` supplies
`redHomology [M]_ℤ = [M]₂`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.IntersectionFormEvenInt
import SKEFTHawking.IntFundamentalClassOrientation

namespace SKEFTHawking.SingularHomologyInt

open SKEFTHawking.SingularCohomologyInt (redC redH redH_mk SingularCochainInt Cohomology)

variable {X : TopCat} {n : ℕ}

/-- **Chain-level reduction naturality of the Kronecker evaluation**: casting the integral evaluation
`⟨f, c⟩ = Σ_σ c(σ)·f(σ)` to `ZMod 2` is the mod-2 evaluation of the reduced cochain on the reduced
chain. The cast ring hom mapped through the `Finsupp` sum, term by term. -/
theorem kronecker_redCompat (f : SingularCochainInt X n) (c : SingularChainInt X n) :
    ((kronecker f c : ℤ) : ZMod 2)
      = SKEFTHawking.SingularHomologyMod2.kronecker (redC X n f) (redChain X n c) := by
  rw [kronecker, SKEFTHawking.SingularHomologyMod2.kronecker]
  rw [show redChain X n c = Finsupp.mapRange.addMonoidHom (Int.castAddHom (ZMod 2)) c from rfl]
  rw [Finsupp.mapRange.addMonoidHom_apply]
  rw [Finsupp.sum_mapRange_index (by intro σ; simp)]
  rw [show ((c.sum fun σ a => a * f σ : ℤ) : ZMod 2)
      = (Int.castAddHom (ZMod 2)) (c.sum fun σ a => a * f σ) from rfl, map_finsuppSum]
  refine Finsupp.sum_congr (fun σ _ => ?_)
  simp only [Int.coe_castAddHom, SKEFTHawking.SingularCohomologyInt.redC_apply]
  exact Int.cast_mul _ _

/-- **Class-level reduction naturality of the Kronecker pairing**:
`((⟨b, h⟩_ℤ : ℤ) : ZMod 2) = ⟨redH b, redHomology h⟩₂` on integral cohomology/homology classes. The
`eval_compat` engine for `SpinWuDatum` with `mu := fundamentalFunctional`. -/
theorem kroneckerHInt_redCompat (b : Cohomology X n) (h : Homology X n) :
    ((kroneckerHInt n b h : ℤ) : ZMod 2)
      = SKEFTHawking.SingularHomologyMod2.kroneckerH n (redH X n b) (redHomology X n h) := by
  obtain ⟨fc, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  exact kronecker_redCompat fc.1 z.1

end SKEFTHawking.SingularHomologyInt
