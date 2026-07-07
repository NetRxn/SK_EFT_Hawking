/-
# Phase 5q.H (E1 CSC-PD tower) — the integral duality map over the empty subspace is `capHInt`

The integral relative Poincaré-duality map `D_z` (`relativeDualityInt`) over the **empty** subspace
`S = ∅` is, transported by `relCohomologyEmptyEquivInt`, the absolute integral cap-with-a-cycle map
`capHInt`:
  `relativeDualityInt ∅ k m z hz ω = capHInt k m (relCohomologyEmptyEquivInt ω) [z]`.
The bridge by which the PD induction's endpoint `D_univ` (over `M ∖ univ = ∅`) becomes `capHInt · [M]` —
the form `IntCapIso.capEquiv_apply` consumes. Integral mirror of
`SingularDualityEmpty.relativeDuality_empty_eq_capH`.

The proof is `relativeDualityInt_mk` + `relCohomologyEmptyEquivInt_mk` + `capHInt_mk_mk` on a
representative: both sides are `[a ⌢ z]` for the same underlying cochain `a.1.1` and chain `z` (the
empty-subspace cochain equivalence is the identity on the underlying cochain).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularRelativeCohomologyEmptyInt
import SKEFTHawking.IntCapProductInt
import SKEFTHawking.SingularRelativeEmptyInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeEmptyInt
open SKEFTHawking.SingularRelativeCohomologyEmptyInt

namespace SKEFTHawking.SingularDualityEmptyInt

variable {X : TopCat}

/-- An absolute integral chain `z` whose boundary is an `∅`-subspace chain is an absolute **cycle** (the
only `∅`-subspace chain is `0`). -/
theorem cycle_of_subspaceChainsInt_empty {k m : ℕ} (z : SingularChainInt X (k + m + 1))
    (hz : chainBoundary X (k + m) z ∈ subspaceChainsInt (∅ : Set X) (k + m)) :
    z ∈ cycles X (k + m + 1) := by
  show chainBoundary X (k + m) z = 0
  rw [subspaceChainsInt_empty_eq_bot, Submodule.mem_bot] at hz
  exact hz

/-- **The integral duality map over `∅` is `capHInt`**: `relativeDualityInt ∅ k m z hz = capHInt k m · [z]`
transported by `relCohomologyEmptyEquivInt`. The bridge `D_univ = capHInt · [M]` for the integral
Poincaré-duality induction's endpoint. -/
theorem relativeDualityInt_empty_eq_capHInt (k m : ℕ) (z : SingularChainInt X (k + m + 1))
    (hz : chainBoundary X (k + m) z ∈ subspaceChainsInt (∅ : Set X) (k + m))
    (ω : RelativeCohomologyInt (∅ : Set X) k) :
    relativeDualityInt (∅ : Set X) k m z hz ω
      = capHInt k m (relCohomologyEmptyEquivInt k ω)
          (Homology.mk X (k + m + 1) ⟨z, cycle_of_subspaceChainsInt_empty z hz⟩) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ ω
  rw [show (Submodule.Quotient.mk a : RelativeCohomologyInt (∅ : Set X) k)
      = RelativeCohomologyInt.mk (∅ : Set X) k a from rfl,
    relativeDualityInt_mk, relCohomologyEmptyEquivInt_mk, capHInt_mk_mk]
  congr 1

end SKEFTHawking.SingularDualityEmptyInt
