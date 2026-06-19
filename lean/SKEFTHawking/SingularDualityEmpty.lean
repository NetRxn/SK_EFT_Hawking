import Mathlib
import SKEFTHawking.SingularRelativeDuality
import SKEFTHawking.SingularRelativeCohomologyEmpty
import SKEFTHawking.SingularCapHomology

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD5-D∅) — the duality map over the empty subspace is `capH`

The relative Poincaré-duality map `D_z` (`SingularRelativeDuality.relativeDuality`) over the **empty**
subspace `S = ∅` is, transported by the empty-subspace equivalences, the absolute cap-with-a-cycle map
`SingularCapHomology.capH`:
  `relativeDuality ∅ k m z hz ω = capH k m (relCohomologyEmptyEquiv ω) [z]`.
This is the bridge by which the Poincaré-duality induction's endpoint `D_univ` (over `M ∖ univ = ∅`)
becomes the absolute duality map `capH · [M]` — the form `nondeg_of_duality_injective` consumes.

The proof is `relativeDuality_mk` + `relCohomologyEmptyEquiv_mk` + `capH_mk_mk` on a representative: both
sides are `[a ⌢ z]` for the same underlying cochain `a.1.1` and chain `z` (the empty-subspace cochain
equivalence is the identity on the underlying cochain, `cochainEmptyEquiv_apply`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativeDuality SKEFTHawking.SingularRelativeEmpty
open SKEFTHawking.SingularRelativeCohomologyEmpty SKEFTHawking.SingularCapHomology

namespace SKEFTHawking.SingularDualityEmpty

variable {X : TopCat}

/-- An absolute chain `z` whose boundary is an `∅`-subspace chain is an absolute **cycle** (the only
`∅`-subspace chain is `0`). -/
theorem cycle_of_subspaceChains_empty {k m : ℕ} (z : SingularChain X (k + m + 1))
    (hz : chainBoundary X (k + m) z ∈ subspaceChains (∅ : Set X) (k + m)) :
    z ∈ cycles X (k + m + 1) := by
  show chainBoundary X (k + m) z = 0
  rw [subspaceChains_empty_eq_bot, Submodule.mem_bot] at hz
  exact hz

/-- **The duality map over `∅` is `capH`**: `relativeDuality ∅ k m z hz = capH k m · [z]` transported by
`relCohomologyEmptyEquiv`. The bridge `D_univ = capH · [M]` for the Poincaré-duality induction's
endpoint. -/
theorem relativeDuality_empty_eq_capH (k m : ℕ) (z : SingularChain X (k + m + 1))
    (hz : chainBoundary X (k + m) z ∈ subspaceChains (∅ : Set X) (k + m))
    (ω : RelativeCohomology (∅ : Set X) k) :
    relativeDuality (∅ : Set X) k m z hz ω
      = capH k m (relCohomologyEmptyEquiv k ω)
          (Homology.mk X (k + m + 1) ⟨z, cycle_of_subspaceChains_empty z hz⟩) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ ω
  rw [show (Submodule.Quotient.mk a : RelativeCohomology (∅ : Set X) k)
      = RelativeCohomology.mk (∅ : Set X) k a from rfl,
    relativeDuality_mk, relCohomologyEmptyEquiv_mk, capH_mk_mk]
  -- Both classes are `[a ⌢ z]`: the cap representatives `cap a.1.1 z` and
  -- `capCyclesₗ (cocyclesEmptyEquiv k a) ⟨z, _⟩` share the underlying cochain `a.1.1` (defeq).
  congr 1

end SKEFTHawking.SingularDualityEmpty
