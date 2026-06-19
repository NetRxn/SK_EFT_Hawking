import Mathlib
import SKEFTHawking.SingularCapSubKDuality
import SKEFTHawking.SingularPairLES

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4-R3a) — the LHS-half of the connecting-square match

The chain-level reduction of the connecting square's LHS pairing: pairing a **`pullbackCochain`-form**
seam cochain `pullbackCochain S n a` against the boundary-extraction `boundaryExtract S n c` of a
relative-cycle lift reduces to the ambient coboundary pairing `⟨δa, c⟩`:

    ⟨pullbackCochain S n a, boundaryExtract S n c⟩ = ⟨δa, c⟩.

Chains three committed adjunctions: `kronecker_pullbackCochain` (`⟨φ^*a, c⟩ = ⟨a, chainIncl c⟩`),
`chainIncl_boundaryExtract` (`chainIncl (boundaryExtract c) = ∂c`), and
`kronecker_coboundary_chainBoundary` (`⟨δf, c⟩ = ⟨f, ∂c⟩`). This is the LHS-half engine of the unified
shared-`z₀` cup-cap-Leibniz match; paired with the RHS adjunction
`kroneckerH_relativeDualityK_relCohomMvConnecting` and M5a's cup-cap, both legs of `hcore` reduce to
`⟨g ∪ a', z₀⟩` on the shared fundamental cycle.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularCapChainIncl SKEFTHawking.SingularPairLES
  SKEFTHawking.SingularCapSubKDuality

namespace SKEFTHawking.SingularConnSquareMatchLHS

variable {X : TopCat}

/-- **LHS-half match reduction**: the seam pairing of a `pullbackCochain`-form cochain against a
boundary-extraction equals the ambient coboundary pairing `⟨δa, c⟩`. -/
theorem kronecker_pullbackCochain_boundaryExtract (S : Set ↑X) (n : ℕ)
    (a : SingularCochain X n) (c : relCycleLift S n) :
    kronecker (pullbackCochain S n a) (boundaryExtract S n c)
      = kronecker (coboundary X n a) (c : SingularChain X (n + 1)) := by
  rw [kronecker_pullbackCochain, chainIncl_boundaryExtract, ← kronecker_coboundary_chainBoundary]

end SKEFTHawking.SingularConnSquareMatchLHS
