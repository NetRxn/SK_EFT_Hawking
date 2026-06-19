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
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularCapChainIncl
  SKEFTHawking.SingularPairLES SKEFTHawking.SingularCapSubKDuality

namespace SKEFTHawking.SingularConnSquareMatchLHS

variable {X : TopCat}

/-- **LHS-half match reduction**: the seam pairing of a `pullbackCochain`-form cochain against a
boundary-extraction equals the ambient coboundary pairing `⟨δa, c⟩`. -/
theorem kronecker_pullbackCochain_boundaryExtract (S : Set ↑X) (n : ℕ)
    (a : SingularCochain X n) (c : relCycleLift S n) :
    kronecker (pullbackCochain S n a) (boundaryExtract S n c)
      = kronecker (coboundary X n a) (c : SingularChain X (n + 1)) := by
  rw [kronecker_pullbackCochain, chainIncl_boundaryExtract, ← kronecker_coboundary_chainBoundary]

/-- **Cover-partition cap-boundary relation** (cap-Leibniz on the partition): for a cocycle `g` whose cap
`g ⌢ z` is cover-partitioned as `chainIncl A zA + chainIncl B zB`, the boundary of the cap distributes
over the partition and equals `g ⌢ ∂z` (the cap commutes with `∂` for a cocycle, `cap_cocycle_chainMap`):
`chainIncl A (∂zA) + chainIncl B (∂zB) = g ⌢ ∂z`. The chain-level engine of the shared-`z₀` match
(relating the seam boundary `∂zB` to the fundamental cycle's boundary). -/
theorem cover_partition_cap_boundary {k m : ℕ} (A B : Set ↑X) (g : SingularCochain X k)
    (hg : coboundaryₗ X k g = 0) (z : SingularChain X (k + m + 1))
    (zA : SingularChain (sub A) (m + 1)) (zB : SingularChain (sub B) (m + 1))
    (hpart : cap g z = chainIncl A (m + 1) zA + chainIncl B (m + 1) zB) :
    chainIncl A m (chainBoundary (sub A) m zA) + chainIncl B m (chainBoundary (sub B) m zB)
      = cap g (chainBoundary X (k + m) z) := by
  have h1 := cap_cocycle_chainMap g hg z
  rw [hpart, map_add, ← chainIncl_chainBoundary, ← chainIncl_chainBoundary] at h1
  exact h1

/-- **Cup pairing over a cover-partition**: for a cover-partition `g ⌢ z = chainIncl A zA + chainIncl B zB`
of a cap, the cup pairing `⟨g ∪ b, z⟩` reads off as the sum of the partition-part pairings
`⟨b|_A, zA⟩ + ⟨b|_B, zB⟩` (via `kronecker_cup_cap` + `kronecker_pullbackCochain`). Connects the
fundamental cup `⟨g ∪ b, z⟩` to the seam parts — the bridge between the two legs of the match. -/
theorem kronecker_cup_cover_partition {k l : ℕ} (A B : Set ↑X) (g : SingularCochain X k)
    (b : SingularCochain X l) (z : SingularChain X (k + l))
    (zA : SingularChain (sub A) l) (zB : SingularChain (sub B) l)
    (hpart : cap g z = chainIncl A l zA + chainIncl B l zB) :
    kronecker (cup g b) z
      = kronecker (pullbackCochain A l b) zA + kronecker (pullbackCochain B l b) zB := by
  rw [kronecker_cup_cap, hpart, kronecker_add_right, kronecker_pullbackCochain,
    kronecker_pullbackCochain]

end SKEFTHawking.SingularConnSquareMatchLHS
