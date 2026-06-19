import Mathlib
import SKEFTHawking.SingularLocalDualityK
import SKEFTHawking.SingularCapChainIncl

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD6f-c2) — the duality chain is a genuine `sub K`-cap

`pullbackDualityₗ S K z hzK a` (the `sub K`-chain whose `chainIncl` is the absolute cap `a.1.1 ⌢ z`) is
**literally the `sub K`-cap** `(pullbackCochain K a.1.1) ⌢ z_sub` of the pulled-back cochain with the
`sub K`-representative `z_sub = (subspaceChainsEquiv K).symm ⟨z, hzK⟩` of the `K`-supported cycle `z`. Both
have the same `chainIncl` (`= a.1.1 ⌢ z`, by `chainIncl_pullbackDualityₗ` and the cap-chainIncl naturality
`SingularCapChainIncl.cap_chainIncl`), so `chainIncl`-injectivity identifies them.

This is the step that makes the Poincaré-duality cap a `sub K`-level cap product, so the Kronecker pairing
`⟨a', relativeDualityK … (mk a)⟩_{sub K}` becomes a cup pairing via `kronecker_cup_cap` at `X := sub K`
(the connecting-square cap×Kronecker bridge) — with no cochain representative of `relCohomMvConnecting`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularLocalDualityK SKEFTHawking.SingularCapChainIncl
  SKEFTHawking.SingularSubspaceChainsEquiv

namespace SKEFTHawking.SingularCapSubKDuality

variable {X : TopCat}

/-- **The duality chain is a `sub K`-cap**: `pullbackDualityₗ S K z hzK a = (pullbackCochain K a.1.1) ⌢ z_sub`
with `z_sub = (subspaceChainsEquiv K).symm ⟨z, hzK⟩`. Both `chainIncl` to `a.1.1 ⌢ z`. -/
theorem pullbackDualityₗ_eq_subcap {k m : ℕ} {S K : Set ↑X} (z : SingularChain X (k + m + 1))
    (hzK : z ∈ subspaceChains K (k + m + 1))
    (a : LinearMap.ker (relCoboundaryₗ S k)) :
    pullbackDualityₗ S K z hzK a
      = cap (pullbackCochain K k a.1.1) ((subspaceChainsEquiv K (k + m + 1)).symm ⟨z, hzK⟩) := by
  apply chainIncl_injective K (m + 1)
  rw [chainIncl_pullbackDualityₗ, ← cap_chainIncl]
  exact congrArg (cap a.1.1) (chainIncl_subspaceChainsEquiv_symm K (k + m + 1) ⟨z, hzK⟩).symm

/-- **The sub-`K` Kronecker cup bridge**: pairing a `sub K`-cohomology cocycle `a'` against the
Poincaré-duality image `relativeDualityK S K z [a]` equals pairing the cup `(pullbackCochain K a) ∪ a'`
against the `sub K`-representative `z_sub = (subspaceChainsEquiv K).symm ⟨z,hzK⟩` of the fundamental
cycle. Chains together `relativeDualityK_mk` (the image is `[pullbackDualityₗ]`), c2
(`pullbackDualityₗ_eq_subcap`: that chain IS the sub-`K`-cap `(pullbackCochain K a) ⌢ z_sub`), and
`kronecker_cup_cap` at `Y := sub K`. This converts the connecting-square cap pairing into a cup pairing
with **no cochain representative of `relCohomMvConnecting`** — the move that dodged the original block. -/
theorem kroneckerH_relativeDualityK_mk_eq_cup {k m : ℕ} {S K : Set ↑X}
    (z : SingularChain X (k + m + 1)) (hzK : z ∈ subspaceChains K (k + m + 1))
    (hzS : chainBoundary X (k + m) z ∈ subspaceChains S (k + m))
    (a : LinearMap.ker (relCoboundaryₗ S k))
    (a' : LinearMap.ker (coboundaryₗ (sub K) (m + 1))) :
    kroneckerH (X := sub K) (m + 1) (Submodule.Quotient.mk a')
        (relativeDualityK S K k m z hzK hzS (RelativeCohomology.mk S k a))
      = kronecker (cup (pullbackCochain K k a.1.1) a'.1)
          ((subspaceChainsEquiv K (k + m + 1)).symm ⟨z, hzK⟩) := by
  rw [relativeDualityK_mk]
  show kroneckerH (X := sub K) (m + 1) (Submodule.Quotient.mk a')
      (Submodule.Quotient.mk _) = _
  rw [kroneckerH_mk_mk]
  show kronecker a'.1 (pullbackDualityₗ S K z hzK a) = _
  rw [pullbackDualityₗ_eq_subcap, ← kronecker_cup_cap]

end SKEFTHawking.SingularCapSubKDuality
