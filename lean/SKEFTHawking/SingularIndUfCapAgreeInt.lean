/-
# Phase 5q.H (E1 CSC-PD tower) — indUf/g cap-agreement on a V-chain (integral, hcore brick 6e-A)

`capInt_indUf_eq_on_subspaceVInt` — the clean locality sub-fact of the seam-match assembly: for `g` a
relative cocycle for `U ∩ V`, the indicator-restricted cochain `indUf U g` caps a `V`-supported chain
identically to `g` itself. On a `V`-simplex `σ`: if `range σ ⊆ U` then `range σ ⊆ U∩V`, where BOTH
`indUf U g σ = 0` (the `U`-front-face indicator fires) and `g σ = 0` (`g` is `U∩V`-relative); else
`indUf U g σ = g σ`. So `(indUf U g − g)` `V`-vanishes and caps `V`-chains to `0`
(`capInt_subspaceChainInt_eq_zero`). Consumed by the RHS `V'`-leg of the seam-match.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularEuclideanCapIsoInt
import SKEFTHawking.SingularCapIndUfBridgeInt
import SKEFTHawking.SingularRelativeCohomologyMVConnectingInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub simplexIncl)
open SKEFTHawking.SingularExcisionIsoInt (range_simplexIncl_subsetInt mem_subspaceChainsInt_of_support)
open SKEFTHawking.SingularRelativeCohomologyMVConnectingInt (indUf indUf_apply)

namespace SKEFTHawking.SingularIndUfCapAgreeInt

variable {X : TopCat}

/-- **Brick 1**: `indUf U g` agrees with `g` when capped against a `V`-supported chain, for `g` a
relative cocycle for `U ∩ V`. On a `V`-simplex `σ`: if `range σ ⊆ U` then `range σ ⊆ U∩V` so both
`indUf U g σ = 0` and `g σ = 0`; else `indUf U g σ = g σ`. So `(indUf U g − g)` `V`-vanishes and caps
`V`-chains to `0` (`capInt_subspaceChainInt_eq_zero`). -/
theorem capInt_indUf_eq_on_subspaceVInt {U V : Set ↑X} {k m : ℕ}
    (g : LinearMap.ker (relCoboundaryIntₗ (U ∩ V) k))
    {c : SingularChainInt X (k + m)} (hc : c ∈ subspaceChainsInt V (k + m)) :
    capInt (m := m) (indUf U k ((g : relCochainsInt (U ∩ V) k) : SingularCochainInt X k)) c
      = capInt (m := m) ((g : relCochainsInt (U ∩ V) k) : SingularCochainInt X k) c := by
  set gc := ((g : relCochainsInt (U ∩ V) k) : SingularCochainInt X k) with hgc
  have hzero : capInt (m := m) (indUf U k gc - gc) c = 0 := by
    refine capInt_subspaceChainInt_eq_zero V _ ?_ hc
    intro τ
    show (indUf U k gc - gc) (simplexIncl V k τ) = 0
    rw [Pi.sub_apply, indUf_apply]
    split_ifs with hU
    · have hUV : Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk k)) (simplexIncl V k τ)) ⊆ U ∩ V :=
        Set.subset_inter hU (range_simplexIncl_subsetInt V τ)
      have hg0 : gc (simplexIncl V k τ) = 0 := by
        have hmem : Finsupp.single (simplexIncl V k τ) (1 : ℤ) ∈ subspaceChainsInt (U ∩ V) k :=
          mem_subspaceChainsInt_of_support (fun σ hσ => by
            rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hσ
            subst hσ; exact hUV)
        have := g.1.2 _ hmem
        rwa [kronecker_single, one_mul] at this
      rw [hg0, sub_zero]
    · rw [sub_self]
  rw [show indUf U k gc = (indUf U k gc - gc) + gc from by abel, capInt_add_cochain, hzero, zero_add]

end SKEFTHawking.SingularIndUfCapAgreeInt
