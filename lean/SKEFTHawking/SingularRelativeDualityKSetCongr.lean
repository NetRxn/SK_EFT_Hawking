import Mathlib
import SKEFTHawking.SingularLocalDualityK
import SKEFTHawking.SingularCompactlySupportedTop
import SKEFTHawking.SingularConnSquareRHSAdjoint
import SKEFTHawking.SingularRelativeCohomologyMVConnecting

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4-M3 support) — transporting `relativeDualityK` along its source set

The `H(sub K)`-valued relative Poincaré-duality map `relativeDualityK S K k m z …` reads the
cohomology source subspace `S` *only* through its relative-cohomology argument. Hence pre-composing
with the relative-cohomology set-congruence `relCohomSetCongr (h : S = S')` (the `subst`-cast
`RelativeCohomology S ≃ RelativeCohomology S'`) is absorbed by re-indexing the duality map's source
`S' → S`, leaving the fundamental cycle `z`, its support witness `hzK`, and the cap target `K`
untouched.

This is the LHS-of-the-collapse bridge needed in the connecting-square RHS reduction: the
`SingularOpenDualityConnLegdeltaCollapse.openDuality_legδ_eq_legW` collapse produces a
`legW J (relCohomSetCongr hJL …)`; unfolding `legW J = relativeDualityK ((↑J)ᶜ) (U∩V) …` and applying
this lemma rewrites the source set from `(↑J)ᶜ` to `(↑LU)ᶜ ∪ (↑LV)ᶜ`, exposing the bare
`relCohomMvConnecting` for `SingularConnSquareRHSAdjoint.kroneckerH_relativeDualityK_relCohomMvConnecting`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularLocalDualityK SKEFTHawking.SingularCompactlySupportedTop
  SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
  SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativePairing SKEFTHawking.SingularCapChainIncl
  SKEFTHawking.SingularSubspaceChainsEquiv SKEFTHawking.SingularConnSquareRHSAdjoint
  SKEFTHawking.SingularRelativeCohomologyMVConnecting SKEFTHawking.SingularRelativeMV
  SKEFTHawking.SingularCapSubKDuality

namespace SKEFTHawking.SingularRelativeDualityKSetCongr

variable {X : TopCat}

/-- **Transport `relativeDualityK` along a cohomology-source set equality.** Pre-composing the duality
map at source `S'` with the set-congruence `relCohomSetCongr (h : S = S')` equals the duality map at
source `S` (same fundamental cycle `z`, support witness `hzK`, cap target `K`). Proof: `subst h`
reduces `relCohomSetCongr` to the identity. -/
theorem relativeDualityK_relCohomSetCongr {k m : ℕ} {S S' K : Set ↑X} (h : S = S')
    (z : SingularChain X (k + m + 1)) (hzK : z ∈ subspaceChains K (k + m + 1))
    (hzS : chainBoundary X (k + m) z ∈ subspaceChains S (k + m))
    (hzS' : chainBoundary X (k + m) z ∈ subspaceChains S' (k + m))
    (a : RelativeCohomology S k) :
    relativeDualityK S' K k m z hzK hzS' (relCohomSetCongr h k a)
      = relativeDualityK S K k m z hzK hzS a := by
  subst h
  rfl

/-- **The set-congruence-wrapped RHS adjunction, over an abstract fundamental cycle.** The
connecting-square RHS, after `openDuality_legδ_eq_legW` and `legW J = relativeDualityK ((↑J)ᶜ) …`, has
shape `kroneckerH (mk a') (relativeDualityK S' K (N+2) p z hzK hzS' (relCohomSetCongr hSeq …
(relCohomMvConnecting U' V' σ)))`, where `S' = (↑J)ᶜ` is set-equal to `U'∪V'` (the cover of the
connecting map). Absorbing the set-congruence (`relativeDualityK_relCohomSetCongr`) and firing the RHS
adjunction (`kroneckerH_relativeDualityK_relCohomMvConnecting`) moves the connecting homomorphism onto
the homology side as `relMvDelta`.

Stated over an **abstract** cycle `z` (no `fundCycleW`/colimit term in scope) so the proof stays light
and, on instantiation `z := fundCycleW J`, the heavy cycle is bound to `z` as a unification variable —
avoiding the colimit-`whnf` heartbeat wall that arises if the transport/adjunction is applied directly
to the `fundCycleW`-laden term. -/
theorem kroneckerH_relativeDualityK_setCongr_relCohomMvConnecting {p N : ℕ}
    {U' V' K S' : Set ↑X} (hU' : IsOpen U') (hV' : IsOpen V') (hSeq : U' ∪ V' = S')
    (z : SingularChain X (N + 1 + 1 + p + 1)) (hzK : z ∈ subspaceChains K (N + 1 + 1 + p + 1))
    (hzS : chainBoundary X (N + 1 + 1 + p) z ∈ subspaceChains (U' ∪ V') (N + 1 + 1 + p))
    (hzS' : chainBoundary X (N + 1 + 1 + p) z ∈ subspaceChains S' (N + 1 + 1 + p))
    (a' : LinearMap.ker (coboundaryₗ (sub K) (p + 1)))
    (σ : RelativeCohomology (U' ∩ V') (N + 1)) :
    kroneckerH (X := sub K) (p + 1) (Submodule.Quotient.mk a')
        (relativeDualityK S' K (N + 1 + 1) p z hzK hzS'
          (relCohomSetCongr hSeq (N + 1 + 1) (relCohomMvConnecting U' V' hU' hV' N σ)))
      = relKroneckerH (U' ∩ V') σ
          (relMvDelta U' V' hU' hV' (N + 1)
            (RelativeHomology.mk (U' ∪ V') (N + 1 + 1)
              ⟨RelativeChain.mk (U' ∪ V') (N + 1 + 1)
                  (chainIncl K (N + 1 + 1) (rcap a'.1
                    ((subspaceChainsEquiv K (N + 1 + 1 + p + 1)).symm ⟨z, hzK⟩))),
                chainIncl_rcap_mem_relCycles z hzK hzS a'⟩)) := by
  rw [relativeDualityK_relCohomSetCongr hSeq z hzK hzS hzS',
    kroneckerH_relativeDualityK_relCohomMvConnecting]

end SKEFTHawking.SingularRelativeDualityKSetCongr
