import Mathlib
import SKEFTHawking.SingularSubHomologyMVCohomConn
import SKEFTHawking.SingularConnSquareRHSAdjoint
import SKEFTHawking.SingularOpenDuality

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD6f-c4-L2) — the connecting-square LHS reduction

The **left-hand side** of the PD `5`-lemma connecting square, paired with an arbitrary
`sub(U∩V)`-cohomology class `a'`:
  `⟨a', subHomConnecting (legW K g)⟩_{sub(U∩V)}`.
Using the absolute-cohomology-MV-connecting adjunction (`kroneckerH_absCohomConn`, L1b) to move `a'`
through the homology connecting `subHomConnecting`, then the class-level relative cap–Kronecker bridge
(`kroneckerH_relativeDualityK_eq_relKroneckerH`, since `legW K g = relativeDualityK ((↑K)ᶜ) (U∪V) z_K g`),
this reduces to the **relative** Kronecker pairing
  `⟨g, [chainIncl (b ⌢ʳ z_K)]⟩_{(↑K)ᶜ}`,
where `b` is any cocycle representative of `absCohomConn a'`. This is the LHS analogue of the RHS reduction
`kroneckerH_relativeDualityK_relCohomMvConnecting` — both legs of the connecting square are now
relative-Kronecker pairings over the **same** subspace `(↑K)ᶜ`, leaving only the match of the two
relative-homology capped cycles (`[b ⌢ʳ z_K]` vs `relMvDelta [a' ⌢ʳ z'']`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularRelativePairing SKEFTHawking.SingularCompactlySupportedOpen
  SKEFTHawking.SingularSubsetHomology SKEFTHawking.SingularSubHomologyMV
  SKEFTHawking.SingularCapChainIncl SKEFTHawking.SingularCapSubKDuality
  SKEFTHawking.SingularSubspaceChainsEquiv SKEFTHawking.SingularLocalDualityK
  SKEFTHawking.SingularOpenDuality SKEFTHawking.SingularOpenDualityCycle
  SKEFTHawking.SingularSubHomologyMVCohomConn SKEFTHawking.SingularConnSquareRHSAdjoint

namespace SKEFTHawking.SingularConnSquareLHS

variable {X : TopCat} [T2Space ↑X]

/-- **The connecting-square LHS, reduced to a relative-Kronecker pairing.** For any cocycle rep `b` of
`absCohomConn a'`: `⟨a', subHomConnecting (legW K g)⟩ = ⟨g, [chainIncl (b ⌢ʳ z_K)]⟩_{(↑K)ᶜ}`. -/
theorem kroneckerH_subHomConnecting_legW {N p : ℕ} {U V : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChain X (N + 1 + (p + 1) + 1)) (hz₀ : chainBoundary X (N + 1 + (p + 1)) z₀ = 0)
    (K : SingularCompactsInOpen.CompactsIn (U ∪ V)) (g : cohomGW (U ∪ V) (N + 1) K)
    (a' : Cohomology (sub (U ∩ V)) (p + 1))
    (b : LinearMap.ker (coboundaryₗ (sub (U ∪ V)) (p + 2)))
    (hb : Submodule.Quotient.mk b = absCohomConn U V hU hV p a') :
    kroneckerH (X := sub (U ∩ V)) (p + 1) a'
        (subHomConnecting U V hU hV (p + 1) (legW (hU.union hV) z₀ hz₀ K g))
      = relKroneckerH ((↑K.1 : Set ↑X)ᶜ) g
          (RelativeHomology.mk ((↑K.1 : Set ↑X)ᶜ) (N + 1)
            ⟨RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (N + 1)
                (chainIncl (U ∪ V) (N + 1) (rcap b.1
                  ((subspaceChainsEquiv (U ∪ V) (N + 1 + (p + 1) + 1)).symm
                    ⟨fundCycleW (hU.union hV) z₀ hz₀ K, fundCycleW_mem_W (hU.union hV) z₀ hz₀ K⟩))),
              chainIncl_rcap_mem_relCycles (fundCycleW (hU.union hV) z₀ hz₀ K)
                (fundCycleW_mem_W (hU.union hV) z₀ hz₀ K)
                (fundCycleW_boundary (hU.union hV) z₀ hz₀ K) b⟩) := by
  rw [← kroneckerH_absCohomConn, ← hb]
  exact kroneckerH_relativeDualityK_eq_relKroneckerH
    (fundCycleW (hU.union hV) z₀ hz₀ K) (fundCycleW_mem_W (hU.union hV) z₀ hz₀ K)
    (fundCycleW_boundary (hU.union hV) z₀ hz₀ K) b g

end SKEFTHawking.SingularConnSquareLHS
