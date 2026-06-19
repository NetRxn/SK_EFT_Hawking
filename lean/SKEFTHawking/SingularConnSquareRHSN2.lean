import Mathlib
import SKEFTHawking.SingularRelativeDualityKSetCongr

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4-M4 support) — the `N+2`-literal RHS adjunction wrapper

`SingularRelativeDualityKSetCongr.kroneckerH_relativeDualityK_setCongr_relCohomMvConnecting` is stated
with the cohomology degree index written as `N + 1 + 1` (to dodge the colimit-`whnf` heartbeat wall when
the heavy `fundCycleW` cycle is bound as a unification variable). The connecting-square RHS, after
`openDuality_legδ_eq_legW` and `legW = relativeDualityK`, presents that index as the *definitionally
equal but syntactically distinct* literal `N + 2` (from `openDuality (k := N + 2)`). `rw` matches
syntactically, so it cannot fire the `N + 1 + 1` lemma against the `N + 2` goal directly.

This file re-states the adjunction with the `N + 2` literal in the `relativeDualityK` index, discharged by
`exact` (defeq absorbs `N + 1 + 1 ≡ N + 2`). The cycle stays **abstract** so the wrapper carries the same
heartbeat-wall-avoiding shape, and on instantiation the heavy `fundCycleW` binds to `z`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularLocalDualityK SKEFTHawking.SingularCapChainIncl
  SKEFTHawking.SingularSubspaceChainsEquiv SKEFTHawking.SingularRelativePairing
  SKEFTHawking.SingularCompactlySupportedTop SKEFTHawking.SingularRelativeMV
  SKEFTHawking.SingularRelativeCohomologyMVConnecting SKEFTHawking.SingularCapSubKDuality

namespace SKEFTHawking.SingularConnSquareRHSN2

variable {X : TopCat}

/-- **The `N+2`-literal RHS adjunction wrapper** — the connecting-square RHS reduction with the
cohomology degree written as the literal `N + 2` (matching `openDuality (k := N + 2)`), so it `rw`s
into the collapsed connecting-square goal. Defeq-discharged from the `N + 1 + 1` form; cycle abstract. -/
theorem kroneckerH_relativeDualityK_setCongr_relCohomMvConnecting_N2 {p N : ℕ}
    {U' V' K S' : Set ↑X} (hU' : IsOpen U') (hV' : IsOpen V') (hSeq : U' ∪ V' = S')
    (z : SingularChain X (N + 2 + p + 1)) (hzK : z ∈ subspaceChains K (N + 2 + p + 1))
    (hzS : chainBoundary X (N + 2 + p) z ∈ subspaceChains (U' ∪ V') (N + 2 + p))
    (hzS' : chainBoundary X (N + 2 + p) z ∈ subspaceChains S' (N + 2 + p))
    (a' : LinearMap.ker (coboundaryₗ (sub K) (p + 1)))
    (σ : RelativeCohomology (U' ∩ V') (N + 1)) :
    kroneckerH (X := sub K) (p + 1) (Submodule.Quotient.mk a')
        (relativeDualityK S' K (N + 2) p z hzK hzS'
          (relCohomSetCongr hSeq (N + 2) (relCohomMvConnecting U' V' hU' hV' N σ)))
      = relKroneckerH (U' ∩ V') σ
          (relMvDelta U' V' hU' hV' (N + 1)
            (RelativeHomology.mk (U' ∪ V') (N + 2)
              ⟨RelativeChain.mk (U' ∪ V') (N + 2)
                  (chainIncl K (N + 2) (rcap a'.1
                    ((subspaceChainsEquiv K (N + 2 + p + 1)).symm ⟨z, hzK⟩))),
                chainIncl_rcap_mem_relCycles z hzK hzS a'⟩)) :=
  SingularRelativeDualityKSetCongr.kroneckerH_relativeDualityK_setCongr_relCohomMvConnecting
    hU' hV' hSeq z hzK hzS hzS' a' σ

end SKEFTHawking.SingularConnSquareRHSN2
