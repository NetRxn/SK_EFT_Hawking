import Mathlib
import SKEFTHawking.SingularConnSquareClose
import SKEFTHawking.SingularConnSquareMatchLHS
import SKEFTHawking.SingularRelCohomMvConnectingGeom

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4-M7) — the UNCONDITIONAL RHS reduction of the connecting-square MATCH

`SingularConnSquareClose.subHomConnecting_openDuality_of_hcup` reduced the per-`K` connecting-square
equality to a single chain-level cup identity `hcup`. The blocker the lead diagnosed: the cohomology MV
connecting `relCohomMvConnecting` was Kronecker-defined, so any chain-level rep of it was opaque and
every match route circular. The committed geometric realization
(`SingularRelCohomMvConnectingGeom`) fixes this with an explicit cochain `δφ = δ(cochainSplit U' ω)`.

This file lifts that realization into the connecting-square's RHS shape:

* `coboundary_pullbackCochain` — the subspace-inclusion coboundary commutation
  `δ(pullbackCochain S a) = pullbackCochain S (δa)` (subspace analogue of
  `SingularKroneckerFunctoriality.coboundary_pullbackCochainMap`).
* `relKroneckerH_relMvDelta_pairing` — **the unconditional RHS reduction.** The `relMvDelta`-shaped RHS
  pairing of the match reduces, with NO `relCochains (U'∪V')` membership hypothesis (the subdivision gap
  is sidestepped by routing through the *pairing* form rather than the *class* form), to the explicit
  chain-level `⟨δφ, c⟩` for any cover-partition `∂c = u + w` of the capped fundamental cycle. This is the
  non-circular RHS half the geometric realization enables: it replaces the opaque
  `Quotient.mk_surjective` rep of `relCohomMvConnecting` with the concrete seam coboundary `δφ`.

The remaining residual to a full unconditional `subHomConnecting_openDuality` is the **cover-partition of
the specific capped fundamental cycle** (`hbd : ∂c = u + w`, `u ∈ C(LUᶜ)`, `w ∈ C(LVᶜ)`), which the
relative-cycle condition only gives modulo the small-simplices/subdivision content
(`subspaceChains (A∪B) ⊋ C(A) + C(B)`), shared with the bottom-row LHS assembly whose concrete
instantiation is the documented `whnf`-walled residual of `SingularConnSquareLHSExplicit`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularRelativePairing SKEFTHawking.SingularCompactlySupportedOpen
  SKEFTHawking.SingularSubsetHomology SKEFTHawking.SingularSubHomologyMV
  SKEFTHawking.SingularCapChainIncl SKEFTHawking.SingularOpenDuality
  SKEFTHawking.SingularOpenDualityCycle SKEFTHawking.SingularConnSquareLHS
  SKEFTHawking.SingularConnSquareRHSAdjoint SKEFTHawking.SingularRelMvDeltaChain
  SKEFTHawking.SingularMvDeltaPartition SKEFTHawking.SingularCapSubKDuality
  SKEFTHawking.SingularRelativeMV SKEFTHawking.SingularSubspaceChainsEquiv
  SKEFTHawking.SingularCupCapHomology

namespace SKEFTHawking.SingularConnSquareCloseFinal

variable {X : TopCat}

/-- **Cochain pullback commutes with the coboundary** (subspace-inclusion form):
`δ(pullbackCochain S a) = pullbackCochain S (δa)`. The subspace analogue of
`SingularKroneckerFunctoriality.coboundary_pullbackCochainMap`, proved directly from
`simplexIncl_face`. -/
theorem coboundary_pullbackCochain {S : Set ↑X} (k : ℕ) (a : SingularCochain X k) :
    coboundary (sub S) k (pullbackCochain S k a)
      = pullbackCochain S (k + 1) (coboundary X k a) := by
  funext τ
  rw [coboundary_apply, pullbackCochain_apply, coboundary_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pullbackCochain_apply, simplexIncl_face]

section
variable [T2Space ↑X]

open SKEFTHawking.SingularRelativeCohomologyMVConnecting
  SKEFTHawking.SingularRelCohomMvConnectingGeom
  SKEFTHawking.SingularCohomologySnake in
omit [T2Space ↑X] in
/-- **RHS reduction via the unconditional pairing form.** The `relMvDelta`-shaped RHS pairing reduces,
by reversing the connecting adjunction (`relKroneckerH_relMvDelta_eq`) then applying the unconditional
geometric pairing form, to the chain-level `⟨δφ, c⟩` with `δφ = coboundary (cochainSplit U' ωR)` the
explicit seam cochain. Holds for ANY cover-partition `∂c = u + w` of the capped fundamental cycle —
no `relCochains (U'∪V')` membership needed (the subdivision gap is sidestepped by the pairing form). -/
theorem relKroneckerH_relMvDelta_pairing {N p : ℕ} {U' V' KR : Set ↑X}
    (hU' : IsOpen U') (hV' : IsOpen V')
    (ωR : LinearMap.ker (relCoboundaryₗ (U' ∩ V') (N + 1)))
    (aR : LinearMap.ker (coboundaryₗ (sub KR) (p + 1)))
    (zR : SingularChain X (N + 2 + p + 1)) (hzRK : zR ∈ subspaceChains KR (N + 2 + p + 1))
    (hWR : RelativeChain.mk (U' ∪ V') (N + 2)
        (chainIncl KR (N + 2) (rcap aR.1 ((subspaceChainsEquiv KR (N + 2 + p + 1)).symm ⟨zR, hzRK⟩)))
        ∈ relCycles (U' ∪ V') (N + 2))
    (u w : SingularChain X (N + 1))
    (hu : u ∈ subspaceChains U' (N + 1)) (hw : w ∈ subspaceChains V' (N + 1))
    (hbd : chainBoundary X (N + 1)
        (chainIncl KR (N + 2) (rcap aR.1 ((subspaceChainsEquiv KR (N + 2 + p + 1)).symm ⟨zR, hzRK⟩)))
      = u + w)
    (hwcyc : RelativeChain.mk (U' ∩ V') (N + 1) w ∈ relCycles (U' ∩ V') (N + 1)) :
    relKroneckerH (U' ∩ V') (RelativeCohomology.mk (U' ∩ V') (N + 1) ωR)
        (relMvDelta U' V' hU' hV' (N + 1)
          (RelativeHomology.mk (U' ∪ V') (N + 2)
            ⟨RelativeChain.mk (U' ∪ V') (N + 2)
                (chainIncl KR (N + 2) (rcap aR.1
                  ((subspaceChainsEquiv KR (N + 2 + p + 1)).symm ⟨zR, hzRK⟩))), hWR⟩))
      = kronecker (coboundary X (N + 1) (cochainSplit U' (N + 1) ωR.1.1))
          (chainIncl KR (N + 2) (rcap aR.1
            ((subspaceChainsEquiv KR (N + 2 + p + 1)).symm ⟨zR, hzRK⟩))) := by
  rw [SKEFTHawking.SingularConnSquareClose.relKroneckerH_relMvDelta_eq U' V' hU' hV' N
    (RelativeCohomology.mk (U' ∩ V') (N + 1) ωR)]
  exact relKroneckerH_relCohomMvConnecting_cover_partition U' V' hU' hV' N ωR _ u w hu hw hbd hwcyc hWR

end

end SKEFTHawking.SingularConnSquareCloseFinal
