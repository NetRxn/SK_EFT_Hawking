import Mathlib
import SKEFTHawking.SingularConnSquareMatch
import SKEFTHawking.SingularConnSquareLHSExplicit
import SKEFTHawking.SingularCupCapHomology

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4-M6) — closing the connecting-square MATCH M

Scratch / assembly toward discharging `hmatch` of
`SingularConnSquareMatch.subHomConnecting_openDuality_of_match`.

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

namespace SKEFTHawking.SingularConnSquareClose

variable {X : TopCat}

/-- **Abstract LHS-lowering of a relative-Kronecker capped pairing to chain level.** For an arbitrary
relative cohomology class `Ω` over `S`, a cycle `z` supported in `K` with boundary in `S`, and a
`sub K`-cocycle `a'`, the relative Kronecker pairing of `Ω` against `[chainIncl (a' ⌢ʳ z)]` equals
the chain-level absolute Kronecker pairing of any ambient cochain rep `ω` of `Ω` against
`chainIncl K (a' ⌢ʳ z)`. Covers/`z` are kept abstract — no whnf descent. -/
theorem relKroneckerH_chainIncl_rcap_eq_kronecker {k m : ℕ} {S K : Set ↑X}
    (z : SingularChain X (k + 1 + m + 1)) (hzK : z ∈ subspaceChains K (k + 1 + m + 1))
    (hzS : chainBoundary X (k + 1 + m) z ∈ subspaceChains S (k + 1 + m))
    (ω : LinearMap.ker (relCoboundaryₗ S (k + 1)))
    (a' : LinearMap.ker (coboundaryₗ (sub K) (m + 1)))
    (hWcyc : RelativeChain.mk S (k + 1)
        (chainIncl K (k + 1) (rcap a'.1 ((subspaceChainsEquiv K (k + 1 + m + 1)).symm ⟨z, hzK⟩)))
        ∈ relCycles S (k + 1)) :
    relKroneckerH S (RelativeCohomology.mk S (k + 1) ω)
        (RelativeHomology.mk S (k + 1)
          ⟨RelativeChain.mk S (k + 1)
              (chainIncl K (k + 1) (rcap a'.1 ((subspaceChainsEquiv K (k + 1 + m + 1)).symm ⟨z, hzK⟩))),
            hWcyc⟩)
      = kronecker ω.1.1
          (chainIncl K (k + 1) (rcap a'.1 ((subspaceChainsEquiv K (k + 1 + m + 1)).symm ⟨z, hzK⟩))) := by
  rw [← kroneckerH_relativeDualityK_mk_eq_relKroneckerH z hzK hzS ω a' hWcyc,
    kroneckerH_relativeDualityK_mk_eq_rcap z hzK hzS ω a']

/-- **RHS-lowering: reverse the `relMvDelta` MV-connecting adjunction.** The RHS of the match,
`⟨g↾, relMvDelta w⟩_{U'∩V'}`, equals `⟨relCohomMvConnecting g↾, w⟩_{U'∪V'}` — the
`relKroneckerH_relCohomMvConnecting` adjunction read right-to-left, moving the MV connecting map back
onto the cohomology side so the homology argument `w` is the bare capped cycle (no `relMvDelta`),
ready for `relKroneckerH_chainIncl_rcap_eq_kronecker`. Covers abstract. -/
theorem relKroneckerH_relMvDelta_eq {M : TopCat} (U' V' : Set ↑M) (hU' : IsOpen U') (hV' : IsOpen V')
    (N : ℕ) (ω : RelativeCohomology (U' ∩ V') (N + 1)) (w : RelativeHomology (U' ∪ V') (N + 2)) :
    relKroneckerH (U' ∩ V') ω (relMvDelta U' V' hU' hV' (N + 1) w)
      = relKroneckerH (U' ∪ V') (SKEFTHawking.SingularRelativeCohomologyMVConnecting.relCohomMvConnecting
          U' V' hU' hV' N ω) w :=
  (SKEFTHawking.SingularRelativeCohomologyMVConnecting.relKroneckerH_relCohomMvConnecting
    U' V' hU' hV' N ω w).symm

/-- **Chain-level cup form of a `chainIncl (cap) ` pairing.** Pairing an ambient cochain `α` against the
inclusion of a right cap `b ⌢ʳ z_sub` (a `sub K`-chain) equals the ambient pairing of the cup
`(pullbackCochain α) ⌣ b` against `z_sub`. Two steps: `kronecker_pullbackCochain` lifts `α` to `sub K`,
then `kronecker_cup_rcap` (reversed) folds the cap into a cup. Abstract in `K, z_sub, α, b`. -/
theorem kronecker_chainIncl_rcap_eq_cup {k l : ℕ} {K : Set ↑X} (α : SingularCochain X k)
    (b : SingularCochain (sub K) l) (z_sub : SingularChain (sub K) (k + l)) :
    kronecker α (chainIncl K k (rcap b z_sub))
      = kronecker (cup (pullbackCochain K k α) b) z_sub := by
  rw [← kronecker_pullbackCochain, kronecker_cup_rcap]

/-- **Abstract MATCH-M reduction to a chain-level cup equality.** Both legs of the connecting-square
MATCH M are `relKroneckerH` pairings of capped fundamental cycles. Lowering the LHS by
`relKroneckerH_chainIncl_rcap_eq_kronecker` + `kronecker_chainIncl_rcap_eq_cup` and the RHS by
`relKroneckerH_relMvDelta_eq` + the same two, both become chain-level cup pairings
`kronecker (cup (pullbackCochain ·) ·) z_sub`. This lemma packages that reduction abstractly: given
the lowered chain-cup equality `hcup`, the two `relKroneckerH` legs agree. The covers are threaded as
the abstract `S, K` of the lowering lemmas — no concrete preimage cover is spelled, dodging the whnf
wall. (The remaining `hcup` is the genuine `absCohomConn`↔`relCohomMvConnecting` cup-duality on the
shared fundamental cycle `z₀`.) -/
theorem relKroneckerH_match_of_chain
    {N p : ℕ} {SL KL SR KR : Set ↑X}
    (gL : LinearMap.ker (relCoboundaryₗ SL (N + 1)))
    (bL : LinearMap.ker (coboundaryₗ (sub KL) (p + 2)))
    (zL : SingularChain X (N + 1 + (p + 1) + 1)) (hzLK : zL ∈ subspaceChains KL (N + 1 + (p + 1) + 1))
    (hzLS : chainBoundary X (N + 1 + (p + 1)) zL ∈ subspaceChains SL (N + 1 + (p + 1)))
    (hWL : RelativeChain.mk SL (N + 1)
        (chainIncl KL (N + 1) (rcap bL.1 ((subspaceChainsEquiv KL (N + 1 + (p + 1) + 1)).symm ⟨zL, hzLK⟩)))
        ∈ relCycles SL (N + 1))
    (gR : LinearMap.ker (relCoboundaryₗ SR (N + 2)))
    (aR : LinearMap.ker (coboundaryₗ (sub KR) (p + 1)))
    (zR : SingularChain X (N + 2 + p + 1)) (hzRK : zR ∈ subspaceChains KR (N + 2 + p + 1))
    (hzRS : chainBoundary X (N + 2 + p) zR ∈ subspaceChains SR (N + 2 + p))
    (hWR : RelativeChain.mk SR (N + 2)
        (chainIncl KR (N + 2) (rcap aR.1 ((subspaceChainsEquiv KR (N + 2 + p + 1)).symm ⟨zR, hzRK⟩)))
        ∈ relCycles SR (N + 2))
    (hcup : kronecker (cup (pullbackCochain KL (N + 1) gL.1.1) bL.1)
          ((subspaceChainsEquiv KL (N + 1 + (p + 1) + 1)).symm ⟨zL, hzLK⟩)
        = kronecker (cup (pullbackCochain KR (N + 2) gR.1.1) aR.1)
          ((subspaceChainsEquiv KR (N + 2 + p + 1)).symm ⟨zR, hzRK⟩)) :
    relKroneckerH SL (RelativeCohomology.mk SL (N + 1) gL)
        (RelativeHomology.mk SL (N + 1)
          ⟨RelativeChain.mk SL (N + 1)
              (chainIncl KL (N + 1) (rcap bL.1
                ((subspaceChainsEquiv KL (N + 1 + (p + 1) + 1)).symm ⟨zL, hzLK⟩))), hWL⟩)
      = relKroneckerH SR (RelativeCohomology.mk SR (N + 2) gR)
          (RelativeHomology.mk SR (N + 2)
            ⟨RelativeChain.mk SR (N + 2)
                (chainIncl KR (N + 2) (rcap aR.1
                  ((subspaceChainsEquiv KR (N + 2 + p + 1)).symm ⟨zR, hzRK⟩))), hWR⟩) := by
  rw [relKroneckerH_chainIncl_rcap_eq_kronecker (k := N) (m := p + 1) zL hzLK hzLS gL bL hWL,
    relKroneckerH_chainIncl_rcap_eq_kronecker (k := N + 1) (m := p) zR hzRK hzRS gR aR hWR,
    kronecker_chainIncl_rcap_eq_cup gL.1.1 bL.1, kronecker_chainIncl_rcap_eq_cup gR.1.1 aR.1, hcup]

end SKEFTHawking.SingularConnSquareClose
