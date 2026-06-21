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

/-- **Chain-level cup pairing as a homology cap-pairing.** For a cocycle `b` (`δb = 0`) over `sub K`
and a chain `z_sub` whose cap `cap β z_sub` is a cycle, the chain-level cup pairing
`kronecker (cup β b) z_sub` is the homology cap–Kronecker pairing
`⟨[b], (capH … [β]) [z_sub]⟩`. By `kronecker_cup_cap` it is `kronecker b (cap β z_sub)`, which is
`kroneckerH (mk b) (mk (cap β z_sub))` (definitional `kroneckerH_mk_mk`); and `capH … = mk ∘ cap`
on representatives. The homology-level entry point for the M5a cup–cap adjunction. -/
theorem kronecker_cup_eq_kroneckerH_cap {l m : ℕ} {K : Set ↑X}
    (β : LinearMap.ker (coboundaryₗ (sub K) m)) (b : LinearMap.ker (coboundaryₗ (sub K) l))
    (z_sub : SingularChain (sub K) (m + l))
    (hcap : cap β.1 z_sub ∈ cycles (sub K) l) :
    kronecker (cup β.1 b.1) z_sub
      = kroneckerH (X := sub K) l (Submodule.Quotient.mk b)
          (Homology.mk (sub K) l ⟨cap β.1 z_sub, hcap⟩) := by
  rw [kronecker_cup_cap]; rfl

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

/-- **MATCH-M reduction with the RHS in `relMvDelta` form** (the shape of the actual `hmatch`). The
RHS pairing is over `U'∩V'` with the homology argument `relMvDelta` of the capped cycle; reversing the
`relCohomMvConnecting` adjunction (`relKroneckerH_relMvDelta_eq`) puts it in the bare form consumed by
`relKroneckerH_match_of_chain`. The RHS cohomology becomes `relCohomMvConnecting gR` — supplied here as
an abstract cocycle rep `gRconn` (with the defining equation `hgRconn`), so the heavy
`relCohomMvConnecting` composite is a unification variable, never elaborated in the statement type
(dodging the whnf wall). -/
theorem relKroneckerH_match_of_chain_relMvDelta
    {N p : ℕ} {SL KL KR : Set ↑X} {U' V' : Set ↑X} (hU' : IsOpen U') (hV' : IsOpen V')
    (gL : LinearMap.ker (relCoboundaryₗ SL (N + 1)))
    (bL : LinearMap.ker (coboundaryₗ (sub KL) (p + 2)))
    (zL : SingularChain X (N + 1 + (p + 1) + 1)) (hzLK : zL ∈ subspaceChains KL (N + 1 + (p + 1) + 1))
    (hzLS : chainBoundary X (N + 1 + (p + 1)) zL ∈ subspaceChains SL (N + 1 + (p + 1)))
    (hWL : RelativeChain.mk SL (N + 1)
        (chainIncl KL (N + 1) (rcap bL.1 ((subspaceChainsEquiv KL (N + 1 + (p + 1) + 1)).symm ⟨zL, hzLK⟩)))
        ∈ relCycles SL (N + 1))
    (gR : RelativeCohomology (U' ∩ V') (N + 1))
    (gRconn : LinearMap.ker (relCoboundaryₗ (U' ∪ V') (N + 2)))
    (hgRconn : RelativeCohomology.mk (U' ∪ V') (N + 2) gRconn
      = SKEFTHawking.SingularRelativeCohomologyMVConnecting.relCohomMvConnecting U' V' hU' hV' N gR)
    (aR : LinearMap.ker (coboundaryₗ (sub KR) (p + 1)))
    (zR : SingularChain X (N + 2 + p + 1)) (hzRK : zR ∈ subspaceChains KR (N + 2 + p + 1))
    (hzRS : chainBoundary X (N + 2 + p) zR ∈ subspaceChains (U' ∪ V') (N + 2 + p))
    (hWR : RelativeChain.mk (U' ∪ V') (N + 2)
        (chainIncl KR (N + 2) (rcap aR.1 ((subspaceChainsEquiv KR (N + 2 + p + 1)).symm ⟨zR, hzRK⟩)))
        ∈ relCycles (U' ∪ V') (N + 2))
    (hcup : kronecker (cup (pullbackCochain KL (N + 1) gL.1.1) bL.1)
          ((subspaceChainsEquiv KL (N + 1 + (p + 1) + 1)).symm ⟨zL, hzLK⟩)
        = kronecker (cup (pullbackCochain KR (N + 2) gRconn.1.1) aR.1)
          ((subspaceChainsEquiv KR (N + 2 + p + 1)).symm ⟨zR, hzRK⟩)) :
    relKroneckerH SL (RelativeCohomology.mk SL (N + 1) gL)
        (RelativeHomology.mk SL (N + 1)
          ⟨RelativeChain.mk SL (N + 1)
              (chainIncl KL (N + 1) (rcap bL.1
                ((subspaceChainsEquiv KL (N + 1 + (p + 1) + 1)).symm ⟨zL, hzLK⟩))), hWL⟩)
      = relKroneckerH (U' ∩ V') gR
          (relMvDelta U' V' hU' hV' (N + 1)
            (RelativeHomology.mk (U' ∪ V') (N + 2)
              ⟨RelativeChain.mk (U' ∪ V') (N + 2)
                  (chainIncl KR (N + 2) (rcap aR.1
                    ((subspaceChainsEquiv KR (N + 2 + p + 1)).symm ⟨zR, hzRK⟩))), hWR⟩)) := by
  rw [relKroneckerH_relMvDelta_eq U' V' hU' hV' N gR, ← hgRconn]
  exact relKroneckerH_match_of_chain gL bL zL hzLK hzLS hWL gRconn aR zR hzRK hzRS hWR hcup

section
variable [T2Space ↑X]

open SKEFTHawking.SingularCSCMayerVietorisConnecting
  SKEFTHawking.SingularRelativeCohomologyMVConnecting in
/-- **The connecting-square per-`K` cycle core, reduced to the concrete chain-level cup identity.**
Discharges the `hmatch` of `SingularConnSquareMatch.subHomConnecting_openDuality_of_match` using the
M6c `relMvDelta`-shaped reduction, leaving the single per-`K` concrete cup identity `hcup` (the
cap-naturality of the MV connecting map on the shared fundamental cycle `z₀`). The
`relCohomMvConnecting` rep is obtained by `Quotient.mk_surjective`, so it stays a unification variable
(no whnf wall). -/
theorem subHomConnecting_openDuality_of_hcup {N p : ℕ} {U V : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChain X (N + p + 3)) (hz₀ : chainBoundary X (N + p + 2) z₀ = 0)
    (K : SingularCompactsInOpen.CompactsIn (U ∪ V))
    (g : cohomGW (U ∪ V) (N + 1) K)
    (hcup : ∀ (a'rep : LinearMap.ker (coboundaryₗ (sub (U ∩ V)) (p + 1)))
        (b : LinearMap.ker (coboundaryₗ (sub (U ∪ V)) (p + 2)))
        (grep : LinearMap.ker (relCoboundaryₗ ((↑K.1 : Set ↑X)ᶜ) (N + 1)))
        (gRconn : LinearMap.ker (relCoboundaryₗ
          ((↑(legSplitU U V hU hV K).1 : Set ↑X)ᶜ ∪ (↑(legSplitV U V hU hV K).1 : Set ↑X)ᶜ) (N + 2))),
        RelativeCohomology.mk ((↑K.1 : Set ↑X)ᶜ) (N + 1) grep
            = (g : RelativeCohomology ((↑K.1 : Set ↑X)ᶜ) (N + 1)) →
        kronecker (cup (pullbackCochain (U ∪ V) (N + 1) grep.1.1) b.1)
            ((subspaceChainsEquiv (U ∪ V) (N + 1 + (p + 1) + 1)).symm
              ⟨fundCycleW (hU.union hV)
                  (SingularOpenDualityMVConnSquare.castChain
                    (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
                  (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero
                    (by omega) (by omega) z₀ hz₀) K,
                fundCycleW_mem_W (hU.union hV) _ _ _⟩)
          = kronecker (cup (pullbackCochain (U ∩ V) (N + 2) gRconn.1.1) a'rep.1)
            ((subspaceChainsEquiv (U ∩ V) (N + 2 + p + 1)).symm
              ⟨fundCycleW (hU.inter hV)
                  (SingularOpenDualityMVConnSquare.castChain
                    (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
                  (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero
                    (by omega) (by omega) z₀ hz₀)
                  (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K)),
                fundCycleW_mem_W (hU.inter hV) _ _ _⟩)) :
    SKEFTHawking.SingularSubHomologyMV.subHomConnecting U V hU hV (p + 1)
        (SKEFTHawking.SingularOpenDuality.legW (k := N + 1) (m := p + 1) (hU.union hV)
          (SingularOpenDualityMVConnSquare.castChain
            (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
          (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
          K g)
      = SKEFTHawking.SingularOpenDuality.openDuality (k := N + 2) (m := p) (hU.inter hV)
          (SingularOpenDualityMVConnSquare.castChain
            (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
          (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
          (SKEFTHawking.SingularCSCMayerVietorisConnecting.legδ U V hU hV N K g) := by
  apply SingularConnSquareMatch.subHomConnecting_openDuality_of_match hU hV z₀ hz₀ K g
  intro a'rep b hb
  obtain ⟨gL, hgL⟩ := Submodule.Quotient.mk_surjective _ g
  rw [← hgL]
  obtain ⟨gRconn, hgRconn⟩ := Submodule.Quotient.mk_surjective _
    (relCohomMvConnecting ((↑(legSplitU U V hU hV K).1 : Set ↑X)ᶜ)
      ((↑(legSplitV U V hU hV K).1 : Set ↑X)ᶜ)
      (legSplitU U V hU hV K).1.isCompact'.isClosed.isOpen_compl
      (legSplitV U V hU hV K).1.isCompact'.isClosed.isOpen_compl N
      ((SingularRelativeCohomologyRestrict.relCohomRestrict
          (Set.inter_subset_inter subset_rfl subset_rfl) (N + 1))
        ((SingularCompactlySupportedTop.relCohomSetCongr
            (by rw [legSplit_cover U V hU hV K, Set.compl_union]) (N + 1)
            (Submodule.Quotient.mk gL)))))
  refine relKroneckerH_match_of_chain_relMvDelta
    (legSplitU U V hU hV K).1.isCompact'.isClosed.isOpen_compl
    (legSplitV U V hU hV K).1.isCompact'.isClosed.isOpen_compl
    gL b _ (fundCycleW_mem_W (hU.union hV) _ _ _) (fundCycleW_boundary (hU.union hV) _ _ _) ?_
    _ gRconn hgRconn a'rep _ (fundCycleW_mem_W (hU.inter hV) _ _ _) ?_ ?_
    (hcup a'rep b gL gRconn hgL)
  · have hbdy := fundCycleW_boundary (hU.inter hV)
      (SingularOpenDualityMVConnSquare.castChain (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
      (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K))
    rw [infCompact_coe U V (legSplitU U V hU hV K) (legSplitV U V hU hV K), Set.compl_inter] at hbdy
    exact hbdy

open SKEFTHawking.SingularCSCMayerVietorisConnecting
  SKEFTHawking.SingularRelativeCohomologyMVConnecting in
/-- **Linked variant of `subHomConnecting_openDuality_of_hcup`.** Identical reduction, but the `hcup`
hypothesis is *constrained* to the specific reps that actually arise — `b = absCohomConn(a'rep)` and
`gRconn = relCohomMvConnecting(grep)`. This makes `hcup` the TRUE cap-naturality cup-duality on `z₀`
(the unconstrained `_of_hcup` version is false ∀ `b`/`gRconn`, hence undischargeable). Proof is
`_of_hcup`'s body, passing the in-context `hb`/`hgRconn` links to the constrained `hcup`. -/
theorem subHomConnecting_openDuality_of_hcup_linked {N p : ℕ} {U V : Set ↑X} (hU : IsOpen U)
    (hV : IsOpen V) (z₀ : SingularChain X (N + p + 3)) (hz₀ : chainBoundary X (N + p + 2) z₀ = 0)
    (K : SingularCompactsInOpen.CompactsIn (U ∪ V))
    (g : cohomGW (U ∪ V) (N + 1) K)
    (hcup : ∀ (a'rep : LinearMap.ker (coboundaryₗ (sub (U ∩ V)) (p + 1)))
        (b : LinearMap.ker (coboundaryₗ (sub (U ∪ V)) (p + 2)))
        (grep : LinearMap.ker (relCoboundaryₗ ((↑K.1 : Set ↑X)ᶜ) (N + 1)))
        (gRconn : LinearMap.ker (relCoboundaryₗ
          ((↑(legSplitU U V hU hV K).1 : Set ↑X)ᶜ ∪ (↑(legSplitV U V hU hV K).1 : Set ↑X)ᶜ) (N + 2))),
        RelativeCohomology.mk ((↑K.1 : Set ↑X)ᶜ) (N + 1) grep
            = (g : RelativeCohomology ((↑K.1 : Set ↑X)ᶜ) (N + 1)) →
        Submodule.Quotient.mk b
            = SingularSubHomologyMVCohomConn.absCohomConn U V hU hV p (Submodule.Quotient.mk a'rep) →
        Submodule.Quotient.mk gRconn
            = relCohomMvConnecting ((↑(legSplitU U V hU hV K).1 : Set ↑X)ᶜ)
                ((↑(legSplitV U V hU hV K).1 : Set ↑X)ᶜ)
                (legSplitU U V hU hV K).1.isCompact'.isClosed.isOpen_compl
                (legSplitV U V hU hV K).1.isCompact'.isClosed.isOpen_compl N
                ((SingularRelativeCohomologyRestrict.relCohomRestrict
                    (Set.inter_subset_inter subset_rfl subset_rfl) (N + 1))
                  ((SingularCompactlySupportedTop.relCohomSetCongr
                      (by rw [legSplit_cover U V hU hV K, Set.compl_union]) (N + 1)
                      (Submodule.Quotient.mk grep)))) →
        kronecker (cup (pullbackCochain (U ∪ V) (N + 1) grep.1.1) b.1)
            ((subspaceChainsEquiv (U ∪ V) (N + 1 + (p + 1) + 1)).symm
              ⟨fundCycleW (hU.union hV)
                  (SingularOpenDualityMVConnSquare.castChain
                    (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
                  (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero
                    (by omega) (by omega) z₀ hz₀) K,
                fundCycleW_mem_W (hU.union hV) _ _ _⟩)
          = kronecker (cup (pullbackCochain (U ∩ V) (N + 2) gRconn.1.1) a'rep.1)
            ((subspaceChainsEquiv (U ∩ V) (N + 2 + p + 1)).symm
              ⟨fundCycleW (hU.inter hV)
                  (SingularOpenDualityMVConnSquare.castChain
                    (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
                  (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero
                    (by omega) (by omega) z₀ hz₀)
                  (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K)),
                fundCycleW_mem_W (hU.inter hV) _ _ _⟩)) :
    SKEFTHawking.SingularSubHomologyMV.subHomConnecting U V hU hV (p + 1)
        (SKEFTHawking.SingularOpenDuality.legW (k := N + 1) (m := p + 1) (hU.union hV)
          (SingularOpenDualityMVConnSquare.castChain
            (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
          (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
          K g)
      = SKEFTHawking.SingularOpenDuality.openDuality (k := N + 2) (m := p) (hU.inter hV)
          (SingularOpenDualityMVConnSquare.castChain
            (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
          (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
          (SKEFTHawking.SingularCSCMayerVietorisConnecting.legδ U V hU hV N K g) := by
  apply SingularConnSquareMatch.subHomConnecting_openDuality_of_match hU hV z₀ hz₀ K g
  intro a'rep b hb
  obtain ⟨gL, hgL⟩ := Submodule.Quotient.mk_surjective _ g
  rw [← hgL]
  obtain ⟨gRconn, hgRconn⟩ := Submodule.Quotient.mk_surjective _
    (relCohomMvConnecting ((↑(legSplitU U V hU hV K).1 : Set ↑X)ᶜ)
      ((↑(legSplitV U V hU hV K).1 : Set ↑X)ᶜ)
      (legSplitU U V hU hV K).1.isCompact'.isClosed.isOpen_compl
      (legSplitV U V hU hV K).1.isCompact'.isClosed.isOpen_compl N
      ((SingularRelativeCohomologyRestrict.relCohomRestrict
          (Set.inter_subset_inter subset_rfl subset_rfl) (N + 1))
        ((SingularCompactlySupportedTop.relCohomSetCongr
            (by rw [legSplit_cover U V hU hV K, Set.compl_union]) (N + 1)
            (Submodule.Quotient.mk gL)))))
  refine relKroneckerH_match_of_chain_relMvDelta
    (legSplitU U V hU hV K).1.isCompact'.isClosed.isOpen_compl
    (legSplitV U V hU hV K).1.isCompact'.isClosed.isOpen_compl
    gL b _ (fundCycleW_mem_W (hU.union hV) _ _ _) (fundCycleW_boundary (hU.union hV) _ _ _) ?_
    _ gRconn hgRconn a'rep _ (fundCycleW_mem_W (hU.inter hV) _ _ _) ?_ ?_
    (hcup a'rep b gL gRconn hgL hb hgRconn)
  · have hbdy := fundCycleW_boundary (hU.inter hV)
      (SingularOpenDualityMVConnSquare.castChain (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
      (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K))
    rw [infCompact_coe U V (legSplitU U V hU hV K) (legSplitV U V hU hV K), Set.compl_inter] at hbdy
    exact hbdy

end

end SKEFTHawking.SingularConnSquareClose
