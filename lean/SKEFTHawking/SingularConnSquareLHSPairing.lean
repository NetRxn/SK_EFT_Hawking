import Mathlib
import SKEFTHawking.SingularMvDeltaPartition

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4-LHSPair) — the LHS pairing of the connecting square

The **non-circular** LHS half of the connecting-square seam-match pairing: pairing a cohomology class
`a'` against the bottom-row Mayer–Vietoris connecting `mvConnecting` of a cover-partitioned cycle reduces
— via the explicit chain action `mvConnecting_cover_partition` (M2) and `kroneckerH_mk_mk` — to the
**chain-level** Kronecker pairing of `a'`'s cocycle rep against the boundary-extraction `∂zB` of the
`B`-part.

This is the LHS counterpart of the RHS adjunction `kroneckerH_relativeDualityK_relCohomMvConnecting`
(which moves the cohomology MV connecting off `g` onto the homology as `relMvDelta`). Both legs of the
connecting square, paired against `a'`, are thereby explicit chain pairings — *without* routing the LHS
through `absCohomConn` (which is Kronecker-defined ⟹ circular). Stated over an **abstract** cover `A, B`
(no `val⁻¹` preimage in the type) so it elaborates without the `whnf` heartbeat wall.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularPairLES
  SKEFTHawking.SingularExcisionIso SKEFTHawking.SingularMayerVietorisLES
  SKEFTHawking.SingularMvDeltaPartition

namespace SKEFTHawking.SingularConnSquareLHSPairing

variable {X : TopCat}

/-- **LHS pairing of the connecting square** (abstract cover): pairing `a'` against `mvConnecting` of a
cover-partitioned cycle `chainIncl A zA + chainIncl B zB` equals the chain pairing of `a'`'s rep against
`∂zB` (boundary-extracted into the `sub (restr A B)` seam). -/
theorem kroneckerH_mvConnecting_cover_partition (A B : Set ↑X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set ↑X)), interior U) = Set.univ)
    (zA : SingularChain (sub A) (n + 1)) (zB : SingularChain (sub B) (n + 1))
    (hz_cyc : chainIncl A (n + 1) zA + chainIncl B (n + 1) zB ∈ cycles X (n + 1))
    (a' : LinearMap.ker (coboundaryₗ (sub (restr A B)) n)) :
    kroneckerH (X := sub (restr A B)) n (Submodule.Quotient.mk a')
        (mvConnecting A B n hcov (Homology.mk X (n + 1) ⟨_, hz_cyc⟩))
      = kronecker a'.1
          (boundaryExtract (restr A B) n ⟨zB, zB_mem_relCycleLift A B n zA zB hz_cyc⟩) := by
  rw [mvConnecting_cover_partition]
  rfl

end SKEFTHawking.SingularConnSquareLHSPairing
