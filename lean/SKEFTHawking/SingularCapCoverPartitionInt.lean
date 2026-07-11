/-
# Phase 5q.H (E1 CSC-PD tower) — the canonical cap-cover-partition (integral, brick 6e-a)

Integral mirror of `SingularConnSquareRHSScaffold.exists_cap_cover_partition`. For a cochain `g` and a
`(A∪B)`-supported chain `z`, a cover-fine subdivision `Sdᵐ z` splits along the cover `{A,B}` AND its cap
`capInt g (Sdᵐ z)` splits **as genuine caps on each part**:
  `capInt g (Sdᵐ z) = chainIncl A (capInt (g|_A) u) + chainIncl B (capInt (g|_B) w)`.
This is the canonical (not arbitrary) partition the seam-match uses: the `B`-part `capInt (g|_B) w` is a
literal cap, so `∂`(it) is computable by `capInt_cocycle_chainMap` and matches the `indUf`/coboundary shape
of `relCohomMvConnectingInt`. Proof = cover-fine split (`exists_iterate_mvUnionInt` +
`exists_chainIncl_partition_of_mem_mvUnionChainsInt`) + `capInt_chainIncl` (×2).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularCapChainInclInt
import SKEFTHawking.SingularRelativeMVInt
import SKEFTHawking.SingularConnSquareLHSSubdivInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularSubdivisionInt (singularSdInt)
open SKEFTHawking.SingularCapChainInclInt (capInt_chainIncl pullbackCochainInt)
open SKEFTHawking.SingularRelativeMVInt (exists_iterate_mvUnionInt)
open SKEFTHawking.SingularConnSquareLHSSubdivInt (exists_chainIncl_partition_of_mem_mvUnionChainsInt)

namespace SKEFTHawking.SingularCapCoverPartitionInt

variable {M : TopCat}

/-- **The canonical cap-cover-partition** (integral). A cover-fine subdivision of an `(A∪B)`-supported chain
`z` splits along `{A,B}`, and the cap `capInt g` of it splits as `chainIncl`-sum of genuine caps on each
part. The `B`-part is `capInt (pullbackCochainInt B g) w` — a literal cap (not a homology-slack witness). -/
theorem exists_cap_cover_partitionInt {k l : ℕ} (A B : Set ↑M) (hA : IsOpen A) (hB : IsOpen B)
    (g : SingularCochainInt M k) (z : SingularChainInt M (k + l))
    (hz : z ∈ subspaceChainsInt (A ∪ B) (k + l)) :
    ∃ (m : ℕ) (u : SingularChainInt (sub A) (k + l)) (w : SingularChainInt (sub B) (k + l)),
      (⇑(singularSdInt M (k + l)))^[m] z = chainIncl A (k + l) u + chainIncl B (k + l) w ∧
      capInt (m := l) g ((⇑(singularSdInt M (k + l)))^[m] z)
        = chainIncl A l (capInt (m := l) (pullbackCochainInt A k g) u)
          + chainIncl B l (capInt (m := l) (pullbackCochainInt B k g) w) := by
  obtain ⟨m, hm⟩ := exists_iterate_mvUnionInt A B hA hB (k + l) z hz
  obtain ⟨u, w, hsplit⟩ := exists_chainIncl_partition_of_mem_mvUnionChainsInt A B (k + l) _ hm
  refine ⟨m, u, w, hsplit, ?_⟩
  rw [hsplit, map_add, capInt_chainIncl, capInt_chainIncl]

end SKEFTHawking.SingularCapCoverPartitionInt
