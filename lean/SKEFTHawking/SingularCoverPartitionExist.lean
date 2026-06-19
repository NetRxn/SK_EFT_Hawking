import Mathlib
import SKEFTHawking.SingularConnSquareLHSExplicit

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4-M8) — cover-partition existence for a homology class

Any homology class of `Y` whose cycle representative is supported in `A ∪ B` is the class of a
**cover-fine partition** `chainIncl A zA + chainIncl B zB` (subordinate to the open cover `{A, B}`):
enough barycentric subdivisions make the cycle `C(A)+C(B)`-small (`exists_iterate_mvUnion`), subdivision
does not change the homology class (`homology_mk_singularSd_iterate`), and an `mvUnionChains` member splits
into the partition (`exists_chainIncl_partition_of_mem_mvUnionChains`). Stated over an **abstract** cover
`A, B` (no `val⁻¹` preimage spelled in the type) so it elaborates without the `whnf` heartbeat wall; the
PD6f-c4 connecting-square LHS instantiates it at `Y := sub (U ∪ V)`, `A := val⁻¹U`, `B := val⁻¹V` (whose
union is `univ`, so every cap cycle qualifies) to feed `mvDelta_cover_partition` (M2).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
  SKEFTHawking.SingularRelativeMV SKEFTHawking.SingularConnSquareLHSExplicit
  SKEFTHawking.SingularSubdivision

namespace SKEFTHawking.SingularCoverPartitionExist

variable {Y : TopCat}

/-- **Cover-partition existence** (abstract cover `A, B`): a homology class of `Y` whose cycle rep is
supported in `A ∪ B` equals the class of a cover-fine partition `chainIncl A zA + chainIncl B zB`. -/
theorem exists_mvUnion_partition (A B : Set ↑Y) (hA : IsOpen A) (hB : IsOpen B) (n : ℕ)
    (z : cycles Y (n + 1)) (hzAB : (z : SingularChain Y (n + 1)) ∈ subspaceChains (A ∪ B) (n + 1)) :
    ∃ (zA : SingularChain (sub A) (n + 1)) (zB : SingularChain (sub B) (n + 1))
      (hcyc : chainIncl A (n + 1) zA + chainIncl B (n + 1) zB ∈ cycles Y (n + 1)),
      Homology.mk Y (n + 1) z = Homology.mk Y (n + 1) ⟨_, hcyc⟩ := by
  obtain ⟨m, hm⟩ := exists_iterate_mvUnion A B hA hB (n + 1) (z : SingularChain Y (n + 1)) hzAB
  obtain ⟨zA, zB, hpart⟩ := exists_chainIncl_partition_of_mem_mvUnionChains A B (n + 1) _ hm
  have hSdcyc : (⇑(singularSd Y (n + 1)))^[m] (z : SingularChain Y (n + 1)) ∈ cycles Y (n + 1) :=
    singularSd_iterate_mem_cycles Y n m (z : SingularChain Y (n + 1)) z.2
  have hcyc : chainIncl A (n + 1) zA + chainIncl B (n + 1) zB ∈ cycles Y (n + 1) := hpart ▸ hSdcyc
  refine ⟨zA, zB, hcyc, ?_⟩
  rw [show Homology.mk Y (n + 1) z
      = Homology.mk Y (n + 1) ⟨(z : SingularChain Y (n + 1)), z.2⟩ from rfl,
    homology_mk_singularSd_iterate Y n m (z : SingularChain Y (n + 1)) z.2 hSdcyc]
  exact congrArg (Homology.mk Y (n + 1)) (Subtype.ext hpart)

end SKEFTHawking.SingularCoverPartitionExist
