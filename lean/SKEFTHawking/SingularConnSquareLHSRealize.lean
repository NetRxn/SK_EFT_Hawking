import Mathlib
import SKEFTHawking.SingularAbsCohomConnGeom
import SKEFTHawking.SingularCoverPartitionExist

/-!
# Phase 5q.F (w₂-foundation) — abstract-cycle wrapper for the LHS cover-split realization

Wraps `SingularAbsCohomConnGeom.kroneckerH_absCohomConn_cover_partition` so it applies to an ARBITRARY
cycle `w : cycles (sub (U ∪ V)) (p+1+1)` — the cover-split is done internally via
`SingularCoverPartitionExist.exists_mvUnion_partition`. Stating it over an **abstract** `w` keeps the
cover-split's `rw [hclass]` off any concretely-nested `pullbackDualityₗ` carrier (which triggers the
200k-`whnf` heartbeat wall when `w` is the concrete cap cycle, as `SingularConnSquareCloseNC` discovered).
The consumer applies this by a STRUCTURAL `rw` (`Homology.mk ?w` ↦ its concrete cycle = a metavar
assignment, not a `whnf` reduction).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularSubsetHomology
  SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularExcisionIso
  SKEFTHawking.SingularMayerVietorisLES SKEFTHawking.SingularMvDeltaPartition
  SKEFTHawking.SingularSubHomologyMV SKEFTHawking.SingularSubHomologyMVCohomConn
  SKEFTHawking.SingularConnSquareLHSLeg SKEFTHawking.SingularConnSquareLHSExplicit
  SKEFTHawking.SingularPairLES SKEFTHawking.SingularAbsCohomConnGeom
  SKEFTHawking.SingularCoverPartitionExist

namespace SKEFTHawking.SingularConnSquareLHSRealize

variable {X : TopCat}

/-- **LHS cover-split realization for an abstract cycle.** Pairing `absCohomConn a'` against the class of
an arbitrary cycle `w` of `sub (U ∪ V)` equals the chain pairing of `a'`'s rep against a seam cycle pushed
through both seam homeomorphisms — the abstract-`w` form of
`SingularAbsCohomConnGeom.kroneckerH_absCohomConn_cover_partition` (cover-split internally). -/
theorem kroneckerH_absCohomConn_coverClass (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) (p : ℕ)
    (a' : LinearMap.ker (coboundaryₗ (sub (U ∩ V)) (p + 1)))
    (w : cycles (sub (U ∪ V)) (p + 1 + 1)) :
    ∃ z : cycles (sub (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V))) (p + 1),
      kroneckerH (X := sub (U ∪ V)) (p + 1 + 1)
          (absCohomConn U V hU hV p (Cohomology.mk (sub (U ∩ V)) (p + 1) a'))
          (Homology.mk (sub (U ∪ V)) (p + 1 + 1) w)
        = kronecker a'.1
            (mapChain ⟨subSeamHomeo (Set.inter_subset_left.trans Set.subset_union_left)
                (fun _ => Iff.rfl), (subSeamHomeo (Set.inter_subset_left.trans Set.subset_union_left)
                  (fun _ => Iff.rfl)).continuous⟩ (p + 1)
              (mapChain ⟨seamHomeo (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V),
                (seamHomeo (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)).continuous⟩
                  (p + 1) (z : SingularChain _ (p + 1)))) := by
  obtain ⟨zA, zB, hcyc', hclass⟩ := SingularCoverPartitionExist.exists_mvUnion_partition
    (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V) (hU.preimage continuous_subtype_val)
    (hV.preimage continuous_subtype_val) (p + 1) w
    (SingularConnSquareLHSExplicit.mem_subspaceChains_preimage_union U V (p + 1 + 1) w)
  rw [hclass]
  obtain ⟨z, _hsh, hkron⟩ := SingularAbsCohomConnGeom.kroneckerH_absCohomConn_cover_partition
    U V hU hV p a' zA zB hcyc'
  exact ⟨z, hkron⟩

end SKEFTHawking.SingularConnSquareLHSRealize
