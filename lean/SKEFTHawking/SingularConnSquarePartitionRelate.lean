import Mathlib
import SKEFTHawking.SingularMvDeltaPartition

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4) — partition-independence of the connecting cycle

`boundaryExtract_class_eq_of_partition_homologous`: two cover-partitions of *homologous* cycles have
*equal* `boundaryExtract` V-part homology classes. This is just the well-definedness of the
Mayer–Vietoris connecting map `mvConnecting` on homology classes, read through
`mvConnecting_cover_partition` (which computes `mvConnecting [partition] = [boundaryExtract zB]`).

The connecting-square `hLHS` needs exactly this: the GIVEN cover-partition `zB` (from the `hcore`
hypothesis) and the CLEAN cap-partition V-part `cap (g̃|_V) w` (from `exists_cap_cover_partition`) are
homologous (both represent the legW class), so their connecting cycles are seam-homologous, hence pair
equally against the test cocycle `ωrep` — letting the proof work with the clean cap-realized V-part.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
  SKEFTHawking.SingularPairLES SKEFTHawking.SingularExcisionIso

namespace SKEFTHawking.SingularConnSquarePartitionRelate

open SKEFTHawking.SingularMvDeltaPartition

variable {X : TopCat}

/-- **Partition-independence of the connecting cycle**: for two cover-partitions of homologous cycles
`[chainIncl zA + chainIncl zB] = [chainIncl zA' + chainIncl zB']`, the `boundaryExtract` V-part classes
agree. (The MV connecting map `mvConnecting` is well-defined on homology, so applying it to the equal
classes — via `mvConnecting_cover_partition` — equates the two `[boundaryExtract zB]`.) -/
theorem boundaryExtract_class_eq_of_partition_homologous (A B : Set ↑X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set ↑X)), interior U) = Set.univ)
    (zA zA' : SingularChain (sub A) (n + 1)) (zB zB' : SingularChain (sub B) (n + 1))
    (hz_cyc : chainIncl A (n + 1) zA + chainIncl B (n + 1) zB ∈ cycles X (n + 1))
    (hz_cyc' : chainIncl A (n + 1) zA' + chainIncl B (n + 1) zB' ∈ cycles X (n + 1))
    (hhom : Homology.mk X (n + 1) ⟨_, hz_cyc⟩ = Homology.mk X (n + 1) ⟨_, hz_cyc'⟩) :
    Homology.mk (sub (restr A B)) n
        ⟨boundaryExtract (restr A B) n ⟨zB, zB_mem_relCycleLift A B n zA zB hz_cyc⟩,
          boundaryExtract_mem_cycles (restr A B) n _⟩
      = Homology.mk (sub (restr A B)) n
        ⟨boundaryExtract (restr A B) n ⟨zB', zB_mem_relCycleLift A B n zA' zB' hz_cyc'⟩,
          boundaryExtract_mem_cycles (restr A B) n _⟩ := by
  rw [← mvConnecting_cover_partition A B n hcov zA zB hz_cyc,
    ← mvConnecting_cover_partition A B n hcov zA' zB' hz_cyc', hhom]

end SKEFTHawking.SingularConnSquarePartitionRelate
