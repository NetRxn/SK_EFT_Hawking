/-
# Phase 5q.H — every AMBIENT class has a cover-partition representative (integral)

The ambient-space mirror of `SingularCoverPartitionMkInt.exists_cover_partition_mkInt` (which is
stated on the union SUBSPACE `sub (U ∪ V)`): for an honest open cover `A ∪ B = univ` of `X`
itself, every homology class `h : Hₙ₊₁(X;ℤ)` has a cover-partitioned cycle representative
`ι_A zA + ι_B zB`. This is exactly the `(zA, zB, hz_cyc)` datum the MV cup–Stokes seam assembly
(`SphereProdStokesPeel.kronecker_cup_cover_seam_cup_form`) and the MV partition readout
(`SingularMvDeltaPartitionInt.mvDelta_cover_partition`) jointly consume: pick the partitioned
representative of the fundamental class, then `mvDeltaInt [z]` IS the class of the extracted seam
chain `t_B`.

Proof: cover-totality gives every chain membership in `subspaceChainsInt (A ∪ B) = subspaceChainsInt
univ` (`mem_subspaceChainsInt_univ`), a barycentric-subdivision iterate lands the representative in
the small-chains submodule `C(A) + C(B)` (`exists_iterate_mvUnionInt`), the sum splits
(`exists_chainIncl_partition_of_mem_mvUnionChainsInt`), and subdivision-invariance in homology
identifies the classes (`homology_mk_singularSd_iterateInt`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularConnSquareLHSSubdivInt
import SKEFTHawking.SingularFundamentalDualityBridgeInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt (chainIncl)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularRelativeMVInt (exists_iterate_mvUnionInt)
open SKEFTHawking.SingularConnSquareLHSSubdivInt
open SKEFTHawking.SingularFundamentalDualityBridgeInt (mem_subspaceChainsInt_univ)

namespace SKEFTHawking.SingularCoverPartitionAmbientInt

/-- **Every ambient class has a cover-partition representative.** For an honest open cover
`A ∪ B = univ` of `X`, every `h : Hₙ₊₁(X;ℤ)` is represented by a cycle of the form
`ι_A zA + ι_B zB` — the input datum of the MV cup–Stokes seam assembly and of
`mvDelta_cover_partition`. -/
theorem exists_cover_partition_ambient {X : TopCat} (A B : Set ↑X)
    (hA : IsOpen A) (hB : IsOpen B) (hcov : A ∪ B = Set.univ) {n : ℕ}
    (h : Homology X (n + 1)) :
    ∃ (zA : SingularChainInt (sub A) (n + 1)) (zB : SingularChainInt (sub B) (n + 1))
      (hz_cyc : chainIncl A (n + 1) zA + chainIncl B (n + 1) zB ∈ cycles X (n + 1)),
      h = Homology.mk X (n + 1) ⟨_, hz_cyc⟩ := by
  obtain ⟨⟨cyc, hcyc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  obtain ⟨m, hm⟩ := exists_iterate_mvUnionInt A B hA hB (n + 1) cyc
    (by rw [hcov]; exact mem_subspaceChainsInt_univ cyc)
  obtain ⟨zA, zB, hsplit⟩ := exists_chainIncl_partition_of_mem_mvUnionChainsInt A B (n + 1) _ hm
  have hSd := singularSd_iterate_mem_cyclesInt X n m cyc hcyc
  have hzc : chainIncl A (n + 1) zA + chainIncl B (n + 1) zB ∈ cycles X (n + 1) :=
    hsplit ▸ hSd
  refine ⟨zA, zB, hzc, ?_⟩
  show Homology.mk X (n + 1) ⟨cyc, hcyc⟩ = _
  rw [homology_mk_singularSd_iterateInt X n m cyc hcyc hSd]
  exact congrArg _ (Subtype.ext hsplit)

end SKEFTHawking.SingularCoverPartitionAmbientInt
