/-
# Phase 5q.H (E1 CSC-PD tower) — every class has a cover-fine partition representative (integral, brick 6c)

The whnf-safe half of the `hcore` assembly (`SingularConnSquareCloseM2Int`). For ANY homology class
`h : Hₙ₊₁(sub (U ∪ V); ℤ)` on the union subspace, there is a cover-fine partition representative:
chains `zA` over `val⁻¹U`, `zB` over `val⁻¹V` (the subspace preimages inside `sub (U ∪ V)`) whose
`chainIncl`-sum is a cycle representing `h`. This is exactly the `(zA, zB, hz_cyc, hw)` datum the
seam-RHS reducer `mvConnecting_eq_seamRHS_of_partitionInt` consumes — packaged as one existence lemma so
the hcore never states the (whnf-heavy) doubly-nested `mvConnectingInt` application freshly.

Proof: pass to a cover-fine iterate `Sdᵐ cyc` (`exists_iterate_mvUnionInt` — cover-totality of the
open preimages), split it along the cover (`exists_chainIncl_partition_of_mem_mvUnionChainsInt`), and use
subdivision-invariance in homology (`homology_mk_singularSd_iterateInt`) to identify the classes. Purely a
class-equality (the RHS-collapse route the mod-2 tower could not use cleanly; clean over ℤ).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularConnSquareCapCoverFineInt
import SKEFTHawking.SingularConnSquareLHSSubdivInt
import SKEFTHawking.SingularSubHomologyMVInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularRelativeMVInt (exists_iterate_mvUnionInt)
open SKEFTHawking.SingularConnSquareCapCoverFineInt (mem_subspaceChains_preimage_unionInt)
open SKEFTHawking.SingularConnSquareLHSSubdivInt

namespace SKEFTHawking.SingularCoverPartitionMkInt

variable {X : TopCat}

/-- **Every class on the union subspace has a cover-fine partition representative** (integral). For any
`h : Hₙ₊₁(sub (U ∪ V); ℤ)` there exist `zA` over `val⁻¹U`, `zB` over `val⁻¹V` whose `chainIncl`-sum is a
cycle representing `h`. The whnf-safe `(zA, zB, hz_cyc, hw)` datum for `mvConnecting_eq_seamRHS_of_partitionInt`. -/
theorem exists_cover_partition_mkInt (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) {n : ℕ}
    (h : Homology (sub (U ∪ V)) (n + 1)) :
    ∃ (zA : SingularChainInt (sub (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V)))) (n + 1))
      (zB : SingularChainInt (sub (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V)))) (n + 1))
      (hz_cyc : chainIncl (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (n + 1) zA
          + chainIncl (Subtype.val ⁻¹' V) (n + 1) zB ∈ cycles (sub (U ∪ V)) (n + 1)),
      h = Homology.mk (sub (U ∪ V)) (n + 1) ⟨_, hz_cyc⟩ := by
  obtain ⟨⟨cyc, hcyc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  obtain ⟨m, hm⟩ := exists_iterate_mvUnionInt (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V)))
    (Subtype.val ⁻¹' V) (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
    (n + 1) cyc (mem_subspaceChains_preimage_unionInt U V (n + 1) cyc)
  obtain ⟨zA, zB, hsplit⟩ := exists_chainIncl_partition_of_mem_mvUnionChainsInt _ _ (n + 1) _ hm
  have hSd := singularSd_iterate_mem_cyclesInt (sub (U ∪ V)) n m cyc hcyc
  have hzc : chainIncl (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (n + 1) zA
      + chainIncl (Subtype.val ⁻¹' V) (n + 1) zB ∈ cycles (sub (U ∪ V)) (n + 1) := hsplit ▸ hSd
  refine ⟨zA, zB, hzc, ?_⟩
  show Homology.mk (sub (U ∪ V)) (n + 1) ⟨cyc, hcyc⟩ = _
  rw [homology_mk_singularSd_iterateInt (sub (U ∪ V)) n m cyc hcyc hSd]
  exact congrArg _ (Subtype.ext hsplit)

end SKEFTHawking.SingularCoverPartitionMkInt
