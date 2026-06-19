import Mathlib
import SKEFTHawking.SingularMayerVietorisLES

/-!
# Phase 5q.F (w₂-foundation, brick PD6f-c4-M2) — the absolute MV connecting map's chain action

The (absolute) Mayer–Vietoris connecting map `mvDelta A B n hcov : Hₙ₊₁(X) → Hₙ(A∩B)` sends the class
of a cover-partitioned cycle to the class of the boundary of its `A`-part (equivalently, its `B`-part;
over `ℤ/2` they agree in the seam). Concretely, for a cycle `z` of `X` written subordinate to the
cover `{A, B}` as `z = chainIncl A zA + chainIncl B zB`, the connecting map's pre-seam form
`mvConnecting A B n hcov [z]` is the class of `∂zB` realized in the `sub (restr A B)` representation,
i.e. `[boundaryExtract (restr A B) n ⟨zB, _⟩]` — and `mvDelta` is this post-composed with
`seamHomologyEquiv`.

This is the LHS-side analogue of `SingularRelMvDeltaChain.relMvDelta_iotaEquiv_relLiftToQHom` (the
same explicit chain action for the *relative* MV connecting map). It is the explicit chain form needed
to match the two legs of the Poincaré-duality connecting square at the chain level.

The crux is the **excision computation**: a cover-partitioned cycle `z` projects under `homProj A` to
the `(X, A)`-class of `chainIncl B zB`, which is exactly the excision image of the `(B, A∩B)`-class of
`zB` (`relCycleToHom`-of-a-`relCycleLift`). So `excisionEquiv.symm (homProj A [z])` is that
`(B, A∩B)`-class, and the pair-LES `connecting` then computes its boundary extraction.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularPairLES SKEFTHawking.SingularExcisionIso
open SKEFTHawking.SingularMayerVietorisLES

namespace SKEFTHawking.SingularMvDeltaPartition

variable {X : TopCat}

/-- For a cover-partitioned cycle `z = chainIncl A zA + chainIncl B zB` of `X`, the `B`-part `zB` is a
relative `(n+1)`-cycle lift of the source pair `(B, A∩B)` (i.e. `∂zB` is supported in `restr A B`):
since `z` is a cycle, `chainIncl B ∂zB = chainIncl A ∂zA` lands in `A`, and the reflection lemma pulls
this back to `restr A B`. -/
theorem zB_mem_relCycleLift (A B : Set X) (n : ℕ)
    (zA : SingularChain (sub A) (n + 1)) (zB : SingularChain (sub B) (n + 1))
    (hz_cyc : chainIncl A (n + 1) zA + chainIncl B (n + 1) zB ∈ cycles X (n + 1)) :
    zB ∈ relCycleLift (restr A B) n := by
  -- `∂(chainIncl A zA + chainIncl B zB) = 0`, so over `ℤ/2`,
  -- `chainIncl B (∂zB) = ∂(chainIncl B zB) = ∂(chainIncl A zA) = chainIncl A (∂zA)`.
  have hz0 : chainBoundary X n (chainIncl A (n + 1) zA + chainIncl B (n + 1) zB) = 0 :=
    LinearMap.mem_ker.mp hz_cyc
  rw [map_add] at hz0
  have hBeqA : chainBoundary X n (chainIncl B (n + 1) zB)
      = chainBoundary X n (chainIncl A (n + 1) zA) := by
    have h := hz0; rw [add_comm] at h
    exact eq_of_sub_eq_zero (by
      rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_right (ZModModule.add_self _)]; exact h)
  -- `∂(chainIncl B zB) = chainIncl B (∂zB)` lands in `C(A)` (= `∂(chainIncl A zA)`) and in `C(B)`,
  -- hence in `C(A∩B)`; reflect through the seam `chainIncl_mem_inter_iff` to land in `C(restr A B)`.
  show chainBoundary (sub B) n zB ∈ subspaceChains (restr A B) n
  rw [← chainIncl_mem_inter_iff, chainIncl_chainBoundary, ← SingularExcision.subspaceChains_inf]
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [hBeqA, ← chainIncl_chainBoundary]; exact ⟨chainBoundary (sub A) n zA, rfl⟩
  · rw [← chainIncl_chainBoundary]; exact ⟨chainBoundary (sub B) n zB, rfl⟩

/-- **The excision computation**: the `homProj A`-projection of a cover-partitioned cycle is the
excision image of the `(B, A∩B)`-class of its `B`-part. -/
theorem homProj_cover_partition (A B : Set X) (n : ℕ)
    (zA : SingularChain (sub A) (n + 1)) (zB : SingularChain (sub B) (n + 1))
    (hz_cyc : chainIncl A (n + 1) zA + chainIncl B (n + 1) zB ∈ cycles X (n + 1)) :
    homProj A (n + 1) (Homology.mk X (n + 1) ⟨_, hz_cyc⟩)
      = excisionMap A B (n + 1)
          (relCycleToHom (restr A B) n ⟨zB, zB_mem_relCycleLift A B n zA zB hz_cyc⟩) := by
  rw [homProj_mk, relCycleToHom_apply, excisionMap_mk]
  refine congrArg (RelativeHomology.mk A (n + 1)) (Subtype.ext ?_)
  show RelativeChain.mk A (n + 1) (chainIncl A (n + 1) zA + chainIncl B (n + 1) zB)
      = relChainIncl A B (n + 1) (RelativeChain.mk (restr A B) (n + 1) zB)
  rw [relChainIncl_mk, RelativeChain.mk, RelativeChain.mk]
  refine (Submodule.Quotient.eq _).2 ?_
  have hsub : (chainIncl A (n + 1) zA + chainIncl B (n + 1) zB) - chainIncl B (n + 1) zB
      = chainIncl A (n + 1) zA := by abel
  rw [hsub]
  exact ⟨zA, rfl⟩

/-- **The absolute MV connecting map's cover-partition chain action** (pre-seam form): on the class of
a cover-partitioned cycle `z = chainIncl A zA + chainIncl B zB`, `mvConnecting` is the class of `∂zB`
realized in the `sub (restr A B)` representation. -/
theorem mvConnecting_cover_partition (A B : Set X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set X)), interior U) = Set.univ)
    (zA : SingularChain (sub A) (n + 1)) (zB : SingularChain (sub B) (n + 1))
    (hz_cyc : chainIncl A (n + 1) zA + chainIncl B (n + 1) zB ∈ cycles X (n + 1)) :
    mvConnecting A B n hcov (Homology.mk X (n + 1) ⟨_, hz_cyc⟩)
      = Homology.mk (sub (restr A B)) n
          ⟨boundaryExtract (restr A B) n ⟨zB, zB_mem_relCycleLift A B n zA zB hz_cyc⟩,
            boundaryExtract_mem_cycles (restr A B) n _⟩ := by
  rw [mvConnecting, LinearMap.comp_apply, LinearMap.comp_apply, homProj_cover_partition,
    show excisionMap A B (n + 1)
          (relCycleToHom (restr A B) n ⟨zB, zB_mem_relCycleLift A B n zA zB hz_cyc⟩)
        = excisionEquiv A B n hcov
            (relCycleToHom (restr A B) n ⟨zB, zB_mem_relCycleLift A B n zA zB hz_cyc⟩) from rfl,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, connecting_relCycleToHom,
    connectingLift_apply]

/-- **The absolute MV connecting map's cover-partition chain action** (`mvDelta` form): on the class of
a cover-partitioned cycle `z = chainIncl A zA + chainIncl B zB`, the Mayer–Vietoris connecting map is
`seamHomologyEquiv` of the class of `∂zB` (realized in `sub (restr A B)`). -/
theorem mvDelta_cover_partition (A B : Set X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set X)), interior U) = Set.univ)
    (zA : SingularChain (sub A) (n + 1)) (zB : SingularChain (sub B) (n + 1))
    (hz_cyc : chainIncl A (n + 1) zA + chainIncl B (n + 1) zB ∈ cycles X (n + 1)) :
    mvDelta A B n hcov (Homology.mk X (n + 1) ⟨_, hz_cyc⟩)
      = seamHomologyEquiv A B n
          (Homology.mk (sub (restr A B)) n
            ⟨boundaryExtract (restr A B) n ⟨zB, zB_mem_relCycleLift A B n zA zB hz_cyc⟩,
              boundaryExtract_mem_cycles (restr A B) n _⟩) := by
  rw [mvDelta, LinearMap.comp_apply, LinearEquiv.coe_coe, mvConnecting_cover_partition]

end SKEFTHawking.SingularMvDeltaPartition
