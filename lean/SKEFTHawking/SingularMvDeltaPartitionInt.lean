/-
# Phase 5q.H (E1 CSC-PD tower) — the absolute integral MV connecting map's chain action (cover-partition)

Integral (`ZMod 2 → ℤ`) mirror of `SingularMvDeltaPartition`. For a cover-partitioned cycle
`z = chainIncl A zA + chainIncl B zB` of `X`, the integral MV connecting map `mvDeltaInt A B n hcov [z]`
is `seamHomologyEquivInt` of the class of `∂zB` realized in the `sub (restr A B)` representation
(`boundaryExtract`). This is the explicit chain form needed to match the two legs of the integral
Poincaré-duality connecting square (`hcore`) at the chain level.

The ONE divergence from the mod-2 mirror: `zB_mem_relCycleLift` — over `ℤ/2` the mod-2 uses `x + x = 0`
to get `∂(chainIncl B zB) = ∂(chainIncl A zA)`; over ℤ this is the honest `∂(chainIncl B zB) =
-∂(chainIncl A zA)` (the sign lands in a submodule, closed under negation, so the membership survives).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularMayerVietorisLESInt
import SKEFTHawking.SingularExcisionBotInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularExcisionIsoInt
  (excisionMapInt excisionMapInt_mk excisionEquivInt subspaceChainsInt_inf chainIncl_mem_inter_iffInt
    relChainInclInt relChainInclInt_mk)
open SKEFTHawking.SingularMayerVietorisLESInt (mvConnectingInt mvDeltaInt seamHomologyEquivInt)

namespace SKEFTHawking.SingularMvDeltaPartitionInt

variable {X : TopCat}

/-- For a cover-partitioned cycle `z = chainIncl A zA + chainIncl B zB`, the `B`-part `zB` is a relative
`(n+1)`-cycle lift of the source pair `(B, A∩B)`: since `z` is a cycle, `chainIncl B (∂zB) = -chainIncl A
(∂zA)` lands in `C(A)` (submodule, closed under negation) and in `C(B)`, hence in `C(A∩B)`, reflected to
`restr A B`. (Integral: the mod-2 `x+x=0` becomes the honest `-∂`.) -/
theorem zB_mem_relCycleLift (A B : Set ↑X) (n : ℕ)
    (zA : SingularChainInt (sub A) (n + 1)) (zB : SingularChainInt (sub B) (n + 1))
    (hz_cyc : chainIncl A (n + 1) zA + chainIncl B (n + 1) zB ∈ cycles X (n + 1)) :
    zB ∈ relCycleLift (restr A B) n := by
  have hz0 : chainBoundary X n (chainIncl A (n + 1) zA + chainIncl B (n + 1) zB) = 0 :=
    LinearMap.mem_ker.mp hz_cyc
  rw [map_add] at hz0
  have hBeqA : chainBoundary X n (chainIncl B (n + 1) zB)
      = - chainBoundary X n (chainIncl A (n + 1) zA) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hz0
  show chainBoundary (sub B) n zB ∈ subspaceChainsInt (restr A B) n
  rw [← chainIncl_mem_inter_iffInt, chainIncl_chainBoundary, ← subspaceChainsInt_inf]
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [hBeqA, ← chainIncl_chainBoundary]
    exact Submodule.neg_mem _ ⟨chainBoundary (sub A) n zA, rfl⟩
  · rw [← chainIncl_chainBoundary]; exact ⟨chainBoundary (sub B) n zB, rfl⟩

/-- **The excision computation** (integral): the `homProjInt A`-projection of a cover-partitioned cycle is
the excision image of the `(B, A∩B)`-class of its `B`-part. -/
theorem homProj_cover_partition (A B : Set ↑X) (n : ℕ)
    (zA : SingularChainInt (sub A) (n + 1)) (zB : SingularChainInt (sub B) (n + 1))
    (hz_cyc : chainIncl A (n + 1) zA + chainIncl B (n + 1) zB ∈ cycles X (n + 1)) :
    homProjInt A (n + 1) (Homology.mk X (n + 1) ⟨_, hz_cyc⟩)
      = excisionMapInt A B (n + 1)
          (relCycleToHom (restr A B) n ⟨zB, zB_mem_relCycleLift A B n zA zB hz_cyc⟩) := by
  rw [homProjInt_mk, relCycleToHom_apply, excisionMapInt_mk]
  refine congrArg (RelHomologyInt.mk A (n + 1)) (Subtype.ext ?_)
  show RelativeChainInt.mk A (n + 1) (chainIncl A (n + 1) zA + chainIncl B (n + 1) zB)
      = relChainInclInt A B (n + 1) (RelativeChainInt.mk (restr A B) (n + 1) zB)
  rw [relChainInclInt_mk, RelativeChainInt.mk, RelativeChainInt.mk]
  refine (Submodule.Quotient.eq _).2 ?_
  have hsub : (chainIncl A (n + 1) zA + chainIncl B (n + 1) zB) - chainIncl B (n + 1) zB
      = chainIncl A (n + 1) zA := by abel
  rw [hsub]
  exact ⟨zA, rfl⟩

/-- **The absolute integral MV connecting map's cover-partition chain action** (pre-seam form): on the
class of a cover-partitioned cycle, `mvConnectingInt` is the class of `∂zB` realized in `sub (restr A B)`. -/
theorem mvConnecting_cover_partition (A B : Set ↑X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set ↑X)), interior U) = Set.univ)
    (zA : SingularChainInt (sub A) (n + 1)) (zB : SingularChainInt (sub B) (n + 1))
    (hz_cyc : chainIncl A (n + 1) zA + chainIncl B (n + 1) zB ∈ cycles X (n + 1)) :
    mvConnectingInt A B n hcov (Homology.mk X (n + 1) ⟨_, hz_cyc⟩)
      = Homology.mk (sub (restr A B)) n
          ⟨boundaryExtract (restr A B) n ⟨zB, zB_mem_relCycleLift A B n zA zB hz_cyc⟩,
            boundaryExtract_mem_cyclesInt (restr A B) n _⟩ := by
  rw [mvConnectingInt, LinearMap.comp_apply, LinearMap.comp_apply, homProj_cover_partition,
    show excisionMapInt A B (n + 1)
          (relCycleToHom (restr A B) n ⟨zB, zB_mem_relCycleLift A B n zA zB hz_cyc⟩)
        = excisionEquivInt A B n hcov
            (relCycleToHom (restr A B) n ⟨zB, zB_mem_relCycleLift A B n zA zB hz_cyc⟩) from rfl,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, connectingInt_relCycleToHom,
    connectingLift_apply]

/-- **The absolute integral MV connecting map's cover-partition chain action** (`mvDeltaInt` form): on the
class of a cover-partitioned cycle, `mvDeltaInt` is `seamHomologyEquivInt` of the class of `∂zB`. -/
theorem mvDelta_cover_partition (A B : Set ↑X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set ↑X)), interior U) = Set.univ)
    (zA : SingularChainInt (sub A) (n + 1)) (zB : SingularChainInt (sub B) (n + 1))
    (hz_cyc : chainIncl A (n + 1) zA + chainIncl B (n + 1) zB ∈ cycles X (n + 1)) :
    mvDeltaInt A B n hcov (Homology.mk X (n + 1) ⟨_, hz_cyc⟩)
      = seamHomologyEquivInt A B n
          (Homology.mk (sub (restr A B)) n
            ⟨boundaryExtract (restr A B) n ⟨zB, zB_mem_relCycleLift A B n zA zB hz_cyc⟩,
              boundaryExtract_mem_cyclesInt (restr A B) n _⟩) := by
  rw [mvDeltaInt, LinearMap.comp_apply, LinearEquiv.coe_coe, mvConnecting_cover_partition]

end SKEFTHawking.SingularMvDeltaPartitionInt
