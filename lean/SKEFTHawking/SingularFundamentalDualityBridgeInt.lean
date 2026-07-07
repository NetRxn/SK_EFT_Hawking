/-
# Phase 5q.H (E1 CSC-PD tower) — d1 ⊤-collapse bridge foundations (integral)

The foundational bricks of the σ÷16 d1 bridge (`openDuality univ` bij → `fundamentalDualityInt` bij):
every chain is a `univ`-subspace chain, and the ambient inclusion `sub univ ↪ M` induces a homology iso.
Mirror of `SingularPDWindow.mem_subspaceChains_univ` / `homology_map_ambIncl_univ_bijective`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularExcisionIsoInt
import SKEFTHawking.SingularConvexSubAcyclicInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)

namespace SKEFTHawking.SingularFundamentalDualityBridgeInt

/-- Every integral chain is a `univ`-subspace chain. -/
theorem mem_subspaceChainsInt_univ {M : TopCat} {n : ℕ} (c : SingularChainInt M n) :
    c ∈ subspaceChainsInt (Set.univ : Set ↑M) n :=
  SKEFTHawking.SingularExcisionIsoInt.mem_subspaceChainsInt_of_support (fun _ _ => Set.subset_univ _)

/-- `Homology.mapInt` of the `univ`-subspace inclusion is bijective (it is a homeomorphism). -/
theorem homology_map_ambIncl_univ_bijectiveInt {M : TopCat} (n : ℕ) :
    Function.Bijective (Homology.mapInt
      (SKEFTHawking.SingularMayerVietorisLES.ambIncl (Set.univ : Set ↑M)) n) :=
  SKEFTHawking.SingularSphereHomologyInt.Homology.mapInt_bijective_of_comp_id_all
    (SKEFTHawking.SingularMayerVietorisLES.ambIncl (Set.univ : Set ↑M))
    (⟨fun x => ⟨x, Set.mem_univ x⟩, Continuous.subtype_mk continuous_id _⟩ :
      C(↑M, ↑(sub (Set.univ : Set ↑M))))
    (ContinuousMap.ext fun _z => Subtype.ext rfl)
    (ContinuousMap.ext fun _z => rfl) n

end SKEFTHawking.SingularFundamentalDualityBridgeInt
