import Mathlib
import SKEFTHawking.SingularPrism
import SKEFTHawking.SingularFunctoriality

/-!
# Homotopy invariance, functor level

The prism's endpoint chain map `endMap H r` is exactly the pushforward `mapChain` of the time-`r`
slice `H(·, r) : X → Y` (`endMap_eq_mapChain`). Combined with `endMap_add_mem_boundaries`, this gives
homotopy invariance of the homology functor: homotopic maps induce equal maps on `Hₙ(·; ℤ/2)`.
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularPrism
open SKEFTHawking.SingularFunctoriality

namespace SKEFTHawking.SingularHomotopyInvariance

/-- The time-`r` slice of a homotopy `H : X × I → Y` as a continuous map `X → Y`, `x ↦ H(x, r)`. -/
noncomputable def slice {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y)) (r : unitInterval) :
    C(↑X, ↑Y) :=
  H.comp ((ContinuousMap.id ↑X).prodMk (ContinuousMap.const ↑X r))

/-- The endpoint simplex is the pushforward of the slice (definitionally). -/
theorem endSimplex_eq_mapSimplex {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (r : unitInterval) (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    endSimplex H r σ = mapSimplex (slice H r) σ := rfl

/-- **The endpoint map is the pushforward of the slice**: `endMap H r = (H(·, r))_#`. This transports
the prism's chain-level homotopy invariance to the homology functor. -/
theorem endMap_eq_mapChain {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y)) (r : unitInterval) (n : ℕ)
    (c : SingularChain X n) :
    endMap H r n c = mapChain (slice H r) n c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single σ a => rw [endMap_single, mapChain_single, endSimplex_eq_mapSimplex]

/-- **Homotopy invariance, chain level** (restated for slices): for a cycle `z`, the two slices
`H(·, 1)_#` and `H(·, 0)_#` differ by a boundary. This is `endMap_add_mem_boundaries` transported
across `endMap_eq_mapChain`; it is the engine of acyclicity (a contractible space has `Hₖ = 0` for
`k ≥ 1`), proved at the submodule level to avoid the homology-quotient elaboration. -/
theorem mapChain_slice_add_mem_boundaries {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (z : SingularChain X (n + 1)) (hz : chainBoundary X n z = 0) :
    mapChain (slice H 1) (n + 1) z + mapChain (slice H 0) (n + 1) z ∈ boundaries Y (n + 1) := by
  rw [← endMap_eq_mapChain, ← endMap_eq_mapChain]
  exact endMap_add_mem_boundaries H z hz

end SKEFTHawking.SingularHomotopyInvariance
