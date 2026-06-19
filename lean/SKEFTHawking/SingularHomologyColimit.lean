import Mathlib
import SKEFTHawking.SingularSubsetHomology

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD5-homcolim) — the homology directed system of compacts

The **bottom row** of the Poincaré-duality ladder: `colim_{K compact} H_n(sub K)`, the filtered colimit
of the homology of the compact subspaces, over the directed poset `TopologicalSpace.Compacts ↑M` (⊆). The
transition maps are `homOfSubset` (the subspace-inclusion-induced maps, `SingularSubsetHomology`); the
`DirectedSystem` functoriality comes from `homOfSubset_id` / `homOfSubset_trans`.

By compact support of singular chains (`SingularCompactSupport.exists_compact_support`) this colimit is
`H_n(M)` itself (every chain lies in some compact `K`), the target of the assembled duality map
`D : Hᵏ_c(M) → H_{n-k}(M)`. Paired with the top row `SingularCohomologyColimit.CompactlySupportedCohomology`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
  SKEFTHawking.SingularSubsetHomology

namespace SKEFTHawking.SingularHomologyColimit

variable {M : TopCat}

noncomputable instance : DecidableEq (TopologicalSpace.Compacts ↑M) := Classical.decEq _

/-- The object of the homology directed system: `H_n(sub K)`, the singular homology of the compact
subspace `K`. -/
def homG (n : ℕ) (K : TopologicalSpace.Compacts ↑M) : Type :=
  Homology (sub (↑K : Set ↑M)) n

noncomputable instance (n : ℕ) (K : TopologicalSpace.Compacts ↑M) : AddCommGroup (homG n K) :=
  inferInstanceAs (AddCommGroup (Homology _ n))

noncomputable instance (n : ℕ) (K : TopologicalSpace.Compacts ↑M) : Module (ZMod 2) (homG n K) :=
  inferInstanceAs (Module (ZMod 2) (Homology _ n))

/-- The transition map: for `K ⊆ K'`, the subspace inclusion `sub K ↪ sub K'` induces
`homOfSubset : H_n(sub K) → H_n(sub K')`. -/
noncomputable def homF (n : ℕ) (K K' : TopologicalSpace.Compacts ↑M) (h : K ≤ K') :
    homG n K →ₗ[ZMod 2] homG n K' :=
  homOfSubset h n

/-- **The directed-system functoriality** (`map_self` from `homOfSubset_id`, `map_map` from
`homOfSubset_trans`): makes `(homG, homF)` a `DirectedSystem`. -/
instance directedSystem (n : ℕ) :
    DirectedSystem (homG (M := M) n) (fun i j h => ⇑(homF n i j h)) where
  map_self := fun _i x => LinearMap.congr_fun (homOfSubset_id n) x
  map_map := fun {_i _j _l} hij hjl x => (LinearMap.congr_fun (homOfSubset_trans hij hjl n) x).symm

/-- The homology colimit `colim_{K compact} H_n(sub K)` — the filtered colimit of `(homG, homF)`. By
compact support this is `H_n(M)`; the bottom row of the Poincaré-duality ladder. -/
noncomputable def HomologyColimit (n : ℕ) : Type :=
  Module.DirectLimit (homG (M := M) n) (homF n)

end SKEFTHawking.SingularHomologyColimit
