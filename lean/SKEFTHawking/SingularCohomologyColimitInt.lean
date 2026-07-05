/-
# Phase 5q.H (E1 integral topology) — the integral compactly-supported-cohomology directed system

Integral (`ZMod 2 → ℤ`) mirror of `SingularCohomologyColimit`. The compactly-supported cohomology
`Hᵏ_c(M; ℤ) := colim_{K compact} Hᵏ(M, M∖K; ℤ)` is the **filtered colimit** over the directed poset
of compact subsets `K` (ordered by `⊆`, `TopologicalSpace.Compacts`), with the transition maps the
integral relative-cohomology restrictions `relCohomRestrictInt` over the *complements*
(`K ⊆ K' ⟹ K'ᶜ ⊆ Kᶜ ⟹ Hᵏ(M|K;ℤ) → Hᵏ(M|K';ℤ)`).

This module establishes the **directed system** `(cohomGInt, cohomFInt)` and its `DirectedSystem`
instance (the functoriality, from `relCohomRestrictInt_id` / `relCohomRestrictInt_trans`), so that
`Module.DirectLimit cohomGInt cohomFInt` is the integral compactly-supported cohomology. It is the
**top row** of the integral Poincaré-duality ladder: the integral local duality `D_K : Hᵏ(M|K;ℤ) →
H_{n-k}(sub K;ℤ)` assembles into `D : Hᵏ_c(M;ℤ) → H_{n-k}(M;ℤ)` (Hatcher 3.36).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularRelativeCohomologyRestrictInt

open SKEFTHawking.SingularEuclideanCapIsoInt
  SKEFTHawking.SingularRelativeCohomologyRestrictInt

namespace SKEFTHawking.SingularCohomologyColimitInt

variable {M : TopCat}

noncomputable instance : DecidableEq (TopologicalSpace.Compacts ↑M) := Classical.decEq _

/-- The object of the integral compactly-supported-cohomology directed system: `Hᵏ(M | K; ℤ) = Hᵏ(M,
M∖K; ℤ)` (the integral relative cohomology over the open complement `Kᶜ`), indexed by the compact
`K`. -/
def cohomGInt (k : ℕ) (K : TopologicalSpace.Compacts ↑M) : Type :=
  RelativeCohomologyInt ((↑K : Set ↑M)ᶜ) k

noncomputable instance (k : ℕ) (K : TopologicalSpace.Compacts ↑M) : AddCommGroup (cohomGInt k K) :=
  inferInstanceAs (AddCommGroup (RelativeCohomologyInt _ k))

noncomputable instance (k : ℕ) (K : TopologicalSpace.Compacts ↑M) : Module ℤ (cohomGInt k K) :=
  inferInstanceAs (Module ℤ (RelativeCohomologyInt _ k))

/-- The transition map of the integral directed system: for `K ⊆ K'`, `K'ᶜ ⊆ Kᶜ`, so the integral
relative-cohomology restriction `relCohomRestrictInt` runs `Hᵏ(M|K;ℤ) → Hᵏ(M|K';ℤ)`. -/
noncomputable def cohomFInt (k : ℕ) (K K' : TopologicalSpace.Compacts ↑M) (h : K ≤ K') :
    cohomGInt k K →ₗ[ℤ] cohomGInt k K' :=
  relCohomRestrictInt (Set.compl_subset_compl.mpr h) k

/-- **The directed-system functoriality** (`map_self` from `relCohomRestrictInt_id`, `map_map` from
`relCohomRestrictInt_trans`): makes `(cohomGInt, cohomFInt)` a `DirectedSystem`, so
`Module.DirectLimit cohomGInt (cohomFInt k)` is the integral compactly-supported cohomology
`Hᵏ_c(M;ℤ)`. -/
instance directedSystemInt (k : ℕ) :
    DirectedSystem (cohomGInt (M := M) k) (fun i j h => ⇑(cohomFInt k i j h)) where
  map_self := fun _i x => relCohomRestrictInt_id k x
  map_map := fun {_i _j _l} _hij _hjl x => relCohomRestrictInt_trans _ _ k x

/-- The integral compactly-supported cohomology `Hᵏ_c(M;ℤ) := colim_{K compact} Hᵏ(M | K; ℤ)` — the
filtered colimit of the directed system `(cohomGInt, cohomFInt)` over the compacts. -/
noncomputable def CompactlySupportedCohomologyInt (k : ℕ) : Type :=
  Module.DirectLimit (cohomGInt (M := M) k) (cohomFInt k)

noncomputable instance (k : ℕ) : AddCommGroup (CompactlySupportedCohomologyInt (M := M) k) :=
  inferInstanceAs (AddCommGroup (Module.DirectLimit _ _))

noncomputable instance (k : ℕ) : Module ℤ (CompactlySupportedCohomologyInt (M := M) k) :=
  inferInstanceAs (Module ℤ (Module.DirectLimit _ _))

end SKEFTHawking.SingularCohomologyColimitInt
