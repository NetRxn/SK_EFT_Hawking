import Mathlib
import SKEFTHawking.SingularRelativeCohomologyRestrict

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD5-cohcolim) — the compactly-supported-cohomology directed system

The compactly-supported cohomology `Hᵏ_c(M) := colim_{K compact} Hᵏ(M, M∖K)` is the **filtered colimit**
over the directed poset of compact subsets `K` (ordered by `⊆`, `TopologicalSpace.Compacts`), with the
transition maps the relative-cohomology restrictions `relCohomRestrict` over the *complements*
(`K ⊆ K' ⟹ K'ᶜ ⊆ Kᶜ ⟹ Hᵏ(M|K) → Hᵏ(M|K')`).

This module establishes the **directed system** `(cohomG, cohomF)` and its `DirectedSystem` instance (the
functoriality, from `relCohomRestrict_id` / `relCohomRestrict_trans`), so that `Module.DirectLimit cohomG
cohomF` is the compactly-supported cohomology. It is the **top row** of the Poincaré-duality ladder; the
duality `D_K : Hᵏ(M|K) → H_{n-k}(sub K)` (`SingularLocalDualityK.relativeDualityK`) assembles into
`D : Hᵏ_c(M) → H_{n-k}(M)` (Hatcher 3.36; the corrected open-cover route, 2026-06-19 framework note).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularRelativeCohomologyRestrict

namespace SKEFTHawking.SingularCohomologyColimit

variable {M : TopCat}

noncomputable instance : DecidableEq (TopologicalSpace.Compacts ↑M) := Classical.decEq _

/-- The object of the compactly-supported-cohomology directed system: `Hᵏ(M | K) = Hᵏ(M, M∖K)` (the
relative cohomology over the open complement `Kᶜ`), indexed by the compact `K`. -/
def cohomG (k : ℕ) (K : TopologicalSpace.Compacts ↑M) : Type :=
  RelativeCohomology ((↑K : Set ↑M)ᶜ) k

noncomputable instance (k : ℕ) (K : TopologicalSpace.Compacts ↑M) : AddCommGroup (cohomG k K) :=
  inferInstanceAs (AddCommGroup (RelativeCohomology _ k))

noncomputable instance (k : ℕ) (K : TopologicalSpace.Compacts ↑M) : Module (ZMod 2) (cohomG k K) :=
  inferInstanceAs (Module (ZMod 2) (RelativeCohomology _ k))

/-- The transition map of the directed system: for `K ⊆ K'`, `K'ᶜ ⊆ Kᶜ`, so the relative-cohomology
restriction `relCohomRestrict` runs `Hᵏ(M|K) → Hᵏ(M|K')`. -/
noncomputable def cohomF (k : ℕ) (K K' : TopologicalSpace.Compacts ↑M) (h : K ≤ K') :
    cohomG k K →ₗ[ZMod 2] cohomG k K' :=
  relCohomRestrict (Set.compl_subset_compl.mpr h) k

/-- **The directed-system functoriality** (`map_self` from `relCohomRestrict_id`, `map_map` from
`relCohomRestrict_trans`): makes `(cohomG, cohomF)` a `DirectedSystem`, so `Module.DirectLimit cohomG
(cohomF k)` is the compactly-supported cohomology `Hᵏ_c(M)`. -/
instance directedSystem (k : ℕ) :
    DirectedSystem (cohomG (M := M) k) (fun i j h => ⇑(cohomF k i j h)) where
  map_self := fun _i x => relCohomRestrict_id k x
  map_map := fun {_i _j _l} _hij _hjl x => relCohomRestrict_trans _ _ k x

/-- The compactly-supported cohomology `Hᵏ_c(M) := colim_{K compact} Hᵏ(M | K)` — the filtered colimit
of the directed system `(cohomG, cohomF)` over the compacts. -/
noncomputable def CompactlySupportedCohomology (k : ℕ) : Type :=
  Module.DirectLimit (cohomG (M := M) k) (cohomF k)

end SKEFTHawking.SingularCohomologyColimit
