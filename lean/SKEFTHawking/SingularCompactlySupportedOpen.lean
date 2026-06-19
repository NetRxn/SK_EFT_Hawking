import Mathlib
import SKEFTHawking.SingularCohomologyColimit
import SKEFTHawking.SingularCompactsInOpen

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD6b) — compactly-supported cohomology of an open `Hᵏ_c(W)`

`Hᵏ_c(W) := colim_{K ⊆ W compact} Hᵏ(M | K)`, the filtered colimit of the relative cohomology over the
compacts **contained in the open `W`** (`SingularCompactsInOpen.CompactsIn W`), with the same transition
maps `relCohomRestrict` as the global `SingularCohomologyColimit.CompactlySupportedCohomology` (which is
the `W = univ` case). This is the term of the Poincaré-duality open-cover induction (Hatcher 3.36); the
duality `D_W : Hᵏ_c(W) → H_{n-k}(sub W)` is built on it, and the 5-lemma runs over the cohomology MV of
these for an open cover `{U, V}`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyRestrict
  SKEFTHawking.SingularCohomologyColimit SKEFTHawking.SingularCompactsInOpen

namespace SKEFTHawking.SingularCompactlySupportedOpen

variable {M : TopCat}

/-- The object of the `Hᵏ_c(W)` directed system: `Hᵏ(M | K)` for a compact `K ⊆ W`. -/
def cohomGW (W : Set ↑M) (k : ℕ) (K : CompactsIn W) : Type :=
  cohomG k K.1

noncomputable instance (W : Set ↑M) (k : ℕ) (K : CompactsIn W) : AddCommGroup (cohomGW W k K) :=
  inferInstanceAs (AddCommGroup (cohomG k K.1))

noncomputable instance (W : Set ↑M) (k : ℕ) (K : CompactsIn W) : Module (ZMod 2) (cohomGW W k K) :=
  inferInstanceAs (Module (ZMod 2) (cohomG k K.1))

/-- The transition map of the `Hᵏ_c(W)` system: `relCohomRestrict` over the complements, restricted to
the compacts contained in `W`. -/
noncomputable def cohomFW (W : Set ↑M) (k : ℕ) (K K' : CompactsIn W) (h : K ≤ K') :
    cohomGW W k K →ₗ[ZMod 2] cohomGW W k K' :=
  cohomF k K.1 K'.1 (Subtype.coe_le_coe.mpr h)

instance directedSystemW (W : Set ↑M) (k : ℕ) :
    DirectedSystem (cohomGW W k) (fun i j h => ⇑(cohomFW W k i j h)) where
  map_self := fun _i x => relCohomRestrict_id k x
  map_map := fun {_i _j _l} _hij _hjl x => relCohomRestrict_trans _ _ k x

/-- **The compactly-supported cohomology of the open `W`** `Hᵏ_c(W) := colim_{K ⊆ W compact} Hᵏ(M | K)`. -/
noncomputable def CompactlySupportedCohomologyOpen (W : Set ↑M) (k : ℕ) : Type :=
  Module.DirectLimit (cohomGW W k) (cohomFW W k)

noncomputable instance (W : Set ↑M) (k : ℕ) :
    AddCommGroup (CompactlySupportedCohomologyOpen W k) :=
  inferInstanceAs (AddCommGroup (Module.DirectLimit _ _))

noncomputable instance (W : Set ↑M) (k : ℕ) :
    Module (ZMod 2) (CompactlySupportedCohomologyOpen W k) :=
  inferInstanceAs (Module (ZMod 2) (Module.DirectLimit _ _))

end SKEFTHawking.SingularCompactlySupportedOpen
