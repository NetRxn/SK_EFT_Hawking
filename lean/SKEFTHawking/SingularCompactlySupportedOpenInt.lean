/-
# Phase 5q.H (E1 integral topology) — compactly-supported cohomology of an open, `Hᵏ_c(W; ℤ)`

Integral (`ZMod 2 → ℤ`) mirror of `SingularCompactlySupportedOpen`.
`Hᵏ_c(W; ℤ) := colim_{K ⊆ W compact} Hᵏ(M | K; ℤ)`, the filtered colimit of the integral relative
cohomology over the compacts **contained in the open `W`** (`SingularCompactsInOpen.CompactsIn W`), with
the same transition maps `cohomFInt` (= `relCohomRestrictInt` over the complements) as the global
`SingularCohomologyColimitInt.CompactlySupportedCohomologyInt` (the `W = univ` case). This is the term of
the integral Poincaré-duality open-cover induction (Hatcher 3.36); the open duality
`D_W : Hᵏ_c(W;ℤ) → H_{n-k}(sub W;ℤ)` is built on it, and the 5-lemma runs over the cohomology MV of these
for an open cover `{U, V}`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularCohomologyColimitInt
import SKEFTHawking.SingularCompactsInOpen

open SKEFTHawking.SingularCohomologyColimitInt SKEFTHawking.SingularCompactsInOpen
  SKEFTHawking.SingularRelativeCohomologyRestrictInt

namespace SKEFTHawking.SingularCompactlySupportedOpenInt

variable {M : TopCat}

/-- The object of the `Hᵏ_c(W;ℤ)` directed system: `Hᵏ(M | K; ℤ)` for a compact `K ⊆ W`. -/
def cohomGWInt (W : Set ↑M) (k : ℕ) (K : CompactsIn W) : Type :=
  cohomGInt k K.1

noncomputable instance (W : Set ↑M) (k : ℕ) (K : CompactsIn W) : AddCommGroup (cohomGWInt W k K) :=
  inferInstanceAs (AddCommGroup (cohomGInt k K.1))

noncomputable instance (W : Set ↑M) (k : ℕ) (K : CompactsIn W) : Module ℤ (cohomGWInt W k K) :=
  inferInstanceAs (Module ℤ (cohomGInt k K.1))

/-- The transition map of the `Hᵏ_c(W;ℤ)` system: `cohomFInt` over the complements, restricted to the
compacts contained in `W`. -/
noncomputable def cohomFWInt (W : Set ↑M) (k : ℕ) (K K' : CompactsIn W) (h : K ≤ K') :
    cohomGWInt W k K →ₗ[ℤ] cohomGWInt W k K' :=
  cohomFInt k K.1 K'.1 (Subtype.coe_le_coe.mpr h)

instance directedSystemWInt (W : Set ↑M) (k : ℕ) :
    DirectedSystem (cohomGWInt W k) (fun i j h => ⇑(cohomFWInt W k i j h)) where
  map_self := fun _i x => relCohomRestrictInt_id k x
  map_map := fun {_i _j _l} _hij _hjl x => relCohomRestrictInt_trans _ _ k x

/-- **The integral compactly-supported cohomology of the open `W`**
`Hᵏ_c(W;ℤ) := colim_{K ⊆ W compact} Hᵏ(M | K; ℤ)`. -/
noncomputable def CompactlySupportedCohomologyOpenInt (W : Set ↑M) (k : ℕ) : Type :=
  Module.DirectLimit (cohomGWInt W k) (cohomFWInt W k)

noncomputable instance (W : Set ↑M) (k : ℕ) :
    AddCommGroup (CompactlySupportedCohomologyOpenInt W k) :=
  inferInstanceAs (AddCommGroup (Module.DirectLimit _ _))

noncomputable instance (W : Set ↑M) (k : ℕ) :
    Module ℤ (CompactlySupportedCohomologyOpenInt W k) :=
  inferInstanceAs (Module ℤ (Module.DirectLimit _ _))

end SKEFTHawking.SingularCompactlySupportedOpenInt
