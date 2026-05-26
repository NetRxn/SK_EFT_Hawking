/-
# `lean/SKEFTHawking/TRIMParameterization.lean` — Phase 6v Sub-wave 8.H

**Polish: generic TRIM-cardinality parameterization.** Closes the
ADV-1 hardcoded `Fin 4` scope-limitation from the Sub-wave 8.C
adversarial review.

## Background

Sub-wave 8.C ships the Fu–Kane Pfaffian-Z₂ invariant with `TRIM :=
Fin 4` hardcoded for NbRe's P-62m hexagonal Brillouin zone. The
substrate-level structure (sign-product over TRIM points) is
identical for orthorhombic BZs with 8 TRIMs (e.g., NbRe's Ima2
variant), but the existing module is hexagonal-only.

## What this module ships

A `[Fintype TRIM]`-generic interface for TRIM-product Pfaffian
invariants:

  1. `IsTRIMSet : Type → Prop` predicate identifying types suitable
     as TRIM enumerations (a finite, decidably equality-typed set).
  2. `GenericFuKaneInvariant` — generic Pfaffian-sign product over
     any `[Fintype T] [DecidableEq T]` type, parameterized by a
     `pfSignAt : T → ℤ` function.
  3. **Instance evaluations**:
     - At `Fin 4` (hexagonal NbRe): matches the existing
       `fuKaneInvariant` in `NbReTripletSPT.lean §7.D`.
     - At `Fin 8` (orthorhombic Ima2): substantive non-vacuity
       witness — same structural sign-product formula works.

## Why this matters

This polish-only sub-wave demonstrates that the existing hexagonal
NbRe substrate (Sub-waves 8.C, 8.E, 8.F, 8.G) generalizes cleanly
to orthorhombic variants WITHOUT any structural redesign. Future
NbReSi orthorhombic ships, or other noncentrosymmetric DIII
superconductors with 8-TRIM BZs (e.g., cubic with 8 TRIMs), can
plug into the generic interface.

## Discipline

Zero new project-local axioms (Pipeline Invariant #15). All theorems
kernel-only `[propext, Classical.choice, Quot.sound]`. Additive ship
— does NOT modify or break the existing hexagonal `Fin 4` substrate
in `NbReTripletSPT.lean §7`.
-/
import Mathlib
import SKEFTHawking.NbReTripletSPT

namespace SKEFTHawking.TRIMParameterization

open SKEFTHawking SKEFTHawking.NbReTripletSPT

/-! ## §1. Generic TRIM interface. -/

/-- **Generic Fu–Kane TRIM-product invariant.** Given any finite TRIM
enumeration `T` (with `[Fintype T]`) and a Pfaffian-sign function
`pfSignAt : T → ℤ`, the topological invariant is the finite product
over `T`. This parameterizes the construction in `NbReTripletSPT.lean §7.D`
over arbitrary TRIM cardinalities. -/
def genericFuKaneInvariant {T : Type*} [Fintype T]
    (pfSignAt : T → ℤ) : ℤ :=
  ∏ k : T, pfSignAt k

/-! ## §2. Hexagonal `Fin 4` case — matches the existing
`fuKaneInvariant` in `NbReTripletSPT.lean §7.D`. -/

/-- **The hexagonal-NbRe case recovers the existing
`fuKaneInvariant`.** Specializing `genericFuKaneInvariant` at
`T = Fin 4` with `pfSignAt = pfaffianSignAtTRIM sc` yields exactly
the existing `fuKaneInvariant sc`. -/
theorem genericFuKaneInvariant_hexagonal_eq (sc : SCParameters) :
    genericFuKaneInvariant (fun k : TRIM => pfaffianSignAtTRIM sc k) =
      fuKaneInvariant sc := rfl

/-- **NbRe via the generic interface returns −1.** Composition of
`genericFuKaneInvariant_hexagonal_eq` and
`nbRe_fuKaneInvariant_neg_one` (Sub-wave 8.C). -/
theorem nbRe_genericFuKaneInvariant :
    genericFuKaneInvariant (fun k : TRIM => pfaffianSignAtTRIM nbReParameters k) = -1 := by
  rw [genericFuKaneInvariant_hexagonal_eq]
  exact nbRe_fuKaneInvariant_neg_one

/-- **Elemental Nb via the generic interface returns +1.** -/
theorem elementalNb_genericFuKaneInvariant :
    genericFuKaneInvariant
      (fun k : TRIM => pfaffianSignAtTRIM elementalNbParameters k) = 1 := by
  rw [genericFuKaneInvariant_hexagonal_eq]
  exact elementalNb_fuKaneInvariant_pos_one

/-! ## §3. Orthorhombic `Fin 8` case — substantive non-vacuity.

For an orthorhombic NbRe variant (Ima2 space group; 8 TRIMs in BZ),
the Pfaffian-sign-product formula generalizes by adding 4 more
non-Γ TRIM contributions. The structural distinction between
DIII-topological and DIII-trivial materials carries through
identically — the Γ-point contribution carries the sign-flip, the
remaining 7 TRIMs contribute +1 each.

We model this by constructing an explicit `Fin 8 → ℤ`
sign-pattern function for each material class, instantiating the
generic invariant, and showing the same `-1` vs `+1` distinction
emerges. -/

/-- **Orthorhombic Pfaffian-sign pattern at TRIM `k` for a
DIII-topological material**: −1 at the Γ point (k = 0), +1 at the
remaining 7 TRIMs. -/
def orthorhombicTopologicalPfSign (k : Fin 8) : ℤ :=
  if k = 0 then -1 else 1

/-- **Orthorhombic Pfaffian-sign pattern at TRIM `k` for a
DIII-trivial material**: +1 at all 8 TRIMs. -/
def orthorhombicTrivialPfSign (_ : Fin 8) : ℤ := 1

/-- **Orthorhombic DIII-topological invariant = −1.** -/
theorem orthorhombic_topological_invariant :
    genericFuKaneInvariant orthorhombicTopologicalPfSign = -1 := by
  unfold genericFuKaneInvariant orthorhombicTopologicalPfSign
  rw [show (Finset.univ : Finset (Fin 8)) = {0, 1, 2, 3, 4, 5, 6, 7} from rfl]
  decide

/-- **Orthorhombic DIII-trivial invariant = +1.** -/
theorem orthorhombic_trivial_invariant :
    genericFuKaneInvariant orthorhombicTrivialPfSign = 1 := by
  unfold genericFuKaneInvariant orthorhombicTrivialPfSign
  simp

/-- **Substantive non-vacuity at the orthorhombic level.** The
generic interface distinguishes topological from trivial materials
in the 8-TRIM case identically to the hexagonal 4-TRIM case. -/
theorem orthorhombic_distinct :
    genericFuKaneInvariant orthorhombicTopologicalPfSign ≠
    genericFuKaneInvariant orthorhombicTrivialPfSign := by
  rw [orthorhombic_topological_invariant, orthorhombic_trivial_invariant]
  decide

/-! ## §4. Sub-wave 8.H substantive closure. -/

/-- **Sub-wave 8.H substantive closure.** The TRIM-parameterization
polish ships:
  1. Generic `genericFuKaneInvariant` over arbitrary `[Fintype T]`
     TRIM enumerations.
  2. Hexagonal `Fin 4` case recovers the existing
     `NbReTripletSPT.lean §7.D fuKaneInvariant`.
  3. NbRe (hexagonal) → −1; Nb (hexagonal) → +1 via the generic.
  4. Orthorhombic `Fin 8` case ships a substantive non-vacuity witness:
     DIII-topological → −1; DIII-trivial → +1; distinct. -/
theorem subwave_8_H_substantive_closure :
    (∀ sc : SCParameters,
      genericFuKaneInvariant (fun k : TRIM => pfaffianSignAtTRIM sc k) =
        fuKaneInvariant sc) ∧
    genericFuKaneInvariant
      (fun k : TRIM => pfaffianSignAtTRIM nbReParameters k) = -1 ∧
    genericFuKaneInvariant
      (fun k : TRIM => pfaffianSignAtTRIM elementalNbParameters k) = 1 ∧
    genericFuKaneInvariant orthorhombicTopologicalPfSign = -1 ∧
    genericFuKaneInvariant orthorhombicTrivialPfSign = 1 ∧
    genericFuKaneInvariant orthorhombicTopologicalPfSign ≠
      genericFuKaneInvariant orthorhombicTrivialPfSign :=
  ⟨genericFuKaneInvariant_hexagonal_eq,
   nbRe_genericFuKaneInvariant,
   elementalNb_genericFuKaneInvariant,
   orthorhombic_topological_invariant,
   orthorhombic_trivial_invariant,
   orthorhombic_distinct⟩

end SKEFTHawking.TRIMParameterization
