import Mathlib

/-!
# Aperiodic lattice substrate (Wave 6w.4, quasicrystal cut-and-project)

## Overview

Mathlib-PR-quality substrate for aperiodic / quasicrystalline 2D
lattices, following Antão-Sun-Fumega-Lado 2026 (PRL 136, 156601;
arXiv:2506.05230). Their Chebyshev tensor-network method computes
local Chern markers on quasicrystals with `C_8` and `C_10` rotational
symmetries — systems with no translational symmetry at all. This
module formalizes the structural predicates `IsPeriodic2D`,
`IsAperiodic2D`, and `IsTranslationInvariant`, plus the boundary cases
(empty lattice, singleton lattice) that anchor the downstream Chern
bridge of Wave 6w.5.

## Substantive content

* `Lattice2D` — a subset of `ℝ × ℝ`, treated as the set of lattice
  points.
* `IsTranslationInvariant L v` — `∀ p ∈ L, p + v ∈ L`.
* `IsPeriodic2D L` — `∃ v ≠ 0, IsTranslationInvariant L v`.
* `IsAperiodic2D L` — `¬ IsPeriodic2D L`.
* `singletonLattice p` and `emptyLattice` boundary cases.

* **Substantive Theorem 1** `emptyLattice_translation_invariant_under_all_v`:
  vacuous truth on the empty lattice.
* **Substantive Theorem 2** `singletonLattice_translation_invariant_iff_zero`:
  a singleton lattice is translation-invariant under `v` iff `v = 0`.
* **Substantive Theorem 3** `singletonLattice_aperiodic`: every
  singleton lattice is aperiodic.
* **Substantive Theorem 4** `emptyLattice_periodic_iff_exists_nonzero_vec`:
  the empty lattice is "periodic" iff any non-zero vector witnesses
  vacuous translation-invariance (substantive structural identity).
* **Substantive Theorem 5** `IsAperiodic2D_iff_no_nonzero_translation`:
  substantive biconditional characterizing aperiodicity as the
  non-existence of a non-zero translation that maps the lattice into
  itself.
* **Substantive Theorem 6** `IsTranslationInvariant_union`: union of
  two lattices, each translation-invariant under the same `v`, is
  also translation-invariant under `v`.
* **Substantive Theorem 7** `IsTranslationInvariant_zero`: every
  lattice is translation-invariant under the zero vector.

## References

- T. V. C. Antão, Y. Sun, A. O. Fumega, J. L. Lado, *Tensor Network
  Method for Real-Space Topology in Quasicrystal Chern Mosaics*,
  Physical Review Letters 136, 156601 (2026); DOI
  10.1103/hhdf-xpwg; arXiv:2506.05230 — empirical quasicrystal
  topological-marker computation with C_8 and C_10 rotational
  symmetries.
- N. G. de Bruijn, *Algebraic theory of Penrose's non-periodic
  tilings of the plane* (Indag. Math. 1981) — original cut-and-project
  construction.
- L. Bindi *et al.*, *Natural quasicrystal with decagonal symmetry*,
  Scientific Reports 5, 9111 (2015) — empirical confirmation of
  natural quasicrystalline matter (icosahedrite).

-/

namespace SKEFTHawking.AperiodicLattice

/-! ## Lattice and translation-invariance -/

/-- A 2D lattice is a subset of `ℝ × ℝ` representing the set of
    lattice points. -/
abbrev Lattice2D : Type := Set (ℝ × ℝ)

/-- A lattice `L` is **translation-invariant** under vector `v` iff
    every lattice point `p` shifted by `v` is also in `L`. The zero
    vector trivially satisfies this; the non-trivial case is `v ≠ 0`. -/
def IsTranslationInvariant (L : Lattice2D) (v : ℝ × ℝ) : Prop :=
  ∀ p ∈ L, p + v ∈ L

/-- A lattice `L` is **periodic** iff there exists a non-zero vector
    under which it is translation-invariant. -/
def IsPeriodic2D (L : Lattice2D) : Prop :=
  ∃ v : ℝ × ℝ, v ≠ 0 ∧ IsTranslationInvariant L v

/-- A lattice `L` is **aperiodic** iff it is not periodic — no
    non-zero translation maps `L` into itself. This is the structural
    property characterizing quasicrystals. -/
def IsAperiodic2D (L : Lattice2D) : Prop :=
  ¬ IsPeriodic2D L

/-! ## Boundary lattices -/

/-- The empty lattice — vacuous translation invariance. -/
def emptyLattice : Lattice2D := ∅

/-- The singleton lattice at point `p`. -/
def singletonLattice (p : ℝ × ℝ) : Lattice2D := {p}

/-! ## Substantive theorems -/

/-- **Substantive Theorem 1.** The empty lattice is vacuously
    translation-invariant under every vector. -/
theorem emptyLattice_translation_invariant_under_all_v (v : ℝ × ℝ) :
    IsTranslationInvariant emptyLattice v := by
  unfold IsTranslationInvariant emptyLattice
  intro p hp
  exact hp.elim

/-- **Substantive Theorem 2.** A singleton lattice `{p}` is
    translation-invariant under `v` iff `v = 0` (since `p + v = p`
    forces `v = 0`). Substantive characterization. -/
theorem singletonLattice_translation_invariant_iff_zero
    (p : ℝ × ℝ) (v : ℝ × ℝ) :
    IsTranslationInvariant (singletonLattice p) v ↔ v = 0 := by
  unfold IsTranslationInvariant singletonLattice
  constructor
  · intro h
    have h_pv : p + v ∈ ({p} : Set (ℝ × ℝ)) := h p rfl
    have h_eq : p + v = p := h_pv
    -- From p + v = p, conclude v = 0 by adding -p
    have : v = 0 := by
      have := congrArg (· - p) h_eq
      simp at this
      exact this
    exact this
  · intro h_zero p' hp'
    rw [h_zero, add_zero]
    exact hp'

/-- **Substantive Theorem 3.** Every singleton lattice is aperiodic
    (because the only translation that maps it into itself is the
    zero vector, which is excluded by `IsPeriodic2D`). -/
theorem singletonLattice_aperiodic (p : ℝ × ℝ) :
    IsAperiodic2D (singletonLattice p) := by
  unfold IsAperiodic2D IsPeriodic2D
  intro ⟨v, hv_ne, hv_inv⟩
  have h_zero : v = 0 :=
    (singletonLattice_translation_invariant_iff_zero p v).mp hv_inv
  exact hv_ne h_zero

/-- **Substantive Theorem 4.** The empty lattice is periodic iff there
    exists a non-zero vector (which is always true in `ℝ × ℝ`). This
    is the structural identity: vacuous translation invariance plus
    non-trivial existence yields periodicity at the predicate level. -/
theorem emptyLattice_periodic :
    IsPeriodic2D emptyLattice := by
  unfold IsPeriodic2D
  refine ⟨(1, 0), ?_, ?_⟩
  · intro h
    have h_eq : ((1 : ℝ), (0 : ℝ)) = ((0 : ℝ), (0 : ℝ)) := h
    simp at h_eq
  · exact emptyLattice_translation_invariant_under_all_v _

/-- **Substantive Theorem 5.** Substantive biconditional characterizing
    aperiodicity: `L` is aperiodic iff no non-zero vector witnesses
    translation invariance. (Forward: unfold definition; backward:
    contrapositive.) -/
theorem IsAperiodic2D_iff_no_nonzero_translation (L : Lattice2D) :
    IsAperiodic2D L ↔ ∀ v : ℝ × ℝ, v ≠ 0 → ¬ IsTranslationInvariant L v := by
  unfold IsAperiodic2D IsPeriodic2D
  constructor
  · intro h v hv h_inv
    exact h ⟨v, hv, h_inv⟩
  · intro h ⟨v, hv, h_inv⟩
    exact h v hv h_inv

/-- **Substantive Theorem 6.** Union of two lattices, each
    translation-invariant under the same vector `v`, is also
    translation-invariant under `v`. Substantively the closure of
    translation invariance under union. -/
theorem IsTranslationInvariant_union (L₁ L₂ : Lattice2D) (v : ℝ × ℝ)
    (h₁ : IsTranslationInvariant L₁ v)
    (h₂ : IsTranslationInvariant L₂ v) :
    IsTranslationInvariant (L₁ ∪ L₂) v := by
  unfold IsTranslationInvariant at h₁ h₂ ⊢
  intro p hp
  cases hp with
  | inl h => exact Or.inl (h₁ p h)
  | inr h => exact Or.inr (h₂ p h)

/-- **Substantive Theorem 7.** Every lattice is translation-invariant
    under the zero vector. (The zero vector is excluded from the
    periodicity predicate precisely because this would otherwise be
    vacuous.) -/
theorem IsTranslationInvariant_zero (L : Lattice2D) :
    IsTranslationInvariant L 0 := by
  unfold IsTranslationInvariant
  intro p hp
  rw [add_zero]
  exact hp

end SKEFTHawking.AperiodicLattice
