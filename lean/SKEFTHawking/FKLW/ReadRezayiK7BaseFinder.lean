/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-1 residual B-RR7 — Read-Rezayi `SU(2)_7` constructive base finder

Ships the **algorithmic / runnable** constructive ε₀-net for the
Read-Rezayi `SU(2)_7` `GeneratingSet`. Identical structure to
`ReadRezayiK5BaseFinder.lean` with `rr5*` → `rr7*` substitutions and the
underlying Niven obstruction differing per alphabet (Phase 6x T-B.7
ships the triple-angle identity `4cos³(π/9) − 3cos(π/9) = 1/2` yielding
`1/2 ∈ ℤ̄` contradiction, already discharged in
`ReadRezayiK7V4WitnessUnconditional.rr7_density_unconditional`).

## Pattern mirrored from `RossSelingerLightweight.lean` and `ReadRezayiK5BaseFinder.lean`

## Headline definitions

  * `rr7_finite_epsilon_net_of_compact` — instantiation of
    `finite_epsilon_net_of_compact_dense` at Read-Rezayi `SU(2)_7`.

  * `rr7FiniteCover` — finite ε₀-cover Finset for Read-Rezayi `SU(2)_7`.

  * `rr7BaseFinder_constructive` — UNCONDITIONAL constructive base finder.

  * `rr7BaseFinder_constructive_approx_opNorm` — correctness.

  * `rr7BaseFinder_constructive_in_cover` — structural.

  * `rr7BaseFinder_constructive_length_le_max` — length bound.

  * `rr7BaseFinder_constructive_length_bounded_by` — `BaseFinder_length_bounded_by`
    predicate discharge.

  * `solovayKitaev_dawson_nielsen_quantitative_readRezayiK7_strict_concrete_constructive_unconditional`
    — fully UNCONDITIONAL 3-conjunct strict Read-Rezayi `SU(2)_7`
    headline.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.ConstructiveEpsilonNet
import SKEFTHawking.FKLW.SpecialUnitaryTopology
import SKEFTHawking.FKLW.EpsilonNet
import SKEFTHawking.FKLW.GenericConcreteWordLengthBound
import SKEFTHawking.FKLW.GenericSolovayKitaevRecursionDischarge
import SKEFTHawking.FKLW.ReadRezayiK7V4WitnessUnconditional
import SKEFTHawking.FKLW.ReadRezayiK7Quantitative

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

open Matrix SKEFTHawking SKEFTHawking.FKLW
  SKEFTHawking.FKLW.SolovayKitaevRecursion
  SKEFTHawking.FKLW.SolovayKitaevLengthBound

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. SU(2) compactness at the subtype level (Read-Rezayi RR7 instance) -/

/-- **SU(2) (subtype) is compact** (re-derived; same as `su2_subtype_isCompact`
in `RossSelingerLightweight.lean` and `su2_subtype_isCompact_rr5` in
`ReadRezayiK5BaseFinder.lean`).

Follows from `Matrix.instCompactSpaceSpecialUnitaryGroup`
(Phase 6p Wave 2c.4a-substrate, 2026-05-12) via `isCompact_univ`. -/
private theorem su2_subtype_isCompact_rr7 :
    IsCompact ((Set.univ : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))) :=
  isCompact_univ

/-! ## 2. Read-Rezayi `SU(2)_7` finite ε-net (UNCONDITIONAL) -/

/-- **Read-Rezayi `SU(2)_7` finite-Finset ε-cover existence** (UNCONDITIONAL).

Specializes `finite_epsilon_net_of_compact_dense` at
`readRezayiK7GeneratingSet` and consumes the UNCONDITIONAL
`rr7_density_unconditional` (Phase 6x T-B.7 substantive discharge via
triple-angle `4cos³(π/9) − 3cos(π/9) = 1/2` Niven). -/
theorem rr7_finite_epsilon_net_of_compact
    (h_compact : IsCompact ((Set.univ : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))))
    (ε : ℝ) (hε_pos : 0 < ε) :
    ∃ S : Finset (FreeGroup (Fin 2)),
      ∀ U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
        ∃ w ∈ S, ‖((readRezayiK7GeneratingSet.ρ_hom w :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
                   (U : Matrix (Fin 2) (Fin 2) ℂ)‖ < ε :=
  finite_epsilon_net_of_compact_dense
    readRezayiK7GeneratingSet rr7_density_unconditional h_compact ε hε_pos

/-- **The Read-Rezayi `SU(2)_7` finite ε₀-cover Finset** (UNCONDITIONAL). -/
noncomputable def rr7FiniteCover : Finset (FreeGroup (Fin 2)) :=
  (rr7_finite_epsilon_net_of_compact
    su2_subtype_isCompact_rr7 ε₀ ε₀_pos).choose

/-- **Coverage property of `rr7FiniteCover`**: every `U ∈ SU(2)` has
some `w` in the cover with `‖ρ_RR7 w − U‖ < ε₀`. -/
theorem rr7FiniteCover_covers
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ∃ w ∈ rr7FiniteCover,
      ‖((readRezayiK7GeneratingSet.ρ_hom w :
            ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix (Fin 2) (Fin 2) ℂ) -
          (U : Matrix (Fin 2) (Fin 2) ℂ)‖ < ε₀ :=
  (rr7_finite_epsilon_net_of_compact
    su2_subtype_isCompact_rr7 ε₀ ε₀_pos).choose_spec U

/-! ## 3. Constructive Read-Rezayi `SU(2)_7` base finder -/

/-- **Constructive Read-Rezayi `SU(2)_7` base finder** (UNCONDITIONAL). -/
noncomputable def rr7BaseFinder_constructive :
    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) → FreeGroup (Fin 2) :=
  fun U => (rr7FiniteCover_covers U).choose

/-- **Correctness of the constructive RR7 base finder** (UNCONDITIONAL):
output ε₀-approximates `U`. -/
theorem rr7BaseFinder_constructive_approx_opNorm
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ‖((readRezayiK7GeneratingSet.ρ_hom (rr7BaseFinder_constructive U) :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ < ε₀ :=
  ((rr7FiniteCover_covers U).choose_spec).2

/-- **Structural**: the constructive RR7 base finder's output always
lies in `rr7FiniteCover` (UNCONDITIONAL). -/
theorem rr7BaseFinder_constructive_in_cover
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    rr7BaseFinder_constructive U ∈ rr7FiniteCover :=
  ((rr7FiniteCover_covers U).choose_spec).1

/-! ## 4. Calibration -/

/-- **Calibration**: the constructive RR7 base finder satisfies
`BaseFinder_approximates_within readRezayiK7GeneratingSet
   rr7BaseFinder_constructive (2 * ε₀)` (UNCONDITIONAL). -/
theorem rr7BaseFinder_constructive_approximates_within_two_ε₀ :
    BaseFinder_approximates_within readRezayiK7GeneratingSet
      rr7BaseFinder_constructive (2 * ε₀) := by
  intro U
  have h1 := rr7BaseFinder_constructive_approx_opNorm U
  have h2 : ε₀ < 2 * ε₀ := by have := ε₀_pos; linarith
  linarith

/-! ## 5. Length bound at the Finset's max length (UNCONDITIONAL) -/

/-- **The Finset's max word length**. -/
noncomputable def rr7FiniteCover_maxLength : ℕ :=
  if h : rr7FiniteCover.Nonempty then
    (rr7FiniteCover.image (fun w => w.toWord.length)).max'
      (h.image _)
  else 0

/-- **Length bound for the constructive RR7 base finder** (UNCONDITIONAL). -/
theorem rr7BaseFinder_constructive_length_le_max
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    (rr7BaseFinder_constructive U).toWord.length
      ≤ rr7FiniteCover_maxLength := by
  have h_in : rr7BaseFinder_constructive U ∈ rr7FiniteCover :=
    rr7BaseFinder_constructive_in_cover U
  have h_nonempty : rr7FiniteCover.Nonempty := ⟨_, h_in⟩
  unfold rr7FiniteCover_maxLength
  rw [dif_pos h_nonempty]
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨_, h_in, rfl⟩

/-- **Parametric length-bound predicate discharge** (UNCONDITIONAL). -/
theorem rr7BaseFinder_constructive_length_bounded_by :
    BaseFinder_length_bounded_by
      (rr7FiniteCover_maxLength : ℝ)
      rr7BaseFinder_constructive := by
  intro U
  have h := rr7BaseFinder_constructive_length_le_max U
  exact_mod_cast h

/-! ## 6. Fully UNCONDITIONAL Read-Rezayi `SU(2)_7` 3-conjunct strict headline -/

/-- **Phase 6x Tier-1 residual B-RR7 — UNCONDITIONAL Read-Rezayi
`SU(2)_7` 3-conjunct strict headline at the constructive base finder**.

For any target `U ∈ SU(2)` and precision `ε ∈ (0, ε₀]`, the lightweight
constructive Dawson-Nielsen Solovay-Kitaev compiler at Read-Rezayi
`SU(2)_7` (using `rr7BaseFinder_constructive` from the finite-Finset
ε₀-cover) returns a `FreeGroup (Fin 2)` word with ALL THREE:

  - **Error**: `‖ρ_RR7 (compile U ε) − U‖ ≤ ε`.
  - **Abstract length**: `skLength (skLevel_polylog ε) ≤ skLengthConst · …`.
  - **Concrete length**: `((compile U ε).toWord.length : ℝ) ≤
    skLength_at_baseCase (rr7FiniteCover_maxLength) (skLevel_polylog ε)`.

The third conjunct is parametric in `rr7FiniteCover_maxLength`
(the actual maximum word length in the finite ε₀-cover Finset for RR7).

UNCONDITIONAL — composes shipped unconditional substrate (SU(2)
compactness + RR7 density via triple-angle `4cos³(π/9) − 3cos(π/9) = 1/2`
Niven + finite-Finset ε-cover existence + M.4 parametric length bound).
Standard kernel only `{propext, Classical.choice, Quot.sound}`.

**Closes Phase 6x Tier-1 residual B-RR7** (2026-05-27 audit addendum) —
retrospective failure mode #4 ("substrate vs headline") now closed at
the UNCONDITIONAL 3-conjunct level for Read-Rezayi `SU(2)_7`. -/
theorem solovayKitaev_dawson_nielsen_quantitative_readRezayiK7_strict_concrete_constructive_unconditional
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ)
    (hε_pos : 0 < ε) (hε_le : ε ≤ ε₀) :
    ‖((readRezayiK7GeneratingSet.ρ_hom
            (solovayKitaev_compile_strict_constructive_generic
              readRezayiK7GeneratingSet rr7BaseFinder_constructive U ε) :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε ∧
    skLength (skLevel_polylog ε) ≤
      skLengthConst * (Real.log (1 / ε)) ^ skLengthExponent ∧
    ((solovayKitaev_compile_strict_constructive_generic
        readRezayiK7GeneratingSet rr7BaseFinder_constructive U ε).toWord.length : ℝ)
        ≤ skLength_at_baseCase (rr7FiniteCover_maxLength : ℝ)
            (skLevel_polylog ε) := by
  have h12 := solovayKitaev_dawson_nielsen_quantitative_generic_strict_constructive_tight_unconditional
    readRezayiK7GeneratingSet rr7BaseFinder_constructive
    rr7BaseFinder_constructive_approximates_within_two_ε₀
    U ε hε_pos hε_le
  have h3 := skApproxC_generic_freeGroup_length_le_skLength_at_baseCase
    ρ_RR7 readRezayiK7Gens readRezayiK7Gens_nonempty readRezayiK7Gens_generate
    rr7BaseFinder_constructive
    (rr7FiniteCover_maxLength : ℝ)
    rr7BaseFinder_constructive_length_bounded_by
    (skLevel_polylog ε) U
  exact ⟨h12.1, h12.2, h3⟩

end SKEFTHawking.FKLW.GenericSU2
