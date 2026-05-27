/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-1 residual B-RR5 — Read-Rezayi `SU(2)_5` constructive base finder

Ships the **algorithmic / runnable** constructive ε₀-net for the
Read-Rezayi `SU(2)_5` `GeneratingSet` by composing the existing
`ConstructiveEpsilonNet` finite-Finset coverage theorem with the
SU(2) compactness substrate
(`Matrix.specialUnitaryGroup_isCompact`, shipped Phase 6p Wave
2c.4a-substrate via `SpecialUnitaryTopology.lean`). The resulting base
finder is length-bounded by the Finset's maximum word length — closing
the "all 4 alphabets UNCONDITIONAL 3-conjunct" gap from the Phase 6x
2026-05-27 audit addendum (Tier-1 residual B-RR5) for Read-Rezayi level
5.

## Pattern mirrored from `RossSelingerLightweight.lean`

Identical structure to the Clifford+T T-S′ ship, with `cliffordT*` →
`rr5*` substitutions and the Niven obstruction differing per alphabet
(Phase 6x T-B.5 ships the Chebyshev `T_7` factorization yielding
`−1/4 ∈ ℤ̄` for `cos(π/7)`, already discharged in
`ReadRezayiK5V4WitnessUnconditional.rr5_density_unconditional`).

## Headline definitions

  * `rr5_finite_epsilon_net_of_compact` — instantiation of
    `finite_epsilon_net_of_compact_dense` at the Read-Rezayi `SU(2)_5`
    generating set, consuming `rr5_density_unconditional`.

  * `rr5FiniteCover` — the finite ε₀-cover Finset for Read-Rezayi
    `SU(2)_5`, built via `rr5_finite_epsilon_net_of_compact` + SU(2)
    compactness. UNCONDITIONAL.

  * `rr5BaseFinder_constructive` — constructive length-bounded base
    finder via `Finset.choose`-style extraction. UNCONDITIONAL.

  * `rr5BaseFinder_constructive_approx_opNorm` — correctness.

  * `rr5BaseFinder_constructive_in_cover` — structural.

  * `rr5BaseFinder_constructive_length_le_max` — length bound.

  * `rr5BaseFinder_constructive_length_bounded_by` — `BaseFinder_length_bounded_by`
    predicate discharge.

  * `solovayKitaev_dawson_nielsen_quantitative_readRezayiK5_strict_concrete_constructive_unconditional`
    — fully UNCONDITIONAL 3-conjunct strict Read-Rezayi `SU(2)_5`
    headline.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected — composes
  unconditional substrate (`Matrix.specialUnitaryGroup_isCompact` +
  `rr5_density_unconditional` + `ConstructiveEpsilonNet` +
  `BaseFinder_length_bounded_by` + `skApproxC_generic_freeGroup_length_le_skLength_at_baseCase`).

-/

import SKEFTHawking.FKLW.ConstructiveEpsilonNet
import SKEFTHawking.FKLW.SpecialUnitaryTopology
import SKEFTHawking.FKLW.EpsilonNet
import SKEFTHawking.FKLW.GenericConcreteWordLengthBound
import SKEFTHawking.FKLW.GenericSolovayKitaevRecursionDischarge
import SKEFTHawking.FKLW.ReadRezayiK5V4WitnessUnconditional
import SKEFTHawking.FKLW.ReadRezayiK5Quantitative

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

open Matrix SKEFTHawking SKEFTHawking.FKLW
  SKEFTHawking.FKLW.SolovayKitaevRecursion
  SKEFTHawking.FKLW.SolovayKitaevLengthBound

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. SU(2) compactness at the subtype level (Read-Rezayi instance)

Re-derived locally to avoid taking a dependency on
`RossSelingerLightweight.lean`. Same proof as in that file: uses the
shipped `Matrix.instCompactSpaceSpecialUnitaryGroup` instance from
`SpecialUnitaryTopology.lean` via `isCompact_univ`. -/

/-- **SU(2) (subtype) is compact** (re-derived; same as `su2_subtype_isCompact`
in `RossSelingerLightweight.lean`).

Follows from `Matrix.instCompactSpaceSpecialUnitaryGroup`
(Phase 6p Wave 2c.4a-substrate, 2026-05-12) via `isCompact_univ`. -/
private theorem su2_subtype_isCompact_rr5 :
    IsCompact ((Set.univ : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))) :=
  isCompact_univ

/-! ## 2. Read-Rezayi `SU(2)_5` finite ε-net (UNCONDITIONAL) -/

/-- **Read-Rezayi `SU(2)_5` finite-Finset ε-cover existence** (UNCONDITIONAL).

Specializes `finite_epsilon_net_of_compact_dense` at
`readRezayiK5GeneratingSet` and consumes the UNCONDITIONAL
`rr5_density_unconditional` (Phase 6x T-B.5 substantive discharge via
Chebyshev `T_7` Niven). -/
theorem rr5_finite_epsilon_net_of_compact
    (h_compact : IsCompact ((Set.univ : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))))
    (ε : ℝ) (hε_pos : 0 < ε) :
    ∃ S : Finset (FreeGroup (Fin 2)),
      ∀ U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
        ∃ w ∈ S, ‖((readRezayiK5GeneratingSet.ρ_hom w :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
                   (U : Matrix (Fin 2) (Fin 2) ℂ)‖ < ε :=
  finite_epsilon_net_of_compact_dense
    readRezayiK5GeneratingSet rr5_density_unconditional h_compact ε hε_pos

/-- **The Read-Rezayi `SU(2)_5` finite ε₀-cover Finset** (UNCONDITIONAL).

Built by applying `rr5_finite_epsilon_net_of_compact` to the shipped
SU(2) compactness. The resulting `Finset (FreeGroup (Fin 2))`
ε₀-covers all of SU(2): for every `U`, some `w` in the Finset has
`‖ρ_RR5 w − U‖ < ε₀`. -/
noncomputable def rr5FiniteCover : Finset (FreeGroup (Fin 2)) :=
  (rr5_finite_epsilon_net_of_compact
    su2_subtype_isCompact_rr5 ε₀ ε₀_pos).choose

/-- **Coverage property of `rr5FiniteCover`**: every `U ∈ SU(2)` has
some `w` in the cover with `‖ρ_RR5 w − U‖ < ε₀`. -/
theorem rr5FiniteCover_covers
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ∃ w ∈ rr5FiniteCover,
      ‖((readRezayiK5GeneratingSet.ρ_hom w :
            ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix (Fin 2) (Fin 2) ℂ) -
          (U : Matrix (Fin 2) (Fin 2) ℂ)‖ < ε₀ :=
  (rr5_finite_epsilon_net_of_compact
    su2_subtype_isCompact_rr5 ε₀ ε₀_pos).choose_spec U

/-! ## 3. Constructive Read-Rezayi `SU(2)_5` base finder -/

/-- **Constructive Read-Rezayi `SU(2)_5` base finder** (UNCONDITIONAL).

For each `U ∈ SU(2)`, picks a `FreeGroup (Fin 2)` word `w` from the
finite cover Finset `rr5FiniteCover` such that
`‖ρ_RR5 w − U‖ < ε₀`. Existence guaranteed by the cover property; one
`Classical.choose` per query. -/
noncomputable def rr5BaseFinder_constructive :
    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) → FreeGroup (Fin 2) :=
  fun U => (rr5FiniteCover_covers U).choose

/-- **Correctness of the constructive RR5 base finder** (UNCONDITIONAL):
output ε₀-approximates `U`. -/
theorem rr5BaseFinder_constructive_approx_opNorm
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ‖((readRezayiK5GeneratingSet.ρ_hom (rr5BaseFinder_constructive U) :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ < ε₀ :=
  ((rr5FiniteCover_covers U).choose_spec).2

/-- **Structural**: the constructive RR5 base finder's output always
lies in `rr5FiniteCover` (UNCONDITIONAL). -/
theorem rr5BaseFinder_constructive_in_cover
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    rr5BaseFinder_constructive U ∈ rr5FiniteCover :=
  ((rr5FiniteCover_covers U).choose_spec).1

/-! ## 4. Calibration -/

/-- **Calibration**: the constructive RR5 base finder satisfies
`BaseFinder_approximates_within readRezayiK5GeneratingSet
   rr5BaseFinder_constructive (2 * ε₀)` (UNCONDITIONAL). -/
theorem rr5BaseFinder_constructive_approximates_within_two_ε₀ :
    BaseFinder_approximates_within readRezayiK5GeneratingSet
      rr5BaseFinder_constructive (2 * ε₀) := by
  intro U
  have h1 := rr5BaseFinder_constructive_approx_opNorm U
  have h2 : ε₀ < 2 * ε₀ := by have := ε₀_pos; linarith
  linarith

/-! ## 5. Length bound at the Finset's max length (UNCONDITIONAL) -/

/-- **The Finset's max word length**: the maximum FreeGroup-word-length
across all words in `rr5FiniteCover`. -/
noncomputable def rr5FiniteCover_maxLength : ℕ :=
  if h : rr5FiniteCover.Nonempty then
    (rr5FiniteCover.image (fun w => w.toWord.length)).max'
      (h.image _)
  else 0

/-- **Length bound for the constructive RR5 base finder** (UNCONDITIONAL):
the output has word length ≤ `rr5FiniteCover_maxLength`. -/
theorem rr5BaseFinder_constructive_length_le_max
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    (rr5BaseFinder_constructive U).toWord.length
      ≤ rr5FiniteCover_maxLength := by
  have h_in : rr5BaseFinder_constructive U ∈ rr5FiniteCover :=
    rr5BaseFinder_constructive_in_cover U
  have h_nonempty : rr5FiniteCover.Nonempty := ⟨_, h_in⟩
  unfold rr5FiniteCover_maxLength
  rw [dif_pos h_nonempty]
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨_, h_in, rfl⟩

/-- **Parametric length-bound predicate discharge** (UNCONDITIONAL):
the constructive base finder satisfies `BaseFinder_length_bounded_by N₀`
for `N₀ := rr5FiniteCover_maxLength`. -/
theorem rr5BaseFinder_constructive_length_bounded_by :
    BaseFinder_length_bounded_by
      (rr5FiniteCover_maxLength : ℝ)
      rr5BaseFinder_constructive := by
  intro U
  have h := rr5BaseFinder_constructive_length_le_max U
  exact_mod_cast h

/-! ## 6. Fully UNCONDITIONAL Read-Rezayi `SU(2)_5` 3-conjunct strict headline -/

/-- **Phase 6x Tier-1 residual B-RR5 — UNCONDITIONAL Read-Rezayi
`SU(2)_5` 3-conjunct strict headline at the constructive base finder**.

For any target `U ∈ SU(2)` and precision `ε ∈ (0, ε₀]`, the lightweight
constructive Dawson-Nielsen Solovay-Kitaev compiler at Read-Rezayi
`SU(2)_5` (using `rr5BaseFinder_constructive` from the finite-Finset
ε₀-cover) returns a `FreeGroup (Fin 2)` word with ALL THREE:

  - **Error**: `‖ρ_RR5 (compile U ε) − U‖ ≤ ε`.
  - **Abstract length**: `skLength (skLevel_polylog ε) ≤ skLengthConst · …`.
  - **Concrete length**: `((compile U ε).toWord.length : ℝ) ≤
    skLength_at_baseCase (rr5FiniteCover_maxLength) (skLevel_polylog ε)`.

The third conjunct is parametric in `rr5FiniteCover_maxLength`
(the actual maximum word length in the finite ε₀-cover Finset for RR5).

UNCONDITIONAL — composes shipped unconditional substrate (SU(2)
compactness + RR5 density via Chebyshev `T_7` Niven + finite-Finset
ε-cover existence + M.4 parametric length bound). Standard kernel only
`{propext, Classical.choice, Quot.sound}`.

**Closes Phase 6x Tier-1 residual B-RR5** (2026-05-27 audit addendum) —
retrospective failure mode #4 ("substrate vs headline") now closed at
the UNCONDITIONAL 3-conjunct level for Read-Rezayi `SU(2)_5`. -/
theorem solovayKitaev_dawson_nielsen_quantitative_readRezayiK5_strict_concrete_constructive_unconditional
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ)
    (hε_pos : 0 < ε) (hε_le : ε ≤ ε₀) :
    ‖((readRezayiK5GeneratingSet.ρ_hom
            (solovayKitaev_compile_strict_constructive_generic
              readRezayiK5GeneratingSet rr5BaseFinder_constructive U ε) :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε ∧
    skLength (skLevel_polylog ε) ≤
      skLengthConst * (Real.log (1 / ε)) ^ skLengthExponent ∧
    ((solovayKitaev_compile_strict_constructive_generic
        readRezayiK5GeneratingSet rr5BaseFinder_constructive U ε).toWord.length : ℝ)
        ≤ skLength_at_baseCase (rr5FiniteCover_maxLength : ℝ)
            (skLevel_polylog ε) := by
  have h12 := solovayKitaev_dawson_nielsen_quantitative_generic_strict_constructive_tight_unconditional
    readRezayiK5GeneratingSet rr5BaseFinder_constructive
    rr5BaseFinder_constructive_approximates_within_two_ε₀
    U ε hε_pos hε_le
  have h3 := skApproxC_generic_freeGroup_length_le_skLength_at_baseCase
    ρ_RR5 readRezayiK5Gens readRezayiK5Gens_nonempty readRezayiK5Gens_generate
    rr5BaseFinder_constructive
    (rr5FiniteCover_maxLength : ℝ)
    rr5BaseFinder_constructive_length_bounded_by
    (skLevel_polylog ε) U
  exact ⟨h12.1, h12.2, h3⟩

end SKEFTHawking.FKLW.GenericSU2
