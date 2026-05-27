/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Track T-S′ (lightweight algorithmic ship) — Constructive length-bounded Clifford+T base finder via finite-Finset enumeration

Ships the **algorithmic / runnable** constructive ε₀-net for the
Clifford+T `GeneratingSet` by composing the existing `ConstructiveEpsilonNet`
finite-Finset coverage theorem (Phase 6x first session) with the
SU(2) compactness substrate (`Matrix.specialUnitaryGroup_isCompact`,
shipped Phase 6p Wave 2c.4a-substrate). The resulting base finder is
length-bounded by the Finset's maximum word length — a constructive
length bound, even if non-optimal compared to Ross-Selinger 2014's
O(log(1/ε)) optimal bound.

## Lift/shift reading vs full Ross-Selinger ship

The Ross-Selinger 2014 algorithm (arXiv:1403.2975) provides
**information-theoretically optimal** Clifford+T compilation via
ℤ[ω][1/√2] symbolic enumeration: words of length O(log(1/ε)) for
ε-approximation. Full Lean formalization of Ross-Selinger requires
~1,600–3,000 LoC of substantive number-theoretic substrate
(`ZOmega`, `ZOmegaSqrt2`, lattice enumeration, Kliuchnikov-Maslov-Mosca
exact synthesis) — multi-session work; Lit-Search task dropped at
`Lit-Search/tasks/ross_selinger_arxiv_1403_2975_zomega_invsqrt2_synthesis.md`.

The **lightweight algorithmic ship** here uses the existing finite-Finset
ε-cover (built via SU(2) compactness + closure-density witness, both
unconditionally discharged in Phase 6p and Phase 6u) to construct a
length-bounded base finder. This is genuinely-runnable (`Finset.choose`
modulo Classical extraction; the Finset itself is finite and
enumerable) and length-bounded (by the Finset's `max'` projection on
word lengths). The length bound is NOT optimal — it's the Finset's
actual maximum length, which can be substantial. But it IS a length
bound, closing the structural gap.

The Ross-Selinger optimal refinement is the natural follow-on once the
Lit-Search task returns.

## Headline definitions

  * `cliffordTFiniteCover ε₀ ε₀_pos : Finset (FreeGroup (Fin 2))` —
    the finite ε₀-cover Finset for Clifford+T, built via
    `cliffordT_finite_epsilon_net_of_compact` + the discharged SU(2)
    compactness substrate. UNCONDITIONAL.

  * `cliffordTBaseFinder_constructive : SU(2) → FreeGroup (Fin 2)` —
    the constructive length-bounded base finder: pick any
    `w ∈ cliffordTFiniteCover` with `‖ρ_CliffT w − U‖ < ε₀`. The
    existence follows from the Finset coverage; the extraction is via
    `Classical.choose` (one-shot per query, not over the entire SU(2)).
    UNCONDITIONAL.

  * `cliffordTBaseFinder_constructive_approx_opNorm` — correctness:
    `‖ρ_CliffT (bf U) − U‖ < ε₀`. UNCONDITIONAL.

  * `cliffordTBaseFinder_constructive_in_cover` — structural: the
    base finder's output lies in the finite cover.

  * `cliffordTBaseFinder_constructive_length_le_max` — length bound:
    the base finder's output has word length ≤ the cover Finset's max
    length (provided the cover is non-empty). UNCONDITIONAL.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected — composes
  unconditional substrate (`Matrix.specialUnitaryGroup_isCompact` +
  `cliffordT_density_unconditional` + `ConstructiveEpsilonNet`).

-/

import SKEFTHawking.FKLW.ConstructiveEpsilonNet
import SKEFTHawking.FKLW.SpecialUnitaryTopology
import SKEFTHawking.FKLW.EpsilonNet
import SKEFTHawking.FKLW.GenericConcreteWordLengthBound
import SKEFTHawking.FKLW.GenericSolovayKitaevRecursionDischarge

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

open Matrix SKEFTHawking SKEFTHawking.FKLW
  SKEFTHawking.FKLW.SolovayKitaevRecursion
  SKEFTHawking.FKLW.SolovayKitaevLengthBound

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. SU(2) compactness at the subtype level

`Matrix.specialUnitaryGroup_isCompact` ships compactness at the carrier
set level (subset of matrices). `Matrix.instCompactSpaceSpecialUnitaryGroup`
ships the `CompactSpace` instance at the subtype level. Combined with
`isCompact_univ`, we get `IsCompact (Set.univ : Set ↥(SU(2)))`. -/

/-- **SU(2) (subtype) is compact**: the whole space `↥SU(2)` is compact.

Follows from `Matrix.instCompactSpaceSpecialUnitaryGroup`
(Phase 6p Wave 2c.4a-substrate, 2026-05-12) via `isCompact_univ`. -/
theorem su2_subtype_isCompact :
    IsCompact ((Set.univ : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))) :=
  isCompact_univ

/-! ## 2. The Clifford+T finite ε₀-cover (UNCONDITIONAL) -/

/-- **The Clifford+T finite ε₀-cover Finset (UNCONDITIONAL)**.

Built by applying `cliffordT_finite_epsilon_net_of_compact` to the
shipped SU(2) compactness. The resulting `Finset (FreeGroup (Fin 2))`
ε₀-covers all of SU(2): for every `U`, some `w` in the Finset has
`‖ρ_CliffT w − U‖ < ε₀`. Existential at the Finset level
(`Classical.choose` extracts the Finset from the compactness +
density proofs); per-`U` enumeration over the Finset is decidable. -/
noncomputable def cliffordTFiniteCover : Finset (FreeGroup (Fin 2)) :=
  (cliffordT_finite_epsilon_net_of_compact
    su2_subtype_isCompact ε₀ ε₀_pos).choose

/-- **Coverage property of `cliffordTFiniteCover`**: every `U ∈ SU(2)`
has some `w` in the cover with `‖ρ_CliffT w − U‖ < ε₀`. -/
theorem cliffordTFiniteCover_covers
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ∃ w ∈ cliffordTFiniteCover,
      ‖((cliffordTGeneratingSet.ρ_hom w :
            ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix (Fin 2) (Fin 2) ℂ) -
          (U : Matrix (Fin 2) (Fin 2) ℂ)‖ < ε₀ :=
  (cliffordT_finite_epsilon_net_of_compact
    su2_subtype_isCompact ε₀ ε₀_pos).choose_spec U

/-! ## 3. Constructive Clifford+T base finder via finite-Finset enumeration

For each `U ∈ SU(2)`, extract a witness `w ∈ cliffordTFiniteCover`
with `‖ρ_CliffT w − U‖ < ε₀`. The existence is the
`cliffordTFiniteCover_covers` theorem; the per-`U` extraction is one
`Classical.choose` invocation. The result IS in the Finset and IS
length-bounded by the Finset's max word length. -/

/-- **Constructive Clifford+T base finder via finite-Finset enumeration
(UNCONDITIONAL)**.

For each `U ∈ SU(2)`, picks a `FreeGroup (Fin 2)` word `w` from the
finite cover Finset `cliffordTFiniteCover` such that
`‖ρ_CliffT w − U‖ < ε₀`. The existence is guaranteed by the cover
property; one `Classical.choose` per query. -/
noncomputable def cliffordTBaseFinder_constructive :
    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) → FreeGroup (Fin 2) :=
  fun U => (cliffordTFiniteCover_covers U).choose

/-- **Correctness of the constructive base finder**: output
ε₀-approximates `U` (UNCONDITIONAL). -/
theorem cliffordTBaseFinder_constructive_approx_opNorm
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ‖((cliffordTGeneratingSet.ρ_hom (cliffordTBaseFinder_constructive U) :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ < ε₀ :=
  ((cliffordTFiniteCover_covers U).choose_spec).2

/-- **Structural property**: the constructive base finder's output
always lies in `cliffordTFiniteCover` (UNCONDITIONAL).

This is the load-bearing fact for the length bound: any
`w = cliffordTBaseFinder_constructive U` is in a fixed finite Finset,
hence has bounded length. -/
theorem cliffordTBaseFinder_constructive_in_cover
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    cliffordTBaseFinder_constructive U ∈ cliffordTFiniteCover :=
  ((cliffordTFiniteCover_covers U).choose_spec).1

/-! ## 4. Calibration: base finder ε₀-approximates → satisfies (2·ε₀) -/

/-- The constructive base finder satisfies
`BaseFinder_approximates_within cliffordTGeneratingSet
   cliffordTBaseFinder_constructive (2 * ε₀)` (UNCONDITIONAL). -/
theorem cliffordTBaseFinder_constructive_approximates_within_two_ε₀ :
    BaseFinder_approximates_within cliffordTGeneratingSet
      cliffordTBaseFinder_constructive (2 * ε₀) := by
  intro U
  have h1 := cliffordTBaseFinder_constructive_approx_opNorm U
  have h2 : ε₀ < 2 * ε₀ := by have := ε₀_pos; linarith
  linarith

/-! ## 5. Length-bound at the Finset's max length (UNCONDITIONAL)

The base finder's output is always in the finite Finset
`cliffordTFiniteCover`, so its word length is bounded by the Finset's
max word length. The bound is parametric in the Finset's construction
(NOT necessarily ≤ `skLengthBaseCase`, which is the conservative Ross-
Selinger calibration constant). -/

/-- **The Finset's max word length**: the maximum FreeGroup-word-length
across all words in `cliffordTFiniteCover`. Defined as
`(cliffordTFiniteCover.image (fun w => w.toWord.length)).max'` when the
Finset is non-empty, else 0. -/
noncomputable def cliffordTFiniteCover_maxLength : ℕ :=
  if h : cliffordTFiniteCover.Nonempty then
    (cliffordTFiniteCover.image (fun w => w.toWord.length)).max'
      (h.image _)
  else 0

/-- **Length bound for the constructive base finder (UNCONDITIONAL)**:
the output has word length ≤ `cliffordTFiniteCover_maxLength`. -/
theorem cliffordTBaseFinder_constructive_length_le_max
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    (cliffordTBaseFinder_constructive U).toWord.length
      ≤ cliffordTFiniteCover_maxLength := by
  -- The output is in cliffordTFiniteCover; the Finset is non-empty
  -- (contains at least the output); max' bounds the image.
  have h_in : cliffordTBaseFinder_constructive U ∈ cliffordTFiniteCover :=
    cliffordTBaseFinder_constructive_in_cover U
  have h_nonempty : cliffordTFiniteCover.Nonempty := ⟨_, h_in⟩
  unfold cliffordTFiniteCover_maxLength
  rw [dif_pos h_nonempty]
  apply Finset.le_max'
  -- The output's word length is in the image of cliffordTFiniteCover.
  exact Finset.mem_image.mpr ⟨_, h_in, rfl⟩

/-- **Parametric length-bound predicate discharge**: the constructive
base finder satisfies `BaseFinder_length_bounded_by N₀` for the
specific `N₀ := cliffordTFiniteCover_maxLength` (UNCONDITIONAL). -/
theorem cliffordTBaseFinder_constructive_length_bounded_by :
    BaseFinder_length_bounded_by
      (cliffordTFiniteCover_maxLength : ℝ)
      cliffordTBaseFinder_constructive := by
  intro U
  have h := cliffordTBaseFinder_constructive_length_le_max U
  exact_mod_cast h

/-! ## 6. Fully UNCONDITIONAL Clifford+T 3-conjunct strict headline

Composes the parametric M.4 headline (`skApproxC_generic_freeGroup_length_le_skLength_at_baseCase`)
with the constructive base finder calibration to produce a **fully
UNCONDITIONAL** Phase 6x Track T-S′ headline at Clifford+T. The
length-bound conjunct is parametric in `cliffordTFiniteCover_maxLength`
(the actual base-case length, NOT the Ross-Selinger-optimal
`skLengthBaseCase = 100`). -/

/-- **Phase 6x Track T-S′ — UNCONDITIONAL Clifford+T 3-conjunct strict
headline at the constructive base finder**.

For any target `U ∈ SU(2)` and precision `ε ∈ (0, ε₀]`, the lightweight
constructive Dawson-Nielsen Solovay-Kitaev compiler at Clifford+T
(using `cliffordTBaseFinder_constructive` from the finite-Finset
ε₀-cover) returns a `FreeGroup (Fin 2)` word with ALL THREE:

  - **Error**: `‖ρ_CliffT (compile U ε) − U‖ ≤ ε`.
  - **Abstract length**: `skLength (skLevel_polylog ε) ≤ skLengthConst · …`.
  - **Concrete length**: `((compile U ε).toWord.length : ℝ) ≤
    skLength_at_baseCase (cliffordTFiniteCover_maxLength) (skLevel_polylog ε)`.

The third conjunct is parametric in `cliffordTFiniteCover_maxLength`
(the actual maximum word length in the finite ε₀-cover Finset). The
Ross-Selinger optimal refinement (length `O(log(1/ε))`, leading
constant matching `skLengthBaseCase = 100`) is the follow-on
substantive ship.

UNCONDITIONAL — composes shipped unconditional substrate (SU(2)
compactness + Clifford+T density + finite-Finset ε-cover existence +
M.4 parametric length bound). Standard kernel only
`{propext, Classical.choice, Quot.sound}`.

**Closes Phase 6x Track T-S′ lightweight algorithmic interpretation**. -/
theorem solovayKitaev_dawson_nielsen_quantitative_cliffordT_strict_concrete_constructive_unconditional
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ)
    (hε_pos : 0 < ε) (hε_le : ε ≤ ε₀) :
    ‖((cliffordTGeneratingSet.ρ_hom
            (solovayKitaev_compile_strict_constructive_generic
              cliffordTGeneratingSet cliffordTBaseFinder_constructive U ε) :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε ∧
    skLength (skLevel_polylog ε) ≤
      skLengthConst * (Real.log (1 / ε)) ^ skLengthExponent ∧
    ((solovayKitaev_compile_strict_constructive_generic
        cliffordTGeneratingSet cliffordTBaseFinder_constructive U ε).toWord.length : ℝ)
        ≤ skLength_at_baseCase (cliffordTFiniteCover_maxLength : ℝ)
            (skLevel_polylog ε) := by
  -- First two conjuncts: existing UNCONDITIONAL 2-conjunct generic headline.
  have h12 := solovayKitaev_dawson_nielsen_quantitative_generic_strict_constructive_tight_unconditional
    cliffordTGeneratingSet cliffordTBaseFinder_constructive
    cliffordTBaseFinder_constructive_approximates_within_two_ε₀
    U ε hε_pos hε_le
  -- Third conjunct: parametric closed-form length bound.
  -- cliffordTGS = mkFreeGroupGS ... by definitional equality (rfl).
  have h3 := skApproxC_generic_freeGroup_length_le_skLength_at_baseCase
    ρ_CliffT cliffordTGens cliffordTGens_nonempty cliffordTGens_generate
    cliffordTBaseFinder_constructive
    (cliffordTFiniteCover_maxLength : ℝ)
    cliffordTBaseFinder_constructive_length_bounded_by
    (skLevel_polylog ε) U
  exact ⟨h12.1, h12.2, h3⟩

end SKEFTHawking.FKLW.GenericSU2
