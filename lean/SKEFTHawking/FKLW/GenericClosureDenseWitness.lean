/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6u Wave 2 — Generic closure-dense witness + culmination

Generalizes the Phase 6t/Phase 5 Step 13 Fibonacci-specific
`H_Fib_v4_witness_unconditional` + `fibonacci_density_F21_unconditional`
chain to an arbitrary `GeneratingSet` via the `ClosureDenseWitness`
structure.

## Headline theorems

  * `H_of_G_eq_top_of_witness`: any `GeneratingSet` admitting a
    `ClosureDenseWitness` has `H_of_G gs = ⊤`, via Phase 5 Step 13's
    alphabet-agnostic `CartanFinalStep_SU2_v4_holds`.

  * `densityFromWitness`: any `GeneratingSet` admitting a witness has its
    image dense in SU(2) (existentially: for every `U ∈ SU(2)` and `ε > 0`,
    there is a word `w : gs.W` with `‖gs.ρ_hom w - U‖ < ε`).

  * `fibonacciClosureDenseWitness`: validates the abstraction by exhibiting
    the Fibonacci-specific `H_Fib_v4_witness_unconditional` as a
    `ClosureDenseWitness fibonacciGeneratingSet`. As a consequence,
    `fibonacci_density_F21_unconditional` becomes a definitional instance
    of `densityFromWitness fibonacciClosureDenseWitness`.

## Design

`ClosureDenseWitness gs` carries TWO explicit ℝ-LI traceless skew-Hermitian
matrices `X₁ X₂ ∈ 𝔰𝔲(2)` plus 1-parameter-subgroup flow lines `exp(t·X_i)
⊆ H_of_G gs` for all real `t`. This is the v4 witness shape — strictly
stronger than v3 (which only requires the flow at one anchor `s`) — that
discharges Cartan's closed-subgroup classification of SU(2) to `H = ⊤`.

The structure carries an `Inhabited`-style payload (it's a `Type`, not a
`Prop`), so its existence is a `MEM`-witness for downstream Wave 3/4/6
consumers that need *constructive* access to the X_1, X_2 data.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected — all proofs are direct
  composition of Phase 5/6t substrate.
- **#15** (no new axioms): respected — zero new project-local axioms.
- **Strengthening discipline**: the witness type is non-vacuous (every
  field is used in the v4 hypothesis composition); the headline theorem
  is load-bearing (it strictly entails Fibonacci's culmination); the
  density predicate `IsDenseInSU2_gs` is not a tautology (it asserts a
  metric-approximation property requiring the witness to discharge).

-/

import SKEFTHawking.FKLW.GenericSU2GeneratingSet
import SKEFTHawking.FKLW.SU2BCHBracketClosure
import SKEFTHawking.FKLW.OneParameterSubgroupSU2

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

open Matrix
open SKEFTHawking.FKLW
open SKEFTHawking.FKLW.SU2LieAlgebra
open SKEFTHawking.FKLW.SU2MatrixExp

/-! ## 1. The `ClosureDenseWitness` structure

Bundles the two ℝ-LI traceless skew-Hermitian flow-line tangents required
by Cartan's v4 hypothesis at `H_of_G gs`. -/

/-- **A `ClosureDenseWitness` for a `GeneratingSet`.**

Two explicit ℝ-LI traceless skew-Hermitian matrices `X₁, X₂ ∈ 𝔰𝔲(2)` with
1-parameter-subgroup flow lines `exp(ℝ • X_i) ⊆ H_of_G gs`. This is the
v4 shape (Cartan's strict-hypothesis form): the all-t identity is required,
not just an anchor.

For Fibonacci: built from `H_Fib_v4_witness_unconditional` (Phase 5 Step 13).
For Clifford+T (Track T-S): to be constructed from the Boykin-Mor-Pulver-
Roychowdhury-Vatan 1999 closure-density argument.

Carrying this as a `Type` (not a `Prop`) gives downstream waves
constructive access to the tangent data. -/
structure ClosureDenseWitness (gs : GeneratingSet) : Type where
  /-- First tangent direction. -/
  X₁ : Matrix (Fin 2) (Fin 2) ℂ
  /-- Second tangent direction. -/
  X₂ : Matrix (Fin 2) (Fin 2) ℂ
  /-- `X₁` is in 𝔰𝔲(2). -/
  hX₁_ts : X₁ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2)
  /-- `X₂` is in 𝔰𝔲(2). -/
  hX₂_ts : X₂ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2)
  /-- The full 1-parameter flow line `exp(ℝ • X₁) ⊆ H_of_G gs`. -/
  flow_X₁ : ∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
      M ∈ H_of_G gs ∧ M.val = expAmbient (((t : ℝ) : ℂ) • X₁)
  /-- The full 1-parameter flow line `exp(ℝ • X₂) ⊆ H_of_G gs`. -/
  flow_X₂ : ∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
      M ∈ H_of_G gs ∧ M.val = expAmbient (((t : ℝ) : ℂ) • X₂)
  /-- `X₁`, `X₂` are ℝ-linearly independent in 𝔰𝔲(2). -/
  hLI : ∀ a b : ℝ, (a : ℂ) • X₁ + (b : ℂ) • X₂ = 0 → a = 0 ∧ b = 0

/-! ## 2. v4 culmination — `H_of_G gs = ⊤`

Applies `CartanFinalStep_SU2_v4_holds` to dispatch the witness into the
top-subgroup conclusion. -/

/-- **Wave 2 headline**: a `GeneratingSet` admitting a `ClosureDenseWitness`
has its generated closed subgroup equal to `⊤ = SU(2)`.

Composes:
  * `H_of_G_isClosed gs` (Wave 1) — closedness of the subgroup;
  * the witness data (X₁, X₂, flow lines, ℝ-LI) — the v4 hypothesis;
  * `CartanFinalStep_SU2_v4_holds` (Phase 5 Step 13, alphabet-agnostic)
    — Cartan's discharge of the closed-subgroup classification.

This is the **abstract analog of `H_Fib_eq_top_of_cartan_final_v4`**: any
GeneratingSet with a witness reaches `H = ⊤`, regardless of the underlying
word-type or generator structure. -/
theorem H_of_G_eq_top_of_witness
    {gs : GeneratingSet} (w : ClosureDenseWitness gs) :
    H_of_G gs = ⊤ := by
  apply CartanFinalStep_SU2_v4_holds (H_of_G gs) (H_of_G_isClosed gs)
  refine ⟨w.X₁, w.X₂, w.hX₁_ts, w.hX₂_ts, ?_, ?_, w.hLI⟩
  · exact w.flow_X₁
  · exact w.flow_X₂

/-! ## 3. Density in SU(2)

`H_of_G gs = ⊤` immediately gives that every element of SU(2) is in the
topological closure of the image of `ρ_hom`, hence is approximable to
arbitrary precision by elements of the form `ρ_hom w` for some `w : gs.W`. -/

/-- **Generic density predicate** for a `GeneratingSet`.

For every `U ∈ SU(2)` and `ε > 0`, there exists `w : gs.W` such that
`‖(gs.ρ_hom w).val - U.val‖ < ε` (the operator norm).

This is the *abstract* analog of `AharonovAradBridge.DenseInSpecialUnitary
3 2 (fun b => ρ_Fib_SU2 b)` — it abstracts away the BraidGroup-specific
typing and operates directly on the GeneratingSet's word type. -/
def IsDenseInSU2_gs (gs : GeneratingSet) : Prop :=
  ∀ (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ), 0 < ε →
    ∃ w : gs.W, ‖((gs.ρ_hom w : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) -
          (U : Matrix (Fin 2) (Fin 2) ℂ)‖ < ε

/-- **`H_of_G gs = ⊤` ↔ `closure (range gs.ρ_hom) = univ`** (generic
analog of `H_Fib_eq_top_iff_closure_eq_univ`, alphabet-independent). -/
theorem H_of_G_eq_top_iff_closure_eq_univ (gs : GeneratingSet) :
    H_of_G gs = ⊤ ↔ closure (Set.range gs.ρ_hom) =
      (Set.univ : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  unfold H_of_G
  rw [SetLike.ext'_iff]
  rw [Subgroup.topologicalClosure_coe, gs.ρ_hom.coe_range, Subgroup.coe_top]

/-- **From `H_of_G gs = ⊤` to generic density.**

The topological closure of `gs.ρ_hom.range` equals `⊤`, so every `U ∈ SU(2)`
is in this closure, which means there is a sequence in the range converging
to `U`. Extracting one term within `ε` and unfolding the range membership
gives the witness word `w`.

Approach (working in the matrix ambient space because Matrix has a normed
ring structure but the SU(2) subtype's quasi-uniformity isn't a metric in
general):
  1. From `h : H_of_G gs = ⊤` get `closure (range gs.ρ_hom) = univ` (subtype).
  2. Push forward via continuous `Subtype.val` to a closure in `Matrix _ _ ℂ`.
  3. `Metric.mem_closure_iff` on the matrix space yields a witness within `ε`. -/
theorem isDenseInSU2_gs_of_eq_top
    (gs : GeneratingSet) (h : H_of_G gs = ⊤) :
    IsDenseInSU2_gs gs := by
  intro U ε hε
  -- Step 1: convert `H_of_G gs = ⊤` to `closure (range gs.ρ_hom) = univ` (subtype).
  have h_closure_univ :
      closure (Set.range gs.ρ_hom) =
        (Set.univ : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :=
    (H_of_G_eq_top_iff_closure_eq_univ gs).mp h
  -- Step 2: U ∈ closure (range gs.ρ_hom).
  have hU_in_subtype_closure :
      (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∈ closure (Set.range gs.ρ_hom) := by
    rw [h_closure_univ]; trivial
  -- Step 3: push forward via continuous Subtype.val.
  have h_cont : Continuous
      (fun x : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) =>
        (x : Matrix (Fin 2) (Fin 2) ℂ)) := continuous_subtype_val
  have h_image_subset :
      (fun x : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) =>
          (x : Matrix (Fin 2) (Fin 2) ℂ)) '' closure (Set.range gs.ρ_hom) ⊆
        closure
          ((fun x : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) =>
              (x : Matrix (Fin 2) (Fin 2) ℂ)) '' (Set.range gs.ρ_hom)) :=
    image_closure_subset_closure_image h_cont
  have hU_val_in_image_closure :
      (U : Matrix (Fin 2) (Fin 2) ℂ) ∈
        closure
          ((fun x : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) =>
              (x : Matrix (Fin 2) (Fin 2) ℂ)) '' (Set.range gs.ρ_hom)) :=
    h_image_subset ⟨U, hU_in_subtype_closure, rfl⟩
  -- Step 4: rewrite image of range as range of composed function.
  have h_image_eq :
      (fun x : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) =>
          (x : Matrix (Fin 2) (Fin 2) ℂ)) '' (Set.range gs.ρ_hom) =
      Set.range (fun w : gs.W =>
        ((gs.ρ_hom w : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix (Fin 2) (Fin 2) ℂ)) := by
    ext A
    constructor
    · rintro ⟨M, ⟨w, hw_eq⟩, hM_val⟩
      refine ⟨w, ?_⟩
      simp only at hM_val ⊢
      rw [hw_eq]; exact hM_val
    · rintro ⟨w, hw_eq⟩
      exact ⟨gs.ρ_hom w, ⟨w, rfl⟩, hw_eq⟩
  rw [h_image_eq] at hU_val_in_image_closure
  -- Step 5: extract a witness within ε using Metric.mem_closure_iff.
  rcases Metric.mem_closure_iff.mp hU_val_in_image_closure ε hε with ⟨A, hA_range, hA_close⟩
  rcases hA_range with ⟨w, hw_eq⟩
  refine ⟨w, ?_⟩
  -- hA_close : dist ↑U A < ε.  A = ↑(gs.ρ_hom w) (from hw_eq).
  -- Goal: ‖↑(gs.ρ_hom w) - ↑U‖ < ε.
  rw [dist_eq_norm] at hA_close
  rw [show ((gs.ρ_hom w : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) = A from hw_eq]
  rw [norm_sub_rev]
  exact hA_close

/-- **Wave 2 density culmination**: a `GeneratingSet` admitting a
`ClosureDenseWitness` has its image dense in SU(2).

Composes `H_of_G_eq_top_of_witness` with `isDenseInSU2_gs_of_eq_top`. -/
theorem densityFromWitness
    {gs : GeneratingSet} (w : ClosureDenseWitness gs) :
    IsDenseInSU2_gs gs :=
  isDenseInSU2_gs_of_eq_top gs (H_of_G_eq_top_of_witness w)

/-! ## 4. Fibonacci instance — validates the abstraction

The Fibonacci specialization recovers `H_Fib = ⊤` (Phase 5 Step 13's
unconditional Fibonacci density culmination) by exhibiting
`H_Fib_v4_witness_unconditional` as a `ClosureDenseWitness fibonacciGeneratingSet`. -/

/-- **The Fibonacci closure-dense witness**.

Built from `H_Fib_v4_witness_unconditional` (Phase 5 Step 13, Phase 6p Wave
2c.4a-R4.2.d). Since `H_of_G fibonacciGeneratingSet = H_Fib` by definitional
reduction (`H_of_G_specialize_Fib`), the flow-line membership conditions
transfer without rewriting.

`H_Fib_v4_witness_unconditional` is a `Prop` (existential), so we use
`Nonempty.some` to extract a `Type`-level witness via `Classical.choice`
(standard kernel). -/
noncomputable def fibonacciClosureDenseWitness :
    ClosureDenseWitness fibonacciGeneratingSet := by
  -- Build Nonempty of the structure from the Prop existential, then extract via Classical.choice.
  have h_ne : Nonempty (ClosureDenseWitness fibonacciGeneratingSet) := by
    obtain ⟨X₁, X₂, hX₁_ts, hX₂_ts, h_flow_X₁, h_flow_X₂, h_LI⟩ :=
      SKEFTHawking.FKLW.OneParameterSubgroupSU2.H_Fib_v4_witness_unconditional
    refine ⟨{ X₁ := X₁, X₂ := X₂
            , hX₁_ts := hX₁_ts, hX₂_ts := hX₂_ts
            , flow_X₁ := ?_, flow_X₂ := ?_
            , hLI := h_LI }⟩
    · intro t
      obtain ⟨M, hM_in_HFib, hM_val⟩ := h_flow_X₁ t
      refine ⟨M, ?_, hM_val⟩
      rw [show H_of_G fibonacciGeneratingSet = SKEFTHawking.FKLW.H_Fib from H_of_G_specialize_Fib]
      exact hM_in_HFib
    · intro t
      obtain ⟨M, hM_in_HFib, hM_val⟩ := h_flow_X₂ t
      refine ⟨M, ?_, hM_val⟩
      rw [show H_of_G fibonacciGeneratingSet = SKEFTHawking.FKLW.H_Fib from H_of_G_specialize_Fib]
      exact hM_in_HFib
  exact h_ne.some

/-- **Fibonacci density via the generic substrate.**

Recovers Phase 5 Step 13's unconditional Fibonacci density at the generic
density-predicate level, by composing `densityFromWitness` with the
Fibonacci closure-dense witness. -/
theorem fibonacci_density_via_generic :
    IsDenseInSU2_gs fibonacciGeneratingSet :=
  densityFromWitness fibonacciClosureDenseWitness

/-- **Fibonacci closed-subgroup = ⊤ via the generic substrate.**

By composition: `fibonacciClosureDenseWitness` discharges Cartan v4, so
`H_of_G fibonacciGeneratingSet = ⊤`, equivalently `H_Fib = ⊤`. -/
theorem fibonacci_H_eq_top_via_generic :
    SKEFTHawking.FKLW.H_Fib = (⊤ : Subgroup _) := by
  have h := H_of_G_eq_top_of_witness fibonacciClosureDenseWitness
  rw [H_of_G_specialize_Fib] at h
  exact h

end SKEFTHawking.FKLW.GenericSU2
