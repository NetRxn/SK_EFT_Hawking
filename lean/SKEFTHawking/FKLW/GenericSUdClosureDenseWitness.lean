/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.2-consumer — Generic SU(d) `ClosureDenseWitness`

d-parametric lift of Phase 6u's `GenericClosureDenseWitness` to SU(d).
Carries the tangent + flow-line data needed to dispatch
`CartanFinalStep_SUd_v4_holds` (S.2g) into `H_of_G gs = ⊤`.

## Mathematical content

A `ClosureDenseWitness gs` (for `gs : GeneratingSet d`) carries:

  * Finite `n` of traceless skew-Hermitian tangents `X : Fin n → Matrix (Fin d) (Fin d) ℂ`
  * Spanning condition: every traceless skew-Hermitian Y is an
    ℝ-linear combination of the `X i`.
  * Flow-line containment: `exp(ℝ • X i) ⊆ H_of_G gs` for all `i`.

This matches the hypothesis-form of `CartanFinalStep_SUd_v4 d`
(Phase 6y S.2a predicate), so dispatch is direct.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" — consumer substrate for S.2.

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdGeneratingSet
import SKEFTHawking.FKLW.GenericSUdCartanPredicate
import SKEFTHawking.FKLW.SU2LieAlgebra

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. The d-generic `ClosureDenseWitness` structure -/

/-- **Generic SU(d) closure-density witness** for a `GeneratingSet d`.

Bundles a spanning collection of `n` traceless skew-Hermitian tangents
`X : Fin n → Matrix (Fin d) (Fin d) ℂ` together with their full
1-parameter flow-line containment in `H_of_G gs`. Matches the
hypothesis-form of the Phase 6y S.2a predicate `CartanFinalStep_SUd_v4`.

For Phase 6y Track T-A1′.2 (SU(4) trapped-ion): consumers construct
the witness from MS(θ) + per-ion 1Q closure-density at SU(4).
For Phase 6y Track T-A2′.2 (SU(8) Clifford+CCZ): from the Aaronson-
Gottesman 2004 universality of Clifford+CCZ at SU(2^n). -/
structure ClosureDenseWitness {d : ℕ} (gs : GeneratingSet d) : Type where
  /-- Number of tangents. -/
  n : ℕ
  /-- The tangent collection. -/
  X : Fin n → Matrix (Fin d) (Fin d) ℂ
  /-- Each tangent is traceless skew-Hermitian (in 𝔰𝔲(d)). -/
  hX_in_sud : ∀ i, (X i).IsSkewHermitian ∧ (X i).trace = 0
  /-- The ℝ-span of the tangents covers all of 𝔰𝔲(d). -/
  hX_spans : ∀ Y : Matrix (Fin d) (Fin d) ℂ,
    Y.IsSkewHermitian → Y.trace = 0 →
    ∃ c : Fin n → ℝ, Y = ∑ i, ((c i : ℝ) : ℂ) • X i
  /-- Each tangent's 1-parameter flow line is in `H_of_G gs`. -/
  hX_flow : ∀ i, ∀ t : ℝ,
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ),
      M ∈ H_of_G gs ∧ M.val = NormedSpace.exp (((t : ℝ) : ℂ) • X i)

/-! ## 2. Dispatch to `H_of_G gs = ⊤`

Conditional on `CartanFinalStep_SUd_v4 d` (Phase 6y S.2 predicate),
a `ClosureDenseWitness gs` discharges `H_of_G gs = ⊤`. -/

/-- **Conditional dispatch**: a `ClosureDenseWitness` discharges
`H_of_G gs = ⊤` if the SU(d) Cartan-final-step v4 holds.

The full unconditional discharge ships when `CartanFinalStep_SUd_v4_holds`
(Phase 6y S.2g) is composed in. -/
theorem H_of_G_eq_top_of_witness_conditional {d : ℕ} {gs : GeneratingSet d}
    (w : ClosureDenseWitness gs)
    (h_cartan : CartanFinalStep_SUd_v4 d) :
    H_of_G gs = ⊤ := by
  apply h_cartan (H_of_G gs) (H_of_G_isClosed gs)
  exact ⟨w.n, w.X, w.hX_in_sud, w.hX_spans, w.hX_flow⟩

/-! ## 3. Density in SU(d)

`H_of_G gs = ⊤` immediately gives that every element of SU(d) is in the
topological closure of the image of `ρ_hom`, hence approximable to
arbitrary precision. Adapts Phase 6u's SU(2) `isDenseInSU2_gs_of_eq_top`
to arbitrary d. -/

/-- **Generic SU(d) density predicate** for a `GeneratingSet d`. -/
def IsDenseInSUd_gs {d : ℕ} (gs : GeneratingSet d) : Prop :=
  ∀ (U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) (ε : ℝ), 0 < ε →
    ∃ w : gs.W, ‖((gs.ρ_hom w : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
        Matrix (Fin d) (Fin d) ℂ) -
          (U : Matrix (Fin d) (Fin d) ℂ)‖ < ε

/-- **`H_of_G gs = ⊤` ↔ `closure (range gs.ρ_hom) = univ`**. -/
theorem H_of_G_eq_top_iff_closure_eq_univ {d : ℕ} (gs : GeneratingSet d) :
    H_of_G gs = ⊤ ↔ closure (Set.range gs.ρ_hom) =
      (Set.univ : Set ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) := by
  unfold H_of_G
  rw [SetLike.ext'_iff]
  rw [Subgroup.topologicalClosure_coe, gs.ρ_hom.coe_range, Subgroup.coe_top]

/-- **From `H_of_G gs = ⊤` to generic density**. d-generic lift of
Phase 6u's `isDenseInSU2_gs_of_eq_top`. -/
theorem isDenseInSUd_gs_of_eq_top
    {d : ℕ} (gs : GeneratingSet d) (h : H_of_G gs = ⊤) :
    IsDenseInSUd_gs gs := by
  intro U ε hε
  have h_closure_univ :
      closure (Set.range gs.ρ_hom) =
        (Set.univ : Set ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :=
    (H_of_G_eq_top_iff_closure_eq_univ gs).mp h
  have hU_in_subtype_closure :
      (U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) ∈ closure (Set.range gs.ρ_hom) := by
    rw [h_closure_univ]; trivial
  have h_cont : Continuous
      (fun x : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ) =>
        (x : Matrix (Fin d) (Fin d) ℂ)) := continuous_subtype_val
  have h_image_subset :
      (fun x : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ) =>
          (x : Matrix (Fin d) (Fin d) ℂ)) '' closure (Set.range gs.ρ_hom) ⊆
        closure
          ((fun x : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ) =>
              (x : Matrix (Fin d) (Fin d) ℂ)) '' (Set.range gs.ρ_hom)) :=
    image_closure_subset_closure_image h_cont
  have hU_val_in_image_closure :
      (U : Matrix (Fin d) (Fin d) ℂ) ∈
        closure
          ((fun x : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ) =>
              (x : Matrix (Fin d) (Fin d) ℂ)) '' (Set.range gs.ρ_hom)) :=
    h_image_subset ⟨U, hU_in_subtype_closure, rfl⟩
  have h_image_eq :
      (fun x : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ) =>
          (x : Matrix (Fin d) (Fin d) ℂ)) '' (Set.range gs.ρ_hom) =
      Set.range (fun w : gs.W =>
        ((gs.ρ_hom w : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
          Matrix (Fin d) (Fin d) ℂ)) := by
    ext A
    constructor
    · rintro ⟨M, ⟨w, hw_eq⟩, hM_val⟩
      refine ⟨w, ?_⟩
      simp only at hM_val ⊢
      rw [hw_eq]; exact hM_val
    · rintro ⟨w, hw_eq⟩
      exact ⟨gs.ρ_hom w, ⟨w, rfl⟩, hw_eq⟩
  rw [h_image_eq] at hU_val_in_image_closure
  rcases Metric.mem_closure_iff.mp hU_val_in_image_closure ε hε with ⟨A, hA_range, hA_close⟩
  rcases hA_range with ⟨w, hw_eq⟩
  refine ⟨w, ?_⟩
  rw [dist_eq_norm] at hA_close
  rw [show ((gs.ρ_hom w : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
        Matrix (Fin d) (Fin d) ℂ) = A from hw_eq]
  rw [norm_sub_rev]
  exact hA_close

/-- **Density culmination** (conditional): a `GeneratingSet d` admitting
a `ClosureDenseWitness` has its image dense in SU(d), conditional on
`CartanFinalStep_SUd_v4 d`. -/
theorem densityFromWitness_conditional
    {d : ℕ} {gs : GeneratingSet d} (w : ClosureDenseWitness gs)
    (h_cartan : CartanFinalStep_SUd_v4 d) :
    IsDenseInSUd_gs gs :=
  isDenseInSUd_gs_of_eq_top gs (H_of_G_eq_top_of_witness_conditional w h_cartan)

end SKEFTHawking.FKLW.GenericSUd
