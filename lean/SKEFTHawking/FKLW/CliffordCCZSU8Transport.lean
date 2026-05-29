/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6z Wave 4 increment 4f.3b — one tensor-Pauli line ⟹ all of them (Clifford transport)

The transport core of the Clifford-adjoint irreducibility on `𝔰𝔲(8)`: a Clifford-conjugation-invariant
ℝ-submodule `W` that contains a *single* tensor-Pauli line `ℝ·(i·kronK8 v₀)` (for some `v₀ ≠ 0`) contains
*every* nonzero tensor-Pauli line. (Combined with `suEightTangent_spans` this gives `W = ⊤`, the heart of
irreducibility; see the companion increment.)

The argument promotes the nine single-generator line transports (`CliffordCCZSU8LineTransport`) to a full
orbit transport via the **symmetric reachability** of the Clifford label action:

  * `CliffordStep a b := ∃ g ∈ cliffordLabelGens, g a = b` — the one-step label relation.
  * Each `g ∈ cliffordLabelGens` is an **involution** (`cliffordLabelGens_involutive`, kernel `decide`),
    so `CliffordStep` is **symmetric** (`cliffordStep_symm`), hence so is `Relation.ReflTransGen CliffordStep`.
  * The Clifford label transitivity `clifford_label_transitive` (4f.1) gives, for every nonzero `v`,
    a reachability `ReflTransGen CliffordStep (X⊗I⊗I) v` (`nonzero_rtg`, via the orbit→`ReflTransGen`
    promotion `iterate_subset`).
  * Symmetry + transitivity connect any nonzero `v₀` to any nonzero `v`; the nine corollaries make the
    line-membership predicate `{v | i·kronK8 v ∈ W}` `CliffordStep`-forward-closed (`line_step_closed`),
    so a single line `v₀ ∈ W` propagates along `ReflTransGen` to all nonzero `v` (`all_lines_conj`).

The basepoint reverse-reachability is handled structurally (involution symmetry of `ReflTransGen`) rather
than by a 63-start `decide`, which would exceed the heartbeat budget (Pipeline Invariant #10 forbids
raising `maxHeartbeats` in proofs).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected (`maxRecDepth` in 4f.1 only; this module adds none).
  * **#15** (no new project-local axioms): respected. Kernel-pure.

## Phase 6z provenance

Phase 6z Wave 4 increment 4f.3b (one-line ⟹ all-lines Clifford transport). 2026-05-29.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8LineTransport

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix SKEFTHawking.FKLW.TrappedIonSU4 SKEFTHawking.FKLW.GenericSU2 Relation

/-! ## 1. The one-step Clifford label relation and its symmetry -/

/-- One-step Clifford label relation: `b` is a single Clifford-generator image of `a`. -/
def CliffordStep (a b : PauliLabel) : Prop := ∃ g ∈ cliffordLabelGens, g a = b

/-- Each of the nine Clifford label generators is an involution (kernel `decide`). -/
theorem cliffordLabelGens_involutive (g : PauliLabel → PauliLabel)
    (hg : g ∈ cliffordLabelGens) : Function.Involutive g := by
  simp only [cliffordLabelGens, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h|h <;> subst h <;> (unfold Function.Involutive; decide)

/-- `CliffordStep` is symmetric: generators are involutions, so `g a = b ⟹ g b = a`. -/
theorem cliffordStep_symm : Symmetric CliffordStep := by
  rintro a b ⟨g, hg, hgab⟩
  exact ⟨g, hg, by rw [← hgab, cliffordLabelGens_involutive g hg a]⟩

/-! ## 2. Promoting the `List`-orbit closure (4f.1) to `ReflTransGen` reachability -/

/-- One orbit-expansion step preserves "reachable-from-`base`": if every element of `S` is
`ReflTransGen CliffordStep`-reachable from `base`, so is every element of `cliffordLabelStep S`. -/
theorem step_preserves (base : PauliLabel) (S : List PauliLabel)
    (h : ∀ x ∈ S, ReflTransGen CliffordStep base x) :
    ∀ y ∈ cliffordLabelStep S, ReflTransGen CliffordStep base y := by
  intro y hy
  rw [cliffordLabelStep, List.mem_dedup, List.mem_append] at hy
  rcases hy with hyS | hyF
  · exact h y hyS
  · rw [List.mem_flatMap] at hyF
    obtain ⟨g, hg, hgy⟩ := hyF
    rw [List.mem_map] at hgy
    obtain ⟨x, hxS, hgx⟩ := hgy
    exact (h x hxS).tail ⟨g, hg, hgx⟩

/-- Every element of the `n`-step orbit of a `base`-reachable list is `base`-reachable. -/
theorem iterate_subset (base : PauliLabel) :
    ∀ (n : ℕ) (L : List PauliLabel), (∀ x ∈ L, ReflTransGen CliffordStep base x) →
      ∀ y ∈ cliffordLabelStep^[n] L, ReflTransGen CliffordStep base y := by
  intro n
  induction n with
  | zero => intro L hL y hy; simpa using hL y (by simpa using hy)
  | succ k ih =>
      intro L hL y hy
      rw [Function.iterate_succ_apply'] at hy
      exact step_preserves base _ (ih L hL) y hy

/-- **Every nonzero Pauli label is `ReflTransGen CliffordStep`-reachable from `X ⊗ I ⊗ I`.**
Promotes `clifford_label_transitive` (4f.1) to the `ReflTransGen` reachability relation. -/
theorem nonzero_rtg (v : PauliLabel) (hv : v ≠ 0) :
    ReflTransGen CliffordStep ((1, 0, 0) : PauliLabel) v :=
  iterate_subset ((1, 0, 0) : PauliLabel) 6 [((1, 0, 0) : PauliLabel)]
    (fun x hx => by rw [List.mem_singleton] at hx; subst hx; exact .refl)
    v (clifford_label_transitive v hv)

/-! ## 3. Line membership is closed along `ReflTransGen`, and one line gives all -/

/-- A `CliffordStep`-forward-closed line-membership predicate is closed along `ReflTransGen`. -/
theorem reflTransGen_line_closed
    (W : Submodule ℝ (Matrix (Fin 8) (Fin 8) ℂ))
    (hstep : ∀ a b : PauliLabel, CliffordStep a b →
      Complex.I • kronK8 a ∈ W → Complex.I • kronK8 b ∈ W)
    {v0 v : PauliLabel} (hrtg : ReflTransGen CliffordStep v0 v)
    (hmem : Complex.I • kronK8 v0 ∈ W) :
    Complex.I • kronK8 v ∈ W := by
  induction hrtg with
  | refl => exact hmem
  | tail _ hbc ih => exact hstep _ _ hbc ih

/-- **One line ⟹ all lines (abstract step form).** If `W`'s line-membership predicate is
`CliffordStep`-forward-closed and contains one nonzero line `v₀`, it contains every nonzero line. -/
theorem all_lines_of_one
    (W : Submodule ℝ (Matrix (Fin 8) (Fin 8) ℂ))
    (hstep : ∀ a b : PauliLabel, CliffordStep a b →
      Complex.I • kronK8 a ∈ W → Complex.I • kronK8 b ∈ W)
    {v0 : PauliLabel} (hv0 : v0 ≠ 0) (hmem : Complex.I • kronK8 v0 ∈ W) :
    ∀ v : PauliLabel, v ≠ 0 → Complex.I • kronK8 v ∈ W := by
  have hsymm : Symmetric (ReflTransGen CliffordStep) := ReflTransGen.symmetric cliffordStep_symm
  intro v hv
  exact reflTransGen_line_closed W hstep
    ((hsymm (nonzero_rtg v0 hv0)).trans (nonzero_rtg v hv)) hmem

/-! ## 4. The step-closure from the nine conjugation-closure hypotheses -/

/-- The line-membership predicate is `CliffordStep`-forward-closed, given `W` is conjugation-closed under
each of the nine Clifford generator matrices (the nine `line_transport_*` corollaries, dispatched per
generator). -/
theorem line_step_closed
    (W : Submodule ℝ (Matrix (Fin 8) (Fin 8) ℂ))
    (hH1 : ∀ Y ∈ W, (qubit1Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit1Embed H_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hH2 : ∀ Y ∈ W, (qubit2Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit2Embed H_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hH3 : ∀ Y ∈ W, (qubit3Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit3Embed H_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hS1 : ∀ Y ∈ W, (qubit1Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit1Embed S_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hS2 : ∀ Y ∈ W, (qubit2Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit2Embed S_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hS3 : ∀ Y ∈ W, (qubit3Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit3Embed S_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hC12 : ∀ Y ∈ W, CNOT_12_mat * Y * CNOT_12_mat⁻¹ ∈ W)
    (hC13 : ∀ Y ∈ W, CNOT_13_mat * Y * CNOT_13_mat⁻¹ ∈ W)
    (hC23 : ∀ Y ∈ W, CNOT_23_mat * Y * CNOT_23_mat⁻¹ ∈ W) :
    ∀ a b : PauliLabel, CliffordStep a b →
      Complex.I • kronK8 a ∈ W → Complex.I • kronK8 b ∈ W := by
  rintro a b ⟨g, hg, rfl⟩ hmem
  simp only [cliffordLabelGens, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h|h <;> subst h
  · exact line_transport_H_q1 W a hmem hH1
  · exact line_transport_H_q2 W a hmem hH2
  · exact line_transport_H_q3 W a hmem hH3
  · exact line_transport_S_q1 W a hmem hS1
  · exact line_transport_S_q2 W a hmem hS2
  · exact line_transport_S_q3 W a hmem hS3
  · exact line_transport_cnot_12 W a hmem hC12
  · exact line_transport_cnot_13 W a hmem hC13
  · exact line_transport_cnot_23 W a hmem hC23

/-- **One line ⟹ all lines (conjugation-closure form).** If `W` is conjugation-closed under all nine
Clifford generator matrices and contains a single nonzero tensor-Pauli line `i·kronK8 v₀`, then it
contains every nonzero tensor-Pauli line `i·kronK8 v`. Composes `line_step_closed` (step closure from the
nine generators) with `all_lines_of_one` (`ReflTransGen` propagation). -/
theorem all_lines_conj
    (W : Submodule ℝ (Matrix (Fin 8) (Fin 8) ℂ))
    (hH1 : ∀ Y ∈ W, (qubit1Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit1Embed H_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hH2 : ∀ Y ∈ W, (qubit2Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit2Embed H_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hH3 : ∀ Y ∈ W, (qubit3Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit3Embed H_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hS1 : ∀ Y ∈ W, (qubit1Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit1Embed S_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hS2 : ∀ Y ∈ W, (qubit2Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit2Embed S_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hS3 : ∀ Y ∈ W, (qubit3Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit3Embed S_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hC12 : ∀ Y ∈ W, CNOT_12_mat * Y * CNOT_12_mat⁻¹ ∈ W)
    (hC13 : ∀ Y ∈ W, CNOT_13_mat * Y * CNOT_13_mat⁻¹ ∈ W)
    (hC23 : ∀ Y ∈ W, CNOT_23_mat * Y * CNOT_23_mat⁻¹ ∈ W)
    {v0 : PauliLabel} (hv0 : v0 ≠ 0) (hmem : Complex.I • kronK8 v0 ∈ W) :
    ∀ v : PauliLabel, v ≠ 0 → Complex.I • kronK8 v ∈ W :=
  all_lines_of_one W
    (line_step_closed W hH1 hH2 hH3 hS1 hS2 hS3 hC12 hC13 hC23) hv0 hmem

end SKEFTHawking.FKLW.CliffordCCZSU8
