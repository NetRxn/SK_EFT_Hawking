/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6z Wave 4 increment 4f.2b (part 1) — permutation-matrix conjugation as a submatrix reindex

The CNOT generators are permutation matrices (`CNOT_{ct}_mat = Equiv.Perm.permMatrix ℂ σ_cnot`), so their
conjugation action on the tensor-Paulis is a **reindexing**. This module ships the general fact

  `permMatrix σ · M · permMatrix σ⁻¹ = M.submatrix σ σ`  (i.e. `(…) i j = M (σ i) (σ j)`),

the reusable first step of the CNOT tableau lift `CNOT · kronK8 v · CNOT⁻¹ = ± kronK8 (cnotLabel v)`.
(The remaining step — identifying the reindexed `kronK8 v` with the CNOT-transformed tensor-Pauli via the
3-bit index decomposition — is the companion increment.) Clean general lemma, Mathlib-PR-quality.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected. Kernel-pure.

## Phase 6z provenance

Phase 6z Wave 4 increment 4f.2b part 1 (permMatrix conjugation reindex). 2026-05-29.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8TangentSpan
import SKEFTHawking.FKLW.CliffordCCZSU8CNOT
import SKEFTHawking.FKLW.CliffordCCZSU8LabelTransitivity

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix SKEFTHawking.FKLW.TrappedIonSU4

/-- **Conjugation by a permutation matrix is a submatrix reindex**: for any permutation `σ` of a finite
type and any square matrix `M`, `permMatrix σ · M · permMatrix σ⁻¹ = M.submatrix σ σ`, i.e. entrywise
`(permMatrix σ · M · permMatrix σ⁻¹) i j = M (σ i) (σ j)`.

This is the structural form of the CNOT (and any permutation-gate) conjugation action: conjugating a
matrix by a permutation matrix permutes its rows and columns by `σ`. -/
theorem permMatrix_conj_eq_submatrix {n : Type*} [Fintype n] [DecidableEq n]
    (σ : Equiv.Perm n) (M : Matrix n n ℂ) :
    Equiv.Perm.permMatrix ℂ σ * M * Equiv.Perm.permMatrix ℂ σ⁻¹ = M.submatrix σ σ := by
  ext i j
  simp only [Matrix.mul_apply, Equiv.Perm.permMatrix, Equiv.toPEquiv_apply, PEquiv.toMatrix_apply,
    Matrix.submatrix_apply, Option.mem_some_iff, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [Equiv.Perm.inv_def, Equiv.symm_apply_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-! ## 2. The 3-qubit bit-iso and `kronK8` bit-entry / CNOT bit-actions

The CNOT conjugation reindexes `kronK8 v` by `σ_cnot`, which acts on `Fin 8` by permuting the 3-qubit
bit decomposition. This section sets up the bit-iso `Fin 2 × Fin 2 × Fin 2 ≃ Fin 8` (matching the
`kronSU8 = kronSU2SU4 ∘ kronSU4` Kronecker structure), the entrywise formula for `kronK8` in those bits,
and the per-CNOT bit-action (each flips the target bit iff the control bit is set). -/

/-- The 3-qubit bit isomorphism `Fin 2 × Fin 2 × Fin 2 ≃ Fin 8` matching `kronSU8`'s nested-Kronecker
index structure: `(q₁, q₂, q₃) ↦ finProdFinEquiv (q₁, finProdFinEquiv (q₂, q₃))`. -/
def bitIso8 : Fin 2 × Fin 2 × Fin 2 ≃ Fin 8 :=
  ((Equiv.refl (Fin 2)).prodCongr finProdFinEquiv).trans finProdFinEquiv

/-- **`kronK8` bit-entry formula**: at bit-decomposed indices, the tensor-Pauli matrix factors as the
product of the three single-qubit Pauli entries. -/
theorem kronK8_bitIso8_apply (v : Fin 4 × Fin 4 × Fin 4) (i j : Fin 2 × Fin 2 × Fin 2) :
    kronK8 v (bitIso8 i) (bitIso8 j)
      = pauli4 v.1 i.1 j.1 * pauli4 v.2.1 i.2.1 j.2.1 * pauli4 v.2.2 i.2.2 j.2.2 := by
  unfold kronK8 kronSU8 kronSU2SU4 kronSU4 bitIso8
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map, id_eq,
    Matrix.kronecker, Matrix.kroneckerMap_apply]
  ring

/-- **CNOT₁₂ bit-action**: flips bit 2 iff bit 1 is set. -/
theorem cnot12_bitIso8 (b : Fin 2 × Fin 2 × Fin 2) :
    σ_cnot_12 (bitIso8 b) = bitIso8 (b.1, b.1 + b.2.1, b.2.2) := by
  obtain ⟨b1, b2, b3⟩ := b; fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;> decide

/-- **CNOT₁₃ bit-action**: flips bit 3 iff bit 1 is set. -/
theorem cnot13_bitIso8 (b : Fin 2 × Fin 2 × Fin 2) :
    σ_cnot_13 (bitIso8 b) = bitIso8 (b.1, b.2.1, b.1 + b.2.2) := by
  obtain ⟨b1, b2, b3⟩ := b; fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;> decide

/-- **CNOT₂₃ bit-action**: flips bit 3 iff bit 2 is set. -/
theorem cnot23_bitIso8 (b : Fin 2 × Fin 2 × Fin 2) :
    σ_cnot_23 (bitIso8 b) = bitIso8 (b.1, b.2.1, b.2.1 + b.2.2) := by
  obtain ⟨b1, b2, b3⟩ := b; fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;> decide

/-! ## 3. The 2-qubit CNOT Pauli tableau (entrywise, with sign)

The single entrywise identity behind every CNOT tableau lift: conjugating the control-target Pauli pair
by a CNOT (whose bit-action flips the target bit by the control bit, `(i₁,i₂) ↦ (i₁, i₁+i₂)`) gives, up to
a sign `cnotSign ∈ {±1}`, the symplectically-transformed Pauli pair `cnotLabelPair`. The sign is `−1`
exactly on `(X,Z)` and `(Y,Y)` (where the conjugation picks up `i² = −1` via `Y = iXZ`), `+1` otherwise.
The same 2-qubit identity serves all three `CNOT_{12,13,23}` lifts (applied to the relevant qubit pair,
the third a spectator). -/

/-- The CNOT-conjugation sign on a control-target Pauli pair: `−1` exactly on `(X,Z)` and `(Y,Y)`. -/
noncomputable def cnotSign (v1 v2 : Fin 4) : ℂ :=
  if (v1 = 1 ∧ v2 = 3) ∨ (v1 = 2 ∧ v2 = 2) then -1 else 1

/-- **2-qubit CNOT Pauli tableau (entrywise)**: `(σ_{v₁})_{i₁j₁} (σ_{v₂})_{(i₁+i₂)(j₁+j₂)}
= cnotSign v₁ v₂ · (σ_{v₁'})_{i₁j₁} (σ_{v₂'})_{i₂j₂}` where `(v₁',v₂') = cnotLabelPair v₁ v₂`.

Proved by the 16-case Pauli table (`fin_cases v₁ v₂`), reducing `cnotLabelPair v₁ v₂` to its concrete
value once per case (via `decide`, selected by `first` over the 16 targets) so the bit-leaves are cheap
entrywise computations — kernel-pure, within default heartbeats (no `maxHeartbeats`). -/
theorem cnot_tableau (v1 v2 : Fin 4) : ∀ i1 i2 j1 j2 : Fin 2,
    pauli4 v1 i1 j1 * pauli4 v2 (i1 + i2) (j1 + j2)
      = cnotSign v1 v2 * (pauli4 (cnotLabelPair v1 v2).1 i1 j1 * pauli4 (cnotLabelPair v1 v2).2 i2 j2) := by
  fin_cases v1 <;> fin_cases v2 <;>
    (first
      | rw [show cnotLabelPair _ _ = ((0:Fin 4), (0:Fin 4)) from by decide]
      | rw [show cnotLabelPair _ _ = ((0:Fin 4), (1:Fin 4)) from by decide]
      | rw [show cnotLabelPair _ _ = ((3:Fin 4), (2:Fin 4)) from by decide]
      | rw [show cnotLabelPair _ _ = ((3:Fin 4), (3:Fin 4)) from by decide]
      | rw [show cnotLabelPair _ _ = ((1:Fin 4), (1:Fin 4)) from by decide]
      | rw [show cnotLabelPair _ _ = ((1:Fin 4), (0:Fin 4)) from by decide]
      | rw [show cnotLabelPair _ _ = ((2:Fin 4), (3:Fin 4)) from by decide]
      | rw [show cnotLabelPair _ _ = ((2:Fin 4), (2:Fin 4)) from by decide]
      | rw [show cnotLabelPair _ _ = ((2:Fin 4), (1:Fin 4)) from by decide]
      | rw [show cnotLabelPair _ _ = ((2:Fin 4), (0:Fin 4)) from by decide]
      | rw [show cnotLabelPair _ _ = ((1:Fin 4), (3:Fin 4)) from by decide]
      | rw [show cnotLabelPair _ _ = ((1:Fin 4), (2:Fin 4)) from by decide]
      | rw [show cnotLabelPair _ _ = ((3:Fin 4), (0:Fin 4)) from by decide]
      | rw [show cnotLabelPair _ _ = ((3:Fin 4), (1:Fin 4)) from by decide]
      | rw [show cnotLabelPair _ _ = ((0:Fin 4), (2:Fin 4)) from by decide]
      | rw [show cnotLabelPair _ _ = ((0:Fin 4), (3:Fin 4)) from by decide]) <;>
    (simp only [cnotSign] ; intro i1 i2 j1 j2 ;
     fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
       simp [pauli4, SKEFTHawking.σ_x, SKEFTHawking.σ_y, SKEFTHawking.σ_z, Matrix.one_apply])

/-! ## 4. The three CNOT tableau lifts (matrix conjugation = sign • transformed tensor-Pauli)

Assembling §1–§3: `permMatrix σ_cnot · kronK8 v · permMatrix σ_cnot⁻¹ = cnotSign • kronK8 (cnotLabel v)`.
The proof reindexes (§1), evaluates at the bit-iso (`bitIso8.surjective`), applies the CNOT bit-action
(§2) and the `kronK8` bit-entry (§2), and closes with the 2-qubit tableau (§3) — the spectator qubit's
Pauli factor cancels (handled by `linear_combination` weighting / `ring`). Each `CNOT_{ct}` acts on its
control-target qubit pair; the third qubit is the spectator. -/

/-- **CNOT₁₂ tableau lift**: `permMatrix σ_cnot_12 · kronK8 v · permMatrix σ_cnot_12⁻¹
= cnotSign v.1 v.2.1 • kronK8 (cnotLabel 0 1 v)`. -/
theorem cnot12_kronK8_conj (v : Fin 4 × Fin 4 × Fin 4) :
    Equiv.Perm.permMatrix ℂ σ_cnot_12 * kronK8 v * Equiv.Perm.permMatrix ℂ σ_cnot_12⁻¹
      = cnotSign v.1 v.2.1 • kronK8 (cnotLabel 0 1 v) := by
  rw [permMatrix_conj_eq_submatrix]
  ext a b
  obtain ⟨i, rfl⟩ := bitIso8.surjective a
  obtain ⟨j, rfl⟩ := bitIso8.surjective b
  obtain ⟨v1, v2, v3⟩ := v
  rw [Matrix.submatrix_apply, cnot12_bitIso8, cnot12_bitIso8, kronK8_bitIso8_apply,
      Matrix.smul_apply, smul_eq_mul,
      show cnotLabel 0 1 (v1, v2, v3) = ((cnotLabelPair v1 v2).1, (cnotLabelPair v1 v2).2, v3) from rfl,
      kronK8_bitIso8_apply]
  linear_combination (pauli4 v3 i.2.2 j.2.2) * cnot_tableau v1 v2 i.1 i.2.1 j.1 j.2.1

/-- **CNOT₁₃ tableau lift**: `permMatrix σ_cnot_13 · kronK8 v · permMatrix σ_cnot_13⁻¹
= cnotSign v.1 v.2.2 • kronK8 (cnotLabel 0 2 v)`. -/
theorem cnot13_kronK8_conj (v : Fin 4 × Fin 4 × Fin 4) :
    Equiv.Perm.permMatrix ℂ σ_cnot_13 * kronK8 v * Equiv.Perm.permMatrix ℂ σ_cnot_13⁻¹
      = cnotSign v.1 v.2.2 • kronK8 (cnotLabel 0 2 v) := by
  rw [permMatrix_conj_eq_submatrix]
  ext a b
  obtain ⟨i, rfl⟩ := bitIso8.surjective a
  obtain ⟨j, rfl⟩ := bitIso8.surjective b
  obtain ⟨v1, v2, v3⟩ := v
  rw [Matrix.submatrix_apply, cnot13_bitIso8, cnot13_bitIso8, kronK8_bitIso8_apply,
      Matrix.smul_apply, smul_eq_mul,
      show cnotLabel 0 2 (v1, v2, v3) = ((cnotLabelPair v1 v3).1, v2, (cnotLabelPair v1 v3).2) from rfl,
      kronK8_bitIso8_apply]
  linear_combination (pauli4 v2 i.2.1 j.2.1) * cnot_tableau v1 v3 i.1 i.2.2 j.1 j.2.2

/-- **CNOT₂₃ tableau lift**: `permMatrix σ_cnot_23 · kronK8 v · permMatrix σ_cnot_23⁻¹
= cnotSign v.2.1 v.2.2 • kronK8 (cnotLabel 1 2 v)`. -/
theorem cnot23_kronK8_conj (v : Fin 4 × Fin 4 × Fin 4) :
    Equiv.Perm.permMatrix ℂ σ_cnot_23 * kronK8 v * Equiv.Perm.permMatrix ℂ σ_cnot_23⁻¹
      = cnotSign v.2.1 v.2.2 • kronK8 (cnotLabel 1 2 v) := by
  rw [permMatrix_conj_eq_submatrix]
  ext a b
  obtain ⟨i, rfl⟩ := bitIso8.surjective a
  obtain ⟨j, rfl⟩ := bitIso8.surjective b
  obtain ⟨v1, v2, v3⟩ := v
  rw [Matrix.submatrix_apply, cnot23_bitIso8, cnot23_bitIso8, kronK8_bitIso8_apply,
      Matrix.smul_apply, smul_eq_mul,
      show cnotLabel 1 2 (v1, v2, v3) = (v1, (cnotLabelPair v2 v3).1, (cnotLabelPair v2 v3).2) from rfl,
      kronK8_bitIso8_apply]
  linear_combination (pauli4 v1 i.1 j.1) * cnot_tableau v2 v3 i.2.1 i.2.2 j.2.1 j.2.2

end SKEFTHawking.FKLW.CliffordCCZSU8
