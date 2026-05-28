/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A2′.2 (D) witness — the 54 entangling tangent flow lines

The `hX_flow` field of the SU(8) `ClosureDenseWitness` needs flow lines for the 54 entangling
tensor-Pauli tangents `X_{abc}` with ≥ 2 nonzero factors (27 two-qubit + 27 three-qubit). These are
reached from the 9 single-qubit flows (`CliffordCCZSU8PerQubitFlow`) by **conjugation transport**
(`GenericSUd.flow_conj_mem`), in two layers:

  * **CNOT base entanglers** — conjugating a single-qubit `σ_x` flow by `CNOT_{ij} ∈ H_of_G` spreads
    it to an all-`σ_x` entangler on the pair/triple (`cnot12_conj_X1` etc., shipped in
    `CliffordCCZSU8EntanglerSpread`). Gives the 4 base flows `X_{110}, X_{101}, X_{011}, X_{111}`.
  * **Per-qubit Clifford rotation** — conjugating an all-`σ_x` flow by `qubit_iEmbed C ∈ H_of_G`
    (`C` a single-qubit Clifford rotating `σ_x ↦ ±σ_a`) rotates the qubit-`i` factor
    (`qubit_iEmbed_conj`, `CliffordCCZSU8FactorConj`), reaching every `X_{abc}` in the pattern, with a
    sign absorbed by `t ↦ ±t` reparametrisation.

This mirrors the SU(4) `TrappedIonSU4EntanglerSpread` methodology (`entangling_flow_of_conj`) scaled
from 9 entanglers to 54. **Trotter is NOT used** — the flows come from the Phase 6u Clifford+T
per-qubit density (via `T`) spread by conjugation, the lighter route validated for the SU(4) ship.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A2′ provenance

Phase 6y Roadmap §"Track T-A2′ detail" sub-wave T-A2′.2 PROPER — (D) witness 54 entangling flows.
2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8EntanglerSpread
import SKEFTHawking.FKLW.CliffordCCZSU8FactorConj
import SKEFTHawking.FKLW.CliffordCCZSU8PerQubitFlow
import SKEFTHawking.FKLW.CliffordCCZSU8PerQubitContainment
import SKEFTHawking.FKLW.TrappedIonSU4EntanglerSpread
import SKEFTHawking.FKLW.GenericSUdFlowConj

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix Complex SKEFTHawking.FKLW.GenericSUd SKEFTHawking.FKLW.TrappedIonSU4

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. The CNOT generators lie in `H_of_G` (tokens 6, 7, 8) -/

theorem CNOT_12_SU8_mem_H_of_G : CNOT_12_SU8 ∈ H_of_G cliffordCCZGeneratingSetSU8 := by
  have h := H_of_G_ρ_mem cliffordCCZGeneratingSetSU8 (FreeGroup.of (6 : Fin 10))
  rwa [show cliffordCCZGeneratingSetSU8.ρ_hom (FreeGroup.of (6 : Fin 10)) = CNOT_12_SU8 from
    FreeGroup.lift_apply_of] at h

theorem CNOT_13_SU8_mem_H_of_G : CNOT_13_SU8 ∈ H_of_G cliffordCCZGeneratingSetSU8 := by
  have h := H_of_G_ρ_mem cliffordCCZGeneratingSetSU8 (FreeGroup.of (7 : Fin 10))
  rwa [show cliffordCCZGeneratingSetSU8.ρ_hom (FreeGroup.of (7 : Fin 10)) = CNOT_13_SU8 from
    FreeGroup.lift_apply_of] at h

theorem CNOT_23_SU8_mem_H_of_G : CNOT_23_SU8 ∈ H_of_G cliffordCCZGeneratingSetSU8 := by
  have h := H_of_G_ρ_mem cliffordCCZGeneratingSetSU8 (FreeGroup.of (8 : Fin 10))
  rwa [show cliffordCCZGeneratingSetSU8.ρ_hom (FreeGroup.of (8 : Fin 10)) = CNOT_23_SU8 from
    FreeGroup.lift_apply_of] at h

/-! ## 2. The 4 all-`σ_x` base entangler flows (from per-qubit flows + CNOT conjugation) -/

/-- Conjugation pulls a scalar out: `R · (c • M) · R⁻¹ = c • (R · M · R⁻¹)`. -/
private theorem conj_smul (R : Matrix (Fin 8) (Fin 8) ℂ) (c : ℂ) (M : Matrix (Fin 8) (Fin 8) ℂ) :
    R * (c • M) * R⁻¹ = c • (R * M * R⁻¹) := by
  rw [mul_smul_comm, smul_mul_assoc]

/-- **Base pair-(1,2) entangler** `X_{110} = (i/2)·σ_x⊗σ_x⊗I`: flow via `CNOT₁₂`-conjugation of the
qubit-1 `σ_x` flow. -/
theorem suEightTangentAux_X110_flow (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
      M ∈ H_of_G cliffordCCZGeneratingSetSU8 ∧
      (M : Matrix (Fin 8) (Fin 8) ℂ) =
        NormedSpace.exp (((t : ℝ) : ℂ) • suEightTangentAux 1 1 0) := by
  obtain ⟨M, hM, hval⟩ := flow_conj_mem (H_of_G cliffordCCZGeneratingSetSU8) CNOT_12_SU8
    CNOT_12_SU8_mem_H_of_G (suEightTangentAux_qubit1_flow 1 (by decide)) t
  refine ⟨M, hM, ?_⟩
  rw [hval]; congr 2
  show CNOT_12_mat * suEightTangentAux 1 0 0 * CNOT_12_mat⁻¹ = suEightTangentAux 1 1 0
  unfold suEightTangentAux
  rw [conj_smul]
  congr 1
  exact cnot12_conj_X1

/-- **Base pair-(1,3) entangler** `X_{101} = (i/2)·σ_x⊗I⊗σ_x`. -/
theorem suEightTangentAux_X101_flow (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
      M ∈ H_of_G cliffordCCZGeneratingSetSU8 ∧
      (M : Matrix (Fin 8) (Fin 8) ℂ) =
        NormedSpace.exp (((t : ℝ) : ℂ) • suEightTangentAux 1 0 1) := by
  obtain ⟨M, hM, hval⟩ := flow_conj_mem (H_of_G cliffordCCZGeneratingSetSU8) CNOT_13_SU8
    CNOT_13_SU8_mem_H_of_G (suEightTangentAux_qubit1_flow 1 (by decide)) t
  refine ⟨M, hM, ?_⟩
  rw [hval]; congr 2
  show CNOT_13_mat * suEightTangentAux 1 0 0 * CNOT_13_mat⁻¹ = suEightTangentAux 1 0 1
  unfold suEightTangentAux
  rw [conj_smul]
  congr 1
  exact cnot13_conj_X1

/-- **Base pair-(2,3) entangler** `X_{011} = (i/2)·I⊗σ_x⊗σ_x`. -/
theorem suEightTangentAux_X011_flow (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
      M ∈ H_of_G cliffordCCZGeneratingSetSU8 ∧
      (M : Matrix (Fin 8) (Fin 8) ℂ) =
        NormedSpace.exp (((t : ℝ) : ℂ) • suEightTangentAux 0 1 1) := by
  obtain ⟨M, hM, hval⟩ := flow_conj_mem (H_of_G cliffordCCZGeneratingSetSU8) CNOT_23_SU8
    CNOT_23_SU8_mem_H_of_G (suEightTangentAux_qubit2_flow 1 (by decide)) t
  refine ⟨M, hM, ?_⟩
  rw [hval]; congr 2
  show CNOT_23_mat * suEightTangentAux 0 1 0 * CNOT_23_mat⁻¹ = suEightTangentAux 0 1 1
  unfold suEightTangentAux
  rw [conj_smul]
  congr 1
  exact cnot23_conj_X2

/-- **Base 3-qubit entangler** `X_{111} = (i/2)·σ_x⊗σ_x⊗σ_x`: flow via `CNOT₂₃`-conjugation of the
base pair-(1,2) flow `X_{110}`. -/
theorem suEightTangentAux_X111_flow (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
      M ∈ H_of_G cliffordCCZGeneratingSetSU8 ∧
      (M : Matrix (Fin 8) (Fin 8) ℂ) =
        NormedSpace.exp (((t : ℝ) : ℂ) • suEightTangentAux 1 1 1) := by
  obtain ⟨M, hM, hval⟩ := flow_conj_mem (H_of_G cliffordCCZGeneratingSetSU8) CNOT_23_SU8
    CNOT_23_SU8_mem_H_of_G (suEightTangentAux_X110_flow) t
  refine ⟨M, hM, ?_⟩
  rw [hval]; congr 2
  show CNOT_23_mat * suEightTangentAux 1 1 0 * CNOT_23_mat⁻¹ = suEightTangentAux 1 1 1
  unfold suEightTangentAux
  rw [conj_smul]
  congr 1
  exact cnot23_conj_X1X2

/-! ## 3. Per-qubit Clifford rotation transports a tangent flow to a rotated slot -/

/-- **Qubit-1 rotation transport**: if `C ∈ SU(2)` rotates `σ_p ↦ s·σ_a` and `X_{pqr}` has a flow,
then `s·X_{aqr}` has a flow (conjugate by `qubit1Embed C ∈ H_of_G`). -/
theorem qubit1_conj_tangent_flow (C : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (p q r a : Fin 4) (s : ℂ)
    (hC : (C : Matrix (Fin 2) (Fin 2) ℂ) * pauli4 p * (C : Matrix (Fin 2) (Fin 2) ℂ)⁻¹
        = s • pauli4 a)
    (hflow : ∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
        M ∈ H_of_G cliffordCCZGeneratingSetSU8 ∧
        (M : Matrix (Fin 8) (Fin 8) ℂ) = NormedSpace.exp (((t : ℝ) : ℂ) • suEightTangentAux p q r))
    (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
      M ∈ H_of_G cliffordCCZGeneratingSetSU8 ∧
      (M : Matrix (Fin 8) (Fin 8) ℂ) =
        NormedSpace.exp (((t : ℝ) : ℂ) • (s • suEightTangentAux a q r)) := by
  obtain ⟨M, hM, hval⟩ := flow_conj_mem (H_of_G cliffordCCZGeneratingSetSU8) (qubit1Embed C)
    (qubit1Embed_mem_H_of_G C) hflow t
  refine ⟨M, hM, ?_⟩
  rw [hval]; congr 2
  unfold suEightTangentAux
  rw [conj_smul, qubit1Embed_conj, hC]
  unfold kronSU8
  rw [kronSU2SU4_smul_left, smul_comm]

/-- **Qubit-2 rotation transport**: rotates the middle factor `σ_q ↦ s·σ_b`. -/
theorem qubit2_conj_tangent_flow (C : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (p q r b : Fin 4) (s : ℂ)
    (hC : (C : Matrix (Fin 2) (Fin 2) ℂ) * pauli4 q * (C : Matrix (Fin 2) (Fin 2) ℂ)⁻¹
        = s • pauli4 b)
    (hflow : ∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
        M ∈ H_of_G cliffordCCZGeneratingSetSU8 ∧
        (M : Matrix (Fin 8) (Fin 8) ℂ) = NormedSpace.exp (((t : ℝ) : ℂ) • suEightTangentAux p q r))
    (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
      M ∈ H_of_G cliffordCCZGeneratingSetSU8 ∧
      (M : Matrix (Fin 8) (Fin 8) ℂ) =
        NormedSpace.exp (((t : ℝ) : ℂ) • (s • suEightTangentAux p b r)) := by
  obtain ⟨M, hM, hval⟩ := flow_conj_mem (H_of_G cliffordCCZGeneratingSetSU8) (qubit2Embed C)
    (qubit2Embed_mem_H_of_G C) hflow t
  refine ⟨M, hM, ?_⟩
  rw [hval]; congr 2
  unfold suEightTangentAux
  rw [conj_smul, qubit2Embed_conj, hC]
  unfold kronSU8
  rw [kronSU4_smul_left, kronSU2SU4_smul_right, smul_comm]

/-- **Qubit-3 rotation transport**: rotates the last factor `σ_r ↦ s·σ_c`. -/
theorem qubit3_conj_tangent_flow (C : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (p q r c : Fin 4) (s : ℂ)
    (hC : (C : Matrix (Fin 2) (Fin 2) ℂ) * pauli4 r * (C : Matrix (Fin 2) (Fin 2) ℂ)⁻¹
        = s • pauli4 c)
    (hflow : ∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
        M ∈ H_of_G cliffordCCZGeneratingSetSU8 ∧
        (M : Matrix (Fin 8) (Fin 8) ℂ) = NormedSpace.exp (((t : ℝ) : ℂ) • suEightTangentAux p q r))
    (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
      M ∈ H_of_G cliffordCCZGeneratingSetSU8 ∧
      (M : Matrix (Fin 8) (Fin 8) ℂ) =
        NormedSpace.exp (((t : ℝ) : ℂ) • (s • suEightTangentAux p q c)) := by
  obtain ⟨M, hM, hval⟩ := flow_conj_mem (H_of_G cliffordCCZGeneratingSetSU8) (qubit3Embed C)
    (qubit3Embed_mem_H_of_G C) hflow t
  refine ⟨M, hM, ?_⟩
  rw [hval]; congr 2
  unfold suEightTangentAux
  rw [conj_smul, qubit3Embed_conj, hC]
  unfold kronSU8
  rw [kronSU4_smul_right, kronSU2SU4_smul_right, smul_comm]

/-! ## 4. The single-qubit Clifford that rotates `σ_x ↦ ±σ_a` (reused from SU(4)) -/

/-- The single-qubit Clifford rotating `σ_x ↦ ±σ_a`: identity for `a ∈ {0,1}` (`σ_x ↦ σ_x`),
`C_{σz}` for `a = 2` (`σ_x ↦ σ_y`), `C_{σy}` for `a = 3` (`σ_x ↦ −σ_z`). -/
noncomputable def cliffX : Fin 4 → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)
  | 2 => cliffordSU2 SKEFTHawking.σ_z SKEFTHawking.σ_z_hermitian SKEFTHawking.σ_z_trace
  | 3 => cliffordSU2 SKEFTHawking.σ_y σ_y_isHermitian SKEFTHawking.σ_y_trace
  | _ => 1

/-- The accompanying sign: `+1` for `a ∈ {0,1,2}`, `−1` for `a = 3`. -/
def signX : Fin 4 → ℂ
  | 3 => -1
  | _ => 1

/-- **`cliffX a` rotates `σ_x ↦ signX a · σ_a`** for `a ≠ 0`. -/
theorem cliffX_conj (a : Fin 4) (ha : a ≠ 0) :
    (cliffX a : Matrix (Fin 2) (Fin 2) ℂ) * pauli4 1 *
        (cliffX a : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ = signX a • pauli4 a := by
  fin_cases a
  · exact absurd rfl ha
  · exact one_conj_σx_p
  · exact clifford_σz_conj_σx_p
  · exact clifford_σy_conj_σx_p

theorem signX_eq (a : Fin 4) : signX a = 1 ∨ signX a = -1 := by
  fin_cases a <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem mul_pm_one {x y : ℂ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
    x * y = 1 ∨ x * y = -1 := by
  rcases hx with h | h <;> rcases hy with h' | h' <;> rw [h, h']
  · left; ring
  · right; ring
  · right; ring
  · left; ring

/-! ## 5. Scalar-carrying rotation transports (for chaining ≥ 2 slot rotations) + sign drop -/

/-- Matrix identity behind the qubit-2 rotation transport. -/
theorem qubit2_conj_tangent_eq (C : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (p q r b : Fin 4)
    (s : ℂ) (hC : (C : Matrix (Fin 2) (Fin 2) ℂ) * pauli4 q * (C : Matrix (Fin 2) (Fin 2) ℂ)⁻¹
        = s • pauli4 b) :
    (qubit2Embed C : Matrix (Fin 8) (Fin 8) ℂ) * suEightTangentAux p q r *
        ((qubit2Embed C : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :
          Matrix (Fin 8) (Fin 8) ℂ)⁻¹ = s • suEightTangentAux p b r := by
  unfold suEightTangentAux
  rw [conj_smul, qubit2Embed_conj, hC]
  unfold kronSU8
  rw [kronSU4_smul_left, kronSU2SU4_smul_right, smul_comm]

/-- Matrix identity behind the qubit-3 rotation transport. -/
theorem qubit3_conj_tangent_eq (C : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (p q r c : Fin 4)
    (s : ℂ) (hC : (C : Matrix (Fin 2) (Fin 2) ℂ) * pauli4 r * (C : Matrix (Fin 2) (Fin 2) ℂ)⁻¹
        = s • pauli4 c) :
    (qubit3Embed C : Matrix (Fin 8) (Fin 8) ℂ) * suEightTangentAux p q r *
        ((qubit3Embed C : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :
          Matrix (Fin 8) (Fin 8) ℂ)⁻¹ = s • suEightTangentAux p q c := by
  unfold suEightTangentAux
  rw [conj_smul, qubit3Embed_conj, hC]
  unfold kronSU8
  rw [kronSU4_smul_right, kronSU2SU4_smul_right, smul_comm]

/-- **Qubit-2 scalar-carrying rotation**: `e·X_{pqr}` flow ↦ `(e·s)·X_{pbr}` flow. -/
theorem qubit2_conj_flow_scaled (C : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (p q r b : Fin 4)
    (e s : ℂ) (hC : (C : Matrix (Fin 2) (Fin 2) ℂ) * pauli4 q * (C : Matrix (Fin 2) (Fin 2) ℂ)⁻¹
        = s • pauli4 b)
    (hflow : ∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
        M ∈ H_of_G cliffordCCZGeneratingSetSU8 ∧
        (M : Matrix (Fin 8) (Fin 8) ℂ) =
          NormedSpace.exp (((t : ℝ) : ℂ) • (e • suEightTangentAux p q r)))
    (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
      M ∈ H_of_G cliffordCCZGeneratingSetSU8 ∧
      (M : Matrix (Fin 8) (Fin 8) ℂ) =
        NormedSpace.exp (((t : ℝ) : ℂ) • ((e * s) • suEightTangentAux p b r)) := by
  obtain ⟨M, hM, hval⟩ := flow_conj_mem (H_of_G cliffordCCZGeneratingSetSU8) (qubit2Embed C)
    (qubit2Embed_mem_H_of_G C) hflow t
  refine ⟨M, hM, ?_⟩
  rw [hval]; congr 2
  rw [conj_smul, qubit2_conj_tangent_eq C p q r b s hC, smul_smul]

/-- **Qubit-3 scalar-carrying rotation**: `e·X_{pqr}` flow ↦ `(e·s)·X_{pqc}` flow. -/
theorem qubit3_conj_flow_scaled (C : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (p q r c : Fin 4)
    (e s : ℂ) (hC : (C : Matrix (Fin 2) (Fin 2) ℂ) * pauli4 r * (C : Matrix (Fin 2) (Fin 2) ℂ)⁻¹
        = s • pauli4 c)
    (hflow : ∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
        M ∈ H_of_G cliffordCCZGeneratingSetSU8 ∧
        (M : Matrix (Fin 8) (Fin 8) ℂ) =
          NormedSpace.exp (((t : ℝ) : ℂ) • (e • suEightTangentAux p q r)))
    (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
      M ∈ H_of_G cliffordCCZGeneratingSetSU8 ∧
      (M : Matrix (Fin 8) (Fin 8) ℂ) =
        NormedSpace.exp (((t : ℝ) : ℂ) • ((e * s) • suEightTangentAux p q c)) := by
  obtain ⟨M, hM, hval⟩ := flow_conj_mem (H_of_G cliffordCCZGeneratingSetSU8) (qubit3Embed C)
    (qubit3Embed_mem_H_of_G C) hflow t
  refine ⟨M, hM, ?_⟩
  rw [hval]; congr 2
  rw [conj_smul, qubit3_conj_tangent_eq C p q r c s hC, smul_smul]

/-- **Sign drop**: a flow for `s·X` with `s = ±1` gives a flow for `X` (reparametrise `t ↦ ±t`). -/
theorem flow_drop_sign (s : ℂ) (hs : s = 1 ∨ s = -1) (X : Matrix (Fin 8) (Fin 8) ℂ)
    (hflow : ∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
        M ∈ H_of_G cliffordCCZGeneratingSetSU8 ∧
        (M : Matrix (Fin 8) (Fin 8) ℂ) = NormedSpace.exp (((t : ℝ) : ℂ) • (s • X)))
    (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
      M ∈ H_of_G cliffordCCZGeneratingSetSU8 ∧
      (M : Matrix (Fin 8) (Fin 8) ℂ) = NormedSpace.exp (((t : ℝ) : ℂ) • X) := by
  rcases hs with h | h
  · obtain ⟨M, hM, hv⟩ := hflow t
    exact ⟨M, hM, by rw [hv, h, one_smul]⟩
  · obtain ⟨M, hM, hv⟩ := hflow (-t)
    refine ⟨M, hM, ?_⟩
    rw [hv, h, smul_smul, show ((-t : ℝ) : ℂ) * (-1) = ((t : ℝ) : ℂ) from by push_cast; ring]

/-! ## 6. The 54 entangling flows (4 parametric patterns) + the full 63-tangent flow -/

/-- **Pair-(1,2) entangling flows**: `exp(t·X_{ab0}) ∈ H_of_G` for `a, b ≠ 0`. -/
theorem suEightTangentAux_pair12_flow (a b : Fin 4) (ha : a ≠ 0) (hb : b ≠ 0) (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
      M ∈ H_of_G cliffordCCZGeneratingSetSU8 ∧
      (M : Matrix (Fin 8) (Fin 8) ℂ) = NormedSpace.exp (((t : ℝ) : ℂ) • suEightTangentAux a b 0) :=
  flow_drop_sign (signX a * signX b) (mul_pm_one (signX_eq a) (signX_eq b))
    (suEightTangentAux a b 0)
    (qubit2_conj_flow_scaled (cliffX b) a 1 0 b (signX a) (signX b) (cliffX_conj b hb)
      (qubit1_conj_tangent_flow (cliffX a) 1 1 0 a (signX a) (cliffX_conj a ha)
        suEightTangentAux_X110_flow))
    t

/-- **Pair-(1,3) entangling flows**: `exp(t·X_{a0c}) ∈ H_of_G` for `a, c ≠ 0`. -/
theorem suEightTangentAux_pair13_flow (a c : Fin 4) (ha : a ≠ 0) (hc : c ≠ 0) (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
      M ∈ H_of_G cliffordCCZGeneratingSetSU8 ∧
      (M : Matrix (Fin 8) (Fin 8) ℂ) = NormedSpace.exp (((t : ℝ) : ℂ) • suEightTangentAux a 0 c) :=
  flow_drop_sign (signX a * signX c) (mul_pm_one (signX_eq a) (signX_eq c))
    (suEightTangentAux a 0 c)
    (qubit3_conj_flow_scaled (cliffX c) a 0 1 c (signX a) (signX c) (cliffX_conj c hc)
      (qubit1_conj_tangent_flow (cliffX a) 1 0 1 a (signX a) (cliffX_conj a ha)
        suEightTangentAux_X101_flow))
    t

/-- **Pair-(2,3) entangling flows**: `exp(t·X_{0bc}) ∈ H_of_G` for `b, c ≠ 0`. -/
theorem suEightTangentAux_pair23_flow (b c : Fin 4) (hb : b ≠ 0) (hc : c ≠ 0) (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
      M ∈ H_of_G cliffordCCZGeneratingSetSU8 ∧
      (M : Matrix (Fin 8) (Fin 8) ℂ) = NormedSpace.exp (((t : ℝ) : ℂ) • suEightTangentAux 0 b c) :=
  flow_drop_sign (signX b * signX c) (mul_pm_one (signX_eq b) (signX_eq c))
    (suEightTangentAux 0 b c)
    (qubit3_conj_flow_scaled (cliffX c) 0 b 1 c (signX b) (signX c) (cliffX_conj c hc)
      (qubit2_conj_tangent_flow (cliffX b) 0 1 1 b (signX b) (cliffX_conj b hb)
        suEightTangentAux_X011_flow))
    t

/-- **Three-qubit entangling flows**: `exp(t·X_{abc}) ∈ H_of_G` for `a, b, c ≠ 0`. -/
theorem suEightTangentAux_triple_flow (a b c : Fin 4) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
      M ∈ H_of_G cliffordCCZGeneratingSetSU8 ∧
      (M : Matrix (Fin 8) (Fin 8) ℂ) = NormedSpace.exp (((t : ℝ) : ℂ) • suEightTangentAux a b c) :=
  flow_drop_sign (signX a * signX b * signX c)
    (mul_pm_one (mul_pm_one (signX_eq a) (signX_eq b)) (signX_eq c))
    (suEightTangentAux a b c)
    (qubit3_conj_flow_scaled (cliffX c) a b 1 c (signX a * signX b) (signX c) (cliffX_conj c hc)
      (qubit2_conj_flow_scaled (cliffX b) a 1 1 b (signX a) (signX b) (cliffX_conj b hb)
        (qubit1_conj_tangent_flow (cliffX a) 1 1 1 a (signX a) (cliffX_conj a ha)
          suEightTangentAux_X111_flow)))
    t

/-- **Every tensor-Pauli tangent's flow line lies in `H_of_G`** (for `(a,b,c) ≠ (0,0,0)`): single
nonzero factor → per-qubit flow (`CliffordCCZSU8PerQubitFlow`); ≥ 2 nonzero → entangling spread. -/
theorem suEightTangentAux_flow (a b c : Fin 4) (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
      M ∈ H_of_G cliffordCCZGeneratingSetSU8 ∧
      (M : Matrix (Fin 8) (Fin 8) ℂ) = NormedSpace.exp (((t : ℝ) : ℂ) • suEightTangentAux a b c) := by
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases hc : c = 0
  · subst ha hb hc; simp at h
  · subst ha hb; exact suEightTangentAux_qubit3_flow c hc t
  · subst ha hc; exact suEightTangentAux_qubit2_flow b hb t
  · subst ha; exact suEightTangentAux_pair23_flow b c hb hc t
  · subst hb hc; exact suEightTangentAux_qubit1_flow a ha t
  · subst hb; exact suEightTangentAux_pair13_flow a c ha hc t
  · subst hc; exact suEightTangentAux_pair12_flow a b ha hb t
  · exact suEightTangentAux_triple_flow a b c ha hb hc t

/-- **`hX_flow` for the SU(8) witness**: every one of the 63 tensor-Pauli tangents has its
one-parameter flow line in `H_of_G cliffordCCZGeneratingSetSU8`. -/
theorem suEightTangent_flow (j : Fin 63) (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
      M ∈ H_of_G cliffordCCZGeneratingSetSU8 ∧
      (M : Matrix (Fin 8) (Fin 8) ℂ) = NormedSpace.exp (((t : ℝ) : ℂ) • suEightTangent j) :=
  suEightTangentAux_flow (idx63 j).1 (idx63 j).2.1 (idx63 j).2.2 (idx63_ne_zero j) t

end SKEFTHawking.FKLW.CliffordCCZSU8
