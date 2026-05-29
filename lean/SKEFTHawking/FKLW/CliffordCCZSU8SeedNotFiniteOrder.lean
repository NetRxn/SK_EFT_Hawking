/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6z Wave 1 — the seed group element is of infinite order

The faithful literal Clifford+CCZ density needs a continuous one-parameter subgroup in the closure of
`⟨H, S, CNOT, CCZ⟩`. Since every generator is finite-order, the first flow is seeded by an
**infinite-order** group element. This module exhibits that seed and proves it has infinite order.

The seed word is `g_lit = CCZ · H_q1 · H_q2 · H_q3` in the literal alphabet (the SU(8)-normalized
version of `litSeed = CCZ_mat · (H⊗H⊗H)`). The SU(2)-normalized generators carry phases
(`H_SU = i·H_raw`, `CCZ_SU = ccz_phase·CCZ_mat` with `ccz_phase` a 16-th root of unity), so as a matrix

  `g_lit.val = (ccz_phase · (−i)) • litSeed`,   `tr(g_lit) = (ccz_phase · (−i)) · (1/√2)`.

The phase `u := ccz_phase·(−i)` is a 16-th root of unity (hence an algebraic integer with integral
inverse), and `1/√2` is not an algebraic integer, so `tr(g_lit)` is **not** an algebraic integer
(`not_isIntegral_mul_left` + `not_isIntegral_inv_sqrt_two`). A finite-order matrix has an
algebraic-integer trace (`trace_isIntegral_of_pow_eq_one`), so `g_lit` is of **infinite order** — the
Kronecker seed for the Wave-2 flow. (DR2's "phase preservation": the central root-of-unity phase `u`
cannot rescue finite order.)

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6z provenance

Phase 6z Wave 1 — seed not finite order (Substrate_Inventory B2). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8LiteralSeed
import SKEFTHawking.FKLW.CliffordCCZSU8LiteralGeneratingSet
import SKEFTHawking.FKLW.CliffordCCZSU8Irrationality
import SKEFTHawking.FKLW.CliffordCCZSU8QubitEmbed
import SKEFTHawking.FKLW.CliffordCCZSU8PerQubitFlow
import SKEFTHawking.FKLW.CliffordCCZSU8TangentSpan
import SKEFTHawking.FKLW.CCZ_SU

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix SKEFTHawking.FKLW.CCZSUExtension

/-! ## 1. Matrix-bridge helpers -/

/-- `H_SU.val = i • H_raw` (the SU(2)-corrected Hadamard is `i` times the textbook one). -/
theorem H_SU_val_eq_smul_litHadamard :
    (SKEFTHawking.FKLW.GenericSU2.H_SU : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val
      = Complex.I • litHadamard := by
  show SKEFTHawking.FKLW.GenericSU2.H_SU_mat = Complex.I • litHadamard
  rw [SKEFTHawking.FKLW.GenericSU2.H_SU_mat, litHadamard, smul_smul]
  congr 1
  ring

/-- `kronSU8` is homogeneous of degree 3 under a common scalar: `(c•A)⊗(c•B)⊗(c•C) = c³·(A⊗B⊗C)`. -/
theorem kronSU8_smul_cube (c : ℂ) (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    kronSU8 (c • A) (c • B) (c • C) = c ^ 3 • kronSU8 A B C := by
  unfold kronSU8
  simp only [TrappedIonSU4.kronSU4_smul_left, TrappedIonSU4.kronSU4_smul_right,
    kronSU2SU4_smul_left, kronSU2SU4_smul_right, smul_smul]
  congr 1
  ring

/-- `qubit1Embed A = A ⊗ I ⊗ I = kronSU8 A 1 1`. -/
theorem qubit1Embed_val (A : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    (qubit1Embed A).val = kronSU8 A.val 1 1 := by
  show kronSU2SU4 A.val 1 = kronSU8 A.val 1 1
  unfold kronSU8
  rw [TrappedIonSU4.kronSU4_one]

/-- `qubit2Embed B = I ⊗ B ⊗ I = kronSU8 1 B 1`. -/
theorem qubit2Embed_val (B : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    (qubit2Embed B).val = kronSU8 1 B.val 1 := rfl

/-- `qubit3Embed C = I ⊗ I ⊗ C = kronSU8 1 1 C`. -/
theorem qubit3Embed_val (C : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    (qubit3Embed C).val = kronSU8 1 1 C.val := by
  show kronSU4SU2 1 C.val = kronSU8 1 1 C.val
  unfold kronSU8
  rw [kronSU2SU4_one_kronSU4_one]

/-- The product of the three per-qubit embeddings is the full Kronecker product. -/
theorem embed_triple_product (A B C : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    (qubit1Embed A).val * ((qubit2Embed B).val * (qubit3Embed C).val)
      = kronSU8 A.val B.val C.val := by
  rw [qubit1Embed_val, qubit2Embed_val, qubit3Embed_val, ← kronSU8_mul, ← kronSU8_mul]
  simp only [mul_one, one_mul]

/-! ## 2. The seed element and the phase bridge -/

/-- The seed word in the literal alphabet: `CCZ · H_q1 · H_q2 · H_q3` (tokens `9·0·1·2`). -/
noncomputable def seedWord : FreeGroup (Fin 10) :=
  FreeGroup.of 9 * FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 2

/-- **The seed group element** `g_lit ∈ ⟨H,S,CNOT,CCZ⟩ ⊆ SU(8)`. -/
noncomputable def seedSU8 : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ) :=
  cliffordCCZLiteralRho seedWord

/-- `g_lit` is in the closure subgroup `H_of_G` (it is `ρ` of a word). -/
theorem seedSU8_mem :
    seedSU8 ∈ SKEFTHawking.FKLW.GenericSUd.H_of_G cliffordCCZLiteralGeneratingSetSU8 :=
  SKEFTHawking.FKLW.GenericSUd.H_of_G_ρ_mem cliffordCCZLiteralGeneratingSetSU8 seedWord

/-- `g_lit` as a product of the four generator images. -/
theorem seedSU8_eq_prod :
    seedSU8 = CCZ_SU_subtype * H_SU_on_qubit1_SU8 * H_SU_on_qubit2_SU8 * H_SU_on_qubit3_SU8 := by
  unfold seedSU8 seedWord cliffordCCZLiteralRho
  rw [map_mul, map_mul, map_mul, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of,
    FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
  rfl

/-- The seed phase `u = ccz_phase · (−i)` — a 16-th root of unity. -/
noncomputable def seedPhase : ℂ := ccz_phase * (-Complex.I)

/-- **The matrix bridge**: `g_lit.val = u • litSeed`. -/
theorem seedSU8_val_eq : seedSU8.val = seedPhase • litSeed := by
  rw [seedSU8_eq_prod, H_SU_on_qubit1_SU8_eq_embed, H_SU_on_qubit2_SU8_eq_embed,
    H_SU_on_qubit3_SU8_eq_embed, MulMemClass.coe_mul, MulMemClass.coe_mul, MulMemClass.coe_mul,
    show (CCZ_SU_subtype : Matrix (Fin 8) (Fin 8) ℂ) = CCZ_SU from rfl,
    mul_assoc, mul_assoc, embed_triple_product, H_SU_val_eq_smul_litHadamard,
    kronSU8_smul_cube, CCZ_SU, litSeed, seedPhase, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  congr 1
  rw [show (Complex.I) ^ 3 = -Complex.I from by rw [pow_succ, Complex.I_sq]; ring]
  ring

/-! ## 3. The seed has infinite order -/

/-- `u` is a 16-th root of unity: `u¹⁶ = 1`. -/
theorem seedPhase_pow_sixteen : seedPhase ^ 16 = 1 := by
  rw [seedPhase, mul_pow]
  rw [show (16 : ℕ) = 8 * 2 by norm_num, pow_mul, ccz_phase_pow_eight]
  rw [show ((-Complex.I) ^ (8 * 2)) = ((-Complex.I) ^ 2) ^ 8 by rw [← pow_mul, Nat.mul_comm]]
  rw [show (-Complex.I) ^ 2 = -1 from by rw [neg_sq, Complex.I_sq]]
  norm_num

/-- `u ≠ 0`. -/
theorem seedPhase_ne_zero : seedPhase ≠ 0 := by
  intro h
  have := seedPhase_pow_sixteen
  rw [h] at this
  simp at this

/-- **`tr(g_lit)` is not an algebraic integer**: it equals `u · (1/√2)` with `u` a root of unity and
`1/√2` not an algebraic integer. -/
theorem seedSU8_trace_not_isIntegral : ¬ IsIntegral ℤ seedSU8.val.trace := by
  rw [seedSU8_val_eq, Matrix.trace_smul, litSeed_trace, smul_eq_mul]
  refine not_isIntegral_mul_left ?_ seedPhase_ne_zero not_isIntegral_inv_sqrt_two
  exact isIntegral_of_pow_eq_one (n := 16) (by norm_num)
    (by rw [inv_pow, seedPhase_pow_sixteen, inv_one])

/-- **The seed matrix has infinite order**: `g_lit.valⁿ ≠ 1` for every `0 < n`. A finite-order matrix
has an algebraic-integer trace (`trace_isIntegral_of_pow_eq_one`), but `tr(g_lit)` is not one. -/
theorem seedSU8_val_pow_ne_one (n : ℕ) (hn : 0 < n) : seedSU8.val ^ n ≠ 1 := by
  intro h
  exact seedSU8_trace_not_isIntegral (trace_isIntegral_of_pow_eq_one seedSU8.val hn h)

/-- **The seed group element has infinite order**: `g_litⁿ ≠ 1` for every `0 < n`. -/
theorem seedSU8_pow_ne_one (n : ℕ) (hn : 0 < n) : seedSU8 ^ n ≠ 1 := by
  intro h
  refine seedSU8_val_pow_ne_one n hn ?_
  rw [← SubmonoidClass.coe_pow, h, OneMemClass.coe_one]

end SKEFTHawking.FKLW.CliffordCCZSU8
