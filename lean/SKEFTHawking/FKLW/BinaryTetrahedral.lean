/-
Phase 6p Wave 2c.4a-R4.2.d.4.3.d.4 Wedge D session 1
(2026-05-20): Binary tetrahedral group 2T ⊆ SU(2) — first concrete
generator.

## Status

Wedge D of Phase 5 Step 13 Path (i) — binary polyhedral classification
for the finite-case branch of Cartan classification.

This file ships the **first concrete element of 2T**: the half-integer
unit quaternion `(1+i+j+k)/2`, which corresponds via the standard
quaternion → SU(2) isomorphism to:

  `!![(1+I)/2, (1+I)/2; (-1+I)/2, (1-I)/2]`

This element has order 6 in SU(2) (its cube is -I = negOneSU; sixth
power is 1).

## Shipped

§1 — `binaryTetrahedralGen : Matrix (Fin 2) (Fin 2) ℂ`:
  the concrete matrix `!![(1+I)/2, (1+I)/2; (-1+I)/2, (1-I)/2]`.

§2 — `binaryTetrahedralGen_mem_specialUnitaryGroup`:
  membership in SU(2), via unitarity + det = 1.

## Mathlib4 substrate consumed

  - `Matrix.specialUnitaryGroup`
  - `Matrix.mem_specialUnitaryGroup_iff`,
    `Matrix.mem_unitaryGroup_iff`
  - `Matrix.det_fin_two`, `Matrix.star_eq_conjTranspose`
-/

import Mathlib

set_option autoImplicit false

namespace SKEFTHawking.FKLW

open Matrix Complex

/-! ## §1. The binary tetrahedral generator -/

/-- **`(1+i+j+k)/2` as an SU(2) matrix**.

The standard quaternion → SU(2) isomorphism maps `a + b·i + c·j + d·k`
to `!![a + bI, c + dI; -c + dI, a - bI]`. With `a = b = c = d = 1/2`,
this gives `!![(1+I)/2, (1+I)/2; (-1+I)/2, (1-I)/2]`.

This is an order-6 element of the binary tetrahedral group 2T ⊆ SU(2). -/
noncomputable def binaryTetrahedralGen : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 + Complex.I) / 2, (1 + Complex.I) / 2;
     (-1 + Complex.I) / 2, (1 - Complex.I) / 2]

/-! ## §2. SU(2) membership -/

/-- `star binaryTetrahedralGen = !![(1-I)/2, (-1-I)/2; (1-I)/2, (1+I)/2]`. -/
private theorem star_binaryTetrahedralGen :
    star binaryTetrahedralGen =
      !![(1 - Complex.I) / 2, (-1 - Complex.I) / 2;
         (1 - Complex.I) / 2, (1 + Complex.I) / 2] := by
  rw [Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryTetrahedralGen, Matrix.conjTranspose_apply,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.empty_val',
          Matrix.cons_val_fin_one, Complex.div_I, Complex.conj_I,
          map_div₀, map_add, map_sub, map_neg, map_one, Complex.conj_I]
  all_goals ring_nf

/-- `binaryTetrahedralGen * star binaryTetrahedralGen = 1`. -/
private theorem binaryTetrahedralGen_mul_star :
    binaryTetrahedralGen * star binaryTetrahedralGen = 1 := by
  rw [star_binaryTetrahedralGen]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryTetrahedralGen, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.empty_val',
          Matrix.cons_val_fin_one, Matrix.one_apply]
  all_goals ring_nf
  all_goals
    first
      | (rw [show Complex.I^2 = -1 by simp [Complex.I_sq]]; ring)
      | rfl

/-- `det binaryTetrahedralGen = 1`. -/
private theorem binaryTetrahedralGen_det :
    binaryTetrahedralGen.det = 1 := by
  rw [Matrix.det_fin_two]
  simp [binaryTetrahedralGen, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons,
        Matrix.empty_val', Matrix.cons_val_fin_one]
  ring_nf
  rw [show Complex.I^2 = -1 by simp [Complex.I_sq]]
  ring

/-- **`binaryTetrahedralGen ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ`** —
SU(2) membership. -/
theorem binaryTetrahedralGen_mem_specialUnitaryGroup :
    binaryTetrahedralGen ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  Matrix.mem_specialUnitaryGroup_iff.mpr
    ⟨Matrix.mem_unitaryGroup_iff.mpr binaryTetrahedralGen_mul_star,
     binaryTetrahedralGen_det⟩

/-! ## §3. Order-6 element verification: cube = -I -/

/-- **`binaryTetrahedralGen ^ 3 = -1`** — the half-integer quaternion
has order 6.

For the unit quaternion `q = (1+i+j+k)/2`, we have `q² = (-1+i+j+k)/2`
and `q³ = -1`. This makes `q` an order-6 element. Verified at the
matrix level via direct multiplication. -/
theorem binaryTetrahedralGen_cube :
    binaryTetrahedralGen * binaryTetrahedralGen * binaryTetrahedralGen =
      -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryTetrahedralGen, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.empty_val',
          Matrix.cons_val_fin_one, Matrix.neg_apply, Matrix.one_apply]
  all_goals ring_nf
  all_goals
    rw [show Complex.I^3 = -Complex.I from by
      rw [pow_succ, Complex.I_sq]; ring]
  all_goals ring_nf
  all_goals (rw [Complex.I_sq]; ring)

/-- **`binaryTetrahedralGen^6 = 1`** — sixth power is identity.

Direct corollary: `gen^6 = (gen^3)² = (-I)² = I`. -/
theorem binaryTetrahedralGen_sixth :
    binaryTetrahedralGen ^ 6 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h_cube_eq :
      binaryTetrahedralGen * binaryTetrahedralGen * binaryTetrahedralGen =
      -(1 : Matrix (Fin 2) (Fin 2) ℂ) := binaryTetrahedralGen_cube
  -- gen^6 = (gen^3)^2 = (gen·gen·gen)·(gen·gen·gen) = (-1)·(-1) = 1.
  have h_pow3 : binaryTetrahedralGen ^ 3 =
                binaryTetrahedralGen * binaryTetrahedralGen * binaryTetrahedralGen := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_succ, pow_one]
  have h_pow6 : binaryTetrahedralGen ^ 6 =
                (binaryTetrahedralGen * binaryTetrahedralGen * binaryTetrahedralGen) *
                (binaryTetrahedralGen * binaryTetrahedralGen * binaryTetrahedralGen) := by
    rw [show (6 : ℕ) = 3 + 3 from rfl, pow_add, h_pow3]
  rw [h_pow6, h_cube_eq]
  -- Now goal: (-1) * (-1) = 1 (matrix level).
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply,
          Matrix.one_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
          Matrix.cons_val_fin_one]

/-! ## §4. Bundled SU(2) subtype version -/

/-- The bundled SU(2) subtype version of `binaryTetrahedralGen`. -/
noncomputable def binaryTetrahedralElem :
    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  ⟨binaryTetrahedralGen, binaryTetrahedralGen_mem_specialUnitaryGroup⟩

/-- `binaryTetrahedralElem.val = binaryTetrahedralGen`. -/
@[simp] theorem binaryTetrahedralElem_val :
    (binaryTetrahedralElem : Matrix (Fin 2) (Fin 2) ℂ) =
    binaryTetrahedralGen := rfl

/-- `(binaryTetrahedralElem^6).val = 1` — sixth power is identity at
the matrix level, via subtype-power expansion + session-102 result. -/
theorem binaryTetrahedralElem_sixth_val :
    ((binaryTetrahedralElem ^ 6 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) =
    (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  -- Subtype.val is multiplicative; (g^6).val = g.val^6.
  show binaryTetrahedralGen ^ 6 = 1
  exact binaryTetrahedralGen_sixth

end SKEFTHawking.FKLW
