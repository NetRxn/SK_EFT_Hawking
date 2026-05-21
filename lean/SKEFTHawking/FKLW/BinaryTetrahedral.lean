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
import SKEFTHawking.FKLW.StandardTorusSU2

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

/-- `binaryTetrahedralElem^6 = 1` at the subtype level. -/
theorem binaryTetrahedralElem_sixth :
    binaryTetrahedralElem ^ 6 = 1 := by
  apply Subtype.ext
  exact binaryTetrahedralElem_sixth_val

/-- **`binaryTetrahedralElem` has finite order**, with order ≤ 6. -/
theorem binaryTetrahedralElem_isOfFinOrder :
    IsOfFinOrder binaryTetrahedralElem :=
  isOfFinOrder_iff_pow_eq_one.mpr
    ⟨6, by norm_num, binaryTetrahedralElem_sixth⟩

/-- `orderOf binaryTetrahedralElem ≤ 6`. -/
theorem binaryTetrahedralElem_orderOf_le_six :
    orderOf binaryTetrahedralElem ≤ 6 :=
  orderOf_le_of_pow_eq_one (by norm_num) binaryTetrahedralElem_sixth

/-! ## §5a. Cyclic subgroup generated by binaryTetrahedralElem -/

/-- **`Subgroup.zpowers binaryTetrahedralElem`** — the cyclic subgroup
generated by the half-integer quaternion generator.

Contains the 6 powers: `1, gen, gen², gen³ = -I, gen⁴, gen⁵`.
This is the smallest abelian subgroup of 2T containing `gen`. -/
noncomputable def binaryTetrahedralCyclic :
    Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  Subgroup.zpowers binaryTetrahedralElem

/-- `binaryTetrahedralElem ∈ binaryTetrahedralCyclic` (trivially). -/
theorem binaryTetrahedralElem_mem_cyclic :
    binaryTetrahedralElem ∈ binaryTetrahedralCyclic :=
  Subgroup.mem_zpowers _

/-- `Nat.card binaryTetrahedralCyclic ≤ 6` — cardinality bounded by
the order of the generator. -/
theorem binaryTetrahedralCyclic_card_le_six :
    Nat.card binaryTetrahedralCyclic ≤ 6 := by
  show Nat.card ↥(Subgroup.zpowers binaryTetrahedralElem) ≤ 6
  rw [Nat.card_zpowers]
  exact binaryTetrahedralElem_orderOf_le_six

/-! ## §5b. Full 2T as Subgroup.closure -/

/-- **`binaryTetrahedralFull`** — the full binary tetrahedral group 2T ⊆ SU(2)
defined as the closure of three explicit generators:
  - `binaryTetrahedralElem` (half-integer quaternion (1+i+j+k)/2, order 6),
  - `weylElem` (the j-quaternion `!![0,1;-1,0]`, order 4),
  - `torusElem (π/2)` (the i-quaternion `diag(I, -I)`, order 4).

These three generate the full 2T subgroup of order 24 — substantive
verification of `Nat.card binaryTetrahedralFull = 24` is deferred to
future sessions.

Strategic value: provides a concrete reference point for the
binary-polyhedral classification + composes with shipped
`H_Fib_card_ge_200_if_finite` to rule out H_Fib ≅ 2T (since 24 < 200). -/
noncomputable def binaryTetrahedralFull :
    Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  Subgroup.closure
    ({binaryTetrahedralElem, weylElem, torusElem (Real.pi / 2)} :
      Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))

/-- `binaryTetrahedralCyclic ≤ binaryTetrahedralFull` — the cyclic
subgroup is contained in the full 2T. -/
theorem binaryTetrahedralCyclic_le_full :
    binaryTetrahedralCyclic ≤ binaryTetrahedralFull := by
  -- binaryTetrahedralCyclic = zpowers gen; gen ∈ closure {gen, ...}; so zpowers ⊆ closure.
  unfold binaryTetrahedralCyclic
  rw [Subgroup.zpowers_le]
  exact Subgroup.subset_closure (by simp)

/-- `binaryTetrahedralElem ∈ binaryTetrahedralFull`. -/
theorem binaryTetrahedralElem_mem_full :
    binaryTetrahedralElem ∈ binaryTetrahedralFull :=
  Subgroup.subset_closure (by simp)

/-- `weylElem ∈ binaryTetrahedralFull`. -/
theorem weylElem_mem_binaryTetrahedralFull :
    weylElem ∈ binaryTetrahedralFull :=
  Subgroup.subset_closure (by simp)

/-- `torusElem (π/2) ∈ binaryTetrahedralFull`. -/
theorem torusElem_pi_half_mem_binaryTetrahedralFull :
    torusElem (Real.pi / 2) ∈ binaryTetrahedralFull :=
  Subgroup.subset_closure (by simp)

/-- `negOneSU ∈ binaryTetrahedralFull` — the SU(2) element `-I` is in
2T. Via `weylElem ∈ 2T` and `weylElem² = negOneSU` (session 90). -/
theorem negOneSU_mem_binaryTetrahedralFull :
    negOneSU ∈ binaryTetrahedralFull := by
  rw [← weylElem_sq_eq_negOneSU]
  exact binaryTetrahedralFull.mul_mem
    weylElem_mem_binaryTetrahedralFull
    weylElem_mem_binaryTetrahedralFull

/-- `weylElem ≠ 1` — the Weyl element is not the identity (via [0,1] entries). -/
theorem weylElem_ne_one :
    weylElem ≠ (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  intro h_eq
  have h_val := congrArg Subtype.val h_eq
  have h_01 := congrArg (fun M => M 0 1) h_val
  simp [weylMatrix, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.one_apply] at h_01

/-- `torusElem (π/2) ≠ 1` — the i-quaternion is not the identity
(via [0,0] entry: exp(iπ/2) = I ≠ 1). -/
theorem torusElem_pi_half_ne_one :
    torusElem (Real.pi / 2) ≠
    (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  intro h_eq
  have h_val : (torusElem (Real.pi / 2)).val =
               (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    have := congrArg Subtype.val h_eq
    exact this
  have h_00 : (torusElem (Real.pi / 2)).val 0 0 =
              (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 :=
    congrArg (fun M => M 0 0) h_val
  -- LHS = exp(iπ/2) = I; RHS = 1. Compare via .im.
  have h_lhs : (torusElem (Real.pi / 2)).val 0 0 = Complex.I := by
    show torusMatrix (Real.pi / 2) 0 0 = Complex.I
    have h_simp : torusMatrix (Real.pi / 2) 0 0 =
                  Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
      simp [torusMatrix, Matrix.cons_val', Matrix.cons_val_zero,
            Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [h_simp,
        show (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) =
             (↑Real.pi / 2 * Complex.I) by push_cast; ring,
        Complex.exp_pi_div_two_mul_I]
  rw [h_lhs] at h_00
  simp [Matrix.one_apply] at h_00
  have h_im := congrArg Complex.im h_00
  simp [Complex.I_im] at h_im

/-- `binaryTetrahedralFull` is non-trivial (contains weylElem ≠ 1). -/
theorem binaryTetrahedralFull_ne_bot :
    binaryTetrahedralFull ≠ ⊥ := by
  intro h_eq
  -- If 2T = ⊥, then every element is 1. weylElem ∈ 2T but weylElem ≠ 1.
  have h_weyl_mem : weylElem ∈ binaryTetrahedralFull :=
    weylElem_mem_binaryTetrahedralFull
  rw [h_eq, Subgroup.mem_bot] at h_weyl_mem
  -- h_weyl_mem : weylElem = 1, contradicting weylElem ≠ 1 (since weyl² = negOneSU ≠ 1).
  have h_sq : weylElem * weylElem = (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
    rw [h_weyl_mem, one_mul]
  rw [weylElem_sq_eq_negOneSU] at h_sq
  -- h_sq : negOneSU = 1. Contradiction via .val 0 0 = -1 vs 1.
  have h_val := congrArg Subtype.val h_sq
  have h_00 := congrArg (fun M => M 0 0) h_val
  simp [negOneSU_val, Matrix.neg_apply, Matrix.one_apply] at h_00
  exact absurd h_00 (by norm_num)

/-- **2T is non-abelian**: the i-quaternion `torusElem(π/2)` and the
j-quaternion `weylElem` do NOT commute (`ij = -ji = k` in quaternions). -/
theorem binaryTetrahedralFull_non_abelian :
    ∃ g h, g ∈ binaryTetrahedralFull ∧ h ∈ binaryTetrahedralFull ∧
      g * h ≠ h * g := by
  refine ⟨torusElem (Real.pi / 2), weylElem,
          torusElem_pi_half_mem_binaryTetrahedralFull,
          weylElem_mem_binaryTetrahedralFull, ?_⟩
  intro h_comm
  -- Project to [0,1] entry: should differ (I vs -I).
  have h_val :
      (torusElem (Real.pi / 2) * weylElem :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val =
      (weylElem * torusElem (Real.pi / 2) :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val :=
    congrArg Subtype.val h_comm
  have h_01 : (torusMatrix (Real.pi / 2) * weylMatrix) 0 1 =
              (weylMatrix * torusMatrix (Real.pi / 2)) 0 1 :=
    congrArg (fun M => M 0 1) h_val
  -- LHS [0,1] = exp(iπ/2) · weylMatrix[0,1] + 0 · weylMatrix[1,1] = I · 1 = I.
  -- RHS [0,1] = weylMatrix[0,0] · 0 + weylMatrix[0,1] · exp(-iπ/2) = 0 + 1 · (-I) = -I.
  have h_exp_neg : Complex.exp (-((Real.pi : ℂ) / 2 * Complex.I)) = -Complex.I := by
    have := Complex.exp_neg_pi_div_two_mul_I
    convert this using 2
    ring
  simp [torusMatrix, weylMatrix, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one,
        show ((Real.pi / 2 : ℝ) : ℂ) * Complex.I =
             (Real.pi : ℂ) / 2 * Complex.I by push_cast; ring,
        show -(((Real.pi / 2 : ℝ) : ℂ) * Complex.I) =
             -((Real.pi : ℂ) / 2 * Complex.I) by push_cast; ring,
        Complex.exp_pi_div_two_mul_I, h_exp_neg] at h_01
  -- h_01 : I = -I, contradiction via .im.
  have h_im := congrArg Complex.im h_01
  simp [Complex.I_im, Complex.neg_im] at h_im
  linarith

/-! ## §5. binaryTetrahedralElem is NOT in stdTorus_SU2 -/

/-- **`binaryTetrahedralElem ∉ stdTorus_SU2`** — 2T contains elements
outside the standard torus.

The half-integer quaternion has off-diagonal entry `(1+I)/2 ≠ 0`, but
every element of `stdTorus_SU2` is `torusElem t = diag(exp(it), exp(-it))`
with off-diagonal entries = 0. Contradiction.

This shows 2T strictly extends `stdTorus_SU2` (within SU(2)). -/
theorem binaryTetrahedralElem_not_mem_stdTorus :
    binaryTetrahedralElem ∉ stdTorus_SU2 := by
  intro h_mem
  obtain ⟨t, ht⟩ := h_mem
  -- ht : torusElem t = binaryTetrahedralElem
  -- Project to [0,1] entry: should be 0 (torus) but is (1+I)/2 (2T gen).
  have h_val : (torusElem t).val = binaryTetrahedralElem.val :=
    congrArg Subtype.val ht
  have h_01 : torusMatrix t 0 1 = binaryTetrahedralGen 0 1 :=
    congrArg (fun M => M 0 1) h_val
  -- LHS [0,1] = 0; RHS [0,1] = (1+I)/2.
  simp [torusMatrix, binaryTetrahedralGen, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.empty_val',
        Matrix.cons_val_fin_one] at h_01
  -- Show (1+I)/2 ≠ 0 (i.e., 1+I ≠ 0).
  have h_oneAddI_ne : (1 + Complex.I : ℂ) ≠ 0 := by
    intro h
    have h_re := congrArg Complex.re h
    simp [Complex.add_re, Complex.one_re, Complex.I_re] at h_re
  have h_div_ne : ((1 + Complex.I) / 2 : ℂ) ≠ 0 :=
    div_ne_zero h_oneAddI_ne (by norm_num)
  exact h_div_ne h_01.symm

end SKEFTHawking.FKLW
