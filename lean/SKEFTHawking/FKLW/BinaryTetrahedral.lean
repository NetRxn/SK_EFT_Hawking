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

/-- **`binaryTetrahedralElem ^ 3 = negOneSU`** — the cube of the
half-integer quaternion generator is `-I` at the subtype level.

Subtype-power dispatch + `binaryTetrahedralGen_cube` (matrix-level
`gen * gen * gen = -1`). -/
theorem binaryTetrahedralElem_cube :
    binaryTetrahedralElem ^ 3 = negOneSU := by
  apply Subtype.ext
  show binaryTetrahedralGen ^ 3 = (negOneSU : Matrix (Fin 2) (Fin 2) ℂ)
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_succ, pow_one]
  rw [show binaryTetrahedralGen * binaryTetrahedralGen * binaryTetrahedralGen =
       -(1 : Matrix (Fin 2) (Fin 2) ℂ) from binaryTetrahedralGen_cube]
  rw [negOneSU_val]


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

/-- `Subgroup.zpowers weylElem ≤ binaryTetrahedralFull` — the Weyl-cyclic
subgroup (the 4-element ⟨w⟩ generated by the j-quaternion) is contained
in 2T. -/
theorem weylElem_zpowers_le_binaryTetrahedralFull :
    Subgroup.zpowers weylElem ≤ binaryTetrahedralFull := by
  rw [Subgroup.zpowers_le]
  exact Subgroup.subset_closure (by simp)

/-- `Subgroup.zpowers (torusElem (π/2)) ≤ binaryTetrahedralFull` — the
i-quaternion cyclic subgroup (4 elements) is contained in 2T. -/
theorem torusElem_pi_half_zpowers_le_binaryTetrahedralFull :
    Subgroup.zpowers (torusElem (Real.pi / 2)) ≤ binaryTetrahedralFull := by
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

/-- `torusElem (π/2) ∈ Subgroup.normalizer stdTorus_SU2` — every torus
element is in the normalizer of T (trivially, since T ⊆ N(T)). -/
theorem torusElem_pi_half_mem_normalizer :
    torusElem (Real.pi / 2) ∈ Subgroup.normalizer stdTorus_SU2 :=
  Subgroup.le_normalizer ⟨Real.pi / 2, rfl⟩

/-- `torusElem (π/2)² = negOneSU` — the i-quaternion squares to -I.

Composes torusElem_add + torusElem_pi_eq_negOneSU. -/
theorem torusElem_pi_half_sq :
    torusElem (Real.pi / 2) * torusElem (Real.pi / 2) = negOneSU := by
  rw [← torusElem_add]
  have h_sum : Real.pi / 2 + Real.pi / 2 = Real.pi := by ring
  rw [h_sum, torusElem_pi_eq_negOneSU]

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

/-- `negOneSU ∈ Subgroup.normalizer stdTorus_SU2` — trivially, since
`negOneSU ∈ stdTorus_SU2` and every subgroup is in its own normalizer. -/
theorem negOneSU_mem_normalizer_stdTorus :
    negOneSU ∈ Subgroup.normalizer stdTorus_SU2 :=
  Subgroup.le_normalizer negOneSU_mem_stdTorus_SU2

/-- `negOneSU` commutes with every SU(2) element (it is central). -/
theorem negOneSU_mem_center :
    ∀ g : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
      negOneSU * g = g * negOneSU := by
  intro g
  apply Subtype.ext
  show (-(1 : Matrix (Fin 2) (Fin 2) ℂ)) * g.val =
       g.val * (-(1 : Matrix (Fin 2) (Fin 2) ℂ))
  noncomm_ring

/-- `negOneSU * weylElem = weylElem * negOneSU` — specialization of centrality. -/
theorem negOneSU_mul_weylElem_eq_weylElem_mul_negOneSU :
    negOneSU * weylElem = weylElem * negOneSU :=
  negOneSU_mem_center weylElem

/-- `negOneSU * torusElem t = torusElem (t + π)` — multiplying by `-I`
shifts the torus angle by π (since `negOneSU = torusElem π` and T is abelian). -/
theorem negOneSU_mul_torusElem (t : ℝ) :
    negOneSU * torusElem t = torusElem (t + Real.pi) := by
  rw [← torusElem_pi_eq_negOneSU, ← torusElem_add, add_comm]

/-- `torusElem (-t) = (torusElem t)⁻¹` — inverse of a torus element is
the negation parameter. -/
theorem torusElem_neg (t : ℝ) :
    torusElem (-t) = (torusElem t)⁻¹ := by
  have h_mul :
      torusElem (-t) * torusElem t =
      (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
    rw [← torusElem_add, neg_add_cancel]
    exact torusElem_zero
  exact eq_inv_of_mul_eq_one_left h_mul

/-- `torusElem (-π/2) = (torusElem (π/2))⁻¹` — specialization. -/
theorem torusElem_neg_pi_half :
    torusElem (-(Real.pi / 2)) = (torusElem (Real.pi / 2))⁻¹ :=
  torusElem_neg (Real.pi / 2)


/-- `negOneSU * negOneSU = 1` — order-2 verification at subtype level.

Uses (-I)·(-I) = I·I = I = identity matrix. -/
theorem negOneSU_mul_self :
    negOneSU * negOneSU = (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  apply Subtype.ext
  show (-(1 : Matrix (Fin 2) (Fin 2) ℂ)) * (-(1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1
  rw [show (-(1 : Matrix (Fin 2) (Fin 2) ℂ)) * (-(1 : Matrix (Fin 2) (Fin 2) ℂ)) =
       (1 : Matrix (Fin 2) (Fin 2) ℂ) * (1 : Matrix (Fin 2) (Fin 2) ℂ) from by
         noncomm_ring]
  exact one_mul _

/-- `negOneSU⁻¹ = negOneSU` — order-2 implies self-inverse. -/
theorem negOneSU_inv_eq_self :
    negOneSU⁻¹ = negOneSU :=
  (eq_inv_of_mul_eq_one_left negOneSU_mul_self).symm

/-- `weylElem⁻¹ = negOneSU * weylElem` — using `weylElem² = negOneSU`
and `negOneSU² = 1`. -/
theorem weylElem_inv_eq_negOneSU_mul_weylElem :
    weylElem⁻¹ = negOneSU * weylElem := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  -- (negOneSU * weylElem) * weylElem = negOneSU * weylElem² = negOneSU² = 1.
  rw [mul_assoc, weylElem_sq_eq_negOneSU, negOneSU_mul_self]

/-- `weylElem ^ 4 = 1` — Weyl element has order 4. -/
theorem weylElem_pow_four :
    weylElem ^ 4 = (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  have h : weylElem ^ 4 = (weylElem * weylElem) * (weylElem * weylElem) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
  rw [h, weylElem_sq_eq_negOneSU, negOneSU_mul_self]

/-- **`weylElem` has finite order**, with order ≤ 4. -/
theorem weylElem_isOfFinOrder :
    IsOfFinOrder weylElem :=
  isOfFinOrder_iff_pow_eq_one.mpr
    ⟨4, by norm_num, weylElem_pow_four⟩

/-- `orderOf weylElem ≤ 4`. -/
theorem weylElem_orderOf_le_four :
    orderOf weylElem ≤ 4 :=
  orderOf_le_of_pow_eq_one (by norm_num) weylElem_pow_four

/-- `torusElem (π/2) ^ 4 = 1` — order ≤ 4 for the i-quaternion. -/
theorem torusElem_pi_half_pow_four :
    torusElem (Real.pi / 2) ^ 4 =
    (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  have h : torusElem (Real.pi / 2) ^ 4 =
           (torusElem (Real.pi / 2) * torusElem (Real.pi / 2)) *
           (torusElem (Real.pi / 2) * torusElem (Real.pi / 2)) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
  rw [h, torusElem_pi_half_sq, negOneSU_mul_self]

/-- `torusElem (π/2)` has finite order ≤ 4. -/
theorem torusElem_pi_half_isOfFinOrder :
    IsOfFinOrder (torusElem (Real.pi / 2)) :=
  isOfFinOrder_iff_pow_eq_one.mpr
    ⟨4, by norm_num, torusElem_pi_half_pow_four⟩

/-- `orderOf (torusElem (π/2)) ≤ 4`. -/
theorem torusElem_pi_half_orderOf_le_four :
    orderOf (torusElem (Real.pi / 2)) ≤ 4 :=
  orderOf_le_of_pow_eq_one (by norm_num) torusElem_pi_half_pow_four

/-- `negOneSU ≠ 1` — the SU(2) element -I is not the identity. -/
theorem negOneSU_ne_one :
    negOneSU ≠ (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  intro h_eq
  have h_val := congrArg Subtype.val h_eq
  have h_00 : negOneSU.val 0 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 :=
    congrArg (fun M => M 0 0) h_val
  simp [negOneSU_val, Matrix.neg_apply, Matrix.one_apply] at h_00
  exact absurd h_00 (by norm_num)

/-- `weylElem ^ 2 ≠ 1` — Weyl element has order > 2 (since weyl² = -I ≠ 1).

Combined with `weylElem_orderOf_le_four` and `weylElem_pow_four`, this rules
out `orderOf = 1, 2` for `weylElem` (positive divisors of 4 are 1, 2, 4). -/
theorem weylElem_sq_ne_one :
    weylElem ^ 2 ≠ (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  rw [sq, weylElem_sq_eq_negOneSU]
  exact negOneSU_ne_one

/-- `torusElem (π/2) ^ 2 ≠ 1` — the i-quaternion has order > 2
(since torusElem(π/2)² = negOneSU = -I ≠ 1). -/
theorem torusElem_pi_half_sq_ne_one :
    torusElem (Real.pi / 2) ^ 2 ≠
      (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  rw [sq, torusElem_pi_half_sq]
  exact negOneSU_ne_one

/-- `binaryTetrahedralElem ^ 3 ≠ 1` — the cube of the half-integer
quaternion is `-I ≠ 1`, ruling out the prime divisor 3 of orderOf = 6. -/
theorem binaryTetrahedralElem_cube_ne_one :
    binaryTetrahedralElem ^ 3 ≠
      (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  rw [binaryTetrahedralElem_cube]
  exact negOneSU_ne_one

/-- `binaryTetrahedralElem ^ 2 ≠ 1` — the square of the half-integer
quaternion has [0,0] entry `(i-1)/2 ≠ 1`, ruling out the prime divisor 2
of orderOf = 6.

Direct computation: `gen^2 [0,0] = ((1+i)/2)² + ((1+i)/2)((-1+i)/2)
= 2i/4 + (-2)/4 = (i-1)/2`. -/
theorem binaryTetrahedralElem_sq_ne_one :
    binaryTetrahedralElem ^ 2 ≠
      (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  intro h_eq
  have h_val : (binaryTetrahedralElem ^ 2 :
                  ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val =
               (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val :=
    congrArg Subtype.val h_eq
  have h_sq_unfold :
      (binaryTetrahedralElem ^ 2 :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val =
      binaryTetrahedralGen * binaryTetrahedralGen := by
    show binaryTetrahedralGen ^ 2 = binaryTetrahedralGen * binaryTetrahedralGen
    rw [sq]
  rw [h_sq_unfold] at h_val
  have h_00 := congrArg (fun M => M 0 0) h_val
  simp [binaryTetrahedralGen, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.one_apply] at h_00
  -- h_00 : (i-1)/2 = 1 (or equivalent algebraic form)
  -- Take .re: ((i-1)/2).re = -1/2 ≠ 1.re = 1
  have h_re := congrArg Complex.re h_00
  simp [Complex.div_re, Complex.add_re, Complex.sub_re,
        Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.one_re, Complex.one_im, Complex.normSq] at h_re
  linarith

/-- **`orderOf binaryTetrahedralElem = 6`** — the half-integer quaternion
generator has order exactly 6 in SU(2).

Discharges via `orderOf_eq_of_pow_and_pow_div_prime`: primes dividing 6
are {2, 3}; for each, `gen ^ (6/p) ≠ 1` (i.e., `gen ^ 3 ≠ 1` and
`gen ^ 2 ≠ 1` per `_cube_ne_one` and `_sq_ne_one`). -/
theorem binaryTetrahedralElem_orderOf_eq_six :
    orderOf binaryTetrahedralElem = 6 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
    binaryTetrahedralElem_sixth ?_
  intro p hp hpd
  -- Primes dividing 6 are {2, 3}: case-split.
  have h_le : p ≤ 6 := Nat.le_of_dvd (by norm_num) hpd
  have h_ge : 2 ≤ p := hp.two_le
  interval_cases p
  · -- p = 2: show gen ^ (6/2) = gen ^ 3 ≠ 1
    show binaryTetrahedralElem ^ (6 / 2) ≠ 1
    rw [show (6 / 2 : ℕ) = 3 from rfl]
    exact binaryTetrahedralElem_cube_ne_one
  · -- p = 3: show gen ^ (6/3) = gen ^ 2 ≠ 1
    show binaryTetrahedralElem ^ (6 / 3) ≠ 1
    rw [show (6 / 3 : ℕ) = 2 from rfl]
    exact binaryTetrahedralElem_sq_ne_one
  · -- p = 4: not prime
    exact absurd hp (by decide)
  · -- p = 5: 5 ∤ 6
    exact absurd hpd (by decide)
  · -- p = 6: not prime
    exact absurd hp (by decide)

/-- `Nat.card (Subgroup.zpowers binaryTetrahedralElem) = 6` — the cyclic
subgroup generated by the half-integer quaternion has order 6.

Direct corollary of `Nat.card_zpowers` + `_orderOf_eq_six`. -/
theorem binaryTetrahedralElem_zpowers_card :
    Nat.card (Subgroup.zpowers binaryTetrahedralElem) = 6 := by
  rw [Nat.card_zpowers, binaryTetrahedralElem_orderOf_eq_six]

/-- **`Nat.card binaryTetrahedralCyclic = 6`** — strengthened cardinality
equality (versus the prior `_le_six` bound) using the orderOf = 6 result. -/
theorem binaryTetrahedralCyclic_card_eq_six :
    Nat.card binaryTetrahedralCyclic = 6 :=
  binaryTetrahedralElem_zpowers_card

/-- **`negOneSU ∈ binaryTetrahedralCyclic`** — the scalar `-I` is `gen^3`,
hence lies in the cyclic subgroup generated by the half-integer quaternion. -/
theorem negOneSU_mem_binaryTetrahedralCyclic :
    negOneSU ∈ binaryTetrahedralCyclic := by
  show negOneSU ∈ Subgroup.zpowers binaryTetrahedralElem
  rw [← binaryTetrahedralElem_cube]
  exact Subgroup.npow_mem_zpowers binaryTetrahedralElem 3

/-- **`binaryTetrahedralElem⁻¹ = binaryTetrahedralElem^5`** — inverse of
the order-6 generator is its fifth power, since `gen * gen^5 = gen^6 = 1`. -/
theorem binaryTetrahedralElem_inv_eq_pow_five :
    binaryTetrahedralElem⁻¹ = binaryTetrahedralElem ^ 5 := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  -- Goal: binaryTetrahedralElem ^ 5 * binaryTetrahedralElem = 1
  rw [← pow_succ]
  exact binaryTetrahedralElem_sixth

/-- `negOneSU ^ 2 = 1` — square of the scalar `-I` is the identity. -/
theorem negOneSU_pow_two :
    negOneSU ^ 2 = (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  rw [sq]; exact negOneSU_mul_self

/-- `Nat.card (Subgroup.zpowers negOneSU) = 2` — the cyclic subgroup ⟨-I⟩
has 2 elements: `{1, -I}`. -/
theorem negOneSU_zpowers_card :
    Nat.card (Subgroup.zpowers negOneSU) = 2 := by
  rw [Nat.card_zpowers, negOneSU_orderOf_eq_two]

/-- `Subgroup.zpowers negOneSU ≤ binaryTetrahedralFull` — the order-2
center-cyclic ⟨-I⟩ is contained in 2T (since `-I ∈ 2T` via
`negOneSU_mem_binaryTetrahedralFull`). -/
theorem negOneSU_zpowers_le_binaryTetrahedralFull :
    Subgroup.zpowers negOneSU ≤ binaryTetrahedralFull := by
  rw [Subgroup.zpowers_le]
  exact negOneSU_mem_binaryTetrahedralFull

/-- `weylElem ^ 3 = negOneSU * weylElem` — Cube of Weyl element via
the squaring identity `w² = -I`. -/
theorem weylElem_pow_three :
    weylElem ^ 3 = negOneSU * weylElem := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one, sq,
      weylElem_sq_eq_negOneSU]

/-- `torusElem (π/2) ^ 3 = negOneSU * torusElem (π/2)` — Cube of the
i-quaternion via the squaring identity `τ² = -I`. -/
theorem torusElem_pi_half_pow_three :
    torusElem (Real.pi / 2) ^ 3 =
      negOneSU * torusElem (Real.pi / 2) := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one, sq,
      torusElem_pi_half_sq]

/-- `weylElem⁻¹ = weylElem ^ 3` — inverse of the order-4 Weyl element
is its cube, since `w * w^3 = w^4 = 1`. -/
theorem weylElem_inv_eq_pow_three :
    weylElem⁻¹ = weylElem ^ 3 := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  rw [← pow_succ]
  exact weylElem_pow_four

/-- `torusElem (π/2)⁻¹ = torusElem (π/2) ^ 3` — inverse of the order-4
i-quaternion is its cube. -/
theorem torusElem_pi_half_inv_eq_pow_three :
    (torusElem (Real.pi / 2))⁻¹ = torusElem (Real.pi / 2) ^ 3 := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  rw [← pow_succ]
  exact torusElem_pi_half_pow_four

/-- `weylElem⁻¹ ∈ binaryTetrahedralFull` — inverse of the j-quaternion
is in 2T (subgroups are closed under inversion). -/
theorem weylElem_inv_mem_binaryTetrahedralFull :
    weylElem⁻¹ ∈ binaryTetrahedralFull :=
  binaryTetrahedralFull.inv_mem weylElem_mem_binaryTetrahedralFull

/-- `(torusElem (π/2))⁻¹ ∈ binaryTetrahedralFull` — inverse of the
i-quaternion is in 2T. -/
theorem torusElem_pi_half_inv_mem_binaryTetrahedralFull :
    (torusElem (Real.pi / 2))⁻¹ ∈ binaryTetrahedralFull :=
  binaryTetrahedralFull.inv_mem torusElem_pi_half_mem_binaryTetrahedralFull

/-- `binaryTetrahedralElem⁻¹ ∈ binaryTetrahedralFull` — inverse of the
half-integer quaternion is in 2T. -/
theorem binaryTetrahedralElem_inv_mem_binaryTetrahedralFull :
    binaryTetrahedralElem⁻¹ ∈ binaryTetrahedralFull :=
  binaryTetrahedralFull.inv_mem binaryTetrahedralElem_mem_full

/-- `torusElem (π/2) ^ 2 = weylElem ^ 2` — both squares equal `negOneSU`,
giving a structural identity between the i-quaternion² and j-quaternion²
in SU(2). Both express the order-2 center element. -/
theorem torusElem_pi_half_sq_eq_weylElem_sq :
    torusElem (Real.pi / 2) ^ 2 = weylElem ^ 2 := by
  rw [sq, sq, torusElem_pi_half_sq, weylElem_sq_eq_negOneSU]

/-- `weylElem * torusElem (π/2) = torusElem (-(π/2)) * weylElem` —
specialization of the Weyl conjugation `w·τ_t·w⁻¹ = τ_{-t}` at `t = π/2`.

This is the canonical anti-commutation relation `ji = -k = (-i)j` in the
quaternion algebra (since τ_{-π/2} = τ_{π/2}⁻¹ = i⁻¹ = -i). -/
theorem weylElem_mul_torusElem_pi_half_eq :
    weylElem * torusElem (Real.pi / 2) =
      torusElem (-(Real.pi / 2)) * weylElem := by
  have h := weylElem_conj_torusElem (Real.pi / 2)
  -- h : weylElem * torusElem (π/2) * weylElem⁻¹ = torusElem (-(π/2))
  -- Multiply both sides on the right by weylElem.
  have h' : (weylElem * torusElem (Real.pi / 2) * weylElem⁻¹) * weylElem =
            torusElem (-(Real.pi / 2)) * weylElem := by
    rw [h]
  rw [mul_assoc, inv_mul_cancel, mul_one] at h'
  exact h'

/-- **`orderOf weylElem = 4`** — the Weyl element has order exactly 4 in SU(2).

This follows from `weylElem ^ 4 = 1` together with `weylElem ^ 2 ≠ 1` via
the only-prime-divisor-of-4-is-2 mechanism (`orderOf_eq_of_pow_and_pow_div_prime`). -/
theorem weylElem_orderOf_eq_four :
    orderOf weylElem = 4 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) weylElem_pow_four ?_
  intro p hp hpd
  -- Only prime dividing 4 is 2; reduce to `weylElem ^ 2 ≠ 1`.
  have hp2 : p = 2 := by
    have h_le : p ≤ 4 := Nat.le_of_dvd (by norm_num) hpd
    have h_ge : 2 ≤ p := hp.two_le
    interval_cases p
    · rfl
    · exact absurd hpd (by decide)
    · exact absurd hp (by decide)
  subst hp2
  show weylElem ^ (4 / 2) ≠ 1
  rw [show (4 / 2 : ℕ) = 2 from rfl]
  exact weylElem_sq_ne_one

/-- **`orderOf (torusElem (π/2)) = 4`** — the i-quaternion has order exactly 4.

Analogous to `weylElem_orderOf_eq_four`: pow_four = 1 plus pow_two ≠ 1, with
the only prime divisor of 4 being 2. -/
theorem torusElem_pi_half_orderOf_eq_four :
    orderOf (torusElem (Real.pi / 2)) = 4 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
    torusElem_pi_half_pow_four ?_
  intro p hp hpd
  have hp2 : p = 2 := by
    have h_le : p ≤ 4 := Nat.le_of_dvd (by norm_num) hpd
    have h_ge : 2 ≤ p := hp.two_le
    interval_cases p
    · rfl
    · exact absurd hpd (by decide)
    · exact absurd hp (by decide)
  subst hp2
  show torusElem (Real.pi / 2) ^ (4 / 2) ≠ 1
  rw [show (4 / 2 : ℕ) = 2 from rfl]
  exact torusElem_pi_half_sq_ne_one

/-- `Nat.card (Subgroup.zpowers weylElem) = 4` — the cyclic subgroup
generated by the Weyl element has order 4. -/
theorem weylElem_zpowers_card :
    Nat.card (Subgroup.zpowers weylElem) = 4 := by
  rw [Nat.card_zpowers, weylElem_orderOf_eq_four]

/-- `Nat.card (Subgroup.zpowers (torusElem (π/2))) = 4` — the cyclic
subgroup generated by the i-quaternion has order 4. -/
theorem torusElem_pi_half_zpowers_card :
    Nat.card (Subgroup.zpowers (torusElem (Real.pi / 2))) = 4 := by
  rw [Nat.card_zpowers, torusElem_pi_half_orderOf_eq_four]

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
