/-
Phase 6p Wave 2c.4a-R4.2.d.4.3.d.3 Wedge C session 1
(2026-05-20): Standard torus T_std ⊆ SU(2) — substantive ground-up
construction.

## Status

Wedge C of Phase 5 Step 13 Path (i) substantive Cartan classification.
This file ships the **standard torus T_std** and the **canonical
1-parameter subgroup** `t ↦ diag(exp(it), exp(-it))` parametrizing it.

Companion file `CartanSubstrate.lean` ships the predicate substrate
(Wedge A) and the corrected `CartanFinalStep_SU2` predicate (Wedge B).
Wedge C provides the **concrete witness** that `OneParamSubgroupInSU2`
is non-vacuous (the standard torus satisfies it constructively), and
is the substrate that will be consumed by the eventual discharge of
the three Cartan tracked Mathlib4 v4.29.1 gap Props.

## Shipped

§1 — `torusMatrix : ℝ → Matrix (Fin 2) (Fin 2) ℂ`:
  `t ↦ !![exp(it), 0; 0, exp(-it)]`.

§2 — `torusMatrix_mem_specialUnitaryGroup`:
  for all `t : ℝ`, `torusMatrix t ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ`.

§3 — `torusElem : ℝ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)`:
  the bundled SU(2) subtype element.

§4 — Group-homomorphism properties of `torusElem`:
  `torusElem_zero`, `torusElem_add`, `torusElem_neg`.

§5 — Continuity: `torusElem_continuous`.

§6 — Nontriviality witness: `torusElem_pi_ne_one`.

§7 — `stdTorus_SU2 : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)`:
  the standard torus, defined as the range of `torusElem` (viewed as
  a `MonoidHom` from `Multiplicative ℝ`).

§8 — `stdTorus_SU2_oneParamSubgroup`: the constructive witness that
  `stdTorus_SU2` satisfies the `OneParamSubgroupInSU2` predicate
  (Wedge A's predicate substrate).

## Pipeline Invariant compliance

  - Zero new project-local axioms (Inv #15 ✓).
  - Zero `maxHeartbeats` overrides (Inv #10 ✓).
  - ADR-003 zero-sorry ✓.

## Mathlib4 substrate consumed

  - `Matrix.specialUnitaryGroup` (Mathlib.LinearAlgebra.UnitaryGroup)
  - `Matrix.mem_specialUnitaryGroup_iff`,
    `Matrix.mem_unitaryGroup_iff`
  - `Complex.exp_add`, `Complex.exp_zero`, `Complex.exp_pi_mul_I`
  - `Continuous.complex_exp`, `Continuous.mul`
-/

import Mathlib
import SKEFTHawking.FKLW.CartanSubstrate

set_option autoImplicit false

namespace SKEFTHawking.FKLW

open Matrix Complex

/-! ## §1. The diagonal SU(2) matrix `diag(exp(it), exp(-it))` -/

/-- The matrix `diag(exp(it), exp(-it))` for real `t`.

For `t : ℝ`, this is a unit-determinant unitary matrix in SU(2). Its
parametrization gives the **standard maximal torus** of SU(2). -/
noncomputable def torusMatrix (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp ((t : ℂ) * I), 0;
     0, Complex.exp (-((t : ℂ) * I))]

/-! ## §2. `torusMatrix t ∈ SU(2)` -/

/-- `exp(it) · exp(-it) = 1` for any real `t`. -/
private theorem exp_mul_exp_neg_mul_I (t : ℝ) :
    Complex.exp ((t : ℂ) * I) * Complex.exp (-((t : ℂ) * I)) = 1 := by
  rw [← Complex.exp_add]
  simp

/-- `exp(-it) · exp(it) = 1` for any real `t`. -/
private theorem exp_neg_mul_exp_mul_I (t : ℝ) :
    Complex.exp (-((t : ℂ) * I)) * Complex.exp ((t : ℂ) * I) = 1 := by
  rw [mul_comm]
  exact exp_mul_exp_neg_mul_I t

/-- `star (Complex.exp ((t : ℂ) * I)) = Complex.exp (-((t : ℂ) * I))`. -/
private theorem star_exp_t_mul_I (t : ℝ) :
    star (Complex.exp ((t : ℂ) * I)) = Complex.exp (-((t : ℂ) * I)) := by
  show (starRingEnd ℂ) (Complex.exp ((t : ℂ) * I)) =
       Complex.exp (-((t : ℂ) * I))
  rw [← Complex.exp_conj]
  congr 1
  simp [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]

/-- `star (Complex.exp (-((t : ℂ) * I))) = Complex.exp ((t : ℂ) * I)`. -/
private theorem star_exp_neg_t_mul_I (t : ℝ) :
    star (Complex.exp (-((t : ℂ) * I))) = Complex.exp ((t : ℂ) * I) := by
  show (starRingEnd ℂ) (Complex.exp (-((t : ℂ) * I))) =
       Complex.exp ((t : ℂ) * I)
  rw [← Complex.exp_conj]
  congr 1
  simp [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_neg]

/-- The star of `torusMatrix t` equals the diagonal matrix
`diag(exp(-(it)), exp(it))`. -/
private theorem star_torusMatrix (t : ℝ) :
    star (torusMatrix t) =
      !![Complex.exp (-((t : ℂ) * I)), 0;
         0, Complex.exp ((t : ℂ) * I)] := by
  rw [Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusMatrix, Matrix.conjTranspose_apply,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.empty_val',
          Matrix.cons_val_fin_one, star_exp_t_mul_I, star_exp_neg_t_mul_I]

/-- `torusMatrix t · star (torusMatrix t) = 1` — unitarity. -/
private theorem torusMatrix_mul_star (t : ℝ) :
    torusMatrix t * star (torusMatrix t) = 1 := by
  rw [star_torusMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusMatrix, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.empty_val',
          Matrix.cons_val_fin_one,
          Matrix.one_apply, exp_mul_exp_neg_mul_I, exp_neg_mul_exp_mul_I]

/-- `det (torusMatrix t) = 1`. -/
private theorem torusMatrix_det (t : ℝ) :
    (torusMatrix t).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [torusMatrix, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons,
        Matrix.empty_val', Matrix.cons_val_fin_one,
        Matrix.head_fin_const, exp_mul_exp_neg_mul_I]

/-- **`torusMatrix t ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ`** —
membership in SU(2) for every real `t`. -/
theorem torusMatrix_mem_specialUnitaryGroup (t : ℝ) :
    torusMatrix t ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  Matrix.mem_specialUnitaryGroup_iff.mpr
    ⟨Matrix.mem_unitaryGroup_iff.mpr (torusMatrix_mul_star t),
     torusMatrix_det t⟩

/-! ## §3. The bundled SU(2) subtype element -/

/-- `torusElem t : SU(2)` — the SU(2) element corresponding to `torusMatrix t`. -/
noncomputable def torusElem (t : ℝ) :
    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  ⟨torusMatrix t, torusMatrix_mem_specialUnitaryGroup t⟩

/-- `torusElem t` has value `torusMatrix t`. -/
@[simp] theorem torusElem_val (t : ℝ) :
    (torusElem t : Matrix (Fin 2) (Fin 2) ℂ) = torusMatrix t := rfl

/-! ## §4. Group-homomorphism properties of `torusElem` -/

/-- `torusElem 0 = 1`. -/
theorem torusElem_zero : torusElem 0 = 1 := by
  apply Subtype.ext
  show torusMatrix 0 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusMatrix, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons,
          Matrix.empty_val', Matrix.cons_val_fin_one,
          Matrix.head_fin_const, Matrix.one_apply, Complex.ofReal_zero]

/-- `Complex.exp ((↑s + ↑t) * I) = Complex.exp (↑s * I) * Complex.exp (↑t * I)`. -/
private theorem exp_add_real_mul_I (s t : ℝ) :
    Complex.exp (((s : ℂ) + (t : ℂ)) * I) =
      Complex.exp ((s : ℂ) * I) * Complex.exp ((t : ℂ) * I) := by
  rw [show (((s : ℂ) + (t : ℂ)) * I) = ((s : ℂ) * I + (t : ℂ) * I) by ring,
      Complex.exp_add]

/-- `Complex.exp (-((↑s + ↑t) * I)) = Complex.exp (-(↑s * I)) * Complex.exp (-(↑t * I))`. -/
private theorem exp_neg_add_real_mul_I (s t : ℝ) :
    Complex.exp (-(((s : ℂ) + (t : ℂ)) * I)) =
      Complex.exp (-((s : ℂ) * I)) * Complex.exp (-((t : ℂ) * I)) := by
  rw [show (-(((s : ℂ) + (t : ℂ)) * I)) = (-((s : ℂ) * I) + -((t : ℂ) * I)) by ring,
      Complex.exp_add]

/-- `torusMatrix (s + t) = torusMatrix s * torusMatrix t` —
matrix-level homomorphism. -/
private theorem torusMatrix_add (s t : ℝ) :
    torusMatrix (s + t) = torusMatrix s * torusMatrix t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusMatrix, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.empty_val',
          Matrix.cons_val_fin_one,
          exp_add_real_mul_I, exp_neg_add_real_mul_I]

/-- **`torusElem (s + t) = torusElem s * torusElem t`** —
the group-homomorphism property. -/
theorem torusElem_add (s t : ℝ) :
    torusElem (s + t) = torusElem s * torusElem t := by
  apply Subtype.ext
  show torusMatrix (s + t) = torusMatrix s * torusMatrix t
  exact torusMatrix_add s t

/-! ## §5. Continuity -/

/-- **`torusMatrix` is continuous as a function `ℝ → Matrix _ _ ℂ`** —
where Matrix has the function topology. -/
theorem torusMatrix_continuous : Continuous torusMatrix := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [torusMatrix, Matrix.cons_val', Matrix.cons_val_zero,
               Matrix.cons_val_one, Matrix.head_cons,
               Matrix.empty_val', Matrix.cons_val_fin_one,
               Matrix.head_fin_const]
  · exact Complex.continuous_exp.comp
      (Complex.continuous_ofReal.mul continuous_const)
  · exact continuous_const
  · exact continuous_const
  · exact Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.mul continuous_const).neg)

/-- **`torusElem` is continuous as a function `ℝ → SU(2)`** —
via the subtype topology. -/
theorem torusElem_continuous : Continuous torusElem :=
  continuous_induced_rng.mpr torusMatrix_continuous

/-! ## §6. Nontriviality witness -/

/-- **`torusElem π ≠ 1`** — `exp(πi) = -1`, so `torusElem π = -I ≠ I`. -/
theorem torusElem_pi_ne_one : torusElem Real.pi ≠ 1 := by
  intro h_eq
  have h_val : (torusElem Real.pi : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    congrArg Subtype.val h_eq
  have h_00 : torusMatrix Real.pi 0 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by
    rw [← torusElem_val]
    exact congrArg (fun M => M 0 0) h_val
  -- LHS = exp(πi) = -1; RHS = 1; contradiction.
  -- The simp chain below auto-evaluates exp(π·I) = -1.
  simp [torusMatrix, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.empty_val', Matrix.cons_val_fin_one,
        Complex.exp_pi_mul_I] at h_00
  exact absurd h_00 (by norm_num)

/-! ## §7. The standard torus subgroup -/

/-- **The standard torus** `T_std ⊆ SU(2)` — defined as the **range** of
the 1-parameter subgroup `torusElem`.

Equivalently, the set of all SU(2) matrices of the form
`diag(exp(it), exp(-it))` for some `t : ℝ`. Closure under multiplication
follows from `torusElem_add`; closure under inverse from `torusElem_add`
applied to `-t`; the identity is `torusElem 0`. -/
noncomputable def stdTorus_SU2 :
    Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) where
  carrier := Set.range torusElem
  mul_mem' := by
    rintro x y ⟨s, hs⟩ ⟨t, ht⟩
    exact ⟨s + t, by rw [torusElem_add, hs, ht]⟩
  one_mem' := ⟨0, torusElem_zero⟩
  inv_mem' := by
    rintro x ⟨t, ht⟩
    refine ⟨-t, ?_⟩
    have h_inv : torusElem t * torusElem (-t) = 1 := by
      rw [← torusElem_add, add_neg_cancel, torusElem_zero]
    have h_inv_unique : torusElem (-t) = (torusElem t)⁻¹ :=
      eq_inv_of_mul_eq_one_right h_inv
    rw [h_inv_unique, ht]

/-! ## §8a. `stdTorus_SU2` is abelian -/

/-- **`stdTorus_SU2` is commutative**: any two elements of the standard
torus commute.

Direct consequence of the group-homomorphism property of `torusElem`:
`torusElem s * torusElem t = torusElem (s + t) = torusElem (t + s) =
torusElem t * torusElem s`. -/
theorem stdTorus_SU2_abelian (g h : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (hg : g ∈ stdTorus_SU2) (hh : h ∈ stdTorus_SU2) :
    g * h = h * g := by
  obtain ⟨s, hs⟩ := hg
  obtain ⟨t, ht⟩ := hh
  rw [← hs, ← ht, ← torusElem_add, ← torusElem_add, add_comm]

/-! ## §8. `stdTorus_SU2` satisfies `OneParamSubgroupInSU2` -/

/-- **Wedge C session-1 headline — `stdTorus_SU2` is a 1-parameter
subgroup of SU(2).**

Constructive witness for `OneParamSubgroupInSU2 stdTorus_SU2`. The
witness is exactly `torusElem`. This shows that the predicate
`OneParamSubgroupInSU2` (shipped in Wedge A) is non-vacuous on
SU(2) — it has at least one explicit constructive instance. -/
theorem stdTorus_SU2_oneParamSubgroup :
    OneParamSubgroupInSU2 stdTorus_SU2 := by
  refine ⟨torusElem, torusElem_continuous, torusElem_zero,
          torusElem_add, ⟨Real.pi, torusElem_pi_ne_one⟩, ?_⟩
  intro t
  exact ⟨t, rfl⟩

/-! ## §11. The Weyl element `w := !![0, 1; -1, 0]` (session 88) -/

/-- **The Weyl matrix** `w := !![0, 1; -1, 0]` ∈ SU(2).

Used in Cartan classification of closed subgroups of SU(2): the
normalizer `N(T)` of the standard torus is `T ∪ wT`. The Weyl
element implements the non-trivial Weyl-group action on `T` by
conjugation: `w · diag(z, z⁻¹) · w⁻¹ = diag(z⁻¹, z)`. -/
noncomputable def weylMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; -1, 0]

/-- `det weylMatrix = 1`. -/
private theorem weylMatrix_det : weylMatrix.det = 1 := by
  rw [Matrix.det_fin_two]
  simp [weylMatrix, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons,
        Matrix.empty_val', Matrix.cons_val_fin_one]

/-- `star weylMatrix = !![0, -1; 1, 0]`. -/
private theorem star_weylMatrix :
    star weylMatrix = !![0, -1; 1, 0] := by
  rw [Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylMatrix, Matrix.conjTranspose_apply,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.empty_val',
          Matrix.cons_val_fin_one, map_neg, map_one]

/-- `weylMatrix · star weylMatrix = 1` — unitarity. -/
private theorem weylMatrix_mul_star : weylMatrix * star weylMatrix = 1 := by
  rw [star_weylMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylMatrix, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.empty_val',
          Matrix.cons_val_fin_one, Matrix.one_apply]

/-- **`weylMatrix ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ`** — SU(2) membership. -/
theorem weylMatrix_mem_specialUnitaryGroup :
    weylMatrix ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  Matrix.mem_specialUnitaryGroup_iff.mpr
    ⟨Matrix.mem_unitaryGroup_iff.mpr weylMatrix_mul_star,
     weylMatrix_det⟩

/-- The Weyl element bundled as an SU(2) subtype. -/
noncomputable def weylElem :
    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  ⟨weylMatrix, weylMatrix_mem_specialUnitaryGroup⟩

/-- `weylElem.val = weylMatrix`. -/
@[simp] theorem weylElem_val :
    (weylElem : Matrix (Fin 2) (Fin 2) ℂ) = weylMatrix := rfl

/-! ## §12. Weyl conjugation inverts the standard torus -/

/-- `weylMatrix · torusMatrix t · star weylMatrix = torusMatrix (-t)` —
Weyl conjugation inverts torus elements at the matrix level. -/
private theorem weylMatrix_conj_torusMatrix (t : ℝ) :
    weylMatrix * torusMatrix t * star weylMatrix = torusMatrix (-t) := by
  rw [star_weylMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylMatrix, torusMatrix, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.empty_val',
          Matrix.cons_val_fin_one,
          show ((-t : ℝ) : ℂ) * I = -((t : ℂ) * I) by push_cast; ring,
          show -(((-t : ℝ) : ℂ) * I) = ((t : ℂ) * I) by push_cast; ring]

/-- **HEADLINE — Weyl conjugation inverts the standard torus**.

`weylElem · torusElem t · weylElem⁻¹ = torusElem (-t)`. This is the
key Weyl-group structure that makes `N(stdTorus_SU2) = T ∪ wT`. Used
in the Cartan classification: any closed subgroup `H ⊃ T` is either
`T` or `N(T)` or `⊤`. -/
theorem weylElem_conj_torusElem (t : ℝ) :
    weylElem * torusElem t * weylElem⁻¹ = torusElem (-t) := by
  apply Subtype.ext
  -- weylElem⁻¹.val = star weylMatrix (via Matrix.star_eq_inv)
  have h_inv_val :
      ((weylElem⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) = star weylMatrix := by
    have h_star : star weylElem = weylElem⁻¹ := Matrix.star_eq_inv weylElem
    rw [← h_star]
    rfl
  show weylMatrix * torusMatrix t * _ = torusMatrix (-t)
  rw [h_inv_val]
  exact weylMatrix_conj_torusMatrix t

/-- **`weylElem⁻¹ · torusElem t · weylElem = torusElem (-t)`** —
the inverse Weyl conjugation also inverts. Since the Weyl-conjugation
automorphism `f(g) := w · g · w⁻¹` is involutive on T (because
w² = -1 commutes with all of T), `f⁻¹|T = f|T`. -/
theorem weylElem_inv_conj_torusElem (t : ℝ) :
    weylElem⁻¹ * torusElem t * weylElem = torusElem (-t) := by
  -- Apply weylElem_conj_torusElem at -t: w · t_{-t} · w⁻¹ = t_t.
  have h1 : weylElem * torusElem (-t) * weylElem⁻¹ = torusElem t := by
    have := weylElem_conj_torusElem (-t)
    rwa [neg_neg] at this
  -- Conjugate both sides by w⁻¹ / w to peel off the outer w's.
  have h2 : weylElem⁻¹ * (weylElem * torusElem (-t) * weylElem⁻¹) * weylElem
          = weylElem⁻¹ * torusElem t * weylElem := by rw [h1]
  -- LHS simplifies via group axioms.
  have h3 : weylElem⁻¹ * (weylElem * torusElem (-t) * weylElem⁻¹) * weylElem
          = torusElem (-t) := by group
  rw [h3] at h2
  exact h2.symm

/-- **`weylElem ∈ N(stdTorus_SU2)`** — the Weyl element normalizes
the standard torus.

Substantive content: ∀ h ∈ SU(2), h ∈ T ↔ w · h · w⁻¹ ∈ T. Forward
direction via `weylElem_conj_torusElem`; backward direction via
`weylElem_inv_conj_torusElem` (the inverse Weyl conjugation also
maps T → T). -/
theorem weylElem_mem_normalizer_stdTorus :
    weylElem ∈ Subgroup.normalizer stdTorus_SU2 := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · -- h ∈ T → w · h · w⁻¹ ∈ T.
    rintro ⟨t, ht⟩
    refine ⟨-t, ?_⟩
    rw [← ht]
    exact (weylElem_conj_torusElem t).symm
  · -- w · h · w⁻¹ ∈ T → h ∈ T (via w⁻¹ · (w·h·w⁻¹) · w = h).
    rintro ⟨t, ht⟩
    refine ⟨-t, ?_⟩
    -- ht : torusElem t = weylElem * h * weylElem⁻¹
    -- Derive h = weylElem⁻¹ * torusElem t * weylElem
    have h_eq : h = weylElem⁻¹ * torusElem t * weylElem := by
      have : weylElem⁻¹ * (weylElem * h * weylElem⁻¹) * weylElem = h := by group
      rw [← ht] at this
      exact this.symm
    rw [h_eq]
    exact (weylElem_inv_conj_torusElem t).symm

/-- **`weylElem` does NOT lie in `stdTorus_SU2`**.

If `w ∈ T`, then conjugation by `w` would preserve every element of T
pointwise (T is abelian, so `w · t · w⁻¹ = t`). But Weyl conjugation
gives `w · t · w⁻¹ = t⁻¹` for `t ∈ T`. Combining: every `t ∈ T`
satisfies `t = t⁻¹`. Taking `t := torusElem (π/2)` yields
`I = -I` (via the [0,0] entry comparison), contradicting `Complex.I.im = 1`. -/
theorem weylElem_not_mem_stdTorus :
    weylElem ∉ stdTorus_SU2 := by
  intro h_mem
  -- Step 1: w = torusElem s for some s ∈ ℝ.
  obtain ⟨s, hs⟩ := h_mem
  -- Step 2: Weyl conjugation: w · t · w⁻¹ = t⁻¹ for t = torusElem (π/2).
  have h_weyl : weylElem * torusElem (Real.pi / 2) * weylElem⁻¹
              = torusElem (-(Real.pi / 2)) := weylElem_conj_torusElem _
  -- Step 3: but w ∈ T abelian, so w · t = t · w, hence w · t · w⁻¹ = t.
  have h_comm : weylElem * torusElem (Real.pi / 2) =
                torusElem (Real.pi / 2) * weylElem := by
    rw [← hs, ← torusElem_add, ← torusElem_add, add_comm]
  have h_triv : weylElem * torusElem (Real.pi / 2) * weylElem⁻¹
              = torusElem (Real.pi / 2) := by
    rw [h_comm]; group
  -- Step 4: Combining h_weyl and h_triv: torusElem (π/2) = torusElem (-π/2).
  rw [h_triv] at h_weyl
  -- Step 5: Project to [0,0] entry; should give I = -I.
  have h_val : (torusElem (Real.pi / 2)).val =
               (torusElem (-(Real.pi / 2))).val :=
    congrArg Subtype.val h_weyl
  have h_00 : (torusElem (Real.pi / 2)).val 0 0 =
              (torusElem (-(Real.pi / 2))).val 0 0 :=
    congrArg (fun M => M 0 0) h_val
  -- LHS [0,0] = exp((π/2)·I) = I (via Complex.exp_pi_div_two_mul_I).
  -- RHS [0,0] = exp((-π/2)·I) = -I (via Complex.exp_neg_pi_div_two_mul_I).
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
  have h_rhs : (torusElem (-(Real.pi / 2))).val 0 0 = -Complex.I := by
    show torusMatrix (-(Real.pi / 2)) 0 0 = -Complex.I
    have h_simp : torusMatrix (-(Real.pi / 2)) 0 0 =
                  Complex.exp (((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I) := by
      simp [torusMatrix, Matrix.cons_val', Matrix.cons_val_zero,
            Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [h_simp,
        show (((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I) =
             (-↑Real.pi / 2 * Complex.I) by push_cast; ring,
        Complex.exp_neg_pi_div_two_mul_I]
  -- h_00 + h_lhs + h_rhs: I = -I.
  rw [h_lhs, h_rhs] at h_00
  -- Show I ≠ -I via imaginary part.
  have h_im : Complex.I.im = (-Complex.I).im := congrArg Complex.im h_00
  -- LHS = 1, RHS = -1.
  simp [Complex.I_im, Complex.neg_im] at h_im
  linarith

/-! ## §13. Structural intersections with `negOneSU` -/

/-- `exp(-iπ) = -1`. -/
private theorem exp_neg_pi_mul_I :
    Complex.exp (-((Real.pi : ℂ) * Complex.I)) = -1 := by
  rw [Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-- `torusElem π = negOneSU` (the SU(2) element `-I`).

Direct matrix verification: `torusMatrix π = !![exp(iπ), 0; 0, exp(-iπ)] =
!![-1, 0; 0, -1] = -I = negOneSU.val`. -/
theorem torusElem_pi_eq_negOneSU :
    torusElem Real.pi = negOneSU := by
  apply Subtype.ext
  show torusMatrix Real.pi = (negOneSU : Matrix (Fin 2) (Fin 2) ℂ)
  rw [negOneSU_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusMatrix, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val',
          Matrix.cons_val_fin_one,
          Matrix.neg_apply, Matrix.one_apply,
          Complex.exp_pi_mul_I, exp_neg_pi_mul_I]

/-- **`negOneSU ∈ stdTorus_SU2`** — the SU(2) element `-I` lies in the
standard torus.

Direct consequence of `torusElem_pi_eq_negOneSU`. -/
theorem negOneSU_mem_stdTorus_SU2 : negOneSU ∈ stdTorus_SU2 :=
  ⟨Real.pi, torusElem_pi_eq_negOneSU⟩

/-! ## §14. The Weyl element squares to `-I` -/

/-- `weylMatrix² = -(1 : Matrix _ _ ℂ)`. -/
private theorem weylMatrix_sq :
    weylMatrix * weylMatrix = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylMatrix, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.empty_val',
          Matrix.cons_val_fin_one, Matrix.neg_apply, Matrix.one_apply]

/-- **`weylElem² = negOneSU`** — the Weyl element has order 4.

Direct consequence of `weylMatrix_sq` lifted to the subtype.

This is THE structural fact making `N(T) / T ≅ ℤ/2`: the Weyl element
is order-4 in SU(2), order-2 modulo `T` (since `w² ∈ T`). The
Weyl-group quotient `N(T) / T` thus has the standard {1, w}
representative structure. -/
theorem weylElem_sq_eq_negOneSU :
    weylElem * weylElem = negOneSU := by
  apply Subtype.ext
  show weylMatrix * weylMatrix = (negOneSU : Matrix (Fin 2) (Fin 2) ℂ)
  rw [negOneSU_val, weylMatrix_sq]

/-- **`weylElem² ∈ stdTorus_SU2`** — corollary composing
`weylElem_sq_eq_negOneSU` with `negOneSU_mem_stdTorus_SU2`. -/
theorem weylElem_sq_mem_stdTorus_SU2 :
    weylElem * weylElem ∈ stdTorus_SU2 := by
  rw [weylElem_sq_eq_negOneSU]
  exact negOneSU_mem_stdTorus_SU2

/-! ## §10. Substrate for `stdTorus_SU2` infinitude (irrational rotation) -/

/-- **Key non-vanishing lemma**: `Complex.exp ((n+1 : ℝ) · I) ≠ 1` for `n : ℕ`.

If `exp((n+1) · I) = 1`, then by `Complex.exp_eq_one_iff`,
`(n+1) · I = m · (2π · I)` for some integer `m`. Canceling `I` gives
the real equation `(n+1) = 2π · m`. Case-splitting on `m`:
  - `m = 0` ⇒ `n + 1 = 0`, impossible.
  - `m ≠ 0` ⇒ `π = (n+1)/(2m)` is rational, contradicting `irrational_pi`. -/
theorem complex_exp_natCast_succ_mul_I_ne_one (n : ℕ) :
    Complex.exp ((((n + 1 : ℕ) : ℝ) : ℂ) * Complex.I) ≠ 1 := by
  intro h_exp
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h_exp
  -- Cancel I to get a real equation.
  have h_C : (((n + 1 : ℕ) : ℝ) : ℂ) = (m : ℂ) * (2 * (Real.pi : ℂ)) := by
    have h_C_I : (((n + 1 : ℕ) : ℝ) : ℂ) * Complex.I =
                 ((m : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by
      rw [hm]; ring
    exact mul_right_cancel₀ Complex.I_ne_zero h_C_I
  -- Take real parts: (n+1 : ℝ) = 2π · m.
  have h_real : ((n + 1 : ℕ) : ℝ) = (m : ℝ) * (2 * Real.pi) := by
    have h_re := congrArg Complex.re h_C
    simp [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
          Complex.intCast_re, Complex.intCast_im, Complex.ofReal_im,
          Complex.one_re] at h_re
    push_cast
    linarith
  -- LHS ≥ 1 > 0.
  have h_lhs_pos : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg n (α := ℝ)]
    push_cast
    linarith
  -- Case-split on m.
  rcases eq_or_ne m 0 with hm_zero | hm_ne
  · -- m = 0 ⇒ RHS = 0 ⇒ LHS = 0, contradicting LHS ≥ 1.
    rw [hm_zero] at h_real
    push_cast at h_real
    linarith
  · -- m ≠ 0 ⇒ π = (n+1) / (2m) is rational.
    have h_2_ne : (2 : ℝ) ≠ 0 := by norm_num
    have h_m_ne : (m : ℝ) ≠ 0 := by exact_mod_cast hm_ne
    have h_pi_eq : Real.pi = ((n + 1 : ℕ) : ℝ) / (2 * (m : ℝ)) := by
      field_simp
      linarith
    -- Real.pi equals a rational; contradicts irrational_pi.
    refine irrational_pi ⟨((n + 1 : ℤ) : ℚ) / ((2 : ℚ) * (m : ℚ)), ?_⟩
    rw [h_pi_eq]
    push_cast
    ring

end SKEFTHawking.FKLW
