/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6z Wave 1 — the algebraic-integer / root-of-unity obstruction

The faithful literal Clifford+CCZ headline (`⟨H,S,CNOT,CCZ⟩` dense in SU(8), CCZ essential, no `T`)
needs a continuous one-parameter subgroup in the closure of the discrete group. Since every literal
generator is finite-order, the first such flow is seeded by an **infinite-order** element with an
**irrational eigen-angle**. The operative seed (Phase-6z Gate 1, `verify_seed.py`) is
`g₀ = (H⊗H⊗H · CCX)² ∈ SO(8)`, whose non-trivial eigenvalues are `λ_± = (−3 ± i√7)/4` with minimal
polynomial `2x² + 3x + 2` over `ℤ` (monic minpoly over `ℚ` is `x² + (3/2)x + 1`).

The mechanism: a finite-order unitary has all eigenvalues roots of unity, and a root of unity is an
**algebraic integer**. `λ_±` is **not** an algebraic integer (its monic `ℚ`-minimal polynomial has a
non-integer coefficient `3/2`; equivalently `λ + λ̄ = −3/2 ∉ ℤ`). Hence `λ_±` is not a root of unity,
so its argument is an irrational multiple of `π` — the seed for Kronecker accumulation.

This module ships the **general, reusable obstruction** (the highest-leverage Wave-1 artifact):

  `not_rootOfUnity_of_not_isIntegral : ¬ IsIntegral ℤ α → ∀ n, 0 < n → α ^ n ≠ 1`

via the monic integer polynomial `Xⁿ − 1` (a root of unity is integral). Independently reusable.

## Pipeline invariants

  * **#10** (no `maxHeartbeats` in proofs): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6z provenance

Phase 6z Wave 1 (seed + irrationality), 2026-05-28. Gate-1 corrected spectrum `(−3±i√7)/4`.
-/

import Mathlib

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Polynomial

/-- A root of unity is an algebraic integer: if `α ^ n = 1` with `0 < n`, then `IsIntegral ℤ α`,
witnessed by the monic integer polynomial `Xⁿ − 1`. -/
theorem isIntegral_of_pow_eq_one {α : ℂ} {n : ℕ} (hn : 0 < n) (h : α ^ n = 1) :
    IsIntegral ℤ α := by
  refine ⟨X ^ n - C 1, ?_, ?_⟩
  · exact monic_X_pow_sub_C 1 hn.ne'
  · simp [h]

/-- **The reusable irrationality obstruction.** A complex number that is *not* an algebraic integer
is *not* a root of unity. Contrapositive of `isIntegral_of_pow_eq_one`. -/
theorem not_rootOfUnity_of_not_isIntegral {α : ℂ} (hα : ¬ IsIntegral ℤ α) (n : ℕ) (hn : 0 < n) :
    α ^ n ≠ 1 := fun h => hα (isIntegral_of_pow_eq_one hn h)

/-- The seed's non-trivial eigenvalue `λ = (−3 + i√7)/4` (Gate-1 corrected spectrum; minimal
polynomial `2x² + 3x + 2` over `ℤ`, so `|λ| = 1`). -/
noncomputable def seedEigenvalue : ℂ := (-3 + Complex.I * (Real.sqrt 7 : ℂ)) / 4

/-- `λ + λ̄ = −3/2`: the real part of the seed eigenvalue is `−3/4`, and the `√7` cancels. -/
lemma seedEigenvalue_add_conj :
    seedEigenvalue + (starRingEnd ℂ) seedEigenvalue = (-3 / 2 : ℂ) := by
  simp only [seedEigenvalue, map_div₀, map_add, map_mul, map_neg, map_ofNat,
    Complex.conj_I, Complex.conj_ofReal]
  ring

/-- **The seed eigenvalue is not an algebraic integer.** If it were, the complex conjugate would be too
(conjugation is a `ℤ`-algebra map), so `λ + λ̄ = −3/2` would be a rational algebraic integer, hence a
rational integer — but `−3/2 ∉ ℤ`. (`ℤ` is integrally closed in its fraction field `ℚ`.) -/
theorem not_isIntegral_seedEigenvalue : ¬ IsIntegral ℤ seedEigenvalue := by
  intro hlam
  have hconj : IsIntegral ℤ ((starRingEnd ℂ) seedEigenvalue) := by
    have h := hlam.map (Complex.conjAe.toAlgHom.restrictScalars ℤ)
    simpa [Complex.conjAe_coe] using h
  have hsum : IsIntegral ℤ (seedEigenvalue + (starRingEnd ℂ) seedEigenvalue) := hlam.add hconj
  rw [seedEigenvalue_add_conj] at hsum
  have hcast : (-3 / 2 : ℂ) = algebraMap ℚ ℂ (-3 / 2 : ℚ) := by
    simp only [map_div₀, map_neg, map_ofNat]
  rw [hcast, isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective,
    IsIntegrallyClosed.isIntegral_iff] at hsum
  obtain ⟨y, hy⟩ := hsum
  have hy' : (y : ℚ) = -3 / 2 := hy
  have h2 : (2 * y : ℤ) = -3 := by
    have hq : (2 * (y : ℚ)) = -3 := by rw [hy']; norm_num
    exact_mod_cast hq
  omega

/-- **The seed eigenvalue is not a root of unity** — its argument is an irrational multiple of `π`,
the seed for Kronecker accumulation (Wave 2). -/
theorem not_rootOfUnity_seedEigenvalue (n : ℕ) (hn : 0 < n) : seedEigenvalue ^ n ≠ 1 :=
  not_rootOfUnity_of_not_isIntegral not_isIntegral_seedEigenvalue n hn

/-- **Root-of-unity phase preserves non-integrality.** If `α` is not an algebraic integer and `u` is a
unit whose inverse *is* an algebraic integer (e.g. any root of unity), then `u · α` is not an algebraic
integer. This is the algebraic core of DR2's "phase preservation": the seed's genuine group element
`g_grp = ω⁻¹ · g₀` differs from `g₀` by a central root-of-unity phase, and that phase cannot turn the
non-algebraic-integer eigenvalue into an algebraic integer. -/
theorem not_isIntegral_mul_left {u α : ℂ} (hu : IsIntegral ℤ u⁻¹) (hu0 : u ≠ 0)
    (hα : ¬ IsIntegral ℤ α) : ¬ IsIntegral ℤ (u * α) := by
  intro h
  refine hα ?_
  have hmul := hu.mul h
  rwa [← mul_assoc, inv_mul_cancel₀ hu0, one_mul] at hmul

/-- `λ · λ̄ = 1`, i.e. `|λ| = 1`: the seed eigenvalue lies on the unit circle (`9 + 7 = 16`). The
companion to `seedEigenvalue_add_conj`; together they are Vieta's relations for `2x² + 3x + 2`. -/
lemma seedEigenvalue_mul_conj :
    seedEigenvalue * (starRingEnd ℂ) seedEigenvalue = 1 := by
  have hs : ((Real.sqrt 7 : ℝ) : ℂ) ^ 2 = 7 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7)]; norm_num
  simp only [seedEigenvalue, map_div₀, map_add, map_mul, map_neg, map_ofNat,
    Complex.conj_I, Complex.conj_ofReal]
  field_simp
  linear_combination (-(Complex.I ^ 2)) * hs + (-7 : ℂ) * Complex.I_sq

/-- `‖λ‖ = 1`: the seed eigenvalue is on the unit circle. -/
lemma norm_seedEigenvalue : ‖seedEigenvalue‖ = 1 := by
  have h := seedEigenvalue_mul_conj
  rw [Complex.mul_conj] at h
  have hns : Complex.normSq seedEigenvalue = 1 := by exact_mod_cast h
  rw [Complex.norm_def, hns, Real.sqrt_one]

/-- **`1/√2` is not an algebraic integer** (matches the shipped `litSeed_trace = 1/√2`): if it were,
its square `1/2` would be a rational algebraic integer, hence an integer — but `1/2 ∉ ℤ`. Combined with
`not_isIntegral_mul_left`, this shows the seed's trace `ω₀⁻¹·(1/√2)` is not an algebraic integer, the
Route-B route to "seed not finite order". -/
theorem not_isIntegral_inv_sqrt_two : ¬ IsIntegral ℤ (1 / (Real.sqrt 2 : ℂ)) := by
  intro h
  have hsqrt : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have hsq : IsIntegral ℤ ((1 / (Real.sqrt 2 : ℂ)) ^ 2) := h.pow 2
  have he : (1 / (Real.sqrt 2 : ℂ)) ^ 2 = algebraMap ℚ ℂ (1 / 2) := by
    rw [div_pow, one_pow, hsqrt]
    simp only [map_div₀, map_one, map_ofNat]
  rw [he, isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective,
    IsIntegrallyClosed.isIntegral_iff] at hsq
  obtain ⟨y, hy⟩ := hsq
  have hy' : (y : ℚ) = 1 / 2 := hy
  have h2 : (2 * y : ℤ) = 1 := by
    have hq : (2 * (y : ℚ)) = 1 := by rw [hy']; norm_num
    exact_mod_cast hq
  omega

/-! ## The spectral meta-lemma: a finite-order matrix has an algebraic-integer trace -/

/-- **A finite-order complex matrix has an algebraic-integer trace.** If `Mⁿ = 1` with `0 < n`, then
each root of the characteristic polynomial is an `n`-th root of unity (hence an algebraic integer, by
`isIntegral_of_pow_eq_one`), and `tr M` is the sum of those roots. General + reusable; the spectral
core of "the seed is not finite order" (contrapositive: a matrix whose trace is *not* an algebraic
integer cannot be of finite order). -/
theorem trace_isIntegral_of_pow_eq_one {k : ℕ} [NeZero k] (M : Matrix (Fin k) (Fin k) ℂ)
    {n : ℕ} (hn : 0 < n) (hM : M ^ n = 1) : IsIntegral ℤ M.trace := by
  rw [Matrix.trace_eq_sum_roots_charpoly]
  refine IsIntegral.multiset_sum (fun r hr => ?_)
  refine isIntegral_of_pow_eq_one hn ?_
  have hspec : r ∈ spectrum ℂ M :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.mpr (Polynomial.isRoot_of_mem_roots hr)
  have key : r ^ n ∈ spectrum ℂ (Polynomial.aeval M (Polynomial.X ^ n)) :=
    spectrum.subset_polynomial_aeval M (Polynomial.X ^ n)
      ⟨r, hspec, by simp [Polynomial.eval_pow]⟩
  rw [Polynomial.aeval_X_pow, hM, spectrum.one_eq] at key
  simpa using key

end SKEFTHawking.FKLW.CliffordCCZSU8
