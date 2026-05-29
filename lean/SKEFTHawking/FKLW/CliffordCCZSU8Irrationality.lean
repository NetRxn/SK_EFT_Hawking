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

end SKEFTHawking.FKLW.CliffordCCZSU8
