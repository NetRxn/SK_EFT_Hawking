/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 1(c), increment 1 — `ℤ[√2]` unit theory: doubly-positive units are squares

Ross–Selinger arXiv:1403.2975v3 **Lemma C.2** ("the units of `ℤ[√2]` are `(−1)ⁿλᵐ`; a unit is
doubly positive iff it is a square", cited there to Selinger arXiv:1212.6253 Lemma 10). This is
the unit input that **Lemma C.16** (the solvability iff: `t†t = ξ` solvable ⟺ `ξ` doubly positive
∧ †-decomposable) consumes: from `ξ = u·t†t` with `ξ, t†t` doubly positive, the unit `u` is
doubly positive, hence `u = v²`, hence `ξ = (vt)†(vt)`.

We prove the consumed direction directly — **every doubly-positive unit of `ℤ[√2]` is a square**
— by the classical fundamental-unit descent, without classifying the unit group: a norm-one unit
with `1 ≤ φ(u)` and `im > 0` satisfies `im(u·λ⁻²) ∈ [0, im(u))` (where `λ = 1 + √2`,
`λ⁻² = 3 − 2√2`), so induction on `im.natAbs` terminates; the `φ(u) < 1` branch flips through
`star` (which preserves the measure and is handled inside the recursion at the strictly smaller
measure, or at the top level where no descent is needed).

Positivity is via the real embedding `φ = Zsqrtd.toReal`: `ξ ≥ 0` means `0 ≤ φ ξ` — the paper's
order on `ℤ[√2] ⊂ ℝ` (Definition C.1 "doubly positive": `ξ ≥ 0 ∧ ξ• ≥ 0`; for units strict).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide`. Kernel-pure `{propext, Classical.choice, Quot.sound}`.

## References

  * Ross–Selinger, arXiv:1403.2975v3, Appendix C.1 (Definition C.1, Lemma C.2).
  * Selinger, arXiv:1212.6253, Lemma 10 (the original unit classification).
-/

import SKEFTHawking.FKLW.RossSelinger.Zsqrt2
import Mathlib.Algebra.Group.Even

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

/-! ### The real embedding and its star arithmetic -/

/-- The real embedding `ℤ[√2] → ℝ`, `a + b√2 ↦ a + b·√2`. -/
noncomputable def zsqrt2ToReal : Zsqrtd 2 →+* ℝ := Zsqrtd.toReal (by norm_num)

theorem zsqrt2ToReal_apply (z : Zsqrtd 2) :
    zsqrt2ToReal z = (z.re : ℝ) + (z.im : ℝ) * Real.sqrt 2 := by
  show Zsqrtd.toReal _ z = _
  rw [Zsqrtd.toReal_apply]
  norm_num

theorem zsqrt2ToReal_add_star (u : Zsqrtd 2) :
    zsqrt2ToReal u + zsqrt2ToReal (star u) = 2 * (u.re : ℝ) := by
  rw [zsqrt2ToReal_apply, zsqrt2ToReal_apply, Zsqrtd.re_star, Zsqrtd.im_star]
  push_cast
  ring

theorem zsqrt2ToReal_sub_star (u : Zsqrtd 2) :
    zsqrt2ToReal u - zsqrt2ToReal (star u) = 2 * (u.im : ℝ) * Real.sqrt 2 := by
  rw [zsqrt2ToReal_apply, zsqrt2ToReal_apply, Zsqrtd.re_star, Zsqrtd.im_star]
  push_cast
  ring

/-- A norm-one element pairs with its conjugate to `1` under the real embedding. -/
theorem zsqrt2ToReal_mul_star {u : Zsqrtd 2} (h : Zsqrtd.norm u = 1) :
    zsqrt2ToReal u * zsqrt2ToReal (star u) = 1 := by
  rw [← map_mul, ← Zsqrtd.norm_eq_mul_conj, h]
  exact_mod_cast map_one zsqrt2ToReal

/-- **Positive-positive units have norm `+1`** (the norm `−1` case has a negative embedding
product). -/
theorem zsqrt2_unit_norm_eq_one {u : Zsqrtd 2} (hu : IsUnit u)
    (h1 : 0 < zsqrt2ToReal u) (h2 : 0 < zsqrt2ToReal (star u)) : Zsqrtd.norm u = 1 := by
  have habs : (Zsqrtd.norm u).natAbs = 1 := Zsqrtd.norm_eq_one_iff.mpr hu
  rcases Int.natAbs_eq_iff.mp habs with h | h
  · exact h
  · exfalso
    have hprod : zsqrt2ToReal u * zsqrt2ToReal (star u) = -1 := by
      rw [← map_mul, ← Zsqrtd.norm_eq_mul_conj, h]
      push_cast
      exact map_neg zsqrt2ToReal 1 ▸ by rw [map_one]
    nlinarith [mul_pos h1 h2]

/-! ### The fundamental-unit gadgets -/

/-- `λ = 1 + √2`, the fundamental unit. -/
def zsqrt2Lam : Zsqrtd 2 := ⟨1, 1⟩

/-- `λ⁻² = 3 − 2√2`, the descent multiplier. -/
def zsqrt2LamSqInv : Zsqrtd 2 := ⟨3, -2⟩

theorem zsqrt2LamSqInv_mul_lam_sq : zsqrt2LamSqInv * (zsqrt2Lam * zsqrt2Lam) = 1 := by decide

theorem zsqrt2_isUnit_lamSqInv : IsUnit zsqrt2LamSqInv :=
  IsUnit.of_mul_eq_one _ zsqrt2LamSqInv_mul_lam_sq

theorem zsqrt2ToReal_lamSqInv_pos : 0 < zsqrt2ToReal zsqrt2LamSqInv := by
  rw [zsqrt2ToReal_apply]
  show (0 : ℝ) < ((3 : ℤ) : ℝ) + ((-2 : ℤ) : ℝ) * Real.sqrt 2
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hnn := Real.sqrt_nonneg 2
  push_cast
  nlinarith

theorem zsqrt2ToReal_star_lamSqInv_pos : 0 < zsqrt2ToReal (star zsqrt2LamSqInv) := by
  rw [zsqrt2ToReal_apply, Zsqrtd.re_star, Zsqrtd.im_star]
  simp only [show zsqrt2LamSqInv.re = 3 from rfl, show zsqrt2LamSqInv.im = -2 from rfl]
  have hnn := Real.sqrt_nonneg 2
  push_cast
  nlinarith

/-! ### The base case and the descent -/

/-- A real (im-zero) norm-one element with `1 ≤ φ` is `1` — hence a square. -/
theorem zsqrt2_isSquare_of_im_zero {u : Zsqrtd 2} (him : u.im = 0)
    (hnorm : Zsqrtd.norm u = 1) (hge : 1 ≤ zsqrt2ToReal u) : IsSquare u := by
  have hsq : u.re * u.re = 1 := by
    have hd := Zsqrtd.norm_def u
    rw [hnorm, him] at hd
    linarith
  have hφ : zsqrt2ToReal u = (u.re : ℝ) := by
    rw [zsqrt2ToReal_apply, him]
    push_cast
    ring
  have hre : u.re = 1 := by
    rcases mul_self_eq_one_iff.mp hsq with h | h
    · exact h
    · exfalso
      rw [hφ, h] at hge
      norm_num at hge
  have : u = 1 := by
    ext
    · exact hre
    · exact him
  rw [this]
  exact ⟨1, (one_mul 1).symm⟩

/-- **The descent core**: norm-one positive-positive units with `1 ≤ φ u` and `im`-measure
bounded by `n` are squares (induction on `n`; the `λ⁻²`-step strictly shrinks the measure, and
the `φ < 1` branch flips through `star` at the already-smaller measure). -/
theorem zsqrt2_isSquare_aux : ∀ n : ℕ, ∀ u : Zsqrtd 2, u.im.natAbs ≤ n → IsUnit u →
    0 < zsqrt2ToReal u → 0 < zsqrt2ToReal (star u) → 1 ≤ zsqrt2ToReal u → IsSquare u := by
  intro n
  induction n with
  | zero =>
    intro u hm hu h1 h2 hge
    have him : u.im = 0 := by omega
    exact zsqrt2_isSquare_of_im_zero him (zsqrt2_unit_norm_eq_one hu h1 h2) hge
  | succ n ih =>
    intro u hm hu h1 h2 hge
    have hnorm : Zsqrtd.norm u = 1 := zsqrt2_unit_norm_eq_one hu h1 h2
    by_cases him0 : u.im = 0
    · exact zsqrt2_isSquare_of_im_zero him0 hnorm hge
    -- the conjugate embedding is in (0, 1]
    have hprod : zsqrt2ToReal u * zsqrt2ToReal (star u) = 1 := zsqrt2ToReal_mul_star hnorm
    have hstar_le : zsqrt2ToReal (star u) ≤ 1 := by nlinarith
    -- coordinate facts: im ≥ 1, re ≥ 1, re² − 2im² = 1
    have hsqrt_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have him_nonneg : 0 ≤ u.im := by
      by_contra hneg
      have hb' : u.im ≤ -1 := by omega
      have hb : (u.im : ℝ) ≤ -1 := by exact_mod_cast hb'
      have hdiff := zsqrt2ToReal_sub_star u
      nlinarith [mul_le_mul_of_nonneg_right hb hsqrt_pos.le]
    have him_pos : 1 ≤ u.im := by omega
    have hre_pos : 1 ≤ u.re := by
      have hsum := zsqrt2ToReal_add_star u
      have hR : (0 : ℝ) < (u.re : ℝ) := by nlinarith
      have h0 : 0 < u.re := by exact_mod_cast hR
      omega
    have hcoord : u.re * u.re - 2 * (u.im * u.im) = 1 := by
      have hd := Zsqrtd.norm_def u
      rw [hnorm] at hd
      linarith
    -- im = 1 is impossible (re² = 3 has no integer solution)
    have him2 : 2 ≤ u.im := by
      rcases (by omega : u.im = 1 ∨ 2 ≤ u.im) with h | h
      · exfalso
        rw [h] at hcoord
        have h3 : u.re * u.re = 3 := by linarith
        rcases (by omega : u.re = 1 ∨ 2 ≤ u.re) with h' | h'
        · rw [h'] at h3
          norm_num at h3
        · nlinarith
      · exact h
    -- the descent coordinates
    have hab : u.im < u.re := by nlinarith
    have h2a3b : 2 * u.re ≤ 3 * u.im := by nlinarith
    set u' : Zsqrtd 2 := u * zsqrt2LamSqInv with hu'def
    have hre' : u'.re = 3 * u.re - 4 * u.im := by
      rw [hu'def, Zsqrtd.re_mul]
      simp only [show zsqrt2LamSqInv.re = 3 from rfl, show zsqrt2LamSqInv.im = -2 from rfl]
      ring
    have him' : u'.im = 3 * u.im - 2 * u.re := by
      rw [hu'def, Zsqrtd.im_mul]
      simp only [show zsqrt2LamSqInv.re = 3 from rfl, show zsqrt2LamSqInv.im = -2 from rfl]
      ring
    have hmeas : u'.im.natAbs ≤ n := by
      rw [him']
      omega
    have hu'unit : IsUnit u' := hu.mul zsqrt2_isUnit_lamSqInv
    have h1' : 0 < zsqrt2ToReal u' := by
      rw [hu'def, map_mul]
      exact mul_pos h1 zsqrt2ToReal_lamSqInv_pos
    have h2' : 0 < zsqrt2ToReal (star u') := by
      rw [hu'def, star_mul', map_mul]
      exact mul_pos h2 zsqrt2ToReal_star_lamSqInv_pos
    -- recover `u` from a square of `u'`
    have hback : u = u' * (zsqrt2Lam * zsqrt2Lam) := by
      rw [hu'def, mul_assoc, zsqrt2LamSqInv_mul_lam_sq, mul_one]
    by_cases hge' : 1 ≤ zsqrt2ToReal u'
    · obtain ⟨v, hv⟩ := ih u' hmeas hu'unit h1' h2' hge'
      exact ⟨v * zsqrt2Lam, by rw [hback, hv]; ring⟩
    · -- flip through star at the smaller measure
      have hnorm' : Zsqrtd.norm u' = 1 := zsqrt2_unit_norm_eq_one hu'unit h1' h2'
      have hprod' := zsqrt2ToReal_mul_star hnorm'
      have hge'' : 1 ≤ zsqrt2ToReal (star u') := by nlinarith [not_le.mp hge']
      have hu''unit : IsUnit (star u') :=
        IsUnit.of_mul_eq_one u' (by
          rw [mul_comm, ← Zsqrtd.norm_eq_mul_conj, hnorm']
          exact Int.cast_one)
      have hmeas' : (star u').im.natAbs ≤ n := by
        rw [Zsqrtd.im_star]
        omega
      obtain ⟨v, hv⟩ := ih (star u') hmeas' hu''unit h2'
        (by rw [star_star]; exact h1') hge''
      have hu'eq : u' = star v * star v := by
        rw [← star_star u', hv, star_mul']
      exact ⟨star v * zsqrt2Lam, by rw [hback, hu'eq]; ring⟩

/-- **Doubly-positive units of `ℤ[√2]` are squares** (Ross–Selinger arXiv:1403.2975v3 Lemma C.2
= Selinger arXiv:1212.6253 Lemma 10, the direction Lemma C.16 consumes). -/
theorem zsqrt2_isSquare_of_unit_pos_pos {u : Zsqrtd 2} (hu : IsUnit u)
    (h1 : 0 < zsqrt2ToReal u) (h2 : 0 < zsqrt2ToReal (star u)) : IsSquare u := by
  by_cases hge : 1 ≤ zsqrt2ToReal u
  · exact zsqrt2_isSquare_aux u.im.natAbs u le_rfl hu h1 h2 hge
  · have hnorm : Zsqrtd.norm u = 1 := zsqrt2_unit_norm_eq_one hu h1 h2
    have hprod : zsqrt2ToReal u * zsqrt2ToReal (star u) = 1 := zsqrt2ToReal_mul_star hnorm
    have hge' : 1 ≤ zsqrt2ToReal (star u) := by nlinarith [not_le.mp hge]
    have hu' : IsUnit (star u) :=
      IsUnit.of_mul_eq_one u (by
        rw [mul_comm, ← Zsqrtd.norm_eq_mul_conj, hnorm]
        exact Int.cast_one)
    obtain ⟨v, hv⟩ := zsqrt2_isSquare_aux (star u).im.natAbs (star u) le_rfl hu'
      h2 (by rw [star_star]; exact h1) hge'
    exact ⟨star v, by rw [← star_star u, hv, star_mul']⟩

/-- The converse (easy direction of Lemma C.2): squares are doubly nonneg under the embedding. -/
theorem zsqrt2_toReal_nonneg_of_isSquare {u : Zsqrtd 2} (h : IsSquare u) :
    0 ≤ zsqrt2ToReal u ∧ 0 ≤ zsqrt2ToReal (star u) := by
  obtain ⟨v, rfl⟩ := h
  constructor
  · rw [map_mul]
    exact mul_self_nonneg _
  · rw [star_mul', map_mul]
    exact mul_self_nonneg _

end SKEFTHawking.RossSelinger
