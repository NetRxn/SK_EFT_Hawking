/-
# The real-place Hilbert symbol — first brick of the Hasse–Minkowski development

The Hilbert symbol `(a,b)_v ∈ {±1}` measures whether `z² = a x² + b y²` has a nontrivial solution over
the completion `ℚ_v`. This file builds the **real place** `v = ∞`, where the symbol has the elementary
closed form `(a,b)_∞ = -1 ⟺ a < 0 ∧ b < 0` (otherwise one of `a, b ≥ 0` lets `ax² + by² = z²` be solved).

This is the easiest of the local symbols and is fully elementary. The p-adic symbols (`(a,b)_p` via the
Legendre/Jacobi closed form) and the product formula `∏_v (a,b)_v = 1` (≡ quadratic reciprocity) are the
remaining frontier toward [HM-LG] (local–global Hasse–Minkowski), the sole classical input still needed for
`8 ∣ σ` on *indefinite* even unimodular forms (the definite case is discharged by theta-modularity:
`ThetaDefiniteDischarge.eight_dvd_latticeSig_of_definite`).

All theorems kernel-pure, no axioms.
-/

import Mathlib

namespace SKEFTHawking.HilbertSymbol

/-- The **real (infinite-place) Hilbert symbol** `(a,b)_∞`: equals `-1` exactly when both arguments are
negative, and `1` otherwise. Captures real solvability of `z² = a x² + b y²`. -/
noncomputable def hilbertReal (a b : ℝ) : ℤ := if a < 0 ∧ b < 0 then -1 else 1

@[simp] theorem hilbertReal_neg_neg {a b : ℝ} (ha : a < 0) (hb : b < 0) : hilbertReal a b = -1 := by
  simp [hilbertReal, ha, hb]

/-- The symbol takes values in `{±1}`. -/
theorem hilbertReal_mem (a b : ℝ) : hilbertReal a b = 1 ∨ hilbertReal a b = -1 := by
  unfold hilbertReal; split_ifs <;> simp

/-- The symbol is never zero. -/
theorem hilbertReal_ne_zero (a b : ℝ) : hilbertReal a b ≠ 0 := by
  rcases hilbertReal_mem a b with h | h <;> simp [h]

/-- The symbol squares to `1`. -/
theorem hilbertReal_sq (a b : ℝ) : hilbertReal a b * hilbertReal a b = 1 := by
  rcases hilbertReal_mem a b with h | h <;> simp [h]

/-- **Symmetry:** `(a,b)_∞ = (b,a)_∞`. -/
theorem hilbertReal_comm (a b : ℝ) : hilbertReal a b = hilbertReal b a := by
  simp only [hilbertReal, and_comm]

/-- A nonnegative left argument gives symbol `1`. -/
theorem hilbertReal_of_nonneg_left {a : ℝ} (ha : 0 ≤ a) (b : ℝ) : hilbertReal a b = 1 := by
  simp [hilbertReal, not_lt.mpr ha]

/-- A nonnegative right argument gives symbol `1`. -/
theorem hilbertReal_of_nonneg_right (a : ℝ) {b : ℝ} (hb : 0 ≤ b) : hilbertReal a b = 1 := by
  rw [hilbertReal_comm]; exact hilbertReal_of_nonneg_left hb a

@[simp] theorem hilbertReal_one_left (b : ℝ) : hilbertReal 1 b = 1 :=
  hilbertReal_of_nonneg_left zero_le_one b

@[simp] theorem hilbertReal_one_right (a : ℝ) : hilbertReal a 1 = 1 :=
  hilbertReal_of_nonneg_right a zero_le_one

/-- **Bimultiplicativity in the first argument** (for nonzero arguments). -/
theorem hilbertReal_mul_left {a₁ a₂ b : ℝ} (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) :
    hilbertReal (a₁ * a₂) b = hilbertReal a₁ b * hilbertReal a₂ b := by
  rcases le_or_gt 0 b with hb | hb
  · rw [hilbertReal_of_nonneg_right _ hb, hilbertReal_of_nonneg_right _ hb,
      hilbertReal_of_nonneg_right _ hb, one_mul]
  · rcases lt_or_gt_of_ne ha₁ with h₁ | h₁ <;> rcases lt_or_gt_of_ne ha₂ with h₂ | h₂
    · rw [hilbertReal_neg_neg h₁ hb, hilbertReal_neg_neg h₂ hb,
        hilbertReal_of_nonneg_left (le_of_lt (mul_pos_of_neg_of_neg h₁ h₂)) b]; ring
    · rw [hilbertReal_neg_neg h₁ hb, hilbertReal_of_nonneg_left h₂.le b,
        hilbertReal_neg_neg (mul_neg_of_neg_of_pos h₁ h₂) hb]; ring
    · rw [hilbertReal_neg_neg h₂ hb, hilbertReal_of_nonneg_left h₁.le b,
        hilbertReal_neg_neg (mul_neg_of_pos_of_neg h₁ h₂) hb]; ring
    · rw [hilbertReal_of_nonneg_left h₁.le b, hilbertReal_of_nonneg_left h₂.le b,
        hilbertReal_of_nonneg_left (le_of_lt (mul_pos h₁ h₂)) b]; ring

/-- **Bimultiplicativity in the second argument** (for nonzero arguments). -/
theorem hilbertReal_mul_right {a b₁ b₂ : ℝ} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    hilbertReal a (b₁ * b₂) = hilbertReal a b₁ * hilbertReal a b₂ := by
  rw [hilbertReal_comm, hilbertReal_mul_left hb₁ hb₂, hilbertReal_comm a b₁, hilbertReal_comm a b₂]

/-- **`(a, -a)_∞ = 1`** — the Steinberg relation at the real place. -/
theorem hilbertReal_self_neg {a : ℝ} (ha : a ≠ 0) : hilbertReal a (-a) = 1 := by
  rcases lt_or_gt_of_ne ha with h | h
  · exact hilbertReal_of_nonneg_right a (by linarith)
  · exact hilbertReal_of_nonneg_left h.le (-a)

/-- **`(a, 1-a)_∞ = 1`** — the Steinberg relation. Over ℝ at least one of `a`, `1-a` is positive. -/
theorem hilbertReal_one_sub {a : ℝ} : hilbertReal a (1 - a) = 1 := by
  rcases le_or_gt 0 a with ha | ha
  · exact hilbertReal_of_nonneg_left ha (1 - a)
  · exact hilbertReal_of_nonneg_right a (by linarith)

/-- **Real solvability criterion.** `(a,b)_∞ = 1` iff `z² = a x² + b y²` has a nontrivial real solution.
The forward direction packages the witness; the reverse shows two negative coefficients force triviality. -/
theorem hilbertReal_eq_one_iff {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertReal a b = 1 ↔ ∃ x y z : ℝ, (x, y, z) ≠ 0 ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2 := by
  constructor
  · intro hsym
    rcases le_or_gt 0 a with hapos | haneg
    · exact ⟨1, 0, Real.sqrt a, by simp, by rw [Real.sq_sqrt hapos]; ring⟩
    · rcases le_or_gt 0 b with hbpos | hbneg
      · exact ⟨0, 1, Real.sqrt b, by simp, by rw [Real.sq_sqrt hbpos]; ring⟩
      · rw [hilbertReal_neg_neg haneg hbneg] at hsym; norm_num at hsym
  · rintro ⟨x, y, z, hne, hz⟩
    by_contra h
    rcases hilbertReal_mem a b with h1 | h1
    · exact h h1
    · have hcond : a < 0 ∧ b < 0 := by
        by_contra hc; rw [hilbertReal, if_neg hc] at h1; norm_num at h1
      obtain ⟨haneg, hbneg⟩ := hcond
      have hax : a * x ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg haneg.le (sq_nonneg x)
      have hby : b * y ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hbneg.le (sq_nonneg y)
      have hzsq : z ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg z]) (sq_nonneg z)
      have hax0 : a * x ^ 2 = 0 := le_antisymm hax (by nlinarith)
      have hby0 : b * y ^ 2 = 0 := le_antisymm hby (by nlinarith)
      have hx0 : x = 0 := by
        rcases mul_eq_zero.mp hax0 with hh | hh
        · exact absurd hh ha
        · exact pow_eq_zero_iff (by norm_num) |>.mp hh
      have hy0 : y = 0 := by
        rcases mul_eq_zero.mp hby0 with hh | hh
        · exact absurd hh hb
        · exact pow_eq_zero_iff (by norm_num) |>.mp hh
      have hz0 : z = 0 := pow_eq_zero_iff (by norm_num) |>.mp hzsq
      exact hne (by rw [hx0, hy0, hz0]; rfl)

end SKEFTHawking.HilbertSymbol
