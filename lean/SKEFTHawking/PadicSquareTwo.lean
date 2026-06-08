/-
# 2-adic local isotropy of rank-≥5 diagonal forms ([HM] p=2 frontier)

The odd-`p` rank-≥5 local isotropy (`PadicSquare.exists_diag_nary_zero_odd_padic`) reduces a diagonal form
to a ternary unit sub-block, which is isotropic over `ℚ_p` by finite-field universality + Hensel. **This
fails at `p = 2`**: the unit ternary `⟨1,1,1⟩` is anisotropic over `ℚ₂` (`(-1,-1)₂ = -1`). The genuine
`2`-adic fact "every rank-≥5 form over `ℚ₂` is isotropic" needs the rank-4 anisotropic classification, for
which Mathlib has no substrate.

This file builds it via a route that avoids both square-class counting and multivariate Hensel:

1. **Normalize** each coefficient to valuation `0` or `1` (unit or `2·unit`) by the square substitution
   `xᵢ ↦ 2^(-⌊vᵢ/2⌋) yᵢ` (reusing the valuation arithmetic of `PadicSquare`), then **halve** the whole form
   if necessary so that at least three coefficients are units (`max(#val0, #val1) ≥ 3`).
2. Solve `∑ aᵢ xᵢ² ≡ 0 (mod 8)` with one *unit* coordinate odd — a **finite combinatorial fact** decided in
   the kernel over `ZMod 8` (no `native_decide`). This is `mod8_quinary_solvable` below.
3. The mod-8 solution forces the freeze-and-solve residue `c ≡ 1 (mod 8)` at the odd unit coordinate, hence
   an **exact square root** via `PadicSquare.isSquare_iff_toZModPow_three_eq_one`. No multivariate Hensel.

This file ships **step 2** (the finite combinatorial core, kernel-`decide`-tractable). Steps 1 and 3 (the
`ℤ₂` lift and the valuation normalization) build on top.

Kernel-pure, no axioms, no `native_decide`, no `maxHeartbeats`.
-/

import Mathlib
import SKEFTHawking.PadicSquare

namespace SKEFTHawking

open scoped BigOperators

/-! ## The finite mod-8 combinatorial core

Squares in `ZMod 8` lie in `{0,1,4}` (value `1` iff the root is odd). After normalizing a rank-5 diagonal
form so that coordinates `0,1,2` carry unit coefficients (residues in `{1,3,5,7}`) and coordinates `3,4`
carry unit-or-two-unit coefficients (residues in `{1,2,3,5,6,7}` = nonzero, not `4`), the form has a
primitive zero mod 8 with coordinate `0` odd. -/

/-- A `ZMod 8` unit residue is one of `1,3,5,7`; package it as a `Fin 4` index into `![1,3,5,7]`. -/
theorem exists_fin4_of_unit8 {u : ZMod 8} (h : IsUnit u) : ∃ i : Fin 4, ![1, 3, 5, 7] i = u := by
  have : u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7 := by revert h; revert u; decide
  rcases this with h | h | h | h
  exacts [⟨0, by simp [h]⟩, ⟨1, by simp [h]⟩, ⟨2, by simp [h]⟩, ⟨3, by simp [h]⟩]

/-- A nonzero `ZMod 8` residue other than `4` is one of `1,2,3,5,6,7` (a unit or a two-unit `2·unit`);
package it as a `Fin 6` index into `![1,2,3,5,6,7]`. -/
theorem exists_fin6_of_nz {u : ZMod 8} (h0 : u ≠ 0) (h4 : u ≠ 4) :
    ∃ a : Fin 6, ![1, 2, 3, 5, 6, 7] a = u := by
  have : u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 5 ∨ u = 6 ∨ u = 7 := by revert h0 h4; revert u; decide
  rcases this with h | h | h | h | h | h
  exacts [⟨0, by simp [h]⟩, ⟨1, by simp [h]⟩, ⟨2, by simp [h]⟩, ⟨3, by simp [h]⟩,
    ⟨4, by simp [h]⟩, ⟨5, by simp [h]⟩]

/-- **The finite combinatorial core (kernel `decide`).** For any unit residues `![1,3,5,7] i,j,k` and any
unit-or-two-unit residues `![1,2,3,5,6,7] a,b`, there are square-root representatives `![0,1,2] q,r,s,t`
making the diagonal form vanish mod 8 with the first coordinate fixed to `1` (odd). The `0/1/2`
representatives realize the three square classes `0²=0, 1²=1, 2²=4` in `ZMod 8`. -/
theorem mod8_core (i j k : Fin 4) (a b : Fin 6) : ∃ q r s t : Fin 3,
    (![1, 3, 5, 7] i) * 1
    + (![1, 3, 5, 7] j) * (![0, 1, 2] q) ^ 2
    + (![1, 3, 5, 7] k) * (![0, 1, 2] r) ^ 2
    + (![1, 2, 3, 5, 6, 7] a) * (![0, 1, 2] s) ^ 2
    + (![1, 2, 3, 5, 6, 7] b) * (![0, 1, 2] t) ^ 2 = (0 : ZMod 8) := by decide +revert

/-- **Rank-5 mod-8 solvability (consumable form).** A diagonal form `∑ uᵢ xᵢ²` over `ZMod 8` whose first
three coefficients are units and whose last two are nonzero and `≠ 4` (i.e. units or two-units) has a zero
with `x 0 = 1` (so the zeroth coordinate is odd — the coordinate at which the lift to `ℤ₂` solves an exact
unit square root). Bridges `mod8_core` through the residue-indexing helpers. -/
theorem mod8_quinary_solvable (u : Fin 5 → ZMod 8)
    (hu0 : IsUnit (u 0)) (hu1 : IsUnit (u 1)) (hu2 : IsUnit (u 2))
    (h30 : u 3 ≠ 0) (h34 : u 3 ≠ 4) (h40 : u 4 ≠ 0) (h44 : u 4 ≠ 4) :
    ∃ x : Fin 5 → ZMod 8, x 0 = 1 ∧ ∑ i, u i * (x i) ^ 2 = 0 := by
  obtain ⟨i, hi⟩ := exists_fin4_of_unit8 hu0
  obtain ⟨j, hj⟩ := exists_fin4_of_unit8 hu1
  obtain ⟨k, hk⟩ := exists_fin4_of_unit8 hu2
  obtain ⟨a, ha⟩ := exists_fin6_of_nz h30 h34
  obtain ⟨b, hb⟩ := exists_fin6_of_nz h40 h44
  obtain ⟨q, r, s, t, heq⟩ := mod8_core i j k a b
  rw [hi, hj, hk, ha, hb] at heq
  refine ⟨![1, ![0, 1, 2] q, ![0, 1, 2] r, ![0, 1, 2] s, ![0, 1, 2] t], rfl, ?_⟩
  simp only [Fin.sum_univ_five]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons]
  linear_combination heq

/-! ## The `ℤ₂` lift: mod-8 solution → exact zero

The mod-8 solution lifts to an exact `ℤ₂` zero with **no multivariate Hensel**: freeze coordinates `1..4`
at integer lifts of their residues, then solve coordinate `0` (a unit, odd in the mod-8 solution) as an
exact square root. The mod-8 equation forces the freeze-and-solve residue `c ≡ 1 (mod 8)`, so
`isSquare_iff_toZModPow_three_eq_one` provides the root directly. -/

open PadicInt

/-- A `2`-adic integer whose `mod 8` residue is a unit is itself a unit. (Contrapositive: a non-unit is
divisible by `2`, so its residue is even, hence a non-unit of `ZMod 8`.) -/
theorem isUnit_of_isUnit_toZModPow {x : ℤ_[2]} (h : IsUnit (PadicInt.toZModPow 3 x)) : IsUnit x := by
  rw [PadicInt.isUnit_iff]
  by_contra hne
  have hlt : ‖x‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one x) hne
  obtain ⟨y, rfl⟩ := (PadicInt.norm_lt_one_iff_dvd x).mp hlt
  rw [map_mul] at h
  have h2 : IsUnit (PadicInt.toZModPow 3 ((2 : ℕ) : ℤ_[2])) := isUnit_of_mul_isUnit_left h
  rw [map_natCast] at h2
  revert h2; decide

/-- **Rank-5 `ℤ₂` lift (unit-normalized form).** For `a : Fin 5 → ℤ₂` with the first three coefficients
units and the last two of residue `≠ 0, ≠ 4` (i.e. units or two-units), the diagonal form `∑ aᵢ xᵢ²` has a
nontrivial `ℤ₂` zero. The mod-8 core (`mod8_quinary_solvable`) supplies a primitive residue solution with
coordinate `0` odd; freezing coordinates `1..4` at the integer lifts of their residues, coordinate `0`
solves an exact unit square root (`isSquare_iff_toZModPow_three_eq_one`), since the residue equation forces
`-R/a₀ ≡ 1 (mod 8)`. -/
theorem quinary_lift_2adic (a : Fin 5 → ℤ_[2])
    (hu0 : IsUnit (a 0)) (hu1 : IsUnit (a 1)) (hu2 : IsUnit (a 2))
    (h30 : toZModPow 3 (a 3) ≠ 0) (h34 : toZModPow 3 (a 3) ≠ 4)
    (h40 : toZModPow 3 (a 4) ≠ 0) (h44 : toZModPow 3 (a 4) ≠ 4) :
    ∃ x : Fin 5 → ℤ_[2], x 0 ≠ 0 ∧ ∑ i, a i * (x i) ^ 2 = 0 := by
  set r : Fin 5 → ZMod 8 := fun i => toZModPow 3 (a i) with hr
  have ru0 : IsUnit (r 0) := hu0.map _
  have ru1 : IsUnit (r 1) := hu1.map _
  have ru2 : IsUnit (r 2) := hu2.map _
  obtain ⟨x8, hx80, hx8eq⟩ := mod8_quinary_solvable r ru0 ru1 ru2 h30 h34 h40 h44
  set y : Fin 5 → ℤ_[2] := fun i => ((x8 i).val : ℤ_[2]) with hy
  have hyr : ∀ i, toZModPow 3 (y i) = x8 i := by
    intro i; rw [hy]; simp only; rw [map_natCast]; exact ZMod.natCast_rightInverse (x8 i)
  set R : ℤ_[2] := a 1 * (y 1) ^ 2 + a 2 * (y 2) ^ 2 + a 3 * (y 3) ^ 2 + a 4 * (y 4) ^ 2 with hR
  have hRres : toZModPow 3 R = - r 0 := by
    have hsum := hx8eq
    rw [Fin.sum_univ_five, hx80] at hsum
    rw [hR]
    simp only [map_add, map_mul, map_pow, hyr]
    have e0 : toZModPow 3 (a 1) = r 1 := rfl
    have e1 : toZModPow 3 (a 2) = r 2 := rfl
    have e2 : toZModPow 3 (a 3) = r 3 := rfl
    have e3 : toZModPow 3 (a 4) = r 4 := rfl
    rw [e0, e1, e2, e3]
    linear_combination hsum
  have hRunit : IsUnit R := isUnit_of_isUnit_toZModPow (by rw [hRres]; exact ru0.neg)
  set c : ℤ_[2] := (-R) * ↑hu0.unit⁻¹ with hc
  have ha0inv : a 0 * ↑hu0.unit⁻¹ = 1 := by
    have h1 := hu0.unit.mul_inv
    rw [hu0.unit_spec] at h1; exact h1
  have hac : a 0 * c = -R := by rw [hc]; linear_combination (-R) * ha0inv
  have hcres : toZModPow 3 c = 1 := by
    have hmul : toZModPow 3 (a 0 * c) = toZModPow 3 (-R) := by rw [hac]
    rw [map_mul, map_neg, hRres, neg_neg] at hmul
    have : r 0 * toZModPow 3 c = r 0 * 1 := by rw [hmul, mul_one]
    exact ru0.mul_left_cancel this
  have hcunit : IsUnit c := by rw [hc]; exact hRunit.neg.mul hu0.unit⁻¹.isUnit
  obtain ⟨w, hw⟩ := (isSquare_iff_toZModPow_three_eq_one hcunit).mpr hcres
  have hwunit : IsUnit w := by rw [hw] at hcunit; exact isUnit_of_mul_isUnit_left hcunit
  have hfin : a 0 * w ^ 2 = -R := by rw [pow_two, ← hw]; exact hac
  refine ⟨![w, y 1, y 2, y 3, y 4], ?_, ?_⟩
  · simp only [Matrix.cons_val_zero]; exact hwunit.ne_zero
  · simp only [Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons]
    rw [hR] at hfin
    linear_combination hfin

end SKEFTHawking
