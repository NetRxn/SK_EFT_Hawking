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

end SKEFTHawking
