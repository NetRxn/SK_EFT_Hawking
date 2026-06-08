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

/-! ## Normalization glue: reorder + residue facts

To feed `quinary_lift_2adic`, the rank-5 form is normalized so that every coefficient has valuation `0` or
`1` (unit or two-unit) and the three units sit at coordinates `0,1,2`. The permutation glue reorders three
chosen unit-coordinates to the front; the residue helper certifies the `≠ 0, ≠ 4` hypotheses. -/

/-- **Move three distinct indices to the front.** For distinct `i,j,k : Fin (m+3)` there is a coordinate
permutation sending `0 ↦ i, 1 ↦ j, 2 ↦ k` (three transpositions). Extends `exists_equiv_zero_one`. -/
theorem exists_equiv_zero_one_two {m : ℕ} (i j k : Fin (m + 3))
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ e : Fin (m + 3) ≃ Fin (m + 3), e 0 = i ∧ e 1 = j ∧ e 2 = k := by
  obtain ⟨e1, he10, he11⟩ : ∃ e : Fin (m + 3) ≃ Fin (m + 3), e 0 = i ∧ e 1 = j := by
    set s := Equiv.swap (0 : Fin (m + 3)) i with hs
    set a := s.symm j with ha
    have ha0 : a ≠ 0 := by
      rw [ha]; intro h; apply hij
      have h1 : s (s.symm j) = j := s.apply_symm_apply j
      rw [h, hs, Equiv.swap_apply_left] at h1; exact h1
    set t := Equiv.swap (1 : Fin (m + 3)) a with ht
    refine ⟨t.trans s, ?_, ?_⟩
    · show s (t 0) = i
      have ht0 : t 0 = 0 := by rw [ht, Equiv.swap_apply_of_ne_of_ne (by norm_num) (Ne.symm ha0)]
      rw [ht0, hs, Equiv.swap_apply_left]
    · show s (t 1) = j
      have ht1 : t 1 = a := by rw [ht]; exact Equiv.swap_apply_left 1 a
      rw [ht1, ha]; exact s.apply_symm_apply j
  set p := e1.symm k with hp
  have hp0 : p ≠ 0 := by rw [hp]; intro h; apply hik; rw [← he10, ← h, e1.apply_symm_apply]
  have hp1 : p ≠ 1 := by rw [hp]; intro h; apply hjk; rw [← he11, ← h, e1.apply_symm_apply]
  have h02 : (0 : Fin (m + 3)) ≠ 2 := by apply Fin.ne_of_val_ne; rw [Fin.val_zero, Fin.val_two]; omega
  have h12 : (1 : Fin (m + 3)) ≠ 2 := by apply Fin.ne_of_val_ne; rw [Fin.val_one, Fin.val_two]; omega
  set sw := Equiv.swap (2 : Fin (m + 3)) p with hsw
  refine ⟨sw.trans e1, ?_, ?_, ?_⟩
  · show e1 (sw 0) = i
    rw [hsw, Equiv.swap_apply_of_ne_of_ne h02 (Ne.symm hp0)]; exact he10
  · show e1 (sw 1) = j
    rw [hsw, Equiv.swap_apply_of_ne_of_ne h12 (Ne.symm hp1)]; exact he11
  · show e1 (sw 2) = k
    rw [hsw, Equiv.swap_apply_left, hp, e1.apply_symm_apply]

/-- A `2`-adic integer of valuation `0` or `1` (norm `1` or `1/2`) has residue mod `8` neither `0` nor `4`
(it is a unit or a two-unit). This certifies the last-two-coordinate hypotheses of `quinary_lift_2adic`. -/
theorem toZModPow3_ne_zero_four_of_norm {x : ℤ_[2]} (hx : ‖x‖ = 1 ∨ ‖x‖ = 2⁻¹) :
    toZModPow 3 x ≠ 0 ∧ toZModPow 3 x ≠ 4 := by
  haveI : Fact (1 < 2 ^ 3) := ⟨by norm_num⟩
  rcases hx with h | h
  · have hu : IsUnit x := PadicInt.isUnit_iff.mpr h
    have hru : IsUnit (toZModPow 3 x) := hu.map _
    refine ⟨hru.ne_zero, ?_⟩
    intro h4; rw [h4] at hru; revert hru; decide
  · have hlt : ‖x‖ < 1 := by rw [h]; norm_num
    obtain ⟨u, rfl⟩ := (PadicInt.norm_lt_one_iff_dvd x).mp hlt
    have h2norm : ‖((2 : ℕ) : ℤ_[2])‖ = 2⁻¹ := by
      rw [show ((2 : ℕ) : ℤ_[2]) = (2 : ℤ_[2]) by norm_num]
      simpa using (PadicInt.norm_p (p := 2))
    have huu : IsUnit u := by
      rw [PadicInt.isUnit_iff]
      rw [norm_mul, h2norm] at h
      have hh : (2 : ℝ)⁻¹ * ‖u‖ = 2⁻¹ := h
      field_simp at hh
      linarith [hh]
    rw [map_mul, map_natCast]
    have hdec : ∀ r : ZMod 8, IsUnit r → 2 * r ≠ 0 ∧ 2 * r ≠ 4 := by decide +revert
    have := hdec (toZModPow 3 u) (huu.map _)
    convert this using 2

/-! ## Rank-5 isotropy over `ℚ₂` (arbitrary nonzero coefficients)

The normalization: per-coordinate square substitution `xᵢ ↦ 2^(kᵢ) yᵢ` together with a single global parity
choice `m ∈ {0,1}` reduces every coefficient to valuation `0` or `1`, with three coordinates (the
same-parity triple from the pigeonhole) becoming units. After reordering those three to the front and
bridging to `ℤ₂`, `quinary_lift_2adic` supplies the zero; the back-substitution recovers a zero of the
original form. -/

/-- A `ℚ₂` element of norm `≤ 1` lifts to `ℤ₂` (recovering its coercion and norm). -/
theorem exists_padicInt_of_norm_le {z : ℚ_[2]} (h : ‖z‖ ≤ 1) :
    ∃ z' : ℤ_[2], (z' : ℚ_[2]) = z ∧ ‖z'‖ = ‖z‖ := ⟨⟨z, h⟩, rfl, rfl⟩

/-- **Normalized coefficient norm.** After the global parity shift `m` and the square substitution
`xᵢ ↦ 2^(-⌊(vᵢ+m)/2⌋) yᵢ`, the coefficient `2^m · w · 2^(2·(-⌊(v+m)/2⌋))` has norm `2^(-((v+m) % 2))`,
i.e. valuation `(v+m) % 2 ∈ {0,1}` (unit or two-unit). -/
theorem norm_normalized (w : ℚ_[2]) (hw : w ≠ 0) (m : ℤ) :
    ‖(2 : ℚ_[2]) ^ m * w * (2 : ℚ_[2]) ^ (2 * (-((w.valuation + m) / 2)))‖
      = (2 : ℝ) ^ (-((w.valuation + m) % 2)) := by
  set v := w.valuation with hv
  set k : ℤ := -((v + m) / 2) with hk
  have hn2 : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := by
    rw [show (2 : ℚ_[2]) = ((2 : ℕ) : ℚ_[2]) by norm_num]; simpa using (Padic.norm_p (p := 2))
  have hnw : ‖w‖ = (2 : ℝ) ^ (-v) := by rw [hv]; simpa using Padic.norm_eq_zpow_neg_valuation hw
  rw [norm_mul, norm_mul, norm_zpow, norm_zpow, hn2, hnw,
    show ((2 : ℝ)⁻¹) = (2 : ℝ) ^ (-1 : ℤ) by simp,
    ← zpow_mul, ← zpow_mul, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
    ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1; omega

/-- **Back-substitution.** If the per-coordinate-scaled, globally-`2^m`-shifted form `∑ (2^m wᵢ 2^(2kᵢ)) yᵢ²`
has a nontrivial zero `y`, then so does `∑ wᵢ xᵢ²` (with `xᵢ = 2^(kᵢ) yᵢ`). -/
theorem diag_scale_back_padic {n : ℕ} (w : Fin n → ℚ_[2]) (k : Fin n → ℤ) (m : ℤ)
    (y : Fin n → ℚ_[2]) (hy : y ≠ 0)
    (heq : ∑ i, ((2 : ℚ_[2]) ^ m * w i * (2 : ℚ_[2]) ^ (2 * k i)) * y i ^ 2 = 0) :
    ∃ x : Fin n → ℚ_[2], x ≠ 0 ∧ ∑ i, w i * x i ^ 2 = 0 := by
  have h2 : (2 : ℚ_[2]) ≠ 0 := two_ne_zero
  refine ⟨fun i => (2 : ℚ_[2]) ^ (k i) * y i, ?_, ?_⟩
  · intro hx; apply hy; funext i
    have hxi := congrFun hx i
    simp only [Pi.zero_apply, mul_eq_zero] at hxi ⊢
    rcases hxi with h | h
    · exact absurd h (zpow_ne_zero _ h2)
    · exact h
  · have key : ∀ i, w i * ((2 : ℚ_[2]) ^ (k i) * y i) ^ 2
        = (2 : ℚ_[2]) ^ (-m) * (((2 : ℚ_[2]) ^ m * w i * (2 : ℚ_[2]) ^ (2 * k i)) * y i ^ 2) := by
      intro i
      have e1 : ((2 : ℚ_[2]) ^ (k i)) ^ 2 = (2 : ℚ_[2]) ^ (2 * k i) := by
        rw [sq, ← zpow_add₀ h2, show k i + k i = 2 * k i from by ring]
      have e2 : (2 : ℚ_[2]) ^ (-m) * (2 : ℚ_[2]) ^ m = 1 := by
        rw [← zpow_add₀ h2, neg_add_cancel, zpow_zero]
      rw [mul_pow, e1,
        show (2 : ℚ_[2]) ^ (-m) * ((2 : ℚ_[2]) ^ m * w i * (2 : ℚ_[2]) ^ (2 * k i) * y i ^ 2)
          = ((2 : ℚ_[2]) ^ (-m) * (2 : ℚ_[2]) ^ m) * (w i * (2 : ℚ_[2]) ^ (2 * k i) * y i ^ 2)
          from by ring, e2, one_mul]
      ring
    have hrw : ∑ i, w i * ((2 : ℚ_[2]) ^ (k i) * y i) ^ 2
        = (2 : ℚ_[2]) ^ (-m) * ∑ i, ((2 : ℚ_[2]) ^ m * w i * (2 : ℚ_[2]) ^ (2 * k i)) * y i ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => key i)
    show ∑ i, w i * ((2 : ℚ_[2]) ^ (k i) * y i) ^ 2 = 0
    rw [hrw, heq, mul_zero]

/-- **Rank-5 `ℚ₂` local isotropy.** Every diagonal form `∑ wᵢ xᵢ²` of rank `5` over `ℚ₂` with all
coefficients nonzero is isotropic. This is the `2`-adic analogue of the odd-`p`
`exists_diag_nary_zero_odd_padic` — the genuine frontier, since the odd-`p` ternary route fails at `p = 2`
(`⟨1,1,1⟩` is anisotropic over `ℚ₂`). Built from the mod-8 combinatorial core + exact `ℤ₂` lift after
normalizing all coefficients to valuation `0/1` with three units, via a single global parity choice. -/
theorem exists_quinary_zero_2adic (w : Fin 5 → ℚ_[2]) (hw : ∀ i, w i ≠ 0) :
    ∃ x : Fin 5 → ℚ_[2], x ≠ 0 ∧ ∑ i, w i * x i ^ 2 = 0 := by
  set v : Fin 5 → ℤ := fun i => (w i).valuation with hvdef
  obtain ⟨i0, i1, i2, d01, d02, d12, hg01, hg12⟩ :=
    exists_three_same_parity (n := 5) (by norm_num) (fun i => ((v i : ZMod 2)))
  have hpar01 : v i0 % 2 = v i1 % 2 := (ZMod.intCast_eq_intCast_iff _ _ _).mp hg01
  have hpar12 : v i1 % 2 = v i2 % 2 := (ZMod.intCast_eq_intCast_iff _ _ _).mp hg12
  set m : ℤ := v i0 % 2 with hm
  set k : Fin 5 → ℤ := fun i => -((v i + m) / 2) with hkdef
  set b : Fin 5 → ℚ_[2] := fun i => (2 : ℚ_[2]) ^ m * w i * (2 : ℚ_[2]) ^ (2 * k i) with hbdef
  have hbnorm : ∀ i, ‖b i‖ = (2 : ℝ) ^ (-((v i + m) % 2)) := by
    intro i; exact norm_normalized (w i) (hw i) m
  have hall : ∀ i, (v i + m) % 2 = 0 ∨ (v i + m) % 2 = 1 := by intro i; omega
  have h0chosen : (v i0 + m) % 2 = 0 := by omega
  have h1chosen : (v i1 + m) % 2 = 0 := by omega
  have h2chosen : (v i2 + m) % 2 = 0 := by omega
  have hle : ∀ i, ‖b i‖ ≤ 1 := by
    intro i; rw [hbnorm i]; rcases hall i with h | h <;> rw [h] <;> norm_num
  choose b' hb'coe hb'norm using fun i => exists_padicInt_of_norm_le (hle i)
  have hbu : ∀ i, (v i + m) % 2 = 0 → IsUnit (b' i) := by
    intro i hi; rw [PadicInt.isUnit_iff, hb'norm i, hbnorm i, hi]; norm_num
  have hres : ∀ i, toZModPow 3 (b' i) ≠ 0 ∧ toZModPow 3 (b' i) ≠ 4 := by
    intro i; apply toZModPow3_ne_zero_four_of_norm
    rw [hb'norm i, hbnorm i]; rcases hall i with h | h <;> rw [h] <;> [left; right] <;> norm_num
  obtain ⟨e, he0, he1, he2⟩ := exists_equiv_zero_one_two (m := 2) i0 i1 i2 d01 d02 d12
  set a : Fin 5 → ℤ_[2] := fun i => b' (e i) with hadef
  have hua0 : IsUnit (a 0) := by rw [hadef]; simp only; rw [he0]; exact hbu i0 h0chosen
  have hua1 : IsUnit (a 1) := by rw [hadef]; simp only; rw [he1]; exact hbu i1 h1chosen
  have hua2 : IsUnit (a 2) := by rw [hadef]; simp only; rw [he2]; exact hbu i2 h2chosen
  obtain ⟨x', hx'0, hx'eq⟩ := quinary_lift_2adic a hua0 hua1 hua2
    (hres (e 3)).1 (hres (e 3)).2 (hres (e 4)).1 (hres (e 4)).2
  set y : Fin 5 → ℚ_[2] := fun j => ((x' (e.symm j) : ℚ_[2])) with hydef
  have hy0 : y ≠ 0 := by
    intro hyz; apply hx'0
    have hh : y (e 0) = 0 := by rw [hyz]; rfl
    rw [hydef] at hh; simp only [Equiv.symm_apply_apply] at hh
    exact PadicInt.coe_eq_zero.mp hh
  have hcast : ∑ i, (a i : ℚ_[2]) * ((x' i : ℚ_[2])) ^ 2 = 0 := by
    have := congrArg (fun t : ℤ_[2] => (t : ℚ_[2])) hx'eq
    push_cast at this; simpa using this
  have hsum : ∑ j, b j * (y j) ^ 2 = 0 := by
    rw [← Equiv.sum_comp e (fun j => b j * (y j) ^ 2)]
    have hterm : ∀ i, b (e i) * (y (e i)) ^ 2 = (a i : ℚ_[2]) * ((x' i : ℚ_[2])) ^ 2 := by
      intro i
      have hye : y (e i) = ((x' i : ℚ_[2])) := by rw [hydef]; simp [Equiv.symm_apply_apply]
      have hbe : b (e i) = ((a i : ℚ_[2])) := by rw [hadef]; simp only; rw [← hb'coe (e i)]
      rw [hye, hbe]
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]; exact hcast
  exact diag_scale_back_padic w k m y hy0 hsum

/-- **Rank-≥5 `ℚ₂` local isotropy.** Any diagonal form `∑ wᵢ xᵢ²` of rank `n ≥ 5` over `ℚ₂` with all
coefficients nonzero is isotropic — the `2`-adic companion of `PadicSquare.exists_diag_nary_zero_odd_padic`.
Reduces to the rank-5 case (`exists_quinary_zero_2adic`) on the leading five coordinates, padding the rest
with `0`. Together with the odd-`p` lemma and the real (indefinite) case, this discharges the `p = 2` local
hypothesis of the general-rank Hasse–Minkowski spine `diag_nary_zero_of_local` for any rank-≥5 form. -/
theorem exists_diag_nary_zero_2adic {n : ℕ} (hn : 5 ≤ n)
    (w : Fin n → ℚ_[2]) (hw : ∀ i, w i ≠ 0) :
    ∃ x : Fin n → ℚ_[2], x ≠ 0 ∧ ∑ i, w i * x i ^ 2 = 0 := by
  set w5 : Fin 5 → ℚ_[2] := fun j => w (Fin.castLE hn j) with hw5def
  have hw5 : ∀ j, w5 j ≠ 0 := fun j => hw _
  obtain ⟨x5, hx50, hx5eq⟩ := exists_quinary_zero_2adic w5 hw5
  set x : Fin n → ℚ_[2] := fun i => if h : i.val < 5 then x5 ⟨i.val, h⟩ else 0 with hxdef
  refine ⟨x, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp hx50
    intro hxz
    apply hj
    have hxi : x (Fin.castLE hn j) = 0 := by rw [hxz]; rfl
    rw [hxdef] at hxi; simp only at hxi
    rw [dif_pos (show (Fin.castLE hn j).val < 5 from j.isLt)] at hxi
    exact hxi
  · have hzero : ∀ i ∈ Finset.univ, i ∉ Finset.univ.map (Fin.castLEEmb hn) →
        w i * x i ^ 2 = 0 := by
      intro i _ hi
      have hnlt : ¬ (i.val < 5) := by
        intro hlt
        exact hi (Finset.mem_map.mpr ⟨⟨i.val, hlt⟩, Finset.mem_univ _, rfl⟩)
      rw [hxdef]; simp only [dif_neg hnlt]; ring
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map (Fin.castLEEmb hn))) hzero,
      Finset.sum_map]
    have hterm : ∀ j : Fin 5, w (Fin.castLEEmb hn j) * x (Fin.castLEEmb hn j) ^ 2
        = w5 j * x5 j ^ 2 := by
      intro j
      have hxj : x (Fin.castLEEmb hn j) = x5 j := by
        rw [hxdef]; simp only [dif_pos (show (Fin.castLEEmb hn j).val < 5 from j.isLt)]; congr 1
      rw [hxj]; rfl
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]
    exact hx5eq

end SKEFTHawking
