/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 3, site 3/4 inc 4b — the `kSO3 = 0` quantization (toward the structural
Clifford base)

The bridge from `kSO3 (reconstruct x y k) = 0` to the torsion classes of `ZOmegaTorsion.lean`:

  * the `(Z,Z)` Bloch numerator identity `blochEntry (reconstruct x y k) 2 2 =
    mk (2(|x|² − |y|²)) 6` (`k`-free — the phase cancels on the diagonal);
  * `kSO3 = 0 ⟹ denExp (R₂₂) = 0 ⟹ √2⁶ ∣ 2(|x|² − |y|²) ⟹ 4 ∣ |x|² − |y|²`;
  * **the quantization trichotomy**: with the unit-column equation `|x|² + |y|² = ⟨0,0,0,4⟩`,
    the real element `u = |x|²` satisfies `2u = ⟨0,0,0,4⟩ + (u − v)` with `4 ∣ u − v`, so `u`
    is even-coordinate with `u.d ∈ {0, 2, 4}`; Galois positivity (`2·u.c² ≤ u.d²`, applied to
    BOTH `x` and `y`) kills the `√2`-part, leaving exactly
    `(x, |y|²) = (0, 4)`, `(|x|², |y|²) = (2, 2)`, or `(|x|², y) = (4, 0)`.

Composed with `ZOmegaTorsion`, every `kSO3 = 0` reconstruction key `(x, y)` is
`(0, 2ωᵇ)`, `(√2ωᵃ, √2ωᵇ)`, or `(2ωᵃ, 0)` — the substrate for the per-class finite coverage
checks that replace the `cliffordBase_box_core` box sweep (inc 4c).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15**: no new axioms. No `native_decide`.
  Kernel-pure `{propext, Classical.choice, Quot.sound}`.
-/

import SKEFTHawking.FKLW.RossSelinger.BridgeStructural
import SKEFTHawking.FKLW.RossSelinger.ZOmegaTorsion
import SKEFTHawking.FKLW.RossSelinger.ColumnBaseCase

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger
namespace KMM

open CliffordTGate ZOmegaSqrt2

set_option maxRecDepth 4000 in
/-- **The `(Z,Z)` Bloch numerator identity**: `R(reconstruct x y k)₂₂` clears to
`2(|x|² − |y|²)` at level 6 — `k`-free (the diagonal phase pair cancels). -/
theorem blochEntry_reconstruct_zz (x y : ZOmega) (k : ℕ) :
    blochEntry (reconstruct x y k) 2 2
      = mk (2 * (x * ZOmega.conj x - y * ZOmega.conj y)) 6 := by
  rw [blochEntry]
  simp only [reconstruct, pauliMat, gateMatrix, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two, adjoint_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
    omegaS_pow_mk, conj_mk, half, zero_mul, one_mul, mul_zero, mul_one,
    neg_mul, mul_neg, neg_one_mul, mul_neg_one, add_zero, zero_add, neg_zero, neg_neg,
    ZOmega.conj_neg, ZOmega.conj_mul, ZOmega.conj_conj, mk_mul, mk_add, mk_neg]
  rw [mk_eq_mk_iff]
  linear_combination (ZOmega.sqrt2 ^ 18
    * (ZOmega.conj x * x - ZOmega.conj y * y)) * omega_pow_mul_conj k

/-- **`kSO3 = 0` forces `4 ∣ |x|² − |y|²`** (the `(Z,Z)` entry is a denominator-free
rational, and its cleared numerator carries `√2⁶ = 8`). -/
theorem four_dvd_normSq_sub_of_kSO3_eq_zero {x y : ZOmega} {k : ℕ}
    (h0 : kSO3 (reconstruct x y k) = 0) :
    (4 : ZOmega) ∣ (ZOmega.normSq x - ZOmega.normSq y) := by
  have hle : denExp (blochEntry (reconstruct x y k) 2 2) ≤ 0 := by
    have := denExp_blochEntry_le_kSO3 (reconstruct x y k) 2 2
    omega
  obtain ⟨w, hw⟩ := denExp_le_iff.mp hle
  rw [pow_zero, one_mul, blochEntry_reconstruct_zz, of_def, mk_eq_mk_iff] at hw
  -- hw relates √2-powers of the two numerators; cancel 2 over the domain ZOmega
  refine ⟨w, ?_⟩
  have h8 : (ZOmega.sqrt2 : ZOmega) ^ 6 = 8 := by decide
  have h2 : (2 : ZOmega) * (ZOmega.normSq x - ZOmega.normSq y) = 2 * (4 * w) := by
    have hw' : 2 * (x * ZOmega.conj x - y * ZOmega.conj y) * ZOmega.sqrt2 ^ 0
        = w * ZOmega.sqrt2 ^ 6 := hw
    rw [pow_zero, mul_one, h8] at hw'
    show (2 : ZOmega) * (x * ZOmega.conj x - y * ZOmega.conj y) = 2 * (4 * w)
    linear_combination hw'
  exact mul_left_cancel₀ (by decide : (2 : ZOmega) ≠ 0) h2

/-- **The `kSO3 = 0` quantization trichotomy**: a unit-column pair `(x, y)`
(`|x|² + |y|² = ⟨0,0,0,4⟩`) with `4 ∣ |x|² − |y|²` is in one of exactly three classes:
`x = 0` (then `|y|² = 4`), both norms `2`, or `y = 0` (then `|x|² = 4`). Galois positivity
applied to both coordinates kills the `√2`-parts. -/
theorem normSq_quantized {x y : ZOmega}
    (hsum : ZOmega.normSq x + ZOmega.normSq y = (⟨0, 0, 0, 4⟩ : ZOmega))
    (hZZ : (4 : ZOmega) ∣ (ZOmega.normSq x - ZOmega.normSq y)) :
    (x = 0 ∧ ZOmega.normSq y = (⟨0, 0, 0, 4⟩ : ZOmega)) ∨
    (ZOmega.normSq x = (⟨0, 0, 0, 2⟩ : ZOmega) ∧
      ZOmega.normSq y = (⟨0, 0, 0, 2⟩ : ZOmega)) ∨
    (ZOmega.normSq x = (⟨0, 0, 0, 4⟩ : ZOmega) ∧ y = 0) := by
  obtain ⟨w, hw⟩ := hZZ
  have h4lit : (4 : ZOmega) = (⟨0, 0, 0, 4⟩ : ZOmega) := by decide
  rw [h4lit] at hw
  -- coordinate extractions
  have hs1 := congrArg ZOmega.a hsum
  have hs2 := congrArg ZOmega.b hsum
  have hs3 := congrArg ZOmega.c hsum
  have hs4 := congrArg ZOmega.d hsum
  have hw1 := congrArg ZOmega.a hw
  have hw2 := congrArg ZOmega.b hw
  have hw3 := congrArg ZOmega.c hw
  have hw4 := congrArg ZOmega.d hw
  simp only [ZOmega.add_a, ZOmega.add_b, ZOmega.add_c, ZOmega.add_d, ZOmega.sub_a,
    ZOmega.sub_b, ZOmega.sub_c, ZOmega.sub_d, ZOmega.mul_a, ZOmega.mul_b, ZOmega.mul_c,
    ZOmega.mul_d] at hs1 hs2 hs3 hs4 hw1 hw2 hw3 hw4
  -- reality of both norms
  have hbx := ZOmega.normSq_b_zero x
  have hax := ZOmega.normSq_a_eq_neg_c x
  have hby := ZOmega.normSq_b_zero y
  have hay := ZOmega.normSq_a_eq_neg_c y
  -- positivity of the rational parts
  have hdx : 0 ≤ (ZOmega.normSq x).d := by rw [ZOmega.normSq_d]; positivity
  have hdy : 0 ≤ (ZOmega.normSq y).d := by rw [ZOmega.normSq_d]; positivity
  -- Galois positivity (√2-part bounds)
  have hgx := ZOmega.normSq_galois_nonneg x
  have hgy := ZOmega.normSq_galois_nonneg y
  -- the rational part is an even value in {0, 2, 4}
  have hd024 : (ZOmega.normSq x).d = 0 ∨ (ZOmega.normSq x).d = 2 ∨
      (ZOmega.normSq x).d = 4 := by omega
  -- the √2-part of |x|² is even, and so is |y|²'s (their difference is 4w, sum is rational)
  have hcx_even : (ZOmega.normSq x).c % 2 = 0 := by omega
  rcases hd024 with hd0 | hd2 | hd4
  · -- |x|².d = 0 ⟹ Galois kills c ⟹ |x|² = 0 ⟹ x = 0; |y|² = the full literal
    have hcx : (ZOmega.normSq x).c = 0 := by
      have h1 : (ZOmega.normSq x).c ≤ 0 := by nlinarith [hgx]
      have h2 : 0 ≤ (ZOmega.normSq x).c := by nlinarith [hgx]
      omega
    have hx0 : ZOmega.normSq x = 0 := by
      ext <;> simp only [ZOmega.zero_a, ZOmega.zero_b, ZOmega.zero_c, ZOmega.zero_d] <;> omega
    refine Or.inl ⟨ZOmega.normSq_eq_zero_iff.mp hx0, ?_⟩
    ext <;> simp only [] <;> omega
  · -- |x|².d = 2 ⟹ c² ≤ 2 even ⟹ c = 0 ⟹ both norms are the rational 2
    have hcx : (ZOmega.normSq x).c = 0 := by
      have h1 : (ZOmega.normSq x).c ≤ 1 := by nlinarith [hgx]
      have h2 : -1 ≤ (ZOmega.normSq x).c := by nlinarith [hgx]
      omega
    refine Or.inr (Or.inl ⟨?_, ?_⟩) <;>
      (ext <;> simp only [] <;> omega)
  · -- |x|².d = 4 ⟹ |y|².d = 0 ⟹ Galois on y kills its c ⟹ y = 0, |x|² = the literal
    have hcy : (ZOmega.normSq y).c = 0 := by
      have hdy0 : (ZOmega.normSq y).d = 0 := by omega
      have h1 : (ZOmega.normSq y).c ≤ 0 := by nlinarith [hgy]
      have h2 : 0 ≤ (ZOmega.normSq y).c := by nlinarith [hgy]
      omega
    have hy0 : ZOmega.normSq y = 0 := by
      ext <;> simp only [ZOmega.zero_a, ZOmega.zero_b, ZOmega.zero_c, ZOmega.zero_d] <;> omega
    refine Or.inr (Or.inr ⟨?_, ZOmega.normSq_eq_zero_iff.mp hy0⟩)
    ext <;> simp only [] <;> omega

end KMM
end SKEFTHawking.RossSelinger
