/-
# Discharging the [HM] hypothesis — Hasse–Minkowski for indefinite even unimodular forms

`RokhlinFromHM` reduces even-unimodular `8 ∣ σ` (hence `16 ∣ σ`) to the single input
`HasWeakIsotropicVectorHyp`: every indefinite even unimodular integer form has a nonzero integer isotropic
vector. This file discharges that input by assembling the local–global machinery:

* the general-rank diagonal Hasse–Minkowski spine `diag_nary_zero_of_local` (n ≤ 4 bases + n ≥ 5 Meyer
  descent), with the local hypotheses supplied by
  - ℝ: `diag_real_isotropic_of_signs` (indefinite ⟹ a `+` and a `−` coefficient),
  - odd `p`: `PadicSquare.exists_diag_nary_zero_odd_padic` (rank ≥ 5),
  - `p = 2`: `PadicSquareTwo.exists_diag_nary_zero_2adic` (rank ≥ 5 — the 2-adic frontier),
* the base-change bridge `matrix_isotropic_congr` (transfer between the Gram matrix and its ℚ-diagonalization),
* content extraction `exists_int_isotropic_of_rat` (rational ⟹ integer isotropic vector).

This file currently ships the **rank-≥5 local–global wrapper** `diag_indefinite_rat_zero`; the matrix
diagonalization + signature plumbing and the small-rank (2, 4) cases build on top toward the full
`HasWeakIsotropicVectorHyp`. Kernel-pure, no axioms.
-/

import Mathlib
import SKEFTHawking.HasseMinkowskiNary
import SKEFTHawking.PadicSquareTwo

namespace SKEFTHawking

open scoped BigOperators
open QuadraticMap

/-! ## Signature ⟹ value bricks (for transferring indefiniteness to the diagonalization)

`sigPos > 0`/`sigNeg > 0` of a form means it takes a positive/negative value. The reusable direction we need
(a positive value forces `sigPos ≥ 1`) is `le_sigPos_of_posDef` applied to the line spanned by that value. -/

/-- A positive value of a quadratic form forces `1 ≤ sigPos` (the line it spans is positive-definite). -/
theorem one_le_sigPos_of_pos_value {K M : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup M] [Module K M] [Module.Finite K M] (Q : QuadraticForm K M) (x : M)
    (hx : 0 < Q x) : 1 ≤ sigPos Q := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hposdef : (Q.restrict (Submodule.span K {x})).PosDef := by
    intro v hv
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp v.2
    have hvval : (v : M) = t • x := ht.symm
    have htne : t ≠ 0 := by
      rintro rfl; simp only [zero_smul] at hvval
      exact hv (Subtype.ext (by simpa using hvval))
    show 0 < Q.restrict _ v
    rw [QuadraticMap.restrict_apply, hvval, QuadraticMap.map_smul, smul_eq_mul]
    exact mul_pos (mul_self_pos.mpr htne) hx
  have hfr : Module.finrank K (Submodule.span K {x}) = 1 := finrank_span_singleton hx0
  calc 1 = Module.finrank K (Submodule.span K {x}) := hfr.symm
    _ ≤ sigPos Q := le_sigPos_of_posDef Q hposdef

/-- A negative value of a quadratic form forces `1 ≤ sigNeg` (via `sigNeg Q = sigPos (-Q)`). -/
theorem one_le_sigNeg_of_neg_value {K M : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup M] [Module K M] [Module.Finite K M] (Q : QuadraticForm K M) (x : M)
    (hx : Q x < 0) : 1 ≤ sigNeg Q := by
  rw [← sigPos_neg]
  exact one_le_sigPos_of_pos_value (-Q) x (by rw [QuadraticMap.neg_apply]; exact neg_pos.mpr hx)

/-- **Local–global for an indefinite integer diagonal form (rank ≥ 5).** A diagonal form `∑ cᵢ xᵢ²` of
rank `n ≥ 5` with nonzero integer coefficients that is indefinite over ℝ (a positive and a negative
coefficient) has a nontrivial rational zero. The local hypotheses of `diag_nary_zero_of_local` are all
automatic at this rank: ℝ from indefiniteness (`diag_real_isotropic_of_signs`), odd `p` from
`exists_diag_nary_zero_odd_padic`, and `p = 2` from `exists_diag_nary_zero_2adic`. This is the clean payoff
of the closed 2-adic frontier — the local input that was missing is now total. -/
theorem diag_indefinite_rat_zero {n : ℕ} (hn : 5 ≤ n) (c : Fin n → ℤ) (hc : ∀ i, c i ≠ 0)
    (hpos : ∃ i, 0 < c i) (hneg : ∃ j, c j < 0) :
    ∃ x : Fin n → ℚ, x ≠ 0 ∧ ∑ i, (c i : ℚ) * x i ^ 2 = 0 := by
  apply diag_nary_zero_of_local n c hc
  · obtain ⟨i, hi⟩ := hpos; obtain ⟨j, hj⟩ := hneg
    have hij : i ≠ j := by rintro rfl; omega
    exact diag_real_isotropic_of_signs (fun i => (c i : ℝ)) i j hij
      (Int.cast_pos.mpr hi) (Int.cast_lt_zero.mpr hj)
  · intro p _
    rcases eq_or_ne p 2 with rfl | hp2
    · exact exists_diag_nary_zero_2adic hn (fun i => (c i : ℚ_[2]))
        (fun i => Int.cast_ne_zero.mpr (hc i))
    · exact exists_diag_nary_zero_odd_padic hp2 hn (fun i => (c i : ℚ_[p]))
        (fun i => Int.cast_ne_zero.mpr (hc i))

end SKEFTHawking
