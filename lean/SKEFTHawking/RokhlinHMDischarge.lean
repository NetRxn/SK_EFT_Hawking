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
