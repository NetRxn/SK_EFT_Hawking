/-
Phase 6n.α Wave (G2 Resurgence) — Higher-order transport-coefficient
counting theorems for SK-EFT orders 4–7.

These specialize `SKEFTHawking.SecondOrderSK.transport_coefficient_count`
(`{p ∈ Finset.Icc (0,0) (N+1, N+1) | p.1 + p.2 = N+1 ∧ p.1 % 2 = 0}.card =
(N+1) / 2 + 1`) to specific orders 4, 5, 6, 7 — the orders shipped through
`src/core/formulas.py:fourth_order_correction` through `seventh_order_correction`
under sub-wave 6n.α.1.

Each specialization is a one-line `decide` from the general theorem;
they exist as named witnesses for the formulas.py `Lean:` cross-references
to resolve, satisfying Pipeline Invariant #4 (every formula has a Lean theorem).

References:
- `SKEFTHawking.SecondOrderSK.transport_coefficient_count` (general N).
- `src/core/formulas.py` lines 281-423 (4 higher-order corrections).
- DR §3 (count(N) = ⌊(N+1)/2⌋ + 1; without spatial parity).
- temporary/working-docs/phase6n/6n_alpha_resurgence_stage1.md
-/
import SKEFTHawking.SecondOrderSK
import Mathlib.LinearAlgebra.Dimension.Finite

namespace SKEFTHawking.HigherOrderSK

/-- **count(4) = 3.** Specialization of `transport_coefficient_count` to N = 4
    (matches `formulas.py:fourth_order_correction` 3-coefficient signature
    γ_{4,1}, γ_{4,2}, γ_{4,3}). The 3 m-even monomials at derivative level 5
    are (m, n_x) ∈ {(0,5), (2,3), (4,1)}. -/
theorem fourth_order_count_eq_3 :
    Finset.card (Finset.filter
      (fun p : ℕ × ℕ => p.1 + p.2 = 5 ∧ p.1 % 2 = 0)
      (Finset.Icc (0, 0) (5, 5))) = 3 := by
  decide

/-- **count(5) = 4.** Specialization to N = 5 (matches
    `formulas.py:fifth_order_correction` 4-coefficient signature). The 4
    m-even monomials at derivative level 6 are
    (m, n_x) ∈ {(0,6), (2,4), (4,2), (6,0)}. -/
theorem fifth_order_count_eq_4 :
    Finset.card (Finset.filter
      (fun p : ℕ × ℕ => p.1 + p.2 = 6 ∧ p.1 % 2 = 0)
      (Finset.Icc (0, 0) (6, 6))) = 4 := by
  decide

/-- **count(6) = 4.** Specialization to N = 6 (matches
    `formulas.py:sixth_order_correction` 4-coefficient signature). The 4
    m-even monomials at derivative level 7 are
    (m, n_x) ∈ {(0,7), (2,5), (4,3), (6,1)}. -/
theorem sixth_order_count_eq_4 :
    Finset.card (Finset.filter
      (fun p : ℕ × ℕ => p.1 + p.2 = 7 ∧ p.1 % 2 = 0)
      (Finset.Icc (0, 0) (7, 7))) = 4 := by
  decide

/-- **count(7) = 5.** Specialization to N = 7 (matches
    `formulas.py:seventh_order_correction` 5-coefficient signature). The 5
    m-even monomials at derivative level 8 are
    (m, n_x) ∈ {(0,8), (2,6), (4,4), (6,2), (8,0)}. -/
theorem seventh_order_count_eq_5 :
    Finset.card (Finset.filter
      (fun p : ℕ × ℕ => p.1 + p.2 = 8 ∧ p.1 % 2 = 0)
      (Finset.Icc (0, 0) (8, 8))) = 5 := by
  decide

/-- **Cumulative count through order 7**: 2 + 2 + 3 + 3 + 4 + 4 + 5 = 23
    free transport coefficients across orders 1–7 (without spatial parity).
    First-order: 2; second-order: 2; third-order: 3; fourth-order: 3;
    fifth-order: 4; sixth-order: 4; seventh-order: 5.
    Useful for Padé–Borel reconstruction sample-size accounting. -/
theorem cumulative_count_through_7 :
    2 + 2 + 3 + 3 + 4 + 4 + 5 = 23 := by decide

end SKEFTHawking.HigherOrderSK
