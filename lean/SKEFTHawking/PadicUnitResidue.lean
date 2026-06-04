/-
# The p-adic unit residue — infrastructure for the p-adic Hilbert symbol

The explicit (Legendre-symbol) formula for the p-adic Hilbert symbol `(a,b)_p` (`p` odd) reads, writing
`a = p^α u`, `b = p^β v` with `u, v` units,
`  (a,b)_p = (-1)^{αβ(p-1)/2} · (u | p)^β · (v | p)^α `.
The "unit residue" `u mod p ∈ ZMod p` of a nonzero integer/natural is the object on which the Legendre
symbols are evaluated. This file builds it on ℕ (and lifts the key facts to ℤ): strip the `p`-part via
`ordCompl[p]` and reduce mod `p`. It is multiplicative and nonzero (for `p` prime), the two properties
that make the Hilbert-symbol formula bimultiplicative.

Part of the from-scratch Hasse–Minkowski development ([HM-LG]); see `HilbertSymbolReal` for the real place.
Kernel-pure, no axioms.
-/

import Mathlib

namespace SKEFTHawking.HilbertSymbol

open Nat

/-- The **p-adic unit residue** of a natural number: the `p`-free part `ordCompl[p] n`, reduced mod `p`. -/
def natUnitRes (p n : ℕ) : ZMod p := (ordCompl[p] n : ZMod p)

@[simp] theorem natUnitRes_zero (p : ℕ) : natUnitRes p 0 = 0 := by simp [natUnitRes]

@[simp] theorem natUnitRes_one (p : ℕ) : natUnitRes p 1 = 1 := by simp [natUnitRes]

/-- **Multiplicativity:** the unit residue is a multiplicative function. -/
theorem natUnitRes_mul (p a b : ℕ) : natUnitRes p (a * b) = natUnitRes p a * natUnitRes p b := by
  simp only [natUnitRes, Nat.ordCompl_mul, Nat.cast_mul]

/-- **Nonvanishing:** for a prime `p` and nonzero `n`, the residue is a unit (nonzero in `ZMod p`),
since `p ∤ ordCompl[p] n`. -/
theorem natUnitRes_ne_zero {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) : natUnitRes p n ≠ 0 := by
  simp only [natUnitRes, Ne, CharP.cast_eq_zero_iff (ZMod p) p]
  exact Nat.not_dvd_ordCompl hp hn

/-- On a number coprime to `p`, the residue is just the reduction mod `p` (no `p`-part to strip). -/
theorem natUnitRes_of_not_dvd {p n : ℕ} (h : ¬ p ∣ n) : natUnitRes p n = (n : ZMod p) := by
  simp only [natUnitRes, Nat.factorization_eq_zero_of_not_dvd h, pow_zero, Nat.div_one]

/-- The residue depends only on the `p`-free part: `natUnitRes p (p^k * n) = natUnitRes p n`. -/
theorem natUnitRes_ordProj_mul {p : ℕ} (hp : p.Prime) (k n : ℕ) :
    natUnitRes p (p ^ k * n) = natUnitRes p n := by
  rw [natUnitRes_mul]
  have : natUnitRes p (p ^ k) = 1 := by
    simp only [natUnitRes, Nat.ordCompl_self_pow hp, Nat.cast_one]
  rw [this, one_mul]

end SKEFTHawking.HilbertSymbol
