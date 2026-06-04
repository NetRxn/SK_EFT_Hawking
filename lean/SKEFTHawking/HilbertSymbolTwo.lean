/-
# The dyadic supplementary characters ε, ω — foundation of the `p = 2` Hilbert symbol

The 2-adic Hilbert symbol of `a = 2^α u`, `b = 2^β v` (`u, v` odd) is
`  (a,b)_2 = (-1)^{ε(u)·ε(v) + α·ω(v) + β·ω(u)} `
where `ε(u) = (u-1)/2 mod 2` (a character of `(ℤ/4)ˣ`) and `ω(u) = (u²-1)/8 mod 2` (a character of
`(ℤ/8)ˣ`). This file defines `ε, ω : ZMod 8 → ZMod 2` by their residue formulas and proves they are
**additive on the units of `ℤ/8`** (`ε(uv)=ε(u)+ε(v)`, `ω(uv)=ω(u)+ω(v)`) — the *supplementary laws* that
make the dyadic Hilbert symbol bimultiplicative. The additivity is a finite check (`decide`) over the four
units `{1,3,5,7}`.

Part of the from-scratch Hasse–Minkowski development ([HM-LG]); companion to `HilbertSymbolReal` (∞) and
`HilbertSymbolPadic` (odd `p`). Kernel-pure, no axioms, no `native_decide`.
-/

import Mathlib

namespace SKEFTHawking.HilbertSymbol

/-- The dyadic character `ε(u) = (u-1)/2 mod 2`, as a function of `u mod 8`. Values: `ε(1)=ε(5)=0`,
`ε(3)=ε(7)=1` — the nontrivial character of `(ℤ/4)ˣ`. -/
def eps2 (x : ZMod 8) : ZMod 2 := (((x.val - 1) / 2 : ℕ) : ZMod 2)

/-- The dyadic character `ω(u) = (u²-1)/8 mod 2`, as a function of `u mod 8`. Values: `ω(1)=ω(7)=0`,
`ω(3)=ω(5)=1` — the other nontrivial character of `(ℤ/8)ˣ`. -/
def omega2 (x : ZMod 8) : ZMod 2 := (((x.val ^ 2 - 1) / 8 : ℕ) : ZMod 2)

@[simp] theorem eps2_one : eps2 1 = 0 := by decide
@[simp] theorem omega2_one : omega2 1 = 0 := by decide

/-- **Supplementary law for ε:** `ε` is additive on units of `ℤ/8` (`ε(uv) = ε(u)+ε(v)`), reflecting
`(u-1)(v-1) ≡ 0 mod 4`. -/
theorem eps2_mul {x y : ZMod 8} (hx : IsUnit x) (hy : IsUnit y) :
    eps2 (x * y) = eps2 x + eps2 y := by
  revert hx hy; revert x y; decide

/-- **Supplementary law for ω:** `ω` is additive on units of `ℤ/8` (`ω(uv) = ω(u)+ω(v)`), reflecting
`(u²-1)(v²-1) ≡ 0 mod 16`. -/
theorem omega2_mul {x y : ZMod 8} (hx : IsUnit x) (hy : IsUnit y) :
    omega2 (x * y) = omega2 x + omega2 y := by
  revert hx hy; revert x y; decide

/-- The `±1`-valued character of `ZMod 2`: `χ₂ 0 = 1`, `χ₂ 1 = -1`. Converts the additive `ZMod 2` exponent
of the dyadic Hilbert symbol into its multiplicative `{±1}` value. -/
def chi2 (e : ZMod 2) : ℤ := (-1) ^ e.val

@[simp] theorem chi2_zero : chi2 0 = 1 := by decide
@[simp] theorem chi2_one : chi2 1 = -1 := by decide

/-- `χ₂` turns addition into multiplication: `χ₂(e+f) = χ₂ e · χ₂ f`. -/
theorem chi2_add (e f : ZMod 2) : chi2 (e + f) = chi2 e * chi2 f := by
  revert e f; decide

theorem chi2_mem (e : ZMod 2) : chi2 e = 1 ∨ chi2 e = -1 := by revert e; decide

/-- The `2`-free part of a nonzero natural, cast to `ZMod 8`, is a **unit** (it is odd, hence coprime to 8). -/
theorem isUnit_cast_ordCompl_two {n : ℕ} (hn : n ≠ 0) :
    IsUnit ((ordCompl[2] n : ℕ) : ZMod 8) := by
  rw [ZMod.isUnit_iff_coprime]
  have hodd : ¬ (2 : ℕ) ∣ ordCompl[2] n := Nat.not_dvd_ordCompl Nat.prime_two hn
  have hcop2 : Nat.Coprime (ordCompl[2] n) 2 :=
    (Nat.coprime_comm.mp ((Nat.prime_two.coprime_iff_not_dvd).mpr hodd))
  simpa using hcop2.pow_right 3

end SKEFTHawking.HilbertSymbol
