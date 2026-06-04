/-
# The p-adic Hilbert symbol (odd prime, positive-natural inputs)

For an odd prime `p`, the p-adic Hilbert symbol of `a = p^α u`, `b = p^β v` (`u, v` p-units) is
`  (a,b)_p = (-1)^{αβ·(p-1)/2} · (u | p)^β · (v | p)^α `
where `(· | p)` is the Legendre symbol. This file gives the explicit definition on positive naturals
(`α, β = factorization`, `u, v = ordCompl[p]`) and proves it is **bimultiplicative** and **`{±1}`-valued**:
both properties read off the exponent split `factorization (a₁a₂) = factorization a₁ + factorization a₂`
together with `ordCompl_mul` and Legendre multiplicativity, so the cross term `(-1)^{αβ·ε}` splits cleanly.

Part of the from-scratch Hasse–Minkowski development ([HM-LG]); builds on `PadicUnitResidue` and
`HilbertSymbolReal`. Sign / rational extension and the product formula come in later bricks.
Kernel-pure, no axioms.
-/

import Mathlib
import SKEFTHawking.PadicUnitResidue

namespace SKEFTHawking.HilbertSymbol

open Nat

variable (p : ℕ) [Fact p.Prime]

/-- The **p-adic Hilbert symbol** on positive naturals, via the explicit Legendre-symbol formula. -/
def hilbertPadicNat (a b : ℕ) : ℤ :=
  (-1) ^ (a.factorization p * b.factorization p * ((p - 1) / 2)) *
      legendreSym p ((ordCompl[p] a : ℕ) : ℤ) ^ b.factorization p *
    legendreSym p ((ordCompl[p] b : ℕ) : ℤ) ^ a.factorization p

/-- The `p`-free part, cast to `ZMod p`, is nonzero (it is coprime to `p`). -/
theorem cast_ordCompl_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (((ordCompl[p] n : ℕ) : ℤ) : ZMod p) ≠ 0 := by
  have hp : p.Prime := Fact.out
  rw [Int.cast_natCast, Ne, CharP.cast_eq_zero_iff (ZMod p) p]
  exact Nat.not_dvd_ordCompl hp hn

/-- The symbol is `{±1}`-valued (for nonzero arguments): a product of units. -/
theorem hilbertPadicNat_mem {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertPadicNat p a b = 1 ∨ hilbertPadicNat p a b = -1 := by
  rw [← Int.isUnit_iff]
  have hu1 : IsUnit (legendreSym p ((ordCompl[p] a : ℕ) : ℤ)) :=
    Int.isUnit_iff.mpr (legendreSym.eq_one_or_neg_one p (cast_ordCompl_ne_zero p ha))
  have hu2 : IsUnit (legendreSym p ((ordCompl[p] b : ℕ) : ℤ)) :=
    Int.isUnit_iff.mpr (legendreSym.eq_one_or_neg_one p (cast_ordCompl_ne_zero p hb))
  unfold hilbertPadicNat
  exact (((IsUnit.neg isUnit_one).pow _).mul (hu1.pow _)).mul (hu2.pow _)

/-- **Bimultiplicativity in the first argument.** -/
theorem hilbertPadicNat_mul_left {a₁ a₂ b : ℕ} (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) :
    hilbertPadicNat p (a₁ * a₂) b = hilbertPadicNat p a₁ b * hilbertPadicNat p a₂ b := by
  unfold hilbertPadicNat
  rw [Nat.ordCompl_mul, Nat.factorization_mul ha₁ ha₂]
  simp only [Finsupp.coe_add, Pi.add_apply, Nat.cast_mul, legendreSym.mul, add_mul, pow_add, mul_pow]
  ring

/-- **Bimultiplicativity in the second argument.** -/
theorem hilbertPadicNat_mul_right {a b₁ b₂ : ℕ} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    hilbertPadicNat p a (b₁ * b₂) = hilbertPadicNat p a b₁ * hilbertPadicNat p a b₂ := by
  unfold hilbertPadicNat
  rw [Nat.ordCompl_mul, Nat.factorization_mul hb₁ hb₂]
  simp only [Finsupp.coe_add, Pi.add_apply, Nat.cast_mul, legendreSym.mul, mul_add, pow_add, mul_pow]
  ring

/-- **Symmetry:** `(a,b)_p = (b,a)_p`. -/
theorem hilbertPadicNat_comm (a b : ℕ) : hilbertPadicNat p a b = hilbertPadicNat p b a := by
  unfold hilbertPadicNat
  rw [Nat.mul_comm (a.factorization p) (b.factorization p)]
  ring

/-- **Unit forms are locally isotropic:** if `p` divides neither `a` nor `b`, then `(a,b)_p = 1`
(both valuations vanish, so the formula collapses to `(-1)^0 · _^0 · _^0`). -/
theorem hilbertPadicNat_units {a b : ℕ} (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) :
    hilbertPadicNat p a b = 1 := by
  unfold hilbertPadicNat
  rw [Nat.factorization_eq_zero_of_not_dvd ha, Nat.factorization_eq_zero_of_not_dvd hb]
  simp

/-- `(1, b)_p = 1`. -/
@[simp] theorem hilbertPadicNat_one_left (b : ℕ) : hilbertPadicNat p 1 b = 1 := by
  unfold hilbertPadicNat; simp [Nat.factorization_one]

/-- `(a, 1)_p = 1`. -/
@[simp] theorem hilbertPadicNat_one_right (a : ℕ) : hilbertPadicNat p a 1 = 1 := by
  rw [hilbertPadicNat_comm]; exact hilbertPadicNat_one_left p a

/-- The **`p`-free part of a nonzero integer** `a = p^{v_p(a)} · pfreeInt a`. -/
def pfreeInt (a : ℤ) : ℤ := a / (p : ℤ) ^ padicValInt p a

omit [Fact p.Prime] in
/-- `a = p^{v_p(a)} · pfreeInt a` (exact, since `p^{v_p(a)} ∣ a`). -/
theorem pfreeInt_spec (a : ℤ) : a = (p : ℤ) ^ padicValInt p a * pfreeInt p a :=
  (Int.mul_ediv_cancel' (padicValInt_dvd a)).symm

/-- **Multiplicativity of the `p`-free part:** `pfreeInt (a·b) = pfreeInt a · pfreeInt b` (nonzero `a, b`). -/
theorem pfreeInt_mul {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    pfreeInt p (a * b) = pfreeInt p a * pfreeInt p b := by
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).pos.ne'
  have hkey : a * b = pfreeInt p a * pfreeInt p b * ((p : ℤ) ^ padicValInt p a * (p : ℤ) ^ padicValInt p b) := by
    conv_lhs => rw [pfreeInt_spec p a, pfreeInt_spec p b]
    ring
  rw [pfreeInt, padicValInt.mul ha hb, pow_add,
    Int.ediv_eq_of_eq_mul_left (mul_ne_zero (pow_ne_zero _ hpne) (pow_ne_zero _ hpne)) hkey]

/-- **Legendre connection:** for `p ∤ a`, `(a, p)_p = (a | p)` — the symbol against the uniformizer is
the Legendre symbol. -/
theorem hilbertPadicNat_eq_legendre {a : ℕ} (ha : ¬ p ∣ a) :
    hilbertPadicNat p a p = legendreSym p (a : ℤ) := by
  have hp : p.Prime := Fact.out
  unfold hilbertPadicNat
  rw [Nat.factorization_eq_zero_of_not_dvd ha, hp.factorization_self]
  simp

end SKEFTHawking.HilbertSymbol
