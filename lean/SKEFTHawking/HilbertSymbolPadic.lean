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

/-- The `p`-free part is **coprime to `p`** (`p ∤ pfreeInt a`), so its Legendre symbol is `±1`. -/
theorem not_dvd_pfreeInt {a : ℤ} (ha : a ≠ 0) : ¬ (p : ℤ) ∣ pfreeInt p a := by
  intro hdvd
  have hmax : ¬ p ^ (padicValInt p a + 1) ∣ a.natAbs :=
    pow_succ_padicValNat_not_dvd (p := p) (Int.natAbs_ne_zero.mpr ha)
  obtain ⟨k, hk⟩ := hdvd
  have hdvdInt : (p : ℤ) ^ (padicValInt p a + 1) ∣ a := by
    refine ⟨k, ?_⟩
    conv_lhs => rw [pfreeInt_spec p a, hk]
    ring
  apply hmax
  simpa [Int.natAbs_pow] using Int.natAbs_dvd_natAbs.mpr hdvdInt

/-- **Legendre connection:** for `p ∤ a`, `(a, p)_p = (a | p)` — the symbol against the uniformizer is
the Legendre symbol. -/
theorem hilbertPadicNat_eq_legendre {a : ℕ} (ha : ¬ p ∣ a) :
    hilbertPadicNat p a p = legendreSym p (a : ℤ) := by
  have hp : p.Prime := Fact.out
  unfold hilbertPadicNat
  rw [Nat.factorization_eq_zero_of_not_dvd ha, hp.factorization_self]
  simp

/-- The **signed (ℤ) odd-`p` Hilbert symbol** via the explicit Legendre formula on the `p`-free parts; the
Legendre symbol absorbs the sign. Extends `hilbertPadicNat` to all nonzero integers, as the product formula
over `ℚˣ` requires. -/
def hilbertPadicInt (a b : ℤ) : ℤ :=
  (-1) ^ (padicValInt p a * padicValInt p b * ((p - 1) / 2)) *
      legendreSym p (pfreeInt p a) ^ padicValInt p b *
    legendreSym p (pfreeInt p b) ^ padicValInt p a

/-- The `p`-free part, cast to `ZMod p`, is nonzero. -/
theorem cast_pfreeInt_ne_zero {a : ℤ} (ha : a ≠ 0) : ((pfreeInt p a : ℤ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact not_dvd_pfreeInt p ha

/-- The signed symbol is `{±1}`-valued (nonzero arguments): a product of units. -/
theorem hilbertPadicInt_mem {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertPadicInt p a b = 1 ∨ hilbertPadicInt p a b = -1 := by
  rw [← Int.isUnit_iff]
  have hu1 : IsUnit (legendreSym p (pfreeInt p a)) :=
    Int.isUnit_iff.mpr (legendreSym.eq_one_or_neg_one p (cast_pfreeInt_ne_zero p ha))
  have hu2 : IsUnit (legendreSym p (pfreeInt p b)) :=
    Int.isUnit_iff.mpr (legendreSym.eq_one_or_neg_one p (cast_pfreeInt_ne_zero p hb))
  unfold hilbertPadicInt
  exact (((IsUnit.neg isUnit_one).pow _).mul (hu1.pow _)).mul (hu2.pow _)

/-- **Bimultiplicativity of the signed symbol in the first argument** (nonzero arguments). -/
theorem hilbertPadicInt_mul_left {a₁ a₂ b : ℤ} (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) :
    hilbertPadicInt p (a₁ * a₂) b = hilbertPadicInt p a₁ b * hilbertPadicInt p a₂ b := by
  unfold hilbertPadicInt
  rw [pfreeInt_mul p ha₁ ha₂, padicValInt.mul ha₁ ha₂, legendreSym.mul]
  simp only [add_mul, pow_add, mul_pow]
  ring

/-- **Bimultiplicativity of the signed symbol in the second argument** (nonzero arguments). -/
theorem hilbertPadicInt_mul_right {a b₁ b₂ : ℤ} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    hilbertPadicInt p a (b₁ * b₂) = hilbertPadicInt p a b₁ * hilbertPadicInt p a b₂ := by
  unfold hilbertPadicInt
  rw [pfreeInt_mul p hb₁ hb₂, padicValInt.mul hb₁ hb₂, legendreSym.mul]
  simp only [mul_add, pow_add, mul_pow]
  ring

/-- **Symmetry of the signed symbol:** `(a,b)_p = (b,a)_p`. -/
theorem hilbertPadicInt_comm (a b : ℤ) : hilbertPadicInt p a b = hilbertPadicInt p b a := by
  unfold hilbertPadicInt
  rw [Nat.mul_comm (padicValInt p a) (padicValInt p b)]
  ring

end SKEFTHawking.HilbertSymbol
