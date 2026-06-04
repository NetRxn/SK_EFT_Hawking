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
import SKEFTHawking.HilbertSymbolPadic

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

/-- `χ₂(↑n) = (-1)^n` for `n : ℕ`. -/
theorem chi2_natCast (n : ℕ) : chi2 ((n : ℕ) : ZMod 2) = (-1 : ℤ) ^ n := by
  unfold chi2
  rw [ZMod.val_natCast, ← neg_one_pow_eq_pow_mod_two]

/-- For odd `p`, the dyadic character `ε(p)` is `p/2 mod 2`. -/
theorem eps2_natCast_odd {p : ℕ} (hp : Odd p) : eps2 (p : ZMod 8) = ((p / 2 : ℕ) : ZMod 2) := by
  have hp2 : p % 2 = 1 := Nat.odd_iff.mp hp
  unfold eps2
  rw [ZMod.val_natCast, ZMod.natCast_eq_natCast_iff]
  unfold Nat.ModEq
  omega

/-- **The dyadic cross term equals the reciprocity sign:** for odd `p, q`,
`χ₂(ε(p)·ε(q)) = (-1)^{(p/2)(q/2)}` — exactly the right-hand side of quadratic reciprocity. -/
theorem chi2_eps2_mul {p q : ℕ} (hp : Odd p) (hq : Odd q) :
    chi2 (eps2 (p : ZMod 8) * eps2 (q : ZMod 8)) = (-1 : ℤ) ^ (p / 2 * (q / 2)) := by
  rw [eps2_natCast_odd hp, eps2_natCast_odd hq, ← Nat.cast_mul, chi2_natCast]

/-- The `2`-free part of a nonzero natural, cast to `ZMod 8`, is a **unit** (it is odd, hence coprime to 8). -/
theorem isUnit_cast_ordCompl_two {n : ℕ} (hn : n ≠ 0) :
    IsUnit ((ordCompl[2] n : ℕ) : ZMod 8) := by
  rw [ZMod.isUnit_iff_coprime]
  have hodd : ¬ (2 : ℕ) ∣ ordCompl[2] n := Nat.not_dvd_ordCompl Nat.prime_two hn
  have hcop2 : Nat.Coprime (ordCompl[2] n) 2 :=
    (Nat.coprime_comm.mp ((Nat.prime_two.coprime_iff_not_dvd).mpr hodd))
  simpa using hcop2.pow_right 3

/-- An **odd integer**, cast to `ZMod 8`, is a **unit** (coprime to `8 = 2³`). The signed (ℤ) version of
`isUnit_cast_ordCompl_two`, for the signed dyadic Hilbert symbol. -/
theorem isUnit_intCast_zmod8 {z : ℤ} (h : ¬ (2 : ℤ) ∣ z) : IsUnit ((z : ℤ) : ZMod 8) := by
  have hcop : IsCoprime z (8 : ℤ) := by
    have hz2 : IsCoprime z (2 : ℤ) := ((Int.prime_two.coprime_iff_not_dvd).mpr h).symm
    rw [show (8 : ℤ) = 2 ^ 3 from by norm_num]
    exact hz2.pow_right
  obtain ⟨a, b, hab⟩ := hcop
  refine IsUnit.of_mul_eq_one ((a : ℤ) : ZMod 8) ?_
  have key : ((z : ℤ) : ZMod 8) * ((a : ℤ) : ZMod 8) = ((a * z : ℤ) : ZMod 8) := by
    push_cast; ring
  rw [key, show (a * z : ℤ) = 1 - b * 8 from by linear_combination hab]
  push_cast
  rw [show (8 : ZMod 8) = 0 from by decide]
  ring

/-- The **dyadic (`p = 2`) Hilbert symbol** on positive naturals, via the explicit ε/ω formula:
`(a,b)_2 = (-1)^{ε(u)ε(v) + α·ω(v) + β·ω(u)}` with `α,β = v₂`, `u,v = ` odd parts (`ordCompl[2]`). -/
def hilbert2Nat (a b : ℕ) : ℤ :=
  chi2 (eps2 ((ordCompl[2] a : ℕ) : ZMod 8) * eps2 ((ordCompl[2] b : ℕ) : ZMod 8)
    + (a.factorization 2 : ZMod 2) * omega2 ((ordCompl[2] b : ℕ) : ZMod 8)
    + (b.factorization 2 : ZMod 2) * omega2 ((ordCompl[2] a : ℕ) : ZMod 8))

/-- The dyadic symbol is `{±1}`-valued. -/
theorem hilbert2Nat_mem (a b : ℕ) : hilbert2Nat a b = 1 ∨ hilbert2Nat a b = -1 :=
  chi2_mem _

/-- **Bimultiplicativity of the dyadic symbol in the first argument** (nonzero arguments): the exponent is
additive (`eps2_mul`/`omega2_mul` supplementary laws + valuation additivity), and `χ₂` turns the sum into a
product. -/
theorem hilbert2Nat_mul_left {a₁ a₂ b : ℕ} (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) :
    hilbert2Nat (a₁ * a₂) b = hilbert2Nat a₁ b * hilbert2Nat a₂ b := by
  unfold hilbert2Nat
  rw [← chi2_add]
  congr 1
  rw [Nat.ordCompl_mul, Nat.cast_mul,
    eps2_mul (isUnit_cast_ordCompl_two ha₁) (isUnit_cast_ordCompl_two ha₂),
    omega2_mul (isUnit_cast_ordCompl_two ha₁) (isUnit_cast_ordCompl_two ha₂),
    Nat.factorization_mul ha₁ ha₂, Finsupp.add_apply]
  push_cast
  ring

/-- **Bimultiplicativity of the dyadic symbol in the second argument** (nonzero arguments). -/
theorem hilbert2Nat_mul_right {a b₁ b₂ : ℕ} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    hilbert2Nat a (b₁ * b₂) = hilbert2Nat a b₁ * hilbert2Nat a b₂ := by
  unfold hilbert2Nat
  rw [← chi2_add]
  congr 1
  rw [Nat.ordCompl_mul, Nat.cast_mul,
    eps2_mul (isUnit_cast_ordCompl_two hb₁) (isUnit_cast_ordCompl_two hb₂),
    omega2_mul (isUnit_cast_ordCompl_two hb₁) (isUnit_cast_ordCompl_two hb₂),
    Nat.factorization_mul hb₁ hb₂, Finsupp.add_apply]
  push_cast
  ring

/-- **Symmetry of the dyadic symbol:** `(a,b)_2 = (b,a)_2`. -/
theorem hilbert2Nat_comm (a b : ℕ) : hilbert2Nat a b = hilbert2Nat b a := by
  unfold hilbert2Nat
  rw [mul_comm (eps2 _) (eps2 _)]
  ring_nf

/-- The **signed (ℤ) dyadic Hilbert symbol** via the explicit ε/ω formula on the signed 2-free parts
(`pfreeInt 2`); the residue mod 8 absorbs the sign. Extends `hilbert2Nat` to all nonzero integers. -/
def hilbert2Int (a b : ℤ) : ℤ :=
  chi2 (eps2 ((pfreeInt 2 a : ℤ) : ZMod 8) * eps2 ((pfreeInt 2 b : ℤ) : ZMod 8)
    + (padicValInt 2 a : ZMod 2) * omega2 ((pfreeInt 2 b : ℤ) : ZMod 8)
    + (padicValInt 2 b : ZMod 2) * omega2 ((pfreeInt 2 a : ℤ) : ZMod 8))

/-- The signed dyadic symbol is `{±1}`-valued. -/
theorem hilbert2Int_mem (a b : ℤ) : hilbert2Int a b = 1 ∨ hilbert2Int a b = -1 :=
  chi2_mem _

/-- **Bimultiplicativity of the signed dyadic symbol in the first argument** (nonzero arguments). -/
theorem hilbert2Int_mul_left {a₁ a₂ b : ℤ} (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) :
    hilbert2Int (a₁ * a₂) b = hilbert2Int a₁ b * hilbert2Int a₂ b := by
  unfold hilbert2Int
  rw [← chi2_add]
  congr 1
  rw [pfreeInt_mul 2 ha₁ ha₂, Int.cast_mul,
    eps2_mul (isUnit_intCast_zmod8 (not_dvd_pfreeInt 2 ha₁)) (isUnit_intCast_zmod8 (not_dvd_pfreeInt 2 ha₂)),
    omega2_mul (isUnit_intCast_zmod8 (not_dvd_pfreeInt 2 ha₁)) (isUnit_intCast_zmod8 (not_dvd_pfreeInt 2 ha₂)),
    padicValInt.mul ha₁ ha₂]
  push_cast
  ring

/-- **Bimultiplicativity of the signed dyadic symbol in the second argument** (nonzero arguments). -/
theorem hilbert2Int_mul_right {a b₁ b₂ : ℤ} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    hilbert2Int a (b₁ * b₂) = hilbert2Int a b₁ * hilbert2Int a b₂ := by
  unfold hilbert2Int
  rw [← chi2_add]
  congr 1
  rw [pfreeInt_mul 2 hb₁ hb₂, Int.cast_mul,
    eps2_mul (isUnit_intCast_zmod8 (not_dvd_pfreeInt 2 hb₁)) (isUnit_intCast_zmod8 (not_dvd_pfreeInt 2 hb₂)),
    omega2_mul (isUnit_intCast_zmod8 (not_dvd_pfreeInt 2 hb₁)) (isUnit_intCast_zmod8 (not_dvd_pfreeInt 2 hb₂)),
    padicValInt.mul hb₁ hb₂]
  push_cast
  ring

/-- **Symmetry of the signed dyadic symbol:** `(a,b)_2 = (b,a)_2`. -/
theorem hilbert2Int_comm (a b : ℤ) : hilbert2Int a b = hilbert2Int b a := by
  unfold hilbert2Int
  rw [mul_comm (eps2 _) (eps2 _)]
  ring_nf

/-- `(1, b)_2 = 1` (the identity argument): `ε(1)=ω(1)=0` and `v₂(1)=0` kill the exponent. -/
theorem hilbert2Int_one_left (b : ℤ) : hilbert2Int 1 b = 1 := by
  have hv : padicValInt 2 1 = 0 := by simp [padicValInt]
  have hpf : pfreeInt 2 1 = 1 := by simp [pfreeInt, hv]
  unfold hilbert2Int
  rw [hv, hpf]
  simp [Int.cast_one, eps2_one, omega2_one]

/-- `(a, 1)_2 = 1`. -/
theorem hilbert2Int_one_right (a : ℤ) : hilbert2Int a 1 = 1 := by
  rw [hilbert2Int_comm]; exact hilbert2Int_one_left a

/-- **Dyadic ↔ Legendre supplementary law for `-1`:** for an odd prime `q`, `χ₂(ε(q)) = (q | -1)` — i.e. the
dyadic exponent `ε(q)` matches `legendreSym q (-1) = χ₄ q`. Proved by a finite check over the units of
`ZMod 8` plus cast compatibility `ZMod 8 → ZMod 4`. -/
theorem chi2_eps2_eq_legendre_neg_one (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) :
    chi2 (eps2 (q : ZMod 8)) = legendreSym q (-1) := by
  rw [legendreSym.at_neg_one hq]
  have hu : IsUnit ((q : ℕ) : ZMod 8) := by
    rw [ZMod.isUnit_iff_coprime]
    exact (Nat.coprime_primes Fact.out Nat.prime_two |>.mpr hq).pow_right 3
  have key : ∀ x : ZMod 8, IsUnit x →
      chi2 (eps2 x) = ZMod.χ₄ (ZMod.castHom (by norm_num : (4 : ℕ) ∣ 8) (ZMod 4) x) := by decide
  rw [key _ hu]
  congr 1
  exact map_natCast _ q

/-- **Dyadic ↔ Legendre supplementary law for `2`:** for an odd prime `q`, `χ₂(ω(q)) = (q | 2)` — i.e. the
dyadic exponent `ω(q)` matches `legendreSym q 2 = χ₈ q`. Both live on `ZMod 8`, so this is a direct finite
check over its units. -/
theorem chi2_omega2_eq_legendre_two (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) :
    chi2 (omega2 (q : ZMod 8)) = legendreSym q 2 := by
  rw [legendreSym.at_two hq]
  have hu : IsUnit ((q : ℕ) : ZMod 8) := by
    rw [ZMod.isUnit_iff_coprime]
    exact (Nat.coprime_primes Fact.out Nat.prime_two |>.mpr hq).pow_right 3
  have key : ∀ x : ZMod 8, IsUnit x → chi2 (omega2 x) = ZMod.χ₈ x := by decide
  exact key _ hu

/-- `(-1, -1)_2 = -1`: both odd parts are `-1 ≡ 7 mod 8`, `ε(7)=1`, so the exponent is `ε(7)·ε(7)=1` and
`χ₂(1) = -1`. This is the dyadic contribution that cancels the real `(-1,-1)_∞ = -1` in the product formula. -/
theorem hilbert2Int_neg_one_neg_one : hilbert2Int (-1) (-1) = -1 := by
  have hv : padicValInt 2 (-1) = 0 := by simp [padicValInt]
  have hpf : pfreeInt 2 (-1) = -1 := by simp [pfreeInt, hv]
  unfold hilbert2Int
  rw [hv, hpf]
  decide

/-- `(-1, q)_2 = χ₂(ε(q))` for odd `q`: the `a = -1` exponent collapses to `ε(-1)·ε(q) = ε(q)` (`ε(-1)=1`,
both valuations zero). For prime `q` this equals `legendreSym q (-1)` via `chi2_eps2_eq_legendre_neg_one`. -/
theorem hilbert2Int_neg_one_odd {q : ℤ} (hq : ¬ (2 : ℤ) ∣ q) :
    hilbert2Int (-1) q = chi2 (eps2 (q : ZMod 8)) := by
  have hv1 : padicValInt 2 (-1) = 0 := by simp [padicValInt]
  have hvq : padicValInt 2 q = 0 := padicValInt.eq_zero_of_not_dvd hq
  have hpf1 : pfreeInt 2 (-1) = -1 := by simp [pfreeInt, hv1]
  have hpfq : pfreeInt 2 q = q := by simp [pfreeInt, hvq]
  unfold hilbert2Int
  rw [hv1, hvq, hpf1, hpfq]
  simp only [Int.cast_neg, Int.cast_one, Nat.cast_zero, zero_mul, add_zero]
  rw [show eps2 (-1 : ZMod 8) = 1 from by decide, one_mul]

/-- `(2, q)_2 = χ₂(ω(q))` for odd `q`: the `a = 2` exponent collapses to `v₂(2)·ω(q) = ω(q)` (`ε(1)=0`,
`v₂(2)=1`). For prime `q` this equals `legendreSym q 2` via `chi2_omega2_eq_legendre_two`. -/
theorem hilbert2Int_two_odd {q : ℤ} (hq : ¬ (2 : ℤ) ∣ q) :
    hilbert2Int 2 q = chi2 (omega2 (q : ZMod 8)) := by
  have hv2 : padicValInt 2 2 = 1 := padicValInt_self
  have hvq : padicValInt 2 q = 0 := padicValInt.eq_zero_of_not_dvd hq
  have hpf2 : pfreeInt 2 2 = 1 := by simp [pfreeInt, hv2]
  have hpfq : pfreeInt 2 q = q := by simp [pfreeInt, hvq]
  unfold hilbert2Int
  rw [hv2, hvq, hpf2, hpfq]
  simp only [Int.cast_one, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, add_zero]
  rw [show eps2 (1 : ZMod 8) = 0 from by decide, zero_mul, zero_add]

/-- `(p, q)_2 = χ₂(ε(p)·ε(q))` for odd `p, q`: both valuations vanish, so the exponent is just `ε(p)·ε(q)`. -/
theorem hilbert2Int_odd_odd {p q : ℤ} (hp : ¬ (2 : ℤ) ∣ p) (hq : ¬ (2 : ℤ) ∣ q) :
    hilbert2Int p q = chi2 (eps2 (p : ZMod 8) * eps2 (q : ZMod 8)) := by
  have hvp : padicValInt 2 p = 0 := padicValInt.eq_zero_of_not_dvd hp
  have hvq : padicValInt 2 q = 0 := padicValInt.eq_zero_of_not_dvd hq
  have hpfp : pfreeInt 2 p = p := by simp [pfreeInt, hvp]
  have hpfq : pfreeInt 2 q = q := by simp [pfreeInt, hvq]
  unfold hilbert2Int
  rw [hvp, hvq, hpfp, hpfq]
  simp only [Nat.cast_zero, zero_mul, add_zero]

end SKEFTHawking.HilbertSymbol
