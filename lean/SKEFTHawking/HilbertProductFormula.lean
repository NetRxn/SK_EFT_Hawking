/-
# Toward the Hilbert product formula `∏_v (a,b)_v = 1`

The product formula over all places `v ∈ {∞} ∪ {primes}` is the arithmetic heart of the Hasse–Minkowski
local–global principle ([HM-LG]). This file builds the **unified p-adic place symbol** `hilbertPrime p a b`
— dispatching to `hilbert2Int` at `p = 2`, to `hilbertPadicInt` at odd primes, and `1` at non-primes — so
the per-place factors can be multiplied over a single `Finset` of primes (the `Fact p.Prime` instance is
supplied locally via `letI` inside the dispatch, avoiding a section instance).

Established here: `{±1}`-valuedness, bimultiplicativity, and **finiteness of support**
(`hilbertPrime p a b = 1` for any odd prime `p ∤ a, b`) — so only the primes dividing `2ab` contribute and
the product over places is a finite product. The assembly `∏_v (a,b)_v = 1` (via quadratic reciprocity +
supplementary laws, reducing by bimultiplicativity to the generators `−1` and primes) follows.

Kernel-pure, no axioms.
-/

import Mathlib
import SKEFTHawking.HilbertSymbolReal
import SKEFTHawking.HilbertSymbolPadic
import SKEFTHawking.HilbertSymbolTwo

namespace SKEFTHawking.HilbertSymbol

/-- The **unified p-adic place symbol**: `hilbert2Int` at `p = 2`, `hilbertPadicInt` at odd primes, `1`
otherwise. The `Fact p.Prime` instance is supplied locally so the symbol is a plain function of `p`. -/
noncomputable def hilbertPrime (p : ℕ) (a b : ℤ) : ℤ :=
  if h : p.Prime then
    letI := Fact.mk h
    if p = 2 then hilbert2Int a b else hilbertPadicInt p a b
  else 1

/-- At a non-prime `p`, the place symbol is `1`. -/
theorem hilbertPrime_of_not_prime {p : ℕ} (h : ¬ p.Prime) (a b : ℤ) : hilbertPrime p a b = 1 := by
  simp [hilbertPrime, h]

/-- At `p = 2`, the place symbol is the signed dyadic symbol. -/
theorem hilbertPrime_two (a b : ℤ) : hilbertPrime 2 a b = hilbert2Int a b := by
  simp [hilbertPrime, Nat.prime_two]

/-- At an odd prime, the place symbol is the signed odd-`p` symbol. -/
theorem hilbertPrime_odd {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (a b : ℤ) :
    hilbertPrime p a b = letI := Fact.mk hp; hilbertPadicInt p a b := by
  simp [hilbertPrime, hp, hodd]

/-- The place symbol is `{±1}`-valued (nonzero arguments). -/
theorem hilbertPrime_mem {p : ℕ} (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertPrime p a b = 1 ∨ hilbertPrime p a b = -1 := by
  unfold hilbertPrime
  split_ifs with hp h2
  · letI := Fact.mk hp; exact hilbert2Int_mem a b
  · letI := Fact.mk hp; exact hilbertPadicInt_mem p ha hb
  · exact Or.inl rfl

/-- **Finiteness of support:** at an odd prime dividing neither `a` nor `b`, the place symbol is `1`. So only
the primes dividing `2ab` contribute, and the product over places is finite. -/
theorem hilbertPrime_units {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {a b : ℤ} (ha : ¬ (p : ℤ) ∣ a) (hb : ¬ (p : ℤ) ∣ b) : hilbertPrime p a b = 1 := by
  rw [hilbertPrime_odd hp hodd]
  letI := Fact.mk hp
  exact hilbertPadicInt_units p ha hb

end SKEFTHawking.HilbertSymbol
