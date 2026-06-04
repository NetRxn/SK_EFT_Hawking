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

/-- **Bimultiplicativity of the place symbol in the first argument** (nonzero arguments). -/
theorem hilbertPrime_mul_left {p : ℕ} {a₁ a₂ b : ℤ} (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) :
    hilbertPrime p (a₁ * a₂) b = hilbertPrime p a₁ b * hilbertPrime p a₂ b := by
  unfold hilbertPrime
  split_ifs with hp h2
  · letI := Fact.mk hp; exact hilbert2Int_mul_left ha₁ ha₂
  · letI := Fact.mk hp; exact hilbertPadicInt_mul_left p ha₁ ha₂
  · ring

/-- **Bimultiplicativity of the place symbol in the second argument** (nonzero arguments). -/
theorem hilbertPrime_mul_right {p : ℕ} {a b₁ b₂ : ℤ} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    hilbertPrime p a (b₁ * b₂) = hilbertPrime p a b₁ * hilbertPrime p a b₂ := by
  unfold hilbertPrime
  split_ifs with hp h2
  · letI := Fact.mk hp; exact hilbert2Int_mul_right hb₁ hb₂
  · letI := Fact.mk hp; exact hilbertPadicInt_mul_right p hb₁ hb₂
  · ring

/-- **Symmetry of the place symbol.** -/
theorem hilbertPrime_comm (p : ℕ) (a b : ℤ) : hilbertPrime p a b = hilbertPrime p b a := by
  unfold hilbertPrime
  split_ifs with hp h2
  · letI := Fact.mk hp; exact hilbert2Int_comm a b
  · letI := Fact.mk hp; exact hilbertPadicInt_comm p a b
  · rfl

/-- **The place symbol has finite support.** For nonzero `a, b`, `hilbertPrime p a b = 1` for all but finitely
many `p` (only primes dividing `2ab` can be nontrivial), so the product over all places is a finite product. -/
theorem hilbertPrime_mulSupport_finite {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (Function.mulSupport (fun p => hilbertPrime p a b)).Finite := by
  apply Set.Finite.subset (Nat.divisors (2 * a.natAbs * b.natAbs)).finite_toSet
  intro p hp
  simp only [Function.mem_mulSupport] at hp
  have hm0 : 2 * a.natAbs * b.natAbs ≠ 0 := by
    simp [Int.natAbs_eq_zero, ha, hb]
  rw [Finset.mem_coe, Nat.mem_divisors]
  refine ⟨?_, hm0⟩
  by_cases hpp : p.Prime
  · by_cases h2 : p = 2
    · exact h2 ▸ ⟨a.natAbs * b.natAbs, by ring⟩
    · by_contra hnd
      apply hp
      refine hilbertPrime_units hpp h2 ?_ ?_
      · intro hda
        have hpa : p ∣ a.natAbs := Int.natCast_dvd_natCast.mp ((Int.dvd_natAbs).mpr hda)
        exact hnd ((hpa.mul_left 2).mul_right b.natAbs)
      · intro hdb
        have hpb : p ∣ b.natAbs := Int.natCast_dvd_natCast.mp ((Int.dvd_natAbs).mpr hdb)
        exact hnd (hpb.mul_left (2 * a.natAbs))
  · exact absurd (hilbertPrime_of_not_prime hpp a b) hp

/-- The **global Hilbert product** `∏_v (a,b)_v = (a,b)_∞ · ∏_p (a,b)_p` over all places (the real place
times the finitely-supported product over primes). The **product formula** is the theorem that this equals
`1`; it is the arithmetic heart of Hasse–Minkowski. -/
noncomputable def hilbertGlobalProd (a b : ℤ) : ℤ :=
  hilbertReal (a : ℝ) (b : ℝ) * ∏ᶠ p : ℕ, hilbertPrime p a b

/-- **Bimultiplicativity of the global product in the first argument** (nonzero arguments): each place factor
is bimultiplicative and the finitely-supported products distribute. -/
theorem hilbertGlobalProd_mul_left {a₁ a₂ b : ℤ} (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (hb : b ≠ 0) :
    hilbertGlobalProd (a₁ * a₂) b = hilbertGlobalProd a₁ b * hilbertGlobalProd a₂ b := by
  unfold hilbertGlobalProd
  rw [show ((a₁ * a₂ : ℤ) : ℝ) = (a₁ : ℝ) * (a₂ : ℝ) from by push_cast; ring,
    hilbertReal_mul_left (Int.cast_ne_zero.mpr ha₁) (Int.cast_ne_zero.mpr ha₂),
    finprod_congr (fun p => hilbertPrime_mul_left (p := p) ha₁ ha₂),
    finprod_mul_distrib (hilbertPrime_mulSupport_finite ha₁ hb)
      (hilbertPrime_mulSupport_finite ha₂ hb)]
  ring

/-- **Bimultiplicativity of the global product in the second argument** (nonzero arguments). -/
theorem hilbertGlobalProd_mul_right {a b₁ b₂ : ℤ} (ha : a ≠ 0) (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    hilbertGlobalProd a (b₁ * b₂) = hilbertGlobalProd a b₁ * hilbertGlobalProd a b₂ := by
  unfold hilbertGlobalProd
  rw [show ((b₁ * b₂ : ℤ) : ℝ) = (b₁ : ℝ) * (b₂ : ℝ) from by push_cast; ring,
    hilbertReal_mul_right (Int.cast_ne_zero.mpr hb₁) (Int.cast_ne_zero.mpr hb₂),
    finprod_congr (fun p => hilbertPrime_mul_right (p := p) hb₁ hb₂),
    finprod_mul_distrib (hilbertPrime_mulSupport_finite ha hb₁)
      (hilbertPrime_mulSupport_finite ha hb₂)]
  ring

end SKEFTHawking.HilbertSymbol
