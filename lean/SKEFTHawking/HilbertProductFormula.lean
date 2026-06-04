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

/-- **Support is contained in the divisors of `2ab`.** Only primes dividing `2ab` give a nontrivial place
symbol. -/
theorem hilbertPrime_mulSupport_subset {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Function.mulSupport (fun p => hilbertPrime p a b) ⊆ ↑(Nat.divisors (2 * a.natAbs * b.natAbs)) := by
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

/-- **The place symbol has finite support.** So the product over all places is a finite product. -/
theorem hilbertPrime_mulSupport_finite {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (Function.mulSupport (fun p => hilbertPrime p a b)).Finite :=
  Set.Finite.subset (Nat.divisors (2 * a.natAbs * b.natAbs)).finite_toSet
    (hilbertPrime_mulSupport_subset ha hb)

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

/-- `(1, b)_p = 1` at every place. -/
theorem hilbertPrime_one_left (p : ℕ) (b : ℤ) : hilbertPrime p 1 b = 1 := by
  unfold hilbertPrime
  split_ifs with hp h2
  · letI := Fact.mk hp; exact hilbert2Int_one_left b
  · letI := Fact.mk hp; exact hilbertPadicInt_one_left p b
  · rfl

/-- **Product formula, base case:** `∏_v (1,b)_v = 1` (the identity argument; base of the multiplicative
reduction of the product formula to generators). -/
theorem hilbertGlobalProd_one_left (b : ℤ) : hilbertGlobalProd 1 b = 1 := by
  unfold hilbertGlobalProd
  rw [show ((1 : ℤ) : ℝ) = 1 from by norm_num, hilbertReal_one_left,
    finprod_congr (fun p => hilbertPrime_one_left p b), finprod_one, one_mul]

/-- **Concrete evaluation of the global product.** The finitely-supported product over primes collapses to a
finite `Finset` product over the divisors of `2ab` — the form used to evaluate `∏_v (a,b)_v` on generators. -/
theorem hilbertGlobalProd_eq_finset_prod {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertGlobalProd a b
      = hilbertReal (a : ℝ) (b : ℝ)
        * ∏ p ∈ Nat.divisors (2 * a.natAbs * b.natAbs), hilbertPrime p a b := by
  unfold hilbertGlobalProd
  rw [finprod_eq_finset_prod_of_mulSupport_subset _ (hilbertPrime_mulSupport_subset ha hb)]

/-- **Product formula, generator `(-1,-1)`:** `∏_v (-1,-1)_v = 1`. The real place and the dyadic place each
contribute `-1` (both `-1` are negative; `ε(-1)=1`), and these cancel; all odd places are trivial. -/
theorem hilbertGlobalProd_neg_one_neg_one : hilbertGlobalProd (-1) (-1) = 1 := by
  rw [hilbertGlobalProd_eq_finset_prod (by norm_num) (by norm_num),
    show Nat.divisors (2 * (-1 : ℤ).natAbs * (-1 : ℤ).natAbs) = {1, 2} from by decide,
    Finset.prod_insert (by decide), Finset.prod_singleton,
    hilbertPrime_of_not_prime (by decide), hilbertPrime_two, hilbert2Int_neg_one_neg_one,
    show ((-1 : ℤ) : ℝ) = -1 from by norm_num, hilbertReal_neg_neg (by norm_num) (by norm_num)]
  ring

/-- **Product formula, generator `(-1, q)` for an odd prime `q`:** `∏_v (-1,q)_v = 1`. Only the places `2`
and `q` contribute; both equal `legendreSym q (-1)` (the dyadic value via the supplementary law, the `q`-adic
value as the uniformizer Legendre symbol), so their product is `(legendreSym q (-1))² = 1`. -/
theorem hilbertGlobalProd_neg_one_prime (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) :
    hilbertGlobalProd (-1) (q : ℤ) = 1 := by
  have hqoddN : ¬ 2 ∣ q := by
    have h1 : q % 2 = 1 := Nat.odd_iff.mp ((Fact.out : q.Prime).odd_of_ne_two hq); omega
  have hqodd : ¬ (2 : ℤ) ∣ (q : ℤ) := fun h => hqoddN (by exact_mod_cast h)
  have hqnd1 : ¬ (q : ℤ) ∣ (-1 : ℤ) := fun h =>
    (Fact.out : q.Prime).ne_one (Nat.dvd_one.mp (by exact_mod_cast (dvd_neg.mp h)))
  have hsub : Function.mulSupport (fun p => hilbertPrime p (-1) (q : ℤ)) ⊆ ↑({2, q} : Finset ℕ) := by
    intro p hp
    simp only [Function.mem_mulSupport] at hp
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra hpne
    push_neg at hpne
    apply hp
    by_cases hpp : p.Prime
    · refine hilbertPrime_units hpp hpne.1 ?_ ?_
      · intro h
        exact hpp.ne_one (Nat.dvd_one.mp (by exact_mod_cast (dvd_neg.mp h)))
      · intro hpd
        exact hpne.2 ((Nat.prime_dvd_prime_iff_eq hpp Fact.out).mp
          (Int.natCast_dvd_natCast.mp (by exact_mod_cast hpd)))
    · exact hilbertPrime_of_not_prime hpp _ _
  unfold hilbertGlobalProd
  rw [finprod_eq_finset_prod_of_mulSupport_subset _ hsub,
    Finset.prod_insert (by simp [Ne.symm hq]), Finset.prod_singleton,
    hilbertPrime_two, hilbertPrime_odd Fact.out hq,
    hilbert2Int_neg_one_odd hqodd, @Int.cast_natCast (ZMod 8) _ q, chi2_eps2_eq_legendre_neg_one q hq,
    hilbertPadicInt_eq_legendre q hqnd1,
    show ((-1 : ℤ) : ℝ) = -1 from by norm_num,
    hilbertReal_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ ((q : ℤ) : ℝ))]
  rcases legendreSym.eq_one_or_neg_one q
      (show ((-1 : ℤ) : ZMod q) ≠ 0 by push_cast; exact neg_ne_zero.mpr one_ne_zero) with h | h <;>
    · rw [h]; ring

end SKEFTHawking.HilbertSymbol
