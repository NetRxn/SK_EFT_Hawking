import Mathlib
import SKEFTHawking.PadicSquare
import SKEFTHawking.HilbertProductFormula

/-!
# Global Hasse–Minkowski: from local representability to a global common value

This module sits above the per-place represents⟺symbol theory (`PadicSquare`) and the global Hilbert
product formula (`HilbertProductFormula`). It is where the **global existence of a value `t` represented by
two binary forms at every place** is assembled — the sole remaining keystone of the Phase 5q.B `[HM]`
indefinite-even-unimodular leg (the rest of the `n = 4` reduction, `quaternary_isotropic_of_keystone`, is
already a theorem in `PadicSquare`).

## Architecture

At every place `v` (odd `p`, `p = 2`, `∞`) the local criterion is now linear in the unknown `t`:
`⟨a,b⟩` represents `t` over `ℚ_v` iff `(t, −ab)_v = (a,b)_v` (`PadicSquare.represents_*_iff_symbol_linear`).
The finite-place criteria are consolidated here into the unified `hilbertPrime`-level statement, so the
global step is governed directly by `HilbertProductFormula.hilbertGlobalProd_eq_one` (the product formula,
`∏_v (a,b)_v = 1`). The remaining mathematical content is **Serre, *Course in Arithmetic*, Ch. III §2.2,
Theorem 4** — the global existence of `t ∈ ℚˣ` with prescribed Hilbert symbols at all places, given the
consistency conditions (almost-all-`1`, product `= 1`, per-place realizability).

## Anti-circularity

Routes through quadratic-form / Hilbert-symbol arithmetic only (quadratic reciprocity, Dirichlet on primes
in arithmetic progressions, the product formula). It does NOT use ABP, the Adams spectral sequence, or
Rokhlin's theorem — Rokhlin's theorem `16 ∣ σ` is the eventual conclusion downstream.
-/

namespace SKEFTHawking

open SKEFTHawking.HilbertSymbol

/-- **Linear-in-`t` represents⟺symbol at a finite place, unified over `hilbertPrime`.** For any prime `p`,
`⟨a,b⟩` represents `t` over `ℚ_p` iff `(t, −ab)_p = (a,b)_p`, where the symbol is the unified place symbol
`hilbertPrime` (which is `hilbert2Int` at `p = 2` and `hilbertPadicInt p` at odd `p`). Dispatches to
`represents_2adic_iff_symbol_linear` / `represents_padic_iff_symbol_linear_odd`. This is the finite-place
input to Serre's Theorem 4 in the form the product formula `hilbertGlobalProd_eq_one` governs. -/
theorem represents_padic_iff_hilbertPrime_linear {p : ℕ} [Fact p.Prime] {a b t : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0) :
    (∃ u v : ℚ_[p], (a : ℚ_[p]) * u ^ 2 + (b : ℚ_[p]) * v ^ 2 = (t : ℚ_[p])) ↔
    hilbertPrime p t (-(a * b)) = hilbertPrime p a b := by
  have hp : p.Prime := Fact.out
  by_cases h2 : p = 2
  · subst h2
    rw [hilbertPrime_two, hilbertPrime_two, represents_2adic_iff_symbol_linear ha hb ht]
  · rw [hilbertPrime_odd hp h2, hilbertPrime_odd hp h2,
        represents_padic_iff_symbol_linear_odd h2 ha hb ht]

/-- **Global represents⟺symbol packaging.** `⟨a,b⟩` represents the integer `t` at *every* place (ℝ and all
ℚ_p) iff the linear Hilbert-symbol prescription `(t,−ab)_v = (a,b)_v` holds at every place. Just the
conjunction of the per-place trio (`represents_real_iff_symbol_linear` at ∞,
`represents_padic_iff_hilbertPrime_linear` at finite places). This is the bridge between the two faces of the
`n = 4` keystone: the LHS is exactly the `everywhere-represented` hypothesis `quaternary_isotropic_of_keystone`
consumes; the RHS is exactly the prescribed-Hilbert-symbol conclusion Serre Ch III §2.2 Theorem 4 produces.
So once Serre Thm 4 is proven, a global `t` with the RHS symbols yields the LHS representability, hence the
keystone, hence `n = 4` Hasse–Minkowski. -/
theorem represents_everywhere_iff_symbols {a b t : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0) :
    ((∃ u v : ℝ, (a : ℝ) * u ^ 2 + (b : ℝ) * v ^ 2 = (t : ℝ)) ∧
      (∀ (p : ℕ) [Fact p.Prime], ∃ u v : ℚ_[p],
        (a : ℚ_[p]) * u ^ 2 + (b : ℚ_[p]) * v ^ 2 = (t : ℚ_[p]))) ↔
    (HilbertSymbol.hilbertReal (t : ℝ) ((-(a * b) : ℤ) : ℝ) = HilbertSymbol.hilbertReal (a : ℝ) (b : ℝ) ∧
      (∀ (p : ℕ) [Fact p.Prime], hilbertPrime p t (-(a * b)) = hilbertPrime p a b)) := by
  constructor
  · rintro ⟨hR, hloc⟩
    exact ⟨(represents_real_iff_symbol_linear ha hb ht).mp hR,
      fun p _ => (represents_padic_iff_hilbertPrime_linear ha hb ht).mp (hloc p)⟩
  · rintro ⟨hR, hsym⟩
    exact ⟨(represents_real_iff_symbol_linear ha hb ht).mpr hR,
      fun p _ => (represents_padic_iff_hilbertPrime_linear ha hb ht).mpr (hsym p)⟩

/-- **Product-formula closure: the real place comes for free.** If the linear Hilbert-symbol prescription
`(t, −ab)_p = (a,b)_p` holds at *every finite place* `p`, then it holds at the real place too. This is the
distinguished-place mechanism of Serre Ch III §2.2 Theorem 4: both global products `∏_v (t,−ab)_v` and
`∏_v (a,b)_v` equal `1` (`hilbertGlobalProd_eq_one`), so once the finite-place factors agree their (common,
nonzero, ±1-valued) product cancels and the two real factors must be equal. Using `∞` as the free place means
the construction only has to *match the symbols at the finitely many bad finite places* — the archimedean
condition is then automatic, removing one degree of constraint exactly as the product formula dictates. -/
theorem hilbertReal_eq_of_hilbertPrime_eq {a b t : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0)
    (hfin : ∀ p : ℕ, hilbertPrime p t (-(a * b)) = hilbertPrime p a b) :
    hilbertReal ((t : ℤ) : ℝ) ((-(a * b) : ℤ) : ℝ) = hilbertReal ((a : ℤ) : ℝ) ((b : ℤ) : ℝ) := by
  have hab : -(a * b) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero ha hb)
  have h1 := hilbertGlobalProd_eq_one ht hab
  have h2 := hilbertGlobalProd_eq_one ha hb
  unfold hilbertGlobalProd at h1 h2
  rw [finprod_congr hfin] at h1
  have hP : (∏ᶠ p : ℕ, hilbertPrime p a b) ≠ 0 := by
    intro h; rw [h, mul_zero] at h2; exact one_ne_zero h2.symm
  exact mul_right_cancel₀ hP (h1.trans h2.symm)

/-- **Product-formula closure at a chosen finite place.** If the linear Hilbert-symbol prescription
`(t,−ab)_p = (a,b)_p` holds at the real place and at *every finite place except one prime `q`*, then it holds
at `q` too. This is the general distinguished-place mechanism of Serre Ch III §2.2 Theorem 4 (the companion of
`hilbertReal_eq_of_hilbertPrime_eq`, which takes `∞` as the free place): both global products are `1`, so once
all-but-`q` factors agree, the common (nonzero, ±1) cofactor cancels and the two `q`-factors are equal. Lets
the construction designate *any* place as the one recovered for free — exactly the degree of freedom the
product formula supplies. -/
theorem hilbertPrime_eq_of_others {a b t : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0) (q : ℕ)
    (hreal : hilbertReal ((t : ℤ) : ℝ) ((-(a * b) : ℤ) : ℝ) = hilbertReal ((a : ℤ) : ℝ) ((b : ℤ) : ℝ))
    (hfin : ∀ p : ℕ, p ≠ q → hilbertPrime p t (-(a * b)) = hilbertPrime p a b) :
    hilbertPrime q t (-(a * b)) = hilbertPrime q a b := by
  have hab : -(a * b) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero ha hb)
  have h1 := hilbertGlobalProd_eq_one ht hab
  have h2 := hilbertGlobalProd_eq_one ha hb
  unfold hilbertGlobalProd at h1 h2
  rw [← mul_finprod_cond_ne q (hilbertPrime_mulSupport_finite ht hab)] at h1
  rw [← mul_finprod_cond_ne q (hilbertPrime_mulSupport_finite ha hb)] at h2
  have hcond : (∏ᶠ (p : ℕ) (_ : p ≠ q), hilbertPrime p t (-(a * b)))
      = ∏ᶠ (p : ℕ) (_ : p ≠ q), hilbertPrime p a b :=
    finprod_congr (fun p => finprod_congr (fun hpq => hfin p hpq))
  rw [hcond, hreal] at h1
  have hKPg : hilbertReal ((a : ℤ) : ℝ) ((b : ℤ) : ℝ) * (∏ᶠ (p : ℕ) (_ : p ≠ q), hilbertPrime p a b) ≠ 0 := by
    intro h
    rw [show hilbertReal ((a : ℤ) : ℝ) ((b : ℤ) : ℝ) * (hilbertPrime q a b *
        ∏ᶠ (p : ℕ) (_ : p ≠ q), hilbertPrime p a b)
        = (hilbertReal ((a : ℤ) : ℝ) ((b : ℤ) : ℝ) *
        ∏ᶠ (p : ℕ) (_ : p ≠ q), hilbertPrime p a b) * hilbertPrime q a b by ring, h, zero_mul] at h2
    exact one_ne_zero h2.symm
  exact mul_left_cancel₀ hKPg (by linear_combination h1.trans h2.symm)

/-- **Keystone in pure Hilbert-symbol form (the Serre Thm 4 output shape).** If there is a single nonzero
integer `t` whose linear Hilbert-symbol prescriptions match *both* binary parts at *every* place — ℝ and all
ℚ_p, for `(t,−ab)` against `(a,b)` and `(t,−cd)` against `(c,d)` — then the quaternary
`a x² + b y² = c z² + d w²` has a nontrivial rational solution. (`represents_everywhere_iff_symbols` turns the
symbol prescriptions into everywhere-representability of `t` by both binaries; `quaternary_isotropic_of_keystone`
assembles.) This is exactly the interface between Serre Ch III §2.2 Theorem 4 (which produces such a global `t`
with prescribed symbols) and the rank-4 Hasse–Minkowski conclusion: the *sole* remaining input to `n = 4` HM is
the construction of this `t`. -/
theorem quaternary_isotropic_of_symbol_keystone {a b c d : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hkey : ∃ t : ℤ, t ≠ 0 ∧
      (hilbertReal ((t : ℤ) : ℝ) ((-(a * b) : ℤ) : ℝ) = hilbertReal ((a : ℤ) : ℝ) ((b : ℤ) : ℝ)) ∧
      (∀ (p : ℕ) [Fact p.Prime], hilbertPrime p t (-(a * b)) = hilbertPrime p a b) ∧
      (hilbertReal ((t : ℤ) : ℝ) ((-(c * d) : ℤ) : ℝ) = hilbertReal ((c : ℤ) : ℝ) ((d : ℤ) : ℝ)) ∧
      (∀ (p : ℕ) [Fact p.Prime], hilbertPrime p t (-(c * d)) = hilbertPrime p c d)) :
    ∃ x y z w : ℚ, ¬(x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) ∧
      (a : ℚ) * x ^ 2 + (b : ℚ) * y ^ 2 = (c : ℚ) * z ^ 2 + (d : ℚ) * w ^ 2 := by
  obtain ⟨t, ht, hRab, hPab, hRcd, hPcd⟩ := hkey
  obtain ⟨hRab', hlocab⟩ := (represents_everywhere_iff_symbols ha hb ht).mpr ⟨hRab, hPab⟩
  obtain ⟨hRcd', hloccd⟩ := (represents_everywhere_iff_symbols hc hd ht).mpr ⟨hRcd, hPcd⟩
  refine quaternary_isotropic_of_keystone (by exact_mod_cast ha) (by exact_mod_cast hb)
    (by exact_mod_cast hc) (by exact_mod_cast hd) ⟨(t : ℚ), by exact_mod_cast ht, ?_, ?_, ?_, ?_⟩
  · obtain ⟨u, v, h⟩ := hRab'; exact ⟨u, v, by push_cast at h ⊢; linear_combination h⟩
  · intro p _; obtain ⟨u, v, h⟩ := hlocab p; exact ⟨u, v, by push_cast at h ⊢; linear_combination h⟩
  · obtain ⟨u, v, h⟩ := hRcd'; exact ⟨u, v, by push_cast at h ⊢; linear_combination h⟩
  · intro p _; obtain ⟨u, v, h⟩ := hloccd p; exact ⟨u, v, by push_cast at h ⊢; linear_combination h⟩

/-- **Symbol-form bad-place certificate (odd `p`).** From local quaternary isotropy over `ℚ_[p]` (odd `p`),
an integer common value `m ≠ 0` such that every integer `t ≡ m (mod p^{v_p(m)+1})` matches *both* families'
Hilbert symbols at `p`: `(t,−ab)_p = (a,b)_p` and `(t,−cd)_p = (c,d)_p` (in the unified `hilbertPrime` form).
The representation certificate `binary_pair_represents_of_congr_odd` converted to the symbol currency the
keystone construction works in (`represents_padic_iff_hilbertPrime_linear`). At each bad odd prime the
prime-power-CRT value of the construction matches both symbols. -/
theorem hilbertPrime_pair_match_of_congr_odd {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a b c d : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hiso : ∃ x y z w : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) ∧
      (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2 = (c : ℚ_[p]) * z ^ 2 + (d : ℚ_[p]) * w ^ 2) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ {t : ℤ}, t ≠ 0 → (p : ℤ) ^ (padicValInt p m + 1) ∣ (t - m) →
      hilbertPrime p t (-(a * b)) = hilbertPrime p a b ∧
      hilbertPrime p t (-(c * d)) = hilbertPrime p c d := by
  obtain ⟨m, hm, hcert⟩ := binary_pair_represents_of_congr_odd hp ha hb hc hd hiso
  refine ⟨m, hm, fun {t} ht hcong => ?_⟩
  obtain ⟨hrab, hrcd⟩ := hcert ht hcong
  exact ⟨(represents_padic_iff_hilbertPrime_linear ha hb ht).mp hrab,
         (represents_padic_iff_hilbertPrime_linear hc hd ht).mp hrcd⟩

/-- **Symbol-form bad-place certificate at `p = 2`** (the `p = 2` analogue, mod `2^{v_2(m)+3}`). -/
theorem hilbertPrime_pair_match_of_congr_2 {a b c d : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hiso : ∃ x y z w : ℚ_[2], ¬(x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) ∧
      (a : ℚ_[2]) * x ^ 2 + (b : ℚ_[2]) * y ^ 2 = (c : ℚ_[2]) * z ^ 2 + (d : ℚ_[2]) * w ^ 2) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ {t : ℤ}, t ≠ 0 → (2 : ℤ) ^ (padicValInt 2 m + 3) ∣ (t - m) →
      hilbertPrime 2 t (-(a * b)) = hilbertPrime 2 a b ∧
      hilbertPrime 2 t (-(c * d)) = hilbertPrime 2 c d := by
  obtain ⟨m, hm, hcert⟩ := binary_pair_represents_of_congr_2 ha hb hc hd hiso
  refine ⟨m, hm, fun {t} ht hcong => ?_⟩
  obtain ⟨hrab, hrcd⟩ := hcert ht hcong
  exact ⟨(represents_padic_iff_hilbertPrime_linear ha hb ht).mp hrab,
         (represents_padic_iff_hilbertPrime_linear hc hd ht).mp hrcd⟩

/-- **Good-place symbol coverage (unified `hilbertPrime` form).** At an odd prime `p` dividing none of
`a, b, c, d, t`, both families' Hilbert symbols match automatically: `(t,−ab)_p = (a,b)_p` and
`(t,−cd)_p = (c,d)_p` (both `= 1`). The `hilbertPrime`-level wrapper of `good_prime_symbol_auto` (via
`hilbertPrime_odd`). In the keystone construction, the constructed value `t = (S-part)·q` is a unit at every
odd prime outside `S ∪ {q}`, so both symbols match there with no further work — leaving only the finitely many
bad places (`hilbertPrime_pair_match_of_congr_*`), `∞`, and the single free place `q` to handle. -/
theorem hilbertPrime_pair_match_good {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a b c d t : ℤ}
    (ha : ¬ (p : ℤ) ∣ a) (hb : ¬ (p : ℤ) ∣ b) (hc : ¬ (p : ℤ) ∣ c) (hd : ¬ (p : ℤ) ∣ d)
    (ht : ¬ (p : ℤ) ∣ t) :
    hilbertPrime p t (-(a * b)) = hilbertPrime p a b ∧
    hilbertPrime p t (-(c * d)) = hilbertPrime p c d := by
  obtain ⟨h1, h2⟩ := good_prime_symbol_auto ha hb hc hd ht
  rw [hilbertPrime_odd Fact.out hp, hilbertPrime_odd Fact.out hp,
      hilbertPrime_odd Fact.out hp, hilbertPrime_odd Fact.out hp]
  exact ⟨h1, h2⟩

/-- **Closing lemma of the keystone construction: one free finite place `q`.** If a single nonzero integer `t`
matches *both* families' Hilbert symbols at `∞` and at every finite place *except* one prime `q`, then the
quaternary `a x² + b y² = c z² + d w²` is isotropic over ℚ. The two free-place closures
(`hilbertPrime_eq_of_others`, applied per family) recover the symbols at `q` from the product formula, so all
places match and `quaternary_isotropic_of_symbol_keystone` fires. **This reduces the entire `n = 4` Hasse–
Minkowski to a single constructive task: produce an integer `t` matching both families at `∞` and all finite
places ≠ q** — which the clean construction does via the bad-place certificates
(`hilbertPrime_pair_match_of_congr_*`), good-place coverage (`hilbertPrime_pair_match_good`), a sign choice at
`∞`, and a plain-Dirichlet prime `q` (no consistency obstruction — the `q`-place is the free one here). -/
theorem quaternary_isotropic_of_symbol_except_q {a b c d t : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (ht : t ≠ 0) (q : ℕ)
    (hRab : hilbertReal ((t : ℤ) : ℝ) ((-(a * b) : ℤ) : ℝ) = hilbertReal ((a : ℤ) : ℝ) ((b : ℤ) : ℝ))
    (hRcd : hilbertReal ((t : ℤ) : ℝ) ((-(c * d) : ℤ) : ℝ) = hilbertReal ((c : ℤ) : ℝ) ((d : ℤ) : ℝ))
    (hab : ∀ p : ℕ, p ≠ q → hilbertPrime p t (-(a * b)) = hilbertPrime p a b)
    (hcd : ∀ p : ℕ, p ≠ q → hilbertPrime p t (-(c * d)) = hilbertPrime p c d) :
    ∃ x y z w : ℚ, ¬(x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) ∧
      (a : ℚ) * x ^ 2 + (b : ℚ) * y ^ 2 = (c : ℚ) * z ^ 2 + (d : ℚ) * w ^ 2 := by
  have hqab : hilbertPrime q t (-(a * b)) = hilbertPrime q a b :=
    hilbertPrime_eq_of_others ha hb ht q hRab hab
  have hqcd : hilbertPrime q t (-(c * d)) = hilbertPrime q c d :=
    hilbertPrime_eq_of_others hc hd ht q hRcd hcd
  refine quaternary_isotropic_of_symbol_keystone ha hb hc hd ⟨t, ht, hRab, ?_, hRcd, ?_⟩
  · intro p _; rcases eq_or_ne p q with hpq | hpq
    · subst hpq; exact hqab
    · exact hab p hpq
  · intro p _; rcases eq_or_ne p q with hpq | hpq
    · subst hpq; exact hqcd
    · exact hcd p hpq

end SKEFTHawking
