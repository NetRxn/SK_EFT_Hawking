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

end SKEFTHawking
