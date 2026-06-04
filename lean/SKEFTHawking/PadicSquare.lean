/-
# p-adic squares via Hensel — foundation of local solvability ([HM-LG])

For an odd prime `p`, a `p`-adic unit whose residue mod `p` is a (nonzero) square is itself a square in
`ℤ_[p]`. This is the foundational fact of the p-adic square-class theory underlying local solvability of
quadratic forms (the form-level input of Hasse–Minkowski). Proof: Hensel's lemma applied to `X² - u` at a
lift `a` of the residue square root — `‖a²-u‖ < 1 = ‖2a‖²` (odd `p`, `a` a unit), so the approximate root
refines to an exact square root.

Mathlib has no p-adic square theory, so this is built from raw `hensels_lemma`. Kernel-pure, no axioms.
-/

import Mathlib

namespace SKEFTHawking

open Polynomial PadicInt

/-- `toZMod x = 0 ↔ ‖x‖ < 1` in `ℤ_[p]` (kernel of `toZMod` is the maximal ideal = non-units). -/
theorem toZMod_eq_zero_iff_norm_lt_one {p : ℕ} [Fact p.Prime] (x : ℤ_[p]) :
    PadicInt.toZMod x = 0 ↔ ‖x‖ < 1 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits]

/-- **p-adic squares lift from residues:** for an odd prime `p` and a `p`-adic unit `u` whose image in
`ZMod p` is a square, `u` is a square in `ℤ_[p]`. -/
theorem isSquare_of_isSquare_toZMod {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {u : ℤ_[p]}
    (hu : IsUnit u) (hsq : IsSquare (PadicInt.toZMod u)) : IsSquare u := by
  obtain ⟨r, hr⟩ := hsq
  obtain ⟨a, ha⟩ := ZMod.ringHom_surjective PadicInt.toZMod r
  have hr0 : r ≠ 0 := by
    intro h
    have hlt : ‖u‖ < 1 := (toZMod_eq_zero_iff_norm_lt_one u).mp (by rw [hr, h, mul_zero])
    rw [PadicInt.isUnit_iff.mp hu] at hlt; exact lt_irrefl 1 hlt
  have hau : ‖a ^ 2 - u‖ < 1 := by
    rw [← toZMod_eq_zero_iff_norm_lt_one]
    simp only [map_sub, map_pow, ha, hr]; ring
  have h2 : ‖(2 : ℤ_[p])‖ = 1 := by
    rw [show (2 : ℤ_[p]) = ((2 : ℕ) : ℤ_[p]) by norm_num, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes Fact.out Nat.prime_two).mpr hp
  have ha1 : ‖a‖ = 1 := by
    rcases lt_or_eq_of_le (PadicInt.norm_le_one a) with h | h
    · exact absurd (ha.symm.trans ((toZMod_eq_zero_iff_norm_lt_one a).mpr h)) hr0
    · exact h
  set F : ℤ_[p][X] := X ^ 2 - C u with hF
  have hFe : ∀ x : ℤ_[p], F.aeval x = x ^ 2 - u := fun x => by simp [hF]
  have hFda : F.derivative.aeval a = 2 * a := by
    simp only [hF, derivative_sub, derivative_X_pow, derivative_C, sub_zero, map_mul, map_pow,
      aeval_X, Nat.cast_ofNat, map_ofNat]
    norm_num
  have hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2 := by
    rw [hFe, hFda, norm_mul, h2, ha1]; simpa using hau
  obtain ⟨z, hz, _⟩ := hensels_lemma (F := F) (a := a) hnorm
  rw [hFe] at hz
  exact ⟨z, by linear_combination -hz⟩

/-- The easy direction: a square in `ℤ_[p]` has a square residue (`toZMod` is a ring hom). -/
theorem isSquare_toZMod_of_isSquare {p : ℕ} [Fact p.Prime] {u : ℤ_[p]} (h : IsSquare u) :
    IsSquare (PadicInt.toZMod u) := h.map PadicInt.toZMod

/-- **p-adic unit square criterion** (odd `p`): a `p`-adic unit is a square iff its residue mod `p` is. -/
theorem isSquare_iff_isSquare_toZMod {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {u : ℤ_[p]}
    (hu : IsUnit u) : IsSquare u ↔ IsSquare (PadicInt.toZMod u) :=
  ⟨isSquare_toZMod_of_isSquare, isSquare_of_isSquare_toZMod hp hu⟩

/-- `toZModPow n x = 0 ↔ ‖x‖ ≤ p^(-n)` — the residue/norm bridge at higher level (kernel `= span{pⁿ}`). -/
theorem toZModPow_eq_zero_iff_norm_le {p : ℕ} [Fact p.Prime] (n : ℕ) (x : ℤ_[p]) :
    PadicInt.toZModPow n x = 0 ↔ ‖x‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]
  exact (PadicInt.norm_le_pow_iff_mem_span_pow x n).symm

/-- **2-adic square criterion (forward):** a `2`-adic integer `≡ 1 (mod 8)` is a square. The dyadic
analog of `isSquare_of_isSquare_toZMod`: Hensel on `X² - u` at `a = 1` needs `‖1-u‖ < ‖2‖² = 1/4`,
and `u ≡ 1 (mod 8)` gives `‖1-u‖ ≤ 1/8`. -/
theorem isSquare_of_toZModPow_three_eq_one {u : ℤ_[2]} (h8 : PadicInt.toZModPow 3 u = 1) :
    IsSquare u := by
  have hnorm8 := (toZModPow_eq_zero_iff_norm_le 3 ((1 : ℤ_[2]) - u)).mp (by
    simp only [map_sub, map_one, h8, sub_self])
  have h2 : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := by
    rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) by norm_num]
    exact_mod_cast PadicInt.norm_p (p := 2)
  set F : ℤ_[2][X] := X ^ 2 - C u with hF
  have hFe : ∀ x : ℤ_[2], F.aeval x = x ^ 2 - u := fun x => by simp [hF]
  have hFda : F.derivative.aeval (1 : ℤ_[2]) = 2 := by
    simp only [hF, derivative_sub, derivative_X_pow, derivative_C, sub_zero, map_mul, map_pow,
      aeval_X, Nat.cast_ofNat, map_ofNat, one_pow, mul_one]
  have hnorm : ‖F.aeval (1 : ℤ_[2])‖ < ‖F.derivative.aeval (1 : ℤ_[2])‖ ^ 2 := by
    rw [hFe, hFda, h2, one_pow]
    calc ‖(1 : ℤ_[2]) - u‖ ≤ ((2 : ℕ) : ℝ) ^ (-(3 : ℤ)) := hnorm8
      _ < (2⁻¹ : ℝ) ^ 2 := by norm_num
  obtain ⟨z, hz, _⟩ := hensels_lemma (F := F) (a := (1 : ℤ_[2])) hnorm
  rw [hFe] at hz
  exact ⟨z, by linear_combination -hz⟩

end SKEFTHawking
