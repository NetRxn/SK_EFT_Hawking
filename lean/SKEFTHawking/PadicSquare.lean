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
import SKEFTHawking.HasseMinkowskiLocal
import SKEFTHawking.HilbertSymbolReal
import SKEFTHawking.HilbertSymbolPadic
import SKEFTHawking.HilbertSymbolTwo

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

/-- **2-adic square criterion (converse):** a `2`-adic *unit* square is `≡ 1 (mod 8)`. The only square
in `(ZMod 8)ˣ` is `1`. -/
theorem toZModPow_three_eq_one_of_isSquare {u : ℤ_[2]} (hu : IsUnit u) (h : IsSquare u) :
    PadicInt.toZModPow 3 u = 1 := by
  obtain ⟨v, rfl⟩ := h
  have hv : IsUnit v := isUnit_of_mul_isUnit_left hu
  have hw : IsUnit (PadicInt.toZModPow 3 v) := hv.map _
  rw [map_mul]
  revert hw
  generalize PadicInt.toZModPow 3 v = w
  revert w
  decide

/-- **2-adic unit square criterion:** a `2`-adic unit is a square iff it is `≡ 1 (mod 8)`. -/
theorem isSquare_iff_toZModPow_three_eq_one {u : ℤ_[2]} (hu : IsUnit u) :
    IsSquare u ↔ PadicInt.toZModPow 3 u = 1 :=
  ⟨toZModPow_three_eq_one_of_isSquare hu, isSquare_of_toZModPow_three_eq_one⟩

/-! ## Local isotropy of the unit ternary form (good-reduction case of `(a,b)_p = 1`) -/

/-- A `p`-adic unit has nonzero residue mod `p`. -/
theorem toZMod_ne_zero_of_isUnit {p : ℕ} [Fact p.Prime] {a : ℤ_[p]} (ha : IsUnit a) :
    PadicInt.toZMod a ≠ 0 := by
  rw [Ne, toZMod_eq_zero_iff_norm_lt_one, PadicInt.isUnit_iff.mp ha]; exact lt_irrefl 1

/-- **Local isotropy of the unit ternary form (odd `p`):** for an odd prime `p` and `p`-adic units
`a, b`, the form `a X² + b Y² = Z²` has a solution with `Z` a unit (hence a nontrivial isotropic
vector). This is the good-reduction case `(a,b)_p = 1`: at residue level the binary form `a X² + b Y²`
is universal over `𝔽_p` (`FiniteField.exists_root_sum_quadratic`), representing `1 = 1²`; then Hensel
(`isSquare_of_isSquare_toZMod`) lifts `a X² + b Y² ≡ 1 (mod p)` to an exact square `Z²`. -/
theorem exists_ternary_isotropic_odd {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a b : ℤ_[p]}
    (ha : IsUnit a) (hb : IsUnit b) :
    ∃ X Y Z : ℤ_[p], IsUnit Z ∧ a * X ^ 2 + b * Y ^ 2 = Z ^ 2 := by
  have haz : PadicInt.toZMod a ≠ 0 := toZMod_ne_zero_of_isUnit ha
  have hbz : PadicInt.toZMod b ≠ 0 := toZMod_ne_zero_of_isUnit hb
  have hgdeg : (C (PadicInt.toZMod b) * X ^ 2 - C 1).degree = 2 := by
    have hlt : (C (1 : ZMod p)).degree < (C (PadicInt.toZMod b) * X ^ 2).degree := by
      rw [Polynomial.degree_C_mul_X_pow 2 hbz]
      exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)
    rw [Polynomial.degree_sub_eq_left_of_degree_lt hlt, Polynomial.degree_C_mul_X_pow 2 hbz]
    rfl
  have hcard : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card]; exact Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp)
  obtain ⟨xb, yb, hxy⟩ := FiniteField.exists_root_sum_quadratic
    (f := C (PadicInt.toZMod a) * X ^ 2) (g := C (PadicInt.toZMod b) * X ^ 2 - C 1)
    (Polynomial.degree_C_mul_X_pow 2 haz) hgdeg hcard
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_sub] at hxy
  have hres : PadicInt.toZMod a * xb ^ 2 + PadicInt.toZMod b * yb ^ 2 = 1 := by
    linear_combination hxy
  obtain ⟨X, hX⟩ := ZMod.ringHom_surjective PadicInt.toZMod xb
  obtain ⟨Y, hY⟩ := ZMod.ringHom_surjective PadicInt.toZMod yb
  have hcz : PadicInt.toZMod (a * X ^ 2 + b * Y ^ 2) = 1 := by
    simp only [map_add, map_mul, map_pow, hX, hY]; exact hres
  have hcunit : IsUnit (a * X ^ 2 + b * Y ^ 2) := by
    rw [PadicInt.isUnit_iff]
    rcases lt_or_eq_of_le (PadicInt.norm_le_one (a * X ^ 2 + b * Y ^ 2)) with h | h
    · exact absurd ((toZMod_eq_zero_iff_norm_lt_one _).mpr h) (by rw [hcz]; exact one_ne_zero)
    · exact h
  obtain ⟨Z, hZ⟩ := isSquare_of_isSquare_toZMod hp hcunit (by rw [hcz]; exact ⟨1, by ring⟩)
  refine ⟨X, Y, Z, ?_, ?_⟩
  · rw [hZ] at hcunit; exact isUnit_of_mul_isUnit_left hcunit
  · rw [hZ]; ring

/-- **Symmetric diagonal ternary isotropy (odd `p`):** for an odd prime and `p`-adic units `a, b, c`,
the diagonal form `a x² + b y² + c z² = 0` has a nontrivial zero. Derived from
`exists_ternary_isotropic_odd` by scaling the `Z²` term by the unit `-c`. -/
theorem exists_diag_ternary_zero_odd {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a b c : ℤ_[p]}
    (ha : IsUnit a) (hb : IsUnit b) (hc : IsUnit c) :
    ∃ x y z : ℤ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 := by
  obtain ⟨w, hw⟩ := hc.neg
  obtain ⟨X, Y, Z, hZ, hXYZ⟩ :=
    exists_ternary_isotropic_odd hp (ha.mul (w⁻¹).isUnit) (hb.mul (w⁻¹).isUnit)
  refine ⟨X, Y, Z, fun h => hZ.ne_zero h.2.2, ?_⟩
  have hww : (w : ℤ_[p]) * ↑w⁻¹ = 1 := Units.mul_inv w
  have e1 : a * X ^ 2 + b * Y ^ 2 = (w : ℤ_[p]) * Z ^ 2 := by
    linear_combination (w : ℤ_[p]) * hXYZ - (a * X ^ 2 + b * Y ^ 2) * hww
  rw [hw] at e1
  linear_combination e1

/-- **Odd-`p` higher-rank local isotropy:** a diagonal form `∑ aᵢ xᵢ²` of rank `n ≥ 3` over `ℚ_p`
(odd `p`) with all coefficients units is isotropic. Reduces to the ternary sub-block on the first
three coordinates (`exists_diag_ternary_zero_odd`), padding the remaining coordinates with `0`. -/
theorem exists_diag_nary_zero_odd {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {n : ℕ} (hn : 3 ≤ n)
    (a : Fin n → ℤ_[p]) (ha : ∀ i, IsUnit (a i)) :
    ∃ x : Fin n → ℤ_[p], x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set i1 : Fin n := ⟨1, by omega⟩ with hi1
  set i2 : Fin n := ⟨2, by omega⟩ with hi2
  have d01 : i0 ≠ i1 := Fin.ne_of_val_ne (by simp [hi0, hi1])
  have d02 : i0 ≠ i2 := Fin.ne_of_val_ne (by simp [hi0, hi2])
  have d12 : i1 ≠ i2 := Fin.ne_of_val_ne (by simp [hi1, hi2])
  obtain ⟨x0, y0, z0, hnz, hzero⟩ :=
    exists_diag_ternary_zero_odd hp (ha i0) (ha i1) (ha i2)
  set x : Fin n → ℤ_[p] :=
    fun i => if i = i0 then x0 else if i = i1 then y0 else if i = i2 then z0 else 0 with hx
  have vx0 : x i0 = x0 := by rw [hx]; simp
  have vx1 : x i1 = y0 := by rw [hx]; simp [d01.symm]
  have vx2 : x i2 = z0 := by rw [hx]; simp [d02.symm, d12.symm]
  have vxo : ∀ i, i ≠ i0 → i ≠ i1 → i ≠ i2 → x i = 0 := by
    intro i h0 h1 h2; rw [hx]; simp [h0, h1, h2]
  refine ⟨x, ?_, ?_⟩
  · intro hxz
    refine hnz ⟨?_, ?_, ?_⟩
    · rw [← vx0, hxz]; rfl
    · rw [← vx1, hxz]; rfl
    · rw [← vx2, hxz]; rfl
  · rw [← Finset.sum_subset (Finset.subset_univ {i0, i1, i2})]
    · rw [Finset.sum_insert (by simp [d01, d02]), Finset.sum_insert (by simp [d12]),
        Finset.sum_singleton, vx0, vx1, vx2]
      linear_combination hzero
    · intro i _ hi
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      rw [vxo i hi.1 hi.2.1 hi.2.2]; ring

/-! ## p-adic valuation decomposition over the field `ℚ_[p]` (toward the rank-≥5 local workhorse) -/

/-- **p-adic valuation decomposition over `ℚ_[p]`.** Every nonzero `x : ℚ_[p]` factors as `x = p^k · u` with
`k = x.valuation` and `‖u‖ = 1` (so `u` is a unit of the value ring `ℤ_[p]`). The starting point for
normalizing a diagonal form's weights to square-class representatives `unit` / `p · unit` at a `p`-adic place. -/
theorem padic_valuation_decomp {p : ℕ} [Fact p.Prime] {x : ℚ_[p]} (hx : x ≠ 0) :
    ∃ u : ℚ_[p], ‖u‖ = 1 ∧ x = (p : ℚ_[p]) ^ x.valuation * u := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨x * (p : ℚ_[p]) ^ (-x.valuation), ?_, ?_⟩
  · rw [norm_mul, norm_zpow, Padic.norm_p, Padic.norm_eq_zpow_neg_valuation hx, inv_zpow]
    exact mul_inv_cancel₀ (zpow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero))
  · rw [mul_comm ((p : ℚ_[p]) ^ x.valuation) (x * (p : ℚ_[p]) ^ (-x.valuation)), mul_assoc,
      ← zpow_add₀ hp0, neg_add_cancel, zpow_zero, mul_one]

/-- **A norm-1 element of `ℚ_[p]` lifts to a `ℤ_[p]` unit.** If `‖u‖ = 1` then `u` is the image of a unit of
the ring of integers `ℤ_[p]`. This carries the unit-coefficient diagonal lemmas (stated over `ℤ_[p]`) to a
diagonalized form over the field `ℚ_[p]`. -/
theorem exists_padicInt_unit_of_norm_one {p : ℕ} [Fact p.Prime] {u : ℚ_[p]} (hu : ‖u‖ = 1) :
    ∃ u' : ℤ_[p], IsUnit u' ∧ (u' : ℚ_[p]) = u := by
  refine ⟨⟨u, le_of_eq hu⟩, ?_, rfl⟩
  rw [PadicInt.isUnit_iff]
  exact hu

/-- **Odd-`p` unit ternary isotropy over the field `ℚ_[p]`.** For an odd prime `p` and norm-1 coefficients
`a, b, c : ℚ_[p]`, the form `a x² + b y² + c z² = 0` has a nontrivial zero. Lift the coefficients to `ℤ_[p]`
units (`exists_padicInt_unit_of_norm_one`), solve over `ℤ_[p]` (`exists_diag_ternary_zero_odd`), cast the
solution back. This is the field-level shape produced by diagonalizing a `ℤ_p`-unimodular form. -/
theorem exists_diag_ternary_zero_odd_padic {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a b c : ℚ_[p]}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    ∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 := by
  obtain ⟨a', ha'u, ha'⟩ := exists_padicInt_unit_of_norm_one ha
  obtain ⟨b', hb'u, hb'⟩ := exists_padicInt_unit_of_norm_one hb
  obtain ⟨c', hc'u, hc'⟩ := exists_padicInt_unit_of_norm_one hc
  obtain ⟨x', y', z', hnz, hzero⟩ := exists_diag_ternary_zero_odd hp ha'u hb'u hc'u
  refine ⟨(x' : ℚ_[p]), (y' : ℚ_[p]), (z' : ℚ_[p]), ?_, ?_⟩
  · rintro ⟨hx0, hy0, hz0⟩
    exact hnz ⟨PadicInt.coe_eq_zero.mp hx0, PadicInt.coe_eq_zero.mp hy0, PadicInt.coe_eq_zero.mp hz0⟩
  · have h := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hzero
    push_cast at h
    rw [ha', hb', hc'] at h
    exact h

/-- **Same-valuation-parity ternary isotropy over `ℚ_[p]` (odd `p`).** Three nonzero coefficients whose
`p`-adic valuations share a parity give an isotropic ternary form. Normalize each `wᵢ = p^vᵢ·uᵢ` by the
square substitution `xᵢ ↦ p^(−vᵢ/2)·yᵢ`, sending its valuation to `vᵢ % 2 = ε` (common by parity); factor the
constant `p^ε`; the residual unit ternary is isotropic (`exists_diag_ternary_zero_odd_padic`). -/
theorem exists_ternary_zero_same_parity_padic {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a b c : ℚ_[p]}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : a.valuation % 2 = b.valuation % 2)
    (hbc : b.valuation % 2 = c.valuation % 2) :
    ∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨ua, hua, hae⟩ := padic_valuation_decomp ha
  obtain ⟨ub, hub, hbe⟩ := padic_valuation_decomp hb
  obtain ⟨uc, huc, hce⟩ := padic_valuation_decomp hc
  obtain ⟨y0, y1, y2, hnz, hzero⟩ := exists_diag_ternary_zero_odd_padic hp hua hub huc
  have key : ∀ (v : ℤ) (u yv : ℚ_[p]),
      ((p : ℚ_[p]) ^ v * u) * ((p : ℚ_[p]) ^ (-(v / 2)) * yv) ^ 2
        = (p : ℚ_[p]) ^ (v % 2) * (u * yv ^ 2) := by
    intro v u yv
    have hvd : v + (-(v / 2) + -(v / 2)) = v % 2 := by omega
    have h2 : ((p : ℚ_[p]) ^ (-(v / 2)) * yv) ^ 2
        = (p : ℚ_[p]) ^ (-(v / 2) + -(v / 2)) * yv ^ 2 := by
      rw [mul_pow, pow_two, ← zpow_add₀ hp0]
    have hL : (p : ℚ_[p]) ^ (v + (-(v / 2) + -(v / 2))) * (u * yv ^ 2)
        = (p : ℚ_[p]) ^ v * u * ((p : ℚ_[p]) ^ (-(v / 2) + -(v / 2)) * yv ^ 2) := by
      rw [zpow_add₀ hp0]; ring
    rw [h2, ← hL, hvd]
  set va := a.valuation with hva
  set vb := b.valuation with hvb
  set vc := c.valuation with hvc
  refine ⟨(p : ℚ_[p]) ^ (-(va / 2)) * y0, (p : ℚ_[p]) ^ (-(vb / 2)) * y1,
          (p : ℚ_[p]) ^ (-(vc / 2)) * y2, ?_, ?_⟩
  · rintro ⟨hx0, hy0, hz0⟩
    refine hnz ⟨?_, ?_, ?_⟩
    · rcases mul_eq_zero.mp hx0 with h | h
      · exact absurd h (zpow_ne_zero _ hp0)
      · exact h
    · rcases mul_eq_zero.mp hy0 with h | h
      · exact absurd h (zpow_ne_zero _ hp0)
      · exact h
    · rcases mul_eq_zero.mp hz0 with h | h
      · exact absurd h (zpow_ne_zero _ hp0)
      · exact h
  · rw [hae, hbe, hce, key va ua y0, key vb ub y1, key vc uc y2, ← hab, ← hab.trans hbc,
      ← mul_add, ← mul_add, hzero, mul_zero]

/-- **Parity pigeonhole.** Among `n ≥ 5` indices each assigned a parity in `ZMod 2`, three distinct ones
share the same parity (`2·2 = 4 < 5 ≤ n`). Used to find a same-valuation-parity ternary sub-block in a
rank-≥5 diagonal form over `ℚ_[p]`. -/
theorem exists_three_same_parity {n : ℕ} (hn : 5 ≤ n) (g : Fin n → ZMod 2) :
    ∃ i j k : Fin n, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ g i = g j ∧ g j = g k := by
  have hcard : Fintype.card (ZMod 2) * 2 < Fintype.card (Fin n) := by
    simp only [ZMod.card, Fintype.card_fin]; omega
  obtain ⟨y, hy⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card g hcard
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc
  exact ⟨a, b, c, hab, hac, hbc, ha.trans hb.symm, hb.trans hc.symm⟩

/-- **Rank-≥5 odd-`p` local workhorse over `ℚ_[p]`.** Any diagonal form `∑ wᵢ xᵢ²` of rank `n ≥ 5` over
`ℚ_[p]` (odd `p`) with all coefficients nonzero is isotropic. By the parity pigeonhole, three coordinates
share a valuation parity; their ternary sub-block is isotropic
(`exists_ternary_zero_same_parity_padic`); pad the rest with `0`. This discharges every odd-`p` local
condition for forms of rank ≥ 5 (in particular every `ℤ_p`-unimodular form, regardless of coefficient
valuations). -/
theorem exists_diag_nary_zero_odd_padic {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {n : ℕ} (hn : 5 ≤ n)
    (w : Fin n → ℚ_[p]) (hw : ∀ i, w i ≠ 0) :
    ∃ x : Fin n → ℚ_[p], x ≠ 0 ∧ ∑ i, w i * x i ^ 2 = 0 := by
  obtain ⟨i0, i1, i2, d01, d02, d12, hg01, hg12⟩ :=
    exists_three_same_parity hn (fun i => ((w i).valuation : ZMod 2))
  have hpar01 : (w i0).valuation % 2 = (w i1).valuation % 2 :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mp hg01
  have hpar12 : (w i1).valuation % 2 = (w i2).valuation % 2 :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mp hg12
  obtain ⟨x0, x1, x2, hnz, hzero⟩ :=
    exists_ternary_zero_same_parity_padic hp (hw i0) (hw i1) (hw i2) hpar01 hpar12
  set x : Fin n → ℚ_[p] :=
    fun i => if i = i0 then x0 else if i = i1 then x1 else if i = i2 then x2 else 0 with hx
  have vx0 : x i0 = x0 := by rw [hx]; simp
  have vx1 : x i1 = x1 := by rw [hx]; simp [d01.symm]
  have vx2 : x i2 = x2 := by rw [hx]; simp [d02.symm, d12.symm]
  have vxo : ∀ i, i ≠ i0 → i ≠ i1 → i ≠ i2 → x i = 0 := by
    intro i h0 h1 h2; rw [hx]; simp [h0, h1, h2]
  refine ⟨x, ?_, ?_⟩
  · intro hxz
    refine hnz ⟨?_, ?_, ?_⟩
    · rw [← vx0, hxz]; rfl
    · rw [← vx1, hxz]; rfl
    · rw [← vx2, hxz]; rfl
  · rw [← Finset.sum_subset (Finset.subset_univ {i0, i1, i2})]
    · rw [Finset.sum_insert (by simp [d01, d02]), Finset.sum_insert (by simp [d12]),
        Finset.sum_singleton, vx0, vx1, vx2]
      linear_combination hzero
    · intro i _ hi
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      rw [vxo i hi.1 hi.2.1 hi.2.2]; ring

/-! ## The Hilbert canonical form `z² = a x² + b y²` (toward the symbol ⟺ solvability bridge) -/

/-- **Canonical Hilbert ternary, odd-`p` unit case.** For an odd prime and `p`-adic units `a, b`, the
equation `z² = a x² + b y²` (the form whose solvability `(a,b)_p = 1` encodes) has a nontrivial solution.
This is the `(a,b)_p = 1` content for units, the base of the symbol ⟺ solvability bridge. -/
theorem solvable_canonical_ternary_odd_units {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a b : ℚ_[p]}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2 := by
  obtain ⟨x, y, z, hnz, h⟩ :=
    exists_diag_ternary_zero_odd_padic hp ha hb (by rw [norm_neg, norm_one] : ‖(-1 : ℚ_[p])‖ = 1)
  exact ⟨x, y, z, hnz, by linear_combination -h⟩

/-- **Solvability of `z² = a x² + b y²` depends only on the square classes of `a, b`.** Scaling a
coefficient by a nonzero square `s²` preserves solvability (substitute `x ↦ x / s`). This mirrors the
square-class dependence of the Hilbert symbol `(a,b)_p = (a s², b)_p` and feeds the general (non-unit)
reduction of the symbol ⟺ solvability bridge. -/
theorem solvable_canonical_congr_sq_left {p : ℕ} [Fact p.Prime] {a b s : ℚ_[p]} (hs : s ≠ 0) :
    (∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2) ↔
    (∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ z ^ 2 = (a * s ^ 2) * x ^ 2 + b * y ^ 2) := by
  constructor
  · rintro ⟨x, y, z, hnz, h⟩
    refine ⟨x / s, y, z, ?_, ?_⟩
    · rintro ⟨hx0, hy0, hz0⟩
      exact hnz ⟨by rw [div_eq_zero_iff] at hx0; exact hx0.resolve_right hs, hy0, hz0⟩
    · rw [h]; field_simp
  · rintro ⟨x, y, z, hnz, h⟩
    refine ⟨s * x, y, z, ?_, ?_⟩
    · rintro ⟨hx0, hy0, hz0⟩
      exact hnz ⟨(mul_eq_zero.mp hx0).resolve_left hs, hy0, hz0⟩
    · rw [h]; ring

/-- **Square-class normal form of a `ℚ_[p]` coefficient.** Every nonzero `a : ℚ_[p]` is, up to a nonzero
square factor, either a unit or `p` × a unit (according to the parity of its valuation): `a = u·s²` or
`a = (p·u)·s²` with `‖u‖ = 1`, `s ≠ 0`. With `solvable_canonical_congr_sq_left` this reduces the Hilbert
ternary `z² = a x² + b y²` to the four canonical cases (`unit`/`p·unit` in each coefficient). -/
theorem exists_unit_or_pUnit_sq {p : ℕ} [Fact p.Prime] {a : ℚ_[p]} (ha : a ≠ 0) :
    ∃ u s : ℚ_[p], ‖u‖ = 1 ∧ s ≠ 0 ∧ (a = u * s ^ 2 ∨ a = (p : ℚ_[p]) * u * s ^ 2) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨ua, hua, hae⟩ := padic_valuation_decomp ha
  set va := a.valuation with hva
  rcases Int.even_or_odd va with ⟨k, hk⟩ | ⟨k, hk⟩
  · refine ⟨ua, (p : ℚ_[p]) ^ k, hua, zpow_ne_zero _ hp0, Or.inl ?_⟩
    rw [hae, hk, zpow_add₀ hp0]; ring
  · refine ⟨ua, (p : ℚ_[p]) ^ k, hua, zpow_ne_zero _ hp0, Or.inr ?_⟩
    rw [hae, hk, show (2 * k + 1 : ℤ) = k + k + 1 from by ring, zpow_add₀ hp0, zpow_add₀ hp0,
      zpow_one]; ring

/-! ## Anisotropy of the mixed ternary `z² = u x² + p v y²` (the descent converse) -/

/-- A `p`-adic integer with zero residue is a non-unit. -/
theorem not_isUnit_of_toZMod_eq_zero {p : ℕ} [Fact p.Prime] {x : ℤ_[p]}
    (hx : PadicInt.toZMod x = 0) : ¬ IsUnit x := by
  rw [PadicInt.isUnit_iff]
  exact ne_of_lt ((toZMod_eq_zero_iff_norm_lt_one x).mp hx)

/-- **Anisotropy of `z² = u x² + p v y²` for a non-square unit `u` (odd `p`).** There is no *primitive*
`ℤ_[p]` solution: reducing mod `p` gives `z̄² = ū x̄²`, so either `x̄ ≠ 0` makes `ū = (z̄/x̄)²` a square
(contradiction), or `x̄ = 0` forces `z̄ = 0`, and a mod-`p²` descent (`p ∣ x, z ⟹ v y² = p(z₁²-u x₁²) ⟹
ȳ = 0`) makes all coordinates non-units, contradicting primitivity. The converse direction of the symbol
⟺ solvability bridge in the `(u, p·v)` case. -/
theorem no_primitive_sol_unit_pUnit {p : ℕ} [Fact p.Prime] {u v : ℤ_[p]} (hv : IsUnit v)
    (hunsq : ¬ IsSquare (PadicInt.toZMod u)) :
    ¬ ∃ x y z : ℤ_[p], (IsUnit x ∨ IsUnit y ∨ IsUnit z) ∧
      z ^ 2 = u * x ^ 2 + (p : ℤ_[p]) * v * y ^ 2 := by
  rintro ⟨x, y, z, hprim, h⟩
  have hp_zero : PadicInt.toZMod (p : ℤ_[p]) = 0 := by rw [map_natCast, ZMod.natCast_self]
  have hpne : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hred : PadicInt.toZMod z ^ 2 = PadicInt.toZMod u * PadicInt.toZMod x ^ 2 := by
    have hh := congrArg PadicInt.toZMod h
    simpa only [map_pow, map_add, map_mul, hp_zero, zero_mul, add_zero] using hh
  by_cases hx : PadicInt.toZMod x = 0
  · have hz : PadicInt.toZMod z = 0 := by
      have hz2 : PadicInt.toZMod z ^ 2 = 0 := by rw [hred, hx]; ring
      exact pow_eq_zero_iff (by norm_num) |>.mp hz2
    obtain ⟨x1, hx1⟩ := (PadicInt.norm_lt_one_iff_dvd x).mp ((toZMod_eq_zero_iff_norm_lt_one x).mp hx)
    obtain ⟨z1, hz1⟩ := (PadicInt.norm_lt_one_iff_dvd z).mp ((toZMod_eq_zero_iff_norm_lt_one z).mp hz)
    have hvy : v * y ^ 2 = (p : ℤ_[p]) * (z1 ^ 2 - u * x1 ^ 2) := by
      apply mul_left_cancel₀ hpne
      rw [hx1, hz1] at h
      linear_combination -h
    have hyz : PadicInt.toZMod y = 0 := by
      have h2 : PadicInt.toZMod v * PadicInt.toZMod y ^ 2 = 0 := by
        have := congrArg PadicInt.toZMod hvy
        simpa only [map_mul, map_pow, hp_zero, zero_mul] using this
      rcases mul_eq_zero.mp h2 with hh | hh
      · exact absurd hh (hv.map _).ne_zero
      · exact pow_eq_zero_iff (by norm_num) |>.mp hh
    exact hprim.elim (not_isUnit_of_toZMod_eq_zero hx)
      (fun hh => hh.elim (not_isUnit_of_toZMod_eq_zero hyz) (not_isUnit_of_toZMod_eq_zero hz))
  · apply hunsq
    refine ⟨PadicInt.toZMod z / PadicInt.toZMod x, ?_⟩
    field_simp
    linear_combination -hred

/-- **Descent step for the mixed ternary.** If every coordinate of a `ℤ_[p]` solution of `Z² = u X² + p v Y²`
is divisible by `p`, dividing through by `p` yields a solution of the *same* form: `(Z/p)² = u(X/p)² +
p v (Y/p)²`. Iterating this (until some coordinate is a unit) extracts a primitive solution from any `ℤ_[p]`
solution — the bridge from `ℚ_[p]` solvability (after clearing denominators) to `no_primitive_sol_unit_pUnit`. -/
theorem ternary_descent_step {p : ℕ} [Fact p.Prime] {u v X Y Z : ℤ_[p]}
    (hX : (p : ℤ_[p]) ∣ X) (hY : (p : ℤ_[p]) ∣ Y) (hZ : (p : ℤ_[p]) ∣ Z)
    (h : Z ^ 2 = u * X ^ 2 + (p : ℤ_[p]) * v * Y ^ 2) :
    ∃ X' Y' Z' : ℤ_[p], X = (p : ℤ_[p]) * X' ∧ Y = (p : ℤ_[p]) * Y' ∧ Z = (p : ℤ_[p]) * Z' ∧
      Z' ^ 2 = u * X' ^ 2 + (p : ℤ_[p]) * v * Y' ^ 2 := by
  obtain ⟨X', rfl⟩ := hX
  obtain ⟨Y', rfl⟩ := hY
  obtain ⟨Z', rfl⟩ := hZ
  refine ⟨X', Y', Z', rfl, rfl, rfl, ?_⟩
  have hp2 : (p : ℤ_[p]) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  apply mul_left_cancel₀ hp2
  linear_combination h

/-- **Clearing denominators for the mixed ternary.** A `ℚ_[p]` solution of `z² = u x² + p v y²`
(coefficients in `ℤ_[p]`) scales to a `ℤ_[p]` solution: multiply through by `p^N` for `N` large enough that
each coordinate has norm `≤ 1` (so lands in `ℤ_[p]`); the equation is homogeneous of degree 2. -/
theorem exists_padicInt_ternary_of_padic {p : ℕ} [Fact p.Prime] {u v : ℤ_[p]}
    (hsol : ∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = (u : ℚ_[p]) * x ^ 2 + (p : ℚ_[p]) * v * y ^ 2) :
    ∃ X Y Z : ℤ_[p], ¬(X = 0 ∧ Y = 0 ∧ Z = 0) ∧
      Z ^ 2 = u * X ^ 2 + (p : ℤ_[p]) * v * Y ^ 2 := by
  obtain ⟨x, y, z, hnz, h⟩ := hsol
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hppos : (0 : ℝ) < (p : ℝ) := lt_trans zero_lt_one hp1
  have hpne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨Nx, hNx⟩ := pow_unbounded_of_one_lt ‖x‖ hp1
  obtain ⟨Ny, hNy⟩ := pow_unbounded_of_one_lt ‖y‖ hp1
  obtain ⟨Nz, hNz⟩ := pow_unbounded_of_one_lt ‖z‖ hp1
  set N := max Nx (max Ny Nz) with hNdef
  have hmono : ∀ M, M ≤ N → ∀ w : ℚ_[p], ‖w‖ < (p : ℝ) ^ M → ‖(p : ℚ_[p]) ^ N * w‖ ≤ 1 := by
    intro M hM w hw
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ (pow_pos hppos N), mul_one]
    exact le_trans hw.le (pow_le_pow_right₀ hp1.le hM)
  have hx' := hmono Nx (le_max_left _ _) x hNx
  have hy' := hmono Ny (le_trans (le_max_left _ _) (le_max_right _ _)) y hNy
  have hz' := hmono Nz (le_trans (le_max_right _ _) (le_max_right _ _)) z hNz
  refine ⟨⟨(p : ℚ_[p]) ^ N * x, hx'⟩, ⟨(p : ℚ_[p]) ^ N * y, hy'⟩, ⟨(p : ℚ_[p]) ^ N * z, hz'⟩, ?_, ?_⟩
  · rintro ⟨hX0, hY0, hZ0⟩
    apply hnz
    have hpN : (p : ℚ_[p]) ^ N ≠ 0 := pow_ne_zero N hpne
    refine ⟨?_, ?_, ?_⟩
    · have h1 : (p : ℚ_[p]) ^ N * x = 0 := by
        have := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hX0; simpa using this
      exact (mul_eq_zero.mp h1).resolve_left hpN
    · have h1 : (p : ℚ_[p]) ^ N * y = 0 := by
        have := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hY0; simpa using this
      exact (mul_eq_zero.mp h1).resolve_left hpN
    · have h1 : (p : ℚ_[p]) ^ N * z = 0 := by
        have := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hZ0; simpa using this
      exact (mul_eq_zero.mp h1).resolve_left hpN
  · rw [← sub_eq_zero]
    apply PadicInt.coe_eq_zero.mp
    push_cast
    linear_combination ((p : ℚ_[p]) ^ N) ^ 2 * h

/-- **No `ℤ_[p]` solution of `z² = u x² + p v y²` for non-square unit `u`.** Descent iteration: any nonzero
`ℤ_[p]` solution reduces (by `ternary_descent_step`, while all coordinates are non-units) to a *primitive*
one, contradicting `no_primitive_sol_unit_pUnit`. Strong induction on a nonzero coordinate's valuation. -/
theorem no_padicInt_sol_unit_pUnit {p : ℕ} [Fact p.Prime] {u v : ℤ_[p]} (hv : IsUnit v)
    (hunsq : ¬ IsSquare (PadicInt.toZMod u)) :
    ¬ ∃ X Y Z : ℤ_[p], ¬(X = 0 ∧ Y = 0 ∧ Z = 0) ∧ Z ^ 2 = u * X ^ 2 + (p : ℤ_[p]) * v * Y ^ 2 := by
  have hdvd : ∀ w : ℤ_[p], ¬ IsUnit w → (p : ℤ_[p]) ∣ w := by
    intro w hw
    rw [← PadicInt.norm_lt_one_iff_dvd]
    rcases lt_or_eq_of_le (PadicInt.norm_le_one w) with hlt | heq
    · exact hlt
    · exact absurd (PadicInt.isUnit_iff.mpr heq) hw
  have hunit : ∀ w : ℤ_[p], w ≠ 0 → w.valuation = 0 → IsUnit w := by
    intro w hw0 hwv
    rw [PadicInt.isUnit_iff, PadicInt.norm_eq_zpow_neg_valuation hw0, hwv]; simp
  have main : ∀ n : ℕ, ∀ X Y Z : ℤ_[p],
      ((X ≠ 0 ∧ X.valuation ≤ n) ∨ (Y ≠ 0 ∧ Y.valuation ≤ n) ∨ (Z ≠ 0 ∧ Z.valuation ≤ n)) →
      Z ^ 2 = u * X ^ 2 + (p : ℤ_[p]) * v * Y ^ 2 → False := by
    intro n
    induction n with
    | zero =>
      intro X Y Z hwit heq
      refine no_primitive_sol_unit_pUnit hv hunsq ⟨X, Y, Z, ?_, heq⟩
      rcases hwit with ⟨h0, hv0⟩ | ⟨h0, hv0⟩ | ⟨h0, hv0⟩
      · exact Or.inl (hunit X h0 (Nat.le_zero.mp hv0))
      · exact Or.inr (Or.inl (hunit Y h0 (Nat.le_zero.mp hv0)))
      · exact Or.inr (Or.inr (hunit Z h0 (Nat.le_zero.mp hv0)))
    | succ k ih =>
      intro X Y Z hwit heq
      by_cases hprim : IsUnit X ∨ IsUnit Y ∨ IsUnit Z
      · exact no_primitive_sol_unit_pUnit hv hunsq ⟨X, Y, Z, hprim, heq⟩
      · simp only [not_or] at hprim
        obtain ⟨X', hX'eq⟩ := hdvd X hprim.1
        obtain ⟨Y', hY'eq⟩ := hdvd Y hprim.2.1
        obtain ⟨Z', hZ'eq⟩ := hdvd Z hprim.2.2
        obtain ⟨X'', Y'', Z'', hXX, hYY, hZZ, heq'⟩ :=
          ternary_descent_step ⟨X', hX'eq⟩ ⟨Y', hY'eq⟩ ⟨Z', hZ'eq⟩ heq
        refine ih X'' Y'' Z'' ?_ heq'
        have hvshift : ∀ w w' : ℤ_[p], w = (p : ℤ_[p]) * w' → w ≠ 0 →
            w' ≠ 0 ∧ w'.valuation = w.valuation - 1 := by
          intro w w' hww hw0
          have hw'0 : w' ≠ 0 := fun h => hw0 (by rw [hww, h, mul_zero])
          refine ⟨hw'0, ?_⟩
          have : w.valuation = 1 + w'.valuation := by
            rw [hww, show (p : ℤ_[p]) * w' = (p : ℤ_[p]) ^ 1 * w' from by ring,
              PadicInt.valuation_p_pow_mul 1 w' hw'0]
          omega
        rcases hwit with ⟨h0, hvle⟩ | ⟨h0, hvle⟩ | ⟨h0, hvle⟩
        · obtain ⟨h0', hv'⟩ := hvshift X X'' hXX h0
          exact Or.inl ⟨h0', by omega⟩
        · obtain ⟨h0', hv'⟩ := hvshift Y Y'' hYY h0
          exact Or.inr (Or.inl ⟨h0', by omega⟩)
        · obtain ⟨h0', hv'⟩ := hvshift Z Z'' hZZ h0
          exact Or.inr (Or.inr ⟨h0', by omega⟩)
  rintro ⟨X, Y, Z, hnz, heq⟩
  by_cases hX : X = 0
  · by_cases hY : Y = 0
    · exact main Z.valuation X Y Z (Or.inr (Or.inr ⟨fun h => hnz ⟨hX, hY, h⟩, le_refl _⟩)) heq
    · exact main Y.valuation X Y Z (Or.inr (Or.inl ⟨hY, le_refl _⟩)) heq
  · exact main X.valuation X Y Z (Or.inl ⟨hX, le_refl _⟩) heq

/-- **Anisotropy of `z² = u x² + p v y²` over the field `ℚ_[p]` (non-square unit `u`, odd implicit via `v`
unit).** The full converse direction of the symbol ⟺ solvability bridge in the `(u, p·v)` case: clearing
denominators (`exists_padicInt_ternary_of_padic`) reduces any `ℚ_[p]` solution to a `ℤ_[p]` one, excluded by
the descent (`no_padicInt_sol_unit_pUnit`). -/
theorem no_padic_sol_unit_pUnit {p : ℕ} [Fact p.Prime] {u v : ℤ_[p]} (hv : IsUnit v)
    (hunsq : ¬ IsSquare (PadicInt.toZMod u)) :
    ¬ ∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = (u : ℚ_[p]) * x ^ 2 + (p : ℚ_[p]) * v * y ^ 2 :=
  fun hsol => no_padicInt_sol_unit_pUnit hv hunsq (exists_padicInt_ternary_of_padic hsol)

/-! ## Generic primitive-solution extraction for the symmetric diagonal ternary `a x² + b y² + c z² = 0`

Reusable across all coefficient cases (odd `p` mixed/non-unit, `p = 2`): a `ℚ_[p]` solution scales to a
*primitive* `ℤ_[p]` solution, after which a case-specific mod-`p` argument supplies the contradiction. -/

/-- Generic descent step: if all coordinates of a `ℤ_[p]` solution of `a x² + b y² + c z² = 0` are divisible
by `p`, dividing through by `p` yields a solution of the same form. -/
theorem diag_ternary_descent_step {p : ℕ} [Fact p.Prime] {a b c X Y Z : ℤ_[p]}
    (hX : (p : ℤ_[p]) ∣ X) (hY : (p : ℤ_[p]) ∣ Y) (hZ : (p : ℤ_[p]) ∣ Z)
    (h : a * X ^ 2 + b * Y ^ 2 + c * Z ^ 2 = 0) :
    ∃ X' Y' Z' : ℤ_[p], X = (p : ℤ_[p]) * X' ∧ Y = (p : ℤ_[p]) * Y' ∧ Z = (p : ℤ_[p]) * Z' ∧
      a * X' ^ 2 + b * Y' ^ 2 + c * Z' ^ 2 = 0 := by
  obtain ⟨X', rfl⟩ := hX
  obtain ⟨Y', rfl⟩ := hY
  obtain ⟨Z', rfl⟩ := hZ
  refine ⟨X', Y', Z', rfl, rfl, rfl, ?_⟩
  have hp2 : (p : ℤ_[p]) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  apply mul_left_cancel₀ hp2
  linear_combination h

/-- Generic denominator clearing: a `ℚ_[p]` solution of `a x² + b y² + c z² = 0` (coefficients in `ℤ_[p]`)
scales to a `ℤ_[p]` solution (multiply by `p^N`; degree-2 homogeneous). -/
theorem exists_padicInt_diag_ternary_of_padic {p : ℕ} [Fact p.Prime] {a b c : ℤ_[p]}
    (hsol : ∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2 + (c : ℚ_[p]) * z ^ 2 = 0) :
    ∃ X Y Z : ℤ_[p], ¬(X = 0 ∧ Y = 0 ∧ Z = 0) ∧ a * X ^ 2 + b * Y ^ 2 + c * Z ^ 2 = 0 := by
  obtain ⟨x, y, z, hnz, h⟩ := hsol
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hppos : (0 : ℝ) < (p : ℝ) := lt_trans zero_lt_one hp1
  have hpne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨Nx, hNx⟩ := pow_unbounded_of_one_lt ‖x‖ hp1
  obtain ⟨Ny, hNy⟩ := pow_unbounded_of_one_lt ‖y‖ hp1
  obtain ⟨Nz, hNz⟩ := pow_unbounded_of_one_lt ‖z‖ hp1
  set N := max Nx (max Ny Nz) with hNdef
  have hmono : ∀ M, M ≤ N → ∀ w : ℚ_[p], ‖w‖ < (p : ℝ) ^ M → ‖(p : ℚ_[p]) ^ N * w‖ ≤ 1 := by
    intro M hM w hw
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ (pow_pos hppos N), mul_one]
    exact le_trans hw.le (pow_le_pow_right₀ hp1.le hM)
  have hx' := hmono Nx (le_max_left _ _) x hNx
  have hy' := hmono Ny (le_trans (le_max_left _ _) (le_max_right _ _)) y hNy
  have hz' := hmono Nz (le_trans (le_max_right _ _) (le_max_right _ _)) z hNz
  have hpN : (p : ℚ_[p]) ^ N ≠ 0 := pow_ne_zero N hpne
  refine ⟨⟨(p : ℚ_[p]) ^ N * x, hx'⟩, ⟨(p : ℚ_[p]) ^ N * y, hy'⟩, ⟨(p : ℚ_[p]) ^ N * z, hz'⟩, ?_, ?_⟩
  · rintro ⟨hX0, hY0, hZ0⟩
    apply hnz
    refine ⟨?_, ?_, ?_⟩
    · have h1 : (p : ℚ_[p]) ^ N * x = 0 := by
        have := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hX0; simpa using this
      exact (mul_eq_zero.mp h1).resolve_left hpN
    · have h1 : (p : ℚ_[p]) ^ N * y = 0 := by
        have := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hY0; simpa using this
      exact (mul_eq_zero.mp h1).resolve_left hpN
    · have h1 : (p : ℚ_[p]) ^ N * z = 0 := by
        have := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hZ0; simpa using this
      exact (mul_eq_zero.mp h1).resolve_left hpN
  · rw [← sub_eq_zero]
    apply PadicInt.coe_eq_zero.mp
    push_cast
    linear_combination ((p : ℚ_[p]) ^ N) ^ 2 * h

/-- **Generic primitive-solution extraction.** A `ℚ_[p]` solution of `a x² + b y² + c z² = 0` yields a
*primitive* `ℤ_[p]` solution (some coordinate a unit). Clearing denominators then iterating the descent step
(while all coordinates are non-units), by strong induction on a witness coordinate's `PadicInt.valuation`. The
reusable bridge: each coefficient case then needs only a mod-`p` argument on the primitive solution. -/
theorem exists_primitive_diag_ternary {p : ℕ} [Fact p.Prime] {a b c : ℤ_[p]}
    (hsol : ∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2 + (c : ℚ_[p]) * z ^ 2 = 0) :
    ∃ X Y Z : ℤ_[p], (IsUnit X ∨ IsUnit Y ∨ IsUnit Z) ∧ a * X ^ 2 + b * Y ^ 2 + c * Z ^ 2 = 0 := by
  obtain ⟨X₀, Y₀, Z₀, hnz, heq₀⟩ := exists_padicInt_diag_ternary_of_padic hsol
  have hdvd : ∀ w : ℤ_[p], ¬ IsUnit w → (p : ℤ_[p]) ∣ w := by
    intro w hw
    rw [← PadicInt.norm_lt_one_iff_dvd]
    rcases lt_or_eq_of_le (PadicInt.norm_le_one w) with hlt | heq
    · exact hlt
    · exact absurd (PadicInt.isUnit_iff.mpr heq) hw
  have hunit : ∀ w : ℤ_[p], w ≠ 0 → w.valuation = 0 → IsUnit w := by
    intro w hw0 hwv
    rw [PadicInt.isUnit_iff, PadicInt.norm_eq_zpow_neg_valuation hw0, hwv]; simp
  have main : ∀ n : ℕ, ∀ X Y Z : ℤ_[p],
      ((X ≠ 0 ∧ X.valuation ≤ n) ∨ (Y ≠ 0 ∧ Y.valuation ≤ n) ∨ (Z ≠ 0 ∧ Z.valuation ≤ n)) →
      a * X ^ 2 + b * Y ^ 2 + c * Z ^ 2 = 0 →
      ∃ X' Y' Z' : ℤ_[p], (IsUnit X' ∨ IsUnit Y' ∨ IsUnit Z') ∧
        a * X' ^ 2 + b * Y' ^ 2 + c * Z' ^ 2 = 0 := by
    intro n
    induction n with
    | zero =>
      intro X Y Z hwit heq
      refine ⟨X, Y, Z, ?_, heq⟩
      rcases hwit with ⟨h0, hv0⟩ | ⟨h0, hv0⟩ | ⟨h0, hv0⟩
      · exact Or.inl (hunit X h0 (Nat.le_zero.mp hv0))
      · exact Or.inr (Or.inl (hunit Y h0 (Nat.le_zero.mp hv0)))
      · exact Or.inr (Or.inr (hunit Z h0 (Nat.le_zero.mp hv0)))
    | succ k ih =>
      intro X Y Z hwit heq
      by_cases hprim : IsUnit X ∨ IsUnit Y ∨ IsUnit Z
      · exact ⟨X, Y, Z, hprim, heq⟩
      · simp only [not_or] at hprim
        obtain ⟨X'', Y'', Z'', hXX, hYY, hZZ, heq'⟩ :=
          diag_ternary_descent_step (hdvd X hprim.1) (hdvd Y hprim.2.1) (hdvd Z hprim.2.2) heq
        refine ih X'' Y'' Z'' ?_ heq'
        have hvshift : ∀ w w' : ℤ_[p], w = (p : ℤ_[p]) * w' → w ≠ 0 →
            w' ≠ 0 ∧ w'.valuation = w.valuation - 1 := by
          intro w w' hww hw0
          have hw'0 : w' ≠ 0 := fun h => hw0 (by rw [hww, h, mul_zero])
          refine ⟨hw'0, ?_⟩
          have : w.valuation = 1 + w'.valuation := by
            rw [hww, show (p : ℤ_[p]) * w' = (p : ℤ_[p]) ^ 1 * w' from by ring,
              PadicInt.valuation_p_pow_mul 1 w' hw'0]
          omega
        rcases hwit with ⟨h0, hvle⟩ | ⟨h0, hvle⟩ | ⟨h0, hvle⟩
        · obtain ⟨h0', hv'⟩ := hvshift X X'' hXX h0
          exact Or.inl ⟨h0', by omega⟩
        · obtain ⟨h0', hv'⟩ := hvshift Y Y'' hYY h0
          exact Or.inr (Or.inl ⟨h0', by omega⟩)
        · obtain ⟨h0', hv'⟩ := hvshift Z Z'' hZZ h0
          exact Or.inr (Or.inr ⟨h0', by omega⟩)
  by_cases hX : X₀ = 0
  · by_cases hY : Y₀ = 0
    · exact main Z₀.valuation X₀ Y₀ Z₀ (Or.inr (Or.inr ⟨fun h => hnz ⟨hX, hY, h⟩, le_refl _⟩)) heq₀
    · exact main Y₀.valuation X₀ Y₀ Z₀ (Or.inr (Or.inl ⟨hY, le_refl _⟩)) heq₀
  · exact main X₀.valuation X₀ Y₀ Z₀ (Or.inl ⟨hX, le_refl _⟩) heq₀

/-- **Anisotropy of `pu·X² + pv·Y² − Z² = 0` for `-uv` a non-square (primitive case).** Mod `p` forces
`Z̄ = 0`; one descent (`Z = p Z'`, cancel `p`) gives `u X² + v Y² = p Z'²`, whose mod-`p` reduction
`ū X̄² + v̄ Ȳ² = 0` makes `-ū v̄ = (v̄ Ȳ / X̄)²` a square unless `X̄ = 0` — then `Ȳ = 0` too, so all
coordinates are non-units, contradicting primitivity. -/
theorem no_primitive_sol_pUnit_pUnit {p : ℕ} [Fact p.Prime] {u v : ℤ_[p]} (hv : IsUnit v)
    (hunsq : ¬ IsSquare (PadicInt.toZMod (-(u * v)))) :
    ¬ ∃ X Y Z : ℤ_[p], (IsUnit X ∨ IsUnit Y ∨ IsUnit Z) ∧
      (p : ℤ_[p]) * u * X ^ 2 + (p : ℤ_[p]) * v * Y ^ 2 + (-1) * Z ^ 2 = 0 := by
  rintro ⟨X, Y, Z, hprim, h⟩
  have hp_zero : PadicInt.toZMod (p : ℤ_[p]) = 0 := by rw [map_natCast, ZMod.natCast_self]
  have hpne : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hZbar : PadicInt.toZMod Z = 0 := by
    have hh := congrArg PadicInt.toZMod h
    simp only [map_add, map_mul, map_pow, map_neg, hp_zero, zero_mul, neg_mul, one_mul,
      add_zero, zero_add, neg_eq_zero, map_zero] at hh
    exact pow_eq_zero_iff (by norm_num) |>.mp hh
  obtain ⟨Z', hZ'⟩ := (PadicInt.norm_lt_one_iff_dvd Z).mp ((toZMod_eq_zero_iff_norm_lt_one Z).mp hZbar)
  have hin : u * X ^ 2 + v * Y ^ 2 = (p : ℤ_[p]) * Z' ^ 2 := by
    apply mul_left_cancel₀ hpne
    rw [hZ'] at h
    linear_combination h
  have hmod : PadicInt.toZMod u * PadicInt.toZMod X ^ 2 + PadicInt.toZMod v * PadicInt.toZMod Y ^ 2 = 0 := by
    have := congrArg PadicInt.toZMod hin
    simpa only [map_add, map_mul, map_pow, hp_zero, zero_mul] using this
  have hvu : IsUnit (PadicInt.toZMod v) := hv.map _
  have hXbar : PadicInt.toZMod X = 0 := by
    by_contra hXne
    apply hunsq
    refine ⟨PadicInt.toZMod v * PadicInt.toZMod Y / PadicInt.toZMod X, ?_⟩
    rw [map_neg, map_mul]
    field_simp
    linear_combination -PadicInt.toZMod v * hmod
  have hYbar : PadicInt.toZMod Y = 0 := by
    rw [hXbar] at hmod
    have : PadicInt.toZMod v * PadicInt.toZMod Y ^ 2 = 0 := by linear_combination hmod
    rcases mul_eq_zero.mp this with hh | hh
    · exact absurd hh hvu.ne_zero
    · exact pow_eq_zero_iff (by norm_num) |>.mp hh
  exact hprim.elim (not_isUnit_of_toZMod_eq_zero hXbar)
    (fun hh => hh.elim (not_isUnit_of_toZMod_eq_zero hYbar) (not_isUnit_of_toZMod_eq_zero hZbar))

/-- **Anisotropy of `pu·x² + pv·y² − z² = 0` over `ℚ_[p]` (`-uv` non-square).** The full converse of the
symbol ⟺ solvability bridge in the `(p·u, p·v)` case: generic extraction
(`exists_primitive_diag_ternary`) ∘ the primitive anisotropy. -/
theorem no_padic_sol_pUnit_pUnit {p : ℕ} [Fact p.Prime] {u v : ℤ_[p]} (hv : IsUnit v)
    (hunsq : ¬ IsSquare (PadicInt.toZMod (-(u * v)))) :
    ¬ ∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      ((p : ℤ_[p]) * u : ℚ_[p]) * x ^ 2 + ((p : ℤ_[p]) * v : ℚ_[p]) * y ^ 2 +
        ((-1 : ℤ_[p]) : ℚ_[p]) * z ^ 2 = 0 :=
  fun hsol => no_primitive_sol_pUnit_pUnit hv hunsq (exists_primitive_diag_ternary hsol)

/-- **Solvability criterion for `z² = u x² + p v y²` (odd `p`, `u, v` units).** The complete `(u, p·v)`
symbol case as an iff: solvable over `ℚ_[p]` ⟺ `ū` is a square mod `p`. Forward = converse of
`no_padic_sol_unit_pUnit`; backward = `u` square ⟹ the `a`-coefficient is a square ⟹
`solvable_ternary_of_sufficient`. This is the form the Hasse–Minkowski local condition consumes. -/
theorem solvable_unit_pUnit_iff {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {u v : ℤ_[p]} (hu : IsUnit u)
    (hv : IsUnit v) :
    (∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = (u : ℚ_[p]) * x ^ 2 + (p : ℚ_[p]) * v * y ^ 2) ↔ IsSquare (PadicInt.toZMod u) := by
  constructor
  · intro hsolv
    by_contra hns
    exact no_padic_sol_unit_pUnit hv hns hsolv
  · intro hsq
    obtain ⟨w, hw⟩ := isSquare_of_isSquare_toZMod hp hu hsq
    exact solvable_ternary_of_sufficient (Or.inl ⟨(w : ℚ_[p]), by rw [hw]; push_cast; ring⟩)

/-- **Solvability criterion for `z² = pu x² + pv y²` (odd `p`, `u, v` units).** The complete `(p·u, p·v)`
symbol case as an iff: solvable over `ℚ_[p]` ⟺ `-uv` is a square mod `p`. Forward = converse of
`no_padic_sol_pUnit_pUnit`; backward = `-uv` square ⟹ `-(pu·pv) = (p·w)²` ⟹ `solvable_ternary_of_sufficient`
(binary part vanishes). The Hasse–Minkowski local condition in the both-`p·unit` case. -/
theorem solvable_pUnit_pUnit_iff {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {u v : ℤ_[p]} (hu : IsUnit u)
    (hv : IsUnit v) :
    (∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = (p : ℚ_[p]) * u * x ^ 2 + (p : ℚ_[p]) * v * y ^ 2) ↔
      IsSquare (PadicInt.toZMod (-(u * v))) := by
  have hpne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  constructor
  · intro hsolv
    by_contra hns
    refine no_padic_sol_pUnit_pUnit hv hns ?_
    obtain ⟨x, y, z, hxyz, he⟩ := hsolv
    exact ⟨x, y, z, hxyz, by push_cast; linear_combination -he⟩
  · intro hsq
    obtain ⟨w, hw⟩ := isSquare_of_isSquare_toZMod hp (hu.mul hv).neg hsq
    refine solvable_ternary_of_sufficient
      (Or.inr (Or.inr ⟨mul_ne_zero hpne (by rw [Ne, PadicInt.coe_eq_zero]; exact hu.ne_zero),
        ⟨(p : ℚ_[p]) * w, ?_⟩⟩))
    rw [show -((p : ℚ_[p]) * u * ((p : ℚ_[p]) * v)) = (p : ℚ_[p]) ^ 2 * ((-(u * v) : ℤ_[p]) : ℚ_[p]) from by
      push_cast; ring, hw]
    push_cast; ring

/-- **Solvability criterion for `z² = p u x² + v y²` (odd `p`, `u, v` units).** The `(p·u, v)` symbol case
(`p` on the *first* coefficient): solvable over `ℚ_[p]` ⟺ `v̄` is a square mod `p`. Swap to the
`solvable_unit_pUnit_iff` form via `solvable_canonical_symm`. -/
theorem solvable_pUnit_unit_iff {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {u v : ℤ_[p]} (hu : IsUnit u)
    (hv : IsUnit v) :
    (∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = (p : ℚ_[p]) * u * x ^ 2 + (v : ℚ_[p]) * y ^ 2) ↔ IsSquare (PadicInt.toZMod v) := by
  constructor
  · rintro ⟨x, y, z, hnz, he⟩
    exact (solvable_unit_pUnit_iff hp hv hu).mp
      ⟨y, x, z, fun hc => hnz ⟨hc.2.1, hc.1, hc.2.2⟩, by linear_combination he⟩
  · intro hsq
    obtain ⟨x, y, z, hnz, he⟩ := (solvable_unit_pUnit_iff hp hv hu).mpr hsq
    exact ⟨y, x, z, fun hc => hnz ⟨hc.2.1, hc.1, hc.2.2⟩, by linear_combination he⟩

/-- **2-adic forward solvability.** If `u ≡ 1 (mod 8)` (a `2`-adic square) then `z² = u x² + b y²` is
solvable over `ℚ_[2]` for any `b` (take `y = 0`, `z = √u · x`). The easy direction of the `p = 2` symbol
case, via the 2-adic square criterion `isSquare_of_toZModPow_three_eq_one`. -/
theorem solvable_2adic_of_unit_sq {u : ℤ_[2]} (hu8 : PadicInt.toZModPow 3 u = 1) (b : ℚ_[2]) :
    ∃ x y z : ℚ_[2], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ z ^ 2 = (u : ℚ_[2]) * x ^ 2 + b * y ^ 2 := by
  obtain ⟨w, hw⟩ := isSquare_of_toZModPow_three_eq_one hu8
  exact solvable_ternary_of_sufficient (Or.inl ⟨(w : ℚ_[2]), by rw [hw]; push_cast; ring⟩)

/-- **2-adic solvability from a represented unit-square.** If `u X² + v Y²` is a `2`-adic unit-square
(`toZModPow 3 (u X² + v Y²) = 1`), then `z² = u x² + v y²` is solvable over `ℚ_[2]` (take `z = √(u X²+v Y²)`,
`x = X`, `y = Y`). The lifting half of the `p = 2` symbol↔solvability bridge: a primitive mod-8 representation
of a square lifts to a genuine `ℚ_[2]` solution. -/
theorem solvable_2adic_of_repr_sq {u v X Y : ℤ_[2]}
    (h : PadicInt.toZModPow 3 (u * X ^ 2 + v * Y ^ 2) = 1) :
    ∃ x y z : ℚ_[2], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = (u : ℚ_[2]) * x ^ 2 + (v : ℚ_[2]) * y ^ 2 := by
  obtain ⟨w, hw⟩ := isSquare_of_toZModPow_three_eq_one h
  have hw0 : w ≠ 0 := by
    rintro rfl; rw [mul_zero] at hw; rw [hw, map_zero] at h; exact absurd h (by decide)
  refine ⟨(X : ℚ_[2]), (Y : ℚ_[2]), (w : ℚ_[2]), ?_, ?_⟩
  · exact fun hc => hw0 (PadicInt.coe_eq_zero.mp hc.2.2)
  · have heq : ((u * X ^ 2 + v * Y ^ 2 : ℤ_[2]) : ℚ_[2]) = ((w * w : ℤ_[2]) : ℚ_[2]) := by rw [hw]
    push_cast at heq ⊢; linear_combination -heq

/-- **A `ℤ_[2]` unit reduces mod 8 to an odd residue** (`val % 2 = 1`). -/
theorem isUnit_zmod8_val_odd {z : ZMod 8} (h : IsUnit z) : z.val % 2 = 1 := by
  have hc : Nat.Coprime z.val 8 := by
    have hi := ZMod.isUnit_iff_coprime z.val 8
    rw [ZMod.natCast_zmod_val] at hi; exact hi.mp h
  have hnd : ¬ 2 ∣ z.val := fun hd => by
    have h2 : (2 : ℕ) ∣ 1 := hc ▸ Nat.dvd_gcd hd (by norm_num)
    omega
  omega

/-- **2-adic solvability for the both-`2·` case from a `2 × unit-square` representation.** If
`a X² + b Y² = 2 c` with `c` a `2`-adic unit-square (`toZModPow 3 c = 1`), then `z² = 2a x² + 2b y²` is
solvable over `ℚ_[2]` (take `z = 2√c`, `x = X`, `y = Y`: `z² = 4c = 2(aX²+bY²)`). The lifting half of the
`(2·unit)/(2·unit)` p=2 case, where the represented value is even. -/
theorem solvable_2adic_of_repr_two {a b X Y c : ℤ_[2]} (hc : a * X ^ 2 + b * Y ^ 2 = 2 * c)
    (h : PadicInt.toZModPow 3 c = 1) :
    ∃ x y z : ℚ_[2], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = (2 : ℚ_[2]) * (a : ℚ_[2]) * x ^ 2 + (2 : ℚ_[2]) * (b : ℚ_[2]) * y ^ 2 := by
  obtain ⟨w, hw⟩ := isSquare_of_toZModPow_three_eq_one h
  have hw0 : w ≠ 0 := by rintro rfl; rw [mul_zero] at hw; rw [hw, map_zero] at h; exact absurd h (by decide)
  refine ⟨(X : ℚ_[2]), (Y : ℚ_[2]), (2 : ℚ_[2]) * (w : ℚ_[2]), ?_, ?_⟩
  · refine fun hcc => hw0 ?_
    have h2w : (2 : ℚ_[2]) * (w : ℚ_[2]) = 0 := hcc.2.2
    rcases mul_eq_zero.mp h2w with h2 | h2
    · exact absurd h2 (by norm_num)
    · exact PadicInt.coe_eq_zero.mp h2
  · have h2c : ((2 : ℤ_[2]) : ℚ_[2]) = 2 := by norm_cast
    have heq : ((a * X ^ 2 + b * Y ^ 2 : ℤ_[2]) : ℚ_[2]) = ((2 * c : ℤ_[2]) : ℚ_[2]) := by rw [hc]
    have hcw : ((c : ℤ_[2]) : ℚ_[2]) = ((w : ℤ_[2]) : ℚ_[2]) ^ 2 := by rw [hw]; push_cast; ring
    push_cast [h2c] at heq ⊢
    linear_combination -2 * heq - 4 * hcw

/-- **Both-`2·` reduction (field-generic).** Over a field with `2 ≠ 0` and `u ≠ 0`, the form
`z² = 2u x² + 2v y²` is solvable iff `z² = 2u x² + (-(u·v)) y²` is. (Forward: `(x,y,z) ↦ (z, 2y, 2u·x)`;
backward: `(x,y,z) ↦ (z, u·y, 2u·x)`.) This is the algebraic identity behind the `(2·unit)/(2·unit)` p=2
case: it sends it to the already-bridged `(2·unit)/unit` shape, dodging the mod-16 obstruction. -/
theorem two_two_reduce {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {u v : K} (hu : u ≠ 0) :
    (∃ x y z : K, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ z ^ 2 = 2 * u * x ^ 2 + 2 * v * y ^ 2) ↔
    (∃ x y z : K, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ z ^ 2 = 2 * u * x ^ 2 + (-(u * v)) * y ^ 2) := by
  have h2u : 2 * u ≠ 0 := mul_ne_zero h2 hu
  constructor
  · rintro ⟨x, y, z, hnz, he⟩
    refine ⟨z, 2 * y, 2 * u * x, ?_, by linear_combination (-2 * u) * he⟩
    rintro ⟨h1, h2', h3⟩
    exact hnz ⟨(mul_eq_zero.mp h3).resolve_left h2u, (mul_eq_zero.mp h2').resolve_left h2, h1⟩
  · rintro ⟨x, y, z, hnz, he⟩
    refine ⟨z, u * y, 2 * u * x, ?_, by linear_combination (-2 * u) * he⟩
    rintro ⟨h1, h2', h3⟩
    exact hnz ⟨(mul_eq_zero.mp h3).resolve_left h2u, (mul_eq_zero.mp h2').resolve_left hu, h1⟩

/-- **2-adic solvability reduces to a primitive mod-8 solution.** If `z² = u x² + v y²` is solvable over
`ℚ_[2]`, then it has a solution modulo 8 with an *odd* (unit) coordinate (reduce a primitive `ℤ_[2]` solution
via `toZModPow 3`; a unit coordinate stays a unit mod 8, hence odd). The descent half of the `p = 2`
symbol↔solvability bridge — pairs with `solvable_2adic_of_repr_sq` and the `ZMod 8` `decide`. -/
theorem solvable_2adic_imp_mod8 {u v : ℤ_[2]}
    (h : ∃ x y z : ℚ_[2], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = (u : ℚ_[2]) * x ^ 2 + (v : ℚ_[2]) * y ^ 2) :
    ∃ X Y Z : ZMod 8, (X.val % 2 = 1 ∨ Y.val % 2 = 1 ∨ Z.val % 2 = 1) ∧
      Z ^ 2 = PadicInt.toZModPow 3 u * X ^ 2 + PadicInt.toZModPow 3 v * Y ^ 2 := by
  have hter : ∃ x y z : ℚ_[2], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      (u : ℚ_[2]) * x ^ 2 + (v : ℚ_[2]) * y ^ 2 + ((-1 : ℤ_[2]) : ℚ_[2]) * z ^ 2 = 0 := by
    obtain ⟨x, y, z, hnz, he⟩ := h
    exact ⟨x, y, z, hnz, by push_cast; linear_combination -he⟩
  obtain ⟨X, Y, Z, hprim, heq⟩ := exists_primitive_diag_ternary (p := 2) (a := u) (b := v) (c := -1) hter
  refine ⟨PadicInt.toZModPow 3 X, PadicInt.toZModPow 3 Y, PadicInt.toZModPow 3 Z, ?_, ?_⟩
  · rcases hprim with hh | hh | hh
    exacts [Or.inl (isUnit_zmod8_val_odd (hh.map (PadicInt.toZModPow 3))),
      Or.inr (Or.inl (isUnit_zmod8_val_odd (hh.map (PadicInt.toZModPow 3)))),
      Or.inr (Or.inr (isUnit_zmod8_val_odd (hh.map (PadicInt.toZModPow 3))))]
  · have hc := congrArg (PadicInt.toZModPow 3) heq
    simp only [map_add, map_mul, map_pow, map_neg, map_one, map_zero] at hc
    linear_combination -hc

/-- **2-adic unit/unit solvability ⟺ symbol condition, at the residue level (finite `decide`).** For odd
residues `u, v : ZMod 8`, the form `Z² = u X² + v Y²` has a nontrivial (unit-coordinate) solution mod 8 iff
`eps2 u · eps2 v = 0` (i.e. `u ≡ 1` or `v ≡ 1 mod 4`) — the mod-8 content of `(u,v)_2 = 1`. Pure `decide` over
`ZMod 8` (no `native_decide`). The combinatorial heart of the `p = 2` unit/unit symbol↔solvability bridge. -/
theorem padic2_unit_sol_mod8_iff : ∀ u v : ZMod 8, u.val % 2 = 1 → v.val % 2 = 1 →
    ((∃ X Y Z : ZMod 8, (X.val % 2 = 1 ∨ Y.val % 2 = 1 ∨ Z.val % 2 = 1) ∧
        Z ^ 2 = u * X ^ 2 + v * Y ^ 2) ↔
      HilbertSymbol.eps2 u * HilbertSymbol.eps2 v = 0) := by decide

/-- **Forward p=2 decide:** if `eps2 u · eps2 v = 0` (odd `u, v : ZMod 8`) then `u X² + v Y² = 1` has a
solution mod 8 — feeding `solvable_2adic_of_repr_sq` (`u X² + v Y² ≡ 1 ≡ square mod 8`). Pure `decide`. -/
theorem padic2_unit_repr_one : ∀ u v : ZMod 8, u.val % 2 = 1 → v.val % 2 = 1 →
    HilbertSymbol.eps2 u * HilbertSymbol.eps2 v = 0 → ∃ X Y : ZMod 8, u * X ^ 2 + v * Y ^ 2 = 1 := by
  decide

/-- **p=2 (2·unit)/unit decide** (descent): `Z² = 2u X² + v Y²` has a unit-coordinate solution mod 8 ⟺
`eps2 u · eps2 v + omega2 v = 0`. Pure `decide`. -/
theorem padic2_2unit_sol_mod8_iff : ∀ u v : ZMod 8, u.val % 2 = 1 → v.val % 2 = 1 →
    ((∃ X Y Z : ZMod 8, (X.val % 2 = 1 ∨ Y.val % 2 = 1 ∨ Z.val % 2 = 1) ∧
        Z ^ 2 = 2 * u * X ^ 2 + v * Y ^ 2) ↔
      HilbertSymbol.eps2 u * HilbertSymbol.eps2 v + HilbertSymbol.omega2 v = 0) := by decide

/-- **p=2 (2·unit)/unit decide** (forward): the symbol condition gives a mod-8 representation of `1`. -/
theorem padic2_2unit_repr_one : ∀ u v : ZMod 8, u.val % 2 = 1 → v.val % 2 = 1 →
    HilbertSymbol.eps2 u * HilbertSymbol.eps2 v + HilbertSymbol.omega2 v = 0 →
    ∃ X Y : ZMod 8, 2 * u * X ^ 2 + v * Y ^ 2 = 1 := by decide

/-- `chi2 e = 1 ↔ e = 0` (the dyadic character is `+1` exactly on `0 : ZMod 2`). -/
theorem chi2_eq_one_iff (e : ZMod 2) : HilbertSymbol.chi2 e = 1 ↔ e = 0 := by revert e; decide

/-- **`hilbert2Int` for odd integers ⟺ `eps2` condition.** For odd `u, v`, the dyadic Hilbert symbol's
valuation (`ω`) terms vanish, so `hilbert2Int u v = χ₂(eps2 ū · eps2 v̄) = 1 ⟺ eps2 ū · eps2 v̄ = 0`. The
connection from the combinatorial dyadic symbol to the `ZMod 8` `decide` condition. -/
theorem hilbert2Int_odd_eq_one_iff {u v : ℤ} (hu : ¬ (2 : ℤ) ∣ u) (hv : ¬ (2 : ℤ) ∣ v) :
    HilbertSymbol.hilbert2Int u v = 1 ↔
    HilbertSymbol.eps2 ((u : ℤ) : ZMod 8) * HilbertSymbol.eps2 ((v : ℤ) : ZMod 8) = 0 := by
  have hpu : HilbertSymbol.pfreeInt 2 u = u := by
    rw [HilbertSymbol.pfreeInt, padicValInt.eq_zero_of_not_dvd hu, pow_zero, Int.ediv_one]
  have hpv : HilbertSymbol.pfreeInt 2 v = v := by
    rw [HilbertSymbol.pfreeInt, padicValInt.eq_zero_of_not_dvd hv, pow_zero, Int.ediv_one]
  rw [HilbertSymbol.hilbert2Int, hpu, hpv, padicValInt.eq_zero_of_not_dvd hu,
      padicValInt.eq_zero_of_not_dvd hv]
  simp only [Nat.cast_zero, zero_mul, add_zero]
  exact chi2_eq_one_iff _

/-- **`hilbert2Int (2u) v` for odd integers ⟺ `eps2`/`omega2` condition.** Valuation `1` in the first
argument activates the `ω(v)` term: `hilbert2Int (2u) v = χ₂(eps2 ū · eps2 v̄ + omega2 v̄) = 1 ⟺
eps2 ū · eps2 v̄ + omega2 v̄ = 0`. -/
theorem hilbert2Int_2unit_unit_eq_one_iff {u v : ℤ} (hu : ¬ (2 : ℤ) ∣ u) (hv : ¬ (2 : ℤ) ∣ v) :
    HilbertSymbol.hilbert2Int (2 * u) v = 1 ↔
    HilbertSymbol.eps2 ((u : ℤ) : ZMod 8) * HilbertSymbol.eps2 ((v : ℤ) : ZMod 8)
      + HilbertSymbol.omega2 ((v : ℤ) : ZMod 8) = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu0 : u ≠ 0 := fun h => hu (h ▸ dvd_zero _)
  have hval2 : padicValInt 2 (2 * u) = 1 := by
    rw [padicValInt.mul (by norm_num) hu0, padicValInt.eq_zero_of_not_dvd hu, add_zero]
    exact padicValInt_self
  have hpu2 : HilbertSymbol.pfreeInt 2 (2 * u) = u := by
    rw [HilbertSymbol.pfreeInt, hval2, pow_one]; push_cast; omega
  have hpv : HilbertSymbol.pfreeInt 2 v = v := by
    rw [HilbertSymbol.pfreeInt, padicValInt.eq_zero_of_not_dvd hv, pow_zero, Int.ediv_one]
  rw [HilbertSymbol.hilbert2Int, hpu2, hpv, hval2, padicValInt.eq_zero_of_not_dvd hv]
  simp only [Nat.cast_one, one_mul, Nat.cast_zero, zero_mul, add_zero]
  exact chi2_eq_one_iff _

/-- **`hilbert2Int (2u)(2w)` value (both `2·unit`).** Both valuations `1`, both `ω` terms active:
`hilbert2Int (2u)(2w) = χ₂(eps2 ū·eps2 w̄ + omega2 ū + omega2 w̄)`. -/
theorem hilbert2Int_2unit_2unit_eq {u w : ℤ} (hu : ¬ (2 : ℤ) ∣ u) (hw : ¬ (2 : ℤ) ∣ w) :
    HilbertSymbol.hilbert2Int (2 * u) (2 * w) =
      HilbertSymbol.chi2 (HilbertSymbol.eps2 ((u : ℤ) : ZMod 8) * HilbertSymbol.eps2 ((w : ℤ) : ZMod 8)
        + HilbertSymbol.omega2 ((u : ℤ) : ZMod 8) + HilbertSymbol.omega2 ((w : ℤ) : ZMod 8)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu0 : u ≠ 0 := fun h => hu (h ▸ dvd_zero _)
  have hw0 : w ≠ 0 := fun h => hw (h ▸ dvd_zero _)
  have hvu : padicValInt 2 (2 * u) = 1 := by
    rw [padicValInt.mul (by norm_num) hu0, padicValInt.eq_zero_of_not_dvd hu, add_zero]
    exact padicValInt_self
  have hvw : padicValInt 2 (2 * w) = 1 := by
    rw [padicValInt.mul (by norm_num) hw0, padicValInt.eq_zero_of_not_dvd hw, add_zero]
    exact padicValInt_self
  have hpu : HilbertSymbol.pfreeInt 2 (2 * u) = u := by
    rw [HilbertSymbol.pfreeInt, hvu, pow_one]; push_cast; omega
  have hpw : HilbertSymbol.pfreeInt 2 (2 * w) = w := by
    rw [HilbertSymbol.pfreeInt, hvw, pow_one]; push_cast; omega
  rw [HilbertSymbol.hilbert2Int, hpu, hpw, hvu, hvw]
  simp only [Nat.cast_one, one_mul]
  congr 1; ring

/-- Steinberg `ZMod 8` decide: for odd `u`, `eps2 u·eps2(-u) + omega2 u + omega2(-u) = 0`. -/
theorem padic2_steinberg_decide : ∀ u : ZMod 8, u.val % 2 = 1 →
    HilbertSymbol.eps2 u * HilbertSymbol.eps2 (-u) + HilbertSymbol.omega2 u
      + HilbertSymbol.omega2 (-u) = 0 := by decide

/-- **Steinberg for the dyadic symbol at `2·unit`:** `hilbert2Int (2u) (-(2u)) = 1` (odd `u`). -/
theorem hilbert2Int_2unit_neg2unit_eq_one {u : ℤ} (hu : ¬ (2 : ℤ) ∣ u) :
    HilbertSymbol.hilbert2Int (2 * u) (-(2 * u)) = 1 := by
  have hnu : ¬ (2 : ℤ) ∣ -u := fun h => hu (dvd_neg.mp h)
  have hu8 : ((u : ℤ) : ZMod 8).val % 2 = 1 := by have h := @ZMod.val_intCast 8 u _; omega
  rw [show -(2 * u) = 2 * (-u) by ring, hilbert2Int_2unit_2unit_eq hu hnu,
      show ((-u : ℤ) : ZMod 8) = -((u : ℤ) : ZMod 8) by push_cast; ring, chi2_eq_one_iff]
  exact padic2_steinberg_decide _ hu8

/-- **Symbol identity:** `hilbert2Int (2u)(2v) = hilbert2Int (2u)(-(u·v))` (odd `u,v`). Product of the two
is `hilbert2Int (2u)(-(2u)·v²) = (2u,-2u)·(2u,v²) = 1·1 = 1`; both are `±1`, so they are equal. -/
theorem hilbert2Int_2unit_2unit_eq_neguv {u v : ℤ} (hu : ¬ (2 : ℤ) ∣ u) (hv : ¬ (2 : ℤ) ∣ v) :
    HilbertSymbol.hilbert2Int (2 * u) (2 * v) = HilbertSymbol.hilbert2Int (2 * u) (-(u * v)) := by
  have hv0 : v ≠ 0 := fun h => hv (h ▸ dvd_zero _)
  have hu0 : u ≠ 0 := fun h => hu (h ▸ dvd_zero _)
  have h2u0 : (2 * u : ℤ) ≠ 0 := mul_ne_zero (by norm_num) hu0
  have hprod : HilbertSymbol.hilbert2Int (2 * u) (2 * v) *
      HilbertSymbol.hilbert2Int (2 * u) (-(u * v)) = 1 := by
    rw [← HilbertSymbol.hilbert2Int_mul_right (mul_ne_zero (by norm_num) hv0)
          (neg_ne_zero.mpr (mul_ne_zero hu0 hv0)),
        show 2 * v * -(u * v) = -(2 * u) * (v * v) by ring,
        HilbertSymbol.hilbert2Int_mul_right (neg_ne_zero.mpr h2u0) (mul_ne_zero hv0 hv0),
        hilbert2Int_2unit_neg2unit_eq_one hu,
        HilbertSymbol.hilbert2Int_mul_right hv0 hv0]
    rcases HilbertSymbol.hilbert2Int_mem (2 * u) v with h | h <;> rw [h] <;> ring
  rcases HilbertSymbol.hilbert2Int_mem (2 * u) (2 * v) with h1 | h1 <;>
    rcases HilbertSymbol.hilbert2Int_mem (2 * u) (-(u * v)) with h2 | h2 <;>
    rw [h1, h2] at hprod ⊢ <;> simp_all

/-- **p=2 unit/unit symbol↔solvability bridge.** For odd integers `u, v`, `z² = u x² + v y²` is solvable
over `ℚ_[2]` iff `hilbert2Int u v = 1`. Assembled from the lift (`solvable_2adic_of_repr_sq`), descent
(`solvable_2adic_imp_mod8`), the `ZMod 8` `decide`s (`padic2_unit_sol_mod8_iff`, `padic2_unit_repr_one`), and
the symbol connection (`hilbert2Int_odd_eq_one_iff`). -/
theorem solvable_2adic_unit_iff {u v : ℤ} (hu : ¬ (2 : ℤ) ∣ u) (hv : ¬ (2 : ℤ) ∣ v) :
    (∃ x y z : ℚ_[2], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = (u : ℚ_[2]) * x ^ 2 + (v : ℚ_[2]) * y ^ 2) ↔
    HilbertSymbol.hilbert2Int u v = 1 := by
  have hu8 : ((u : ℤ) : ZMod 8).val % 2 = 1 := by have h := @ZMod.val_intCast 8 u _; omega
  have hv8 : ((v : ℤ) : ZMod 8).val % 2 = 1 := by have h := @ZMod.val_intCast 8 v _; omega
  rw [hilbert2Int_odd_eq_one_iff hu hv]
  constructor
  · intro hsol
    have hsol2 : ∃ x y z : ℚ_[2], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
        z ^ 2 = ((u : ℤ_[2]) : ℚ_[2]) * x ^ 2 + ((v : ℤ_[2]) : ℚ_[2]) * y ^ 2 := by
      obtain ⟨x, y, z, hnz, he⟩ := hsol
      exact ⟨x, y, z, hnz, by rw [PadicInt.coe_intCast, PadicInt.coe_intCast]; exact he⟩
    obtain ⟨X, Y, Z, hprim, heq⟩ := solvable_2adic_imp_mod8 hsol2
    rw [show PadicInt.toZModPow 3 ((u : ℤ) : ℤ_[2]) = ((u : ℤ) : ZMod 8) from map_intCast _ u,
        show PadicInt.toZModPow 3 ((v : ℤ) : ℤ_[2]) = ((v : ℤ) : ZMod 8) from map_intCast _ v] at heq
    exact (padic2_unit_sol_mod8_iff _ _ hu8 hv8).mp ⟨X, Y, Z, hprim, heq⟩
  · intro heps
    obtain ⟨X, Y, hXY⟩ := padic2_unit_repr_one _ _ hu8 hv8 heps
    have hlift : ∀ X : ZMod 8, PadicInt.toZModPow 3 ((X.val : ℤ_[2])) = X := by
      intro X; rw [map_natCast, ZMod.natCast_val, ZMod.cast_id]
    have key : PadicInt.toZModPow 3 ((u : ℤ_[2]) * (X.val : ℤ_[2]) ^ 2
        + (v : ℤ_[2]) * (Y.val : ℤ_[2]) ^ 2) = 1 := by
      rw [map_add, map_mul, map_mul, map_pow, map_pow, hlift, hlift, map_intCast, map_intCast]
      exact hXY
    have := solvable_2adic_of_repr_sq key
    obtain ⟨x, y, z, hnz, he⟩ := this
    exact ⟨x, y, z, hnz, by rw [← PadicInt.coe_intCast (u), ← PadicInt.coe_intCast (v)]; exact he⟩

/-- **p=2 (2·unit)/unit symbol↔solvability bridge.** For odd integers `u, v`, `z² = (2u) x² + v y²` is
solvable over `ℚ_[2]` iff `hilbert2Int (2u) v = 1`. Parallel to `solvable_2adic_unit_iff`, with the (2·unit)
decides and the `((2u : ZMod 8)) = 2 · (u : ZMod 8)` conversion. -/
theorem solvable_2adic_pUnit_unit_iff {u v : ℤ} (hu : ¬ (2 : ℤ) ∣ u) (hv : ¬ (2 : ℤ) ∣ v) :
    (∃ x y z : ℚ_[2], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = ((2 * u : ℤ) : ℚ_[2]) * x ^ 2 + (v : ℚ_[2]) * y ^ 2) ↔
    HilbertSymbol.hilbert2Int (2 * u) v = 1 := by
  have hu8 : ((u : ℤ) : ZMod 8).val % 2 = 1 := by have h := @ZMod.val_intCast 8 u _; omega
  have hv8 : ((v : ℤ) : ZMod 8).val % 2 = 1 := by have h := @ZMod.val_intCast 8 v _; omega
  have hconv : ((2 * u : ℤ) : ZMod 8) = 2 * ((u : ℤ) : ZMod 8) := by push_cast; ring
  rw [hilbert2Int_2unit_unit_eq_one_iff hu hv]
  have hlift : ∀ X : ZMod 8, PadicInt.toZModPow 3 ((X.val : ℤ_[2])) = X := by
    intro X; rw [map_natCast, ZMod.natCast_val, ZMod.cast_id]
  constructor
  · intro hsol
    have hsol2 : ∃ x y z : ℚ_[2], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
        z ^ 2 = (((2 * u : ℤ) : ℤ_[2]) : ℚ_[2]) * x ^ 2 + ((v : ℤ_[2]) : ℚ_[2]) * y ^ 2 := by
      obtain ⟨x, y, z, hnz, he⟩ := hsol
      exact ⟨x, y, z, hnz, by rw [PadicInt.coe_intCast, PadicInt.coe_intCast]; exact he⟩
    obtain ⟨X, Y, Z, hprim, heq⟩ := solvable_2adic_imp_mod8 hsol2
    rw [show PadicInt.toZModPow 3 ((2 * u : ℤ) : ℤ_[2]) = ((2 * u : ℤ) : ZMod 8) from map_intCast _ _,
        show PadicInt.toZModPow 3 ((v : ℤ) : ℤ_[2]) = ((v : ℤ) : ZMod 8) from map_intCast _ v,
        hconv] at heq
    exact (padic2_2unit_sol_mod8_iff _ _ hu8 hv8).mp ⟨X, Y, Z, hprim, heq⟩
  · intro heps
    obtain ⟨X, Y, hXY⟩ := padic2_2unit_repr_one _ _ hu8 hv8 heps
    have key : PadicInt.toZModPow 3 (((2 * u : ℤ) : ℤ_[2]) * (X.val : ℤ_[2]) ^ 2
        + ((v : ℤ) : ℤ_[2]) * (Y.val : ℤ_[2]) ^ 2) = 1 := by
      rw [map_add, map_mul, map_mul, map_pow, map_pow, hlift, hlift, map_intCast, map_intCast, hconv]
      exact hXY
    obtain ⟨x, y, z, hnz, he⟩ := solvable_2adic_of_repr_sq key
    exact ⟨x, y, z, hnz, by rw [← PadicInt.coe_intCast (2 * u), ← PadicInt.coe_intCast (v)]; exact he⟩

/-- **p=2 (2·unit)/(2·unit) symbol↔solvability bridge.** For odd integers `u, v`, `z² = (2u) x² + (2v) y²`
is solvable over `ℚ_[2]` iff `hilbert2Int (2u) (2v) = 1`. Via the symbol identity
`hilbert2Int_2unit_2unit_eq_neguv` (→ `hilbert2Int (2u) (-(uv))`), the field-generic `two_two_reduce`
(→ the `(2u, -(uv))` form), and `solvable_2adic_pUnit_unit_iff`. -/
theorem solvable_2adic_pUnit_pUnit_iff {u v : ℤ} (hu : ¬ (2 : ℤ) ∣ u) (hv : ¬ (2 : ℤ) ∣ v) :
    (∃ x y z : ℚ_[2], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = ((2 * u : ℤ) : ℚ_[2]) * x ^ 2 + ((2 * v : ℤ) : ℚ_[2]) * y ^ 2) ↔
    HilbertSymbol.hilbert2Int (2 * u) (2 * v) = 1 := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ dvd_zero _)
  have huv : ¬ (2 : ℤ) ∣ (u * v) := fun h => (Int.prime_two.dvd_mul.mp h).elim hu hv
  have hnuv : ¬ (2 : ℤ) ∣ (-(u * v)) := fun h => huv (dvd_neg.mp h)
  have hconv2u : ((2 * u : ℤ) : ℚ_[2]) = 2 * (u : ℚ_[2]) := by push_cast; ring
  have hconv2v : ((2 * v : ℤ) : ℚ_[2]) = 2 * (v : ℚ_[2]) := by push_cast; ring
  have hconvuv : (((-(u * v)) : ℤ) : ℚ_[2]) = -((u : ℚ_[2]) * (v : ℚ_[2])) := by push_cast; ring
  rw [hilbert2Int_2unit_2unit_eq_neguv hu hv, ← solvable_2adic_pUnit_unit_iff hu hnuv,
      hconv2u, hconv2v, hconvuv]
  exact two_two_reduce (by norm_num) (by exact_mod_cast hu0)

/-- **Square in `ℚ_[p]` ⟺ square in `ℤ_[p]`, for a unit.** A `p`-adic *unit* `u` is a square in the field
`ℚ_[p]` iff it is a square in the ring `ℤ_[p]` (a square root in `ℚ_[p]` has norm 1, hence lies in `ℤ_[p]`).
With `isSquare_iff_isSquare_toZMod` this gives "square in `ℚ_[p]` ⟺ residue square" — the link from field
squares to the residue criterion used in the rational-square local–global. -/
theorem isSquare_padic_coe_iff {p : ℕ} [Fact p.Prime] {u : ℤ_[p]} (hu : IsUnit u) :
    IsSquare ((u : ℚ_[p])) ↔ IsSquare u := by
  constructor
  · rintro ⟨w, hw⟩
    have hun : ‖(u : ℚ_[p])‖ = 1 := PadicInt.isUnit_iff.mp hu
    have hwn : ‖w‖ = 1 := by
      have h1 : ‖w‖ * ‖w‖ = 1 := by rw [← norm_mul, ← hw]; exact hun
      nlinarith [norm_nonneg w]
    obtain ⟨wL, _, hwL⟩ := exists_padicInt_unit_of_norm_one hwn
    refine ⟨wL, ?_⟩
    have hsub : (u - wL * wL : ℤ_[p]) = 0 := by
      rw [← PadicInt.coe_eq_zero]; push_cast [hwL]; rw [hw]; ring
    exact sub_eq_zero.mp hsub
  · rintro ⟨w, hw⟩
    exact ⟨(w : ℚ_[p]), by rw [hw]; push_cast; ring⟩

/-- **Squares in `ℚ_[p]` have even valuation.** If `x ≠ 0` is a square then `x.valuation` is even
(`valuation (w*w) = 2 · valuation w`). One direction of the field-square characterization, and the
local condition feeding the rational-square local–global. -/
theorem isSquare_valuation_even {p : ℕ} [Fact p.Prime] {x : ℚ_[p]} (hx : x ≠ 0) (h : IsSquare x) :
    Even x.valuation := by
  obtain ⟨w, hw⟩ := h
  have hwne : w ≠ 0 := fun hw0 => hx (by rw [hw, hw0, mul_zero])
  rw [hw, Padic.valuation_mul hwne hwne]
  exact ⟨w.valuation, rfl⟩

/-- **Odd-`p` field-square criterion (unit case).** A `p`-adic unit is a square in the field `ℚ_[p]` iff its
residue mod `p` is a square — the computable criterion assembled from `isSquare_padic_coe_iff` and
`isSquare_iff_isSquare_toZMod`. -/
theorem isSquare_padic_unit_iff_residue {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {u : ℤ_[p]}
    (hu : IsUnit u) : IsSquare ((u : ℚ_[p])) ↔ IsSquare (PadicInt.toZMod u) :=
  (isSquare_padic_coe_iff hu).trans (isSquare_iff_isSquare_toZMod hp hu)

/-- **A squarefree natural that is a square in every `ℚ_[p]` equals 1.** Any prime divisor `p` of a
squarefree `a > 1` gives `padicValNat p a = 1` (squarefree ⟹ ≤ 1, divides ⟹ ≥ 1), so `(a : ℚ_[p])` has odd
valuation and is not a square — contradicting `isSquare_valuation_even`. The squarefree core of the
integer/rational-square local–global (n = 2 Hasse–Minkowski). -/
theorem squarefree_eq_one_of_isSquare_padic {a : ℕ} (ha : Squarefree a)
    (h : ∀ (p : ℕ) [Fact p.Prime], IsSquare ((a : ℚ_[p]))) : a = 1 := by
  by_contra hne
  obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd hne
  haveI : Fact p.Prime := ⟨hp⟩
  have ha0 : a ≠ 0 := ha.ne_zero
  have hane : (a : ℚ_[p]) ≠ 0 := by exact_mod_cast ha0
  have heven : Even ((a : ℚ_[p]).valuation) := isSquare_valuation_even hane (h p)
  rw [Padic.valuation_natCast] at heven
  have hval1 : padicValNat p a = 1 := by
    have hle : a.factorization p ≤ 1 := (Nat.squarefree_iff_factorization_le_one ha0).mp ha p
    have hge : 1 ≤ a.factorization p := by
      rw [← Nat.Prime.dvd_iff_one_le_factorization hp ha0]; exact hpa
    have hfp : a.factorization p = 1 := le_antisymm hle hge
    rwa [Nat.factorization_def a hp] at hfp
  rw [hval1] at heven
  norm_num at heven

/-- **Integer-square local–global (natural numbers).** A natural number that is a square in every `ℚ_[p]`
is a square. Write `a = b²·s` with `s` squarefree (`Nat.sq_mul_squarefree`); `a` square ⟹ `s` square in
every `ℚ_[p]` ⟹ `s = 1` (`squarefree_eq_one_of_isSquare_padic`) ⟹ `a = b²`. The n = 2 Hasse–Minkowski
ingredient over ℕ. -/
theorem isSquare_nat_of_isSquare_padic {a : ℕ} (h : ∀ (p : ℕ) [Fact p.Prime], IsSquare ((a : ℚ_[p]))) :
    IsSquare a := by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact ⟨0, rfl⟩
  obtain ⟨s, b, hab, hsf⟩ := Nat.sq_mul_squarefree a
  have hb0 : b ≠ 0 := by rintro rfl; rw [zero_pow (by norm_num), zero_mul] at hab; exact ha0 hab.symm
  have hsq : s = 1 := by
    apply squarefree_eq_one_of_isSquare_padic hsf
    intro p inst
    haveI := inst
    obtain ⟨w, hw⟩ := h p
    have hbne : (b : ℚ_[p]) ≠ 0 := by exact_mod_cast hb0
    refine ⟨w / (b : ℚ_[p]), ?_⟩
    have hcast : (b : ℚ_[p]) ^ 2 * (s : ℚ_[p]) = w * w := by
      have hh := hw
      rw [← hab] at hh
      push_cast at hh
      linear_combination hh
    field_simp
    linear_combination hcast
  rw [hsq, mul_one] at hab
  exact ⟨b, by rw [← hab]; ring⟩

/-- **Integer-square local–global.** A nonnegative integer that is a square in every `ℚ_[p]` is a square
(reduce to `natAbs` via `isSquare_nat_of_isSquare_padic`). The full n = 2 Hasse–Minkowski ingredient over ℤ:
combined with `Real.isSquare_iff` (square in ℝ ⟺ `0 ≤ ·`) this is "square in every completion ⟹ square in ℤ". -/
theorem isSquare_int_of_isSquare_padic {n : ℤ} (hn : 0 ≤ n)
    (h : ∀ (p : ℕ) [Fact p.Prime], IsSquare ((n : ℚ_[p]))) : IsSquare n := by
  have hnat : ∀ (p : ℕ) [Fact p.Prime], IsSquare ((n.natAbs : ℚ_[p])) := by
    intro p inst
    haveI := inst
    have hc : ((n.natAbs : ℕ) : ℚ_[p]) = (n : ℚ_[p]) := by
      rw [← Int.cast_natCast (R := ℚ_[p]), Int.natAbs_of_nonneg hn]
    rw [hc]; exact h p
  obtain ⟨k, hk⟩ := isSquare_nat_of_isSquare_padic hnat
  refine ⟨(k : ℤ), ?_⟩
  rw [← Int.natAbs_of_nonneg hn, hk]; push_cast; ring

/-- **Rational-square local–global.** A nonnegative rational that is a square in every `ℚ_[p]` is a square.
Via `Rat.isSquare_iff` (`IsSquare q ↔ IsSquare q.num ∧ IsSquare q.den`): the product `q.num · q.den =
q · q.den²` is a square in every `ℚ_[p]` (square × square) and nonnegative, hence an integer square
(`isSquare_int_of_isSquare_padic`); then `Int.sq_of_isCoprime` (with `q.num`, `q.den` coprime) splits the
product square into `q.num` and `q.den` each square (sign forced by `0 ≤ q.num`, `0 < q.den`). The n = 2
Hasse–Minkowski ingredient over ℚ. -/
theorem isSquare_rat_of_isSquare_padic {q : ℚ} (hq : 0 ≤ q)
    (h : ∀ (p : ℕ) [Fact p.Prime], IsSquare ((q : ℚ_[p]))) : IsSquare q := by
  have hnum_nonneg : 0 ≤ q.num := Rat.num_nonneg.mpr hq
  have hdenpos : 0 < (q.den : ℤ) := by exact_mod_cast q.den_pos
  have hprod_padic : ∀ (p : ℕ) [Fact p.Prime], IsSquare ((q.num * (q.den : ℤ) : ℤ) : ℚ_[p]) := by
    intro p inst
    haveI := inst
    have hdne : (q.den : ℚ_[p]) ≠ 0 := by
      have hd : (q.den : ℕ) ≠ 0 := q.den_nz
      exact_mod_cast hd
    have key : ((q.num * (q.den : ℤ) : ℤ) : ℚ_[p]) = (q : ℚ_[p]) * (q.den : ℚ_[p]) ^ 2 := by
      rw [Rat.cast_def]
      push_cast
      field_simp
    rw [key]
    exact (h p).mul ⟨(q.den : ℚ_[p]), by ring⟩
  have hprod_nonneg : 0 ≤ q.num * (q.den : ℤ) := mul_nonneg hnum_nonneg (le_of_lt hdenpos)
  obtain ⟨c, hc⟩ := isSquare_int_of_isSquare_padic hprod_nonneg hprod_padic
  have hcop : IsCoprime q.num (q.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact q.reduced
  rw [Rat.isSquare_iff]
  refine ⟨?_, ?_⟩
  · obtain ⟨a0, ha0⟩ := Int.sq_of_isCoprime hcop (by rw [hc]; ring)
    rcases ha0 with h1 | h1
    · exact ⟨a0, by rw [h1]; ring⟩
    · have hz : q.num = 0 := le_antisymm (by rw [h1]; nlinarith [sq_nonneg a0]) hnum_nonneg
      exact ⟨0, by rw [hz]; ring⟩
  · rw [← Int.isSquare_natCast_iff]
    obtain ⟨a0, ha0⟩ := Int.sq_of_isCoprime hcop.symm (by rw [mul_comm, hc]; ring)
    rcases ha0 with h1 | h1
    · exact ⟨a0, by rw [h1]; ring⟩
    · exfalso; nlinarith [sq_nonneg a0, hdenpos]

/-- **Rational-square local–global, as an iff (Hasse–Minkowski n = 2 base case).** A rational is a square
iff it is a square at the real place (`0 ≤ q`) and at every finite place (`IsSquare (q : ℚ_[p])`). Forward:
squares are nonnegative in the ordered field ℚ and map to squares under the ring homs `ℚ → ℚ_[p]`. Backward
is `isSquare_rat_of_isSquare_padic`. This is exactly the local–global principle for binary forms: combined
with `exists_binary_zero_iff` (`a x² + b y² = 0` nontrivial ⟺ `IsSquare (-(a·b))`), a binary form over ℚ is
isotropic iff it is isotropic over ℝ and over every ℚ_p. -/
theorem isSquare_rat_iff_local {q : ℚ} :
    IsSquare q ↔ 0 ≤ q ∧ ∀ (p : ℕ) [Fact p.Prime], IsSquare ((q : ℚ_[p])) := by
  constructor
  · intro hsq
    refine ⟨?_, ?_⟩
    · obtain ⟨r, hr⟩ := hsq; rw [hr]; exact mul_self_nonneg r
    · intro p inst
      haveI := inst
      have hmap := hsq.map (Rat.castHom ℚ_[p])
      simpa using hmap
  · rintro ⟨hq, h⟩; exact isSquare_rat_of_isSquare_padic hq h

/-- **Squarefree representative of an integer square class.** Every nonzero integer equals a *squarefree*
integer times a perfect square: `n = s · c²` with `s` squarefree, `s ≠ 0`, `c ≠ 0`. (Factor
`n.natAbs = b²·a` with `a` squarefree by `Nat.sq_mul_squarefree`, set `s = sign(n)·a`, `c = b`.) -/
theorem exists_squarefree_sq_mul_int {n : ℤ} (hn : n ≠ 0) :
    ∃ (s c : ℤ), s ≠ 0 ∧ c ≠ 0 ∧ Squarefree s ∧ n = s * c ^ 2 := by
  obtain ⟨a, b, hab, hsf⟩ := Nat.sq_mul_squarefree n.natAbs
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num), zero_mul] at hab
    exact hn (Int.natAbs_eq_zero.mp hab.symm)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hab
    exact hn (Int.natAbs_eq_zero.mp hab.symm)
  refine ⟨n.sign * (a : ℤ), (b : ℤ), ?_, ?_, ?_, ?_⟩
  · exact mul_ne_zero (by rw [Ne, Int.sign_eq_zero_iff_zero]; exact hn) (by exact_mod_cast ha0)
  · exact_mod_cast hb0
  · rw [← Int.squarefree_natAbs, Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hn, one_mul,
      Int.natAbs_natCast]
    exact hsf
  · have hb2a : (n.natAbs : ℤ) = (b : ℤ) ^ 2 * (a : ℤ) := by exact_mod_cast hab.symm
    rw [show n.sign * (a : ℤ) * (b : ℤ) ^ 2 = n.sign * ((b : ℤ) ^ 2 * (a : ℤ)) by ring, ← hb2a]
    exact (Int.sign_mul_natAbs n).symm

/-- **Squarefree representative of a rational square class.** Every nonzero rational equals a *squarefree*
integer times a rational square: `q = s · t²` with `s` squarefree, `s ≠ 0`, `t ≠ 0`. (`q.num·q.den = s·c²`
by `exists_squarefree_sq_mul_int`, so `q = (s·c²)/q.den² = s·(c/q.den)²`.) This is the diagonal-coefficient
normalization that opens Legendre's theorem / the ternary Hasse–Minkowski descent: combined with
`exists_diag_isotropic_congr_sq` it reduces a diagonal form over ℚ to one with squarefree integer
coefficients. -/
theorem exists_squarefree_sq_mul_rat {q : ℚ} (hq : q ≠ 0) :
    ∃ (s : ℤ) (t : ℚ), s ≠ 0 ∧ t ≠ 0 ∧ Squarefree s ∧ q = (s : ℚ) * t ^ 2 := by
  have hnum : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have hdenℤ : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_nz
  have hdenℚ : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  obtain ⟨s, c, hs0, hc0, hsf, hsc⟩ := exists_squarefree_sq_mul_int (mul_ne_zero hnum hdenℤ)
  refine ⟨s, (c : ℚ) / (q.den : ℚ), hs0, div_ne_zero (by exact_mod_cast hc0) hdenℚ, hsf, ?_⟩
  have hqd : (q.num : ℚ) = q * (q.den : ℚ) := (div_eq_iff hdenℚ).mp (Rat.num_div_den q)
  have e1 : (q.num : ℚ) * (q.den : ℚ) = (s : ℚ) * (c : ℚ) ^ 2 := by exact_mod_cast hsc
  have key : q * (q.den : ℚ) ^ 2 = (s : ℚ) * (c : ℚ) ^ 2 := by
    calc q * (q.den : ℚ) ^ 2 = q * (q.den : ℚ) * (q.den : ℚ) := by ring
      _ = (q.num : ℚ) * (q.den : ℚ) := by rw [← hqd]
      _ = (s : ℚ) * (c : ℚ) ^ 2 := e1
  rw [div_pow, ← mul_div_assoc, ← key, mul_div_assoc, div_self (pow_ne_zero 2 hdenℚ), mul_one]

/-- **Norm-form composition identity in `R[√a]` (the engine of Legendre descent).** The pure ring identity
`(z² − a x²)(t² − a) = (z·t + a·x)² − a·(z + t·x)²` — i.e. `N(α)·N(β) = N(αβ)` for `α = z + x√a`,
`β = t + √a` with norm `N(u + v√a) = u² − a v²`. This is the algebraic heart of the ternary descent. -/
theorem norm_form_comp_identity {R : Type*} [CommRing R] (a t x z : R) :
    (z ^ 2 - a * x ^ 2) * (t ^ 2 - a) = (z * t + a * x) ^ 2 - a * (z + t * x) ^ 2 := by ring

/-- **Solvability transfer down to a smaller coefficient (Legendre descent step).** If `t² − a = b·b''`
and `z² = a x² + b'' y²` has a solution with `y ≠ 0`, then `Z² = a X² + b Y²` has one with `Y ≠ 0`, namely
`(X,Y,Z) = (z + t x, b''·y, z t + a x)`. (Multiply `z² − a x² = b'' y²` by `t² − a = b·b''` and apply
`norm_form_comp_identity`: the left side becomes `b·(b'' y)²`.) This moves a canonical ternary
`z² = a x² + b y²` to the smaller coefficient `b''`, the inductive engine of Legendre's theorem. -/
theorem solvable_transfer {a b b'' t : ℤ} (hb'' : b'' ≠ 0) (hfac : t ^ 2 - a = b * b'')
    {x y z : ℤ} (hy : y ≠ 0) (hsol : z ^ 2 = a * x ^ 2 + b'' * y ^ 2) :
    ∃ X Y Z : ℤ, Y ≠ 0 ∧ Z ^ 2 = a * X ^ 2 + b * Y ^ 2 := by
  refine ⟨z + t * x, b'' * y, z * t + a * x, mul_ne_zero hb'' hy, ?_⟩
  have e1 : z ^ 2 - a * x ^ 2 = b'' * y ^ 2 := by linarith [hsol]
  calc (z * t + a * x) ^ 2
      = a * (z + t * x) ^ 2 + (z ^ 2 - a * x ^ 2) * (t ^ 2 - a) := by ring
    _ = a * (z + t * x) ^ 2 + b'' * y ^ 2 * (b * b'') := by rw [e1, hfac]
    _ = a * (z + t * x) ^ 2 + b * (b'' * y) ^ 2 := by ring

/-- **Descent construction step (size reduction).** If `a` is not a perfect square, `|b| ≥ 2`,
`|a| ≤ |b|`, and `a` is a square mod `b` (`∃ t₀, b ∣ t₀² − a`), then choosing the *balanced* residue
`t = t₀.bmod |b|` (so `|t| ≤ |b|/2`) yields `b'' ≠ 0` with `t² − a = b·b''` and `|b''| < |b|`. (Balanced
residue gives `4t² ≤ b²`, so `|t² − a| ≤ b²/4 + |b| < b²`, forcing `|b''| < |b|`.) The size-reducing half
of Legendre's descent: it feeds `solvable_transfer` to move the canonical ternary to a strictly smaller
coefficient. -/
theorem descent_construct {a b : ℤ} (ha : ¬ IsSquare a) (hb2 : 2 ≤ b.natAbs)
    (hab : a.natAbs ≤ b.natAbs) (hQR : ∃ t : ℤ, b ∣ (t ^ 2 - a)) :
    ∃ (t b'' : ℤ), b'' ≠ 0 ∧ t ^ 2 - a = b * b'' ∧ b''.natAbs < b.natAbs := by
  obtain ⟨t₀, ht₀⟩ := hQR
  set m := b.natAbs with hm
  have hbpos : 0 < m := by omega
  set t := t₀.bmod m with ht
  have hmod : t ≡ t₀ [ZMOD (m : ℤ)] := Int.bmod_emod
  have hbdvd : b ∣ (t - t₀) := by
    have hmdvd : (m : ℤ) ∣ (t - t₀) := (Int.modEq_iff_dvd.mp hmod.symm)
    rwa [hm, Int.natAbs_dvd] at hmdvd
  have hcong : b ∣ (t ^ 2 - a) := by
    have h1 : b ∣ (t ^ 2 - t₀ ^ 2) := by
      have he : t ^ 2 - t₀ ^ 2 = (t - t₀) * (t + t₀) := by ring
      rw [he]; exact hbdvd.mul_right _
    have hsum := dvd_add h1 ht₀
    have he2 : (t ^ 2 - t₀ ^ 2) + (t₀ ^ 2 - a) = t ^ 2 - a := by ring
    rwa [he2] at hsum
  obtain ⟨b'', hb''⟩ := hcong
  -- balanced bounds: 4 t² ≤ m²
  have h_lo := Int.le_bmod (x := t₀) hbpos
  have h_hi := Int.bmod_lt (x := t₀) hbpos
  have ht2 : -(m : ℤ) ≤ 2 * t ∧ 2 * t ≤ (m : ℤ) := by rw [← ht] at h_lo h_hi; omega
  have h4t : 4 * t ^ 2 ≤ (m : ℤ) ^ 2 := by nlinarith [ht2.1, ht2.2]
  -- |a| ≤ m as integer bounds
  have ha_le : |a| ≤ (m : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hab
  have ha_bd := abs_le.mp ha_le
  refine ⟨t, b'', ?_, hb'', ?_⟩
  · intro h0
    rw [h0, mul_zero] at hb''
    exact ha ⟨t, by linarith [hb'', sq t]⟩
  · -- |b''| < |b| via |t² - a| < m²
    have hsize : |t ^ 2 - a| < (m : ℤ) ^ 2 := by
      rw [abs_lt]
      constructor
      · nlinarith [sq_nonneg t, ha_bd.2, hb2]
      · nlinarith [h4t, ha_bd.1, hb2]
    have hprod : (m : ℤ) * (b''.natAbs : ℤ) = |t ^ 2 - a| := by
      rw [hb'', abs_mul, Int.abs_eq_natAbs b, ← hm, Int.abs_eq_natAbs b'']
    have : (m : ℤ) * (b''.natAbs : ℤ) < (m : ℤ) * (m : ℤ) := by
      rw [hprod]; calc |t ^ 2 - a| < (m : ℤ) ^ 2 := hsize
        _ = (m : ℤ) * (m : ℤ) := by ring
    have hlt : (b''.natAbs : ℤ) < (m : ℤ) := lt_of_mul_lt_mul_left this (by positivity)
    exact_mod_cast hlt

/-- **Square-factor scaling of the coefficient.** If `z² = a x² + b' y²` has a solution with `y ≠ 0`, then
`z² = a x² + (b'·w²) y²` does too (scale `(x,z)` by `w`: `(wz)² = a(wx)² + b'·w²·y²`). With `b'' = b'·w²`
(the squarefree decomposition of `b''`) this lifts a solution at the squarefree part `b'` back up to `b''`,
the middle link of the descent chain `b' → b'' → b`. -/
theorem solvable_scale {a b' w : ℤ} {x y z : ℤ} (hy : y ≠ 0)
    (hsol : z ^ 2 = a * x ^ 2 + b' * y ^ 2) :
    ∃ X Y Z : ℤ, Y ≠ 0 ∧ Z ^ 2 = a * X ^ 2 + (b' * w ^ 2) * Y ^ 2 := by
  exact ⟨w * x, y, w * z, hy, by linear_combination w ^ 2 * hsol⟩

/-- **Field-generic solvability transfer (local-preservation engine).** Over any field, if `t² − a = b·b''`
and `z² = a x² + b'' y²` has a solution with `y ≠ 0`, then `z² = a x² + b y²` does. Same witnesses as
`solvable_transfer`, but over a field (e.g. `ℚ_[p]`, `ℝ`) — used to preserve *local* solvability across the
descent `b → b''` (and, by `b ↔ b''` symmetry of the factorization, `b'' → b`). -/
theorem solvable_transfer_field {K : Type*} [Field K] {a b b'' t : K} (hb'' : b'' ≠ 0)
    (hfac : t ^ 2 - a = b * b'') {x y z : K} (hy : y ≠ 0) (hsol : z ^ 2 = a * x ^ 2 + b'' * y ^ 2) :
    ∃ X Y Z : K, Y ≠ 0 ∧ Z ^ 2 = a * X ^ 2 + b * Y ^ 2 :=
  ⟨z + t * x, b'' * y, z * t + a * x, mul_ne_zero hb'' hy, by
    linear_combination (t ^ 2 - a) * hsol + b'' * y ^ 2 * hfac⟩

/-- **Field-generic square-factor scaling (local-preservation engine).** Over any field, `z² = a x² + b' y²`
solvable (`y ≠ 0`) ⟹ `z² = a x² + (b'·w²) y²` solvable (`y ≠ 0`). The field analogue of `solvable_scale`,
for transporting local solvability between a coefficient and its square multiples. -/
theorem solvable_scale_field {K : Type*} [Field K] {a b' w : K} {x y z : K} (hy : y ≠ 0)
    (hsol : z ^ 2 = a * x ^ 2 + b' * y ^ 2) :
    ∃ X Y Z : K, Y ≠ 0 ∧ Z ^ 2 = a * X ^ 2 + (b' * w ^ 2) * Y ^ 2 :=
  ⟨w * x, y, w * z, hy, by linear_combination w ^ 2 * hsol⟩

/-- **One descent step preserves local solvability (field-generic).** Over any field, if `t² − a = b·(b'·w²)`
(the descent factorization, `b'' = b'·w²` the squarefree part of `b''`), `b ≠ 0`, `w ≠ 0`, and
`z² = a x² + b y²` has a solution with `y ≠ 0`, then `z² = a x² + b' y²` does. (Transfer `b → b'·w²` via
`solvable_transfer_field`, then read off `b'` with `Y = w·Y₁`.) Applied at each place `ℚ_v`, this is exactly
the invariant preservation of the Legendre/Hasse–Minkowski descent — coprimality-free, no Hilbert symbols. -/
theorem solvable_descent_field {K : Type*} [Field K] {a b b' w t : K}
    (hb : b ≠ 0) (hw : w ≠ 0) (hfac : t ^ 2 - a = b * (b' * w ^ 2))
    {x y z : K} (hy : y ≠ 0) (hsol : z ^ 2 = a * x ^ 2 + b * y ^ 2) :
    ∃ X Y Z : K, Y ≠ 0 ∧ Z ^ 2 = a * X ^ 2 + b' * Y ^ 2 := by
  obtain ⟨X1, Y1, Z1, hY1, hsol1⟩ :=
    solvable_transfer_field (b := b' * w ^ 2) (b'' := b) hb (by rw [hfac]; ring) hy hsol
  exact ⟨X1, w * Y1, Z1, mul_ne_zero hw hY1, by rw [hsol1]; ring⟩

/-- **Diagonal form normalization to squarefree integer coefficients.** Any diagonal form `∑ wᵢ xᵢ²` over ℚ
with all `wᵢ ≠ 0` is isotropic iff the form `∑ sᵢ xᵢ²` with *squarefree integer* coefficients `sᵢ` is, where
`wᵢ = sᵢ·tᵢ²` (`exists_squarefree_sq_mul_rat`) and the equivalence is the square-class invariance
`exists_diag_isotropic_congr_sq` (scale `xᵢ` by `1/tᵢ`). The normalization opening Legendre's theorem /
ternary Hasse–Minkowski for the diagonalized integer Gram form. -/
theorem exists_squarefree_diag_isotropic {ι : Type*} [Fintype ι] (w : ι → ℚ) (hw : ∀ i, w i ≠ 0) :
    ∃ s : ι → ℤ, (∀ i, Squarefree (s i)) ∧ (∀ i, s i ≠ 0) ∧
      ((∃ x : ι → ℚ, x ≠ 0 ∧ ∑ i, w i * x i ^ 2 = 0) ↔
       (∃ x : ι → ℚ, x ≠ 0 ∧ ∑ i, (s i : ℚ) * x i ^ 2 = 0)) := by
  choose s t hs0 ht0 hsf hwst using fun i => exists_squarefree_sq_mul_rat (hw i)
  refine ⟨s, hsf, hs0, ?_⟩
  have hc : ∀ i, (1 / t i : ℚ) ≠ 0 := fun i => one_div_ne_zero (ht0 i)
  have heq : ∀ i, w i * (1 / t i) ^ 2 = (s i : ℚ) := by
    intro i
    have htt : t i ^ 2 * (1 / t i) ^ 2 = 1 := by
      rw [div_pow, one_pow, mul_one_div, div_self (pow_ne_zero 2 (ht0 i))]
    rw [hwst i, mul_assoc, htt, mul_one]
  rw [exists_diag_isotropic_congr_sq w (fun i => 1 / t i) hc]
  simp_rw [heq]

/-- **`t² − a` is always a norm value (the descent invariant's source).** The canonical ternary
`z² = a x² + (t² − a) y²` is *unconditionally* solvable with `y ≠ 0`: `(x,y,z) = (1,1,t)`. (This is why the
descent preserves local solvability: `t² − a = b·b''`, so at every place `(a,b)_v·(a,b'')_v = (a,t²−a)_v = 1`.) -/
theorem solvable_norm_value (a t : ℤ) :
    ∃ x y z : ℤ, y ≠ 0 ∧ z ^ 2 = a * x ^ 2 + (t ^ 2 - a) * y ^ 2 :=
  ⟨1, 1, t, one_ne_zero, by ring⟩

/-- **Symmetry of the canonical ternary in its two coefficients** (over any commutative ring). `z² = a x² +
b y²` solvable ⟹ `z² = b x² + a y²` solvable (swap `x ↔ y`). Lets the Legendre/Hasse–Minkowski descent
assume `|a| ≤ |b|` without loss, over ℤ, ℚ, and each ℚ_v. -/
theorem solvable_canonical_symm {R : Type*} [CommRing R] {a b : R}
    (h : ∃ x y z : R, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2) :
    ∃ x y z : R, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ z ^ 2 = b * x ^ 2 + a * y ^ 2 := by
  obtain ⟨x, y, z, hnz, he⟩ := h
  exact ⟨y, x, z, fun hc => hnz ⟨hc.2.1, hc.1, hc.2.2⟩, by linear_combination he⟩

/-- **Nontrivial solution ⟹ solution with `y ≠ 0`, when `a` is not a square (over a field).** If `a` is not
a square in `K` and `z² = a x² + b y²` has a nontrivial solution, then it has one with `y ≠ 0`. (A solution
with `y = 0` forces `z² = a x²`; `x ≠ 0` would make `a = (z/x)²` a square, and `x = 0` makes it trivial.)
Converts the "nontrivial" local-solvability hypothesis into the `y ≠ 0` shape the field transfer lemmas need,
at places where `a` is a non-square. -/
theorem exists_y_ne_zero_of_not_isSquare {K : Type*} [Field K] {a b : K} (ha : ¬ IsSquare a)
    {x y z : K} (hnz : ¬(x = 0 ∧ y = 0 ∧ z = 0)) (he : z ^ 2 = a * x ^ 2 + b * y ^ 2) :
    ∃ X Y Z : K, Y ≠ 0 ∧ Z ^ 2 = a * X ^ 2 + b * Y ^ 2 := by
  by_cases hy : y = 0
  · exfalso
    subst hy
    have he' : z ^ 2 = a * x ^ 2 := by rw [he]; ring
    by_cases hx : x = 0
    · subst hx
      have hz : z ^ 2 = 0 := by rw [he']; ring
      exact hnz ⟨rfl, rfl, pow_eq_zero_iff (by norm_num) |>.mp hz⟩
    · exact ha ⟨z / x, by field_simp; linear_combination -he'⟩
  · exact ⟨x, y, z, hy, he⟩

/-- **One descent step preserves nontrivial local solvability at every place (field-generic).** Over any
field, given the descent factorization `t² − a = b·(b'·w²)` (`b ≠ 0`, `w ≠ 0`), a nontrivial solution of
`z² = a x² + b y²` yields a nontrivial solution of `z² = a x² + b' y²`. (If `a` is a square in `K`, the
target is solvable directly by `(1, 0, √a)`; otherwise convert to a `y ≠ 0` solution
[`exists_y_ne_zero_of_not_isSquare`] and apply `solvable_descent_field`.) This is exactly the invariant
preservation of the Hasse–Minkowski descent at each place `ℝ`, `ℚ_p` — uniform, coprimality-free. -/
theorem solvable_descent_or_isSquare_field {K : Type*} [Field K] {a b b' w t : K}
    (hb : b ≠ 0) (hw : w ≠ 0) (hfac : t ^ 2 - a = b * (b' * w ^ 2))
    (h : ∃ x y z : K, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2) :
    ∃ x y z : K, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ z ^ 2 = a * x ^ 2 + b' * y ^ 2 := by
  by_cases ha : IsSquare a
  · obtain ⟨r, hr⟩ := ha
    exact ⟨1, 0, r, fun hc => one_ne_zero hc.1, by rw [hr]; ring⟩
  · obtain ⟨x, y, z, hnz, hsol⟩ := h
    obtain ⟨X, Y, Z, hY, hsol'⟩ := exists_y_ne_zero_of_not_isSquare ha hnz hsol
    obtain ⟨X', Y', Z', hY', hsol''⟩ := solvable_descent_field hb hw hfac hY hsol'
    exact ⟨X', Y', Z', fun hc => hY' hc.2.1, hsol''⟩

/-- **Odd-`p` per-place bridge from global integers to the residue square condition.** For an odd prime `p`
and integers `a, c` with `p ∤ a`, `p ∤ c`, the canonical ternary `z² = a x² + (p·c) y²` over `ℚ_[p]` is
solvable iff `a` is a square mod `p`. (Cast `a, c` to `ℤ_[p]` units via `norm_intCast_eq_one_iff`, match the
`(u, p·v)` shape of `solvable_unit_pUnit_iff`, and identify `toZMod ↑a = (a : ZMod p)`.) This connects a
*global* squarefree coefficient `b = p·c` (exact `p`-valuation 1) to the elementary congruence "`a` QR mod
`p`" that drives the Legendre descent / Hasse–Minkowski local conditions. -/
theorem solvable_padic_odd_iff_residue {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a c : ℤ}
    (ha : ¬ (p : ℤ) ∣ a) (hc : ¬ (p : ℤ) ∣ c) :
    (∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = (a : ℚ_[p]) * x ^ 2 + (p : ℚ_[p]) * (c : ℚ_[p]) * y ^ 2) ↔ IsSquare ((a : ZMod p)) := by
  have hpp : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp Fact.out
  have hcop_a : IsCoprime (a : ℤ) (p : ℤ) := (hpp.coprime_iff_not_dvd.mpr ha).symm
  have hcop_c : IsCoprime (c : ℤ) (p : ℤ) := (hpp.coprime_iff_not_dvd.mpr hc).symm
  have hua : IsUnit ((a : ℤ_[p])) := PadicInt.isUnit_iff.mpr (PadicInt.norm_intCast_eq_one_iff.mpr hcop_a)
  have huc : IsUnit ((c : ℤ_[p])) := PadicInt.isUnit_iff.mpr (PadicInt.norm_intCast_eq_one_iff.mpr hcop_c)
  have hres : PadicInt.toZMod ((a : ℤ_[p])) = (a : ZMod p) := map_intCast _ a
  rw [← hres]
  have key := solvable_unit_pUnit_iff hp hua huc
  rw [PadicInt.coe_intCast, PadicInt.coe_intCast] at key
  exact key

/-- **`a` a square mod `|b|` ⟹ the divisibility `descent_construct` consumes.** If `a` is a square in
`ZMod |b|` then `∃ t, b ∣ t² − a` (lift the square root `s = ↑t` and reduce `t² − a ≡ 0`). The interface
turning the residue/CRT square condition into the input of the Legendre descent step. -/
theorem exists_dvd_sq_sub_of_isSquare_zmod {a b : ℤ} (h : IsSquare ((a : ZMod b.natAbs))) :
    ∃ t : ℤ, b ∣ (t ^ 2 - a) := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨t, rfl⟩ := ZMod.intCast_surjective s
  refine ⟨t, ?_⟩
  rw [← Int.natAbs_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [hs]; ring

/-- **Real-place bridge for the canonical ternary.** For nonzero integers `a, b`, the form
`z² = a x² + b y²` is solvable over ℝ iff `a, b` are not both negative. (Immediate from
`HilbertSymbolReal.hilbertReal_eq_one_iff` and `hilbertReal = -1 ⟺ both negative`.) The archimedean local
condition of Hasse–Minkowski for the canonical ternary. -/
theorem solvable_real_canonical_iff {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (∃ x y z : ℝ, (x, y, z) ≠ 0 ∧ z ^ 2 = (a : ℝ) * x ^ 2 + (b : ℝ) * y ^ 2) ↔ ¬ (a < 0 ∧ b < 0) := by
  have har : (a : ℝ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hbr : (b : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb
  rw [← HilbertSymbol.hilbertReal_eq_one_iff har hbr, HilbertSymbol.hilbertReal]
  have hcast : ((a : ℝ) < 0 ∧ (b : ℝ) < 0) ↔ (a < 0 ∧ b < 0) := by
    rw [Int.cast_lt_zero, Int.cast_lt_zero]
  split_ifs with h
  · exact iff_of_false (by decide) (not_not.mpr (hcast.mp h))
  · exact iff_of_true rfl (hcast.not.mp h)

/-- **`IsSquare` in a product is componentwise.** `IsSquare p ↔ IsSquare p.1 ∧ IsSquare p.2`. A CRT helper:
under `ZMod.chineseRemainder` a residue is a square iff it is a square in each coprime factor. -/
theorem isSquare_prod_iff {M N : Type*} [Monoid M] [Monoid N] {p : M × N} :
    IsSquare p ↔ IsSquare p.1 ∧ IsSquare p.2 := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨⟨s.1, by rw [hs]; rfl⟩, ⟨s.2, by rw [hs]; rfl⟩⟩
  · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    exact ⟨(s, t), Prod.ext hs ht⟩

/-- **`IsSquare` transfers across a multiplicative equivalence.** For `e : A ≃* B`,
`IsSquare (e x) ↔ IsSquare x`. A CRT helper: `ZMod.chineseRemainder` is a `RingEquiv`, so squareness of a
residue is preserved under the CRT isomorphism. -/
theorem isSquare_mulEquiv {A B : Type*} [Monoid A] [Monoid B] (e : A ≃* B) {x : A} :
    IsSquare (e x) ↔ IsSquare x := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨e.symm s, e.injective (by rw [map_mul, e.apply_symm_apply, hs])⟩
  · rintro ⟨s, hs⟩
    exact ⟨e s, by rw [hs, map_mul]⟩

/-- **CRT bridge: square mod each prime ⟹ square mod the squarefree product.** For squarefree `m`, if `a` is
a square mod every prime `p ∣ m`, then `a` is a square mod `m`. (Strong induction: split off a prime `p`,
`m = p·k` with `p, k` coprime, transport `IsSquare` across `ZMod.chineseRemainder` and `isSquare_prod_iff`.)
Combines the per-prime local conditions into the global "`a` square mod `|b|`" that drives the descent. -/
theorem isSquare_zmod_of_forall_prime {a : ℤ} : ∀ {m : ℕ}, Squarefree m →
    (∀ p : ℕ, p.Prime → p ∣ m → IsSquare ((a : ZMod p))) → IsSquare ((a : ZMod m)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro hm h
    rcases eq_or_ne m 1 with rfl | hm1
    · exact ⟨0, Subsingleton.elim _ _⟩
    · obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
      set k := m / p with hkdef
      have hk : p * k = m := Nat.mul_div_cancel' hpm
      have hkm : k ∣ m := ⟨p, by rw [← hk, Nat.mul_comm]⟩
      have hpos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
      have hklt : k < m := by rw [hkdef]; exact Nat.div_lt_self hpos hp.one_lt
      have hpk : ¬ p ∣ k := by
        intro hdvd
        obtain ⟨c, hc⟩ := hdvd
        have hpp : p * p ∣ m := ⟨c, by rw [← hk, hc]; ring⟩
        have := hm p hpp
        rw [Nat.isUnit_iff] at this
        have := hp.one_lt
        omega
      have hcop : Nat.Coprime p k := hp.coprime_iff_not_dvd.mpr hpk
      have hksf : Squarefree k := hm.squarefree_of_dvd hkm
      set e : ZMod (p * k) ≃* ZMod p × ZMod k := (ZMod.chineseRemainder hcop).toMulEquiv with he
      have hca : e (a : ZMod (p * k)) = ((a : ZMod p), (a : ZMod k)) := by
        show (ZMod.chineseRemainder hcop) (a : ZMod (p * k)) = _
        rw [map_intCast]; rfl
      rw [← hk, ← isSquare_mulEquiv e, hca, isSquare_prod_iff]
      exact ⟨h p hp hpm, IH k hklt hksf fun q hq hqk => h q hq (hqk.trans hkm)⟩

/-- **Everything is a square mod 2.** `ZMod 2 = {0, 1}` and `0 = 0²`, `1 = 1²`. So the `p = 2` factor of the
CRT square condition is automatic — no `2`-adic solvability bridge is needed for the descent. -/
theorem isSquare_zmod_two : ∀ x : ZMod 2, IsSquare x := by decide

/-- **"`a` square mod `b`" from the odd-prime residue conditions.** For `b` squarefree, if `a` is a square
mod every odd prime `p ∣ b` with `p ∤ a`, then `∃ t, b ∣ t² − a`. (At `p = 2` and at odd `p ∣ a` the residue
square is automatic — `isSquare_zmod_two`, resp. `a ≡ 0`; the CRT `isSquare_zmod_of_forall_prime` assembles
`a` square mod `|b|`, then `exists_dvd_sq_sub_of_isSquare_zmod`.) This is the input `descent_construct`
consumes, derived from the local solvability of `z² = a x² + b y²` (via `solvable_padic_odd_iff_residue`). -/
theorem exists_dvd_sq_sub_of_odd_residue {a b : ℤ} (hb : Squarefree b.natAbs)
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℤ) ∣ b → ¬ (p : ℤ) ∣ a → IsSquare ((a : ZMod p))) :
    ∃ t : ℤ, b ∣ (t ^ 2 - a) := by
  apply exists_dvd_sq_sub_of_isSquare_zmod
  apply isSquare_zmod_of_forall_prime hb
  intro p hp hpb
  have hpbz : (p : ℤ) ∣ b := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hpb)
  rcases eq_or_ne p 2 with rfl | hp2
  · exact isSquare_zmod_two _
  · rcases em ((p : ℤ) ∣ a) with hpa | hpa
    · exact ⟨0, by rw [(ZMod.intCast_zmod_eq_zero_iff_dvd a p).mpr hpa]; ring⟩
    · exact h p hp hp2 hpbz hpa

/-- **Local solvability at an odd prime ⟹ residue square (squarefree coefficient).** For `b` squarefree
with odd prime `p ∣ b` and `p ∤ a`, if `z² = a x² + b y²` is solvable over `ℚ_[p]` then `a` is a square mod
`p`. (Write `b = p·c` with `p ∤ c` from squarefreeness, match the `(u, p·v)` shape of
`solvable_padic_odd_iff_residue`.) The per-prime input to `exists_dvd_sq_sub_of_odd_residue` inside the
descent recursion. -/
theorem isSquare_residue_of_solvable_padic {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a b : ℤ}
    (hsf : Squarefree b.natAbs) (hpa : ¬ (p : ℤ) ∣ a) (hpb : (p : ℤ) ∣ b)
    (hsol : ∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2) :
    IsSquare ((a : ZMod p)) := by
  obtain ⟨c, hc⟩ := hpb
  have hpc : ¬ (p : ℤ) ∣ c := by
    rintro ⟨d, hd⟩
    have hb2 : b = (p : ℤ) * (p : ℤ) * d := by rw [hc, hd]; ring
    have hdvd : (p * p : ℕ) ∣ b.natAbs := by
      refine ⟨d.natAbs, ?_⟩
      rw [hb2]; simp [Int.natAbs_mul, Int.natAbs_natCast, Nat.mul_assoc]
    have := hsf p (by exact_mod_cast hdvd)
    rw [Nat.isUnit_iff] at this
    exact (Fact.out : p.Prime).one_lt.ne' this
  have hcoeff : (b : ℚ_[p]) = (p : ℚ_[p]) * (c : ℚ_[p]) := by rw [hc]; push_cast; ring
  rw [hcoeff] at hsol
  exact (solvable_padic_odd_iff_residue hp hpa hpc).mp hsol

/-- **`∃ t, b ∣ t² − a` from local solvability at the odd primes (squarefree `b`).** Composes
`isSquare_residue_of_solvable_padic` (per odd prime) with `exists_dvd_sq_sub_of_odd_residue` (CRT). This is
the exact input `descent_construct` requires, derived from the descent's local-solvability invariant. -/
theorem exists_dvd_sq_sub_of_locally_solvable {a b : ℤ} (hsf : Squarefree b.natAbs)
    (hloc : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → (p : ℤ) ∣ b → ¬ (p : ℤ) ∣ a →
      ∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
        z ^ 2 = (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2) :
    ∃ t : ℤ, b ∣ (t ^ 2 - a) := by
  apply exists_dvd_sq_sub_of_odd_residue hsf
  intro p hp hp2 hpb hpa
  haveI : Fact p.Prime := ⟨hp⟩
  exact isSquare_residue_of_solvable_padic hp2 hsf hpa hpb (hloc p hp2 hpb hpa)

/-- **Base case of the ternary descent: a square coefficient ⟹ ℚ-solvable.** If `a` or `b` is a perfect
square (integer) then `z² = a x² + b y²` has a nontrivial rational solution (`(1,0,√a)` resp. `(0,1,√b)`).
The terminating case of the Legendre/Hasse–Minkowski descent over ℚ. -/
theorem ratSol_of_isSquare {a b : ℤ} (h : IsSquare a ∨ IsSquare b) :
    ∃ x y z : ℚ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ z ^ 2 = (a : ℚ) * x ^ 2 + (b : ℚ) * y ^ 2 := by
  rcases h with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact ⟨1, 0, (r : ℚ), fun hc => one_ne_zero hc.1, by
      rw [show (a : ℚ) = (r : ℚ) * (r : ℚ) by exact_mod_cast hr]; ring⟩
  · exact ⟨0, 1, (r : ℚ), fun hc => one_ne_zero hc.2.1, by
      rw [show (b : ℚ) = (r : ℚ) * (r : ℚ) by exact_mod_cast hr]; ring⟩

/-- **Ternary Hasse–Minkowski (canonical form, Legendre's theorem).** For nonzero squarefree integers `a, b`,
if `z² = a x² + b y²` has a nontrivial solution over `ℝ` and over every `ℚ_[p]`, then it has one over `ℚ`.
Proof by infinite descent (Legendre): strong induction on `|a| + |b|`; the base case is a square coefficient
(`ratSol_of_isSquare`); the step extracts "`a` square mod `b`" from local solvability
(`exists_dvd_sq_sub_of_locally_solvable`), reduces the larger coefficient (`descent_construct` +
`exists_squarefree_sq_mul_int`), preserves local solvability at every place
(`solvable_descent_or_isSquare_field`), recurses, and lifts the rational solution back
(`solvable_scale_field` + `solvable_transfer_field`). Coprimality-free; no Dirichlet, no Hilbert symbols. -/
theorem ternary_solvable_of_local {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hasf : Squarefree a.natAbs) (hbsf : Squarefree b.natAbs)
    (hR : ∃ x y z : ℝ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ z ^ 2 = (a : ℝ) * x ^ 2 + (b : ℝ) * y ^ 2)
    (hloc : ∀ (p : ℕ) [Fact p.Prime], ∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2) :
    ∃ x y z : ℚ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ z ^ 2 = (a : ℚ) * x ^ 2 + (b : ℚ) * y ^ 2 := by
  suffices H : ∀ n : ℕ, ∀ a b : ℤ, a.natAbs + b.natAbs ≤ n → a ≠ 0 → b ≠ 0 →
      Squarefree a.natAbs → Squarefree b.natAbs →
      (∃ x y z : ℝ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ z ^ 2 = (a : ℝ) * x ^ 2 + (b : ℝ) * y ^ 2) →
      (∀ (p : ℕ) [Fact p.Prime], ∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
        z ^ 2 = (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2) →
      ∃ x y z : ℚ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ z ^ 2 = (a : ℚ) * x ^ 2 + (b : ℚ) * y ^ 2 by
    exact H _ a b le_rfl ha hb hasf hbsf hR hloc
  intro n
  induction n with
  | zero =>
    intro a b hle ha _ _ _ _ _
    exact absurd (Int.natAbs_eq_zero.mp (by omega)) ha
  | succ n IH =>
    -- ordered descent: assume a.natAbs ≤ b.natAbs
    have step : ∀ a b : ℤ, a.natAbs + b.natAbs ≤ n + 1 → a.natAbs ≤ b.natAbs → a ≠ 0 → b ≠ 0 →
        Squarefree a.natAbs → Squarefree b.natAbs →
        (∃ x y z : ℝ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ z ^ 2 = (a : ℝ) * x ^ 2 + (b : ℝ) * y ^ 2) →
        (∀ (p : ℕ) [Fact p.Prime], ∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
          z ^ 2 = (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2) →
        ∃ x y z : ℚ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ z ^ 2 = (a : ℚ) * x ^ 2 + (b : ℚ) * y ^ 2 := by
      intro a b hle hab ha hb hasf hbsf hR hloc
      by_cases hsq : IsSquare a ∨ IsSquare b
      · exact ratSol_of_isSquare hsq
      · rw [not_or] at hsq
        obtain ⟨hnsa, hnsb⟩ := hsq
        have hreal : ¬(a < 0 ∧ b < 0) := by
          rw [← solvable_real_canonical_iff ha hb]
          obtain ⟨x, y, z, hnz, he⟩ := hR
          exact ⟨x, y, z, fun h => hnz (by rw [Prod.mk_eq_zero, Prod.mk_eq_zero] at h; exact h), he⟩
        have hb2 : 2 ≤ b.natAbs := by
          by_contra hc
          rw [not_le] at hc
          have hb1 : b.natAbs = 1 := by
            have := Int.natAbs_pos.mpr hb; omega
          rcases Int.natAbs_eq_iff.mp hb1 with hbv | hbv
          · exact hnsb (by rw [hbv]; exact ⟨1, by ring⟩)
          · have ha1 : a.natAbs = 1 := by
              have := Int.natAbs_pos.mpr ha; omega
            rcases Int.natAbs_eq_iff.mp ha1 with hav | hav
            · exact hnsa (by rw [hav]; exact ⟨1, by ring⟩)
            · exact hreal ⟨by rw [hav]; norm_num, by rw [hbv]; norm_num⟩
        have hext : ∃ t : ℤ, b ∣ (t ^ 2 - a) :=
          exists_dvd_sq_sub_of_locally_solvable hbsf (fun p _ _ _ _ => hloc p)
        obtain ⟨t, b'', hb''0, hb''eq, hb''lt⟩ := descent_construct hnsa hb2 hab hext
        obtain ⟨s, c, hs0, hc0, hssf, hsc⟩ := exists_squarefree_sq_mul_int hb''0
        have hfacZ : t ^ 2 - a = b * (s * c ^ 2) := by rw [hb''eq, hsc]
        have hsle : s.natAbs ≤ b''.natAbs :=
          Nat.le_of_dvd (Int.natAbs_pos.mpr hb''0) (Int.natAbs_dvd_natAbs.mpr ⟨c ^ 2, hsc⟩)
        have hmeas : a.natAbs + s.natAbs ≤ n := by omega
        have hsnatsf : Squarefree s.natAbs := Int.squarefree_natAbs.mpr hssf
        have hR' : ∃ x y z : ℝ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
            z ^ 2 = (a : ℝ) * x ^ 2 + (s : ℝ) * y ^ 2 := by
          have hfacR : (t : ℝ) ^ 2 - (a : ℝ) = (b : ℝ) * ((s : ℝ) * (c : ℝ) ^ 2) := by
            exact_mod_cast hfacZ
          exact solvable_descent_or_isSquare_field (Int.cast_ne_zero.mpr hb)
            (Int.cast_ne_zero.mpr hc0) hfacR hR
        have hloc' : ∀ (p : ℕ) [Fact p.Prime], ∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
            z ^ 2 = (a : ℚ_[p]) * x ^ 2 + (s : ℚ_[p]) * y ^ 2 := by
          intro p _
          have hfacp : (t : ℚ_[p]) ^ 2 - (a : ℚ_[p]) = (b : ℚ_[p]) * ((s : ℚ_[p]) * (c : ℚ_[p]) ^ 2) := by
            exact_mod_cast hfacZ
          exact solvable_descent_or_isSquare_field (Int.cast_ne_zero.mpr hb)
            (Int.cast_ne_zero.mpr hc0) hfacp (hloc p)
        have hrat' := IH a s hmeas ha hs0 hasf hsnatsf hR' hloc'
        -- lift back RatSol(a,s) → RatSol(a,b)
        by_cases haq : IsSquare (a : ℚ)
        · obtain ⟨r, hr⟩ := haq
          exact ⟨1, 0, r, fun hc => one_ne_zero hc.1, by rw [hr]; ring⟩
        · obtain ⟨x', y', z', hnz', he'⟩ := hrat'
          obtain ⟨X, Y, Z, hY, heY⟩ := exists_y_ne_zero_of_not_isSquare haq hnz' he'
          obtain ⟨X2, Y2, Z2, hY2, he2⟩ := solvable_scale_field (w := (c : ℚ)) hY heY
          have hb''q : (s : ℚ) * (c : ℚ) ^ 2 ≠ 0 :=
            mul_ne_zero (Int.cast_ne_zero.mpr hs0) (pow_ne_zero 2 (Int.cast_ne_zero.mpr hc0))
          have hfacQ : (t : ℚ) ^ 2 - a = (b : ℚ) * ((s : ℚ) * (c : ℚ) ^ 2) := by exact_mod_cast hfacZ
          obtain ⟨X3, Y3, Z3, hY3, he3⟩ := solvable_transfer_field hb''q hfacQ hY2 he2
          exact ⟨X3, Y3, Z3, fun hc => hY3 hc.2.1, he3⟩
    -- dispatch via le_total
    intro a b hle ha hb hasf hbsf hR hloc
    rcases le_total a.natAbs b.natAbs with hab | hab
    · exact step a b hle hab ha hb hasf hbsf hR hloc
    · have hRs : ∃ x y z : ℝ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
          z ^ 2 = (b : ℝ) * x ^ 2 + (a : ℝ) * y ^ 2 := solvable_canonical_symm hR
      have hlocs : ∀ (p : ℕ) [Fact p.Prime], ∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
          z ^ 2 = (b : ℚ_[p]) * x ^ 2 + (a : ℚ_[p]) * y ^ 2 := fun p => solvable_canonical_symm (hloc p)
      exact solvable_canonical_symm
        (step b a (by omega) hab hb ha hbsf hasf hRs hlocs)

/-- **Homogenization: a binary form represents `c` iff the ternary equation is solvable with `z ≠ 0`.** Over
a field, for `c ≠ 0`, `∃ x y, a x² + b y² = c` iff `∃ x y z, z ≠ 0 ∧ a x² + b y² = c z²` (take `z = 1`
forward; `x/z, y/z` backward). The link between *representation* of a value by a binary form and *isotropy*
of the associated ternary — the algebraic core of the rank-reduction step `n → n−1` of Hasse–Minkowski. -/
theorem represents_iff_homog {K : Type*} [Field K] {a b c : K} :
    (∃ x y : K, a * x ^ 2 + b * y ^ 2 = c) ↔
    (∃ x y z : K, z ≠ 0 ∧ a * x ^ 2 + b * y ^ 2 = c * z ^ 2) := by
  constructor
  · rintro ⟨x, y, h⟩
    exact ⟨x, y, 1, one_ne_zero, by rw [h]; ring⟩
  · rintro ⟨x, y, z, hz, h⟩
    exact ⟨x / z, y / z, by field_simp; linear_combination h⟩

/-- **Ternary Hasse–Minkowski, canonical form with rational coefficients.** Extends
`ternary_solvable_of_local` from squarefree-integer to arbitrary nonzero *rational* coefficients `A, B`:
`z² = A x² + B y²` solvable over ℝ and every ℚ_p ⟹ solvable over ℚ. (Write `A = a'·s²`, `B = b'·u²` with
`a', b'` squarefree integers via `exists_squarefree_sq_mul_rat`, reduce at every place via
`solvable_canonical_of_sq_mul`, apply the integer ternary HM.) The form directly consumable after
`isotropic_diag_ternary_iff_canonical` turns a diagonal ternary into canonical shape. -/
theorem ternary_canonical_solvable_of_local_rat {A B : ℚ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hR : ∃ x y z : ℝ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ z ^ 2 = (A : ℝ) * x ^ 2 + (B : ℝ) * y ^ 2)
    (hloc : ∀ (p : ℕ) [Fact p.Prime], ∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = (A : ℚ_[p]) * x ^ 2 + (B : ℚ_[p]) * y ^ 2) :
    ∃ x y z : ℚ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ z ^ 2 = (A : ℚ) * x ^ 2 + (B : ℚ) * y ^ 2 := by
  obtain ⟨a', s, ha'0, hs0, ha'sf, hAeq⟩ := exists_squarefree_sq_mul_rat hA
  obtain ⟨b', u, hb'0, hu0, hb'sf, hBeq⟩ := exists_squarefree_sq_mul_rat hB
  have hR' : ∃ x y z : ℝ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = ((a' : ℤ) : ℝ) * x ^ 2 + ((b' : ℤ) : ℝ) * y ^ 2 :=
    (solvable_canonical_of_sq_mul (K := ℝ) (s := ((s : ℚ) : ℝ)) (u := ((u : ℚ) : ℝ))
      (by exact_mod_cast hs0) (by exact_mod_cast hu0) (by exact_mod_cast hAeq)
      (by exact_mod_cast hBeq)).mp hR
  have hloc' : ∀ (p : ℕ) [Fact p.Prime], ∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = ((a' : ℤ) : ℚ_[p]) * x ^ 2 + ((b' : ℤ) : ℚ_[p]) * y ^ 2 := by
    intro p _
    exact (solvable_canonical_of_sq_mul (K := ℚ_[p]) (s := ((s : ℚ) : ℚ_[p])) (u := ((u : ℚ) : ℚ_[p]))
      (by exact_mod_cast hs0) (by exact_mod_cast hu0) (by exact_mod_cast hAeq)
      (by exact_mod_cast hBeq)).mp (hloc p)
  have key := ternary_solvable_of_local ha'0 hb'0 (Int.squarefree_natAbs.mpr ha'sf)
    (Int.squarefree_natAbs.mpr hb'sf) hR' hloc'
  exact (solvable_canonical_of_sq_mul (K := ℚ) (s := (s : ℚ)) (u := (u : ℚ))
    hs0 hu0 hAeq hBeq).mpr key

/-- **Ternary Hasse–Minkowski for a diagonal form (rational coefficients).** For nonzero rationals
`a, b, c`, the diagonal ternary `a x² + b y² + c z² = 0` is solvable nontrivially over ℚ iff over ℝ and
every ℚ_p. (Normalize to canonical `z² = (−a/c) x² + (−b/c) y²` at every place via
`isotropic_diag_ternary_iff_canonical`, then `ternary_canonical_solvable_of_local_rat`.) The `n = 3` base
case of the Hasse–Minkowski rank reduction, directly consumable by the matrix→diagonal application. -/
theorem diag_ternary_solvable_of_local {a b c : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hR : ∃ x y z : ℝ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      (a : ℝ) * x ^ 2 + (b : ℝ) * y ^ 2 + (c : ℝ) * z ^ 2 = 0)
    (hloc : ∀ (p : ℕ) [Fact p.Prime], ∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2 + (c : ℚ_[p]) * z ^ 2 = 0) :
    ∃ x y z : ℚ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      (a : ℚ) * x ^ 2 + (b : ℚ) * y ^ 2 + (c : ℚ) * z ^ 2 = 0 := by
  rw [isotropic_diag_ternary_iff_canonical hc]
  have hAne : -a / c ≠ 0 := div_ne_zero (neg_ne_zero.mpr ha) hc
  have hBne : -b / c ≠ 0 := div_ne_zero (neg_ne_zero.mpr hb) hc
  refine ternary_canonical_solvable_of_local_rat hAne hBne ?_ ?_
  · have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
    obtain ⟨x, y, z, hnz, he⟩ := hR
    refine ⟨x, y, z, hnz, ?_⟩
    rw [show ((-a / c : ℚ) : ℝ) = -(a : ℝ) / (c : ℝ) by push_cast; ring,
       show ((-b / c : ℚ) : ℝ) = -(b : ℝ) / (c : ℝ) by push_cast; ring]
    field_simp
    linear_combination he
  · intro p _
    have hcp : (c : ℚ_[p]) ≠ 0 := by exact_mod_cast hc
    obtain ⟨x, y, z, hnz, he⟩ := hloc p
    refine ⟨x, y, z, hnz, ?_⟩
    rw [show ((-a / c : ℚ) : ℚ_[p]) = -(a : ℚ_[p]) / (c : ℚ_[p]) by push_cast; ring,
       show ((-b / c : ℚ) : ℚ_[p]) = -(b : ℚ_[p]) / (c : ℚ_[p]) by push_cast; ring]
    field_simp
    linear_combination he

/-- **Value representation is a local property (binary forms over ℚ).** A binary form `⟨a,b⟩` (`a, b ≠ 0`)
represents a nonzero rational `t` iff it does over ℝ and every ℚ_p. (`⟨a,b⟩` represents `t` ⟺ the ternary
`a x² + b y² + (−t) z² = 0` is isotropic [witness `z = 1`, resp. `represents_of_ternary_isotropic`]; the
ternary local–global is `diag_ternary_solvable_of_local`.) The value-representation engine of the
Hasse–Minkowski rank-reduction step `n → n−1`. -/
theorem binary_represents_of_local {a b t : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0)
    (hR : ∃ u v : ℝ, (a : ℝ) * u ^ 2 + (b : ℝ) * v ^ 2 = t)
    (hloc : ∀ (p : ℕ) [Fact p.Prime], ∃ u v : ℚ_[p], (a : ℚ_[p]) * u ^ 2 + (b : ℚ_[p]) * v ^ 2 = t) :
    ∃ u v : ℚ, (a : ℚ) * u ^ 2 + (b : ℚ) * v ^ 2 = t := by
  haveI : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  have hiso := diag_ternary_solvable_of_local (a := a) (b := b) (c := -t) ha hb
    (neg_ne_zero.mpr ht) ?hR' ?hloc'
  · obtain ⟨x, y, z, hnz, he⟩ := hiso
    exact represents_of_ternary_isotropic ha hb ⟨x, y, z, hnz, by linarith [he]⟩
  case hR' =>
    obtain ⟨u, v, he⟩ := hR
    exact ⟨u, v, 1, by simp, by push_cast; linarith [he]⟩
  case hloc' =>
    intro p _
    obtain ⟨u, v, he⟩ := hloc p
    exact ⟨u, v, 1, by simp, by push_cast; linear_combination he⟩

/-- **Binary Hasse–Minkowski (n = 2 base case).** For `a ≠ 0` (any `b`), the binary form `a x² + b y² = 0`
has a nontrivial zero over ℚ iff over ℝ and every ℚ_p. (`exists_binary_zero_iff` turns isotropy into
`IsSquare (-(a·b))`, and `isSquare_rat_iff_local` is the square local–global.) The `n = 2` base case of the
Hasse–Minkowski rank reduction, parallel to `diag_ternary_solvable_of_local`. -/
theorem binary_solvable_of_local {a b : ℚ} (ha : a ≠ 0)
    (hR : ∃ x y : ℝ, ¬(x = 0 ∧ y = 0) ∧ (a : ℝ) * x ^ 2 + (b : ℝ) * y ^ 2 = 0)
    (hloc : ∀ (p : ℕ) [Fact p.Prime], ∃ x y : ℚ_[p], ¬(x = 0 ∧ y = 0) ∧
      (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2 = 0) :
    ∃ x y : ℚ, ¬(x = 0 ∧ y = 0) ∧ (a : ℚ) * x ^ 2 + (b : ℚ) * y ^ 2 = 0 := by
  rw [exists_binary_zero_iff ha, isSquare_rat_iff_local]
  refine ⟨?_, fun p _ => ?_⟩
  · have har : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    have h := Real.isSquare_iff.mp ((exists_binary_zero_iff har).mp hR)
    have hc : (0 : ℝ) ≤ ((-(a * b) : ℚ) : ℝ) := by push_cast; linarith [h]
    exact_mod_cast hc
  · have hap : (a : ℚ_[p]) ≠ 0 := by exact_mod_cast ha
    have h := (exists_binary_zero_iff hap).mp (hloc p)
    have hcast : ((-(a * b) : ℚ) : ℚ_[p]) = -((a : ℚ_[p]) * (b : ℚ_[p])) := by push_cast; ring
    rw [hcast]; exact h

/-- **Square-discriminant quaternary Hasse–Minkowski (over ℚ).** For nonzero rationals `a, b, c, d` with
`a·b·c·d = s²` (square discriminant), `a x² + b y² − c z² − d w² = 0` is solvable nontrivially over ℚ iff
over ℝ and every ℚ_p. (The square-disc isometry `quaternary_sqdisc_iso_iff_ternary` reduces it — at every
place with the same `s` — to the ternary `z² = −ab x² + ac y²`, closed by
`ternary_canonical_solvable_of_local_rat`.) The first complete n = 4 Hasse–Minkowski case, fully
Dirichlet-free; covers the even-unimodular ranks with square discriminant (e.g. signature (2,2), (4,4)). -/
theorem quaternary_sqdisc_solvable_of_local {a b c d s : ℚ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (hsq : a * b * c * d = s ^ 2)
    (hR : ∃ x y z w : ℝ, ¬(x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) ∧
      (a : ℝ) * x ^ 2 + (b : ℝ) * y ^ 2 - (c : ℝ) * z ^ 2 - (d : ℝ) * w ^ 2 = 0)
    (hloc : ∀ (p : ℕ) [Fact p.Prime], ∃ x y z w : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) ∧
      (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2 - (c : ℚ_[p]) * z ^ 2 - (d : ℚ_[p]) * w ^ 2 = 0) :
    ∃ x y z w : ℚ, ¬(x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) ∧
      (a : ℚ) * x ^ 2 + (b : ℚ) * y ^ 2 - (c : ℚ) * z ^ 2 - (d : ℚ) * w ^ 2 = 0 := by
  rw [quaternary_sqdisc_iso_iff_ternary ha hb hc hd hsq]
  refine ternary_canonical_solvable_of_local_rat (neg_ne_zero.mpr (mul_ne_zero ha hb))
    (mul_ne_zero ha hc) ?_ ?_
  · obtain ⟨x, y, z, hnz, he⟩ := (quaternary_sqdisc_iso_iff_ternary (a := (a : ℝ)) (b := (b : ℝ))
      (c := (c : ℝ)) (d := (d : ℝ)) (s := (s : ℝ)) (by exact_mod_cast ha) (by exact_mod_cast hb)
      (by exact_mod_cast hc) (by exact_mod_cast hd) (by exact_mod_cast hsq)).mp hR
    exact ⟨x, y, z, hnz, by push_cast at he ⊢; linear_combination he⟩
  · intro p _
    obtain ⟨x, y, z, hnz, he⟩ := (quaternary_sqdisc_iso_iff_ternary (a := (a : ℚ_[p])) (b := (b : ℚ_[p]))
      (c := (c : ℚ_[p])) (d := (d : ℚ_[p])) (s := (s : ℚ_[p])) (by exact_mod_cast ha)
      (by exact_mod_cast hb) (by exact_mod_cast hc) (by exact_mod_cast hd) (by exact_mod_cast hsq)).mp (hloc p)
    exact ⟨x, y, z, hnz, by push_cast at he ⊢; linear_combination he⟩

/-- **Rank ≥ 3 unit diagonal form over `ℚ_[p]` (odd `p`) is isotropic.** Fills the rank-3,4 gap below
`exists_diag_nary_zero_odd_padic` (rank ≥ 5): any diagonal form `∑ wᵢ xᵢ²` over `ℚ_[p]` with `p` odd and all
`‖wᵢ‖ = 1` (units) and rank ≥ 3 has a nontrivial zero (ternary sub-block on `{0,1,2}` via
`exists_diag_ternary_zero_odd_padic`, padded with zeros). The local-isotropy input for even unimodular forms
at odd primes (where they diagonalize to units over `ℤ_p`). -/
theorem exists_diag_nary_zero_odd_padic_unit {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {n : ℕ} (hn : 3 ≤ n)
    (w : Fin n → ℚ_[p]) (hw : ∀ i, ‖w i‖ = 1) :
    ∃ x : Fin n → ℚ_[p], x ≠ 0 ∧ ∑ i, w i * x i ^ 2 = 0 := by
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set i1 : Fin n := ⟨1, by omega⟩ with hi1
  set i2 : Fin n := ⟨2, by omega⟩ with hi2
  have d01 : i0 ≠ i1 := Fin.ne_of_val_ne (by simp [hi0, hi1])
  have d02 : i0 ≠ i2 := Fin.ne_of_val_ne (by simp [hi0, hi2])
  have d12 : i1 ≠ i2 := Fin.ne_of_val_ne (by simp [hi1, hi2])
  obtain ⟨x0, y0, z0, hnz, hzero⟩ :=
    exists_diag_ternary_zero_odd_padic hp (hw i0) (hw i1) (hw i2)
  set x : Fin n → ℚ_[p] :=
    fun i => if i = i0 then x0 else if i = i1 then y0 else if i = i2 then z0 else 0 with hx
  have vx0 : x i0 = x0 := by rw [hx]; simp
  have vx1 : x i1 = y0 := by rw [hx]; simp [d01.symm]
  have vx2 : x i2 = z0 := by rw [hx]; simp [d02.symm, d12.symm]
  have vxo : ∀ i, i ≠ i0 → i ≠ i1 → i ≠ i2 → x i = 0 := by
    intro i h0 h1 h2; rw [hx]; simp [h0, h1, h2]
  refine ⟨x, ?_, ?_⟩
  · intro hxz
    refine hnz ⟨?_, ?_, ?_⟩
    · rw [← vx0, hxz]; rfl
    · rw [← vx1, hxz]; rfl
    · rw [← vx2, hxz]; rfl
  · rw [← Finset.sum_subset (Finset.subset_univ {i0, i1, i2})]
    · rw [Finset.sum_insert (by simp [d01, d02]), Finset.sum_insert (by simp [d12]),
        Finset.sum_singleton, vx0, vx1, vx2]
      linear_combination hzero
    · intro i _ hi
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      rw [vxo i hi.1 hi.2.1 hi.2.2]; ring

/-- **Binary forms represent every unit value at a good odd prime.** Over `ℚ_[p]` with `p` an odd prime, if
`a`, `b`, `t` are all `p`-adic units (`‖·‖ = 1`), then `⟨a,b⟩` represents `t`: `∃ u v, a u² + b v² = t`.
(The ternary `a x² + b y² + (−t) z² = 0` has all-unit coefficients, hence is isotropic by
`exists_diag_ternary_zero_odd_padic`; `represents_of_ternary_isotropic` extracts the representation.) This is
the *good-place* fact that makes the bad set finite in the Hasse–Minkowski rank-4 / rank-≥5 argument: outside
the finitely many primes dividing `2·a·b·t`, a binary form automatically represents a chosen unit value. -/
theorem binary_represents_padic_of_units {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {a b t : ℚ_[p]} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (ht : ‖t‖ = 1) :
    ∃ u v : ℚ_[p], a * u ^ 2 + b * v ^ 2 = t := by
  haveI : Invertible (2 : ℚ_[p]) := invertibleOfNonzero two_ne_zero
  have ha0 : a ≠ 0 := by rintro rfl; rw [norm_zero] at ha; exact one_ne_zero ha.symm
  have hb0 : b ≠ 0 := by rintro rfl; rw [norm_zero] at hb; exact one_ne_zero hb.symm
  obtain ⟨x, y, z, hnz, he⟩ :=
    exists_diag_ternary_zero_odd_padic hp ha hb (show ‖(-t : ℚ_[p])‖ = 1 by rw [norm_neg]; exact ht)
  exact represents_of_ternary_isotropic ha0 hb0 ⟨x, y, z, hnz, by linear_combination he⟩

/-- **Even-valuation values are represented at a good odd prime.** Over `ℚ_[p]` with `p` odd and unit
coefficients `‖a‖ = ‖b‖ = 1`, the binary form `⟨a,b⟩` represents every nonzero `t` whose `p`-adic valuation
is even. (Write `t = u · (p^k)²` with `u` a unit via `padic_valuation_decomp`; representability is a
square-class invariant `binary_represents_congr_sq`, and units are represented by
`binary_represents_padic_of_units`.) So at a good odd prime, the *only* obstruction to representing a value
is odd valuation — the characterization that bounds the Dirichlet search in the rank-4 / rank-≥5 step. -/
theorem binary_represents_padic_even_val {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {a b t : ℚ_[p]} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (ht : t ≠ 0) (hv : Even t.valuation) :
    ∃ u v : ℚ_[p], a * u ^ 2 + b * v ^ 2 = t := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨k, hk⟩ := hv
  obtain ⟨w, hw, hwe⟩ := padic_valuation_decomp ht
  have hs : (p : ℚ_[p]) ^ k ≠ 0 := zpow_ne_zero _ hp0
  have hts : t = w * ((p : ℚ_[p]) ^ k) ^ 2 := by
    rw [hwe, hk, zpow_add₀ hp0]; ring
  obtain ⟨u, v, h⟩ := (binary_represents_congr_sq (a := a) (b := b) (t := w) hs).mp
    (binary_represents_padic_of_units hp ha hb hw)
  exact ⟨u, v, by rw [hts]; exact h⟩

/-- **Real-place binary representability criterion.** Over ℝ, for `a, b ≠ 0`, the binary form `⟨a,b⟩`
represents `t` iff `0 ≤ a·t ∨ 0 ≤ b·t`. (Forward: if `a·t < 0` and `b·t < 0` then `t² = a·t·u² + b·t·v² ≤ 0`,
impossible for `t ≠ 0`. Backward: if `0 ≤ a·t` then `0 ≤ t/a`, so `(√(t/a), 0)` works; symmetrically for
`b`.) The archimedean-place input to the Hasse–Minkowski rank-4 / rank-≥5 common-value search — a sign
condition matched by the global value's sign. -/
theorem real_binary_represents_iff {a b t : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (∃ u v : ℝ, a * u ^ 2 + b * v ^ 2 = t) ↔ (0 ≤ a * t ∨ 0 ≤ b * t) := by
  constructor
  · rintro ⟨u, v, h⟩
    by_contra hcon
    rw [not_or, not_le, not_le] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have ht : t ≠ 0 := by rintro rfl; simp at h1
    have k1 : a * t * u ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1.le (sq_nonneg u)
    have k2 : b * t * v ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h2.le (sq_nonneg v)
    have ht2 : t ^ 2 = a * t * u ^ 2 + b * t * v ^ 2 := by linear_combination (-t) * h
    have htpos : 0 < t ^ 2 := lt_of_le_of_ne (sq_nonneg t) (Ne.symm (pow_ne_zero 2 ht))
    linarith
  · intro h
    rcases h with h | h
    · have hta : 0 ≤ t / a := by
        have he : t / a = a * t / (a * a) := by field_simp
        rw [he]; exact div_nonneg h (mul_self_nonneg a)
      exact ⟨Real.sqrt (t / a), 0, by rw [Real.sq_sqrt hta]; field_simp; ring⟩
    · have htb : 0 ≤ t / b := by
        have he : t / b = b * t / (b * b) := by field_simp
        rw [he]; exact div_nonneg h (mul_self_nonneg b)
      exact ⟨0, Real.sqrt (t / b), by rw [Real.sq_sqrt htb]; field_simp; ring⟩

/-- **A binary form with `−ab` a square mod `p` is universal over `ℚ_[p]` (good prime).** Over `ℚ_[p]` with
`p` odd and unit coefficients `a, b : ℤ_[p]`, if `−a·b` is a square mod `p`, then `⟨a,b⟩` represents *every*
value over `ℚ_[p]` (regardless of valuation). (`−ab` square mod `p` ⟹ square in `ℚ_[p]`
[`isSquare_of_isSquare_toZMod`] ⟹ `⟨a,b⟩` is isotropic [`exists_binary_zero_iff`] ⟹ universal
[`binary_isotropic_universal`].) This is the *Dirichlet-controlled* clause of the rank-4 / rank-≥5
common-value search: at the one extra prime `q` introduced by the global value, choosing `q` (via Dirichlet)
so that `−ab` and `−cd` are both squares mod `q` makes both binary forms represent the value there,
*including at odd valuation*. -/
theorem binary_universal_padic_of_residue {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {a b : ℤ_[p]} (ha : IsUnit a) (hb : IsUnit b)
    (hres : IsSquare (PadicInt.toZMod (-(a * b)))) (t : ℚ_[p]) :
    ∃ x y : ℚ_[p], (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2 = t := by
  haveI : Invertible (2 : ℚ_[p]) := invertibleOfNonzero two_ne_zero
  obtain ⟨w, hw⟩ := isSquare_of_isSquare_toZMod hp (ha.mul hb).neg hres
  have ha0 : (a : ℚ_[p]) ≠ 0 := by rw [Ne, PadicInt.coe_eq_zero]; exact ha.ne_zero
  have hb0 : (b : ℚ_[p]) ≠ 0 := by rw [Ne, PadicInt.coe_eq_zero]; exact hb.ne_zero
  have hsq : IsSquare (-((a : ℚ_[p]) * (b : ℚ_[p]))) := by
    refine ⟨(w : ℚ_[p]), ?_⟩
    have hcast : (-((a : ℚ_[p]) * (b : ℚ_[p]))) = (((-(a * b) : ℤ_[p])) : ℚ_[p]) := by push_cast; ring
    rw [hcast, hw]; push_cast; ring
  exact binary_isotropic_universal ha0 hb0 ((exists_binary_zero_iff ha0).mpr hsq) t

/-! ### Dirichlet-prime selection for the rank-4 common-value keystone

The Serre rank-4 argument introduces a single extra prime `q` (outside the finite bad set) at which the
global value has odd valuation; there both binary forms must still represent it. By
`binary_universal_padic_of_residue`, it suffices that `−ab` and `−cd` are squares mod `q`. The following
lemmas produce, via Dirichlet's theorem (`Nat.forall_exists_prime_gt_and_modEq`) + quadratic reciprocity,
an arbitrarily large prime `q` at which two prescribed integers are *both* squares — the Dirichlet-controlled
clause of the keystone. -/

/-- **An odd prime `p` is a QR mod `q` when `q ≡ 1 mod 4` and `q ≡ 1 mod p`.** Pure quadratic reciprocity:
`(q | p) = 1` from `q ≡ 1 (mod p)`, and the reciprocity sign is `+1` since `q ≡ 1 (mod 4)`. -/
theorem isSquare_odd_prime_zmod {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) (hq4 : q % 4 = 1)
    (hqp : (q : ZMod p) = 1) : IsSquare ((p : ZMod q)) := by
  have hpz : ((p : ℤ) : ZMod q) ≠ 0 := by
    rw [Int.cast_natCast, Ne, CharP.cast_eq_zero_iff (ZMod q) q]
    exact fun h => hpq ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp h).symm
  have hpq1 : legendreSym p q = 1 := by
    rw [legendreSym.eq_one_iff p (by rw [Int.cast_natCast, hqp]; exact one_ne_zero)]
    rw [Int.cast_natCast, hqp]; exact ⟨1, by ring⟩
  have hqr := legendreSym.quadratic_reciprocity hp hq hpq
  rw [hpq1, mul_one] at hqr
  have heven : Even (p / 2 * (q / 2)) := (Nat.even_iff.mpr (by omega)).mul_left _
  rw [heven.neg_one_pow] at hqr
  exact by simpa using (legendreSym.eq_one_iff q hpz).mp hqr

/-- **Multiplicative QR criterion (ℕ).** If `q ≡ 1 (mod 8)` and every prime factor `p` of `m` satisfies
`q ≡ 1 (mod p)`, then `m` is a square mod `q`. Reduces over the factorisation of `m` (`Nat.recOnMul`):
the prime case is `isSquare_odd_prime_zmod` (odd `p`) or `ZMod.exists_sq_eq_two_iff` (`p = 2`, using
`q ≡ 1 mod 8`), and `IsSquare.mul` assembles. -/
theorem isSquare_natCast_zmod_of_modEq {q : ℕ} [Fact q.Prime] (hq8 : q % 8 = 1) :
    ∀ {m : ℕ}, (∀ p, p.Prime → p ∣ m → (q : ZMod p) = 1) → IsSquare ((m : ZMod q)) := by
  have hq2 : q ≠ 2 := by omega
  intro m
  induction m using Nat.recOnMul with
  | zero => intro _; exact ⟨0, by simp⟩
  | one => intro _; exact ⟨1, by simp⟩
  | prime p hp_prime =>
      intro hyp
      haveI := Fact.mk hp_prime
      have h := hyp p hp_prime (dvd_refl p)
      by_cases hp2 : p = 2
      · subst hp2; simpa using (ZMod.exists_sq_eq_two_iff hq2).mpr (Or.inl hq8)
      · exact isSquare_odd_prime_zmod hp2 hq2
          (fun he => by subst he; rw [ZMod.natCast_self] at h; exact one_ne_zero h.symm)
          (by omega) h
  | mul a b iha ihb =>
      intro hyp
      have hypA : ∀ p, p.Prime → p ∣ a → (q : ZMod p) = 1 :=
        fun p pp hpa => hyp p pp (hpa.mul_right b)
      have hypB : ∀ p, p.Prime → p ∣ b → (q : ZMod p) = 1 :=
        fun p pp hpb => hyp p pp (hpb.mul_left a)
      rw [Nat.cast_mul]
      exact (iha hypA).mul (ihb hypB)

/-- **Multiplicative QR criterion (ℤ).** If `q ≡ 1 (mod 8)` and every prime factor of `|m|` satisfies
`q ≡ 1 (mod p)`, then `m` is a square mod `q` (handle the sign: `−1` is a square since `q ≡ 1 mod 4`). -/
theorem isSquare_intCast_zmod_of_modEq {q : ℕ} [Fact q.Prime] (hq8 : q % 8 = 1)
    {m : ℤ} (hdvd : ∀ p, p.Prime → p ∣ m.natAbs → (q : ZMod p) = 1) :
    IsSquare ((m : ZMod q)) := by
  have hnat : IsSquare ((m.natAbs : ZMod q)) := isSquare_natCast_zmod_of_modEq hq8 hdvd
  rcases Int.natAbs_eq m with he | he
  · rw [he, Int.cast_natCast]; exact hnat
  · rw [he, Int.cast_neg, Int.cast_natCast, neg_eq_neg_one_mul]
    exact (ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)).mul hnat

/-- **Dirichlet-prime selection: a prime making two integers squares.** For nonzero `m, n : ℤ` and any
bound `N`, there is a prime `q > N` with both `m` and `n` squares mod `q`. (Dirichlet supplies a prime
`q ≡ 1 mod (8·|m|·|n|)`; then `isSquare_intCast_zmod_of_modEq` makes each of `m, n` a square mod `q`.) The
Dirichlet-controlled clause of the rank-4 Hasse–Minkowski common-value keystone: take `m = −ab`, `n = −cd`,
`N` past the bad set, and `binary_universal_padic_of_residue` makes both binaries universal at `q`. -/
theorem exists_prime_gt_isSquare_pair (N : ℕ) {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) :
    ∃ q : ℕ, q.Prime ∧ N < q ∧ IsSquare ((m : ZMod q)) ∧ IsSquare ((n : ZMod q)) := by
  set M : ℕ := 8 * m.natAbs * n.natAbs with hM
  have hMpos : M ≠ 0 := by
    rw [hM]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Int.natAbs_ne_zero.mpr hm))
      (Int.natAbs_ne_zero.mpr hn)
  obtain ⟨q, hqN, hqp, hqmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N (q := M) (a := 1) hMpos (Nat.coprime_one_left M)
  haveI := Fact.mk hqp
  have hq8 : q % 8 = 1 := by
    have h8 : q ≡ 1 [MOD 8] := Nat.ModEq.of_dvd ⟨m.natAbs * n.natAbs, by rw [hM]; ring⟩ hqmod
    have := h8; unfold Nat.ModEq at this; omega
  have mkdvd : ∀ {k : ℤ}, k ≠ 0 → (∀ p', p'.Prime → p' ∣ k.natAbs → p' ∣ M) →
      ∀ p, p.Prime → p ∣ k.natAbs → (q : ZMod p) = 1 := by
    intro k _ hsub p pp hpk
    haveI := Fact.mk pp
    have hmod : q ≡ 1 [MOD p] := Nat.ModEq.of_dvd (hsub p pp hpk) hqmod
    have h2 : ((q : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := (ZMod.natCast_eq_natCast_iff q 1 p).mpr hmod
    simpa using h2
  refine ⟨q, hqp, hqN, ?_, ?_⟩
  · exact isSquare_intCast_zmod_of_modEq hq8 (mkdvd hm (fun p' _ hpm => by
      rw [hM]; exact (hpm.mul_left 8).mul_right n.natAbs))
  · exact isSquare_intCast_zmod_of_modEq hq8 (mkdvd hn (fun p' _ hpn => by
      rw [hM]; exact (Dvd.dvd.mul_left hpn (8 * m.natAbs))))

/-- **`hilbertPadicInt` is invariant under a square factor (left).** `(a·s², b)_p = (a, b)_p`
(bimultiplicativity + `(±1)² = 1`). The symbol-side analogue of `solvable_canonical_congr_sq_left`, reducing
the symbol↔solvability bridge to the four `unit`/`p·unit` canonical cases. -/
theorem hilbertPadicInt_mul_sq_left {p : ℕ} [Fact p.Prime] {a b s : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hs : s ≠ 0) :
    HilbertSymbol.hilbertPadicInt p (a * s ^ 2) b = HilbertSymbol.hilbertPadicInt p a b := by
  rw [show a * s ^ 2 = a * (s * s) by ring,
      HilbertSymbol.hilbertPadicInt_mul_left (p := p) ha (mul_ne_zero hs hs),
      HilbertSymbol.hilbertPadicInt_mul_left (p := p) hs hs]
  rcases HilbertSymbol.hilbertPadicInt_mem (p := p) hs hb with h | h <;> rw [h] <;> ring

/-- **Integer canonical factorisation at `p`.** Every nonzero `a : ℤ` factors as `a = c · s²` with `s ≠ 0`
and `c` either `p`-free or `p ×` a `p`-free integer (split `a = p^{v} · pfree` by the parity of `v`). This
reduces the symbol↔solvability bridge to the four canonical cases. -/
theorem exists_canonical_padic_factor {p : ℕ} [Fact p.Prime] {a : ℤ} (ha : a ≠ 0) :
    ∃ c s : ℤ, s ≠ 0 ∧ a = c * s ^ 2 ∧
      (¬ (p : ℤ) ∣ c ∨ ∃ c', ¬ (p : ℤ) ∣ c' ∧ c = (p : ℤ) * c') := by
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hu : ¬ (p : ℤ) ∣ HilbertSymbol.pfreeInt p a := HilbertSymbol.not_dvd_pfreeInt p ha
  have hspec : a = (p : ℤ) ^ padicValInt p a * HilbertSymbol.pfreeInt p a :=
    HilbertSymbol.pfreeInt_spec p a
  rcases Nat.even_or_odd (padicValInt p a) with ⟨k, hk⟩ | ⟨k, hk⟩
  · refine ⟨HilbertSymbol.pfreeInt p a, (p : ℤ) ^ k, pow_ne_zero _ hpne, ?_, Or.inl hu⟩
    nth_rewrite 1 [hspec]; rw [hk, pow_add]; ring
  · refine ⟨(p : ℤ) * HilbertSymbol.pfreeInt p a, (p : ℤ) ^ k, pow_ne_zero _ hpne, ?_,
      Or.inr ⟨_, hu, rfl⟩⟩
    nth_rewrite 1 [hspec]; rw [hk, show 2 * k + 1 = k + k + 1 by ring, pow_add, pow_add, pow_one]; ring

/-- **Norm of a `p`-free integer is `1` in `ℚ_[p]`.** -/
theorem padic_norm_intCast_eq_one {p : ℕ} [Fact p.Prime] {k : ℤ} (h : ¬ (p : ℤ) ∣ k) :
    ‖((k : ℤ) : ℚ_[p])‖ = 1 := by
  have hc : ((k : ℤ) : ℚ_[p]) = ((k : ℤ_[p]) : ℚ_[p]) := by push_cast; ring
  rw [hc, padic_norm_e_of_padicInt, PadicInt.norm_intCast_eq_one_iff, isCoprime_comm]
  exact ((Nat.prime_iff_prime_int.mp Fact.out).coprime_iff_not_dvd).mpr h

/-- **Symbol↔solvability bridge, unit/unit case.** For `p ∤ a`, `p ∤ b` (odd `p`): `z² = a x² + b y²` is
solvable over `ℚ_[p]` iff `(a,b)_p = 1` — both hold (unit ternary is isotropic; `hilbertPadicInt_units`). -/
theorem solvable_padic_iff_hilbert_uu {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a b : ℤ}
    (ha : ¬ (p : ℤ) ∣ a) (hb : ¬ (p : ℤ) ∣ b) :
    (∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2) ↔
    HilbertSymbol.hilbertPadicInt p a b = 1 := by
  refine ⟨fun _ => HilbertSymbol.hilbertPadicInt_units (p := p) ha hb, fun _ => ?_⟩
  exact solvable_canonical_ternary_odd_units hp (padic_norm_intCast_eq_one ha)
    (padic_norm_intCast_eq_one hb)

/-- **`hilbertPadicInt` against a `p·unit` second argument** (`p ∤ a`, `p ∤ b'`): `(a, p·b')_p = (a | p)`
(bimultiplicativity: `(a,p·b')=(a,p)·(a,b')=(a|p)·1`). Computes the symbol in the `unit`/`p·unit` bridge case. -/
theorem hilbertPadicInt_pUnit_right {p : ℕ} [Fact p.Prime] {a b' : ℤ} (ha : ¬ (p : ℤ) ∣ a)
    (hb' : ¬ (p : ℤ) ∣ b') :
    HilbertSymbol.hilbertPadicInt p a ((p : ℤ) * b') = legendreSym p a := by
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hb0 : b' ≠ 0 := fun h => hb' (h ▸ dvd_zero _)
  rw [HilbertSymbol.hilbertPadicInt_mul_right (p := p) hpne hb0,
      HilbertSymbol.hilbertPadicInt_eq_legendre (p := p) ha,
      HilbertSymbol.hilbertPadicInt_units (p := p) ha hb', mul_one]

/-- **`hilbertPadicInt` against two `p·unit` arguments**: `(p·a', p·b')_p = (-1)^{(p-1)/2}·(a'|p)·(b'|p)`. -/
theorem hilbertPadicInt_pUnit_pUnit {p : ℕ} [Fact p.Prime] {a' b' : ℤ} (ha' : ¬ (p : ℤ) ∣ a')
    (hb' : ¬ (p : ℤ) ∣ b') :
    HilbertSymbol.hilbertPadicInt p ((p : ℤ) * a') ((p : ℤ) * b') =
      (-1) ^ ((p - 1) / 2) * legendreSym p a' * legendreSym p b' := by
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have ha0 : a' ≠ 0 := fun h => ha' (h ▸ dvd_zero _)
  have hb0 : b' ≠ 0 := fun h => hb' (h ▸ dvd_zero _)
  rw [HilbertSymbol.hilbertPadicInt_mul_left (p := p) hpne ha0,
      hilbertPadicInt_pUnit_right ha' hb',
      HilbertSymbol.hilbertPadicInt_mul_right (p := p) hpne hb0,
      HilbertSymbol.hilbertPadicInt_diag,
      HilbertSymbol.hilbertPadicInt_comm p (p : ℤ) b',
      HilbertSymbol.hilbertPadicInt_eq_legendre (p := p) hb']
  ring

/-- **Symbol↔solvability bridge, unit/`p·unit` case.** For `p ∤ a`, `p ∤ b'` (odd `p`):
`z² = a x² + (p·b') y²` solvable over `ℚ_[p]` iff `(a, p·b')_p = 1`. (`solvable_unit_pUnit_iff` ⟺
`toZMod a` square; `hilbertPadicInt_pUnit_right` gives the symbol `= (a|p)`; `legendreSym.eq_one_iff`.) -/
theorem solvable_padic_iff_hilbert_up {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a b' : ℤ}
    (ha : ¬ (p : ℤ) ∣ a) (hb' : ¬ (p : ℤ) ∣ b') :
    (∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = (a : ℚ_[p]) * x ^ 2 + (((p : ℤ) * b' : ℤ) : ℚ_[p]) * y ^ 2) ↔
    HilbertSymbol.hilbertPadicInt p a ((p : ℤ) * b') = 1 := by
  have hua : IsUnit ((a : ℤ_[p])) := by
    rw [PadicInt.isUnit_iff, ← padic_norm_e_of_padicInt, PadicInt.coe_intCast]
    exact padic_norm_intCast_eq_one ha
  have hub : IsUnit ((b' : ℤ_[p])) := by
    rw [PadicInt.isUnit_iff, ← padic_norm_e_of_padicInt, PadicInt.coe_intCast]
    exact padic_norm_intCast_eq_one hb'
  have haz : ((a : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact ha
  have hform : (∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = (a : ℚ_[p]) * x ^ 2 + (((p : ℤ) * b' : ℤ) : ℚ_[p]) * y ^ 2) ↔
      (∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = ((a : ℤ_[p]) : ℚ_[p]) * x ^ 2 + (p : ℚ_[p]) * ((b' : ℤ_[p]) : ℚ_[p]) * y ^ 2) := by
    rw [PadicInt.coe_intCast]; push_cast; ring_nf
  rw [hform, solvable_unit_pUnit_iff hp hua hub, hilbertPadicInt_pUnit_right ha hb',
      show PadicInt.toZMod (a : ℤ_[p]) = ((a : ℤ) : ZMod p) from map_intCast PadicInt.toZMod a,
      ← legendreSym.eq_one_iff p haz]

/-- **Symbol↔solvability bridge, `p·unit`/unit case** (symmetric to `_up` via coefficient swap +
`hilbertPadicInt_comm`). -/
theorem solvable_padic_iff_hilbert_pu {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a' b : ℤ}
    (ha' : ¬ (p : ℤ) ∣ a') (hb : ¬ (p : ℤ) ∣ b) :
    (∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = (((p : ℤ) * a' : ℤ) : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2) ↔
    HilbertSymbol.hilbertPadicInt p ((p : ℤ) * a') b = 1 := by
  rw [HilbertSymbol.hilbertPadicInt_comm p ((p : ℤ) * a') b, ← solvable_padic_iff_hilbert_up hp hb ha']
  exact ⟨solvable_canonical_symm, solvable_canonical_symm⟩

/-- `legendreSym p (-1) = (-1)^{(p-1)/2}` for an odd prime (`χ₄` ↔ the power, by `p mod 4`). -/
theorem legendreSym_neg_one_eq_pow {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p (-1) = (-1 : ℤ) ^ ((p - 1) / 2) := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp)
  rw [legendreSym.at_neg_one hp, ZMod.χ₄_nat_eq_if_mod_four, if_neg (by omega)]
  rcases (show p % 4 = 1 ∨ p % 4 = 3 by omega) with h | h
  · rw [if_pos h, eq_comm]; exact Even.neg_one_pow (Nat.even_iff.mpr (by omega))
  · rw [if_neg (by omega), eq_comm]; exact Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))

/-- **Symbol↔solvability bridge, `p·unit`/`p·unit` case.** For `p ∤ a'`, `p ∤ b'` (odd `p`):
`z² = (p·a') x² + (p·b') y²` solvable over `ℚ_[p]` iff `(p·a', p·b')_p = 1`. (`solvable_pUnit_pUnit_iff` ⟺
`toZMod (-(a'·b'))` square; `hilbertPadicInt_pUnit_pUnit` gives the symbol; `legendreSym` multiplicativity +
`legendreSym_neg_one_eq_pow`.) -/
theorem solvable_padic_iff_hilbert_pp {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a' b' : ℤ}
    (ha' : ¬ (p : ℤ) ∣ a') (hb' : ¬ (p : ℤ) ∣ b') :
    (∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = (((p : ℤ) * a' : ℤ) : ℚ_[p]) * x ^ 2 + (((p : ℤ) * b' : ℤ) : ℚ_[p]) * y ^ 2) ↔
    HilbertSymbol.hilbertPadicInt p ((p : ℤ) * a') ((p : ℤ) * b') = 1 := by
  have hua' : IsUnit ((a' : ℤ_[p])) := by
    rw [PadicInt.isUnit_iff, ← padic_norm_e_of_padicInt, PadicInt.coe_intCast]
    exact padic_norm_intCast_eq_one ha'
  have hub' : IsUnit ((b' : ℤ_[p])) := by
    rw [PadicInt.isUnit_iff, ← padic_norm_e_of_padicInt, PadicInt.coe_intCast]
    exact padic_norm_intCast_eq_one hb'
  have haz : ((-(a' * b') : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun h => (((Nat.prime_iff_prime_int.mp Fact.out).dvd_mul.mp
      ((dvd_neg).mp h)).elim ha' hb')
  have hform : (∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = (((p : ℤ) * a' : ℤ) : ℚ_[p]) * x ^ 2 + (((p : ℤ) * b' : ℤ) : ℚ_[p]) * y ^ 2) ↔
      (∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = (p : ℚ_[p]) * ((a' : ℤ_[p]) : ℚ_[p]) * x ^ 2
        + (p : ℚ_[p]) * ((b' : ℤ_[p]) : ℚ_[p]) * y ^ 2) := by
    rw [PadicInt.coe_intCast, PadicInt.coe_intCast]; push_cast; ring_nf
  rw [hform, solvable_pUnit_pUnit_iff hp hua' hub', hilbertPadicInt_pUnit_pUnit ha' hb',
      show PadicInt.toZMod (-((a' : ℤ_[p]) * (b' : ℤ_[p]))) = ((-(a' * b') : ℤ) : ZMod p) by
        rw [map_neg, map_mul, map_intCast, map_intCast]; push_cast; ring,
      ← legendreSym.eq_one_iff p haz,
      show (-(a' * b') : ℤ) = (-1) * (a' * b') by ring, legendreSym.mul, legendreSym.mul,
      legendreSym_neg_one_eq_pow hp, mul_assoc]

/-- **Real-place sign selection for the common value.** Over ℝ, if `⟨a,b⟩` and `⟨c,d⟩` share a *nonzero*
represented value (in the `real_binary_represents_iff` sign form `0 ≤ a·t ∨ 0 ≤ b·t`), then there is a
sign `ε ∈ {1, −1}` with `0 ≤ a·ε ∨ 0 ≤ b·ε` and `0 ≤ c·ε ∨ 0 ≤ d·ε`. Since the representability sign
condition for `ε·q` (`q > 0`) is exactly the sign condition for `ε`, this fixes the real sign of the global
value `t = ε·q` in the rank-4 keystone so that both binaries represent it over ℝ. -/
theorem exists_sign_for_real_common {a b c d : ℝ}
    (h : ∃ t : ℝ, t ≠ 0 ∧ (0 ≤ a * t ∨ 0 ≤ b * t) ∧ (0 ≤ c * t ∨ 0 ≤ d * t)) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ (0 ≤ a * ε ∨ 0 ≤ b * ε) ∧ (0 ≤ c * ε ∨ 0 ≤ d * ε) := by
  obtain ⟨t, ht, hab, hcd⟩ := h
  rcases lt_or_gt_of_ne ht with htneg | htpos
  · refine ⟨-1, Or.inr rfl, ?_, ?_⟩
    · rcases hab with h | h
      · exact Or.inl (by nlinarith)
      · exact Or.inr (by nlinarith)
    · rcases hcd with h | h
      · exact Or.inl (by nlinarith)
      · exact Or.inr (by nlinarith)
  · refine ⟨1, Or.inl rfl, ?_, ?_⟩
    · rcases hab with h | h
      · exact Or.inl (by nlinarith)
      · exact Or.inr (by nlinarith)
    · rcases hcd with h | h
      · exact Or.inl (by nlinarith)
      · exact Or.inr (by nlinarith)

/-- **Rank-4 isotropy from the common-value keystone (top-level reduction).** If there is a single nonzero
rational `t` that is represented by `⟨a,b⟩` *and* by `⟨c,d⟩` over ℝ and over every ℚ_p, then the quaternary
`a x² + b y² = c z² + d w²` has a nontrivial rational solution. (Two applications of the value-local–global
`binary_represents_of_local` make both binaries represent `t` over ℚ; `quaternary_isotropic_of_common_value`
assembles.) This isolates the entire remaining content of the n=4 non-square-disc Hasse–Minkowski case into a
single keystone: *the existence of such a global `t`* (the weak-approximation / Dirichlet construction
`t = ε·q`). Everything downstream of the keystone is now a theorem. -/
theorem quaternary_isotropic_of_keystone {a b c d : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0)
    (hkey : ∃ t : ℚ, t ≠ 0 ∧
      (∃ u v : ℝ, (a : ℝ) * u ^ 2 + (b : ℝ) * v ^ 2 = (t : ℝ)) ∧
      (∀ (p : ℕ) [Fact p.Prime], ∃ u v : ℚ_[p], (a : ℚ_[p]) * u ^ 2 + (b : ℚ_[p]) * v ^ 2 = (t : ℚ_[p])) ∧
      (∃ u v : ℝ, (c : ℝ) * u ^ 2 + (d : ℝ) * v ^ 2 = (t : ℝ)) ∧
      (∀ (p : ℕ) [Fact p.Prime], ∃ u v : ℚ_[p], (c : ℚ_[p]) * u ^ 2 + (d : ℚ_[p]) * v ^ 2 = (t : ℚ_[p]))) :
    ∃ x y z w : ℚ, ¬(x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) ∧
      a * x ^ 2 + b * y ^ 2 = c * z ^ 2 + d * w ^ 2 := by
  obtain ⟨t, ht, hRab, hlocab, hRcd, hloccd⟩ := hkey
  have h1 : ∃ u v : ℚ, a * u ^ 2 + b * v ^ 2 = t := binary_represents_of_local ha hb ht hRab hlocab
  have h2 : ∃ u v : ℚ, c * u ^ 2 + d * v ^ 2 = t := binary_represents_of_local hc hd ht hRcd hloccd
  exact quaternary_isotropic_of_common_value ht h1 h2

/-- **Representability transfers across a square ratio (field-generic).** If `⟨a,b⟩` represents `c ≠ 0` and
`r / c` is a square, then `⟨a,b⟩` represents `r`. (Write `r = c·s²`; `binary_represents_congr_sq`.) This is the
*square-class-matching* mechanism of the rank-4 keystone: once the global value `t` is constructed so that
`t / c_p` is a `ℚ_p`-square at each bad place `p` (with `c_p` the local common value there), this transfers
the local representability of `c_p` to `t`. -/
theorem binary_represents_of_isSquare_ratio {K : Type*} [Field K] {a b c r : K} (hc : c ≠ 0)
    (hrep : ∃ u v : K, a * u ^ 2 + b * v ^ 2 = c) (hsq : IsSquare (r / c)) :
    ∃ u v : K, a * u ^ 2 + b * v ^ 2 = r := by
  obtain ⟨s, hs⟩ := hsq
  by_cases hr : r = 0
  · exact ⟨0, 0, by rw [hr]; ring⟩
  · have hs0 : s ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hs
      exact hr ((div_eq_zero_iff.mp hs).resolve_right hc)
    have hrcs : r = c * s ^ 2 := by
      have : r / c = s ^ 2 := by rw [hs]; ring
      field_simp [hc] at this ⊢; linear_combination this
    rw [hrcs]
    exact (binary_represents_congr_sq hs0).mp hrep

/-- **CRT: an integer hitting prescribed residues at finitely many distinct primes.** For a `Nodup` list of
primes `ps` and any target-residue function `r`, there is an integer `k` with `(k : ZMod p) = r p` for every
`p ∈ ps` (`Nat.chineseRemainderOfList`, distinct primes pairwise coprime). The unit-residue–matching core of
the rank-4 keystone's global-value construction `t = ε·q·∏p^{δ_p}`: it sets the unit part of `t` to the
prescribed `ℚ_p`-square class at each bad odd prime simultaneously. -/
theorem exists_int_residues (ps : List ℕ) (hps : ∀ p ∈ ps, p.Prime) (hd : ps.Nodup)
    (r : ℕ → ℕ) : ∃ k : ℤ, ∀ p ∈ ps, (k : ZMod p) = (r p : ZMod p) := by
  have hpw : List.Pairwise (Function.onFun Nat.Coprime id) ps := by
    rw [List.pairwise_iff_get]
    intro i j hij
    have hne : ps.get i ≠ ps.get j := fun h => by
      have := hd.get_inj_iff.mp h; omega
    exact (Nat.coprime_primes (hps _ (List.get_mem _ _)) (hps _ (List.get_mem _ _))).mpr hne
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfList r id ps hpw
  refine ⟨(k : ℤ), fun p hp => ?_⟩
  have h2 : (k : ZMod p) = (r p : ZMod p) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hk p hp)
  push_cast
  exact_mod_cast h2

/-- **Equal residues ⟹ square ratio (odd `p`, unit case).** Two `ℤ_[p]` units `u, v` with the same residue
mod `p` have `u/v` a square in `ℚ_[p]`. (`u·v⁻¹` is a unit with residue `1`, hence a square by
`isSquare_iff_isSquare_toZMod`.) The valuation-`0` half of the square-class matching in the rank-4 keystone:
combined with `binary_represents_of_isSquare_ratio` it transfers local representability of a unit common value
to a constructed global value sharing its residue at a bad odd prime. -/
theorem isSquare_padic_div_units {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {u v : ℤ_[p]}
    (hu : IsUnit u) (hv : IsUnit v) (hres : PadicInt.toZMod u = PadicInt.toZMod v) :
    IsSquare ((u : ℚ_[p]) / (v : ℚ_[p])) := by
  obtain ⟨vinv, hvinv⟩ := hv.exists_right_inv
  have hvinvu : IsUnit vinv := IsUnit.of_mul_eq_one v (by rw [mul_comm]; exact hvinv)
  have hw : IsUnit (u * vinv) := hu.mul hvinvu
  have hvc : (v : ℚ_[p]) * (vinv : ℚ_[p]) = 1 := by
    rw [← PadicInt.coe_mul, hvinv, PadicInt.coe_one]
  have hvcoe : (v : ℚ_[p]) ≠ 0 := by rw [Ne, PadicInt.coe_eq_zero]; exact hv.ne_zero
  have hdiv : ((u * vinv : ℤ_[p]) : ℚ_[p]) = (u : ℚ_[p]) / (v : ℚ_[p]) := by
    rw [PadicInt.coe_mul, eq_div_iff hvcoe]; linear_combination (u : ℚ_[p]) * hvc
  rw [← hdiv]
  refine (isSquare_padic_unit_iff_residue hp hw).mpr ?_
  have htz : PadicInt.toZMod (u * vinv) = 1 := by
    rw [map_mul, hres, ← map_mul, hvinv, map_one]
  rw [htz]; exact ⟨1, by ring⟩

/-- `hilbertPadicInt` invariant under a square factor (right), via `_left` + `comm`. -/
theorem hilbertPadicInt_mul_sq_right {p : ℕ} [Fact p.Prime] {a b s : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hs : s ≠ 0) :
    HilbertSymbol.hilbertPadicInt p a (b * s ^ 2) = HilbertSymbol.hilbertPadicInt p a b := by
  rw [HilbertSymbol.hilbertPadicInt_comm p a (b * s ^ 2), hilbertPadicInt_mul_sq_left hb ha hs,
      HilbertSymbol.hilbertPadicInt_comm p b a]

/-- `hilbert2Int` invariant under a square factor (left), via bimultiplicativity + `(±1)² = 1`. -/
theorem hilbert2Int_mul_sq_left {a b s : ℤ} (ha : a ≠ 0) (_hb : b ≠ 0) (hs : s ≠ 0) :
    HilbertSymbol.hilbert2Int (a * s ^ 2) b = HilbertSymbol.hilbert2Int a b := by
  rw [show a * s ^ 2 = a * (s * s) by ring, HilbertSymbol.hilbert2Int_mul_left ha (mul_ne_zero hs hs),
      HilbertSymbol.hilbert2Int_mul_left hs hs]
  rcases HilbertSymbol.hilbert2Int_mem s b with h | h <;> rw [h] <;> ring

/-- `hilbert2Int` invariant under a square factor (right). -/
theorem hilbert2Int_mul_sq_right {a b s : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0) :
    HilbertSymbol.hilbert2Int a (b * s ^ 2) = HilbertSymbol.hilbert2Int a b := by
  rw [HilbertSymbol.hilbert2Int_comm a (b * s ^ 2), hilbert2Int_mul_sq_left hb ha hs,
      HilbertSymbol.hilbert2Int_comm b a]

/-- **Symbol↔solvability bridge over `ℚ_[p]` (odd `p`).** For nonzero integers `a, b` and odd `p`, the
canonical Hilbert ternary `z² = a x² + b y²` is solvable over `ℚ_[p]` iff `(a,b)_p = 1`. Reduce `a, b` to
their canonical (`unit`/`p·unit`) classes by factoring out squares (`exists_canonical_padic_factor`;
`solvable_canonical_congr_sq`(`_right`) and `hilbertPadicInt_mul_sq_left`(`_right`) make both sides
square-class invariant), then dispatch to the four canonical cases (`_uu`/`_up`/`_pu`/`_pp`). This connects
the *combinatorial* Hilbert symbol (whose product formula `hilbertGlobalProd_eq_one` is proven) to actual
local solvability — the reframing that makes the rank-4 common-value consistency a corollary of reciprocity. -/
theorem solvable_padic_iff_hilbertPadicInt_one {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a b : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    (∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2) ↔
    HilbertSymbol.hilbertPadicInt p a b = 1 := by
  obtain ⟨ca, sa, hsa, hae, hca⟩ := exists_canonical_padic_factor (p := p) ha
  obtain ⟨cb, sb, hsb, hbe, hcb⟩ := exists_canonical_padic_factor (p := p) hb
  have hca0 : ca ≠ 0 := by rintro rfl; rw [zero_mul] at hae; exact ha hae
  have hcb0 : cb ≠ 0 := by rintro rfl; rw [zero_mul] at hbe; exact hb hbe
  have hsaQ : (sa : ℚ_[p]) ≠ 0 := by exact_mod_cast hsa
  have hsbQ : (sb : ℚ_[p]) ≠ 0 := by exact_mod_cast hsb
  have hsol : (∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2) ↔
      (∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = (ca : ℚ_[p]) * x ^ 2 + (cb : ℚ_[p]) * y ^ 2) := by
    rw [show (a : ℚ_[p]) = (ca : ℚ_[p]) * (sa : ℚ_[p]) ^ 2 by rw [hae]; push_cast; ring,
        show (b : ℚ_[p]) = (cb : ℚ_[p]) * (sb : ℚ_[p]) ^ 2 by rw [hbe]; push_cast; ring]
    exact ((solvable_canonical_congr_sq hsaQ).trans (solvable_canonical_congr_sq_right hsbQ)).symm
  have hsym : HilbertSymbol.hilbertPadicInt p a b = HilbertSymbol.hilbertPadicInt p ca cb := by
    rw [hae, hbe, hilbertPadicInt_mul_sq_left hca0 (mul_ne_zero hcb0 (pow_ne_zero 2 hsb)) hsa,
        hilbertPadicInt_mul_sq_right hca0 hcb0 hsb]
  rw [hsol, hsym]
  rcases hca with hpca | ⟨ca', hca', rfl⟩
  · rcases hcb with hpcb | ⟨cb', hcb', rfl⟩
    · exact solvable_padic_iff_hilbert_uu hp hpca hpcb
    · exact solvable_padic_iff_hilbert_up hp hpca hcb'
  · rcases hcb with hpcb | ⟨cb', hcb', rfl⟩
    · exact solvable_padic_iff_hilbert_pu hp hca' hpcb
    · exact solvable_padic_iff_hilbert_pp hp hca' hcb'

/-- **Symbol↔solvability bridge over `ℚ_[2]`.** For nonzero integers `a, b`, the canonical Hilbert ternary
`z² = a x² + b y²` is solvable over `ℚ_[2]` iff `hilbert2Int a b = 1`. Reduce `a, b` to their canonical
(`odd`/`2·odd`) classes by factoring out squares (`exists_canonical_padic_factor` at `p = 2`;
`hilbert2Int_mul_sq_left`(`_right`) and `solvable_canonical_congr_sq`(`_right`) make both sides square-class
invariant), then dispatch to the four canonical cases (`unit`/`2u-v`/`u-2v`[by symmetry]/`2u-2v`). -/
theorem solvable_2adic_iff_hilbert2Int {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (∃ x y z : ℚ_[2], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = (a : ℚ_[2]) * x ^ 2 + (b : ℚ_[2]) * y ^ 2) ↔
    HilbertSymbol.hilbert2Int a b = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ca, sa, hsa, hae, hca⟩ := exists_canonical_padic_factor (p := 2) ha
  obtain ⟨cb, sb, hsb, hbe, hcb⟩ := exists_canonical_padic_factor (p := 2) hb
  simp only [Nat.cast_ofNat] at hca hcb
  have hca0 : ca ≠ 0 := by rintro rfl; rw [zero_mul] at hae; exact ha hae
  have hcb0 : cb ≠ 0 := by rintro rfl; rw [zero_mul] at hbe; exact hb hbe
  have hsaQ : (sa : ℚ_[2]) ≠ 0 := by exact_mod_cast hsa
  have hsbQ : (sb : ℚ_[2]) ≠ 0 := by exact_mod_cast hsb
  have hsol : (∃ x y z : ℚ_[2], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = (a : ℚ_[2]) * x ^ 2 + (b : ℚ_[2]) * y ^ 2) ↔
      (∃ x y z : ℚ_[2], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = (ca : ℚ_[2]) * x ^ 2 + (cb : ℚ_[2]) * y ^ 2) := by
    rw [show (a : ℚ_[2]) = (ca : ℚ_[2]) * (sa : ℚ_[2]) ^ 2 by rw [hae]; push_cast; ring,
        show (b : ℚ_[2]) = (cb : ℚ_[2]) * (sb : ℚ_[2]) ^ 2 by rw [hbe]; push_cast; ring]
    exact ((solvable_canonical_congr_sq hsaQ).trans (solvable_canonical_congr_sq_right hsbQ)).symm
  have hsym : HilbertSymbol.hilbert2Int a b = HilbertSymbol.hilbert2Int ca cb := by
    rw [hae, hbe, hilbert2Int_mul_sq_left hca0 (mul_ne_zero hcb0 (pow_ne_zero 2 hsb)) hsa,
        hilbert2Int_mul_sq_right hca0 hcb0 hsb]
  rw [hsol, hsym]
  rcases hca with hpca | ⟨ca', hca', rfl⟩
  · rcases hcb with hpcb | ⟨cb', hcb', rfl⟩
    · exact solvable_2adic_unit_iff hpca hpcb
    · rw [show (∃ x y z : ℚ_[2], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
            z ^ 2 = (ca : ℚ_[2]) * x ^ 2 + ((2 * cb' : ℤ) : ℚ_[2]) * y ^ 2) ↔
          (∃ x y z : ℚ_[2], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
            z ^ 2 = ((2 * cb' : ℤ) : ℚ_[2]) * x ^ 2 + (ca : ℚ_[2]) * y ^ 2) from
        ⟨solvable_canonical_symm, solvable_canonical_symm⟩,
        solvable_2adic_pUnit_unit_iff hcb' hpca, HilbertSymbol.hilbert2Int_comm]
  · rcases hcb with hpcb | ⟨cb', hcb', rfl⟩
    · exact solvable_2adic_pUnit_unit_iff hca' hpcb
    · exact solvable_2adic_pUnit_pUnit_iff hca' hcb'

/-- **Binary representability ⟺ Hilbert symbol over `ℚ_[p]` (odd `p`).** `⟨a,b⟩` represents `t` over `ℚ_[p]`
iff `hilbertPadicInt p (a·t) (b·t) = 1`. (`⟨a,b⟩` represents `t` ⟺ `⟨a,b,−t⟩` isotropic ⟺ [×t, `Z = t·z`]
`Z² = (at) x² + (bt) y²` solvable ⟺ [`solvable_padic_iff_hilbertPadicInt_one`] the symbol.) Converts the
keystone's local representability conditions into the symbol conditions the product formula governs. -/
theorem represents_padic_iff_symbol_odd {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a b t : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0) :
    (∃ u v : ℚ_[p], (a : ℚ_[p]) * u ^ 2 + (b : ℚ_[p]) * v ^ 2 = (t : ℚ_[p])) ↔
    HilbertSymbol.hilbertPadicInt p (a * t) (b * t) = 1 := by
  haveI : Invertible (2 : ℚ_[p]) := invertibleOfNonzero two_ne_zero
  rw [← solvable_padic_iff_hilbertPadicInt_one hp (mul_ne_zero ha ht) (mul_ne_zero hb ht)]
  have htQ : (t : ℚ_[p]) ≠ 0 := by exact_mod_cast ht
  constructor
  · rintro ⟨u, v, he⟩
    refine ⟨u, v, (t : ℚ_[p]), fun hc => htQ hc.2.2, ?_⟩
    push_cast; linear_combination (-(t : ℚ_[p])) * he
  · rintro ⟨x, y, z, hnz, he⟩
    have ha0 : (a : ℚ_[p]) ≠ 0 := by exact_mod_cast ha
    have hb0 : (b : ℚ_[p]) ≠ 0 := by exact_mod_cast hb
    refine represents_of_ternary_isotropic ha0 hb0 ⟨x, y, z / (t : ℚ_[p]), ?_, ?_⟩
    · rintro ⟨hx, hy, hz⟩
      refine hnz ⟨hx, hy, ?_⟩
      rw [div_eq_zero_iff] at hz; exact hz.resolve_right htQ
    · field_simp
      push_cast at he; linear_combination -he

end SKEFTHawking
