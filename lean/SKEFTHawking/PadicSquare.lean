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

/-- **2-adic forward solvability.** If `u ≡ 1 (mod 8)` (a `2`-adic square) then `z² = u x² + b y²` is
solvable over `ℚ_[2]` for any `b` (take `y = 0`, `z = √u · x`). The easy direction of the `p = 2` symbol
case, via the 2-adic square criterion `isSquare_of_toZModPow_three_eq_one`. -/
theorem solvable_2adic_of_unit_sq {u : ℤ_[2]} (hu8 : PadicInt.toZModPow 3 u = 1) (b : ℚ_[2]) :
    ∃ x y z : ℚ_[2], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ z ^ 2 = (u : ℚ_[2]) * x ^ 2 + b * y ^ 2 := by
  obtain ⟨w, hw⟩ := isSquare_of_toZModPow_three_eq_one hu8
  exact solvable_ternary_of_sufficient (Or.inl ⟨(w : ℚ_[2]), by rw [hw]; push_cast; ring⟩)

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
      · push_neg at hsq
        obtain ⟨hnsa, hnsb⟩ := hsq
        have hreal : ¬(a < 0 ∧ b < 0) := by
          rw [← solvable_real_canonical_iff ha hb]
          obtain ⟨x, y, z, hnz, he⟩ := hR
          exact ⟨x, y, z, fun h => hnz (by rw [Prod.mk_eq_zero, Prod.mk_eq_zero] at h; exact h), he⟩
        have hb2 : 2 ≤ b.natAbs := by
          by_contra hc
          push_neg at hc
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

end SKEFTHawking
