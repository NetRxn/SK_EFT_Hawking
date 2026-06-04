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
    ∃ (k : ℤ) (u : ℚ_[p]), ‖u‖ = 1 ∧ x = (p : ℚ_[p]) ^ k * u := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨x.valuation, x * (p : ℚ_[p]) ^ (-x.valuation), ?_, ?_⟩
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

end SKEFTHawking
