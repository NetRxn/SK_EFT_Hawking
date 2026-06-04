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

end SKEFTHawking
