/-
# Phase 5q.H — Hasse–Minkowski at ranks 3 and 4 for ODD unimodular forms

`OddFormDiagonalization.odd_indefinite_pmDiagonal` (Milnor–Husemoller II.4.3) runs an unconditional
unit-peel induction down to rank 4 and then stalls: the peel needs a unit vector, which comes from an
integer isotropic vector, which at rank `≥ 5` is Meyer (`weakIsotropic_of_five_le`). Ranks 3 and 4 are
the residue, exposed there as `OddRank34Diagonalizable`.

This module discharges the local–global input at those ranks. The banked local tooling carries most
of it:

* **odd `p`** — `RokhlinHMRankFour.isotropic_padicInt_of_unit_det` is *not* even-specific: it needs
  only rank `≥ 3`, `p ≠ 2` and a unit determinant over `ℤ_[p]`. Transported through the explicit
  rational congruence `congr_of_equiv_weighted`, it gives local isotropy of the ℚ-diagonalization at
  every odd prime (`diag_weights_isotropic_odd_padic`, shared by both ranks).
* **`ℝ`** — indefiniteness (`diag_real_isotropic_of_signs`).
* **`p = 2`** — reciprocity. This is the only place the two ranks differ:
  - rank 3: the ternary form's isotropy at a place is the *single* Hilbert symbol `(α, β)_v` with
    `α = −d₀d₂`, `β = −d₁d₂` (`isotropic_diag_ternary_iff_canonical` +
    `solvable_canonical_of_sq_mul` + the per-place symbol bridges), so
    `hilbertPrime_two_eq_one_of_real_odd` pins the place `2` from the others
    (`diag_ternary_isotropic_2adic_of_real_odd`). **No square-discriminant hypothesis is needed** —
    a ternary form is always governed by one symbol.
  - rank 4 with `det = 1`: square discriminant, so `quaternary_sqdisc_solvable_of_local_no_two`
    applies verbatim — the *only* use of evenness in `weakIsotropic_rank_four` was
    `det_eq_one_of_evenUnimodular_four`, i.e. the determinant value, so replacing evenness by
    `det = 1` reproves it for odd forms.

`OddRank34Diagonalizable` is discharged relative to the single residual local statement
`OddRank4NegDetIsotropic` (rank 4, `det = −1`, i.e. `σ = ±2`): a rank-4 form of *non-square*
discriminant is isotropic at every place, but that local fact is not a symbol condition and is not
in the banked 2-adic tooling.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.OddFormDiagonalization

namespace SKEFTHawking

open Matrix Module QuadraticForm

/-! ### Shared: odd-`p` local isotropy of the rational diagonalization

The rank-4 even-unimodular assembly `weakIsotropic_rank_four` transports
`isotropic_padicInt_of_unit_det` through the explicit congruence `A = Pᵀ · diag w · P`. Neither step
uses evenness or rank 4, so the transport is factored out here for reuse at ranks 3 and 4. -/

/-- **Odd-`p` local isotropy of the weights of a rational diagonalization.** If a symmetric unimodular
integer matrix `A` of rank `≥ 3` is rationally congruent to `diagonal w` via an invertible `P`, then the
diagonal form `∑ wᵢ xᵢ²` has a nontrivial zero over every `ℚ_[p]` with `p` odd: `A` is `ℤ_[p]`-unimodular,
so `isotropic_padicInt_of_unit_det` (rank `≥ 3`, `p ≠ 2`, unit determinant — no evenness, no
discriminant condition) gives an isotropic vector over `ℤ_[p]`, which the *same* `P` (cast to `ℚ_[p]`)
carries to the diagonal form (`matrix_isotropic_congr`). -/
theorem diag_weights_isotropic_odd_padic {n : ℕ} (hn : 3 ≤ n) (A : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : Aᵀ = A) (hunim : IsUnimodular A) {w : Fin n → ℚ} {P : Matrix (Fin n) (Fin n) ℚ}
    (hPunit : IsUnit P.det)
    (hAeq : A.map (Int.cast : ℤ → ℚ) = Pᵀ * Matrix.diagonal w * P)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ x : Fin n → ℚ_[p], x ≠ 0 ∧ ∑ i, ((w i : ℚ) : ℚ_[p]) * x i ^ 2 = 0 := by
  set φ : ℚ →+* ℚ_[p] := Rat.castHom ℚ_[p] with hφ
  -- `A` is symmetric with unit determinant over `ℤ_[p]`
  have hsymZp : (A.map (Int.castRingHom ℤ_[p])).transpose = A.map (Int.castRingHom ℤ_[p]) := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply]
    congr 1
    have := congrFun (congrFun hsymm i) j; rwa [Matrix.transpose_apply] at this
  have hunitZp : IsUnit ((A.map (Int.castRingHom ℤ_[p])).det) := by
    have hdt : (A.map (Int.castRingHom ℤ_[p])).det = (Int.castRingHom ℤ_[p]) A.det :=
      (RingHom.map_det (Int.castRingHom ℤ_[p]) A).symm
    rw [hdt]
    rcases hunim with h | h <;> rw [h] <;> simp
  obtain ⟨vp, hvp0, hvpe⟩ := isotropic_padicInt_of_unit_det hp2 hn _ hsymZp hunitZp
  -- push the `ℤ_[p]` witness into `ℚ_[p]`
  set ι : ℤ_[p] →+* ℚ_[p] := algebraMap ℤ_[p] ℚ_[p] with hι
  have hAQp_iso : ∃ x : Fin n → ℚ_[p], x ≠ 0 ∧
      x ⬝ᵥ (A.map (Int.cast : ℤ → ℚ_[p])) *ᵥ x = 0 := by
    have hinj : Function.Injective ι := FaithfulSMul.algebraMap_injective ℤ_[p] ℚ_[p]
    refine ⟨fun i => ι (vp i), fun h => hvp0 (funext fun i => ?_), ?_⟩
    · have hc := congrFun h i
      exact hinj ((show ι (vp i) = 0 by simpa using hc).trans (map_zero ι).symm)
    · have hmateq : A.map (Int.cast : ℤ → ℚ_[p])
          = (A.map (Int.castRingHom ℤ_[p])).map ι := by
        ext i j; simp [Matrix.map_apply, hι, map_intCast]
      have hg := ringHom_map_gram ι (A.map (Int.castRingHom ℤ_[p])) vp
      rw [hvpe, map_zero] at hg
      rw [hmateq]; exact hg.symm
  -- transfer along the congruence
  have hAcast : A.map (Int.cast : ℤ → ℚ_[p]) = (A.map (Int.cast : ℤ → ℚ)).map φ := by
    ext i j; simp only [Matrix.map_apply, hφ, map_intCast]
  have hAeqp : (A.map (Int.cast : ℤ → ℚ)).map φ
      = (P.map φ)ᵀ * Matrix.diagonal (fun i => φ (w i)) * (P.map φ) := by
    rw [hAeq, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
      Matrix.diagonal_map (map_zero φ)]
  have hPunitp : IsUnit (P.map φ).det := by
    have hdt : (P.map φ).det = φ P.det := (RingHom.map_det φ P).symm
    rw [hdt]; exact hPunit.map φ
  have hdiagiso : ∃ x : Fin n → ℚ_[p], x ≠ 0 ∧
      x ⬝ᵥ Matrix.diagonal (fun i => φ (w i)) *ᵥ x = 0 := by
    rw [matrix_isotropic_congr (Matrix.diagonal (fun i => φ (w i))) (P.map φ) hPunitp]
    rw [← hAeqp, ← hAcast]; exact hAQp_iso
  obtain ⟨x, hx0, hxe⟩ := hdiagiso
  refine ⟨x, hx0, ?_⟩
  rw [← hxe, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_diagonal]; simp only [hφ, Rat.coe_castHom]; ring

/-! ### Rank 3: the ternary place-`2` symbol is free by reciprocity -/

/-- **A ternary integer diagonal form in canonical Hilbert shape.** Over any field of characteristic
zero, `∑ dᵢ xᵢ² = 0` (nontrivially) iff `z² = α x² + β y²` (nontrivially) with the *integer*
coefficients `α = −d₀d₂`, `β = −d₁d₂`. Divide by `−d₂` (`isotropic_diag_ternary_iff_canonical`) and
clear the resulting denominators, both being square-class shifts (`solvable_canonical_of_sq_mul`).
This is what makes the ternary case symbol-governed at *every* place with no discriminant hypothesis:
the whole local obstruction is the single Hilbert symbol `(α, β)_v`. -/
theorem diag_ternary_iso_iff_canonical_int {K : Type*} [Field K] [CharZero K] {d : Fin 3 → ℤ}
    (h2 : d 2 ≠ 0) :
    (∃ x : Fin 3 → K, x ≠ 0 ∧ ∑ i, ((d i : ℤ) : K) * x i ^ 2 = 0) ↔
    (∃ x y z : K, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      z ^ 2 = ((-(d 0 * d 2) : ℤ) : K) * x ^ 2 + ((-(d 1 * d 2) : ℤ) : K) * y ^ 2) := by
  have h2K : ((d 2 : ℤ) : K) ≠ 0 := Int.cast_ne_zero.mpr h2
  have hstep1 : (∃ x : Fin 3 → K, x ≠ 0 ∧ ∑ i, ((d i : ℤ) : K) * x i ^ 2 = 0) ↔
      (∃ x y z : K, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
        ((d 0 : ℤ) : K) * x ^ 2 + ((d 1 : ℤ) : K) * y ^ 2 + ((d 2 : ℤ) : K) * z ^ 2 = 0) := by
    constructor
    · rintro ⟨x, hx0, hxe⟩
      exact ⟨x 0, x 1, x 2, (ne_zero_iff_three x).mp hx0,
        by rw [Fin.sum_univ_three] at hxe; linear_combination hxe⟩
    · rintro ⟨x, y, z, hnz, he⟩
      refine ⟨![x, y, z], (ne_zero_iff_three _).mpr (by simpa using hnz), ?_⟩
      rw [Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]
      linear_combination he
  rw [hstep1, isotropic_diag_ternary_iff_canonical h2K]
  refine solvable_canonical_of_sq_mul (s := (((d 2 : ℤ) : K))⁻¹) (u := (((d 2 : ℤ) : K))⁻¹)
    (inv_ne_zero h2K) (inv_ne_zero h2K) ?_ ?_
  · push_cast; field_simp
  · push_cast; field_simp

/-- **Ternary reciprocity: the place `2` is free.** A ternary integer diagonal form with nonzero
coefficients that is isotropic over `ℝ` and over every *odd* `ℚ_[p]` is isotropic over `ℚ_[2]`. At each
place the obstruction is the single symbol `(α, β)_v` with `α = −d₀d₂`, `β = −d₁d₂`
(`diag_ternary_iso_iff_canonical_int` + `hilbertReal_eq_one_iff` /
`solvable_padic_iff_hilbertPadicInt_one` / `solvable_2adic_iff_hilbert2Int`), so the Hilbert product
formula pins the `2`-factor from the others (`hilbertPrime_two_eq_one_of_real_odd`). -/
theorem diag_ternary_isotropic_2adic_of_real_odd {d : Fin 3 → ℤ}
    (h0 : d 0 ≠ 0) (h1 : d 1 ≠ 0) (h2 : d 2 ≠ 0)
    (hR : ∃ x : Fin 3 → ℝ, x ≠ 0 ∧ ∑ i, ((d i : ℤ) : ℝ) * x i ^ 2 = 0)
    (hodd : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
      ∃ x : Fin 3 → ℚ_[p], x ≠ 0 ∧ ∑ i, ((d i : ℤ) : ℚ_[p]) * x i ^ 2 = 0) :
    ∃ x : Fin 3 → ℚ_[2], x ≠ 0 ∧ ∑ i, ((d i : ℤ) : ℚ_[2]) * x i ^ 2 = 0 := by
  set α : ℤ := -(d 0 * d 2) with hα'
  set β : ℤ := -(d 1 * d 2) with hβ'
  have hα : α ≠ 0 := neg_ne_zero.mpr (mul_ne_zero h0 h2)
  have hβ : β ≠ 0 := neg_ne_zero.mpr (mul_ne_zero h1 h2)
  -- the real place
  have hreal : HilbertSymbol.hilbertReal ((α : ℤ) : ℝ) ((β : ℤ) : ℝ) = 1 := by
    obtain ⟨X, Y, Z, hnzt, het⟩ := (diag_ternary_iso_iff_canonical_int (K := ℝ) h2).mp hR
    rw [HilbertSymbol.hilbertReal_eq_one_iff (by exact_mod_cast hα) (by exact_mod_cast hβ)]
    refine ⟨X, Y, Z, ?_, het⟩
    intro h
    rw [Prod.mk_eq_zero] at h
    obtain ⟨hX, hYZ⟩ := h
    rw [Prod.mk_eq_zero] at hYZ
    exact hnzt ⟨hX, hYZ.1, hYZ.2⟩
  -- the odd places
  have hoddsym : ∀ p : ℕ, p.Prime → p ≠ 2 → HilbertSymbol.hilbertPrime p α β = 1 := by
    intro p hp hp2
    haveI := Fact.mk hp
    rw [HilbertSymbol.hilbertPrime_odd hp hp2, ← solvable_padic_iff_hilbertPadicInt_one hp2 hα hβ]
    exact (diag_ternary_iso_iff_canonical_int (K := ℚ_[p]) h2).mp (hodd p hp2)
  -- the place 2, by the product formula
  have h2sym : HilbertSymbol.hilbert2Int α β = 1 := by
    rw [← HilbertSymbol.hilbertPrime_two]
    exact hilbertPrime_two_eq_one_of_real_odd hα hβ hreal hoddsym
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (diag_ternary_iso_iff_canonical_int (K := ℚ_[2]) h2).mpr
    ((solvable_2adic_iff_hilbert2Int hα hβ).mpr h2sym)

/-! ### Rank 3 and rank-4-`det = 1`: the isotropic vector -/

/-- **Every indefinite unimodular ternary integer form has a nonzero integer isotropic vector.**
No evenness (none exists at rank 3) and no discriminant hypothesis. Diagonalize over `ℚ`
(`equivalent_weightedSumSquares_fin` + `congr_of_equiv_weighted`), clear denominators, then feed the
ternary Hasse–Minkowski `diag_ternary_zero_sum`: the real place is indefiniteness, the odd places are
`diag_weights_isotropic_odd_padic`, and the place `2` is free by reciprocity
(`diag_ternary_isotropic_2adic_of_real_odd`). -/
theorem ternary_unimodular_indefinite_isotropic (M : Matrix (Fin 3) (Fin 3) ℤ) (hsymm : Mᵀ = M)
    (hunim : IsUnimodular M)
    (hsp : 0 < sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsn : 0 < sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap') :
    ∃ v : Fin 3 → ℤ, v ≠ 0 ∧ v ⬝ᵥ M *ᵥ v = 0 := by
  apply exists_int_isotropic_of_rat M
  set Aq : Matrix (Fin 3) (Fin 3) ℚ := M.map (Int.cast : ℤ → ℚ) with hAq
  have hAqsymm : Aq.IsSymm := by
    ext i j
    rw [Matrix.transpose_apply, hAq, Matrix.map_apply, Matrix.map_apply]
    congr 1
    have := congrFun (congrFun hsymm i) j; rwa [Matrix.transpose_apply] at this
  obtain ⟨w, hwe⟩ := equivalent_weightedSumSquares_fin Aq
  obtain ⟨P, hPunit, hAeq⟩ := congr_of_equiv_weighted Aq hAqsymm hwe
  have hspq : 0 < sigPos Aq.toQuadraticMap' := sigPos_cast_pos M hsp
  have hsnq : 0 < sigNeg Aq.toQuadraticMap' := sigNeg_cast_pos M hsn
  rw [sigPos_of_equiv_weightedSumSquares hwe] at hspq
  rw [sigNeg_of_equiv_weightedSumSquares hwe] at hsnq
  obtain ⟨ip, hip⟩ : ∃ i, 0 < w i := Set.nonempty_of_ncard_ne_zero hspq.ne'
  obtain ⟨iN, hiN⟩ : ∃ i, w i < 0 := Set.nonempty_of_ncard_ne_zero hsnq.ne'
  rw [matrix_isotropic_iff_weighted Aq w hwe]
  by_cases hz : ∃ i, w i = 0
  · obtain ⟨i0, hi0⟩ := hz
    exact ⟨fun j => if j = i0 then 1 else 0, fun h => by simpa using congrFun h i0, by
      rw [Finset.sum_eq_single i0]
      · simp [hi0]
      · intro b _ hb; simp [hb]
      · intro h; simp at h⟩
  · simp only [not_exists] at hz
    set d : Fin 3 → ℤ := fun i => (w i).num * ((w i).den : ℤ) with hd
    have hdne : ∀ i, d i ≠ 0 := fun i =>
      mul_ne_zero (Rat.num_ne_zero.mpr (hz i)) (by exact_mod_cast (w i).den_nz)
    have hiff := diag_iso_rat_int (K := ℚ) w
    simp only [Rat.cast_id] at hiff
    rw [hiff]
    -- the real place
    have hR : ∃ x : Fin 3 → ℝ, x ≠ 0 ∧ ∑ i, ((d i : ℤ) : ℝ) * x i ^ 2 = 0 := by
      have hdR_pos : 0 < ((d ip : ℤ) : ℝ) := by
        rw [hd]
        have : (0 : ℤ) < (w ip).num * (w ip).den :=
          mul_pos (Rat.num_pos.mpr hip) (by exact_mod_cast (w ip).pos)
        exact_mod_cast this
      have hdR_neg : ((d iN : ℤ) : ℝ) < 0 := by
        rw [hd]
        have : (w iN).num * ((w iN).den : ℤ) < 0 :=
          mul_neg_of_neg_of_pos (Rat.num_neg.mpr hiN) (by exact_mod_cast (w iN).pos)
        exact_mod_cast this
      have hipN : ip ≠ iN := fun h => by rw [h] at hip; exact absurd (hip.trans hiN) (lt_irrefl _)
      exact diag_real_isotropic_of_signs (fun i => (d i : ℝ)) ip iN hipN hdR_pos hdR_neg
    -- the odd places
    have hoddloc : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
        ∃ x : Fin 3 → ℚ_[p], x ≠ 0 ∧ ∑ i, ((d i : ℤ) : ℚ_[p]) * x i ^ 2 = 0 := by
      intro p _ hp2
      exact (diag_iso_rat_int (K := ℚ_[p]) w).mp
        (diag_weights_isotropic_odd_padic (by norm_num) M hsymm hunim hPunit hAeq p hp2)
    -- assemble
    have hkey : ∃ x : Fin 3 → ℚ, x ≠ 0 ∧ ∑ i, ((d i : ℤ) : ℚ) * x i ^ 2 = 0 := by
      refine diag_ternary_zero_sum (fun i => ((d i : ℤ) : ℚ))
        (by show ((d 0 : ℤ) : ℚ) ≠ 0; exact_mod_cast hdne 0)
        (by show ((d 1 : ℤ) : ℚ) ≠ 0; exact_mod_cast hdne 1)
        (by show ((d 2 : ℤ) : ℚ) ≠ 0; exact_mod_cast hdne 2)
        ⟨hR.choose, hR.choose_spec.1, by
          have := hR.choose_spec.2; push_cast at this ⊢; convert this using 2⟩
        (fun p _ => ?_)
      rcases eq_or_ne p 2 with rfl | hp2
      · obtain ⟨x, hx0, hxe⟩ := diag_ternary_isotropic_2adic_of_real_odd (hdne 0) (hdne 1) (hdne 2)
          hR (fun q _ hq => hoddloc q hq)
        exact ⟨x, hx0, by push_cast at hxe ⊢; convert hxe using 2⟩
      · obtain ⟨x, hx0, hxe⟩ := hoddloc p hp2
        exact ⟨x, hx0, by push_cast at hxe ⊢; convert hxe using 2⟩
    exact hkey

/-- **A rank-4 unimodular indefinite form of determinant `+1` has a nonzero integer isotropic vector.**
Exactly `weakIsotropic_rank_four` with evenness replaced by the determinant value it was only ever used
to produce (`det_eq_one_of_evenUnimodular_four`): `det = 1` makes the ℚ-diagonalization
square-discriminant, so the odd-place input (`diag_weights_isotropic_odd_padic`) plus reciprocity
(`quaternary_sqdisc_solvable_of_local_no_two`) closes the local–global step with the place `2` free.
For an *odd* rank-4 indefinite unimodular form this is the `σ = 0` shape. -/
theorem quaternary_unimodular_det_one_isotropic (M : Matrix (Fin 4) (Fin 4) ℤ) (hsymm : Mᵀ = M)
    (hdet : M.det = 1)
    (hsp : 0 < sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsn : 0 < sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap') :
    ∃ v : Fin 4 → ℤ, v ≠ 0 ∧ v ⬝ᵥ M *ᵥ v = 0 := by
  have hunim : IsUnimodular M := Or.inl hdet
  apply exists_int_isotropic_of_rat M
  set Aq : Matrix (Fin 4) (Fin 4) ℚ := M.map (Int.cast : ℤ → ℚ) with hAq
  have hAqsymm : Aq.IsSymm := by
    ext i j
    rw [Matrix.transpose_apply, hAq, Matrix.map_apply, Matrix.map_apply]
    congr 1
    have := congrFun (congrFun hsymm i) j; rwa [Matrix.transpose_apply] at this
  have hdetq : Aq.det = 1 := by
    have h : Aq.det = ((M.det : ℤ) : ℚ) := (RingHom.map_det (Int.castRingHom ℚ) M).symm
    rw [h, hdet, Int.cast_one]
  obtain ⟨w, hwe⟩ := equivalent_weightedSumSquares_fin Aq
  obtain ⟨P, hPunit, hAeq⟩ := congr_of_equiv_weighted Aq hAqsymm hwe
  have hsqw : IsSquare (∏ i, w i) := isSquare_prod_weights Aq hAqsymm hdetq hwe
  have hspq : 0 < sigPos Aq.toQuadraticMap' := sigPos_cast_pos M hsp
  have hsnq : 0 < sigNeg Aq.toQuadraticMap' := sigNeg_cast_pos M hsn
  rw [sigPos_of_equiv_weightedSumSquares hwe] at hspq
  rw [sigNeg_of_equiv_weightedSumSquares hwe] at hsnq
  obtain ⟨ip, hip⟩ : ∃ i, 0 < w i := Set.nonempty_of_ncard_ne_zero hspq.ne'
  obtain ⟨iN, hiN⟩ : ∃ i, w i < 0 := Set.nonempty_of_ncard_ne_zero hsnq.ne'
  rw [matrix_isotropic_iff_weighted Aq w hwe]
  by_cases hz : ∃ i, w i = 0
  · obtain ⟨i0, hi0⟩ := hz
    exact ⟨fun j => if j = i0 then 1 else 0, fun h => by simpa using congrFun h i0, by
      rw [Finset.sum_eq_single i0]
      · simp [hi0]
      · intro b _ hb; simp [hb]
      · intro h; simp at h⟩
  · simp only [not_exists] at hz
    set d : Fin 4 → ℤ := fun i => (w i).num * ((w i).den : ℤ) with hd
    have hdne : ∀ i, d i ≠ 0 := fun i =>
      mul_ne_zero (Rat.num_ne_zero.mpr (hz i)) (by exact_mod_cast (w i).den_nz)
    have hiff := diag_iso_rat_int (K := ℚ) w
    simp only [Rat.cast_id] at hiff
    rw [hiff]
    have hsqd : IsSquare (d 0 * d 1 * d 2 * d 3) := by
      rw [← Rat.isSquare_intCast_iff]
      have hnum : ∀ i, ((w i).num : ℚ) = (w i) * ((w i).den : ℚ) :=
        fun i => (div_eq_iff (by exact_mod_cast (w i).den_nz)).mp (Rat.num_div_den (w i))
      have hcast : ((d 0 * d 1 * d 2 * d 3 : ℤ) : ℚ)
          = (∏ i, w i) * (((w 0).den * (w 1).den * (w 2).den * (w 3).den : ℕ) : ℚ) ^ 2 := by
        simp only [hd, Fin.prod_univ_four]
        push_cast
        rw [hnum 0, hnum 1, hnum 2, hnum 3]; ring
      rw [hcast]
      exact hsqw.mul ⟨_, pow_two _⟩
    refine diag_four_solvable_of_local_no_two hdne hsqd ?_ ?_
    · have hdR_pos : 0 < ((d ip : ℤ) : ℝ) := by
        rw [hd]
        have : (0 : ℤ) < (w ip).num * (w ip).den :=
          mul_pos (Rat.num_pos.mpr hip) (by exact_mod_cast (w ip).pos)
        exact_mod_cast this
      have hdR_neg : ((d iN : ℤ) : ℝ) < 0 := by
        rw [hd]
        have : (w iN).num * ((w iN).den : ℤ) < 0 :=
          mul_neg_of_neg_of_pos (Rat.num_neg.mpr hiN) (by exact_mod_cast (w iN).pos)
        exact_mod_cast this
      have hipN : ip ≠ iN := fun h => by rw [h] at hip; exact absurd (hip.trans hiN) (lt_irrefl _)
      exact diag_real_isotropic_of_signs (fun i => (d i : ℝ)) ip iN hipN hdR_pos hdR_neg
    · intro p _ hp2
      exact (diag_iso_rat_int (K := ℚ_[p]) w).mp
        (diag_weights_isotropic_odd_padic (by norm_num) M hsymm hunim hPunit hAeq p hp2)

/-! ### The unit peel, driven by an isotropic vector instead of the rank bound

`odd_indefinite_unit_peel` is stated for rank `≥ 5` only because
`odd_indefinite_represents_one`/`_neg_one` consume Meyer at that rank. Everything else in it — the
signature bookkeeping, and the `y = x + w`, `z = x − ε·v` correction that keeps the residual ODD — is
rank-free. Restating it with the isotropic vector as the hypothesis makes it usable at ranks 3 and 4.
The hypothesis is negation-invariant (`v ⬝ᵥ (−M) *ᵥ v = −(v ⬝ᵥ M *ᵥ v)`), so one isotropic vector
serves both the `ε = 1` and the `ε = −1` branch. -/

/-- **The unit peel from an isotropic vector.** An ODD INDEFINITE unimodular form `M` of rank `n ≥ 3`
that has a nonzero integer isotropic vector is `IntCongr` to `⟨ε⟩ ⊕ M'` with `ε = ±1` and `M'` again
odd, indefinite and unimodular of rank `n − 1`. Same proof as `odd_indefinite_unit_peel` with the
rank-`≥5` representation input replaced by `odd_unimodular_represents_one_of_isotropic` (applied to `M`
for `ε = 1`, to `−M` for `ε = −1`). -/
theorem odd_indefinite_unit_peel_of_isotropic {n : ℕ} (hn : 3 ≤ n) (M : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : Mᵀ = M) (hunim : IsUnimodular M) (i₀ : Fin n) (hodd : ¬ (2 ∣ M i₀ i₀))
    (hsp : 0 < sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsn : 0 < sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hiso : ∃ v : Fin n → ℤ, v ≠ 0 ∧ v ⬝ᵥ M *ᵥ v = 0) :
    ∃ (ε : ℤ) (M' : Matrix (Fin (n - 1)) (Fin (n - 1)) ℤ) (e : Fin 1 ⊕ Fin (n - 1) ≃ Fin n),
      (ε = 1 ∨ ε = -1) ∧
      IntCongr M (Matrix.reindex e e (Matrix.fromBlocks !![ε] 0 0 M')) ∧
      M'ᵀ = M' ∧ IsUnimodular M' ∧ (∃ j, ¬ (2 ∣ M' j j)) ∧
      0 < sigPos (M'.map (Int.cast : ℤ → ℝ)).toQuadraticMap' ∧
      0 < sigNeg (M'.map (Int.cast : ℤ → ℝ)).toQuadraticMap' := by
  classical
  obtain ⟨v₀, hv₀ne, hv₀iso⟩ := hiso
  have hle := abs_sig_add_two_le_of_indefinite M hsymm hunim hsp hsn
  obtain ⟨ε, hε, hres, x, hx⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (latticeSig M - ε).natAbs < n - 1
      ∧ ∃ x : Fin n → ℤ, x ⬝ᵥ M *ᵥ x = ε := by
    rcases le_or_gt 0 (latticeSig M) with h | h
    · obtain ⟨x, -, hx⟩ :=
        odd_unimodular_represents_one_of_isotropic M hsymm hunim i₀ hodd v₀ hv₀ne hv₀iso
      exact ⟨1, Or.inl rfl, by omega, x, hx⟩
    · have hsymm' : (-M)ᵀ = -M := by rw [Matrix.transpose_neg, hsymm]
      have hunim' : IsUnimodular (-M) := isUnimodular_neg hunim
      have hodd' : ¬ (2 ∣ (-M) i₀ i₀) := by
        simpa [Matrix.neg_apply, Int.dvd_neg] using hodd
      have hv₀iso' : v₀ ⬝ᵥ (-M) *ᵥ v₀ = 0 := by
        rw [Matrix.neg_mulVec, dotProduct_neg, hv₀iso, neg_zero]
      obtain ⟨x, -, hx⟩ :=
        odd_unimodular_represents_one_of_isotropic (-M) hsymm' hunim' i₀ hodd' v₀ hv₀ne hv₀iso'
      refine ⟨-1, Or.inr rfl, by omega, x, ?_⟩
      have hxx : x ⬝ᵥ (-M) *ᵥ x = -(x ⬝ᵥ M *ᵥ x) := by rw [Matrix.neg_mulVec, dotProduct_neg]
      omega
  have hεε : ε * ε = 1 := by rcases hε with h | h <;> rw [h] <;> ring
  have hfr := unitPerp_finrank M x (unit_linearIndependent M x ε hx hεε)
    (unit_isCompl M x ε hx hεε)
  obtain ⟨e, hcong, hunim', hsig'⟩ := unit_split_congr_of_finrank M hsymm hunim ε hε x hx hfr
  have hsymm' : (unitResidGram M x hfr)ᵀ = unitResidGram M x hfr := unitResidGram_symm M hsymm x hfr
  have hlt' : (latticeSig (unitResidGram M x hfr)).natAbs < n - 1 := by rw [hsig']; exact hres
  obtain ⟨hsp', hsn'⟩ := indefinite_of_abs_sig_lt _ hsymm' hunim' hlt'
  by_cases hM'odd : ∃ j, ¬ (2 ∣ (unitResidGram M x hfr) j j)
  · exact ⟨ε, unitResidGram M x hfr, e, hε, hcong, hsymm', hunim', hM'odd, hsp', hsn'⟩
  -- even residual: correct the vector
  push_neg at hM'odd
  have heven' : ∀ j, 2 ∣ (unitResidGram M x hfr) j j := fun j => hM'odd j
  have heu' : IsEvenUnimodular (unitResidGram M x hfr) := ⟨hsymm', hunim', heven'⟩
  obtain ⟨v₁, hv₁p, hv₁iso⟩ := hasIsotropicVector _ heu' hsp' hsn'
  obtain ⟨w₀, -, hvw₀, hw₀⟩ :=
    exists_hyperbolic_pair _ hsymm' heven' v₁ hv₁p hv₁iso hunim'
  set v : Fin n → ℤ := ∑ i, v₁ i • (unitPerpBasis M x hfr i : Fin n → ℤ) with hv
  set w : Fin n → ℤ := ∑ i, w₀ i • (unitPerpBasis M x hfr i : Fin n → ℤ) with hw
  have hxv : x ⬝ᵥ M *ᵥ v = 0 := unitPerp_mem_sum M x hfr v₁
  have hxw : x ⬝ᵥ M *ᵥ w = 0 := unitPerp_mem_sum M x hfr w₀
  have hvv : v ⬝ᵥ M *ᵥ v = 0 := by rw [hv, unitResidGram_transport]; exact hv₁iso
  have hvw : v ⬝ᵥ M *ᵥ w = 1 := by rw [hv, hw, unitResidGram_transport]; exact hvw₀
  have hww : w ⬝ᵥ M *ᵥ w = 0 := by rw [hw, unitResidGram_transport]; exact hw₀
  obtain ⟨hy, hzy, hzz⟩ := unit_correct_by_hyp_pair M hsymm ε x v w hx hxv hxw hvv hvw hww
  set y : Fin n → ℤ := x + w with hydef
  set z : Fin n → ℤ := x - ε • v with hzdef
  have hfr2 := unitPerp_finrank M y (unit_linearIndependent M y ε hy hεε)
    (unit_isCompl M y ε hy hεε)
  obtain ⟨e2, hcong2, hunim2, hsig2⟩ := unit_split_congr_of_finrank M hsymm hunim ε hε y hy hfr2
  have hsymm2 : (unitResidGram M y hfr2)ᵀ = unitResidGram M y hfr2 :=
    unitResidGram_symm M hsymm y hfr2
  have hodd2 : ∃ j, ¬ (2 ∣ (unitResidGram M y hfr2) j j) := by
    by_contra hcon
    push_neg at hcon
    have hdvd := unitResidGram_even_value M hsymm y hfr2 (fun j => hcon j) z hzy
    rw [hzz] at hdvd
    rcases hε with h | h <;> rw [h] at hdvd <;> norm_num at hdvd
  have hlt2 : (latticeSig (unitResidGram M y hfr2)).natAbs < n - 1 := by rw [hsig2]; exact hres
  obtain ⟨hsp2, hsn2⟩ := indefinite_of_abs_sig_lt _ hsymm2 hunim2 hlt2
  exact ⟨ε, unitResidGram M y hfr2, e2, hε, hcong2, hsymm2, hunim2, hodd2, hsp2, hsn2⟩

/-! ### The rank-3 and rank-4 base cases -/

/-- **The rank-3 base case, DISCHARGED.** An odd indefinite unimodular ternary form is `±1`-diagonal.
Peel a unit block with `odd_indefinite_unit_peel_of_isotropic` (fed by
`ternary_unimodular_indefinite_isotropic`); the rank-2 residual is again odd, indefinite and
unimodular, hence `oddBinary_pmDiagonal`. -/
theorem oddTernary_pmDiagonal (M : Matrix (Fin 3) (Fin 3) ℤ) (hsymm : Mᵀ = M)
    (hunim : IsUnimodular M) (hodd : ∃ i, ¬ (2 ∣ M i i))
    (hsp : 0 < sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsn : 0 < sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap') :
    ∃ N, IsPMDiagonal N ∧ IntCongr M N := by
  obtain ⟨i₀, hi₀⟩ := hodd
  obtain ⟨ε, M', e, hε, hcong, hsymm', hunim', hodd', hsp', hsn'⟩ :=
    odd_indefinite_unit_peel_of_isotropic (by norm_num) M hsymm hunim i₀ hi₀ hsp hsn
      (ternary_unimodular_indefinite_isotropic M hsymm hunim hsp hsn)
  obtain ⟨N, hN, hcongN⟩ := oddBinary_pmDiagonal M' hsymm' hunim' hodd' hsp' hsn'
  exact ⟨_, isPMDiagonal_cons ε hε e hN, hcong.trans (IntCongr.block_left e _ hcongN)⟩

/-- **The rank-4 base case, relative to one isotropic vector.** Given a nonzero integer isotropic
vector, an odd indefinite unimodular `4×4` form is `±1`-diagonal: peel once
(`odd_indefinite_unit_peel_of_isotropic`) and finish with the discharged rank-3 case. -/
theorem oddQuaternary_pmDiagonal_of_isotropic (M : Matrix (Fin 4) (Fin 4) ℤ) (hsymm : Mᵀ = M)
    (hunim : IsUnimodular M) (hodd : ∃ i, ¬ (2 ∣ M i i))
    (hsp : 0 < sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsn : 0 < sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hiso : ∃ v : Fin 4 → ℤ, v ≠ 0 ∧ v ⬝ᵥ M *ᵥ v = 0) :
    ∃ N, IsPMDiagonal N ∧ IntCongr M N := by
  obtain ⟨i₀, hi₀⟩ := hodd
  obtain ⟨ε, M', e, hε, hcong, hsymm', hunim', hodd', hsp', hsn'⟩ :=
    odd_indefinite_unit_peel_of_isotropic (by norm_num) M hsymm hunim i₀ hi₀ hsp hsn hiso
  obtain ⟨N, hN, hcongN⟩ := oddTernary_pmDiagonal M' hsymm' hunim' hodd' hsp' hsn'
  exact ⟨_, isPMDiagonal_cons ε hε e hN, hcong.trans (IntCongr.block_left e _ hcongN)⟩

end SKEFTHawking
