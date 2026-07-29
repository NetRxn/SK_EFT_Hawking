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
  - rank 4 with `det = 1` (`σ = 0`): square discriminant, so
    `quaternary_sqdisc_solvable_of_local_no_two` applies verbatim — the *only* use of evenness in
    `weakIsotropic_rank_four` was `det_eq_one_of_evenUnimodular_four`, i.e. the determinant value, so
    replacing evenness by `det = 1` reproves it for odd forms.
  - rank 4 with `det = −1` (`σ = ±2`): NON-square discriminant, so reciprocity does not close it and
    the place `2` is settled directly in `ℚ_[2]`. With `α = −d₀d₁`, `β = −d₂d₃` and `αβ = −s²`:
    either `α` or `β` is a square, in which case that *binary* is already isotropic
    (`exists_binary_zero_iff`) and we are done; or `α` and `−α` are both non-squares (because
    `(−α)·β = s²`), and then `exists_hilbert2Int_witness` produces `g` with `(g,α)₂ = −1`,
    `(g,−1)₂ = 1`, so `{1, g, −1, −g}` realizes *every* prescription of the pair `((t,α)₂, (t,−1)₂)`
    — which is exactly the common-value condition, since `(t,α)₂·(t,β)₂ = (t,−1)₂`. The local–global
    step is then the full rank-4 Hasse–Minkowski `diag_quaternary_zero_sum_int`.

Consequence: **`OddRank34Diagonalizable` is a theorem** (`oddRank34Diagonalizable`), so Milnor–
Husemoller II.4.3 is unconditional here (`odd_indefinite_pmDiagonal_unconditional`,
`odd_indefinite_intCongr_unconditional`), and `EvenUnimodularIndefiniteSplit.StableNegRank16` reduces
to **Wall's characteristic-vector transitivity alone**.

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

/-! ### Rank 4 with `det = −1`: the place `2` from the `ℚ_[2]` square classes

`σ = ±2` means `det = −1`, i.e. **non-square discriminant**, so the square-discriminant reciprocity of
`quaternary_sqdisc_solvable_of_local_no_two` does not apply and the place `2` must be done by hand.
It is not a symbol *identity* but a symbol *solvability* question: with `α = −d₀d₁`, `β = −d₂d₃` and
`αβ = −s²`, the quaternary is isotropic over `ℚ_[2]` as soon as some `t ≠ 0` is represented by both
binaries, i.e. `(t,α)₂ = (d₀,d₁)₂` and `(t,β)₂ = (−d₂,−d₃)₂`. Since `α·β ≡ −1` mod squares,
`(t,α)₂·(t,β)₂ = (t,−1)₂`, so the two conditions are a prescription for the pair `((t,α)₂, (t,−1)₂)`,
and the pair is realizable because `α ∉ {1, −1}` mod `(ℚ_[2]ˣ)²` — which is exactly the case left
after the two degenerate branches (`α` or `β` a square) are dispatched by an *isotropic binary*. -/

/-- Squareness is invariant under multiplying by a nonzero square. -/
theorem isSquare_mul_sq_iff {K : Type*} [Field K] {c s : K} (hs : s ≠ 0) :
    IsSquare (c * s ^ 2) ↔ IsSquare c := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r / s, by field_simp; linear_combination hr⟩
  · rintro ⟨r, hr⟩
    exact ⟨r * s, by rw [hr]; ring⟩

/-- **2-adic square criterion for an odd integer**: `u` is a square in `ℚ_[2]` iff `u ≡ 1 (mod 8)`.
(`isSquare_padic_coe_iff` moves the question into `ℤ_[2]`, where
`isSquare_iff_toZModPow_three_eq_one` is the mod-8 test.) -/
theorem isSquare_2adic_intCast_odd_iff {u : ℤ} (hu : ¬ (2 : ℤ) ∣ u) :
    IsSquare ((u : ℤ) : ℚ_[2]) ↔ ((u : ℤ) : ZMod 8) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hunit : IsUnit ((u : ℤ_[2])) := padicInt_intCast_isUnit (by exact_mod_cast hu)
  have hcast : (((u : ℤ_[2])) : ℚ_[2]) = ((u : ℤ) : ℚ_[2]) := by push_cast; ring
  rw [← hcast, isSquare_padic_coe_iff hunit, isSquare_iff_toZModPow_three_eq_one hunit]
  have hmap : PadicInt.toZModPow 3 ((u : ℤ_[2])) = ((u : ℤ) : ZMod (2 ^ 3)) := map_intCast _ u
  rw [hmap]

/-- **The two non-square, non-`(−1)` unit classes mod 8 are `3` and `5`, where `ω = 1`.** The finite
kernel of the rank-4 place-`2` argument: `u ≡ 1 (mod 8)` is the square class and `u ≡ 7 (mod 8)` the
`−1` class, and on what remains `(2, u)₂ = χ₂(ω(u)) = −1`. -/
theorem omega2_eq_one_of_unit_ne_one_ne_seven :
    ∀ y : ZMod 8, IsUnit y → y ≠ 1 → y ≠ 7 → HilbertSymbol.omega2 y = 1 := by decide

/-- **A `ℚ_[2]`-symbol witness in the kernel of `(·, −1)₂`.** If neither `α` nor `−α` is a square in
`ℚ_[2]` then there is `g ≠ 0` with `(g, α)₂ = −1` and `(g, −1)₂ = 1`. Reduce `α` to its canonical
class `c · σ²` (`exists_canonical_padic_factor`): if `c = 2c'` take `g = 5` (`(5,2)₂ = −1`,
`(5, odd)₂ = 1`); if `c` is odd then `c ≢ 1, 7 (mod 8)` by the two non-square hypotheses, so
`c ≡ 3, 5 (mod 8)`, where `ω(c) = 1` and `g = 2` works. In both cases `(g, −1)₂ = 1`. -/
theorem exists_hilbert2Int_witness {α : ℤ} (hα : α ≠ 0)
    (hns : ¬ IsSquare ((α : ℤ) : ℚ_[2])) (hnsneg : ¬ IsSquare (((-α) : ℤ) : ℚ_[2])) :
    ∃ g : ℤ, g ≠ 0 ∧ HilbertSymbol.hilbert2Int g α = -1 ∧
      HilbertSymbol.hilbert2Int g (-1) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, σ, hσ, hαeq, hc⟩ := exists_canonical_padic_factor (p := 2) hα
  have hc0 : c ≠ 0 := by rintro rfl; rw [zero_mul] at hαeq; exact hα hαeq
  simp only [Nat.cast_ofNat] at hc
  rcases hc with hcodd | ⟨c', hc'odd, rfl⟩
  · -- `α ≡ c` with `c` odd
    have hc'0 : ((c : ℤ) : ℚ_[2]) ≠ 0 := by
      exact_mod_cast hc0
    have hsqc : ¬ IsSquare ((c : ℤ) : ℚ_[2]) := by
      intro h
      refine hns ?_
      rw [hαeq]
      push_cast
      exact (isSquare_mul_sq_iff (c := ((c : ℤ) : ℚ_[2])) (s := ((σ : ℤ) : ℚ_[2]))
        (by exact_mod_cast hσ)).mpr h
    have hsqcneg : ¬ IsSquare (((-c) : ℤ) : ℚ_[2]) := by
      intro h
      refine hnsneg ?_
      have : ((-α : ℤ) : ℚ_[2]) = ((-c : ℤ) : ℚ_[2]) * ((σ : ℤ) : ℚ_[2]) ^ 2 := by
        rw [hαeq]; push_cast; ring
      rw [this]
      exact (isSquare_mul_sq_iff (c := ((-c : ℤ) : ℚ_[2])) (s := ((σ : ℤ) : ℚ_[2]))
        (by exact_mod_cast hσ)).mpr h
    have hne1 : ((c : ℤ) : ZMod 8) ≠ 1 := fun h =>
      hsqc ((isSquare_2adic_intCast_odd_iff hcodd).mpr h)
    have hne7 : ((c : ℤ) : ZMod 8) ≠ 7 := by
      intro h
      refine hsqcneg ((isSquare_2adic_intCast_odd_iff (u := -c) ?_).mpr ?_)
      · simpa using hcodd
      · push_cast at h ⊢; rw [h]; decide
    have hunit8 : IsUnit ((c : ℤ) : ZMod 8) := HilbertSymbol.isUnit_intCast_zmod8 hcodd
    have homega : HilbertSymbol.omega2 ((c : ℤ) : ZMod 8) = 1 :=
      omega2_eq_one_of_unit_ne_one_ne_seven _ hunit8 hne1 hne7
    refine ⟨2, two_ne_zero, ?_, ?_⟩
    · rw [hαeq, hilbert2Int_mul_sq_right two_ne_zero hc0 hσ,
        HilbertSymbol.hilbert2Int_two_odd hcodd, homega]
      exact HilbertSymbol.chi2_one
    · rw [HilbertSymbol.hilbert2Int_comm]
      exact HilbertSymbol.hilbert2Int_neg_one_two
  · -- `α ≡ 2c'` with `c'` odd
    have hc'0 : c' ≠ 0 := by rintro rfl; exact hc'odd ⟨0, by ring⟩
    have hcc : (2 : ℤ) * c' ≠ 0 := mul_ne_zero two_ne_zero hc'0
    have h5odd : ¬ (2 : ℤ) ∣ 5 := by decide
    refine ⟨5, by norm_num, ?_, ?_⟩
    · rw [hαeq, hilbert2Int_mul_sq_right (by norm_num) hcc hσ,
        HilbertSymbol.hilbert2Int_mul_right two_ne_zero hc'0]
      have h52 : HilbertSymbol.hilbert2Int 5 2 = -1 := by
        rw [HilbertSymbol.hilbert2Int_comm, HilbertSymbol.hilbert2Int_two_odd h5odd]
        decide
      -- v4.32: `decide` now refuses a goal whose context still carries free variables it would
      -- have to ignore, and points at `+revert` to clean them up first. The decided propositions
      -- (`eps2 5 = 0`, `chi2 0 = 1`) are unchanged closed facts about `ZMod 8` literals.
      have h5c : HilbertSymbol.hilbert2Int 5 c' = 1 := by
        rw [HilbertSymbol.hilbert2Int_odd_odd h5odd hc'odd,
          show ((5 : ℤ) : ZMod 8) = 5 from by decide,
          show HilbertSymbol.eps2 (5 : ZMod 8) = 0 from by decide +revert, zero_mul]
        decide +revert
      rw [h52, h5c]; ring
    · rw [HilbertSymbol.hilbert2Int_comm, HilbertSymbol.hilbert2Int_neg_one_odd h5odd,
        show ((5 : ℤ) : ZMod 8) = 5 from by decide,
        show HilbertSymbol.eps2 (5 : ZMod 8) = 0 from by decide +revert]
      decide +revert

/-- **Place-`2` isotropy of a quaternary of discriminant `−square`.** A diagonal integer quaternary
with `d₀d₁d₂d₃ = −s²` (`s ≠ 0`) is isotropic over `ℚ_[2]`. If `α = −d₀d₁` is a square the binary
`⟨d₀,d₁⟩` is already isotropic (`exists_binary_zero_iff`); likewise for `β = −d₂d₃`. Otherwise both
`α` and `−α` are non-squares (`(−α)·β = s²`), so `exists_hilbert2Int_witness` supplies `g` with
`(g,α)₂ = −1`, `(g,−1)₂ = 1`; together with `t = 1, −1, −g` this realizes every prescription of the
pair `((t,α)₂, (t,−1)₂)`, hence a common represented value for `⟨d₀,d₁⟩` and `⟨−d₂,−d₃⟩`
(`represents_2adic_iff_symbol_linear` + `quaternary_isotropic_of_common_value`). -/
theorem diag_quaternary_isotropic_2adic_of_neg_sq_prod {d : Fin 4 → ℤ} (hd : ∀ i, d i ≠ 0)
    {s : ℤ} (hs : s ≠ 0) (hprod : d 0 * d 1 * d 2 * d 3 = -(s ^ 2)) :
    ∃ x : Fin 4 → ℚ_[2], x ≠ 0 ∧ ∑ i, ((d i : ℤ) : ℚ_[2]) * x i ^ 2 = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set α : ℤ := -(d 0 * d 1) with hαdef
  set β : ℤ := -(d 2 * d 3) with hβdef
  have hα : α ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (hd 0) (hd 1))
  have hβ : β ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (hd 2) (hd 3))
  have hmk : ∀ x y z w : ℚ_[2], ¬(x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) →
      ((d 0 : ℤ) : ℚ_[2]) * x ^ 2 + ((d 1 : ℤ) : ℚ_[2]) * y ^ 2
        + ((d 2 : ℤ) : ℚ_[2]) * z ^ 2 + ((d 3 : ℤ) : ℚ_[2]) * w ^ 2 = 0 →
      ∃ v : Fin 4 → ℚ_[2], v ≠ 0 ∧ ∑ i, ((d i : ℤ) : ℚ_[2]) * v i ^ 2 = 0 := by
    intro x y z w hnz he
    refine ⟨![x, y, z, w], (ne_zero_iff_four _).mpr (by simpa using hnz), ?_⟩
    rw [Fin.sum_univ_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons]
    linear_combination he
  by_cases hsqα : IsSquare ((α : ℤ) : ℚ_[2])
  · obtain ⟨x, y, hxy, he⟩ :=
      (exists_binary_zero_iff (K := ℚ_[2]) (a := ((d 0 : ℤ) : ℚ_[2])) (b := ((d 1 : ℤ) : ℚ_[2]))
        (by exact_mod_cast hd 0)).mpr
        (by rw [show -(((d 0 : ℤ) : ℚ_[2]) * ((d 1 : ℤ) : ℚ_[2])) = ((α : ℤ) : ℚ_[2]) from by
              rw [hαdef]; push_cast; ring]
            exact hsqα)
    exact hmk x y 0 0 (fun h => hxy ⟨h.1, h.2.1⟩) (by linear_combination he)
  by_cases hsqβ : IsSquare ((β : ℤ) : ℚ_[2])
  · obtain ⟨z, w, hzw, he⟩ :=
      (exists_binary_zero_iff (K := ℚ_[2]) (a := ((d 2 : ℤ) : ℚ_[2])) (b := ((d 3 : ℤ) : ℚ_[2]))
        (by exact_mod_cast hd 2)).mpr
        (by rw [show -(((d 2 : ℤ) : ℚ_[2]) * ((d 3 : ℤ) : ℚ_[2])) = ((β : ℤ) : ℚ_[2]) from by
              rw [hβdef]; push_cast; ring]
            exact hsqβ)
    exact hmk 0 0 z w (fun h => hzw ⟨h.2.2.1, h.2.2.2⟩) (by linear_combination he)
  -- both `α` and `β` non-square: `(−α)·β = s²`, so `−α` is non-square too
  have hαβ : α * β = -(s ^ 2) := by rw [hαdef, hβdef]; linear_combination hprod
  have hnegα : ¬ IsSquare (((-α) : ℤ) : ℚ_[2]) := by
    rintro ⟨r, hr⟩
    have hrne : r ≠ 0 := by
      intro h; rw [h, mul_zero] at hr
      exact (neg_ne_zero.mpr hα) (by exact_mod_cast hr)
    refine hsqβ ⟨((s : ℤ) : ℚ_[2]) / r, ?_⟩
    have hcast : (((-α) : ℤ) : ℚ_[2]) * ((β : ℤ) : ℚ_[2]) = ((s : ℤ) : ℚ_[2]) ^ 2 := by
      have : ((-α * β : ℤ) : ℚ_[2]) = ((s ^ 2 : ℤ) : ℚ_[2]) := by rw [show -α * β = s ^ 2 from by
        linear_combination -hαβ]
      push_cast at this ⊢; linear_combination this
    rw [hr] at hcast
    field_simp
    linear_combination hcast
  obtain ⟨g, hg0, hgα, hgν⟩ := exists_hilbert2Int_witness hα hsqα hnegα
  -- the symbol prescription for the common value
  set s₁ : ℤ := HilbertSymbol.hilbert2Int (d 0) (d 1) with hs₁def
  set s₂ : ℤ := HilbertSymbol.hilbert2Int (-(d 2)) (-(d 3)) with hs₂def
  have hs₁mem : s₁ = 1 ∨ s₁ = -1 := HilbertSymbol.hilbert2Int_mem _ _
  have hs₂mem : s₂ = 1 ∨ s₂ = -1 := HilbertSymbol.hilbert2Int_mem _ _
  have hprodχ : ∀ t : ℤ, t ≠ 0 → HilbertSymbol.hilbert2Int t α * HilbertSymbol.hilbert2Int t β
      = HilbertSymbol.hilbert2Int t (-1) := by
    intro t ht
    rw [← HilbertSymbol.hilbert2Int_mul_right hα hβ, hαβ,
      show -(s ^ 2) = (-1) * s ^ 2 from by ring, hilbert2Int_mul_sq_right ht (by norm_num) hs]
  -- realize any prescription of `((t,α)₂, (t,−1)₂)`
  have hpair : ∀ σ₁ σ₂ : ℤ, (σ₁ = 1 ∨ σ₁ = -1) → (σ₂ = 1 ∨ σ₂ = -1) →
      ∃ t : ℤ, t ≠ 0 ∧ HilbertSymbol.hilbert2Int t α = σ₁ ∧
        HilbertSymbol.hilbert2Int t (-1) = σ₂ := by
    intro σ₁ σ₂ h₁ h₂
    have hc := HilbertSymbol.hilbert2Int_mem (-1 : ℤ) α
    rcases h₂ with rfl | rfl
    · rcases h₁ with rfl | rfl
      · exact ⟨1, one_ne_zero, HilbertSymbol.hilbert2Int_one_left _,
          HilbertSymbol.hilbert2Int_one_left _⟩
      · exact ⟨g, hg0, hgα, hgν⟩
    · have hneg1 : HilbertSymbol.hilbert2Int (-1 : ℤ) (-1) = -1 :=
        HilbertSymbol.hilbert2Int_neg_one_neg_one
      have hgneg : HilbertSymbol.hilbert2Int (-g) α = -HilbertSymbol.hilbert2Int (-1 : ℤ) α := by
        rw [show -g = (-1 : ℤ) * g from by ring,
          HilbertSymbol.hilbert2Int_mul_left (by norm_num) hg0, hgα]
        ring
      have hgnegν : HilbertSymbol.hilbert2Int (-g) (-1) = -1 := by
        rw [show -g = (-1 : ℤ) * g from by ring,
          HilbertSymbol.hilbert2Int_mul_left (by norm_num) hg0, hgν, hneg1]
        ring
      rcases h₁ with rfl | rfl
      · rcases hc with hc1 | hc1
        · exact ⟨-1, by norm_num, hc1, hneg1⟩
        · exact ⟨-g, neg_ne_zero.mpr hg0, by rw [hgneg, hc1]; ring, hgnegν⟩
      · rcases hc with hc1 | hc1
        · exact ⟨-g, neg_ne_zero.mpr hg0, by rw [hgneg, hc1], hgnegν⟩
        · exact ⟨-1, by norm_num, hc1, hneg1⟩
  obtain ⟨t, ht0, htα, htν⟩ := hpair s₁ (s₁ * s₂) hs₁mem
    (by rcases hs₁mem with h | h <;> rcases hs₂mem with h' | h' <;> rw [h, h'] <;> norm_num)
  have htβ : HilbertSymbol.hilbert2Int t β = s₂ := by
    have h := hprodχ t ht0
    rw [htα, htν] at h
    rcases hs₁mem with h1 | h1 <;> rw [h1] at h <;> linarith
  -- the common value gives the isotropic vector
  have hrep1 : ∃ u v : ℚ_[2], ((d 0 : ℤ) : ℚ_[2]) * u ^ 2 + ((d 1 : ℤ) : ℚ_[2]) * v ^ 2
      = ((t : ℤ) : ℚ_[2]) :=
    (represents_2adic_iff_symbol_linear (hd 0) (hd 1) ht0).mpr htα
  have hrep2 : ∃ u v : ℚ_[2], (((-(d 2)) : ℤ) : ℚ_[2]) * u ^ 2 + (((-(d 3)) : ℤ) : ℚ_[2]) * v ^ 2
      = ((t : ℤ) : ℚ_[2]) := by
    refine (represents_2adic_iff_symbol_linear (neg_ne_zero.mpr (hd 2))
      (neg_ne_zero.mpr (hd 3)) ht0).mpr ?_
    rw [show -(-(d 2) * -(d 3)) = β from by rw [hβdef]; ring]
    exact htβ
  obtain ⟨x, y, z, w, hnz, he⟩ := quaternary_isotropic_of_common_value
    (K := ℚ_[2]) (a := ((d 0 : ℤ) : ℚ_[2])) (b := ((d 1 : ℤ) : ℚ_[2]))
    (c := (((-(d 2)) : ℤ) : ℚ_[2])) (d := (((-(d 3)) : ℤ) : ℚ_[2]))
    (t := ((t : ℤ) : ℚ_[2])) (by exact_mod_cast ht0) hrep1 hrep2
  refine hmk x y z w hnz ?_
  push_cast at he ⊢
  linear_combination he

/-- **`det = −1` pins the discriminant of the diagonalization to `−square`.** If a symmetric `det = −1`
Gram form over `ℚ` is isometric to `∑ wᵢ xᵢ²`, then `−∏ wᵢ = (det P)⁻²`. The `det = −1` companion of
`isSquare_prod_weights`. -/
theorem isSquare_neg_prod_weights {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : A.IsSymm)
    (hdet : A.det = -1) {w : Fin n → ℚ}
    (hwe : A.toQuadraticMap'.Equivalent (QuadraticMap.weightedSumSquares ℚ w)) :
    IsSquare (-(∏ i, w i)) := by
  obtain ⟨P, hPunit, hAeq⟩ := congr_of_equiv_weighted A hA hwe
  have key : A.det = P.det ^ 2 * ∏ i, w i := by
    rw [hAeq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]; ring
  rw [hdet] at key
  have hne : P.det ≠ 0 := hPunit.ne_zero
  exact ⟨P.det⁻¹, by field_simp; linear_combination key⟩

/-- **A rank-4 unimodular indefinite form of determinant `−1` has a nonzero integer isotropic vector.**
The `σ = ±2` (non-square discriminant) companion of `quaternary_unimodular_det_one_isotropic`. The
odd places and `ℝ` are as before; the place `2` is `diag_quaternary_isotropic_2adic_of_neg_sq_prod`,
whose hypothesis `∏ dᵢ = −s²` is exactly what `det = −1` gives (`isSquare_neg_prod_weights`). The
local–global step is then the *full* rank-4 Hasse–Minkowski `diag_quaternary_zero_sum_int`. -/
theorem quaternary_unimodular_det_neg_one_isotropic (M : Matrix (Fin 4) (Fin 4) ℤ) (hsymm : Mᵀ = M)
    (hdet : M.det = -1)
    (hsp : 0 < sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsn : 0 < sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap') :
    ∃ v : Fin 4 → ℤ, v ≠ 0 ∧ v ⬝ᵥ M *ᵥ v = 0 := by
  have hunim : IsUnimodular M := Or.inr hdet
  apply exists_int_isotropic_of_rat M
  set Aq : Matrix (Fin 4) (Fin 4) ℚ := M.map (Int.cast : ℤ → ℚ) with hAq
  have hAqsymm : Aq.IsSymm := by
    ext i j
    rw [Matrix.transpose_apply, hAq, Matrix.map_apply, Matrix.map_apply]
    congr 1
    have := congrFun (congrFun hsymm i) j; rwa [Matrix.transpose_apply] at this
  have hdetq : Aq.det = -1 := by
    have h : Aq.det = ((M.det : ℤ) : ℚ) := (RingHom.map_det (Int.castRingHom ℚ) M).symm
    rw [h, hdet]; norm_num
  obtain ⟨w, hwe⟩ := equivalent_weightedSumSquares_fin Aq
  obtain ⟨P, hPunit, hAeq⟩ := congr_of_equiv_weighted Aq hAqsymm hwe
  have hsqw : IsSquare (-(∏ i, w i)) := isSquare_neg_prod_weights Aq hAqsymm hdetq hwe
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
    -- the discriminant of the cleared form is `−square`
    have hsqd : IsSquare (-(d 0 * d 1 * d 2 * d 3)) := by
      rw [← Rat.isSquare_intCast_iff]
      have hnum : ∀ i, ((w i).num : ℚ) = (w i) * ((w i).den : ℚ) :=
        fun i => (div_eq_iff (by exact_mod_cast (w i).den_nz)).mp (Rat.num_div_den (w i))
      have hcast : ((-(d 0 * d 1 * d 2 * d 3) : ℤ) : ℚ)
          = (-(∏ i, w i)) * (((w 0).den * (w 1).den * (w 2).den * (w 3).den : ℕ) : ℚ) ^ 2 := by
        simp only [hd, Fin.prod_univ_four]
        push_cast
        rw [hnum 0, hnum 1, hnum 2, hnum 3]; ring
      rw [hcast]
      exact hsqw.mul ⟨_, pow_two _⟩
    obtain ⟨s, hsdef⟩ := hsqd
    have hprod : d 0 * d 1 * d 2 * d 3 = -(s ^ 2) := by rw [pow_two]; linear_combination -hsdef
    have hs0 : s ≠ 0 := by
      have hne : d 0 * d 1 * d 2 * d 3 ≠ 0 :=
        mul_ne_zero (mul_ne_zero (mul_ne_zero (hdne 0) (hdne 1)) (hdne 2)) (hdne 3)
      intro h
      rw [h] at hprod
      exact hne (by rw [hprod]; norm_num)
    -- the real place
    have hR : ∃ x : Fin 4 → ℝ, x ≠ 0 ∧ ∑ i, ((d i : ℤ) : ℝ) * x i ^ 2 = 0 := by
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
    refine diag_quaternary_zero_sum_int d (hdne 0) (hdne 1) (hdne 2) (hdne 3) hR (fun p _ => ?_)
    rcases eq_or_ne p 2 with rfl | hp2
    · exact diag_quaternary_isotropic_2adic_of_neg_sq_prod hdne hs0 hprod
    · exact (diag_iso_rat_int (K := ℚ_[p]) w).mp
        (diag_weights_isotropic_odd_padic (by norm_num) M hsymm hunim hPunit hAeq p hp2)

/-! ### `OddRank34Diagonalizable` — DISCHARGED -/

/-- **Every indefinite unimodular `4×4` integer form has a nonzero integer isotropic vector.** Both
determinant shapes: `det = 1` (`σ = 0`, square discriminant, reciprocity) and `det = −1` (`σ = ±2`,
non-square discriminant, the `ℚ_[2]` square-class argument). No evenness, no oddness. -/
theorem quaternary_unimodular_indefinite_isotropic (M : Matrix (Fin 4) (Fin 4) ℤ) (hsymm : Mᵀ = M)
    (hunim : IsUnimodular M)
    (hsp : 0 < sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsn : 0 < sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap') :
    ∃ v : Fin 4 → ℤ, v ≠ 0 ∧ v ⬝ᵥ M *ᵥ v = 0 := by
  rcases hunim with h | h
  · exact quaternary_unimodular_det_one_isotropic M hsymm h hsp hsn
  · exact quaternary_unimodular_det_neg_one_isotropic M hsymm h hsp hsn

/-- **THE RANK-3/4 BASE-CASE INTERFACE IS A THEOREM.** `OddFormDiagonalization.OddRank34Diagonalizable`
— the sole residue of Milnor–Husemoller II.4.3 — holds unconditionally. -/
theorem oddRank34Diagonalizable : OddRank34Diagonalizable := by
  intro n h3 h4 M hsymm hunim hodd hsp hsn
  interval_cases n
  · exact oddTernary_pmDiagonal M hsymm hunim hodd hsp hsn
  · exact oddQuaternary_pmDiagonal_of_isotropic M hsymm hunim hodd hsp hsn
      (quaternary_unimodular_indefinite_isotropic M hsymm hunim hsp hsn)

/-- **Milnor–Husemoller II.4.3, UNCONDITIONAL.** An odd indefinite unimodular integer form is
congruent to `⟨1⟩^p ⊕ ⟨−1⟩^q`. -/
theorem odd_indefinite_pmDiagonal_unconditional {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : Mᵀ = M) (hunim : IsUnimodular M) (hodd : ∃ i, ¬ (2 ∣ M i i))
    (hsp : 0 < sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsn : 0 < sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap') :
    ∃ N, IsPMDiagonal N ∧ IntCongr M N :=
  odd_indefinite_pmDiagonal oddRank34Diagonalizable M hsymm hunim hodd hsp hsn

/-- **Odd indefinite unimodular forms are classified by rank and signature, UNCONDITIONAL** — the
form of II.4.3 the `StableNegRank16` assembly consumes. -/
theorem odd_indefinite_intCongr_unconditional {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℤ)
    (hsymmM : Mᵀ = M) (hunimM : IsUnimodular M) (hoddM : ∃ i, ¬ (2 ∣ M i i))
    (hspM : 0 < sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsnM : 0 < sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsymmN : Nᵀ = N) (hunimN : IsUnimodular N) (hoddN : ∃ i, ¬ (2 ∣ N i i))
    (hspN : 0 < sigPos (N.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsnN : 0 < sigNeg (N.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsig : latticeSig M = latticeSig N) : IntCongr M N :=
  odd_indefinite_intCongr oddRank34Diagonalizable M N hsymmM hunimM hoddM hspM hsnM
    hsymmN hunimN hoddN hspN hsnN hsig

end SKEFTHawking
