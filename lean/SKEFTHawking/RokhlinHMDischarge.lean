/-
# Discharging the [HM] hypothesis — Hasse–Minkowski for indefinite even unimodular forms

`RokhlinFromHM` reduces even-unimodular `8 ∣ σ` (hence `16 ∣ σ`) to the single input
`HasWeakIsotropicVectorHyp`: every indefinite even unimodular integer form has a nonzero integer isotropic
vector. This file discharges that input by assembling the local–global machinery:

* the general-rank diagonal Hasse–Minkowski spine `diag_nary_zero_of_local` (n ≤ 4 bases + n ≥ 5 Meyer
  descent), with the local hypotheses supplied by
  - ℝ: `diag_real_isotropic_of_signs` (indefinite ⟹ a `+` and a `−` coefficient),
  - odd `p`: `PadicSquare.exists_diag_nary_zero_odd_padic` (rank ≥ 5),
  - `p = 2`: `PadicSquareTwo.exists_diag_nary_zero_2adic` (rank ≥ 5 — the 2-adic frontier),
* the base-change bridge `matrix_isotropic_congr` (transfer between the Gram matrix and its ℚ-diagonalization),
* content extraction `exists_int_isotropic_of_rat` (rational ⟹ integer isotropic vector).

This file currently ships the **rank-≥5 local–global wrapper** `diag_indefinite_rat_zero`; the matrix
diagonalization + signature plumbing and the small-rank (2, 4) cases build on top toward the full
`HasWeakIsotropicVectorHyp`. Kernel-pure, no axioms.
-/

import Mathlib
import SKEFTHawking.HasseMinkowskiNary
import SKEFTHawking.PadicSquareTwo
import SKEFTHawking.LatticeContent

namespace SKEFTHawking

open scoped BigOperators
open QuadraticForm Matrix

/-! ## Signature ⟹ value bricks (for transferring indefiniteness to the diagonalization)

`sigPos > 0`/`sigNeg > 0` of a form means it takes a positive/negative value. The reusable direction we need
(a positive value forces `sigPos ≥ 1`) is `le_sigPos_of_posDef` applied to the line spanned by that value. -/

/-- A positive value of a quadratic form forces `1 ≤ sigPos` (the line it spans is positive-definite). -/
theorem one_le_sigPos_of_pos_value {K M : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup M] [Module K M] [Module.Finite K M] (Q : QuadraticForm K M) (x : M)
    (hx : 0 < Q x) : 1 ≤ sigPos Q := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hposdef : (Q.restrict (Submodule.span K {x})).PosDef := by
    intro v hv
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp v.2
    have hvval : (v : M) = t • x := ht.symm
    have htne : t ≠ 0 := by
      rintro rfl; simp only [zero_smul] at hvval
      exact hv (Subtype.ext (by simpa using hvval))
    show 0 < Q.restrict _ v
    rw [QuadraticMap.restrict_apply, hvval, QuadraticMap.map_smul, smul_eq_mul]
    exact mul_pos (mul_self_pos.mpr htne) hx
  have hfr : Module.finrank K (Submodule.span K {x}) = 1 := finrank_span_singleton hx0
  calc 1 = Module.finrank K (Submodule.span K {x}) := hfr.symm
    _ ≤ sigPos Q := le_sigPos_of_posDef Q hposdef

/-- A negative value of a quadratic form forces `1 ≤ sigNeg` (via `sigNeg Q = sigPos (-Q)`). -/
theorem one_le_sigNeg_of_neg_value {K M : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup M] [Module K M] [Module.Finite K M] (Q : QuadraticForm K M) (x : M)
    (hx : Q x < 0) : 1 ≤ sigNeg Q := by
  rw [← sigPos_neg]
  exact one_le_sigPos_of_pos_value (-Q) x (by rw [QuadraticMap.neg_apply]; exact neg_pos.mpr hx)

/-! ## ℝ → ℚ signature positivity transfer (by density)

`sigPos`/`sigNeg` of a rational form is not known to Mathlib to be scalar-extension invariant, but POSITIVITY
transfers ℝ → ℚ by density: a positive (resp. negative) value of the real form gives, via density of `ℚ^m` in
`ℝ^m` and continuity, a positive (resp. negative) value of the rational form, which forces `sigPos`/`sigNeg`
of the rational form to be `≥ 1`. This converts the ℝ-stated indefiniteness hypotheses of
`HasWeakIsotropicVectorHyp` into the ℚ-side input needed to feed the ℚ-diagonalization to the spine. -/

/-- **`sigPos` positivity transfers ℝ → ℚ.** If the real Gram form has `sigPos > 0`, so does the rational
Gram form (a real positive value yields a rational one by density of `ℚ^m`, then `one_le_sigPos_of_pos_value`). -/
theorem sigPos_cast_pos {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ)
    (hsp : 0 < sigPos (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap') :
    0 < sigPos (A.map (Int.cast : ℤ → ℚ)).toQuadraticMap' := by
  obtain ⟨V, hVdim, hVpd⟩ :=
    exists_finrank_eq_sigPos_and_posDef (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap'
  have hVne : V ≠ ⊥ := by rintro rfl; rw [finrank_bot] at hVdim; omega
  obtain ⟨y, hyV, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVne
  have hQy : 0 < y ⬝ᵥ (A.map (Int.cast : ℤ → ℝ)) *ᵥ y := by
    have := hVpd ⟨y, hyV⟩ (by simp [hy0])
    rwa [QuadraticMap.restrict_apply, toQuadraticMap'_apply] at this
  set B : Matrix (Fin m) (Fin m) ℝ := A.map (Int.cast : ℤ → ℝ) with hB
  have hcont : Continuous (fun z : Fin m → ℝ => z ⬝ᵥ B *ᵥ z) := by
    unfold dotProduct Matrix.mulVec dotProduct; fun_prop
  have hUopen : IsOpen {z : Fin m → ℝ | 0 < z ⬝ᵥ B *ᵥ z} := isOpen_lt continuous_const hcont
  have hdense : DenseRange (fun (q : Fin m → ℚ) (i : Fin m) => ((q i : ℝ))) := by
    have h : (Set.range (fun (q : Fin m → ℚ) (i : Fin m) => ((q i : ℝ))))
        = Set.univ.pi (fun _ : Fin m => Set.range ((↑) : ℚ → ℝ)) := by
      ext z; simp only [Set.mem_range, Set.mem_univ_pi]
      refine ⟨?_, ?_⟩
      · rintro ⟨q, rfl⟩ i; exact ⟨q i, rfl⟩
      · intro h; choose q hq using h; exact ⟨q, funext fun i => hq i⟩
    rw [DenseRange, h]; exact dense_pi Set.univ (fun i _ => Rat.denseRange_cast)
  obtain ⟨x, hx⟩ := hdense.exists_mem_open hUopen ⟨y, hQy⟩
  have hcast : (fun i => ((x i : ℝ))) ⬝ᵥ B *ᵥ (fun i => ((x i : ℝ)))
      = ((x ⬝ᵥ (A.map (Int.cast : ℤ → ℚ)) *ᵥ x : ℚ) : ℝ) := by
    simp only [dotProduct, Matrix.mulVec, hB, Matrix.map_apply]; push_cast; rfl
  rw [Set.mem_setOf_eq, hcast] at hx
  have hQqx : 0 < x ⬝ᵥ (A.map (Int.cast : ℤ → ℚ)) *ᵥ x := by exact_mod_cast hx
  exact one_le_sigPos_of_pos_value _ x (by rwa [toQuadraticMap'_apply])

/-- **`sigNeg` positivity transfers ℝ → ℚ.** Dual of `sigPos_cast_pos` (negative value, via the negated
form's `posDef` subspace and `one_le_sigNeg_of_neg_value`). -/
theorem sigNeg_cast_pos {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ)
    (hsn : 0 < sigNeg (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap') :
    0 < sigNeg (A.map (Int.cast : ℤ → ℚ)).toQuadraticMap' := by
  obtain ⟨V, hVdim, hVpd⟩ :=
    exists_finrank_eq_sigPos_and_posDef (-(A.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
  rw [sigPos_neg] at hVdim
  have hVne : V ≠ ⊥ := by rintro rfl; rw [finrank_bot] at hVdim; omega
  obtain ⟨y, hyV, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVne
  have hQy : y ⬝ᵥ (A.map (Int.cast : ℤ → ℝ)) *ᵥ y < 0 := by
    have := hVpd ⟨y, hyV⟩ (by simp [hy0])
    rw [QuadraticMap.restrict_apply, QuadraticMap.neg_apply, toQuadraticMap'_apply] at this
    linarith
  set B : Matrix (Fin m) (Fin m) ℝ := A.map (Int.cast : ℤ → ℝ) with hB
  have hcont : Continuous (fun z : Fin m → ℝ => z ⬝ᵥ B *ᵥ z) := by
    unfold dotProduct Matrix.mulVec dotProduct; fun_prop
  have hUopen : IsOpen {z : Fin m → ℝ | z ⬝ᵥ B *ᵥ z < 0} := isOpen_lt hcont continuous_const
  have hdense : DenseRange (fun (q : Fin m → ℚ) (i : Fin m) => ((q i : ℝ))) := by
    have h : (Set.range (fun (q : Fin m → ℚ) (i : Fin m) => ((q i : ℝ))))
        = Set.univ.pi (fun _ : Fin m => Set.range ((↑) : ℚ → ℝ)) := by
      ext z; simp only [Set.mem_range, Set.mem_univ_pi]
      refine ⟨?_, ?_⟩
      · rintro ⟨q, rfl⟩ i; exact ⟨q i, rfl⟩
      · intro h; choose q hq using h; exact ⟨q, funext fun i => hq i⟩
    rw [DenseRange, h]; exact dense_pi Set.univ (fun i _ => Rat.denseRange_cast)
  obtain ⟨x, hx⟩ := hdense.exists_mem_open hUopen ⟨y, hQy⟩
  have hcast : (fun i => ((x i : ℝ))) ⬝ᵥ B *ᵥ (fun i => ((x i : ℝ)))
      = ((x ⬝ᵥ (A.map (Int.cast : ℤ → ℚ)) *ᵥ x : ℚ) : ℝ) := by
    simp only [dotProduct, Matrix.mulVec, hB, Matrix.map_apply]; push_cast; rfl
  rw [Set.mem_setOf_eq, hcast] at hx
  have hQqx : x ⬝ᵥ (A.map (Int.cast : ℤ → ℚ)) *ᵥ x < 0 := by exact_mod_cast hx
  exact one_le_sigNeg_of_neg_value _ x (by rwa [toQuadraticMap'_apply])

/-- **Local–global for an indefinite integer diagonal form (rank ≥ 5).** A diagonal form `∑ cᵢ xᵢ²` of
rank `n ≥ 5` with nonzero integer coefficients that is indefinite over ℝ (a positive and a negative
coefficient) has a nontrivial rational zero. The local hypotheses of `diag_nary_zero_of_local` are all
automatic at this rank: ℝ from indefiniteness (`diag_real_isotropic_of_signs`), odd `p` from
`exists_diag_nary_zero_odd_padic`, and `p = 2` from `exists_diag_nary_zero_2adic`. This is the clean payoff
of the closed 2-adic frontier — the local input that was missing is now total. -/
theorem diag_indefinite_rat_zero {n : ℕ} (hn : 5 ≤ n) (c : Fin n → ℤ) (hc : ∀ i, c i ≠ 0)
    (hpos : ∃ i, 0 < c i) (hneg : ∃ j, c j < 0) :
    ∃ x : Fin n → ℚ, x ≠ 0 ∧ ∑ i, (c i : ℚ) * x i ^ 2 = 0 := by
  apply diag_nary_zero_of_local n c hc
  · obtain ⟨i, hi⟩ := hpos; obtain ⟨j, hj⟩ := hneg
    have hij : i ≠ j := by rintro rfl; omega
    exact diag_real_isotropic_of_signs (fun i => (c i : ℝ)) i j hij
      (Int.cast_pos.mpr hi) (Int.cast_lt_zero.mpr hj)
  · intro p _
    rcases eq_or_ne p 2 with rfl | hp2
    · exact exists_diag_nary_zero_2adic hn (fun i => (c i : ℚ_[2]))
        (fun i => Int.cast_ne_zero.mpr (hc i))
    · exact exists_diag_nary_zero_odd_padic hp2 hn (fun i => (c i : ℚ_[p]))
        (fun i => Int.cast_ne_zero.mpr (hc i))

/-! ## Rank-≥5 weak isotropy (the main case of [HM])

For rank `≥ 5`, indefiniteness alone (no even-unimodularity needed) gives an integer isotropic vector:
diagonalize over ℚ, transfer indefiniteness to the rational weights (`sigPos/sigNeg_cast_pos` +
`sig*_of_equiv_weightedSumSquares`), then either a zero weight gives a trivial isotropic vector or the
rank-≥5 local–global wrapper `diag_indefinite_rat_zero` applies to the cleared-denominator integer form. -/

/-- **Weak [HM] for rank ≥ 5.** An indefinite integer Gram form of rank `≥ 5` (positive `sigPos` and
`sigNeg` over ℝ) has a nonzero integer isotropic vector. Even-unimodularity is *not* required at this rank —
local isotropy over every `ℚ_p` is automatic for rank-≥5 diagonal forms. -/
theorem weakIsotropic_of_five_le {m : ℕ} (hm : 5 ≤ m) (A : Matrix (Fin m) (Fin m) ℤ)
    (hsp : 0 < sigPos (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsn : 0 < sigNeg (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap') :
    ∃ v : Fin m → ℤ, v ≠ 0 ∧ v ⬝ᵥ A *ᵥ v = 0 := by
  apply exists_int_isotropic_of_rat A
  set Aq : Matrix (Fin m) (Fin m) ℚ := A.map (Int.cast : ℤ → ℚ) with hAq
  obtain ⟨w, hwe⟩ := QuadraticForm.equivalent_weightedSumSquares Aq.toQuadraticMap'
  have hspq : 0 < sigPos Aq.toQuadraticMap' := sigPos_cast_pos A hsp
  have hsnq : 0 < sigNeg Aq.toQuadraticMap' := sigNeg_cast_pos A hsn
  rw [sigPos_of_equiv_weightedSumSquares hwe] at hspq
  rw [sigNeg_of_equiv_weightedSumSquares hwe] at hsnq
  obtain ⟨ip, hip⟩ : ∃ i, 0 < w i := Set.nonempty_of_ncard_ne_zero hspq.ne'
  obtain ⟨iN, hiN⟩ : ∃ i, w i < 0 := Set.nonempty_of_ncard_ne_zero hsnq.ne'
  rw [matrix_isotropic_iff_weighted Aq w hwe]
  by_cases hz : ∃ i, w i = 0
  · obtain ⟨i0, hi0⟩ := hz
    refine ⟨fun j => if j = i0 then 1 else 0, ?_, ?_⟩
    · intro h; have := congrFun h i0; simp at this
    · rw [Finset.sum_eq_single i0]
      · simp [hi0]
      · intro b _ hb; simp [hb]
      · intro h; simp at h
  · simp only [not_exists] at hz
    have hn : Module.finrank ℚ (Fin m → ℚ) = m := Module.finrank_fin_fun ℚ
    set d : Fin (Module.finrank ℚ (Fin m → ℚ)) → ℤ := fun i => (w i).num * ((w i).den : ℤ) with hd
    have hdne : ∀ i, d i ≠ 0 := by
      intro i; rw [hd]; simp only
      exact mul_ne_zero (Rat.num_ne_zero.mpr (hz i)) (by exact_mod_cast (w i).den_nz)
    have hdpos : ∃ i, 0 < d i := ⟨ip, by rw [hd]; positivity⟩
    have hdneg : ∃ i, d i < 0 := by
      refine ⟨iN, ?_⟩; rw [hd]; simp only
      have hnum : (w iN).num < 0 := Rat.num_neg.mpr hiN
      have hden : (0 : ℤ) < (w iN).den := by exact_mod_cast (w iN).pos
      exact mul_neg_of_neg_of_pos hnum hden
    have h5n : 5 ≤ Module.finrank ℚ (Fin m → ℚ) := by rw [hn]; exact hm
    obtain ⟨x, hx0, hxe⟩ := diag_indefinite_rat_zero h5n d hdne hdpos hdneg
    have hiff := diag_iso_rat_int (K := ℚ) w
    simp only [Rat.cast_id] at hiff
    rw [hiff]
    exact ⟨x, hx0, hxe⟩

end SKEFTHawking
