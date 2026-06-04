/-
Phase 5q.B: the indefinite-case input [HM] — local solvability bricks toward "an indefinite even unimodular
form has a primitive isotropic vector" (Hasse–Minkowski / Meyer).

This is one of the two remaining classical inputs to van der Blij (`VanDerBlijReduction.eight_dvd_latticeSig
_of_HM_of_Theta`). The full statement decomposes (anti-circular, no ABP):
  [HM-ℝ]   indefinite ⟹ represents 0 over ℝ (elementary; `sigPos>0 ∧ sigNeg>0`).
  [HM-p]   a nondegenerate (unimodular) form of rank ≥ 3 represents 0 over ℚ_p, for every prime `p`:
            • `p` odd: the reduction mod `p` is isotropic over 𝔽_p (THIS FILE: `finite_field_form_isotropic`,
              via Chevalley–Warning), then Hensel-lift (`Mathlib`'s Hensel) to ℤ_p;
            • `p = 2`: an even unimodular form of rank ≥ 3 over ℤ_2 contains a hyperbolic plane.
  [HM-LG]  Hasse–Minkowski local-global: solvable over ℝ and all ℚ_p ⟹ solvable over ℚ. (The frontier:
            needs the Hilbert symbol + its product formula + Dirichlet on primes in AP for rank 3,4 — not yet
            in Mathlib.)
  [HM-ℤ]   a ℚ-isotropic vector of a unimodular ℤ-form scales to a primitive ℤ-isotropic vector (elementary).

`finite_field_form_isotropic` is the residue-field core of [HM-p] at odd primes — a genuine, kernel-pure,
classical result built directly on Mathlib's Chevalley–Warning (`char_dvd_card_solutions`): over a finite
field, a symmetric form in `≥ 3` variables has a nonzero zero (the number of zeros is divisible by the
characteristic and includes `0`, so exceeds one).

All proofs are kernel-pure (`propext`/`Classical.choice`/`Quot.sound` only); no `native_decide`, no
`maxHeartbeats`, no axiom.
-/

import Mathlib

namespace SKEFTHawking

open Matrix MvPolynomial QuadraticMap

/-- **A symmetric form over a finite field in `≥ 3` variables is isotropic.** For a finite field `K` and a
matrix `A` over `K` with `3 ≤ n`, there is a nonzero `x` with `xᵀ A x = 0`. Proof via Chevalley–Warning: the
quadratic polynomial `∑ᵢⱼ Aᵢⱼ Xᵢ Xⱼ` has total degree `≤ 2 < n`, so its number of zeros is divisible by
`char K = p`; the zero vector is a solution, so there are at least `p ≥ 2` solutions, hence a nonzero one.
This is the residue-field core of the local solvability [HM-p] at odd primes. -/
theorem finite_field_form_isotropic {K : Type*} [Field K] [Fintype K] {n : ℕ} (hn : 3 ≤ n)
    (A : Matrix (Fin n) (Fin n) K) : ∃ x : Fin n → K, x ≠ 0 ∧ x ⬝ᵥ A *ᵥ x = 0 := by
  classical
  obtain ⟨p, hp⟩ := CharP.exists K
  haveI : Fact p.Prime := Fact.mk (CharP.char_is_prime K p)
  set P : MvPolynomial (Fin n) K := ∑ i, ∑ j, C (A i j) * X i * X j with hP
  have hterm : ∀ i j : Fin n, (C (A i j) * X i * X j : MvPolynomial (Fin n) K).totalDegree ≤ 2 := by
    intro i j
    have e1 := totalDegree_mul (C (A i j) * X i) (X j : MvPolynomial (Fin n) K)
    have e2 := totalDegree_mul (C (A i j)) (X i : MvPolynomial (Fin n) K)
    have e3 : (C (A i j) : MvPolynomial (Fin n) K).totalDegree = 0 := totalDegree_C _
    have e4 : (X i : MvPolynomial (Fin n) K).totalDegree = 1 := totalDegree_X i
    have e5 : (X j : MvPolynomial (Fin n) K).totalDegree = 1 := totalDegree_X j
    omega
  have hP2 : P.totalDegree ≤ 2 := by
    rw [hP]
    apply (totalDegree_finset_sum _ _).trans
    apply Finset.sup_le; intro i _
    apply (totalDegree_finset_sum _ _).trans
    apply Finset.sup_le; intro j _
    exact hterm i j
  have hdeg : P.totalDegree < Fintype.card (Fin n) := by rw [Fintype.card_fin]; omega
  have heval : ∀ x : Fin n → K, eval x P = x ⬝ᵥ A *ᵥ x := by
    intro x
    rw [hP]
    simp only [map_sum, map_mul, eval_C, eval_X]
    rw [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hsol := char_dvd_card_solutions (K := K) (p := p) hdeg
  have h0 : eval (0 : Fin n → K) P = 0 := by rw [heval]; simp
  have hcard : 1 < Fintype.card {x : Fin n → K // eval x P = 0} := by
    have hpos : 0 < Fintype.card {x : Fin n → K // eval x P = 0} :=
      Fintype.card_pos_iff.mpr ⟨⟨0, h0⟩⟩
    have hple := Nat.le_of_dvd hpos hsol
    have h2 := (Fact.out : p.Prime).two_le
    omega
  obtain ⟨⟨y, hy⟩, hne⟩ := Fintype.exists_ne_of_one_lt_card hcard ⟨0, h0⟩
  refine ⟨y, ?_, ?_⟩
  · intro hy0; exact hne (by subst hy0; rfl)
  · rw [← heval]; exact hy

/-- **[HM-ℝ] — an indefinite real quadratic form represents zero nontrivially.** If both inertia indices are
positive, pick `u` with `Q u > 0` and `w` with `Q w < 0`; then `Q(r•u + w) = Qu·r² + polar·r + Qw` is a real
quadratic in `r` with discriminant `polar² - 4·Qu·Qw > 0` (since `Qu·Qw < 0`), so it has a real root, giving a
nonzero isotropic vector. Elementary; the real-place input of Hasse–Minkowski [HM]. -/
theorem indefinite_repr_zero {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (Q : QuadraticForm ℝ V) (hp : 0 < sigPos Q) (hn : 0 < sigNeg Q) :
    ∃ x : V, x ≠ 0 ∧ Q x = 0 := by
  obtain ⟨Vp, hVp, hVppos⟩ := exists_finrank_eq_sigPos_and_posDef Q
  have hVpne : Vp ≠ ⊥ := fun h => by rw [h, finrank_bot] at hVp; omega
  obtain ⟨u, huVp, hu0⟩ := Vp.exists_mem_ne_zero_of_ne_bot hVpne
  have hQu : 0 < Q u := by
    have := hVppos ⟨u, huVp⟩ (by simpa [Subtype.ext_iff] using hu0)
    rwa [restrict_apply] at this
  obtain ⟨Vn, hVn, hVnpos⟩ := exists_finrank_eq_sigPos_and_posDef (-Q)
  have hVnne : Vn ≠ ⊥ := fun h => by rw [h, finrank_bot] at hVn; rw [sigNeg] at hn; omega
  obtain ⟨w, hwVn, hw0⟩ := Vn.exists_mem_ne_zero_of_ne_bot hVnne
  have hQw : Q w < 0 := by
    have := hVnpos ⟨w, hwVn⟩ (by simpa [Subtype.ext_iff] using hw0)
    rw [restrict_apply, QuadraticMap.neg_apply] at this; linarith
  set b := polar (⇑Q) u w with hb
  have hD : 0 ≤ b ^ 2 - 4 * Q u * Q w := by nlinarith [mul_pos hQu (neg_pos.mpr hQw)]
  set r := (-b + Real.sqrt (b ^ 2 - 4 * Q u * Q w)) / (2 * Q u) with hr
  have hexp : Q (r • u + w) = Q u * r ^ 2 + b * r + Q w := by
    have h1 : Q (r • u + w) = polar (⇑Q) (r • u) w + Q (r • u) + Q w := by
      simp only [polar]; ring
    rw [h1, Q.map_smul, polar_smul_left, hb]
    simp only [smul_eq_mul]; ring
  have hQune : Q u ≠ 0 := ne_of_gt hQu
  have hroot : Q (r • u + w) = 0 := by
    rw [hexp, hr]
    set s := Real.sqrt (b ^ 2 - 4 * Q u * Q w) with hsdef
    have hs : s ^ 2 = b ^ 2 - 4 * Q u * Q w := by rw [hsdef]; exact Real.sq_sqrt hD
    field_simp
    linear_combination hs
  refine ⟨r • u + w, ?_, hroot⟩
  intro hzero
  have hw_eq : w = -(r • u) := eq_neg_of_add_eq_zero_right hzero
  rw [hw_eq, QuadraticMap.map_neg, Q.map_smul, smul_eq_mul] at hQw
  nlinarith [mul_nonneg (mul_self_nonneg r) hQu.le]

/-- **[HM-ℝ], matrix form.** An indefinite real symmetric matrix form represents zero nontrivially:
`∃ x ≠ 0, xᵀ A x = 0`. This is the shape consumed by the [HM] application (the isotropic vector is for the
bilinear value `x ⬝ᵥ A *ᵥ x`). -/
theorem indefinite_matrix_repr_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hp : 0 < sigPos A.toQuadraticMap') (hn : 0 < sigNeg A.toQuadraticMap') :
    ∃ x : Fin n → ℝ, x ≠ 0 ∧ x ⬝ᵥ A *ᵥ x = 0 := by
  obtain ⟨x, hx0, hQx⟩ := indefinite_repr_zero A.toQuadraticMap' hp hn
  refine ⟨x, hx0, ?_⟩
  have happ : A.toQuadraticMap' x = x ⬝ᵥ A *ᵥ x := by
    simp [Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply']
  rwa [happ] at hQx

/-! ## Diagonalization scaffold: matrix ↔ quadratic-map and isotropy transfer

These connect the Gram-matrix isotropy shape `x ⬝ᵥ M *ᵥ x = 0` (consumed by the [HM] application) to the
abstract `QuadraticMap` API, so that Mathlib's diagonalization (`equivalent_weightedSumSquares`, over any
field with `Invertible 2`) can be applied at each completion `ℝ`/`ℚ_p` and the resulting diagonal isotropy
transported back. -/

/-- **Matrix quadratic-map apply.** `M.toQuadraticMap' x = x ⬝ᵥ M *ᵥ x` (the bilinear value). -/
theorem toQuadraticMap'_apply {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (x : n → R) : M.toQuadraticMap' x = x ⬝ᵥ M *ᵥ x := by
  simp [Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply']

/-- **Isotropy transfers across an isometric equivalence.** Equivalent quadratic maps are simultaneously
isotropic: `(∃ x ≠ 0, Q₁ x = 0) ↔ (∃ x ≠ 0, Q₂ x = 0)`. The workhorse for transporting a diagonalized
form's isotropy back to the original Gram form. -/
theorem exists_ne_zero_isotropic_congr {R M₁ M₂ N : Type*} [CommRing R] [AddCommMonoid M₁]
    [AddCommMonoid M₂] [AddCommMonoid N] [Module R M₁] [Module R M₂] [Module R N]
    {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N} (h : Q₁.Equivalent Q₂) :
    (∃ x : M₁, x ≠ 0 ∧ Q₁ x = 0) ↔ (∃ x : M₂, x ≠ 0 ∧ Q₂ x = 0) := by
  obtain ⟨f⟩ := h
  constructor
  · rintro ⟨x, hx, hQ⟩
    refine ⟨f x, ?_, by rw [f.map_app]; exact hQ⟩
    intro hfx; apply hx; have : f x = f 0 := by rw [hfx, map_zero]
    exact EquivLike.injective f this
  · rintro ⟨y, hy, hQ⟩
    refine ⟨f.symm y, ?_, ?_⟩
    · intro hfy; apply hy; have : f.symm y = f.symm 0 := by rw [hfy, map_zero]
      exact EquivLike.injective f.symm this
    · have key := f.map_app (f.symm y)
      rw [f.apply_symm_apply] at key
      rw [← key]; exact hQ

end SKEFTHawking
