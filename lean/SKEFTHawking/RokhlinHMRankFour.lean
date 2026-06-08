/-
# Rank-4 Hasse–Minkowski: local isotropy of even unimodular forms

The weak [HM] hypothesis (`RokhlinFromHM.HasWeakIsotropicVectorHyp`) is discharged at rank ≥ 5
(`RokhlinHMDischarge.weakIsotropic_of_five_le`) and at ranks 1, 2, 3 (elementary / vacuous). The lone
remaining rank is **4**, the sub-frontier where local universality fails (anisotropic rank-4 forms exist
over each `ℚ_p`). For an *even unimodular* form the local inputs are nonetheless available:

* **odd `p`** — the form is `ℤ_p`-unimodular, so its mod-`p` reduction is a nondegenerate rank-4 form over
  `𝔽_p`, isotropic by Chevalley–Warning (`finite_field_form_isotropic`); the isotropic point is automatically
  *simple* (nondegeneracy ⟹ nonzero gradient), so a single-variable Hensel lift (`hensels_lemma`) produces a
  `ℚ_p`-isotropic vector. This file builds that input (`evenUnimodular_isotropic_odd_padic`).

The reusable engine is `mulVec_update_coord_quadratic`: varying one coordinate `j` of a vector turns the
quadratic form into a univariate quadratic `A j j · t² + 2·(A *ᵥ y) j · t + y ⬝ᵥ A *ᵥ y`, which is the
polynomial Hensel acts on.

Kernel-pure, no axioms.
-/

import Mathlib
import SKEFTHawking.AlgebraicRokhlin
import SKEFTHawking.HasseMinkowskiLocal
import SKEFTHawking.PadicSquare
import SKEFTHawking.HilbertProductFormula
import SKEFTHawking.RokhlinHMDischarge
import SKEFTHawking.RokhlinFromHM

namespace SKEFTHawking

open scoped BigOperators
open Matrix QuadraticForm

/-- **One-coordinate variation of a quadratic form is a univariate quadratic.** For a symmetric matrix
`A`, replacing coordinate `j` of `y` by `t` (where `y j = 0`) gives
`(y + t·e_j) ⬝ᵥ A *ᵥ (y + t·e_j) = A j j · t² + 2·(A *ᵥ y) j · t + y ⬝ᵥ A *ᵥ y`. The cross terms coincide
by symmetry of `A`. This is the polynomial Hensel's lemma acts on for the local lift. -/
theorem mulVec_update_coord_quadratic {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (hsymm : A.transpose = A) (y : Fin n → R) (j : Fin n) (t : R) :
    (y + t • (Pi.single j 1 : Fin n → R)) ⬝ᵥ A *ᵥ (y + t • (Pi.single j 1 : Fin n → R))
      = A j j * t ^ 2 + 2 * (A *ᵥ y) j * t + y ⬝ᵥ A *ᵥ y := by
  have hsingle : A *ᵥ (Pi.single j 1 : Fin n → R) = fun i => A i j := by
    ext i; rw [mulVec_single]; simp
  have hyAe : y ⬝ᵥ A *ᵥ (Pi.single j 1 : Fin n → R) = (A *ᵥ y) j := by
    rw [hsingle]
    show ∑ i, y i * A i j = (A *ᵥ y) j
    rw [mulVec]
    show ∑ i, y i * A i j = ∑ i, A j i * y i
    refine Finset.sum_congr rfl fun i _ => ?_
    have hij : A i j = A j i := by
      have h := congrFun (congrFun hsymm j) i; rwa [Matrix.transpose_apply] at h
    rw [hij]; ring
  have heAe : (Pi.single j (1 : R)) ⬝ᵥ A *ᵥ Pi.single j (1 : R) = A j j := by
    rw [hsingle, single_dotProduct]; simp
  have heAy : (Pi.single j (1 : R)) ⬝ᵥ A *ᵥ y = (A *ᵥ y) j := by
    rw [single_dotProduct]; simp
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct,
    mulVec_smul, dotProduct_smul, dotProduct_smul, smul_dotProduct, smul_dotProduct,
    hyAe, heAe, heAy]
  simp only [smul_eq_mul]
  ring

open Polynomial in
/-- **Odd-`p` local isotropy of a `ℤ_p`-unimodular form (rank ≥ 3).** A symmetric matrix over `ℤ_[p]`
(`p` odd) with unit determinant is isotropic over `ℤ_[p]` (hence `ℚ_[p]`). Its mod-`p` reduction is a
nondegenerate rank-≥3 form over `𝔽_p`, isotropic by Chevalley–Warning; the isotropic point is *simple*
(nondegeneracy ⟹ the gradient `Ā *ᵥ x̄` is nonzero), so a single-variable Hensel lift in the
gradient-nonzero coordinate produces an exact `ℤ_[p]` zero. -/
theorem isotropic_padicInt_of_unit_det {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {n : ℕ} (hn : 3 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℤ_[p]) (hsymm : A.transpose = A) (hdet : IsUnit A.det) :
    ∃ v : Fin n → ℤ_[p], v ≠ 0 ∧ v ⬝ᵥ A *ᵥ v = 0 := by
  classical
  set f : ℤ_[p] →+* ZMod p := PadicInt.toZMod with hf
  set Abar : Matrix (Fin n) (Fin n) (ZMod p) := A.map f with hAbar
  -- mod-p reduction is nondegenerate
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have hdetbar : Abar.det ≠ 0 := by
    have hd : Abar.det = f A.det := by rw [hAbar]; exact (RingHom.map_det f A).symm
    rw [hd]; exact (hdet.map f).ne_zero
  -- the residue form is isotropic (Chevalley–Warning, rank ≥ 3)
  obtain ⟨xbar, hxbar0, hxbarz⟩ := finite_field_form_isotropic (K := ZMod p) hn Abar
  -- the isotropic point is simple: the gradient is nonzero
  have hgrad : Abar *ᵥ xbar ≠ 0 := by
    intro h
    exact hdetbar (Matrix.exists_mulVec_eq_zero_iff.mp ⟨xbar, hxbar0, h⟩)
  obtain ⟨j, hj⟩ : ∃ j, (Abar *ᵥ xbar) j ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hgrad (funext h)
  -- lift the residue solution to ℤ_[p]
  have hlift : ∀ i, ∃ X : ℤ_[p], f X = xbar i := fun i => ZMod.ringHom_surjective f (xbar i)
  choose x0 hx0 using hlift
  have hx0fun : (fun k => f (x0 k)) = xbar := funext hx0
  -- map-commutes for the matrix-vector product
  have hmapmv : ∀ (w : Fin n → ℤ_[p]) (i : Fin n),
      f ((A *ᵥ w) i) = (Abar *ᵥ (fun k => f (w k))) i := by
    intro w i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hAbar, Matrix.map_apply]
  -- zero out coordinate j
  set y : Fin n → ℤ_[p] := Function.update x0 j 0 with hy
  set a : ℤ_[p] := x0 j with ha
  have hrestore : x0 = y + a • (Pi.single j 1 : Fin n → ℤ_[p]) := by
    ext i; rcases eq_or_ne i j with rfl | hij
    · simp [hy, ha]
    · simp [hy, Function.update_of_ne hij, Pi.single_eq_of_ne hij]
  -- the Hensel polynomial
  set F : ℤ_[p][X] := C (A j j) * X ^ 2 + C (2 * (A *ᵥ y) j) * X + C (y ⬝ᵥ A *ᵥ y) with hF
  have hFe : ∀ x : ℤ_[p], (aeval x) F = A j j * x ^ 2 + 2 * (A *ᵥ y) j * x + y ⬝ᵥ A *ᵥ y := by
    intro x; simp [hF]
  have hFda : (aeval a) (derivative F) = 2 * A j j * a + 2 * (A *ᵥ y) j := by
    simp [hF, derivative_add, derivative_mul]; ring
  -- F at a evaluates to the full quadratic Q(x0)
  have hQx0 : (aeval a) F = x0 ⬝ᵥ A *ᵥ x0 := by
    rw [hFe]
    have h := mulVec_update_coord_quadratic A hsymm y j a
    rw [← hrestore] at h; rw [h]
  -- F'(a) = 2·(A *ᵥ x0) j
  have hgradx0 : 2 * A j j * a + 2 * (A *ᵥ y) j = 2 * (A *ᵥ x0) j := by
    have : (A *ᵥ x0) j = (A *ᵥ y) j + a * A j j := by
      rw [hrestore]
      simp [Matrix.mulVec_add, Matrix.mulVec_smul, mulVec_single]
    rw [this]; ring
  -- residue facts
  have hmod0 : f (x0 ⬝ᵥ A *ᵥ x0) = 0 := by
    have : f (x0 ⬝ᵥ A *ᵥ x0) = xbar ⬝ᵥ Abar *ᵥ xbar := by
      simp only [dotProduct, map_sum, map_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hx0, hmapmv x0 i, hx0fun]
    rw [this, hxbarz]
  have h2 : f (2 : ℤ_[p]) ≠ 0 := by
    have he : f (2 : ℤ_[p]) = ((2 : ℕ) : ZMod p) := by
      rw [hf, show (2 : ℤ_[p]) = ((2 : ℕ) : ℤ_[p]) by norm_num, map_natCast]
    rw [he, Ne, CharP.cast_eq_zero_iff (ZMod p) p 2]
    intro hdvd
    exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hdvd)
  have hderiv_ne : f ((aeval a) (derivative F)) ≠ 0 := by
    rw [hFda, hgradx0, map_mul, hmapmv x0 j, hx0fun]
    exact mul_ne_zero h2 hj
  -- Hensel lift
  have ha1 : ‖(aeval a) (derivative F)‖ = 1 := by
    rcases lt_or_eq_of_le (PadicInt.norm_le_one ((aeval a) (derivative F))) with h | h
    · exact absurd ((toZMod_eq_zero_iff_norm_lt_one _).mpr h) hderiv_ne
    · exact h
  have hnorm : ‖(aeval a) F‖ < ‖(aeval a) (derivative F)‖ ^ 2 := by
    rw [ha1, one_pow]
    rw [hQx0]
    exact (toZMod_eq_zero_iff_norm_lt_one _).mp hmod0
  obtain ⟨z, hz, _⟩ := hensels_lemma (F := F) (a := a) hnorm
  -- assemble the lifted isotropic vector
  refine ⟨y + z • (Pi.single j 1 : Fin n → ℤ_[p]), ?_, ?_⟩
  · -- nonzero
    intro hv0
    have hsupp : ∀ i, i ≠ j → xbar i = 0 := by
      intro i hij
      have hvi := congrFun hv0 i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hij, smul_zero, add_zero,
        Pi.zero_apply, hy, Function.update_of_ne hij] at hvi
      rw [← hx0 i, hvi, map_zero]
    have hxbarj : xbar j ≠ 0 := by
      intro hjz
      refine hxbar0 (funext fun i => ?_)
      rcases eq_or_ne i j with rfl | h
      · exact hjz
      · exact hsupp i h
    have hgv : (Abar *ᵥ xbar) j = Abar j j * xbar j := by
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single j]
      · intro b _ hb; rw [hsupp b hb, mul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    have hquad : Abar j j * xbar j ^ 2 = 0 := by
      have := hxbarz
      rw [dotProduct, Finset.sum_eq_single j] at this
      · rw [hgv] at this; rw [← this]; ring
      · intro b _ hb; rw [hsupp b hb, zero_mul]
      · intro h; exact absurd (Finset.mem_univ j) h
    have hAbarjj : Abar j j = 0 := by
      rcases mul_eq_zero.mp hquad with h | h
      · exact h
      · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) hxbarj
    rw [hgv, hAbarjj, zero_mul] at hj; exact hj rfl
  · -- isotropic
    have h := mulVec_update_coord_quadratic A hsymm y j z
    rw [h, ← hFe z]; exact hz

/-- **Weighted sum of squares is the diagonal Gram form.** `∑ wᵢ xᵢ² = x ⬝ᵥ diag(w) *ᵥ x`. The bridge from
the abstract diagonalization `QuadraticForm.equivalent_weightedSumSquares` to a concrete diagonal matrix,
so the discriminant `∏ wᵢ = det (diag w)` is exposed for the square-discriminant computation. -/
theorem weightedSumSquares_eq_diagonal {K : Type*} [CommRing K] {n : ℕ} (w : Fin n → K) :
    QuadraticMap.weightedSumSquares K w = (Matrix.diagonal w).toQuadraticMap' := by
  ext x
  rw [QuadraticMap.weightedSumSquares_apply, toQuadraticMap'_apply, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mulVec_diagonal, smul_eq_mul, sq]; ring

/-- **`toMatrix'` inverts `toQuadraticMap'` on symmetric matrices.** Over ℚ, a symmetric Gram matrix is
recovered from its quadratic form. -/
theorem toMatrix'_toQuadraticMap' {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (hM : M.IsSymm) :
    (M.toQuadraticMap').toMatrix' = M := by
  have hsymm : ∀ x y : Fin n → ℚ,
      (Matrix.toLinearMap₂' ℚ M) x y = (Matrix.toLinearMap₂' ℚ M) y x := by
    intro x y
    rw [Matrix.toLinearMap₂'_apply', Matrix.toLinearMap₂'_apply',
        Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose, hM.eq]
  rw [QuadraticMap.toMatrix', Matrix.toQuadraticMap',
      QuadraticMap.associated_left_inverse (S := ℚ) hsymm, LinearMap.toMatrix'_toLinearMap₂']

/-- **Explicit rational congruence to the diagonalization.** A symmetric Gram form over ℚ isometric to
`∑ wᵢ xᵢ²` is matrix-congruent to `diagonal w` via the (invertible) change-of-basis `P = toMatrix' e`.
Exposing `P` lets the congruence cast to every completion `ℝ`/`ℚ_p` (feeding `matrix_isotropic_congr`). -/
theorem congr_of_equiv_weighted {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : A.IsSymm)
    {w : Fin n → ℚ} (hwe : A.toQuadraticMap'.Equivalent (QuadraticMap.weightedSumSquares ℚ w)) :
    ∃ P : Matrix (Fin n) (Fin n) ℚ, IsUnit P.det ∧ A = Pᵀ * Matrix.diagonal w * P := by
  obtain ⟨e⟩ := hwe
  refine ⟨LinearMap.toMatrix' e.toLinearEquiv.toLinearMap, ?_, ?_⟩
  · have hmul : (LinearMap.toMatrix' e.toLinearEquiv.toLinearMap).det
        * (LinearMap.toMatrix' e.toLinearEquiv.symm.toLinearMap).det = 1 := by
      rw [← Matrix.det_mul, ← LinearMap.toMatrix'_comp,
          show e.toLinearEquiv.toLinearMap ∘ₗ e.toLinearEquiv.symm.toLinearMap = LinearMap.id from by
            ext x; simp, LinearMap.toMatrix'_id, Matrix.det_one]
    exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one hmul)
  · have hWM : (QuadraticMap.weightedSumSquares ℚ w).toMatrix' = Matrix.diagonal w := by
      rw [weightedSumSquares_eq_diagonal, toMatrix'_toQuadraticMap' _ (Matrix.isSymm_diagonal w)]
    have hcomp : A.toQuadraticMap'
        = (QuadraticMap.weightedSumSquares ℚ w).comp e.toLinearEquiv.toLinearMap := by
      ext v; rw [QuadraticMap.comp_apply]; exact (e.map_app v).symm
    have h1 := congrArg QuadraticMap.toMatrix' hcomp
    rw [QuadraticMap.toMatrix'_comp, hWM, toMatrix'_toQuadraticMap' A hA] at h1
    exact h1

/-- **`IsSquare (∏ wᵢ)` from `det A = 1`.** If a symmetric `det = 1` Gram form is isometric to the diagonal
form `∑ wᵢ xᵢ²`, then `∏ wᵢ` is a square: `det A = (det P)² · ∏ wᵢ`, so `∏ wᵢ = (det P)⁻²`. This pins the
diagonalization's discriminant to a square — the square-discriminant hypothesis brick (b) consumes. -/
theorem isSquare_prod_weights {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : A.IsSymm)
    (hdet : A.det = 1) {w : Fin n → ℚ}
    (hwe : A.toQuadraticMap'.Equivalent (QuadraticMap.weightedSumSquares ℚ w)) :
    IsSquare (∏ i, w i) := by
  obtain ⟨P, hPunit, hAeq⟩ := congr_of_equiv_weighted A hA hwe
  have key : A.det = P.det ^ 2 * ∏ i, w i := by
    rw [hAeq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]; ring
  rw [hdet] at key
  have hne : P.det ≠ 0 := hPunit.ne_zero
  exact ⟨P.det⁻¹, by field_simp; linear_combination -key⟩

/-- **`Fin n`-indexed diagonalization.** `QuadraticForm.equivalent_weightedSumSquares` produces weights
indexed by `Fin (finrank …)`; reindexing along `finrank (Fin n → ℚ) = n` gives a diagonalization indexed by
`Fin n` directly, removing the `Fin (finrank)` vs `Fin n` friction in the assembly. -/
theorem equivalent_weightedSumSquares_fin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    ∃ w : Fin n → ℚ, A.toQuadraticMap'.Equivalent (QuadraticMap.weightedSumSquares ℚ w) := by
  obtain ⟨w, hwe⟩ := QuadraticForm.equivalent_weightedSumSquares A.toQuadraticMap'
  set e : Fin (Module.finrank ℚ (Fin n → ℚ)) ≃ Fin n := finCongr (Module.finrank_fin_fun ℚ)
  refine ⟨w ∘ e.symm, hwe.trans ⟨⟨LinearEquiv.funCongrLeft ℚ ℚ e.symm, fun m => ?_⟩⟩⟩
  rw [QuadraticMap.weightedSumSquares_apply, QuadraticMap.weightedSumSquares_apply,
      ← Equiv.sum_comp e.symm (fun i => w i • (m i * m i))]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Function.comp]

/-! ## Rank-4 even unimodular forms have determinant `+1`

The signature of a rank-4 even unimodular form is `0` (the `det = -1`, `σ = ±2` shapes do not occur): mod 4,
`det ≡ (A₀₁A₂₃ - A₀₂A₁₃ + A₀₃A₁₂)²` (the diagonal entries are even, so every determinant term containing a
diagonal factor is `≡ 0 mod 4`), a square `∈ {0,1}`; with `det = ±1` this forces `det = 1`. This pins the
discriminant of the diagonalization to a **square**, so the square-discriminant machinery below applies. -/

set_option maxRecDepth 4000 in
/-- **Mod-4 determinant of an even-diagonal symmetric `4×4`.** The determinant equals the squared
"Pfaffian-like" combination `(af - be + cd)²` modulo `4` (every term with a diagonal factor `2gᵢ` is `≡0`). -/
theorem det4_evenDiag_sq (g0 g1 g2 g3 a b c d e f : ZMod 4) :
    (!![2 * g0, a, b, c; a, 2 * g1, d, e; b, d, 2 * g2, f; c, e, f, 2 * g3] :
        Matrix (Fin 4) (Fin 4) (ZMod 4)).det = (a * f - b * e + c * d) ^ 2 := by
  have h4 : (4 : ZMod 4) = 0 := by decide
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  linear_combination (g0 * g1 * g2 * g3 * 4 - g0 * g1 * f ^ 2 - g0 * g2 * e ^ 2 - g0 * g3 * d ^ 2
    + g0 * f * d * e - g1 * g2 * c ^ 2 - g1 * g3 * b ^ 2 + g1 * f * b * c - g2 * g3 * a ^ 2
    + g2 * e * a * c + g3 * d * a * b - f * d * a * c) * h4

/-- **A rank-4 even unimodular form has `det = 1`.** (Mod-4: `det ≡ (A₀₁A₂₃ - A₀₂A₁₃ + A₀₃A₁₂)² ∈ {0,1}`;
with `det = ±1` this forces `det = 1`, excluding the `σ = ±2` shapes — so the diagonalization has square
discriminant.) -/
theorem det_eq_one_of_evenUnimodular_four (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : IsEvenUnimodular A) :
    A.det = 1 := by
  obtain ⟨hsym, hdet, heven⟩ := hA
  obtain ⟨g0, hg0⟩ := heven 0
  obtain ⟨g1, hg1⟩ := heven 1
  obtain ⟨g2, hg2⟩ := heven 2
  obtain ⟨g3, hg3⟩ := heven 3
  have s10 : A 1 0 = A 0 1 := by
    have h := congrFun (congrFun hsym 0) 1; simpa [Matrix.transpose_apply] using h
  have s20 : A 2 0 = A 0 2 := by
    have h := congrFun (congrFun hsym 0) 2; simpa [Matrix.transpose_apply] using h
  have s30 : A 3 0 = A 0 3 := by
    have h := congrFun (congrFun hsym 0) 3; simpa [Matrix.transpose_apply] using h
  have s21 : A 2 1 = A 1 2 := by
    have h := congrFun (congrFun hsym 1) 2; simpa [Matrix.transpose_apply] using h
  have s31 : A 3 1 = A 1 3 := by
    have h := congrFun (congrFun hsym 1) 3; simpa [Matrix.transpose_apply] using h
  have s32 : A 3 2 = A 2 3 := by
    have h := congrFun (congrFun hsym 2) 3; simpa [Matrix.transpose_apply] using h
  have hM : A.map (Int.castRingHom (ZMod 4)) =
      !![2 * (g0 : ZMod 4), (A 0 1 : ZMod 4), (A 0 2 : ZMod 4), (A 0 3 : ZMod 4);
         (A 0 1 : ZMod 4), 2 * (g1 : ZMod 4), (A 1 2 : ZMod 4), (A 1 3 : ZMod 4);
         (A 0 2 : ZMod 4), (A 1 2 : ZMod 4), 2 * (g2 : ZMod 4), (A 2 3 : ZMod 4);
         (A 0 3 : ZMod 4), (A 1 3 : ZMod 4), (A 2 3 : ZMod 4), 2 * (g3 : ZMod 4)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.map_apply, Int.coe_castRingHom, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.cons_val_fin_one,
        Matrix.empty_val', Fin.isValue, Matrix.of_apply] <;>
      push_cast [hg0, hg1, hg2, hg3, s10, s20, s30, s21, s31, s32] <;> ring
  have hmod : (A.det : ZMod 4)
      = ((A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2 : ℤ) : ZMod 4) ^ 2 := by
    have hd : (A.map (Int.castRingHom (ZMod 4))).det = (A.det : ZMod 4) :=
      (RingHom.map_det (Int.castRingHom (ZMod 4)) A).symm
    rw [← hd, hM, det4_evenDiag_sq]
    push_cast; ring
  rcases hdet with h | h
  · exact h
  · exfalso
    rw [h] at hmod
    have hsq : ∀ x : ZMod 4, ((-1 : ℤ) : ZMod 4) ≠ x ^ 2 := by decide
    exact hsq _ hmod

/-! ## p = 2 from reciprocity (the lone sub-frontier, square-discriminant case)

For a square-discriminant rank-4 form the local isotropy at a place `v` is governed by a *single* binary
Hilbert symbol `(α, β)_v` (`α = -ab`, `β = ac`) via the norm-form reduction
`quaternary_sqdisc_iso_iff_ternary` + the per-place symbol bridges. The product formula
`hilbertGlobalProd_eq_one` then forces the `p = 2` factor once all other places are `1` — so a
square-disc form isotropic at `ℝ` and every *odd* prime is automatically isotropic at `2`. -/

open HilbertSymbol in
/-- **Reciprocity completeness for the binary symbol.** If `(α,β)_∞ = 1` and `(α,β)_p = 1` for every odd
prime `p`, then `(α,β)_2 = 1` — the `p = 2` factor is pinned by the Hilbert product formula
`hilbertGlobalProd_eq_one` (every other factor being `1`). -/
theorem hilbertPrime_two_eq_one_of_real_odd {α β : ℤ} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hreal : HilbertSymbol.hilbertReal (α : ℝ) (β : ℝ) = 1)
    (hodd : ∀ p : ℕ, p.Prime → p ≠ 2 → HilbertSymbol.hilbertPrime p α β = 1) :
    HilbertSymbol.hilbertPrime 2 α β = 1 := by
  have hglob := hilbertGlobalProd_eq_one hα hβ
  rw [hilbertGlobalProd] at hglob
  have hfin : ∏ᶠ p : ℕ, HilbertSymbol.hilbertPrime p α β = HilbertSymbol.hilbertPrime 2 α β := by
    refine finprod_eq_single _ 2 (fun p hp2 => ?_)
    by_cases hpp : p.Prime
    · exact hodd p hpp hp2
    · exact hilbertPrime_of_not_prime hpp α β
  rw [hfin, hreal, one_mul] at hglob
  exact hglob

/-- **Square-discriminant quaternary Hasse–Minkowski, without the place `2`.** For nonzero integers with
`a·b·c·d = s²`, if `a x² + b y² − c z² − d w² = 0` is solvable over `ℝ` and over every *odd* `ℚ_p`, it is
solvable over `ℚ`. The `p = 2` local solvability — the lone gap in the shipped
`quaternary_sqdisc_solvable_of_local` — is supplied by reciprocity: each place's isotropy is the symbol
`(−ab, ac)_v = 1`, and `hilbertPrime_two_eq_one_of_real_odd` pins the `2`-factor from the others. -/
theorem quaternary_sqdisc_solvable_of_local_no_two {a b c d s : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (hsq : a * b * c * d = s ^ 2)
    (hR : ∃ x y z w : ℝ, ¬(x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) ∧
      (a : ℝ) * x ^ 2 + (b : ℝ) * y ^ 2 - (c : ℝ) * z ^ 2 - (d : ℝ) * w ^ 2 = 0)
    (hodd : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ x y z w : ℚ_[p],
      ¬(x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) ∧
      (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2 - (c : ℚ_[p]) * z ^ 2 - (d : ℚ_[p]) * w ^ 2 = 0) :
    ∃ x y z w : ℚ, ¬(x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) ∧
      (a : ℚ) * x ^ 2 + (b : ℚ) * y ^ 2 - (c : ℚ) * z ^ 2 - (d : ℚ) * w ^ 2 = 0 := by
  set α : ℤ := -(a * b) with hαdef
  set β : ℤ := a * c with hβdef
  have hα : α ≠ 0 := neg_ne_zero.mpr (mul_ne_zero ha hb)
  have hβ : β ≠ 0 := mul_ne_zero ha hc
  -- real place: the symbol (α,β)_∞ = 1
  have hreal : HilbertSymbol.hilbertReal (α : ℝ) (β : ℝ) = 1 := by
    obtain ⟨X, Y, Z, hnzt, het⟩ :=
      (quaternary_sqdisc_iso_iff_ternary (a := (a : ℝ)) (b := (b : ℝ)) (c := (c : ℝ)) (d := (d : ℝ))
        (s := (s : ℝ)) (by exact_mod_cast ha) (by exact_mod_cast hb) (by exact_mod_cast hc)
        (by exact_mod_cast hd) (by exact_mod_cast hsq)).mp hR
    have het' : Z ^ 2 = (α : ℝ) * X ^ 2 + (β : ℝ) * Y ^ 2 := by
      rw [het, hαdef, hβdef]; push_cast; ring
    rw [HilbertSymbol.hilbertReal_eq_one_iff (by exact_mod_cast hα) (by exact_mod_cast hβ)]
    refine ⟨X, Y, Z, ?_, het'⟩
    intro h
    rw [Prod.mk_eq_zero] at h
    obtain ⟨hX, hYZ⟩ := h
    rw [Prod.mk_eq_zero] at hYZ
    exact hnzt ⟨hX, hYZ.1, hYZ.2⟩
  -- odd primes: the symbol (α,β)_p = 1
  have hoddsym : ∀ p : ℕ, p.Prime → p ≠ 2 → HilbertSymbol.hilbertPrime p α β = 1 := by
    intro p hp hp2
    haveI := Fact.mk hp
    rw [HilbertSymbol.hilbertPrime_odd hp hp2, ← solvable_padic_iff_hilbertPadicInt_one hp2 hα hβ]
    obtain ⟨X, Y, Z, hnzt, het⟩ :=
      (quaternary_sqdisc_iso_iff_ternary (a := (a : ℚ_[p])) (b := (b : ℚ_[p])) (c := (c : ℚ_[p]))
        (d := (d : ℚ_[p])) (s := (s : ℚ_[p])) (by exact_mod_cast ha) (by exact_mod_cast hb)
        (by exact_mod_cast hc) (by exact_mod_cast hd) (by exact_mod_cast hsq)).mp (hodd p hp2)
    exact ⟨X, Y, Z, hnzt, by rw [het, hαdef, hβdef]; push_cast; ring⟩
  -- p = 2 from reciprocity
  have h2sym : HilbertSymbol.hilbert2Int α β = 1 := by
    rw [← HilbertSymbol.hilbertPrime_two]
    exact hilbertPrime_two_eq_one_of_real_odd hα hβ hreal hoddsym
  have h2loc : ∃ x y z w : ℚ_[2], ¬(x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) ∧
      (a : ℚ_[2]) * x ^ 2 + (b : ℚ_[2]) * y ^ 2 - (c : ℚ_[2]) * z ^ 2 - (d : ℚ_[2]) * w ^ 2 = 0 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨X, Y, Z, hnzt, het⟩ := (solvable_2adic_iff_hilbert2Int hα hβ).mpr h2sym
    refine (quaternary_sqdisc_iso_iff_ternary (a := (a : ℚ_[2])) (b := (b : ℚ_[2])) (c := (c : ℚ_[2]))
      (d := (d : ℚ_[2])) (s := (s : ℚ_[2])) (by exact_mod_cast ha) (by exact_mod_cast hb)
      (by exact_mod_cast hc) (by exact_mod_cast hd) (by exact_mod_cast hsq)).mpr ⟨X, Y, Z, hnzt, ?_⟩
    rw [het, hαdef, hβdef]; push_cast; ring
  -- combine all places and invoke the full square-disc Hasse–Minkowski
  have hloc : ∀ (p : ℕ) [Fact p.Prime], ∃ x y z w : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) ∧
      (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2 - (c : ℚ_[p]) * z ^ 2 - (d : ℚ_[p]) * w ^ 2 = 0 := by
    intro p _
    by_cases hp2 : p = 2
    · subst hp2; exact h2loc
    · exact hodd p hp2
  have hQ := quaternary_sqdisc_solvable_of_local (a := (a : ℚ)) (b := (b : ℚ)) (c := (c : ℚ))
    (d := (d : ℚ)) (s := (s : ℚ)) (by exact_mod_cast ha) (by exact_mod_cast hb) (by exact_mod_cast hc)
    (by exact_mod_cast hd) (by exact_mod_cast hsq) ?_ ?_
  · obtain ⟨x, y, z, w, hnz, he⟩ := hQ
    exact ⟨x, y, z, w, hnz, by push_cast at he ⊢; linear_combination he⟩
  · obtain ⟨x, y, z, w, hnz, he⟩ := hR
    exact ⟨x, y, z, w, hnz, by push_cast at he ⊢; linear_combination he⟩
  · intro p _
    obtain ⟨x, y, z, w, hnz, he⟩ := hloc p
    exact ⟨x, y, z, w, hnz, by push_cast at he ⊢; linear_combination he⟩

/-- **Square-discriminant rank-4 diagonal Hasse–Minkowski without place 2**, in `∑ dᵢ xᵢ²` form. A diagonal
form with nonzero integer coefficients and square product, isotropic over `ℝ` and every *odd* `ℚ_p`, is
isotropic over `ℚ`. A thin `Fin 4`-vector wrapper over `quaternary_sqdisc_solvable_of_local_no_two`. -/
theorem diag_four_solvable_of_local_no_two {d : Fin 4 → ℤ} (hne : ∀ i, d i ≠ 0)
    (hsq : IsSquare (d 0 * d 1 * d 2 * d 3))
    (hR : ∃ x : Fin 4 → ℝ, x ≠ 0 ∧ ∑ i, (d i : ℝ) * x i ^ 2 = 0)
    (hodd : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
      ∃ x : Fin 4 → ℚ_[p], x ≠ 0 ∧ ∑ i, (d i : ℚ_[p]) * x i ^ 2 = 0) :
    ∃ x : Fin 4 → ℚ, x ≠ 0 ∧ ∑ i, (d i : ℚ) * x i ^ 2 = 0 := by
  obtain ⟨s, hs⟩ := hsq
  obtain ⟨x, y, z, w, hnz, he⟩ := quaternary_sqdisc_solvable_of_local_no_two
    (hne 0) (hne 1) (neg_ne_zero.mpr (hne 2)) (neg_ne_zero.mpr (hne 3))
    (show d 0 * d 1 * (-d 2) * (-d 3) = s ^ 2 by rw [pow_two]; linear_combination hs)
    (by obtain ⟨v, hv, hve⟩ := hR
        refine ⟨v 0, v 1, v 2, v 3, fun h => hv (funext fun i => by fin_cases i <;> simp_all), ?_⟩
        rw [Fin.sum_univ_four] at hve; push_cast; linear_combination hve)
    (by intro p _ hp2
        obtain ⟨v, hv, hve⟩ := hodd p hp2
        refine ⟨v 0, v 1, v 2, v 3, fun h => hv (funext fun i => by fin_cases i <;> simp_all), ?_⟩
        rw [Fin.sum_univ_four] at hve; push_cast; linear_combination hve)
  refine ⟨![x, y, z, w], fun h => hnz ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · have := congrFun h 0; simpa using this
  · have := congrFun h 1; simpa using this
  · have := congrFun h 2; simpa using this
  · have := congrFun h 3; simpa using this
  · rw [Fin.sum_univ_four]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    push_cast at he ⊢; linear_combination he

/-- A ring hom commutes with the Gram quadratic value `v ⬝ᵥ M *ᵥ v`. -/
theorem ringHom_map_gram {R S : Type*} [CommRing R] [CommRing S] (ι : R →+* S) {k : ℕ}
    (M : Matrix (Fin k) (Fin k) R) (v : Fin k → R) :
    ι (v ⬝ᵥ M *ᵥ v) = (fun i => ι (v i)) ⬝ᵥ (M.map ι) *ᵥ (fun i => ι (v i)) := by
  simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.map_apply]

/-- **Weak [HM] at rank 4.** Every indefinite even unimodular `4×4` form has a nonzero integer isotropic
vector. `det = 1` (excluding `σ = ±2`) makes the ℚ-diagonalization square-discriminant; ℝ-isotropy is
indefiniteness; odd-`p` isotropy is the `ℤ_p`-unimodular fact (brick a) transported through the explicit
congruence; the `p = 2` place is then free by reciprocity (brick b). -/
theorem weakIsotropic_rank_four (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : IsEvenUnimodular A)
    (hsp : 0 < sigPos (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsn : 0 < sigNeg (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap') :
    ∃ v : Fin 4 → ℤ, v ≠ 0 ∧ v ⬝ᵥ A *ᵥ v = 0 := by
  apply exists_int_isotropic_of_rat A
  set Aq : Matrix (Fin 4) (Fin 4) ℚ := A.map (Int.cast : ℤ → ℚ) with hAq
  have hAqsymm : Aq.IsSymm := by
    ext i j
    rw [Matrix.transpose_apply, hAq, Matrix.map_apply, Matrix.map_apply]
    congr 1
    have := congrFun (congrFun hA.1 i) j; rwa [Matrix.transpose_apply] at this
  have hdetq : Aq.det = 1 := by
    have h : Aq.det = ((A.det : ℤ) : ℚ) := (RingHom.map_det (Int.castRingHom ℚ) A).symm
    rw [h, det_eq_one_of_evenUnimodular_four A hA, Int.cast_one]
  obtain ⟨w, hwe⟩ := equivalent_weightedSumSquares_fin Aq
  obtain ⟨P, hPunit, hAeq⟩ := congr_of_equiv_weighted Aq hAqsymm hwe
  have hsqw : IsSquare (∏ i, w i) := isSquare_prod_weights Aq hAqsymm hdetq hwe
  -- real signs of w (from indefiniteness)
  have hspq : 0 < sigPos Aq.toQuadraticMap' := sigPos_cast_pos A hsp
  have hsnq : 0 < sigNeg Aq.toQuadraticMap' := sigNeg_cast_pos A hsn
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
    -- IsSquare (∏ d)
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
    · -- ℝ: indefinite ⟹ a + and − coefficient among (d i : ℝ)
      have hdR_pos : 0 < ((d ip : ℤ) : ℝ) := by
        rw [hd]; have : (0:ℤ) < (w ip).num * (w ip).den :=
          mul_pos (Rat.num_pos.mpr hip) (by exact_mod_cast (w ip).pos)
        exact_mod_cast this
      have hdR_neg : ((d iN : ℤ) : ℝ) < 0 := by
        rw [hd]; have : (w iN).num * ((w iN).den : ℤ) < 0 :=
          mul_neg_of_neg_of_pos (Rat.num_neg.mpr hiN) (by exact_mod_cast (w iN).pos)
        exact_mod_cast this
      have hipN : ip ≠ iN := fun h => by rw [h] at hip; exact absurd (hip.trans hiN) (lt_irrefl _)
      exact diag_real_isotropic_of_signs (fun i => (d i : ℝ)) ip iN hipN hdR_pos hdR_neg
    · -- odd p: brick (a) + congruence transfer
      intro p _ hp2
      set φ : ℚ →+* ℚ_[p] := Rat.castHom ℚ_[p] with hφ
      -- A over ℤ_p isotropic (brick a)
      have hsymZp : (A.map (Int.castRingHom ℤ_[p])).transpose = A.map (Int.castRingHom ℤ_[p]) := by
        ext i j
        simp only [Matrix.transpose_apply, Matrix.map_apply]
        congr 1
        have := congrFun (congrFun hA.1 i) j; rwa [Matrix.transpose_apply] at this
      have hunitZp : IsUnit ((A.map (Int.castRingHom ℤ_[p])).det) := by
        have hdt : (A.map (Int.castRingHom ℤ_[p])).det = (Int.castRingHom ℤ_[p]) A.det :=
          (RingHom.map_det (Int.castRingHom ℤ_[p]) A).symm
        rw [hdt]
        rcases hA.2.1 with h | h <;> rw [h] <;> simp
      obtain ⟨vp, hvp0, hvpe⟩ :=
        isotropic_padicInt_of_unit_det hp2 (by norm_num) _ hsymZp hunitZp
      -- cast ℤ_p → ℚ_p : A.map(ℤ→ℚ_p) isotropic
      set ι : ℤ_[p] →+* ℚ_[p] := algebraMap ℤ_[p] ℚ_[p] with hι
      have hAQp_iso : ∃ x : Fin 4 → ℚ_[p], x ≠ 0 ∧
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
      -- transfer: A_{ℚ_p} = Aq.map φ = (P.map φ)ᵀ * diagonal (φ∘w) * (P.map φ)
      have hAcast : A.map (Int.cast : ℤ → ℚ_[p]) = Aq.map φ := by
        ext i j; simp only [hAq, Matrix.map_apply, hφ, map_intCast]
      have hAeqp : Aq.map φ = (P.map φ)ᵀ * Matrix.diagonal (fun i => φ (w i)) * (P.map φ) := by
        rw [hAeq]
        rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.diagonal_map (map_zero φ)]
      have hPunitp : IsUnit (P.map φ).det := by
        have hdt : (P.map φ).det = φ P.det := (RingHom.map_det φ P).symm
        rw [hdt]; exact hPunit.map φ
      have hdiagiso : ∃ x : Fin 4 → ℚ_[p], x ≠ 0 ∧
          x ⬝ᵥ Matrix.diagonal (fun i => φ (w i)) *ᵥ x = 0 := by
        rw [matrix_isotropic_congr (Matrix.diagonal (fun i => φ (w i))) (P.map φ) hPunitp]
        rw [← hAeqp, ← hAcast]; exact hAQp_iso
      obtain ⟨x, hx0, hxe⟩ := hdiagiso
      have hsum : ∑ i, (w i : ℚ_[p]) * x i ^ 2 = 0 := by
        rw [← hxe, dotProduct]; refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.mulVec_diagonal]; simp only [hφ, Rat.coe_castHom]; ring
      exact (diag_iso_rat_int (K := ℚ_[p]) w).mp ⟨x, hx0, hsum⟩

/-! ## Discharge of `HasWeakIsotropicVectorHyp` (all ranks) -/

/-- **The weak [HM] hypothesis is a theorem.** Every indefinite even unimodular integer form has a nonzero
integer isotropic vector. Rank case-split: rank 0 (`sigPos = 0`, contradiction), ranks 1 & 3 (no even
unimodular form exists), rank 2 (`weakIsotropic_rank_two`), rank 4 (`weakIsotropic_rank_four`), rank ≥ 5
(`weakIsotropic_of_five_le`). -/
theorem hasWeakIsotropicVector : HasWeakIsotropicVectorHyp := by
  intro m A hA hsp hsn
  rcases Nat.lt_or_ge m 5 with hm | hm
  · interval_cases m
    · exfalso
      have h := QuadraticForm.sigPos_add_sigNeg_add_radical
        (Q := (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
      rw [show Module.finrank ℝ (Fin 0 → ℝ) = 0 by simp] at h
      omega
    · exact (not_evenUnimodular_one A hA).elim
    · exact weakIsotropic_rank_two A hA
    · exact (not_evenUnimodular_three A hA).elim
    · exact weakIsotropic_rank_four A hA hsp hsn
  · exact weakIsotropic_of_five_le hm A hsp hsn

/-- **The strong [HM] hypothesis is a theorem** (primitive isotropic vector), via content extraction. -/
theorem hasIsotropicVector : HasIsotropicVectorHyp := hasIsotropic_of_weak hasWeakIsotropicVector

/-- **`8 ∣ σ` for every even unimodular form — unconditional.** Combines the discharged [HM] input with the
theta-modularity [Θ] input (`eight_dvd_latticeSig_of_HM`). -/
theorem eight_dvd_latticeSig (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ) (heu : IsEvenUnimodular M) :
    8 ∣ latticeSig M :=
  eight_dvd_latticeSig_of_HM hasIsotropicVector n M heu

/-- **`16 ∣ σ` for every even unimodular form with the topological factor — unconditional.** -/
theorem sixteen_dvd_latticeSig {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (heu : IsEvenUnimodular M)
    (htopo : (2 : ℤ) ∣ latticeSig M / 8) : (16 : ℤ) ∣ latticeSig M :=
  sixteen_dvd_latticeSig_of_HM_of_topo hasIsotropicVector M heu htopo

end SKEFTHawking
