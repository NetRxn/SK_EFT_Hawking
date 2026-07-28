/-
# `⟨1⟩`-cancellation: the Eichler assembly

`UnitBlockCancellation.UnitCancellation` reduces the K8b interior brick to ONE statement, and
`EichlerTransvection.exists_isometry_map_of_perp_hyp` discharges **STEP 2** of Eichler's criterion
(the three-transvection chain). This module builds the ASSEMBLY between them: everything that turns
STEP 2 plus a STEP-1 normalisation into `UnitCancellation`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.UnitBlockCancellation

namespace SKEFTHawking

open Matrix Module QuadraticForm

/-! ### Extracting `A ≅ B` from a unit-vector-fixing isometry

If `Φ` conjugates `⟨1⟩ ⊕ A` to `⟨1⟩ ⊕ B` *and fixes the adjoined generator*, then `Φ` is itself
block-diagonal `⟨1⟩ ⊕ P`, and `Pᵀ A P = B`. This is the exit gate of the whole route: the entire
remaining problem is producing such a `Φ`.
-/

/-- The adjoined `⟨1⟩` generator, as a vector of `Fin m → ℤ` under the reindexing `e`. -/
def unitGen {n m : ℕ} (e : Fin 1 ⊕ Fin n ≃ Fin m) : Fin m → ℤ :=
  Pi.single (e (Sum.inl 0)) 1

/-- The Gram matrix of `⟨1⟩ ⊕ A` in the reindexing `e`, evaluated on the adjoined generator's row. -/
theorem unitExtend_row {n m : ℕ} (e : Fin 1 ⊕ Fin n ≃ Fin m) (A : Matrix (Fin n) (Fin n) ℤ)
    (l : Fin m) :
    (Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 A)) (e (Sum.inl 0)) l = unitGen e l := by
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, unitGen]
  rcases hl : e.symm l with j | j
  · have : l = e (Sum.inl 0) := by
      have := congrArg e hl
      rwa [Equiv.apply_symm_apply, Subsingleton.elim j 0] at this
    subst this
    simp
  · have : l ≠ e (Sum.inl 0) := by
      intro hcon
      rw [hcon, Equiv.symm_apply_apply] at hl
      simp at hl
    simp [this, Matrix.fromBlocks_apply₁₂]

/-- The adjoined generator's COLUMN of the Gram matrix of `⟨1⟩ ⊕ A`. -/
theorem unitExtend_col {n m : ℕ} (e : Fin 1 ⊕ Fin n ≃ Fin m) (A : Matrix (Fin n) (Fin n) ℤ)
    (i : Fin m) :
    (Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 A)) i (e (Sum.inl 0)) = unitGen e i := by
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, unitGen]
  rcases hi : e.symm i with j | j
  · have : i = e (Sum.inl 0) := by
      have := congrArg e hi
      rwa [Equiv.apply_symm_apply, Subsingleton.elim j 0] at this
    subst this
    simp
  · have : i ≠ e (Sum.inl 0) := by
      intro hcon
      rw [hcon, Equiv.symm_apply_apply] at hi
      simp at hi
    simp [this, Matrix.fromBlocks_apply₂₁]

/-- `⟨1⟩ ⊕ A` fixes the adjoined generator: `G *ᵥ w = w`. -/
theorem unitExtend_mulVec_gen {n m : ℕ} (e : Fin 1 ⊕ Fin n ≃ Fin m)
    (A : Matrix (Fin n) (Fin n) ℤ) :
    (Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 A)) *ᵥ unitGen e = unitGen e := by
  funext i
  have : ((Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 A)) *ᵥ unitGen e) i
      = (Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 A)) i (e (Sum.inl 0)) := by
    rw [unitGen]; simp
  rw [this]
  exact unitExtend_col e A i

/-- **Exit gate.** An isometry `⟨1⟩ ⊕ A → ⟨1⟩ ⊕ B` that FIXES the adjoined generator is block
diagonal, and its residual block realises `IntCongr A B`. -/
theorem intCongr_of_unitFixing {n m : ℕ} (e : Fin 1 ⊕ Fin n ≃ Fin m)
    (A B : Matrix (Fin n) (Fin n) ℤ) (Φ : Matrix (Fin m) (Fin m) ℤ) (hdet : IsUnit Φ.det)
    (hfix : Φ *ᵥ unitGen e = unitGen e)
    (hconj : Φᵀ * (Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 A)) * Φ
      = Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 B)) :
    IntCongr A B := by
  classical
  -- the column of `Φ` at the generator's index is the generator
  have hcolΦ : ∀ i, Φ i (e (Sum.inl 0)) = unitGen e i := by
    intro i
    have h := congrFun hfix i
    rw [unitGen] at h ⊢
    simpa using h
  -- the ROW of `Φ` at the generator's index is the generator too
  have hrowΦ : ∀ j, Φ (e (Sum.inl 0)) j = unitGen e j := by
    have h1 : (Φᵀ * (Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 A)) * Φ) *ᵥ unitGen e
        = unitGen e := by
      rw [hconj]; exact unitExtend_mulVec_gen e B
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfix, unitExtend_mulVec_gen e A] at h1
    intro j
    have h := congrFun h1 j
    rw [unitGen] at h ⊢
    simpa using h
  set Ψ : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℤ := Φ.submatrix e e with hΨ
  set P : Matrix (Fin n) (Fin n) ℤ := Ψ.toBlocks₂₂ with hP
  -- `Ψ` is block diagonal
  have hblock : Ψ = Matrix.fromBlocks !![1] 0 0 P := by
    ext a b
    match a, b with
    | Sum.inl i, Sum.inl j =>
      have hi : i = 0 := Subsingleton.elim i 0
      have hj : j = 0 := Subsingleton.elim j 0
      subst hi; subst hj
      rw [hΨ, Matrix.submatrix_apply, hcolΦ, unitGen]
      simp
    | Sum.inl i, Sum.inr j =>
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      rw [hΨ, Matrix.submatrix_apply, hrowΦ, unitGen, Pi.single_apply]
      have : e (Sum.inr j) ≠ e (Sum.inl 0) := by
        intro hcon; simp at hcon
      simp [this]
    | Sum.inr i, Sum.inl j =>
      have hj : j = 0 := Subsingleton.elim j 0
      subst hj
      rw [hΨ, Matrix.submatrix_apply, hcolΦ, unitGen, Pi.single_apply]
      have : e (Sum.inr i) ≠ e (Sum.inl 0) := by
        intro hcon; simp at hcon
      simp [this]
    | Sum.inr i, Sum.inr j => simp [hP, Matrix.toBlocks₂₂]
  -- transport the conjugation identity down to `Fin 1 ⊕ Fin n`
  have hGsub : ∀ C : Matrix (Fin n) (Fin n) ℤ,
      (Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 C)).submatrix e e
        = Matrix.fromBlocks !![1] 0 0 C := by
    intro C; rw [Matrix.reindex_apply, Matrix.submatrix_submatrix]; simp
  have hsub : Ψᵀ * (Matrix.fromBlocks !![1] 0 0 A) * Ψ = Matrix.fromBlocks !![1] 0 0 B := by
    rw [hΨ, Matrix.transpose_submatrix, ← hGsub A, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, hconj, hGsub B]
  -- block-diagonal conjugation acts blockwise
  have hone : (!![(1 : ℤ)] : Matrix (Fin 1) (Fin 1) ℤ) = 1 := by
    ext i j; fin_cases i; fin_cases j; simp
  have hexp : Ψᵀ * (Matrix.fromBlocks !![1] 0 0 A) * Ψ
      = Matrix.fromBlocks !![1] 0 0 (Pᵀ * A * P) := by
    rw [hblock, Matrix.fromBlocks_transpose, hone]
    simp [Matrix.fromBlocks_multiply]
  refine ⟨P, ?_, ?_⟩
  · have h1 : Ψ.det = Φ.det := Matrix.det_submatrix_equiv_self e Φ
    have h2 : Ψ.det = P.det := by
      rw [hblock, Matrix.det_fromBlocks_zero₂₁, hone]
      simp
    rw [← h2, h1]; exact hdet
  · have := hexp.symm.trans hsub
    have h3 := congrArg Matrix.toBlocks₂₂ this
    simpa [Matrix.toBlocks_fromBlocks₂₂] using h3

/-! ### Characteristic vectors

`c` is characteristic for `G` when `z·z ≡ z·c (mod 2)` for every `z`. Two characteristic vectors of a
UNIMODULAR form are congruent mod `2L` — that is the source of the `w − w' = 2k` hypothesis of
`exists_isometry_map_of_perp_hyp` (Eichler STEP 2). -/

/-- **Characteristic vector** (quadratic form): `z ⬝ᵥ G *ᵥ z ≡ z ⬝ᵥ G *ᵥ c (mod 2)` for all `z`. -/
def IsCharQ {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (c : Fin n → ℤ) : Prop :=
  ∀ z : Fin n → ℤ, (2 : ℤ) ∣ (z ⬝ᵥ G *ᵥ z) - (z ⬝ᵥ G *ᵥ c)

/-- `a² ≡ a (mod 2)`. -/
theorem two_dvd_sq_sub_self (a : ℤ) : (2 : ℤ) ∣ a * a - a := by
  obtain ⟨k, hk⟩ := Int.even_mul_succ_self (a - 1)
  exact ⟨k, by linear_combination hk⟩

/-- **Entry-wise ⟹ quadratic.** If `(G c)ᵢ ≡ Gᵢᵢ (mod 2)` for every `i`, then `c` is characteristic.
The off-diagonal part of `G` is an EVEN symmetric form, so it contributes nothing mod 2. -/
theorem isCharQ_of_diag {n : ℕ} {G : Matrix (Fin n) (Fin n) ℤ} (hsymm : Gᵀ = G) {c : Fin n → ℤ}
    (h : ∀ i, (2 : ℤ) ∣ (G *ᵥ c) i - G i i) : IsCharQ G c := by
  intro z
  set D : Matrix (Fin n) (Fin n) ℤ := Matrix.diagonal (fun i => G i i) with hD
  have hDsymm : (G - D)ᵀ = G - D := by
    rw [Matrix.transpose_sub, hsymm, hD, Matrix.diagonal_transpose]
  have hDeven : ∀ i, (2 : ℤ) ∣ (G - D) i i := by
    intro i; simp [hD, Matrix.diagonal_apply_eq]
  have h1 : (2 : ℤ) ∣ z ⬝ᵥ (G - D) *ᵥ z := EvenLattice.even_form_dvd hDsymm hDeven z
  have hDquad : z ⬝ᵥ D *ᵥ z = ∑ i, G i i * z i * z i := by
    rw [hD]
    simp [dotProduct, Matrix.mulVec_diagonal, mul_comm, mul_left_comm]
  have h2 : z ⬝ᵥ (G - D) *ᵥ z = z ⬝ᵥ G *ᵥ z - ∑ i, G i i * z i * z i := by
    rw [Matrix.sub_mulVec, dotProduct_sub, hDquad]
  have h3 : (2 : ℤ) ∣ (∑ i, G i i * z i * z i) - ∑ i, G i i * z i := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun i _ => ?_
    obtain ⟨k, hk⟩ := two_dvd_sq_sub_self (z i)
    exact ⟨G i i * k, by linear_combination G i i * hk⟩
  have hcdot : z ⬝ᵥ G *ᵥ c = ∑ i, z i * (G *ᵥ c) i := rfl
  have h4 : (2 : ℤ) ∣ (∑ i, G i i * z i) - z ⬝ᵥ G *ᵥ c := by
    rw [hcdot, ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun i _ => ?_
    obtain ⟨k, hk⟩ := h i
    exact ⟨-(z i * k), by linear_combination (-(z i)) * hk⟩
  have hsplit : (z ⬝ᵥ G *ᵥ z) - (z ⬝ᵥ G *ᵥ c)
      = (z ⬝ᵥ (G - D) *ᵥ z)
        + ((∑ i, G i i * z i * z i) - ∑ i, G i i * z i)
        + ((∑ i, G i i * z i) - z ⬝ᵥ G *ᵥ c) := by
    rw [h2]; ring
  rw [hsplit]
  exact dvd_add (dvd_add h1 h3) h4

/-- **Quadratic ⟹ entry-wise**: test against the standard basis vectors. -/
theorem IsCharQ.diag {n : ℕ} {G : Matrix (Fin n) (Fin n) ℤ} {c : Fin n → ℤ} (h : IsCharQ G c)
    (i : Fin n) : (2 : ℤ) ∣ (G *ᵥ c) i - G i i := by
  have hi := h (Pi.single i 1)
  have h1 : (Pi.single i (1 : ℤ)) ⬝ᵥ G *ᵥ (Pi.single i 1) = G i i := by simp
  have h2 : (Pi.single i (1 : ℤ)) ⬝ᵥ G *ᵥ c = (G *ᵥ c) i := by simp
  rw [h1, h2] at hi
  exact dvd_sub_comm.mp hi

/-- **Characteristic vectors transport along congruences.** If `Sᵀ G S = H` and `c` is characteristic
for `H`, then `S *ᵥ c` is characteristic for `G`. -/
theorem IsCharQ.congr {n : ℕ} {G H : Matrix (Fin n) (Fin n) ℤ} {S : Matrix (Fin n) (Fin n) ℤ}
    (hS : IsUnit S.det) (hSGS : Sᵀ * G * S = H) {c : Fin n → ℤ} (h : IsCharQ H c) :
    IsCharQ G (S *ᵥ c) := by
  classical
  letI := S.invertibleOfIsUnitDet hS
  intro z
  have hz : S *ᵥ (⅟S *ᵥ z) = z := by
    rw [Matrix.mulVec_mulVec, mul_invOf_self, Matrix.one_mulVec]
  have hgen : ∀ y y' : Fin n → ℤ, (S *ᵥ y) ⬝ᵥ G *ᵥ (S *ᵥ y') = y ⬝ᵥ H *ᵥ y' := by
    intro y y'
    rw [← hSGS, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
      Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mul_assoc]
  have e1 : z ⬝ᵥ G *ᵥ z = (⅟S *ᵥ z) ⬝ᵥ H *ᵥ (⅟S *ᵥ z) := by
    rw [← hgen, hz]
  have e2 : z ⬝ᵥ G *ᵥ (S *ᵥ c) = (⅟S *ᵥ z) ⬝ᵥ H *ᵥ c := by
    conv_lhs => rw [← hz]
    rw [hgen]
  rw [e1, e2]
  exact h _

/-! ### Bilinear toolkit -/

section Bil
variable {n : ℕ} {G : Matrix (Fin n) (Fin n) ℤ}

theorem bil_comm (hsymm : Gᵀ = G) (x y : Fin n → ℤ) : x ⬝ᵥ G *ᵥ y = y ⬝ᵥ G *ᵥ x := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hsymm, dotProduct_comm]

theorem bil_smul_right (c : ℤ) (x y : Fin n → ℤ) : x ⬝ᵥ G *ᵥ (c • y) = c * (x ⬝ᵥ G *ᵥ y) := by
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem bil_smul_left (c : ℤ) (x y : Fin n → ℤ) : (c • x) ⬝ᵥ G *ᵥ y = c * (x ⬝ᵥ G *ᵥ y) := by
  rw [smul_dotProduct, smul_eq_mul]

theorem bil_add_right (x y z : Fin n → ℤ) : x ⬝ᵥ G *ᵥ (y + z) = x ⬝ᵥ G *ᵥ y + x ⬝ᵥ G *ᵥ z := by
  rw [Matrix.mulVec_add, dotProduct_add]

theorem bil_add_left (x y z : Fin n → ℤ) : (x + y) ⬝ᵥ G *ᵥ z = x ⬝ᵥ G *ᵥ z + y ⬝ᵥ G *ᵥ z := by
  rw [add_dotProduct]

theorem bil_sub_right (x y z : Fin n → ℤ) : x ⬝ᵥ G *ᵥ (y - z) = x ⬝ᵥ G *ᵥ y - x ⬝ᵥ G *ᵥ z := by
  rw [Matrix.mulVec_sub, dotProduct_sub]

theorem bil_sub_left (x y z : Fin n → ℤ) : (x - y) ⬝ᵥ G *ᵥ z = x ⬝ᵥ G *ᵥ z - y ⬝ᵥ G *ᵥ z := by
  rw [sub_dotProduct]

/-- Congruence acts on the bilinear form by change of Gram matrix. -/
theorem bil_congr_matrix (G S : Matrix (Fin n) (Fin n) ℤ) (y y' : Fin n → ℤ) :
    (S *ᵥ y) ⬝ᵥ G *ᵥ (S *ᵥ y') = y ⬝ᵥ (Sᵀ * G * S) *ᵥ y' := by
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mul_assoc]

end Bil

/-! ### The adjoined generator is characteristic; congruence mod `2L` -/

/-- **The adjoined `⟨1⟩` generator is a characteristic vector of `⟨1⟩ ⊕ A`** when `A` is even: its
orthogonal complement is `A`, which is even. -/
theorem isCharQ_unitGen {n m : ℕ} (e : Fin 1 ⊕ Fin n ≃ Fin m) (A : Matrix (Fin n) (Fin n) ℤ)
    (hsym : Aᵀ = A) (heven : ∀ j, (2 : ℤ) ∣ A j j) :
    IsCharQ (Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 A)) (unitGen e) := by
  refine isCharQ_of_diag (unitExtend_symm e A hsym) fun i => ?_
  rw [unitExtend_mulVec_gen e A, unitGen, Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases hi : e.symm i with j | j
  · have hie : i = e (Sum.inl 0) := by
      have := congrArg e hi
      rwa [Equiv.apply_symm_apply, Subsingleton.elim j 0] at this
    subst hie
    simp
  · have hne : i ≠ e (Sum.inl 0) := by
      intro hcon
      rw [hcon, Equiv.symm_apply_apply] at hi
      simp at hi
    simp only [Pi.single_apply, hne, if_false, Matrix.fromBlocks_apply₂₂, zero_sub, dvd_neg]
    exact heven j

/-- **Two characteristic vectors of a UNIMODULAR form are congruent mod `2L`.** `G(c₁ − c₂)` has all
entries even, and `G⁻¹` is integral, so `c₁ − c₂ ∈ 2L`. This is exactly the `w − w' = 2 • k`
hypothesis of `exists_isometry_map_of_perp_hyp`. -/
theorem exists_two_smul_sub_of_char {n : ℕ} {G : Matrix (Fin n) (Fin n) ℤ}
    (hunim : IsUnimodular G) {c₁ c₂ : Fin n → ℤ} (h₁ : IsCharQ G c₁) (h₂ : IsCharQ G c₂) :
    ∃ k : Fin n → ℤ, c₁ - c₂ = (2 : ℤ) • k := by
  classical
  have hdet : IsUnit G.det := by
    rcases hunim with h | h <;> rw [h] <;> simp
  letI := G.invertibleOfIsUnitDet hdet
  have hev : ∀ i, ∃ a : ℤ, (G *ᵥ (c₁ - c₂)) i = 2 * a := by
    intro i
    obtain ⟨a, ha⟩ := h₁.diag i
    obtain ⟨b, hb⟩ := h₂.diag i
    refine ⟨a - b, ?_⟩
    rw [Matrix.mulVec_sub]
    simp only [Pi.sub_apply]
    linarith [ha, hb]
  choose v hv using hev
  refine ⟨⅟G *ᵥ v, ?_⟩
  have hGv : G *ᵥ ((2 : ℤ) • (⅟G *ᵥ v)) = G *ᵥ (c₁ - c₂) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, mul_invOf_self, Matrix.one_mulVec]
    funext i
    rw [hv i]
    simp [two_mul]
  have hinj : ∀ x y : Fin n → ℤ, G *ᵥ x = G *ᵥ y → x = y := by
    intro x y hxy
    have : ⅟G *ᵥ (G *ᵥ x) = ⅟G *ᵥ (G *ᵥ y) := by rw [hxy]
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, invOf_mul_self, Matrix.one_mulVec,
      Matrix.one_mulVec] at this
  exact (hinj _ _ hGv).symm

/-! ### The `k·k` even normalisation (the mod-4 sign flip)

STEP 2 needs `k ⬝ᵥ G *ᵥ k` EVEN, i.e. `w · w' ≡ 1 (mod 4)`. Replacing `w'` by `−w'` (which has the
same orthogonal complement) flips `k` to `k + w'`, and the two self-products sum to `1` — so exactly
one of the two choices is even. -/

/-- The two candidate `k`'s have self-products summing to `1`. -/
theorem char_k_sum_eq_one {n : ℕ} {G : Matrix (Fin n) (Fin n) ℤ} (hsymm : Gᵀ = G)
    {w w' k : Fin n → ℤ} (hww : w ⬝ᵥ G *ᵥ w = 1) (hw'w' : w' ⬝ᵥ G *ᵥ w' = 1)
    (hk : w - w' = (2 : ℤ) • k) :
    (k + w') ⬝ᵥ G *ᵥ (k + w') = 1 - k ⬝ᵥ G *ᵥ k := by
  have hsq : (w - w') ⬝ᵥ G *ᵥ (w - w') = ((2 : ℤ) • k) ⬝ᵥ G *ᵥ ((2 : ℤ) • k) := by rw [hk]
  have hone : (w - w') ⬝ᵥ G *ᵥ w' = ((2 : ℤ) • k) ⬝ᵥ G *ᵥ w' := by rw [hk]
  rw [bil_sub_left, bil_sub_right, bil_sub_right, bil_smul_left, bil_smul_right, hww, hw'w',
    bil_comm hsymm w' w] at hsq
  rw [bil_sub_left, hw'w', bil_smul_left] at hone
  rw [bil_add_left, bil_add_right, bil_add_right, hw'w', bil_comm hsymm w' k]
  linarith

/-- **Normalised STEP-2 data.** Given `w, w'` of self-product `1` with `w − w' = 2k`, a sign `ε = ±1`
makes `k` (for `ε • w'`) have EVEN self-product. -/
theorem exists_char_normalization {n : ℕ} {G : Matrix (Fin n) (Fin n) ℤ} (hsymm : Gᵀ = G)
    {w w' k : Fin n → ℤ} (hww : w ⬝ᵥ G *ᵥ w = 1) (hw'w' : w' ⬝ᵥ G *ᵥ w' = 1)
    (hk : w - w' = (2 : ℤ) • k) :
    ∃ (ε : ℤ) (k' : Fin n → ℤ) (t : ℤ), (ε = 1 ∨ ε = -1) ∧
      w - ε • w' = (2 : ℤ) • k' ∧ k' ⬝ᵥ G *ᵥ k' = 2 * t := by
  rcases Int.even_or_odd (k ⬝ᵥ G *ᵥ k) with ⟨s, hs⟩ | ⟨s, hs⟩
  · exact ⟨1, k, s, Or.inl rfl, by simpa using hk, by rw [hs]; ring⟩
  · refine ⟨-1, k + w', -s, Or.inr rfl, ?_, ?_⟩
    · have : w - (-1 : ℤ) • w' = (w - w') + (2 : ℤ) • w' := by module
      rw [this, hk]; module
    · rw [char_k_sum_eq_one hsymm hww hw'w' hk, hs]; ring

/-! ### Lifting residual-block vectors into `⟨1⟩ ⊕ A`

The two hyperbolic planes that Eichler's criterion consumes live in `w^⊥ = A`. `resLift` embeds a
vector of `A` into `⟨1⟩ ⊕ A` under the reindexing; it preserves the bilinear form and lands in the
orthogonal complement of the adjoined generator. -/

/-- Embed a residual-block vector into `⟨1⟩ ⊕ A` (reindexed). -/
def resLift {n m : ℕ} (e : Fin 1 ⊕ Fin n ≃ Fin m) (x : Fin n → ℤ) : Fin m → ℤ :=
  (Sum.elim 0 x) ∘ e.symm

/-- The bilinear form is reindex-invariant. -/
theorem bil_reindex {n m : ℕ} (e : Fin 1 ⊕ Fin n ≃ Fin m)
    (G' : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℤ) (u v : Fin 1 ⊕ Fin n → ℤ) :
    (u ∘ e.symm) ⬝ᵥ (Matrix.reindex e e G') *ᵥ (v ∘ e.symm) = u ⬝ᵥ G' *ᵥ v := by
  have hmv : ∀ i, ((Matrix.reindex e e G') *ᵥ (v ∘ e.symm)) i = (G' *ᵥ v) (e.symm i) := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
      Function.comp_apply]
    exact Equiv.sum_comp e.symm (fun b => G' (e.symm i) b * v b)
  calc (u ∘ e.symm) ⬝ᵥ (Matrix.reindex e e G') *ᵥ (v ∘ e.symm)
      = ∑ i, u (e.symm i) * (G' *ᵥ v) (e.symm i) := by
        simp only [dotProduct, Function.comp_apply]
        exact Finset.sum_congr rfl fun i _ => by rw [hmv i]
    _ = u ⬝ᵥ G' *ᵥ v := Equiv.sum_comp e.symm (fun a => u a * (G' *ᵥ v) a)

/-- The adjoined generator, as the reindexing of the `Fin 1 ⊕ Fin n` standard vector. -/
theorem unitGen_eq_comp {n m : ℕ} (e : Fin 1 ⊕ Fin n ≃ Fin m) :
    unitGen e = (Pi.single (Sum.inl 0) (1 : ℤ)) ∘ e.symm := by
  funext i
  rw [unitGen, Function.comp_apply, Pi.single_apply, Pi.single_apply]
  by_cases h : i = e (Sum.inl 0)
  · subst h; simp
  · have : e.symm i ≠ Sum.inl 0 := by
      intro hcon
      exact h (by rw [← hcon, Equiv.apply_symm_apply])
    simp [h, this]

/-- `resLift` preserves the bilinear form. -/
theorem resLift_bil {n m : ℕ} (e : Fin 1 ⊕ Fin n ≃ Fin m) (A : Matrix (Fin n) (Fin n) ℤ)
    (x y : Fin n → ℤ) :
    (resLift e x) ⬝ᵥ (Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 A)) *ᵥ (resLift e y)
      = x ⬝ᵥ A *ᵥ y := by
  rw [resLift, resLift, bil_reindex]
  rw [show (Sum.elim 0 y : Fin 1 ⊕ Fin n → ℤ) = Sum.elim (0 : Fin 1 → ℤ) y from rfl]
  rw [Matrix.fromBlocks_mulVec]
  simp [dotProduct, Fintype.sum_sum_type]

/-- `resLift` lands in the orthogonal complement of the adjoined generator. -/
theorem resLift_perp_gen {n m : ℕ} (e : Fin 1 ⊕ Fin n ≃ Fin m) (A : Matrix (Fin n) (Fin n) ℤ)
    (x : Fin n → ℤ) :
    (resLift e x) ⬝ᵥ (Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 A)) *ᵥ (unitGen e) = 0 := by
  rw [resLift, unitGen_eq_comp, bil_reindex]
  rw [show (Pi.single (Sum.inl 0) (1 : ℤ) : Fin 1 ⊕ Fin n → ℤ)
      = Sum.elim (Pi.single 0 (1 : ℤ)) 0 by
    funext a; match a with
    | Sum.inl i => have : i = 0 := Subsingleton.elim i 0
                   subst this; simp
    | Sum.inr j => simp]
  rw [Matrix.fromBlocks_mulVec]
  have hz : (Pi.single (Sum.inl 0) (1 : ℤ) : Fin 1 ⊕ Fin n → ℤ) ∘ Sum.inr = 0 := by
    funext j; simp
  simp [dotProduct, Fintype.sum_sum_type, hz]

/-! ### The two remaining inputs, and the reduction of `UnitCancellation` to them -/

/-- **Input (a): two orthogonal hyperbolic planes inside `A`.** For even unimodular `A` with
`min(σ⁺, σ⁻) ≥ 2` there are vectors `a, b, c, d` spanning `U ⊕ U₁` — the input of Eichler's
criterion. (`even_unimodular_indefinite_split_congr` peels one plane; iterating peels the second.) -/
def TwoHypPlanes : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), IsEvenUnimodular A →
    2 ≤ sigPos (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' →
    2 ≤ sigNeg (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' →
    ∃ a b c d : Fin n → ℤ,
      a ⬝ᵥ A *ᵥ a = 0 ∧ b ⬝ᵥ A *ᵥ b = 0 ∧ a ⬝ᵥ A *ᵥ b = 1 ∧
      c ⬝ᵥ A *ᵥ c = 0 ∧ d ⬝ᵥ A *ᵥ d = 0 ∧ c ⬝ᵥ A *ᵥ d = 1 ∧
      a ⬝ᵥ A *ᵥ c = 0 ∧ a ⬝ᵥ A *ᵥ d = 0 ∧ b ⬝ᵥ A *ᵥ c = 0 ∧ b ⬝ᵥ A *ᵥ d = 0

/-- **Input (b): STEP 1 of Eichler's criterion.** Given TWO orthogonal hyperbolic planes, both
orthogonal to the reference vector `w`, an arbitrary characteristic self-product-`1` vector `w'` can
be moved by an isometry into the orthogonal complement of the FIRST plane. This is exactly the
`SO⁺(U ⊕ U₁) ≅ (SL₂ℤ × SL₂ℤ)/±` normalisation that `exists_isometry_map_of_perp_hyp`'s docstring
flags as not being part of STEP 2. -/
def EichlerStepOne : Prop :=
  ∀ (m : ℕ) (G : Matrix (Fin m) (Fin m) ℤ), Gᵀ = G → IsUnimodular G →
    ∀ e₁ f₁ e₂ f₂ w w' : Fin m → ℤ,
      e₁ ⬝ᵥ G *ᵥ e₁ = 0 → f₁ ⬝ᵥ G *ᵥ f₁ = 0 → e₁ ⬝ᵥ G *ᵥ f₁ = 1 →
      e₂ ⬝ᵥ G *ᵥ e₂ = 0 → f₂ ⬝ᵥ G *ᵥ f₂ = 0 → e₂ ⬝ᵥ G *ᵥ f₂ = 1 →
      e₁ ⬝ᵥ G *ᵥ e₂ = 0 → e₁ ⬝ᵥ G *ᵥ f₂ = 0 → f₁ ⬝ᵥ G *ᵥ e₂ = 0 → f₁ ⬝ᵥ G *ᵥ f₂ = 0 →
      e₁ ⬝ᵥ G *ᵥ w = 0 → f₁ ⬝ᵥ G *ᵥ w = 0 → e₂ ⬝ᵥ G *ᵥ w = 0 → f₂ ⬝ᵥ G *ᵥ w = 0 →
      w ⬝ᵥ G *ᵥ w = 1 → w' ⬝ᵥ G *ᵥ w' = 1 → IsCharQ G w → IsCharQ G w' →
      ∃ T : Matrix (Fin m) (Fin m) ℤ, IsUnit T.det ∧ Tᵀ * G * T = G ∧
        e₁ ⬝ᵥ G *ᵥ (T *ᵥ w') = 0 ∧ f₁ ⬝ᵥ G *ᵥ (T *ᵥ w') = 0

/-- Composing an isometry of `G` with a congruence `G ≅ H`. -/
theorem isom_comp {n : ℕ} {G H X Y : Matrix (Fin n) (Fin n) ℤ}
    (hX : Xᵀ * G * X = G) (hY : Yᵀ * G * Y = H) : (X * Y)ᵀ * G * (X * Y) = H := by
  rw [Matrix.transpose_mul]
  calc Yᵀ * Xᵀ * G * (X * Y) = Yᵀ * (Xᵀ * G * X) * Y := by simp [Matrix.mul_assoc]
    _ = H := by rw [hX, hY]

/-- **The reduction.** `UnitCancellation` follows from the two-hyperbolic-plane datum and STEP 1 of
Eichler's criterion; STEP 2 (`exists_isometry_map_of_perp_hyp`) and the whole assembly above supply
everything else. -/
theorem unitCancellation_of (hplanes : TwoHypPlanes) (hstep1 : EichlerStepOne) :
    UnitCancellation := by
  classical
  intro n m A B eqv hA hB hspA hsnA hcong
  obtain ⟨S, hSdet, hSeq⟩ := hcong
  set G := Matrix.reindex eqv eqv (Matrix.fromBlocks !![1] 0 0 A) with hGdef
  set H := Matrix.reindex eqv eqv (Matrix.fromBlocks !![1] 0 0 B) with hHdef
  have hGsym : Gᵀ = G := unitExtend_symm eqv A hA.1
  have hGunim : IsUnimodular G := unitExtend_unimodular eqv A hA.2.1
  set w : Fin m → ℤ := unitGen eqv with hwdef
  -- the adjoined generator: self-product 1, characteristic
  have hgen_sq : ∀ C : Matrix (Fin n) (Fin n) ℤ,
      (unitGen eqv) ⬝ᵥ (Matrix.reindex eqv eqv (Matrix.fromBlocks !![1] 0 0 C)) *ᵥ
        (unitGen eqv) = 1 := by
    intro C
    rw [unitExtend_mulVec_gen eqv C, unitGen]
    simp
  have hww : w ⬝ᵥ G *ᵥ w = 1 := hgen_sq A
  have hcharw : IsCharQ G w := isCharQ_unitGen eqv A hA.1 hA.2.2
  -- the transported generator
  set w' : Fin m → ℤ := S *ᵥ w with hw'def
  have hw'w' : w' ⬝ᵥ G *ᵥ w' = 1 := by
    rw [hw'def, bil_congr_matrix, hSeq, hHdef]; exact hgen_sq B
  have hcharw' : IsCharQ G w' := IsCharQ.congr hSdet hSeq (isCharQ_unitGen eqv B hB.1 hB.2.2)
  -- two hyperbolic planes, lifted into `w^⊥`
  obtain ⟨a, b, c, d, haa, hbb, hab, hcc, hdd, hcd, hac, had, hbc, hbd⟩ :=
    hplanes n A hA hspA hsnA
  set e₁ := resLift eqv a with he₁def
  set f₁ := resLift eqv b with hf₁def
  set e₂ := resLift eqv c with he₂def
  set f₂ := resLift eqv d with hf₂def
  have hlift : ∀ x y : Fin n → ℤ, (resLift eqv x) ⬝ᵥ G *ᵥ (resLift eqv y) = x ⬝ᵥ A *ᵥ y :=
    fun x y => resLift_bil eqv A x y
  have hperp : ∀ x : Fin n → ℤ, (resLift eqv x) ⬝ᵥ G *ᵥ w = 0 :=
    fun x => resLift_perp_gen eqv A x
  -- STEP 1
  obtain ⟨T₁, hT₁det, hT₁iso, hT₁e, hT₁f⟩ :=
    hstep1 m G hGsym hGunim e₁ f₁ e₂ f₂ w w'
      (by rw [he₁def, hlift]; exact haa) (by rw [hf₁def, hlift]; exact hbb)
      (by rw [he₁def, hf₁def, hlift]; exact hab)
      (by rw [he₂def, hlift]; exact hcc) (by rw [hf₂def, hlift]; exact hdd)
      (by rw [he₂def, hf₂def, hlift]; exact hcd)
      (by rw [he₁def, he₂def, hlift]; exact hac) (by rw [he₁def, hf₂def, hlift]; exact had)
      (by rw [hf₁def, he₂def, hlift]; exact hbc) (by rw [hf₁def, hf₂def, hlift]; exact hbd)
      (hperp a) (hperp b) (hperp c) (hperp d) hww hw'w' hcharw hcharw'
  set v₁ : Fin m → ℤ := T₁ *ᵥ w' with hv₁def
  have hv₁v₁ : v₁ ⬝ᵥ G *ᵥ v₁ = 1 := by rw [hv₁def, bil_congr_matrix, hT₁iso]; exact hw'w'
  have hcharv₁ : IsCharQ G v₁ := IsCharQ.congr hT₁det hT₁iso hcharw'
  -- congruence mod `2L`, then the mod-4 sign normalisation
  obtain ⟨k, hk⟩ := exists_two_smul_sub_of_char hGunim hcharw hcharv₁
  obtain ⟨ε, k', t, hεpm, hk', hk'k'⟩ := exists_char_normalization hGsym hww hv₁v₁ hk
  have hεsq : ε * ε = 1 := by rcases hεpm with h | h <;> rw [h] <;> norm_num
  have hεunit : IsUnit ε := Int.isUnit_iff.mpr hεpm
  set v₂ : Fin m → ℤ := ε • v₁ with hv₂def
  have hv₂v₂ : v₂ ⬝ᵥ G *ᵥ v₂ = 1 := by
    rw [hv₂def, bil_smul_left, bil_smul_right, hv₁v₁, mul_one, hεsq]
  have he₁v₂ : e₁ ⬝ᵥ G *ᵥ v₂ = 0 := by rw [hv₂def, bil_smul_right, hT₁e, mul_zero]
  have hf₁v₂ : f₁ ⬝ᵥ G *ᵥ v₂ = 0 := by rw [hv₂def, bil_smul_right, hT₁f, mul_zero]
  -- STEP 2: the three-transvection chain
  obtain ⟨T₂, hT₂det, hT₂iso, hT₂w⟩ :=
    exists_isometry_map_of_perp_hyp G hGsym hGunim e₁ f₁ w v₂ k' t
      (by rw [he₁def, hlift]; exact haa) (by rw [hf₁def, hlift]; exact hbb)
      (by rw [he₁def, hf₁def, hlift]; exact hab)
      hww hv₂v₂ (hperp a) (hperp b) he₁v₂ hf₁v₂ hk' hk'k'
  -- assemble the generator-fixing isometry `Φ = T₂⁻¹ (ε T₁) S`
  letI := T₂.invertibleOfIsUnitDet hT₂det
  have hT₂'iso : (⅟T₂)ᵀ * G * (⅟T₂) = G := by
    have hid : (T₂ * ⅟T₂)ᵀ * G * (T₂ * ⅟T₂) = G := by rw [mul_invOf_self]; simp
    rw [Matrix.transpose_mul] at hid
    calc (⅟T₂)ᵀ * G * (⅟T₂) = (⅟T₂)ᵀ * (T₂ᵀ * G * T₂) * (⅟T₂) := by rw [hT₂iso]
      _ = (⅟T₂)ᵀ * T₂ᵀ * G * (T₂ * ⅟T₂) := by simp [Matrix.mul_assoc]
      _ = G := hid
  have hεT₁iso : (ε • T₁)ᵀ * G * (ε • T₁) = G := by
    have hs : (ε • T₁)ᵀ * G * (ε • T₁) = (ε * ε) • (T₁ᵀ * G * T₁) := by
      rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    rw [hs, hT₁iso, hεsq, one_smul]
  set Φ : Matrix (Fin m) (Fin m) ℤ := (⅟T₂) * ((ε • T₁) * S) with hΦdef
  have hΦconj : Φᵀ * G * Φ = H := isom_comp hT₂'iso (isom_comp hεT₁iso hSeq)
  have hΦfix : Φ *ᵥ w = w := by
    rw [hΦdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hw'def,
      Matrix.smul_mulVec, ← hv₁def, ← hv₂def, ← hT₂w, Matrix.mulVec_mulVec,
      invOf_mul_self, Matrix.one_mulVec]
  have hΦdet : IsUnit Φ.det := by
    have h1 : IsUnit (⅟T₂).det := by
      refine IsUnit.of_mul_eq_one T₂.det ?_
      rw [← Matrix.det_mul, invOf_mul_self, Matrix.det_one]
    have h2 : IsUnit (ε • T₁).det := by
      rw [Matrix.det_smul]
      exact (hεunit.pow _).mul hT₁det
    rw [hΦdef, Matrix.det_mul, Matrix.det_mul]
    exact h1.mul (h2.mul hSdet)
  exact intCongr_of_unitFixing eqv A B Φ hΦdet hΦfix hΦconj

end SKEFTHawking
