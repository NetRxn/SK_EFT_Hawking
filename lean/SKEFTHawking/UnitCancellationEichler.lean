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
theorem bil_reindex {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (e : ι ≃ Fin m)
    (G' : Matrix ι ι ℤ) (u v : ι → ℤ) :
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

/-! ### Block plumbing for the two-plane extraction

The two hyperbolic planes come from iterating `even_unimodular_indefinite_split_congr`. Each peel
produces `A ≅ H ⊕ A'` in some reindexing `e`; the plane is the pair of first-block generators, and
the NEXT plane comes from the residual `A'` embedded through the second block. -/

section Blk
variable {p q m : ℕ}

/-- Embed a second-block vector into the reindexed block sum. -/
def blkLift (e : Fin p ⊕ Fin q ≃ Fin m) (x : Fin q → ℤ) : Fin m → ℤ := (Sum.elim 0 x) ∘ e.symm

/-- The `i`-th first-block generator of the reindexed block sum. -/
def blkGen (e : Fin p ⊕ Fin q ≃ Fin m) (i : Fin p) : Fin m → ℤ := Pi.single (e (Sum.inl i)) 1

theorem blkGen_eq_comp (e : Fin p ⊕ Fin q ≃ Fin m) (i : Fin p) :
    blkGen e i = (Pi.single (Sum.inl i) (1 : ℤ)) ∘ e.symm := by
  funext l
  rw [blkGen, Function.comp_apply, Pi.single_apply, Pi.single_apply]
  by_cases h : l = e (Sum.inl i)
  · subst h; simp
  · have : e.symm l ≠ Sum.inl i := fun hcon => h (by rw [← hcon, Equiv.apply_symm_apply])
    simp [h, this]

theorem single_inl_eq_elim (i : Fin p) :
    (Pi.single (Sum.inl i) (1 : ℤ) : Fin p ⊕ Fin q → ℤ) = Sum.elim (Pi.single i 1) 0 := by
  funext a
  match a with
  | Sum.inl j => simp [Pi.single_apply, Sum.inl.injEq]
  | Sum.inr j => simp

/-- Pairing of two first-block generators reads off the first block. -/
theorem bil_blk_gg (e : Fin p ⊕ Fin q ≃ Fin m) (C : Matrix (Fin p) (Fin p) ℤ)
    (D : Matrix (Fin q) (Fin q) ℤ) (i j : Fin p) :
    (blkGen e i) ⬝ᵥ (Matrix.reindex e e (Matrix.fromBlocks C 0 0 D)) *ᵥ (blkGen e j) = C i j := by
  have hbs : ∀ (N : ℕ) (M : Matrix (Fin N) (Fin N) ℤ) (a b : Fin N),
      (Pi.single a (1 : ℤ)) ⬝ᵥ M *ᵥ (Pi.single b 1) = M a b := by intro N M a b; simp
  rw [blkGen, blkGen, hbs, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁]

/-- First-block generators are orthogonal to second-block vectors. -/
theorem bil_blk_gl (e : Fin p ⊕ Fin q ≃ Fin m) (C : Matrix (Fin p) (Fin p) ℤ)
    (D : Matrix (Fin q) (Fin q) ℤ) (i : Fin p) (y : Fin q → ℤ) :
    (blkGen e i) ⬝ᵥ (Matrix.reindex e e (Matrix.fromBlocks C 0 0 D)) *ᵥ (blkLift e y) = 0 := by
  rw [blkGen_eq_comp, blkLift, bil_reindex, single_inl_eq_elim,
    show (Sum.elim 0 y : Fin p ⊕ Fin q → ℤ) = Sum.elim (0 : Fin p → ℤ) y from rfl,
    Matrix.fromBlocks_mulVec]
  simp [dotProduct, Fintype.sum_sum_type]

/-- Second-block vectors pair by the second block. -/
theorem bil_blk_ll (e : Fin p ⊕ Fin q ≃ Fin m) (C : Matrix (Fin p) (Fin p) ℤ)
    (D : Matrix (Fin q) (Fin q) ℤ) (x y : Fin q → ℤ) :
    (blkLift e x) ⬝ᵥ (Matrix.reindex e e (Matrix.fromBlocks C 0 0 D)) *ᵥ (blkLift e y)
      = x ⬝ᵥ D *ᵥ y := by
  rw [blkLift, blkLift, bil_reindex,
    show (Sum.elim 0 y : Fin p ⊕ Fin q → ℤ) = Sum.elim (0 : Fin p → ℤ) y from rfl,
    Matrix.fromBlocks_mulVec]
  simp [dotProduct, Fintype.sum_sum_type]

end Blk

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

/-- **Input (a) DISCHARGED.** Two orthogonal hyperbolic planes exist inside any even unimodular `A`
with `min(σ⁺, σ⁻) ≥ 2`: peel one plane with `even_unimodular_indefinite_split_congr`, note the
residual has `min(σ⁺, σ⁻) ≥ 1` (the hyperbolic block carries inertia `(1,1)`), and peel again. The
plane vectors are the images under the two congruences of the first-block generators. -/
theorem twoHypPlanes : TwoHypPlanes := by
  intro n A hA hsp hsn
  have hrank := sigPos_add_sigNeg_of_evenUnimodular A hA
  obtain ⟨A', e, hcongA, hA'eu, hA'sig⟩ :=
    even_unimodular_indefinite_split_congr A hA (by omega) (by omega)
  obtain ⟨P, hPdet, hPeq⟩ := hcongA
  have hrank' := sigPos_add_sigNeg_of_evenUnimodular A' hA'eu
  -- v4.32 `toQuadraticMap'`/`toQuadraticForm'` atom split (see `UnitBlockCancellation`): restate
  -- `hA'sig` once in these statements' own spelling — typechecks by defeq — so `omega` sees a
  -- single atom set instead of two.
  have hA'sig' : (sigPos (A'.map (Int.cast : ℤ → ℝ)).toQuadraticMap' : ℤ)
        - (sigNeg (A'.map (Int.cast : ℤ → ℝ)).toQuadraticMap' : ℤ)
      = (sigPos (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' : ℤ)
        - (sigNeg (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' : ℤ) := hA'sig
  have hsp' : 0 < sigPos (A'.map (Int.cast : ℤ → ℝ)).toQuadraticMap' := by omega
  have hsn' : 0 < sigNeg (A'.map (Int.cast : ℤ → ℝ)).toQuadraticMap' := by omega
  obtain ⟨A'', e', hcongA', -, -⟩ := even_unimodular_indefinite_split_congr A' hA'eu hsp' hsn'
  obtain ⟨Q, hQdet, hQeq⟩ := hcongA'
  have hbilP : ∀ x y : Fin n → ℤ, (P *ᵥ x) ⬝ᵥ A *ᵥ (P *ᵥ y)
      = x ⬝ᵥ (Matrix.reindex e e (Matrix.fromBlocks Hyp 0 0 A')) *ᵥ y := by
    intro x y; rw [bil_congr_matrix, hPeq]
  have hbilQ : ∀ x y : Fin (n - 2) → ℤ, (Q *ᵥ x) ⬝ᵥ A' *ᵥ (Q *ᵥ y)
      = x ⬝ᵥ (Matrix.reindex e' e' (Matrix.fromBlocks Hyp 0 0 A'')) *ᵥ y := by
    intro x y; rw [bil_congr_matrix, hQeq]
  refine ⟨P *ᵥ blkGen e 0, P *ᵥ blkGen e 1,
    P *ᵥ blkLift e (Q *ᵥ blkGen e' 0), P *ᵥ blkLift e (Q *ᵥ blkGen e' 1),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbilP, bil_blk_gg]; simp [Hyp]
  · rw [hbilP, bil_blk_gg]; simp [Hyp]
  · rw [hbilP, bil_blk_gg]; simp [Hyp]
  · rw [hbilP, bil_blk_ll, hbilQ, bil_blk_gg]; simp [Hyp]
  · rw [hbilP, bil_blk_ll, hbilQ, bil_blk_gg]; simp [Hyp]
  · rw [hbilP, bil_blk_ll, hbilQ, bil_blk_gg]; simp [Hyp]
  · rw [hbilP, bil_blk_gl]
  · rw [hbilP, bil_blk_gl]
  · rw [hbilP, bil_blk_gl]
  · rw [hbilP, bil_blk_gl]

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

/-! ### STEP 1: the `U ⊕ U₁` transvection move, and the residual gap

One Eichler transvection `t(e₂, p e₁ + q f₁)` changes the two first-plane pairings of `w'` by
`f₁·w' ↦ f₁·w' − (e₂·w') p` and `e₁·w' ↦ e₁·w' − (e₂·w') q`, leaving `e₂·w'` fixed. So STEP 1 closes
in ONE move as soon as `e₂·w'` divides both — which is the whole remaining content. -/

/-- **The `U ⊕ U₁` transvection move closes STEP 1 under a divisibility hypothesis.** The transvection
`t(e₂, p e₁ + q f₁)` (integral because `(p e₁ + q f₁)² = 2pq` is even) sends `f₁·w' ↦ f₁·w' − (e₂·w')p`
and `e₁·w' ↦ e₁·w' − (e₂·w')q`; with `p, q` the cofactors both pairings vanish. -/
theorem stepOne_of_dvd {m : ℕ} (G : Matrix (Fin m) (Fin m) ℤ) (hsymm : Gᵀ = G)
    (hunim : IsUnimodular G) (e₁ f₁ e₂ w' : Fin m → ℤ) (p q : ℤ)
    (he₁e₁ : e₁ ⬝ᵥ G *ᵥ e₁ = 0) (hf₁f₁ : f₁ ⬝ᵥ G *ᵥ f₁ = 0) (he₁f₁ : e₁ ⬝ᵥ G *ᵥ f₁ = 1)
    (he₂e₂ : e₂ ⬝ᵥ G *ᵥ e₂ = 0) (he₁e₂ : e₁ ⬝ᵥ G *ᵥ e₂ = 0) (hf₁e₂ : f₁ ⬝ᵥ G *ᵥ e₂ = 0)
    (hp : f₁ ⬝ᵥ G *ᵥ w' = (e₂ ⬝ᵥ G *ᵥ w') * p)
    (hq : e₁ ⬝ᵥ G *ᵥ w' = (e₂ ⬝ᵥ G *ᵥ w') * q) :
    ∃ T : Matrix (Fin m) (Fin m) ℤ, IsUnit T.det ∧ Tᵀ * G * T = G ∧
      e₁ ⬝ᵥ G *ᵥ (T *ᵥ w') = 0 ∧ f₁ ⬝ᵥ G *ᵥ (T *ᵥ w') = 0 := by
  set x : Fin m → ℤ := p • e₁ + q • f₁ with hxdef
  have he₂e₁ : e₂ ⬝ᵥ G *ᵥ e₁ = 0 := by rw [bil_comm hsymm]; exact he₁e₂
  have he₂f₁ : e₂ ⬝ᵥ G *ᵥ f₁ = 0 := by rw [bil_comm hsymm]; exact hf₁e₂
  have hf₁e₁ : f₁ ⬝ᵥ G *ᵥ e₁ = 1 := by rw [bil_comm hsymm]; exact he₁f₁
  have hux : e₂ ⬝ᵥ G *ᵥ x = 0 := by
    rw [hxdef, bil_add_right, bil_smul_right, bil_smul_right, he₂e₁, he₂f₁]; ring
  have hxx : x ⬝ᵥ G *ᵥ x = 2 * (p * q) := by
    rw [hxdef, bil_add_left, bil_add_right, bil_add_right, bil_smul_left, bil_smul_left,
      bil_smul_left, bil_smul_left, bil_smul_right, bil_smul_right, bil_smul_right,
      bil_smul_right, he₁e₁, hf₁f₁, he₁f₁, hf₁e₁]
    ring
  have he₁x : e₁ ⬝ᵥ G *ᵥ x = q := by
    rw [hxdef, bil_add_right, bil_smul_right, bil_smul_right, he₁e₁, he₁f₁]; ring
  have hf₁x : f₁ ⬝ᵥ G *ᵥ x = p := by
    rw [hxdef, bil_add_right, bil_smul_right, bil_smul_right, hf₁e₁, hf₁f₁]; ring
  refine ⟨eichler G e₂ x (p * q), eichler_isUnit_det G hsymm hunim e₂ x (p * q) he₂e₂ hux hxx,
    eichler_isometry G hsymm e₂ x (p * q) he₂e₂ hux hxx, ?_, ?_⟩
  · rw [eichler_mulVec_symm G hsymm, bil_sub_right, bil_sub_right, bil_add_right,
      bil_smul_right, bil_smul_right, bil_smul_right, he₁e₂, he₁x, hq]
    ring
  · rw [eichler_mulVec_symm G hsymm, bil_sub_right, bil_sub_right, bil_add_right,
      bil_smul_right, bil_smul_right, bil_smul_right, hf₁e₂, hf₁x, hp]
    ring

/-! #### The full `U ⊕ U₁` move toolkit

The Euclidean descent that closes STEP 1 needs, at each step, the effect of one Eichler transvection
on ALL FOUR pairings `e₁·w'`, `f₁·w'`, `e₂·w'`, `f₂·w'`. `planeMove` packages the transvection
`t(u, p a + q b)` for `u` isotropic orthogonal to a hyperbolic pair `(a, b)` — the only shape needed,
since `u` is always taken from one plane and `x` from the other. -/

/-- Master formula: the bilinear form after one Eichler transvection. -/
theorem eichler_bil {m : ℕ} (G : Matrix (Fin m) (Fin m) ℤ) (hsymm : Gᵀ = G)
    (u x : Fin m → ℤ) (h : ℤ) (y z : Fin m → ℤ) :
    y ⬝ᵥ G *ᵥ ((eichler G u x h) *ᵥ z)
      = y ⬝ᵥ G *ᵥ z + (x ⬝ᵥ G *ᵥ z) * (y ⬝ᵥ G *ᵥ u) - (u ⬝ᵥ G *ᵥ z) * (y ⬝ᵥ G *ᵥ x)
        - h * ((u ⬝ᵥ G *ᵥ z) * (y ⬝ᵥ G *ᵥ u)) := by
  rw [eichler_mulVec_symm G hsymm, bil_sub_right, bil_sub_right, bil_add_right,
    bil_smul_right, bil_smul_right, bil_smul_right]
  ring

/-- **The `U ⊕ U₁` Eichler move** `t(u, p a + q b)`: `u` isotropic and orthogonal to the hyperbolic
pair `(a, b)`. Integral because `(p a + q b)² = 2pq`. -/
def planeMove {m : ℕ} (G : Matrix (Fin m) (Fin m) ℤ) (u a b : Fin m → ℤ) (p q : ℤ) :
    Matrix (Fin m) (Fin m) ℤ := eichler G u (p • a + q • b) (p * q)

section PlaneMove
variable {m : ℕ} {G : Matrix (Fin m) (Fin m) ℤ} {u a b : Fin m → ℤ}

theorem planeMove_aux (hsymm : Gᵀ = G) (haa : a ⬝ᵥ G *ᵥ a = 0) (hbb : b ⬝ᵥ G *ᵥ b = 0)
    (hab : a ⬝ᵥ G *ᵥ b = 1) (hua : u ⬝ᵥ G *ᵥ a = 0) (hub : u ⬝ᵥ G *ᵥ b = 0) (p q : ℤ) :
    u ⬝ᵥ G *ᵥ (p • a + q • b) = 0 ∧
      (p • a + q • b) ⬝ᵥ G *ᵥ (p • a + q • b) = 2 * (p * q) := by
  have hba : b ⬝ᵥ G *ᵥ a = 1 := by rw [bil_comm hsymm]; exact hab
  constructor
  · rw [bil_add_right, bil_smul_right, bil_smul_right, hua, hub]; ring
  · rw [bil_add_left, bil_add_right, bil_add_right, bil_smul_left, bil_smul_left,
      bil_smul_left, bil_smul_left, bil_smul_right, bil_smul_right, bil_smul_right,
      bil_smul_right, haa, hbb, hab, hba]
    ring

/-- The plane move is an isometry of `G`. -/
theorem planeMove_isometry (hsymm : Gᵀ = G) (huu : u ⬝ᵥ G *ᵥ u = 0)
    (haa : a ⬝ᵥ G *ᵥ a = 0) (hbb : b ⬝ᵥ G *ᵥ b = 0) (hab : a ⬝ᵥ G *ᵥ b = 1)
    (hua : u ⬝ᵥ G *ᵥ a = 0) (hub : u ⬝ᵥ G *ᵥ b = 0) (p q : ℤ) :
    (planeMove G u a b p q)ᵀ * G * (planeMove G u a b p q) = G := by
  obtain ⟨h1, h2⟩ := planeMove_aux hsymm haa hbb hab hua hub p q
  exact eichler_isometry G hsymm u _ (p * q) huu h1 h2

/-- The plane move is unimodular. -/
theorem planeMove_isUnit_det (hsymm : Gᵀ = G) (hunim : IsUnimodular G)
    (huu : u ⬝ᵥ G *ᵥ u = 0) (haa : a ⬝ᵥ G *ᵥ a = 0) (hbb : b ⬝ᵥ G *ᵥ b = 0)
    (hab : a ⬝ᵥ G *ᵥ b = 1) (hua : u ⬝ᵥ G *ᵥ a = 0) (hub : u ⬝ᵥ G *ᵥ b = 0) (p q : ℤ) :
    IsUnit (planeMove G u a b p q).det := by
  obtain ⟨h1, h2⟩ := planeMove_aux hsymm haa hbb hab hua hub p q
  exact eichler_isUnit_det G hsymm hunim u _ (p * q) huu h1 h2

/-- **The coordinate effect of a plane move** on an arbitrary pairing. -/
theorem planeMove_bil (hsymm : Gᵀ = G) (p q : ℤ) (y z : Fin m → ℤ) :
    y ⬝ᵥ G *ᵥ ((planeMove G u a b p q) *ᵥ z)
      = y ⬝ᵥ G *ᵥ z
        + (p * (a ⬝ᵥ G *ᵥ z) + q * (b ⬝ᵥ G *ᵥ z)) * (y ⬝ᵥ G *ᵥ u)
        - (u ⬝ᵥ G *ᵥ z) * (p * (y ⬝ᵥ G *ᵥ a) + q * (y ⬝ᵥ G *ᵥ b))
        - p * q * ((u ⬝ᵥ G *ᵥ z) * (y ⬝ᵥ G *ᵥ u)) := by
  rw [planeMove, eichler_bil G hsymm, bil_add_left, bil_smul_left, bil_smul_left,
    bil_add_right, bil_smul_right, bil_smul_right]

end PlaneMove

/-! #### STEP 1 as a pure `ℤ⁴` reachability problem

`PlaneStep` is the *arithmetic shadow* of the four `U ⊕ U₁` Eichler moves on the coordinate 4-tuple
`(α, β, γ, δ) = (f₁·w', e₁·w', f₂·w', e₂·w')`. `planeReduction_lift` shows every arithmetic chain is
realised by an actual isometry — so STEP 1, and with it the whole K8b interior brick, reduces to the
GEOMETRY-FREE statement `PlaneReduction`: every tuple reaches one with `α = β = 0`. -/

/-- Two orthogonal hyperbolic planes for `G` — the input datum of Eichler's criterion. -/
structure TwoPlanes {m : ℕ} (G : Matrix (Fin m) (Fin m) ℤ) (e₁ f₁ e₂ f₂ : Fin m → ℤ) : Prop where
  ee₁ : e₁ ⬝ᵥ G *ᵥ e₁ = 0
  ff₁ : f₁ ⬝ᵥ G *ᵥ f₁ = 0
  ef₁ : e₁ ⬝ᵥ G *ᵥ f₁ = 1
  ee₂ : e₂ ⬝ᵥ G *ᵥ e₂ = 0
  ff₂ : f₂ ⬝ᵥ G *ᵥ f₂ = 0
  ef₂ : e₂ ⬝ᵥ G *ᵥ f₂ = 1
  e₁e₂ : e₁ ⬝ᵥ G *ᵥ e₂ = 0
  e₁f₂ : e₁ ⬝ᵥ G *ᵥ f₂ = 0
  f₁e₂ : f₁ ⬝ᵥ G *ᵥ e₂ = 0
  f₁f₂ : f₁ ⬝ᵥ G *ᵥ f₂ = 0

/-- **One arithmetic step**: the effect of a single `U ⊕ U₁` Eichler move on `(α, β, γ, δ)`. -/
inductive PlaneStep : ℤ × ℤ × ℤ × ℤ → ℤ × ℤ × ℤ × ℤ → Prop
  /-- `t(e₂, p e₁ + q f₁)`. -/
  | m₁ (p q α β γ δ : ℤ) :
      PlaneStep (α, β, γ, δ) (α - δ * p, β - δ * q, γ + (p * β + q * α) - p * q * δ, δ)
  /-- `t(f₂, p e₁ + q f₁)`. -/
  | m₂ (p q α β γ δ : ℤ) :
      PlaneStep (α, β, γ, δ) (α - γ * p, β - γ * q, γ, δ + (p * β + q * α) - p * q * γ)
  /-- `t(e₁, p e₂ + q f₂)`. -/
  | m₃ (p q α β γ δ : ℤ) :
      PlaneStep (α, β, γ, δ) (α + (p * δ + q * γ) - p * q * β, β, γ - p * β, δ - q * β)
  /-- `t(f₁, p e₂ + q f₂)`. -/
  | m₄ (p q α β γ δ : ℤ) :
      PlaneStep (α, β, γ, δ) (α, β + (p * δ + q * γ) - p * q * α, γ - p * α, δ - q * α)

/-- `w'` realises the coordinate tuple `t` in the two planes. -/
def Realizes {m : ℕ} (G : Matrix (Fin m) (Fin m) ℤ) (e₁ f₁ e₂ f₂ w' : Fin m → ℤ)
    (t : ℤ × ℤ × ℤ × ℤ) : Prop :=
  f₁ ⬝ᵥ G *ᵥ w' = t.1 ∧ e₁ ⬝ᵥ G *ᵥ w' = t.2.1 ∧
    f₂ ⬝ᵥ G *ᵥ w' = t.2.2.1 ∧ e₂ ⬝ᵥ G *ᵥ w' = t.2.2.2

section Lift
variable {m : ℕ} {G : Matrix (Fin m) (Fin m) ℤ} {e₁ f₁ e₂ f₂ : Fin m → ℤ}

set_option linter.unusedSimpArgs false in
/-- **Every arithmetic step is realised by an actual isometry.** -/
theorem planeStep_lift (hsymm : Gᵀ = G) (hunim : IsUnimodular G)
    (hp : TwoPlanes G e₁ f₁ e₂ f₂) {t t' : ℤ × ℤ × ℤ × ℤ} (hst : PlaneStep t t')
    {w' : Fin m → ℤ} (hr : Realizes G e₁ f₁ e₂ f₂ w' t) :
    ∃ T : Matrix (Fin m) (Fin m) ℤ, IsUnit T.det ∧ Tᵀ * G * T = G ∧
      Realizes G e₁ f₁ e₂ f₂ (T *ᵥ w') t' := by
  -- the reversed pairings
  have f₁e₁ : f₁ ⬝ᵥ G *ᵥ e₁ = 1 := by rw [bil_comm hsymm]; exact hp.ef₁
  have f₂e₂ : f₂ ⬝ᵥ G *ᵥ e₂ = 1 := by rw [bil_comm hsymm]; exact hp.ef₂
  have e₂e₁ : e₂ ⬝ᵥ G *ᵥ e₁ = 0 := by rw [bil_comm hsymm]; exact hp.e₁e₂
  have f₂e₁ : f₂ ⬝ᵥ G *ᵥ e₁ = 0 := by rw [bil_comm hsymm]; exact hp.e₁f₂
  have e₂f₁ : e₂ ⬝ᵥ G *ᵥ f₁ = 0 := by rw [bil_comm hsymm]; exact hp.f₁e₂
  have f₂f₁ : f₂ ⬝ᵥ G *ᵥ f₁ = 0 := by rw [bil_comm hsymm]; exact hp.f₁f₂
  cases hst with
  | m₁ p q α β γ δ =>
    obtain ⟨hα, hβ, hγ, hδ⟩ := hr
    dsimp only at hα hβ hγ hδ
    refine ⟨planeMove G e₂ e₁ f₁ p q,
      planeMove_isUnit_det hsymm hunim hp.ee₂ hp.ee₁ hp.ff₁ hp.ef₁ e₂e₁ e₂f₁ p q,
      planeMove_isometry hsymm hp.ee₂ hp.ee₁ hp.ff₁ hp.ef₁ e₂e₁ e₂f₁ p q, ?_, ?_, ?_, ?_⟩ <;>
    · dsimp only
      rw [planeMove_bil hsymm]
      simp only [hα, hβ, hγ, hδ, hp.ee₁, hp.ff₁, hp.ef₁, hp.ee₂, hp.ff₂, hp.ef₂, hp.e₁e₂,
        hp.e₁f₂, hp.f₁e₂, hp.f₁f₂, f₁e₁, f₂e₂, e₂e₁, f₂e₁, e₂f₁, f₂f₁]
      ring
  | m₂ p q α β γ δ =>
    obtain ⟨hα, hβ, hγ, hδ⟩ := hr
    dsimp only at hα hβ hγ hδ
    refine ⟨planeMove G f₂ e₁ f₁ p q,
      planeMove_isUnit_det hsymm hunim hp.ff₂ hp.ee₁ hp.ff₁ hp.ef₁ f₂e₁ f₂f₁ p q,
      planeMove_isometry hsymm hp.ff₂ hp.ee₁ hp.ff₁ hp.ef₁ f₂e₁ f₂f₁ p q, ?_, ?_, ?_, ?_⟩ <;>
    · dsimp only
      rw [planeMove_bil hsymm]
      simp only [hα, hβ, hγ, hδ, hp.ee₁, hp.ff₁, hp.ef₁, hp.ee₂, hp.ff₂, hp.ef₂, hp.e₁e₂,
        hp.e₁f₂, hp.f₁e₂, hp.f₁f₂, f₁e₁, f₂e₂, e₂e₁, f₂e₁, e₂f₁, f₂f₁]
      ring
  | m₃ p q α β γ δ =>
    obtain ⟨hα, hβ, hγ, hδ⟩ := hr
    dsimp only at hα hβ hγ hδ
    refine ⟨planeMove G e₁ e₂ f₂ p q,
      planeMove_isUnit_det hsymm hunim hp.ee₁ hp.ee₂ hp.ff₂ hp.ef₂ hp.e₁e₂ hp.e₁f₂ p q,
      planeMove_isometry hsymm hp.ee₁ hp.ee₂ hp.ff₂ hp.ef₂ hp.e₁e₂ hp.e₁f₂ p q, ?_, ?_, ?_, ?_⟩ <;>
    · dsimp only
      rw [planeMove_bil hsymm]
      simp only [hα, hβ, hγ, hδ, hp.ee₁, hp.ff₁, hp.ef₁, hp.ee₂, hp.ff₂, hp.ef₂, hp.e₁e₂,
        hp.e₁f₂, hp.f₁e₂, hp.f₁f₂, f₁e₁, f₂e₂, e₂e₁, f₂e₁, e₂f₁, f₂f₁]
      ring
  | m₄ p q α β γ δ =>
    obtain ⟨hα, hβ, hγ, hδ⟩ := hr
    dsimp only at hα hβ hγ hδ
    refine ⟨planeMove G f₁ e₂ f₂ p q,
      planeMove_isUnit_det hsymm hunim hp.ff₁ hp.ee₂ hp.ff₂ hp.ef₂ hp.f₁e₂ hp.f₁f₂ p q,
      planeMove_isometry hsymm hp.ff₁ hp.ee₂ hp.ff₂ hp.ef₂ hp.f₁e₂ hp.f₁f₂ p q, ?_, ?_, ?_, ?_⟩ <;>
    · dsimp only
      rw [planeMove_bil hsymm]
      simp only [hα, hβ, hγ, hδ, hp.ee₁, hp.ff₁, hp.ef₁, hp.ee₂, hp.ff₂, hp.ef₂, hp.e₁e₂,
        hp.e₁f₂, hp.f₁e₂, hp.f₁f₂, f₁e₁, f₂e₂, e₂e₁, f₂e₁, e₂f₁, f₂f₁]
      ring

/-- **Every arithmetic chain is realised by an isometry.** -/
theorem planeChain_lift (hsymm : Gᵀ = G) (hunim : IsUnimodular G)
    (hp : TwoPlanes G e₁ f₁ e₂ f₂) {t t' : ℤ × ℤ × ℤ × ℤ}
    (hch : Relation.ReflTransGen PlaneStep t t') :
    ∀ {w' : Fin m → ℤ}, Realizes G e₁ f₁ e₂ f₂ w' t →
      ∃ T : Matrix (Fin m) (Fin m) ℤ, IsUnit T.det ∧ Tᵀ * G * T = G ∧
        Realizes G e₁ f₁ e₂ f₂ (T *ᵥ w') t' := by
  induction hch with
  | refl =>
    intro w' hr
    exact ⟨1, by simp, by simp, by rwa [Matrix.one_mulVec]⟩
  | tail _ hlast ih =>
    intro w' hr
    obtain ⟨T, hTdet, hTiso, hTr⟩ := ih hr
    obtain ⟨T', hT'det, hT'iso, hT'r⟩ := planeStep_lift hsymm hunim hp hlast hTr
    exact ⟨T' * T, by rw [Matrix.det_mul]; exact hT'det.mul hTdet, isom_comp hT'iso hTiso,
      by rwa [← Matrix.mulVec_mulVec]⟩

end Lift

/-- **The GEOMETRY-FREE residue of the whole K8b interior brick.** Every integer 4-tuple reaches, via
the four `U ⊕ U₁` Eichler moves, one whose first two entries vanish. -/
def PlaneReduction : Prop :=
  ∀ α β γ δ : ℤ, ∃ γ' δ' : ℤ,
    Relation.ReflTransGen PlaneStep (α, β, γ, δ) (0, 0, γ', δ')

/-- **The terminal case of `PlaneReduction`, and its non-vacuity witness.** A tuple whose second
plane is trivial (`γ = δ = 0`) reduces in exactly TWO moves: `m₁` writes `gcd(α, β)` into `γ` by
Bézout, and `m₂` then divides it out of both `α` and `β`. So `PlaneReduction` is reduced to steering
an arbitrary tuple into `γ = δ = 0`. -/
theorem planeReduction_zero_tail (α β : ℤ) :
    ∃ γ' δ' : ℤ, Relation.ReflTransGen PlaneStep (α, β, 0, 0) (0, 0, γ', δ') := by
  set g : ℤ := (Int.gcd α β : ℤ) with hg
  obtain ⟨a, ha⟩ : g ∣ α := by rw [hg]; exact Int.gcd_dvd_left α β
  obtain ⟨b, hb⟩ : g ∣ β := by rw [hg]; exact Int.gcd_dvd_right α β
  have hval : (Int.gcdB α β) * β + (Int.gcdA α β) * α = g := by
    rw [hg, Int.gcd_eq_gcd_ab]; ring
  refine ⟨g, 0 + (a * β + b * α) - a * b * g, ?_⟩
  have h1 : PlaneStep (α, β, 0, 0) (α, β, g, 0) := by
    have h := PlaneStep.m₁ (Int.gcdB α β) (Int.gcdA α β) α β 0 0
    simp only [zero_mul, sub_zero, mul_zero, zero_add] at h
    rwa [hval] at h
  have h2 : PlaneStep (α, β, g, 0) (0, 0, g, 0 + (a * β + b * α) - a * b * g) := by
    have h := PlaneStep.m₂ a b α β g 0
    rwa [show α - g * a = 0 by rw [ha]; ring, show β - g * b = 0 by rw [hb]; ring] at h
  exact (Relation.ReflTransGen.single h1).tail h2

/-- **STEP 1 from the pure arithmetic statement.** -/
theorem eichlerStepOne_of_planeReduction (hred : PlaneReduction) : EichlerStepOne := by
  intro m G hsymm hunim e₁ f₁ e₂ f₂ w w'
  intro he₁e₁ hf₁f₁ he₁f₁ he₂e₂ hf₂f₂ he₂f₂ he₁e₂ he₁f₂ hf₁e₂ hf₁f₂
  intro _ _ _ _ _ _ _ _
  have hp : TwoPlanes G e₁ f₁ e₂ f₂ :=
    ⟨he₁e₁, hf₁f₁, he₁f₁, he₂e₂, hf₂f₂, he₂f₂, he₁e₂, he₁f₂, hf₁e₂, hf₁f₂⟩
  obtain ⟨γ', δ', hch⟩ :=
    hred (f₁ ⬝ᵥ G *ᵥ w') (e₁ ⬝ᵥ G *ᵥ w') (f₂ ⬝ᵥ G *ᵥ w') (e₂ ⬝ᵥ G *ᵥ w')
  obtain ⟨T, hTdet, hTiso, hTr⟩ :=
    planeChain_lift hsymm hunim hp hch ⟨rfl, rfl, rfl, rfl⟩
  exact ⟨T, hTdet, hTiso, hTr.2.1, hTr.1⟩

/-- **The residual gap of STEP 1.** After an isometry, the second plane's `e₂`-pairing with `w'`
should DIVIDE both first-plane pairings. This is the `SO⁺(U ⊕ U₁) ≅ (SL₂ℤ × SL₂ℤ)/±` reduction — a
Euclidean descent on the four `U ⊕ U₁` coordinates of `w'` — and it is all that remains. -/
def StepOneDivisorNormalization : Prop :=
  ∀ (m : ℕ) (G : Matrix (Fin m) (Fin m) ℤ), Gᵀ = G → IsUnimodular G →
    ∀ e₁ f₁ e₂ f₂ w w' : Fin m → ℤ,
      e₁ ⬝ᵥ G *ᵥ e₁ = 0 → f₁ ⬝ᵥ G *ᵥ f₁ = 0 → e₁ ⬝ᵥ G *ᵥ f₁ = 1 →
      e₂ ⬝ᵥ G *ᵥ e₂ = 0 → f₂ ⬝ᵥ G *ᵥ f₂ = 0 → e₂ ⬝ᵥ G *ᵥ f₂ = 1 →
      e₁ ⬝ᵥ G *ᵥ e₂ = 0 → e₁ ⬝ᵥ G *ᵥ f₂ = 0 → f₁ ⬝ᵥ G *ᵥ e₂ = 0 → f₁ ⬝ᵥ G *ᵥ f₂ = 0 →
      e₁ ⬝ᵥ G *ᵥ w = 0 → f₁ ⬝ᵥ G *ᵥ w = 0 → e₂ ⬝ᵥ G *ᵥ w = 0 → f₂ ⬝ᵥ G *ᵥ w = 0 →
      w ⬝ᵥ G *ᵥ w = 1 → w' ⬝ᵥ G *ᵥ w' = 1 → IsCharQ G w → IsCharQ G w' →
      ∃ T : Matrix (Fin m) (Fin m) ℤ, IsUnit T.det ∧ Tᵀ * G * T = G ∧
        (e₂ ⬝ᵥ G *ᵥ (T *ᵥ w')) ∣ (e₁ ⬝ᵥ G *ᵥ (T *ᵥ w')) ∧
        (e₂ ⬝ᵥ G *ᵥ (T *ᵥ w')) ∣ (f₁ ⬝ᵥ G *ᵥ (T *ᵥ w'))

/-- **STEP 1 from the divisibility normalisation**: normalise, then fire one transvection. -/
theorem eichlerStepOne_of_normalization (hnorm : StepOneDivisorNormalization) :
    EichlerStepOne := by
  intro m G hsymm hunim e₁ f₁ e₂ f₂ w w'
  intro he₁e₁ hf₁f₁ he₁f₁ he₂e₂ hf₂f₂ he₂f₂ he₁e₂ he₁f₂ hf₁e₂ hf₁f₂
  intro he₁w hf₁w he₂w hf₂w hww hw'w' hcw hcw'
  obtain ⟨T₀, hT₀det, hT₀iso, hdvdq, hdvdp⟩ :=
    hnorm m G hsymm hunim e₁ f₁ e₂ f₂ w w' he₁e₁ hf₁f₁ he₁f₁ he₂e₂ hf₂f₂ he₂f₂
      he₁e₂ he₁f₂ hf₁e₂ hf₁f₂ he₁w hf₁w he₂w hf₂w hww hw'w' hcw hcw'
  obtain ⟨q, hq⟩ := hdvdq
  obtain ⟨p, hp⟩ := hdvdp
  obtain ⟨T₁, hT₁det, hT₁iso, hT₁e, hT₁f⟩ :=
    stepOne_of_dvd G hsymm hunim e₁ f₁ e₂ (T₀ *ᵥ w') p q he₁e₁ hf₁f₁ he₁f₁ he₂e₂ he₁e₂ hf₁e₂ hp hq
  refine ⟨T₁ * T₀, ?_, isom_comp hT₁iso hT₀iso, ?_, ?_⟩
  · rw [Matrix.det_mul]; exact hT₁det.mul hT₀det
  · rw [← Matrix.mulVec_mulVec]; exact hT₁e
  · rw [← Matrix.mulVec_mulVec]; exact hT₁f

/-- **`UnitCancellation` now rests on STEP 1 of Eichler's criterion ALONE.** The two-hyperbolic-plane
datum is discharged (`twoHypPlanes`), STEP 2 is discharged
(`exists_isometry_map_of_perp_hyp`), and the whole assembly between them is discharged above. -/
theorem unitCancellation_of_stepOne (hstep1 : EichlerStepOne) : UnitCancellation :=
  unitCancellation_of twoHypPlanes hstep1

/-- **`StableNegRank16Two` from STEP 1 alone** — the K8b interior brick, one input away. -/
theorem stableNegRank16Two_of_stepOne (hstep1 : EichlerStepOne) : StableNegRank16Two :=
  stableNegRank16Two_of_unitCancellation (unitCancellation_of_stepOne hstep1)

/-- **`UnitCancellation` from the pure arithmetic statement.** -/
theorem unitCancellation_of_planeReduction (hred : PlaneReduction) : UnitCancellation :=
  unitCancellation_of_stepOne (eichlerStepOne_of_planeReduction hred)

end SKEFTHawking
