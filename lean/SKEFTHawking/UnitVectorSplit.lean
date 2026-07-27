/-
# Phase 5q.H (K8b interior) — the unit-vector split engine

The rank-1 analogue of `SplitHyperbolic`: from a vector `x` of self-product `±1` in an integer
symmetric form `M`, split off the rank-1 block `⟨ε⟩`:

  `M ≅ ⟨ε⟩ ⊕ M'`,  `M'` symmetric unimodular of rank `n − 1`, `σ(M') = σ(M) − ε`.

This mirrors, one rank down, the hyperbolic machinery `hypPerp` / `hypPerpBasis` / `hypFullBasis` /
`residGram` / `gramB_eq` / `latticeSig_split` of `LatticePrimitive` + `SplitHyperbolic`:

* `unitPerp` — the orthogonal complement `x^⊥ = {y | xᵀMy = 0}`;
* `unit_isCompl` — `ℤⁿ = ℤx ⊕ x^⊥` (the projector is `y ↦ y − ε(xᵀMy)·x`, integral because `ε² = 1`);
* `unitPerpBasis` / `unitFullBasis` — a ℤ-basis of `x^⊥` and the adapted basis of `ℤⁿ`;
* `unitResidGram` — the residual `(n−1) × (n−1)` Gram matrix `M'`;
* `unitGramB_eq` — the block identity `Gram = ⟨ε⟩ ⊕ M'`;
* `unit_split_congr` — the packaged `IntCongr` with the determinant and signature bookkeeping.

No primitivity hypothesis is needed: `x ⬝ᵥ (M *ᵥ x) = ±1` already exhibits `x` as primitive.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.LatticePrimitive
import SKEFTHawking.SplitHyperbolic
import SKEFTHawking.HyperbolicNormalForm
import SKEFTHawking.OddIndefiniteUnitVector

namespace SKEFTHawking

open Matrix Module

/-! ### The orthogonal complement of a unit vector -/

/-- The **orthogonal complement** `x^⊥ = {y | xᵀMy = 0}` of a single vector, as a submodule of `ℤⁿ`.
The rank-1 analogue of `hypPerp`. -/
def unitPerp {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    Submodule ℤ (Fin n → ℤ) where
  carrier := {y | x ⬝ᵥ M *ᵥ y = 0}
  add_mem' := by
    rintro a b ha hb
    show x ⬝ᵥ M *ᵥ (a + b) = 0
    rw [Matrix.mulVec_add, dotProduct_add]; simp_all
  zero_mem' := by simp
  smul_mem' := by
    rintro c a ha
    show x ⬝ᵥ M *ᵥ (c • a) = 0
    rw [Matrix.mulVec_smul, dotProduct_smul]; simp_all

theorem mem_unitPerp {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ} {x y : Fin n → ℤ} :
    y ∈ unitPerp M x ↔ x ⬝ᵥ M *ᵥ y = 0 := Iff.rfl

/-- **The projector onto `x^⊥`** lands in `x^⊥`: `q(y) = y − ε·(xᵀMy)·x` is orthogonal to `x`. It is
integral precisely because `ε² = 1`. -/
theorem unit_proj_ortho {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) (ε : ℤ)
    (hx : x ⬝ᵥ M *ᵥ x = ε) (hε : ε * ε = 1) (y : Fin n → ℤ) :
    x ⬝ᵥ M *ᵥ (y - (ε * (x ⬝ᵥ M *ᵥ y)) • x) = 0 := by
  rw [gramPair_sub_right, gramPair_smul_right, hx]
  linear_combination (-(x ⬝ᵥ M *ᵥ y)) * hε

/-- **The splitting `ℤⁿ = ℤx ⊕ x^⊥`** for a vector of self-product `ε = ±1`. Disjointness: `a·x ∈ x^⊥`
forces `aε = 0`, hence `a = 0`. Codisjointness: `y = ε(xᵀMy)·x + q(y)` with `q(y) ∈ x^⊥`
(`unit_proj_ortho`). The rank-1 analogue of `hyperbolic_isCompl`. -/
theorem unit_isCompl {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) (ε : ℤ)
    (hx : x ⬝ᵥ M *ᵥ x = ε) (hε : ε * ε = 1) :
    IsCompl (Submodule.span ℤ {x}) (unitPerp M x) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro y hyK hyP
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hyK
    have h : a * ε = 0 := by
      have := (mem_unitPerp).mp hyP
      rwa [gramPair_smul_right, hx] at this
    have ha : a = 0 := by
      rcases mul_eq_zero.mp h with h1 | h1
      · exact h1
      · exact absurd h1 (by intro h0; rw [h0] at hε; simp at hε)
    rw [ha, zero_smul]
  · rw [codisjoint_iff_le_sup]
    intro y _
    rw [Submodule.mem_sup]
    exact ⟨(ε * (x ⬝ᵥ M *ᵥ y)) • x, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x),
      y - (ε * (x ⬝ᵥ M *ᵥ y)) • x, unit_proj_ortho M x ε hx hε y, by abel⟩

/-- A vector of self-product `ε = ±1` is **linearly independent** as a one-element family. -/
theorem unit_linearIndependent {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) (ε : ℤ)
    (hx : x ⬝ᵥ M *ᵥ x = ε) (hε : ε * ε = 1) : LinearIndependent ℤ ![x] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h0 : g 0 • x = 0 := by simpa [Fin.sum_univ_one] using hg
  have h1 : (g 0) * ε = 0 := by
    have h2 : x ⬝ᵥ M *ᵥ ((g 0) • x) = 0 := by rw [h0]; simp
    rwa [gramPair_smul_right, hx] at h2
  have hg0 : g 0 = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h (by intro h'; rw [h'] at hε; simp at hε)
  fin_cases i; exact hg0

/-- The complement `x^⊥` is **free of rank `n − 1`**: it is a direct summand of `ℤⁿ` and `ℤx` has
rank `1`. The rank-1 analogue of `hypPerp_finrank`. -/
theorem unitPerp_finrank {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ)
    (hindep : LinearIndependent ℤ ![x])
    (hic : IsCompl (Submodule.span ℤ {x}) (unitPerp M x)) :
    Module.finrank ℤ (unitPerp M x) = n - 1 := by
  have hspan : Submodule.span ℤ {x} = Submodule.span ℤ (Set.range ![x]) := by
    congr 1; ext y
    simp only [Set.mem_singleton_iff, Set.mem_range, Fin.exists_fin_one, Matrix.cons_val_zero]
    exact eq_comm
  have hK : Module.finrank ℤ (Submodule.span ℤ {x}) = 1 := by
    rw [hspan, finrank_span_eq_card hindep]; simp
  have hprod := (Submodule.prodEquivOfIsCompl _ _ hic).finrank_eq
  rw [Module.finrank_prod, hK] at hprod
  have hn : Module.finrank ℤ (Fin n → ℤ) = n := by simp
  rw [hn] at hprod
  omega

/-- A concrete ℤ-basis of `x^⊥`, indexed by `Fin (n−1)`. The rank-1 analogue of `hypPerpBasis`. -/
noncomputable def unitPerpBasis {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ)
    (hfr : Module.finrank ℤ (unitPerp M x) = n - 1) :
    Module.Basis (Fin (n - 1)) ℤ (unitPerp M x) :=
  (Module.finBasis ℤ (unitPerp M x)).reindex (finCongr hfr)

/-- Each `x^⊥`-basis vector is orthogonal to `x` — immediate from membership. -/
theorem unitPerpBasis_ortho {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ)
    (hfr : Module.finrank ℤ (unitPerp M x) = n - 1) (i : Fin (n - 1)) :
    x ⬝ᵥ M *ᵥ ((unitPerpBasis M x hfr i : Fin n → ℤ)) = 0 :=
  (unitPerpBasis M x hfr i).2

/-- The **combined basis of `ℤⁿ`** adapted to `ℤⁿ = ℤx ⊕ x^⊥`, indexed by `Fin 1 ⊕ Fin (n−1)`.
The rank-1 analogue of `hypFullBasis`. -/
noncomputable def unitFullBasis {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) (ε : ℤ)
    (hx : x ⬝ᵥ M *ᵥ x = ε) (hε : ε * ε = 1)
    (hfr : Module.finrank ℤ (unitPerp M x) = n - 1) :
    Module.Basis (Fin 1 ⊕ Fin (n - 1)) ℤ (Fin n → ℤ) :=
  let hindep := unit_linearIndependent M x ε hx hε
  let hic := unit_isCompl M x ε hx hε
  have hspan : Submodule.span ℤ {x} = Submodule.span ℤ (Set.range ![x]) := by
    congr 1; ext y
    simp only [Set.mem_singleton_iff, Set.mem_range, Fin.exists_fin_one, Matrix.cons_val_zero]
    exact eq_comm
  let bK : Module.Basis (Fin 1) ℤ ↥(Submodule.span ℤ {x}) :=
    (Module.Basis.span hindep).map (LinearEquiv.ofEq _ _ hspan.symm)
  (bK.prod (unitPerpBasis M x hfr)).map (Submodule.prodEquivOfIsCompl _ _ hic)

/-- The `ℤx`-part of `unitFullBasis` is `x`. -/
theorem unitFullBasis_inl {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) (ε : ℤ)
    (hx : x ⬝ᵥ M *ᵥ x = ε) (hε : ε * ε = 1)
    (hfr : Module.finrank ℤ (unitPerp M x) = n - 1) (k : Fin 1) :
    (unitFullBasis M x ε hx hε hfr (Sum.inl k) : Fin n → ℤ) = x := by
  simp only [unitFullBasis, Module.Basis.map_apply, Module.Basis.prod_apply, Sum.elim_inl,
    Function.comp_apply, LinearMap.inl_apply]
  rw [Submodule.prodEquivOfIsCompl]
  simp [LinearMap.coprod_apply, Module.Basis.span_apply]

/-- The `x^⊥`-part of `unitFullBasis` is the `unitPerpBasis`. -/
theorem unitFullBasis_inr {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) (ε : ℤ)
    (hx : x ⬝ᵥ M *ᵥ x = ε) (hε : ε * ε = 1)
    (hfr : Module.finrank ℤ (unitPerp M x) = n - 1) (i : Fin (n - 1)) :
    (unitFullBasis M x ε hx hε hfr (Sum.inr i) : Fin n → ℤ)
      = (unitPerpBasis M x hfr i : Fin n → ℤ) := by
  simp only [unitFullBasis, Module.Basis.map_apply, Module.Basis.prod_apply, Sum.elim_inr,
    Function.comp_apply, LinearMap.inr_apply]
  rw [Submodule.prodEquivOfIsCompl]
  simp [LinearMap.coprod_apply]

/-- The **residual Gram matrix** `M'` of `M` restricted to `x^⊥` in the `unitPerpBasis`. The rank-1
analogue of `residGram`. -/
noncomputable def unitResidGram {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ)
    (hfr : Module.finrank ℤ (unitPerp M x) = n - 1) : Matrix (Fin (n - 1)) (Fin (n - 1)) ℤ :=
  fun i j => (unitPerpBasis M x hfr i : Fin n → ℤ) ⬝ᵥ M *ᵥ (unitPerpBasis M x hfr j : Fin n → ℤ)

/-- The residual form is **symmetric** (inherited from `M`). -/
theorem unitResidGram_symm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hsymm : Mᵀ = M) (x : Fin n → ℤ)
    (hfr : Module.finrank ℤ (unitPerp M x) = n - 1) :
    (unitResidGram M x hfr)ᵀ = unitResidGram M x hfr := by
  ext i j
  show (unitPerpBasis M x hfr j : Fin n → ℤ) ⬝ᵥ M *ᵥ _
      = (unitPerpBasis M x hfr i : Fin n → ℤ) ⬝ᵥ M *ᵥ _
  rw [gramPair_comm hsymm]

/-- **The Gram of `M` in the combined basis is block-diagonal `⟨ε⟩ ⊕ M'`.** The rank-1 analogue of
`gramB_eq`: the `[0][0]` entry is `xᵀMx = ε`, the off-diagonal blocks vanish by `unitPerpBasis_ortho`,
and the lower-right block is `unitResidGram` by definition. -/
theorem unitGramB_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hsymm : Mᵀ = M) (x : Fin n → ℤ)
    (ε : ℤ) (hx : x ⬝ᵥ M *ᵥ x = ε) (hε : ε * ε = 1)
    (hfr : Module.finrank ℤ (unitPerp M x) = n - 1) :
    Matrix.of (fun s t => (unitFullBasis M x ε hx hε hfr s : Fin n → ℤ) ⬝ᵥ
        M *ᵥ (unitFullBasis M x ε hx hε hfr t : Fin n → ℤ))
      = Matrix.fromBlocks !![ε] 0 0 (unitResidGram M x hfr) := by
  ext s t
  rcases s with k | i <;> rcases t with l | j
  · rw [Matrix.of_apply, unitFullBasis_inl, unitFullBasis_inl, Matrix.fromBlocks_apply₁₁]
    fin_cases k <;> fin_cases l <;> simpa using hx
  · rw [Matrix.of_apply, unitFullBasis_inl, unitFullBasis_inr, Matrix.fromBlocks_apply₁₂,
      Matrix.zero_apply]
    exact unitPerpBasis_ortho M x hfr j
  · rw [Matrix.of_apply, unitFullBasis_inr, unitFullBasis_inl, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply, gramPair_comm hsymm]
    exact unitPerpBasis_ortho M x hfr i
  · rw [Matrix.of_apply, unitFullBasis_inr, unitFullBasis_inr, Matrix.fromBlocks_apply₂₂]
    rfl

/-! ### The packaged split -/

/-- `⟨ε⟩` is nondegenerate over `ℝ` for `ε = ±1` — the block-additivity side condition. -/
theorem unitBlock_radical {ε : ℤ} (hε : ε * ε = 1) :
    ((!![ε] : Matrix (Fin 1) (Fin 1) ℤ).map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥ := by
  apply nondeg_radical_eq_bot
  · rw [← Matrix.transpose_map]; congr 1; ext i j; fin_cases i <;> fin_cases j <;> rfl
  · refine cast_nondegenerate _ ?_
    rw [Matrix.det_fin_one]
    simp only [Matrix.cons_val_fin_one, Matrix.cons_val', Matrix.empty_val', Matrix.of_apply]
    intro h; rw [h] at hε; simp at hε

/-- `σ(⟨1⟩) = 1`. -/
theorem latticeSig_unitBlock_one : latticeSig (!![1] : Matrix (Fin 1) (Fin 1) ℤ) = 1 := by
  have hpd : ((!![1] : Matrix (Fin 1) (Fin 1) ℤ).map (Int.cast : ℤ → ℝ)).PosDef := by
    have : (!![1] : Matrix (Fin 1) (Fin 1) ℤ).map (Int.cast : ℤ → ℝ)
        = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [this]; exact Matrix.PosDef.one
  simpa using latticeSig_of_posDef _ hpd

/-- `σ(⟨−1⟩) = −1`. -/
theorem latticeSig_unitBlock_neg_one : latticeSig (!![-1] : Matrix (Fin 1) (Fin 1) ℤ) = -1 := by
  have hpd : (((-(!![-1] : Matrix (Fin 1) (Fin 1) ℤ))).map (Int.cast : ℤ → ℝ)).PosDef := by
    have : ((-(!![-1] : Matrix (Fin 1) (Fin 1) ℤ))).map (Int.cast : ℤ → ℝ)
        = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [this]; exact Matrix.PosDef.one
  simpa using latticeSig_of_negDef _ hpd

/-- `σ(⟨ε⟩) = ε` for `ε = ±1`. -/
theorem latticeSig_unitBlock {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    latticeSig (!![ε] : Matrix (Fin 1) (Fin 1) ℤ) = ε := by
  rcases hε with h | h <;> rw [h]
  · exact latticeSig_unitBlock_one
  · exact latticeSig_unitBlock_neg_one

/-- **Congruence extends through an arbitrary left block**: if `M' ≅ N'` then `A ⊕ M' ≅ A ⊕ N'`
(reindexed), via the block change of basis `1 ⊕ Q`. The general form of `IntCongr.hyp_block`. -/
theorem IntCongr.block_left {a q p : ℕ} (e : Fin a ⊕ Fin q ≃ Fin p) (A : Matrix (Fin a) (Fin a) ℤ)
    {M' N' : Matrix (Fin q) (Fin q) ℤ} (h : IntCongr M' N') :
    IntCongr (Matrix.reindex e e (Matrix.fromBlocks A 0 0 M'))
        (Matrix.reindex e e (Matrix.fromBlocks A 0 0 N')) := by
  obtain ⟨Q, hQ, hQeq⟩ := h
  refine ⟨Matrix.reindex e e (Matrix.fromBlocks 1 0 0 Q), ?_, ?_⟩
  · rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
    exact hQ
  · simp only [Matrix.reindex_apply, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]
    congr 1
    rw [Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.transpose_zero, add_zero, zero_add, hQeq]

/-- **The unit-vector split** (the rank-1 analogue of `even_unimodular_indefinite_split_congr`).
A symmetric unimodular form `M` containing a vector `x` of self-product `ε = ±1` is `IntCongr` to
`⟨ε⟩ ⊕ M'` (reindexed to `Fin n`), with `M'` symmetric unimodular of rank `n − 1` and
`σ(M') = σ(M) − ε`.

Construction: `unitFullBasis` (the adapted basis of `ℤⁿ = ℤx ⊕ x^⊥`) gives the unimodular change of
basis `P`; `unitGramB_eq` reads off the block form; `det M' = ε · det M` from
`det (⟨ε⟩ ⊕ M') = ε · det M'`; and the signature bookkeeping is block additivity plus `σ(⟨ε⟩) = ε`. -/
theorem unit_split_congr_of_finrank {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hsymm : Mᵀ = M)
    (hunim : IsUnimodular M) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (x : Fin n → ℤ)
    (hx : x ⬝ᵥ M *ᵥ x = ε) (hfr : Module.finrank ℤ (unitPerp M x) = n - 1) :
    ∃ e : Fin 1 ⊕ Fin (n - 1) ≃ Fin n,
      IntCongr M (Matrix.reindex e e (Matrix.fromBlocks !![ε] 0 0 (unitResidGram M x hfr)))
        ∧ IsUnimodular (unitResidGram M x hfr)
        ∧ latticeSig (unitResidGram M x hfr) = latticeSig M - ε := by
  classical
  have hεε : ε * ε = 1 := by rcases hε with h | h <;> rw [h] <;> ring
  have hn1 : 1 ≤ n := by
    by_contra hcon
    have hn0 : n = 0 := by omega
    subst hn0
    rw [show x ⬝ᵥ M *ᵥ x = 0 by simp] at hx
    rcases hε with h | h <;> rw [← hx] at h <;> simp at h
  set B := unitFullBasis M x ε hx hεε hfr with hB
  let e : Fin 1 ⊕ Fin (n - 1) ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))
  set B' := B.reindex e with hB'
  set P := (Pi.basisFun ℤ (Fin n)).toMatrix ⇑B' with hP
  have hP_entry : ∀ k l, P k l = (B' l) k := fun k l => by
    rw [hP, Basis.toMatrix_apply, Pi.basisFun_repr]
  have hPunit : IsUnit P.det := by
    have h1 : P.det * (B'.toMatrix ⇑(Pi.basisFun ℤ (Fin n))).det = 1 := by
      rw [hP, ← Matrix.det_mul, Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
    exact IsUnit.of_mul_eq_one _ h1
  have hPMP : Pᵀ * M * P
      = Matrix.reindex e e (Matrix.of (fun s t => (B s : Fin n → ℤ) ⬝ᵥ M *ᵥ (B t : Fin n → ℤ))) := by
    ext i j
    have hlhs : (Pᵀ * M * P) i j = (B' i) ⬝ᵥ M *ᵥ (B' j) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, hP_entry, Matrix.mulVec, dotProduct]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    rw [hlhs, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, hB',
      Basis.reindex_apply, Basis.reindex_apply]
  have hgram := unitGramB_eq M hsymm x ε hx hεε hfr
  have hcong : IntCongr M (Matrix.reindex e e (Matrix.fromBlocks !![ε] 0 0
      (unitResidGram M x hfr))) := ⟨P, hPunit, by rw [hPMP, hgram]⟩
  -- determinant bookkeeping
  have hdetblk : (Matrix.fromBlocks !![ε] 0 0 (unitResidGram M x hfr)).det
      = ε * (unitResidGram M x hfr).det := by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_fin_one]
    simp
  have hdetP2 : (P.det) ^ 2 = 1 := by
    rcases Int.isUnit_iff.mp hPunit with h | h <;> rw [h] <;> ring
  have hdetM : (unitResidGram M x hfr).det = ε * M.det := by
    have h1 : (Pᵀ * M * P).det = M.det := by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
      linear_combination M.det * hdetP2
    have h2 : (Pᵀ * M * P).det = ε * (unitResidGram M x hfr).det := by
      rw [hPMP, hgram, Matrix.det_reindex_self, hdetblk]
    rw [h1] at h2
    calc (unitResidGram M x hfr).det = (ε * ε) * (unitResidGram M x hfr).det := by
          rw [hεε]; ring
      _ = ε * (ε * (unitResidGram M x hfr).det) := by ring
      _ = ε * M.det := by rw [← h2]
  have hunim' : IsUnimodular (unitResidGram M x hfr) := by
    rw [IsUnimodular, hdetM]
    rcases hε with h | h <;> rcases hunim with h' | h' <;> rw [h, h'] <;> simp
  -- signature bookkeeping
  have hdetne : (unitResidGram M x hfr).det ≠ 0 := by
    rcases hunim' with h | h <;> rw [h] <;> norm_num
  have hrad : ((unitResidGram M x hfr).map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥ := by
    apply nondeg_radical_eq_bot
    · rw [← Matrix.transpose_map, unitResidGram_symm M hsymm]
    · exact cast_nondegenerate _ hdetne
  have hsig : latticeSig (unitResidGram M x hfr) = latticeSig M - ε := by
    have h := hcong.latticeSig
    rw [← latticeSigOf_fin, latticeSigOf_reindex,
      latticeSigOf_fromBlocks _ _ (unitBlock_radical hεε) hrad, latticeSigOf_fin, latticeSigOf_fin,
      latticeSig_unitBlock hε] at h
    omega
  exact ⟨e, hcong, hunim', hsig⟩

/-- **The unit-vector split, existential form.** Packages `unit_split_congr_of_finrank` with the
rank bookkeeping discharged. -/
theorem unit_split_congr {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hsymm : Mᵀ = M)
    (hunim : IsUnimodular M) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (x : Fin n → ℤ)
    (hx : x ⬝ᵥ M *ᵥ x = ε) :
    ∃ (M' : Matrix (Fin (n - 1)) (Fin (n - 1)) ℤ) (e : Fin 1 ⊕ Fin (n - 1) ≃ Fin n),
      IntCongr M (Matrix.reindex e e (Matrix.fromBlocks !![ε] 0 0 M'))
        ∧ M'ᵀ = M' ∧ IsUnimodular M' ∧ latticeSig M' = latticeSig M - ε := by
  have hεε : ε * ε = 1 := by rcases hε with h | h <;> rw [h] <;> ring
  have hfr := unitPerp_finrank M x (unit_linearIndependent M x ε hx hεε)
    (unit_isCompl M x ε hx hεε)
  obtain ⟨e, hcong, hunim', hsig⟩ := unit_split_congr_of_finrank M hsymm hunim ε hε x hx hfr
  exact ⟨unitResidGram M x hfr, e, hcong, unitResidGram_symm M hsymm x hfr, hunim', hsig⟩

/-! ### Transport between `x^⊥` and the residual Gram

The residual Gram `M'` is *the form `M` restricted to `x^⊥`, in coordinates*. The two lemmas below
make that precise in both directions — a coordinate vector gives an element of `x^⊥` with the same
Gram value (`unitResidGram_transport`), and every element of `x^⊥` is such a combination
(`unitPerp_exists_coords`). The payoff is `unitResidGram_even_value`: parity of the residual form is
exactly parity of `M` on `x^⊥`, which is how the induction of `OddFormDiagonalization` detects
whether a unit peel stranded an even residual. -/

/-- Bilinear expansion of the Gram pairing over coordinate combinations. -/
theorem gram_sum_expand {n m : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (b : Fin m → (Fin n → ℤ))
    (c c' : Fin m → ℤ) :
    (∑ i, c i • b i) ⬝ᵥ M *ᵥ (∑ j, c' j • b j) = ∑ i, ∑ j, c i * c' j * (b i ⬝ᵥ M *ᵥ b j) := by
  rw [Matrix.mulVec_sum, sum_dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_dotProduct, dotProduct_sum, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul]
  ring

/-- Entrywise expansion of a Gram pairing. -/
theorem gram_matrix_expand {m : ℕ} (M' : Matrix (Fin m) (Fin m) ℤ) (c c' : Fin m → ℤ) :
    c ⬝ᵥ M' *ᵥ c' = ∑ i, ∑ j, c i * c' j * (M' i j) := by
  rw [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Forward transport:** the `M`-pairing of two coordinate combinations of the `x^⊥`-basis is the
`M'`-pairing of their coordinate vectors. -/
theorem unitResidGram_transport {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ)
    (hfr : Module.finrank ℤ (unitPerp M x) = n - 1) (c c' : Fin (n - 1) → ℤ) :
    (∑ i, c i • (unitPerpBasis M x hfr i : Fin n → ℤ)) ⬝ᵥ M *ᵥ
        (∑ j, c' j • (unitPerpBasis M x hfr j : Fin n → ℤ))
      = c ⬝ᵥ (unitResidGram M x hfr) *ᵥ c' := by
  rw [gram_sum_expand, gram_matrix_expand]
  rfl

/-- A coordinate combination of the `x^⊥`-basis lies in `x^⊥`. -/
theorem unitPerp_mem_sum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ)
    (hfr : Module.finrank ℤ (unitPerp M x) = n - 1) (c : Fin (n - 1) → ℤ) :
    x ⬝ᵥ M *ᵥ (∑ i, c i • (unitPerpBasis M x hfr i : Fin n → ℤ)) = 0 := by
  rw [Matrix.mulVec_sum, dotProduct_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul, unitPerpBasis_ortho, smul_zero]

/-- **Backward transport:** every element of `x^⊥` is a coordinate combination of the basis. -/
theorem unitPerp_exists_coords {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ)
    (hfr : Module.finrank ℤ (unitPerp M x) = n - 1) (z : Fin n → ℤ) (hz : x ⬝ᵥ M *ᵥ z = 0) :
    ∃ c : Fin (n - 1) → ℤ, z = ∑ i, c i • (unitPerpBasis M x hfr i : Fin n → ℤ) := by
  set b := unitPerpBasis M x hfr with hb
  set zs : unitPerp M x := ⟨z, hz⟩ with hzs
  refine ⟨fun i => b.repr zs i, ?_⟩
  have h : (unitPerp M x).subtype (∑ i, (b.repr zs) i • b i)
      = ∑ i, (b.repr zs) i • ((b i : Fin n → ℤ)) := by
    rw [map_sum]; simp
  rw [b.sum_repr zs] at h
  exact h

/-- **Parity transport:** if the residual Gram is even, then `M` takes only even values on `x^⊥`.
Contrapositive: a vector of ODD self-product orthogonal to `x` witnesses that the residual is odd —
the detection used by the diagonalization induction. -/
theorem unitResidGram_even_value {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hsymm : Mᵀ = M)
    (x : Fin n → ℤ) (hfr : Module.finrank ℤ (unitPerp M x) = n - 1)
    (heven : ∀ i, 2 ∣ (unitResidGram M x hfr) i i)
    (z : Fin n → ℤ) (hz : x ⬝ᵥ M *ᵥ z = 0) : 2 ∣ z ⬝ᵥ M *ᵥ z := by
  obtain ⟨c, hc⟩ := unitPerp_exists_coords M x hfr z hz
  rw [hc, unitResidGram_transport]
  exact EvenLattice.even_form_dvd (unitResidGram_symm M hsymm x hfr) heven c

end SKEFTHawking
