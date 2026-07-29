/-
# Phase 5q.H — the FULL-RANK SUBLATTICE route to a signature

The signature of an integer symmetric form is a **real** invariant: it only sees the form after
`ℤ → ℝ`, so it cannot distinguish a lattice from a finite-index sublattice. In-tree this was only
available at `IntCongr` strength (`LatticeSignatureCongr.latticeSig_congr`, `P ∈ GL(ℤ)`), which is a
strictly stronger hypothesis than the proof actually uses: the proof casts `P` to ℝ and only needs
`det P` to be a unit **there**. This module removes that gap.

    latticeSig_congr_of_det_ne_zero :  P.det ≠ 0  →  latticeSig (Pᵀ * M * P) = latticeSig M

Consequence — the route this module exists to open. To compute `σ` of an unknown lattice `L` one does
**not** need a basis of `L`. It is enough to exhibit `rank L`-many vectors of `L` whose own Gram `G`
is **nondegenerate** (`det G ≠ 0`); they then automatically span a finite-index sublattice and
`σ(L) = σ(G)`. For the welded Kummer `K3` this is decisive: the 16 exceptional `(−2)`-classes and the
6 descended `T⁴` classes span only a **proper** index-`2⁸` sublattice
(`SETTLED_FORKS: kummer-16-plus-6-geometric-block-is-not-a-basis`), so they are useless for the *Gram
congruence* — but they are exactly enough for the *signature*, because `det (⟨−2⟩¹⁶ ⊕ 3H) = ±2¹⁶ ≠ 0`.
No Kummer half-sums, no basis of `H₂(K3;ℤ)`, and — the point — **no signature-additivity-under-gluing
(Novikov) infrastructure**, which does not exist in Mathlib or in this tree.

## Contents

* `radical_eq_bot_of_det_ne_zero` — the nondegeneracy bridge at `det ≠ 0` strength (generalises
  `IsEvenUnimodular.radical_eq_bot`, which needs `det = ±1`);
* `latticeSig_congr_of_det_ne_zero` — **the keystone**;
* `latticeSig_blockDiag_of_det_ne_zero` — block additivity of `σ` for merely nondegenerate blocks
  (generalises `SpinSigmaRoute.latticeSig_blockDiag`, which needs both blocks even unimodular — and
  `⟨−2⟩¹⁶` is *not* unimodular, so the existing lemma cannot see the Kummer sublattice at all);
* `negTwoDiag` — the `⟨−2⟩ⁿ` root-lattice block: `det = (−2)ⁿ`, `σ = −n`;
* `kummerSubForm = ⟨−2⟩¹⁶ ⊕ 3H` — `det = ±2¹⁶ ≠ 0` and `latticeSig = −16`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.LatticeSignatureCongr
import SKEFTHawking.HyperbolicNormalForm
import SKEFTHawking.KummerInvolution

namespace SKEFTHawking.LatticeSigFullRank

open Matrix QuadraticMap QuadraticForm
open SKEFTHawking
open SKEFTHawking.SpinSigmaRoute (blockDiag blockDiag_def)
open SKEFTHawking.KummerInvolution (torusFourForm torusFourForm_isEvenUnimodular
  torusFourForm_latticeSig)

/-! ## §1. Nondegeneracy at `det ≠ 0` strength -/

/-- **A symmetric integer matrix with nonzero determinant has vanishing real radical.**

Exactly `IsEvenUnimodular.radical_eq_bot` with its `det = ±1` hypothesis relaxed to `det ≠ 0` — which
is all its proof ever used (`cast_nondegenerate` needs only `det ≠ 0`). This is what lets the
block-additivity theorems be applied to non-unimodular blocks such as `⟨−2⟩ⁿ`. -/
theorem radical_eq_bot_of_det_ne_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (hsym : Mᵀ = M) (hdet : M.det ≠ 0) :
    (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥ := by
  have hsymR : (M.map (Int.cast : ℤ → ℝ))ᵀ = M.map (Int.cast : ℤ → ℝ) := by
    rw [← Matrix.transpose_map, hsym]
  exact nondeg_radical_eq_bot _ hsymR (cast_nondegenerate M hdet)

/-! ## §2. THE KEYSTONE — signature invariance under a merely `ℝ`-invertible congruence -/

/-- **`latticeSig (Pᵀ M P) = latticeSig M` for ANY integer `P` with `det P ≠ 0`.**

Sylvester's law of inertia is a statement over `ℝ`, so the change of coordinates only has to be
invertible over `ℝ` — `det P ≠ 0` in `ℤ` casts to `det (P : Matrix _ _ ℝ) ≠ 0`, hence a unit in the
field `ℝ`, which is the only thing `LatticeSignatureCongr.latticeSig_congr`'s proof consumes.

**Why the weakening matters.** `IntCongr` (`det P = ±1`) says `M` and `Pᵀ M P` present the *same*
lattice; `det P ≠ 0` says only that `Pᵀ M P` is the restriction of `M` to a **finite-index
sublattice** (index `|det P|`). Signatures cannot tell those apart, and that is the whole content of
the sublattice route: a family of `n` classes with nondegenerate Gram computes `σ` of the ambient
rank-`n` lattice **without being a basis of it**. -/
theorem latticeSig_congr_of_det_ne_zero {n : ℕ} (M P : Matrix (Fin n) (Fin n) ℤ)
    (hP : P.det ≠ 0) :
    latticeSig (Pᵀ * M * P) = latticeSig M := by
  set Mr := M.map (Int.cast : ℤ → ℝ) with hMr
  set Pr := P.map (Int.cast : ℤ → ℝ) with hPr
  have hmap : ((Pᵀ * M * P).map (Int.cast : ℤ → ℝ)) = Prᵀ * Mr * Pr := by
    rw [hMr, hPr, show (Int.cast : ℤ → ℝ) = ⇑(Int.castRingHom ℝ) from rfl,
      Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have hPrdet : IsUnit Pr.det := by
    rw [hPr, ← Int.cast_det]
    refine isUnit_iff_ne_zero.mpr ?_
    exact_mod_cast hP
  letI : Invertible Pr := Matrix.invertibleOfIsUnitDet Pr hPrdet
  have hcoe : (↑(Pr.toLinearEquiv' inferInstance) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
      = Matrix.mulVecLin Pr := by rw [Matrix.toLinearEquiv'_apply]; rfl
  have hequiv : QuadraticMap.Equivalent Mr.toQuadraticMap' (Prᵀ * Mr * Pr).toQuadraticMap' := by
    refine ⟨?_⟩
    have h := QuadraticMap.isometryEquivOfCompLinearEquiv Mr.toQuadraticMap'
      (Pr.toLinearEquiv' inferInstance)
    rwa [hcoe, ← toQuadraticMap'_congr] at h
  unfold latticeSig
  -- v4.32: `latticeSig` unfolds to `toQuadraticForm'` while `hmap`/`hequiv` are stated at the
  -- deprecated alias `toQuadraticMap'`. They are defeq but not syntactically equal, so `rw`
  -- cannot match at reducible transparency; `erw` can. (Renaming the statements is a separate
  -- whole-component pass — a partial rename breaks the BlockSignature interface.)
  erw [hmap, ← hequiv.sigPos_eq, ← hequiv.sigNeg_eq]
  rfl

/-! ## §3. Block additivity for merely nondegenerate blocks -/

/-- **`σ(A ⊕ B) = σ(A) + σ(B)` for symmetric blocks with nonzero determinant.**

`SpinSigmaRoute.latticeSig_blockDiag` requires both blocks to be *even unimodular*. The Kummer
sublattice's first block is `⟨−2⟩¹⁶`, which is even but has `det = 2¹⁶`, so that lemma does not
apply; `latticeSigOf_fromBlocks` only ever wanted nondegeneracy, which §1 now supplies. -/
theorem latticeSig_blockDiag_of_det_ne_zero {na nb : ℕ} (A : Matrix (Fin na) (Fin na) ℤ)
    (B : Matrix (Fin nb) (Fin nb) ℤ) (hAsym : Aᵀ = A) (hAdet : A.det ≠ 0)
    (hBsym : Bᵀ = B) (hBdet : B.det ≠ 0) :
    latticeSig (blockDiag A B) = latticeSig A + latticeSig B := by
  rw [← latticeSigOf_fin, blockDiag_def, latticeSigOf_reindex,
    latticeSigOf_fromBlocks _ _ (radical_eq_bot_of_det_ne_zero A hAsym hAdet)
      (radical_eq_bot_of_det_ne_zero B hBsym hBdet),
    latticeSigOf_fin, latticeSigOf_fin]

/-- **`latticeSig` is invariant under a reindexing of the index type** — the `Fin m ≃ Fin n` form
that `Matrix.reindex (finCongr h)` produces at the `hk3` spelling. -/
theorem latticeSig_reindex {m n : ℕ} (e : Fin m ≃ Fin n) (M : Matrix (Fin m) (Fin m) ℤ) :
    latticeSig (Matrix.reindex e e M) = latticeSig M := by
  rw [← latticeSigOf_fin, latticeSigOf_reindex, latticeSigOf_fin]

/-- **Even-unimodularity is invariant under a reindexing of the index type.** Determinant by
`Matrix.det_reindex_self`, symmetry and evenness entrywise. Needed because
`UnitBlockCancellation.hk3_of_stable16_two` consumes `IsEvenUnimodular` of the *reindexed*
intersection matrix while the geometric arguments produce it on the un-reindexed one. -/
theorem isEvenUnimodular_reindex {m n : ℕ} (e : Fin m ≃ Fin n) (M : Matrix (Fin m) (Fin m) ℤ)
    (heu : IsEvenUnimodular M) : IsEvenUnimodular (Matrix.reindex e e M) := by
  refine ⟨?_, ?_, ?_⟩
  · show (Matrix.reindex e e M)ᵀ = _
    rw [Matrix.reindex_apply, Matrix.transpose_submatrix, heu.1]
  · show (Matrix.reindex e e M).det = 1 ∨ (Matrix.reindex e e M).det = -1
    rw [Matrix.det_reindex_self]
    exact heu.2.1
  · intro i
    rw [Matrix.reindex_apply, Matrix.submatrix_apply]
    exact heu.2.2 _

/-- **The determinant of a block-diagonal sum** — `det (A ⊕ B) = det A * det B`. -/
theorem det_blockDiag {na nb : ℕ} (A : Matrix (Fin na) (Fin na) ℤ)
    (B : Matrix (Fin nb) (Fin nb) ℤ) :
    (blockDiag A B).det = A.det * B.det := by
  rw [blockDiag_def, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

/-- **A block-diagonal sum of symmetric blocks is symmetric.** -/
theorem transpose_blockDiag {na nb : ℕ} (A : Matrix (Fin na) (Fin na) ℤ)
    (B : Matrix (Fin nb) (Fin nb) ℤ) (hAsym : Aᵀ = A) (hBsym : Bᵀ = B) :
    (blockDiag A B)ᵀ = blockDiag A B := by
  rw [blockDiag_def, Matrix.reindex_apply, Matrix.transpose_submatrix,
    Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_zero, hAsym, hBsym]

/-! ## §4. The `⟨−2⟩ⁿ` root block -/

/-- **The negative-definite diagonal form `⟨−2⟩ⁿ`** — the Gram matrix of `n` pairwise-disjoint
`(−2)`-spheres. For the Kummer construction `n = 16`: the exceptional curves of the resolution
`T⁴/±1 → K3`, each an embedded `S²` with self-intersection `−2`, pairwise disjoint. -/
def negTwoDiag (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := Matrix.diagonal fun _ => -2

@[simp] theorem negTwoDiag_apply {n : ℕ} (i j : Fin n) :
    negTwoDiag n i j = if i = j then -2 else 0 := by
  simp [negTwoDiag, Matrix.diagonal]

/-- `⟨−2⟩ⁿ` is symmetric. -/
theorem negTwoDiag_transpose (n : ℕ) : (negTwoDiag n)ᵀ = negTwoDiag n :=
  Matrix.diagonal_transpose _

/-- `det ⟨−2⟩ⁿ = (−2)ⁿ` — in particular nonzero, so the block is nondegenerate even though (for
`n > 0`) it is very far from unimodular. -/
theorem negTwoDiag_det (n : ℕ) : (negTwoDiag n).det = (-2) ^ n := by
  rw [negTwoDiag, Matrix.det_diagonal]
  simp

theorem negTwoDiag_det_ne_zero (n : ℕ) : (negTwoDiag n).det ≠ 0 := by
  rw [negTwoDiag_det]
  exact pow_ne_zero _ (by norm_num)

/-- `⟨−2⟩ⁿ` is an **even** form (every diagonal entry is `−2`). -/
theorem negTwoDiag_even (n : ℕ) : ∀ i : Fin n, (2 : ℤ) ∣ negTwoDiag n i i := by
  intro i; simp

/-- **`σ(⟨−2⟩ⁿ) = −n`** — the form is negative definite, so its whole inertia is negative. -/
theorem negTwoDiag_latticeSig (n : ℕ) : latticeSig (negTwoDiag n) = -(n : ℤ) := by
  refine latticeSig_of_negDef _ ?_
  have hEq : ((-negTwoDiag n).map (Int.cast : ℤ → ℝ))
      = Matrix.diagonal (fun _ : Fin n => (2 : ℝ)) := by
    ext i j
    by_cases h : i = j <;> simp [negTwoDiag, Matrix.diagonal, h]
  rw [hEq]
  exact Matrix.PosDef.diagonal (fun _ => by norm_num)

/-! ## §5. The Kummer sublattice `⟨−2⟩¹⁶ ⊕ 3H` -/

/-- **The Kummer geometric sublattice form** `⟨−2⟩¹⁶ ⊕ 3H` (rank `16 + 6 = 22`): the Gram matrix of
the 16 exceptional `(−2)`-classes together with the 6 descended `T⁴` classes on the welded Kummer
`K3`. It is *not* the K3 lattice — `det = ±2¹⁶`, so it is the restriction of `II(K3)` to a proper
index-`2⁸` sublattice — but §2 makes that irrelevant to the signature. -/
noncomputable def kummerSubForm : Matrix (Fin 22) (Fin 22) ℤ :=
  blockDiag (negTwoDiag 16) torusFourForm

/-- `kummerSubForm` is symmetric. -/
theorem kummerSubForm_transpose : kummerSubFormᵀ = kummerSubForm :=
  transpose_blockDiag _ _ (negTwoDiag_transpose 16) torusFourForm_isEvenUnimodular.1

/-- **`det kummerSubForm = ±2¹⁶ ≠ 0`.** The `3H` block is unimodular and the `⟨−2⟩¹⁶` block has
determinant `2¹⁶`; this nonvanishing is the *only* property of the sublattice the signature route
needs, and it is what makes the (proper!) sublattice full-rank. -/
theorem kummerSubForm_det_ne_zero : kummerSubForm.det ≠ 0 := by
  rw [kummerSubForm, det_blockDiag]
  refine mul_ne_zero (negTwoDiag_det_ne_zero 16) ?_
  rcases torusFourForm_isEvenUnimodular.2.1 with h | h <;> rw [h] <;> norm_num

/-- **`latticeSig kummerSubForm = −16`** — `σ(⟨−2⟩¹⁶) = −16` (negative definite) plus `σ(3H) = 0`
(`KummerInvolution.torusFourForm_latticeSig`), through the nondegenerate block additivity of §3.

This is the arithmetic half of the welded `K3`'s `σ = −16`: the geometric half is the statement that
22 classes with *this* Gram exist in `H²(K3;ℤ)`. Note the numeric pin is falsifiable — it is exactly
`SpinSigmaRoute.k3Form_latticeSig`'s value, computed here from a completely different decomposition
(`⟨−2⟩¹⁶ ⊕ 3H` versus `2(−E₈) ⊕ 3H`), so agreement is a genuine consistency check rather than a
restatement. -/
theorem kummerSubForm_latticeSig : latticeSig kummerSubForm = -16 := by
  rw [kummerSubForm, latticeSig_blockDiag_of_det_ne_zero _ _ (negTwoDiag_transpose 16)
      (negTwoDiag_det_ne_zero 16) torusFourForm_isEvenUnimodular.1
      (by rcases torusFourForm_isEvenUnimodular.2.1 with h | h <;> rw [h] <;> norm_num),
    negTwoDiag_latticeSig, torusFourForm_latticeSig]
  norm_num

/-- **The consistency pin: `kummerSubForm` and `k3Form` have the same signature.**

`⟨−2⟩¹⁶ ⊕ 3H` (the Kummer geometric sublattice) and `2(−E₈) ⊕ 3H` (the K3 lattice) are *not*
congruent — the first has determinant `±2¹⁶`, the second `±1` — yet they share `σ = −16`, which is
precisely the assertion that the sublattice is full-rank. Stated because the whole route rests on it:
if these two numbers disagreed, the geometric family would be the wrong one. -/
theorem kummerSubForm_latticeSig_eq_k3Form_latticeSig :
    latticeSig kummerSubForm = latticeSig SKEFTHawking.SpinSigmaRoute.k3Form := by
  rw [kummerSubForm_latticeSig, SKEFTHawking.SpinSigmaRoute.k3Form_latticeSig]

end SKEFTHawking.LatticeSigFullRank
