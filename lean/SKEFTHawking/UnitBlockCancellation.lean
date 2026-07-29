/-
# `⟨1⟩`-cancellation and the `StableNegRank16` assembly

The `StableNegRank16` route (Milnor–Husemoller II.4.3, now unconditional via
`odd_indefinite_intCongr_unconditional`) reduces the K8b interior brick to ONE elementary statement:

> **`UnitCancellation`** — if `A`, `B` are even unimodular and `A` is indefinite, then
> `⟨1⟩ ⊕ A ≅ ⟨1⟩ ⊕ B` implies `A ≅ B`.

This is exactly Wall's characteristic-vector transitivity in the form the assembly consumes: a
norm-`1` vector `w` of a unimodular lattice `L` splits `L = ⟨w⟩ ⊕ w^⊥`, and `w^⊥` is EVEN precisely
when `w` is characteristic — so "`w^⊥ ≅ w'^⊥` for characteristic `w, w'` of self-product `1`" and
"`⟨1⟩` cancels against even unimodular summands" are the same statement. The cancellation form is the
one stated here because it is directly consumable and manifestly non-vacuous (see below); the
`w^⊥`-form additionally requires the `unitPerp` machinery to even phrase.

**ROUTE CORRECTION — the interior brick had to move from rank 18 to rank 20 (do not revert).** The
elementary proof of `UnitCancellation` is Eichler's criterion applied to `2w` inside the EVEN sublattice
`L_even ≅ A ⊕ ⟨4⟩`, and Eichler's criterion consumes `M = U ⊕ U₁ ⊕ M₀`, i.e. `min(sigPos A, sigNeg A) ≥ 2`.
The ORIGINAL `StableNegRank16` is at rank 18 with `σ = −16`, i.e. inertia `(1, 17)`
(`inertia_of_rank18_sig_neg16`) — the LORENTZIAN lattice `II_{1,17} ≅ U ⊕ E₈(−1)²`, where `2U` cannot
split for numerical reasons and every published proof runs through Eichler's SPINOR GENUS / strong
approximation (Borcherds, *The Leech lattice and other lattices*, Thm 3.9.1), of which Mathlib has
nothing. So the rank-18 phrasing is NOT "elementary, reflections only".
`StableNegRank16Two` (this file) restates the brick at rank 20 — inertia `(2, 18)`
(`inertia_of_rank20_sig_neg16`), `min = 2`, inside Eichler's elementary regime — and
`hk3_of_stable16_two` shows the restatement costs nothing downstream (one `IntCongr.hyp_block` lift
instead of two).

**Non-vacuity.** The hypothesis is realized exactly where the assembly uses it: `A = H ⊕ H ⊕ D` and
`B = H ⊕ H ⊕ 2(−E₈)` are even unimodular of rank 20 and signature `−16`, hence of inertia `(2, 18)`,
and `⟨1⟩ ⊕ A`, `⟨1⟩ ⊕ B` are odd indefinite unimodular of rank 21 and signature `−15`, so
`odd_indefinite_intCongr_unconditional` really does supply the congruence
(`unitExtend_intCongr_of_evenUnimodular` below builds it). Note the *characteristic-vector* phrasing
carries an implicit constraint that the cancellation phrasing makes vacuous-free: in `⟨1⟩^p ⊕ ⟨−1⟩^q`
a characteristic vector has all coordinates odd, so its self-product is `≡ p − q (mod 8)`, and a
characteristic vector of self-product `1` exists only when `p − q ≡ 1 (mod 8)`. Here `⟨1⟩ ⊕ A` has rank
21 and `σ = 1 + (−16) = −15`, so `(p, q) = (3, 18)` and `p − q = −15 ≡ 1 (mod 8)` ✓, with explicit
witness `w = 3e₁ + 3e₂ + e₃ + f₁ + ⋯ + f₁₈` (`9 + 9 + 1 − 18 = 1`, all coordinates odd). The
cancellation form has no such side condition — the congruence hypothesis supplies the vector.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.EvenUnimodularIndefiniteSplit
import SKEFTHawking.UnitVectorSplit
import SKEFTHawking.OddSmallRankHM
import SKEFTHawking.EichlerTransvection

namespace SKEFTHawking

open Matrix Module QuadraticForm
open SKEFTHawking.SpinSigmaRoute

/-! ### Reindexed block sums: even-unimodularity, inertia, signature -/

/-- Casting a reindexed matrix commutes with reindexing. -/
theorem map_reindex_cast {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (e : ι ≃ ι') (M : Matrix ι ι ℤ) :
    (Matrix.reindex e e M).map (Int.cast : ℤ → ℝ)
      = Matrix.reindex e e (M.map (Int.cast : ℤ → ℝ)) := by
  ext i j; simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]

/-- Positive inertia is reindex-invariant. -/
theorem sigPos_reindex {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (e : ι ≃ ι') (M : Matrix ι ι ℤ) :
    sigPos ((Matrix.reindex e e M).map (Int.cast : ℤ → ℝ)).toQuadraticMap'
      = sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' := by
  rw [map_reindex_cast]
  exact QuadraticMap.Equivalent.sigPos_eq ⟨reindexFormEquiv e _⟩

/-- Negative inertia is reindex-invariant. -/
theorem sigNeg_reindex {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (e : ι ≃ ι') (M : Matrix ι ι ℤ) :
    sigNeg ((Matrix.reindex e e M).map (Int.cast : ℤ → ℝ)).toQuadraticMap'
      = sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' := by
  rw [map_reindex_cast]
  exact QuadraticMap.Equivalent.sigNeg_eq ⟨reindexFormEquiv e _⟩

/-- The radical of a reindexed form vanishes iff the original's does. -/
theorem radical_reindex_eq_bot {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] (e : ι ≃ ι') (M : Matrix ι ι ℤ)
    (h : (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥) :
    ((Matrix.reindex e e M).map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥ := by
  have hsum := QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := ((Matrix.reindex e e M).map (Int.cast : ℤ → ℝ)).toQuadraticMap')
  have hsum0 := QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
  rw [h] at hsum0
  simp only [finrank_bot, add_zero, Module.finrank_fintype_fun_eq_card] at hsum hsum0
  rw [sigPos_reindex, sigNeg_reindex] at hsum
  have hcard : Fintype.card ι' = Fintype.card ι := (Fintype.card_congr e).symm
  have hfr : finrank ℝ ((Matrix.reindex e e M).map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = 0 :=
    by omega
  exact Submodule.finrank_eq_zero.mp hfr

/-- **Positive inertia of a reindexed block sum.** -/
theorem sigPos_reindexBlocks {na nb m : ℕ} (e : Fin na ⊕ Fin nb ≃ Fin m)
    (A : Matrix (Fin na) (Fin na) ℤ) (B : Matrix (Fin nb) (Fin nb) ℤ)
    (hA : (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥)
    (hB : (B.map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥) :
    sigPos (((Matrix.reindex e e (Matrix.fromBlocks A 0 0 B))).map
        (Int.cast : ℤ → ℝ)).toQuadraticMap'
      = sigPos (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap'
        + sigPos (B.map (Int.cast : ℤ → ℝ)).toQuadraticMap' := by
  have hmap : (Matrix.fromBlocks A 0 0 B).map (Int.cast : ℤ → ℝ)
      = Matrix.fromBlocks (A.map Int.cast) 0 0 (B.map Int.cast) := by
    rw [Matrix.fromBlocks_map]; simp
  rw [sigPos_reindex, hmap, sigPos_fromBlocks _ _ hA hB]

/-- **Negative inertia of a reindexed block sum.** -/
theorem sigNeg_reindexBlocks {na nb m : ℕ} (e : Fin na ⊕ Fin nb ≃ Fin m)
    (A : Matrix (Fin na) (Fin na) ℤ) (B : Matrix (Fin nb) (Fin nb) ℤ)
    (hA : (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥)
    (hB : (B.map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥) :
    sigNeg (((Matrix.reindex e e (Matrix.fromBlocks A 0 0 B))).map
        (Int.cast : ℤ → ℝ)).toQuadraticMap'
      = sigNeg (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap'
        + sigNeg (B.map (Int.cast : ℤ → ℝ)).toQuadraticMap' := by
  have hmap : (Matrix.fromBlocks A 0 0 B).map (Int.cast : ℤ → ℝ)
      = Matrix.fromBlocks (A.map Int.cast) 0 0 (B.map Int.cast) := by
    rw [Matrix.fromBlocks_map]; simp
  rw [sigNeg_reindex, hmap, sigNeg_fromBlocks _ _ hA hB]

/-- **Even-unimodularity of a reindexed block sum** (the `blockDiag` statement at an arbitrary
reindexing). -/
theorem isEvenUnimodular_reindexBlocks {na nb m : ℕ} (e : Fin na ⊕ Fin nb ≃ Fin m)
    (A : Matrix (Fin na) (Fin na) ℤ) (B : Matrix (Fin nb) (Fin nb) ℤ)
    (hA : IsEvenUnimodular A) (hB : IsEvenUnimodular B) :
    IsEvenUnimodular (Matrix.reindex e e (Matrix.fromBlocks A 0 0 B)) := by
  obtain ⟨hsymA, hdetA, hevenA⟩ := hA
  obtain ⟨hsymB, hdetB, hevenB⟩ := hB
  refine ⟨?_, ?_, ?_⟩
  · show (Matrix.reindex e e (Matrix.fromBlocks A 0 0 B))ᵀ
      = Matrix.reindex e e (Matrix.fromBlocks A 0 0 B)
    rw [Matrix.reindex_apply, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose,
      Matrix.transpose_zero, Matrix.transpose_zero, hsymA, hsymB]
  · have hdet : (Matrix.reindex e e (Matrix.fromBlocks A 0 0 B)).det = A.det * B.det := by
      rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
    show (Matrix.reindex e e (Matrix.fromBlocks A 0 0 B)).det = 1 ∨ _ = -1
    rw [hdet]
    rcases hdetA with h1 | h1 <;> rcases hdetB with h2 | h2 <;> rw [h1, h2] <;> norm_num
  · intro i
    rw [Matrix.reindex_apply, Matrix.submatrix_apply]
    rcases e.symm i with j | j
    · exact hevenA j
    · exact hevenB j

/-- **Signature of a reindexed block sum.** -/
theorem latticeSig_reindexBlocks {na nb m : ℕ} (e : Fin na ⊕ Fin nb ≃ Fin m)
    (A : Matrix (Fin na) (Fin na) ℤ) (B : Matrix (Fin nb) (Fin nb) ℤ)
    (hA : (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥)
    (hB : (B.map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥) :
    latticeSig (Matrix.reindex e e (Matrix.fromBlocks A 0 0 B))
      = latticeSig A + latticeSig B := by
  rw [← latticeSigOf_fin, latticeSigOf_reindex,
    latticeSigOf_fromBlocks _ _ hA hB, latticeSigOf_fin, latticeSigOf_fin]

/-! ### The `⟨1⟩`-extension -/

/-- Symmetry of `⟨1⟩ ⊕ A`. -/
theorem unitExtend_symm {n m : ℕ} (e : Fin 1 ⊕ Fin n ≃ Fin m) (A : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : Aᵀ = A) :
    (Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 A))ᵀ
      = Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 A) := by
  have h1 : (!![(1 : ℤ)])ᵀ = !![1] := by ext i j; fin_cases i; fin_cases j; rfl
  rw [Matrix.reindex_apply, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose,
    Matrix.transpose_zero, Matrix.transpose_zero, hsymm, h1]

/-- Unimodularity of `⟨1⟩ ⊕ A`. -/
theorem unitExtend_unimodular {n m : ℕ} (e : Fin 1 ⊕ Fin n ≃ Fin m)
    (A : Matrix (Fin n) (Fin n) ℤ) (hunim : IsUnimodular A) :
    IsUnimodular (Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 A)) := by
  have hdet : (Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 A)).det
      = (!![(1 : ℤ)]).det * A.det := by
    rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  have h1 : (!![(1 : ℤ)]).det = 1 := by simp
  show _ = 1 ∨ _ = -1
  rw [hdet, h1, one_mul]
  exact hunim

/-- `⟨1⟩ ⊕ A` is ODD: the adjoined generator has self-product `1`. -/
theorem unitExtend_odd {n m : ℕ} (e : Fin 1 ⊕ Fin n ≃ Fin m) (A : Matrix (Fin n) (Fin n) ℤ) :
    ∃ i, ¬ (2 ∣ (Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 A)) i i) := by
  refine ⟨e (Sum.inl 0), ?_⟩
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  simp

/-- The one-by-one unit block is nondegenerate. -/
theorem unitBlock_one_radical :
    ((!![(1 : ℤ)]).map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥ :=
  unitBlock_radical (ε := 1) (by norm_num)

/-- Signature of `⟨1⟩ ⊕ A`. -/
theorem unitExtend_latticeSig {n m : ℕ} (e : Fin 1 ⊕ Fin n ≃ Fin m)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥) :
    latticeSig (Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 A)) = 1 + latticeSig A := by
  rw [latticeSig_reindexBlocks e _ _ unitBlock_one_radical hA, latticeSig_unitBlock_one]

/-- Positive inertia of `⟨1⟩ ⊕ A` dominates that of `A` — so `A` indefinite forces `⟨1⟩ ⊕ A`
indefinite. -/
theorem unitExtend_sigPos_pos {n m : ℕ} (e : Fin 1 ⊕ Fin n ≃ Fin m)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥)
    (hsp : 0 < sigPos (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap') :
    0 < sigPos (((Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 A))).map
      (Int.cast : ℤ → ℝ)).toQuadraticMap' := by
  rw [sigPos_reindexBlocks e _ _ unitBlock_one_radical hA]
  omega

/-- Negative inertia of `⟨1⟩ ⊕ A` dominates that of `A`. -/
theorem unitExtend_sigNeg_pos {n m : ℕ} (e : Fin 1 ⊕ Fin n ≃ Fin m)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥)
    (hsn : 0 < sigNeg (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap') :
    0 < sigNeg (((Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 A))).map
      (Int.cast : ℤ → ℝ)).toQuadraticMap' := by
  rw [sigNeg_reindexBlocks e _ _ unitBlock_one_radical hA]
  omega

/-- **`⟨1⟩ ⊕ A ≅ ⟨1⟩ ⊕ B` is FREE for indefinite even unimodular `A, B` of equal signature.** Both
sides are ODD (the adjoined generator), unimodular, of the same rank, indefinite (positive and
negative inertia dominate `A`'s, resp. `B`'s), and of the same signature `1 + σ` — so the now
unconditional Milnor–Husemoller II.4.3 classification
(`odd_indefinite_intCongr_unconditional`) supplies the congruence. This is exactly why the whole of
`StableNegRank16` reduces to CANCELLING the `⟨1⟩`: the extended forms are congruent for free, and no
information beyond rank and signature survives the extension. -/
theorem unitExtend_intCongr_of_evenUnimodular {n m : ℕ} (e : Fin 1 ⊕ Fin n ≃ Fin m)
    (A B : Matrix (Fin n) (Fin n) ℤ) (hA : IsEvenUnimodular A) (hB : IsEvenUnimodular B)
    (hspA : 0 < sigPos (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsnA : 0 < sigNeg (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hspB : 0 < sigPos (B.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsnB : 0 < sigNeg (B.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsig : latticeSig A = latticeSig B) :
    IntCongr (Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 A))
      (Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 B)) :=
  odd_indefinite_intCongr_unconditional _ _
    (unitExtend_symm e A hA.1) (unitExtend_unimodular e A hA.2.1) (unitExtend_odd e A)
    (unitExtend_sigPos_pos e A hA.radical_eq_bot hspA)
    (unitExtend_sigNeg_pos e A hA.radical_eq_bot hsnA)
    (unitExtend_symm e B hB.1) (unitExtend_unimodular e B hB.2.1) (unitExtend_odd e B)
    (unitExtend_sigPos_pos e B hB.radical_eq_bot hspB)
    (unitExtend_sigNeg_pos e B hB.radical_eq_bot hsnB)
    (by rw [unitExtend_latticeSig e A hA.radical_eq_bot,
      unitExtend_latticeSig e B hB.radical_eq_bot, hsig])

/-! ### The cancellation interface (Wall) -/

/-- **`⟨1⟩`-CANCELLATION for even unimodular forms** — Wall's characteristic-vector transitivity in
the form the `StableNegRank16` assembly consumes. If `A` and `B` are even unimodular of the same rank,
`A` indefinite, and `⟨1⟩ ⊕ A ≅ ⟨1⟩ ⊕ B`, then `A ≅ B`.

Equivalent to: *in a unimodular lattice `L` the orthogonal group acts transitively on characteristic
vectors of self-product `1`*. Indeed a norm-`1` vector `w` splits `L = ⟨w⟩ ⊕ w^⊥` (`unit_split_congr`)
with `w^⊥` even exactly when `w` is characteristic, so the two statements are the same content; the
cancellation phrasing is the one stated because it needs no `unitPerp` machinery and has no
`σ ≡ 1 (mod 8)` side condition to check for non-vacuity.

**THE `2 ≤ sigPos`, `2 ≤ sigNeg` HYPOTHESIS IS NOT COSMETIC — it is the elementary/non-elementary
dividing line, and it is why the interior brick had to be restated at rank 20** (see
`StableNegRank16Two`). The elementary proof of `UnitCancellation` runs in the EVEN sublattice
`M := L_even = A ⊕ ℤ(2w) ≅ A ⊕ ⟨4⟩`: there `2w` and `2w'` are primitive of self-product `4` with
`div_M = 4` and equal image in `D(M) ≅ ℤ/4` (up to replacing `w'` by `−w'`), so **Eichler's criterion**
— three explicit Eichler transvections, `eichler` above — carries `2w` to `2w'` and hence
`B = (2w)^⊥ ≅ (2w')^⊥ = A`. Eichler's criterion consumes `M = U ⊕ U₁ ⊕ M₀` (TWO orthogonal hyperbolic
planes), which for `A` even unimodular means `min(sigPos A, sigNeg A) ≥ 2`. When
`min(sigPos, sigNeg) = 1` the lattice is `A ≅ U ⊕ E₈(±1)^k` — the LORENTZIAN case `II_{8k+1,1}` — where
`2U` cannot split for numerical reasons and every published proof (e.g. Borcherds, *The Leech lattice
and other lattices*, Thm 3.9.1) goes through Eichler's **spinor genus** / strong approximation. Mathlib
has none of that.

That is exactly the case the ORIGINAL rank-18 `StableNegRank16` sits in: `H ⊕ D` has rank 18 and
`σ = −16`, i.e. inertia `(1, 17)` — `min = 1`, Lorentzian, NOT elementary. The rank-20 restatement
`StableNegRank16Two` has inertia `(2, 18)` — `min = 2` — and is elementary, while being exactly as
useful downstream (`hk3_of_stable16_two` below consumes it with one `hyp_block` lift instead of two).

Stated as a `Prop` so `stableNegRank16Two_of_unitCancellation` can consume it: with this ONE elementary
input, the whole K8b interior brick closes. -/
def UnitCancellation : Prop :=
  ∀ (n m : ℕ) (A B : Matrix (Fin n) (Fin n) ℤ) (e : Fin 1 ⊕ Fin n ≃ Fin m),
    IsEvenUnimodular A → IsEvenUnimodular B →
    2 ≤ sigPos (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' →
    2 ≤ sigNeg (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' →
    IntCongr (Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 A))
      (Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 B)) →
    IntCongr A B

/-- Inertia of an even unimodular form is pinned by rank and signature: `sigPos + sigNeg = n` (from
nondegeneracy) and `sigPos − sigNeg = σ`. -/
theorem sigPos_add_sigNeg_of_evenUnimodular {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : IsEvenUnimodular A) :
    sigPos (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap'
      + sigNeg (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' = n := by
  have hsum := QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
  rw [hA.radical_eq_bot] at hsum
  simp only [finrank_bot, add_zero, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hsum
  omega

/-- Inertia of an even unimodular rank-20 form of signature `−16`: `(sigPos, sigNeg) = (2, 18)`. This
is the numeric fact that puts the TWO-hyperbolic-plane restatement of the interior brick inside
Eichler's elementary regime (`min ≥ 2`), unlike the rank-18 form whose inertia is `(1, 17)`. -/
theorem inertia_of_rank20_sig_neg16 (A : Matrix (Fin 20) (Fin 20) ℤ) (hA : IsEvenUnimodular A)
    (hsig : latticeSig A = -16) :
    sigPos (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' = 2 ∧
    sigNeg (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' = 18 := by
  have hsum := sigPos_add_sigNeg_of_evenUnimodular A hA
  -- v4.32: `latticeSig` unfolds to the NEW `toQuadraticForm'` spelling while this statement uses
  -- the deprecated alias `toQuadraticMap'` — defeq, but distinct ATOMS to `omega`. Restate in the
  -- statement's spelling (typechecks by defeq); the old name stays per the whole-component boundary.
  have hsig' : (sigPos (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' : ℤ)
      - (sigNeg (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' : ℤ) = -16 := hsig
  omega

/-- Inertia of an even unimodular rank-18 form of signature `−16`: `(sigPos, sigNeg) = (1, 17)`. The
`min = 1` here is precisely why the rank-18 interior brick is the LORENTZIAN (`II_{1,17}`) case, outside
Eichler's elementary regime — recorded as a theorem so the route obstruction is machine-checked rather
than prose. -/
theorem inertia_of_rank18_sig_neg16 (A : Matrix (Fin 18) (Fin 18) ℤ) (hA : IsEvenUnimodular A)
    (hsig : latticeSig A = -16) :
    sigPos (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' = 1 ∧
    sigNeg (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' = 17 := by
  have hsum := sigPos_add_sigNeg_of_evenUnimodular A hA
  -- v4.32: `latticeSig` unfolds to the NEW `toQuadraticForm'` spelling while this statement uses
  -- the deprecated alias `toQuadraticMap'` — defeq, but distinct ATOMS to `omega`. Restate in the
  -- statement's spelling (typechecks by defeq); the old name stays per the whole-component boundary.
  have hsig' : (sigPos (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' : ℤ)
      - (sigNeg (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' : ℤ) = -16 := hsig
  omega

/-! ### The TWO-hyperbolic-plane interior brick (the elementary restatement) -/

/-- **The interior brick, restated at rank 20 (TWO hyperbolic planes).** For a negative-definite even
unimodular rank-16 residual `D`, `H ⊕ H ⊕ D ≅ H ⊕ H ⊕ 2(−E₈)` in the reindexings the K3 split
produces.

Why two planes and not one: at rank 20 the form has inertia `(2, 18)`, so `2U` splits off and Eichler's
criterion (elementary, three `eichler` transvections) applies; at rank 18 the inertia is `(1, 17)` — the
Lorentzian `II_{1,17}`, where `2U` cannot split and the classical proofs need spinor genus. The rank-20
statement is exactly as useful: `hk3_of_stable16_two` consumes it with a single `IntCongr.hyp_block`
lift where the rank-18 version needed two. -/
def StableNegRank16Two : Prop :=
  ∀ (D : Matrix (Fin 16) (Fin 16) ℤ) (e₂ : Fin 2 ⊕ Fin 18 ≃ Fin 20) (e₃ : Fin 2 ⊕ Fin 16 ≃ Fin 18),
    IsEvenUnimodular D → latticeSig D = -16 →
    sigPos (D.map (Int.cast : ℤ → ℝ)).toQuadraticMap' = 0 →
    IntCongr
      (Matrix.reindex e₂ e₂ (Matrix.fromBlocks Hyp 0 0
        (Matrix.reindex e₃ e₃ (Matrix.fromBlocks Hyp 0 0 D))))
      (Matrix.reindex e₂ e₂ (Matrix.fromBlocks Hyp 0 0
        (Matrix.reindex e₃ e₃ (Matrix.fromBlocks Hyp 0 0 (blockDiag (-E8lit) (-E8lit))))))

/-- `2(−E₈)` is even unimodular. -/
theorem isEvenUnimodular_two_negE8 : IsEvenUnimodular (blockDiag (-E8lit) (-E8lit)) :=
  isEvenUnimodular_blockDiag _ _ isEvenUnimodular_negE8 isEvenUnimodular_negE8

/-- `σ(2(−E₈)) = −16`. -/
theorem latticeSig_two_negE8 : latticeSig (blockDiag (-E8lit) (-E8lit)) = -16 := by
  rw [latticeSig_blockDiag _ _ isEvenUnimodular_negE8 isEvenUnimodular_negE8, neg_e8lit_latticeSig]
  norm_num

/-- **`StableNegRank16Two` from `⟨1⟩`-cancellation ALONE.** `H ⊕ H ⊕ D` and `H ⊕ H ⊕ 2(−E₈)` are even
unimodular of rank 20 and signature `−16`, hence of inertia `(2, 18)` — inside Eichler's elementary
regime; their `⟨1⟩`-extensions are odd indefinite unimodular of rank 21 and signature `−15`, so
`odd_indefinite_intCongr_unconditional` makes them congruent for free
(`unitExtend_intCongr_of_evenUnimodular`); cancelling the `⟨1⟩` gives the brick.

So the K8b interior brick is now reduced to the SINGLE elementary statement `UnitCancellation` at
`min(sigPos, sigNeg) ≥ 2`, which is Eichler's criterion applied to `2w` inside `L_even ≅ A ⊕ ⟨4⟩`. -/
theorem stableNegRank16Two_of_unitCancellation (hcanc : UnitCancellation) :
    StableNegRank16Two := by
  intro D e₂ e₃ hD hDsig _hDdef
  have hEU18A : IsEvenUnimodular (Matrix.reindex e₃ e₃ (Matrix.fromBlocks Hyp 0 0 D)) :=
    isEvenUnimodular_reindexBlocks e₃ _ _ isEvenUnimodular_hyp hD
  have hEU18B : IsEvenUnimodular
      (Matrix.reindex e₃ e₃ (Matrix.fromBlocks Hyp 0 0 (blockDiag (-E8lit) (-E8lit)))) :=
    isEvenUnimodular_reindexBlocks e₃ _ _ isEvenUnimodular_hyp isEvenUnimodular_two_negE8
  have hsig18A : latticeSig (Matrix.reindex e₃ e₃ (Matrix.fromBlocks Hyp 0 0 D)) = -16 := by
    rw [latticeSig_reindexBlocks e₃ _ _ isEvenUnimodular_hyp.radical_eq_bot hD.radical_eq_bot,
      hyp_latticeSig, hDsig, zero_add]
  have hsig18B : latticeSig (Matrix.reindex e₃ e₃
      (Matrix.fromBlocks Hyp 0 0 (blockDiag (-E8lit) (-E8lit)))) = -16 := by
    rw [latticeSig_reindexBlocks e₃ _ _ isEvenUnimodular_hyp.radical_eq_bot
      isEvenUnimodular_two_negE8.radical_eq_bot, hyp_latticeSig, latticeSig_two_negE8, zero_add]
  have hEUA : IsEvenUnimodular (Matrix.reindex e₂ e₂ (Matrix.fromBlocks Hyp 0 0
      (Matrix.reindex e₃ e₃ (Matrix.fromBlocks Hyp 0 0 D)))) :=
    isEvenUnimodular_reindexBlocks e₂ _ _ isEvenUnimodular_hyp hEU18A
  have hEUB : IsEvenUnimodular (Matrix.reindex e₂ e₂ (Matrix.fromBlocks Hyp 0 0
      (Matrix.reindex e₃ e₃ (Matrix.fromBlocks Hyp 0 0 (blockDiag (-E8lit) (-E8lit)))))) :=
    isEvenUnimodular_reindexBlocks e₂ _ _ isEvenUnimodular_hyp hEU18B
  have hsigA : latticeSig (Matrix.reindex e₂ e₂ (Matrix.fromBlocks Hyp 0 0
      (Matrix.reindex e₃ e₃ (Matrix.fromBlocks Hyp 0 0 D)))) = -16 := by
    rw [latticeSig_reindexBlocks e₂ _ _ isEvenUnimodular_hyp.radical_eq_bot
      hEU18A.radical_eq_bot, hyp_latticeSig, hsig18A, zero_add]
  have hsigB : latticeSig (Matrix.reindex e₂ e₂ (Matrix.fromBlocks Hyp 0 0
      (Matrix.reindex e₃ e₃ (Matrix.fromBlocks Hyp 0 0 (blockDiag (-E8lit) (-E8lit)))))) = -16 := by
    rw [latticeSig_reindexBlocks e₂ _ _ isEvenUnimodular_hyp.radical_eq_bot
      hEU18B.radical_eq_bot, hyp_latticeSig, hsig18B, zero_add]
  obtain ⟨hspA, hsnA⟩ := inertia_of_rank20_sig_neg16 _ hEUA hsigA
  obtain ⟨hspB, hsnB⟩ := inertia_of_rank20_sig_neg16 _ hEUB hsigB
  refine hcanc 20 21 _ _ (finSumFinEquiv.trans (finCongr (by norm_num))) hEUA hEUB
    (by omega) (by omega) ?_
  exact unitExtend_intCongr_of_evenUnimodular _ _ _ hEUA hEUB (by omega) (by omega)
    (by omega) (by omega) (hsigA.trans hsigB.symm)

/-- **The K8b consumer, on the TWO-hyperbolic-plane brick.** `IntCongr M k3Form` for any even
unimodular rank-22 form of signature `−16`, from `StableNegRank16Two` alone. Identical to
`hk3_of_stable16` except that the rank-20 stabilization is lifted through ONE peeled `H` instead of the
rank-18 one through two — so nothing downstream pays for the restatement, and the interior brick moves
out of the Lorentzian case into Eichler's elementary regime. -/
theorem hk3_of_stable16_two (hstable : StableNegRank16Two)
    (M : Matrix (Fin 22) (Fin 22) ℤ) (heu : IsEvenUnimodular M) (hsig : latticeSig M = -16) :
    IntCongr M k3Form := by
  obtain ⟨D, e₁, e₂, e₃, hD, hDsig, hDdef, hcong⟩ := k3_candidate_split M heu hsig
  exact (hcong.trans (IntCongr.hyp_block e₁ (hstable D e₂ e₃ hD hDsig hDdef))).trans
    (reblockToK3 e₁ e₂ e₃)

end SKEFTHawking
