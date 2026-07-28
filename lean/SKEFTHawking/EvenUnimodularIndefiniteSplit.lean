/-
# Phase 5q.H (K8b route-(i) opener) — the indefinite-residual hyperbolic split

`HyperbolicNormalForm.even_unimodular_sig_zero_split_congr` peels one hyperbolic plane `H` off a
**signature-0** even unimodular form. This module GENERALIZES the peel to an **indefinite** residual
signature: for any even unimodular `M` of rank `n ≥ 2` that is indefinite (`0 < sigPos ∧ 0 < sigNeg`),
`M ≅ H ⊕ M'` with `M'` even unimodular of rank `n − 2` and `latticeSig M' = latticeSig M` (the `H` block
contributes `0` to the signature). The σ=0 version derived indefiniteness from the signature; here it is
taken directly (or supplied by `even_unimodular_indefinite_of_abs_sig_lt` from `|σ| < n`).

This is the low-risk prefix of the K8b K3-lattice classification (route (i), adjudicated 2026-07-20,
`docs/dev-loops/Phase5qH/KUMMER_K4K10_DESIGN.md`):
* `even_unimodular_indefinite_split_congr` — the generalized peel (deliverable 1);
* `k3_candidate_split` — iterate it three times from `(rank 22, σ = −16)` down to a negative-definite
  rank-16 residual `D`, indefinite at each step while rank `> 16` (deliverable 2);
* `hk3_of_stable16` — the consumer stub reducing `IntCongr M k3Form` to the (future) interior brick
  `stable_neg_rank16` (the one-hyperbolic stabilization `H ⊕ D ≅ H ⊕ 2(−E₈)`) via `IntCongr.hyp_block`
  reassembly (deliverable 3).

The hard interior brick `stable_neg_rank16` is NOT proved here — it is exposed as a `Prop` interface. Note
rank-16 definite uniqueness is FALSE (E₈² vs D₁₆⁺); only the H-stabilized form is true.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SpinSigmaGenerator

namespace SKEFTHawking

open Matrix Module QuadraticForm
open SKEFTHawking.SpinSigmaRoute (blockDiag k3Form)

/-- **An even unimodular form with `|σ| < rank` is indefinite.** `M` unimodular ⟹ nondegenerate
(`radical = ⊥`), so `sigPos + sigNeg = n`; and `|latticeSig M| = |sigPos − sigNeg| < n = sigPos + sigNeg`
forces both inertia indices positive. Supplies the `[HM]` indefiniteness hypothesis
(`0 < sigPos ∧ 0 < sigNeg`) from the pure signature bound the K8b orchestration checks. -/
theorem even_unimodular_indefinite_of_abs_sig_lt {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (heu : IsEvenUnimodular M) (hlt : (latticeSig M).natAbs < n) :
    0 < sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' ∧
    0 < sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' := by
  have hsum := QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
  rw [heu.radical_eq_bot] at hsum
  simp only [finrank_bot, add_zero, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hsum
  unfold latticeSig at hlt
  omega

/-- **The congruence-strengthened split for an INDEFINITE residual** (deliverable 1). An even unimodular
form of rank `≥ 2` that is indefinite (`0 < sigPos ∧ 0 < sigNeg`) is `IntCongr` to `H ⊕ M'` (reindexed to
`Fin n`), with `M'` even unimodular of rank `n − 2` and `latticeSig M' = latticeSig M` (the hyperbolic
block is signature-neutral). Generalizes `even_unimodular_sig_zero_split_congr` off the `σ = 0` locus: the
indefiniteness is taken directly rather than derived from the signature, and the residual signature is
preserved rather than pinned to `0`. Same construction (`hasIsotropicVector` → `exists_hyperbolic_pair` →
`hypFullBasis` change of basis → `gramB_eq`); `latticeSig_split` gives `σ(M) = σ(M')`. -/
theorem even_unimodular_indefinite_split_congr {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (heu : IsEvenUnimodular M)
    (hsp : 0 < sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsn : 0 < sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap') :
    ∃ (M' : Matrix (Fin (n - 2)) (Fin (n - 2)) ℤ) (e : Fin 2 ⊕ Fin (n - 2) ≃ Fin n),
      IntCongr M (Matrix.reindex e e (Matrix.fromBlocks Hyp 0 0 M'))
        ∧ IsEvenUnimodular M' ∧ latticeSig M' = latticeSig M := by
  have hsum := QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
  rw [heu.radical_eq_bot] at hsum
  simp only [finrank_bot, add_zero, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hsum
  have hn2 : 2 ≤ n := by omega
  obtain ⟨v, hvprim, hviso⟩ := hasIsotropicVector M heu hsp hsn
  obtain ⟨w', hv0, hvw, hw0⟩ := exists_hyperbolic_pair M heu.1 heu.2.2 v hvprim hviso heu.2.1
  have hindep := hyperbolic_linearIndependent M heu.1 v w' hv0 hvw hw0
  have hic := hyperbolic_isCompl M v w' heu.1 hv0 hvw hw0
  have hfr := hypPerp_finrank M v w' hindep hic
  classical
  set B := hypFullBasis M v w' heu.1 hv0 hvw hw0 hfr with hB
  let e : Fin 2 ⊕ Fin (n - 2) ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))
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
  have hgram := gramB_eq M v w' heu.1 hv0 hvw hw0 hfr
  refine ⟨residGram M v w' hfr, e, ⟨P, hPunit, ?_⟩,
    residGram_evenUnimodular hn2 M heu v w' hv0 hvw hw0 hfr, ?_⟩
  · rw [hPMP, hgram]
  · have hsplit := latticeSig_split hn2 M heu.1 heu.2.1 v w' hv0 hvw hw0 hfr
    rw [latticeSigOf_fin] at hsplit
    omega

/-! ### The rank-22 / σ = −16 orchestration (deliverable 2)

Iterate the indefinite split three times from `(rank 22, σ = −16)`. After `k` peels the residual has rank
`22 − 2k` and signature `−16`, so it is indefinite exactly while `22 − 2k > 16` (`sigPos = (rank − 16)/2 >
0`); the iteration therefore runs at ranks `22, 20, 18` and STOPS at rank `16`, where `σ = −16` forces
`sigPos = 0` — the residual `D` is negative-definite (inertia `(0, 16)`). -/

/-- **The K3 candidate split** (deliverable 2). Any even unimodular rank-22 form of signature `−16` is
`IntCongr` to three hyperbolic planes stacked over a **negative-definite** rank-16 even unimodular residual
`D` (`σ(D) = −16`, `sigPos(D) = 0`). Three applications of `even_unimodular_indefinite_split_congr`
(indefinite at ranks `22, 20, 18` via `even_unimodular_indefinite_of_abs_sig_lt`, each preserving `σ =
−16`), reassembled through the hyperbolic blocks by `IntCongr.hyp_block`. This is the geometric-reduction
half of the K8b classification: the K3 lattice `k3Form = 2(−E₈) ⊕ 3H` is reached once the interior brick
`stable_neg_rank16` absorbs `D` (see `hk3_of_stable16`). -/
theorem k3_candidate_split (M : Matrix (Fin 22) (Fin 22) ℤ)
    (heu : IsEvenUnimodular M) (hsig : latticeSig M = -16) :
    ∃ (D : Matrix (Fin 16) (Fin 16) ℤ)
      (e₁ : Fin 2 ⊕ Fin 20 ≃ Fin 22) (e₂ : Fin 2 ⊕ Fin 18 ≃ Fin 20)
      (e₃ : Fin 2 ⊕ Fin 16 ≃ Fin 18),
      IsEvenUnimodular D ∧ latticeSig D = -16 ∧
      sigPos (D.map (Int.cast : ℤ → ℝ)).toQuadraticMap' = 0 ∧
      IntCongr M (Matrix.reindex e₁ e₁ (Matrix.fromBlocks Hyp 0 0
        (Matrix.reindex e₂ e₂ (Matrix.fromBlocks Hyp 0 0
          (Matrix.reindex e₃ e₃ (Matrix.fromBlocks Hyp 0 0 D)))))) := by
  obtain ⟨hsp0, hsn0⟩ := even_unimodular_indefinite_of_abs_sig_lt M heu (by rw [hsig]; omega)
  obtain ⟨M₁, e₁, hcong₁, heu₁, hsigraw₁⟩ := even_unimodular_indefinite_split_congr M heu hsp0 hsn0
  have hsig₁ : latticeSig M₁ = -16 := hsigraw₁.trans hsig
  obtain ⟨hsp1, hsn1⟩ := even_unimodular_indefinite_of_abs_sig_lt M₁ heu₁ (by rw [hsig₁]; omega)
  obtain ⟨M₂, e₂, hcong₂, heu₂, hsigraw₂⟩ := even_unimodular_indefinite_split_congr M₁ heu₁ hsp1 hsn1
  have hsig₂ : latticeSig M₂ = -16 := hsigraw₂.trans hsig₁
  obtain ⟨hsp2, hsn2⟩ := even_unimodular_indefinite_of_abs_sig_lt M₂ heu₂ (by rw [hsig₂]; omega)
  obtain ⟨D, e₃, hcong₃, heuD, hsigrawD⟩ := even_unimodular_indefinite_split_congr M₂ heu₂ hsp2 hsn2
  have hsigD : latticeSig D = -16 := hsigrawD.trans hsig₂
  have hsumD := QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := (D.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
  rw [heuD.radical_eq_bot] at hsumD
  simp only [finrank_bot, add_zero, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hsumD
  have hsigD' := hsigD
  unfold latticeSig at hsigD'
  have hDdef : sigPos (D.map (Int.cast : ℤ → ℝ)).toQuadraticMap' = 0 := by omega
  exact ⟨D, e₁, e₂, e₃, heuD, hsigD, hDdef,
    hcong₁.trans (IntCongr.hyp_block e₁ (hcong₂.trans (IntCongr.hyp_block e₂ hcong₃)))⟩

/-! ### Block-permutation congruence toolkit (deliverable 3 support)

The pure-permutation reblock `3H ⊕ 2(−E₈) ≅ 2(−E₈) ⊕ 3H = k3Form` needs a small reusable toolkit: a
permutation `σ` acting on the index (`M.submatrix σ σ`) is an `IntCongr` (the permutation matrix `P =
1.submatrix id σ` is unimodular via `P Pᵀ = 1` and `Pᵀ M P = M.submatrix σ σ`), relabellings of the same
block matrix are congruent, and `blockDiag` respects congruence, commutes, and associates. -/

/-- **A relabelling of the index is an integer congruence.** For a permutation `σ : Fin n ≃ Fin n` the
permutation matrix `P = 1.submatrix id σ` is unimodular (`P Pᵀ = 1`, so `(det P)² = 1`) and satisfies
`Pᵀ M P = M.submatrix σ σ`. The reusable core: a permutation of coordinates reorders orthogonal summands. -/
theorem intCongr_submatrix_self {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (σ : Fin n ≃ Fin n) :
    IntCongr M (M.submatrix σ σ) := by
  refine ⟨(1 : Matrix (Fin n) (Fin n) ℤ).submatrix id σ, ?_, ?_⟩
  · have hPPt : ((1 : Matrix (Fin n) (Fin n) ℤ).submatrix id σ)
        * ((1 : Matrix (Fin n) (Fin n) ℤ).submatrix id σ)ᵀ = 1 := by
      rw [Matrix.transpose_submatrix, Matrix.transpose_one,
        Matrix.mul_submatrix_one, Matrix.submatrix_submatrix]
      simp
    have hdet := congrArg Matrix.det hPPt
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hdet
    exact ⟨Units.mkOfMulEqOne _ _ hdet, rfl⟩
  · rw [Matrix.transpose_submatrix, Matrix.transpose_one]
    ext i j
    simp [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply, Finset.sum_ite_eq,
      Finset.sum_ite_eq', mul_comm]

/-- **Two relabellings of the same block matrix are congruent.** `reindex e e X ≅ reindex f f X` for any
`e f : ι ≃ Fin n`: the two only differ by the permutation `f.symm.trans e` of `Fin n`, so
`intCongr_submatrix_self` applies. Lets an arbitrary reindex (e.g. the `eᵢ` a peel produces) be swapped
for the canonical `finSumFinEquiv` reindex inside `blockDiag`. -/
theorem intCongr_reindex_reindex {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℤ) (e f : ι ≃ Fin n) :
    IntCongr (Matrix.reindex e e X) (Matrix.reindex f f X) := by
  have hsub : Matrix.reindex f f X
      = (Matrix.reindex e e X).submatrix (f.symm.trans e) (f.symm.trans e) := by
    ext i j
    simp [Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [hsub]
  exact intCongr_submatrix_self _ _

/-- **`blockDiag` respects congruence.** If `A ≅ A'` and `B ≅ B'` then `A ⊕ B ≅ A' ⊕ B'`, via the
block-diagonal change of basis `blockDiag P Q` (`det = det P · det Q`, and `fromBlocks` distributes over
the product). The multiplicative core of the reblock. -/
theorem blockDiag_congr {na nb : ℕ} {A A' : Matrix (Fin na) (Fin na) ℤ}
    {B B' : Matrix (Fin nb) (Fin nb) ℤ} (hA : IntCongr A A') (hB : IntCongr B B') :
    IntCongr (blockDiag A B) (blockDiag A' B') := by
  obtain ⟨P, hP, hPeq⟩ := hA
  obtain ⟨Q, hQ, hQeq⟩ := hB
  refine ⟨blockDiag P Q, ?_, ?_⟩
  · rw [SpinSigmaRoute.blockDiag_def, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
    exact hP.mul hQ
  · simp only [SpinSigmaRoute.blockDiag_def]
    simp only [Matrix.reindex_apply, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]
    congr 1
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      hPeq, hQeq]

/-- **`blockDiag` block-swap is a coordinate relabelling.** `B ⊕ A` is the `Sum.swap` submatrix of
`A ⊕ B` (the two orthogonal summands trade places under the half-swap permutation of the index). Combined
with `intCongr_submatrix_self` this yields `A ⊕ B ≅ B ⊕ A` at any concrete pair of block sizes. -/
theorem blockDiag_swap_eq {na nb : ℕ} (A : Matrix (Fin na) (Fin na) ℤ)
    (B : Matrix (Fin nb) (Fin nb) ℤ) :
    blockDiag B A = (blockDiag A B).submatrix
      (finSumFinEquiv.symm.trans ((Equiv.sumComm (Fin nb) (Fin na)).trans finSumFinEquiv))
      (finSumFinEquiv.symm.trans ((Equiv.sumComm (Fin nb) (Fin na)).trans finSumFinEquiv)) := by
  rw [SpinSigmaRoute.blockDiag_def, SpinSigmaRoute.blockDiag_def, Matrix.reindex_apply,
    Matrix.reindex_apply, Matrix.submatrix_submatrix,
    ← Matrix.fromBlocks_submatrix_sum_swap_sum_swap A 0 0 B, Matrix.submatrix_submatrix]
  congr 1 <;>
    (ext x; simp [Function.comp, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.sumComm_apply])

/-! ### The consumer stub: reducing `IntCongr M k3Form` to the interior brick (deliverable 3)

`k3_candidate_split` reduces any even unimodular rank-22 σ=−16 form `M` to `3H ⊕ D` with `D` a
negative-definite rank-16 even unimodular residual. Reaching `k3Form = 2(−E₈) ⊕ 3H` needs one more input:
the hard interior brick, exposed here as a `Prop` interface so its exact statement is concrete and
consumable BEFORE it is proved (a later escalation owns it; NOT this dispatch).

* `StableNegRank16` (`Prop` interface, OPEN) — THE geometric content: the **one-hyperbolic stabilization**
  `H ⊕ D ≅ H ⊕ 2(−E₈)` for any negative-definite even unimodular rank-16 `D`. Note rank-16 *definite*
  uniqueness is FALSE (`E₈² ≇ D₁₆⁺`); only the `H`-stabilized statement is true, so the extra `H` is essential.
* `reblockToK3` (PROVED, above §"Block-permutation congruence toolkit") — pure permutation bookkeeping: the
  block-reordering `3H ⊕ 2(−E₈) ≅ 2(−E₈) ⊕ 3H = k3Form` (no geometry — an orthogonal-summand reordering
  congruence). Discharged, so `hk3_of_stable16` depends on `StableNegRank16` ALONE.

`hk3_of_stable16` wires them: `k3_candidate_split` (2) → `IntCongr.hyp_block` reassembly lifting the
rank-18 stabilization through the three peeled `H`'s → `reblockToK3`. -/

/-- **The interior brick interface (the one-hyperbolic stabilization).** For any negative-definite even
unimodular rank-16 form `D` (`σ = −16`, `sigPos = 0`), adding a hyperbolic plane yields a form congruent to
`H ⊕ 2(−E₈)`: `H ⊕ D ≅ H ⊕ 2(−E₈)` at rank 18, in the reindexing `e` the split produces. This is THE hard
content the K8b escalation must discharge (rank-16 definite uniqueness `E₈² ≟ D₁₆⁺` is FALSE — the `H` is
essential). Stated as a `Prop` so `hk3_of_stable16` can consume it before it is proved.

**ROUTE STATUS (do not re-derive the framing).** `StableNegRank16` is the Eichler/Kneser classification of
indefinite even unimodular lattices; Mathlib has none of that theory (no genus, no spinor genus, no strong
approximation, no `E₈`-lattice classification — only `CartanMatrix.E₈` as a matrix). The tractable route is
the classical **Milnor–Husemoller II.4.3** one adjudicated in `KUMMER_K4K10_DESIGN.md`, which routes the
EVEN statement through the ODD one:

* `M := H ⊕ D` and `N := H ⊕ 2(−E₈)` are even unimodular of rank 18, `σ = −16`;
* `M ⊕ ⟨1⟩` and `N ⊕ ⟨1⟩` are ODD unimodular of rank 19, `σ = −15`, indefinite, hence both `≅ ⟨1⟩² ⊕ ⟨−1⟩¹⁷`
  by the odd classification;
* in each, the adjoined `⟨1⟩` generator is a CHARACTERISTIC vector of self-product `1` whose orthogonal
  complement is `M` (resp. `N`) — so transitivity of the automorphism group on such vectors gives `M ≅ N`.

Two leaves of that route are now BANKED, kernel-pure (built wt1):

* `SKEFTHawking.odd_indefinite_represents_one` / `_neg_one` (`OddIndefiniteUnitVector`) — the II.4.3 entry
  point: an indefinite odd unimodular form of rank `≥ 5` represents `±1` primitively. Enabled by the banked
  Meyer/Hasse–Minkowski `weakIsotropic_of_five_le`, which carries NO evenness hypothesis at rank `≥ 5`.
* `SKEFTHawking.intCongr_I18_oneNegE8` and `SKEFTHawking.intCongr_oneHyp_I21` (`OddFormE8Absorption`) — the
  absorption identities `⟨1⟩ ⊕ ⟨−1⟩⁸ ≅ ⟨1⟩ ⊕ (−E₈)` (explicit del Pezzo `K^⊥ = E₈` basis) and
  `⟨1⟩ ⊕ H ≅ ⟨1⟩ ⊕ ⟨1⟩ ⊕ ⟨−1⟩`. These are what stop the induction stalling when a unit peel strands an
  even residual (`H` and `±E₈` are the only blocks such a residual contributes).

Pieces (1) and (2) are now BUILT (wt1); the route status is:

1. **Unit-vector split engine — DONE** (`SKEFTHawking/UnitVectorSplit.lean`, unconditional). The rank-1
   analogue of `SplitHyperbolic`: `unit_split_congr` turns `x ⬝ᵥ M *ᵥ x = ε` (`ε = ±1`) into
   `IntCongr M (reindex e e (fromBlocks ⟨ε⟩ 0 0 M'))` with `M'` symmetric unimodular of rank `n − 1` and
   `σ(M') = σ(M) − ε`. Mirrors `hypPerp` / `hypFullBasis` / `residGram` / `gramB_eq` / `latticeSig_split`
   one rank down, and adds the transport tower `unitResidGram_transport` /
   `unitPerp_exists_coords` / `unitResidGram_even_value` ("the residual Gram is `M` restricted to `x^⊥`,
   in coordinates"). Also `IntCongr.block_left`, the arbitrary-left-block form of `IntCongr.hyp_block`.
2. **Milnor–Husemoller II.4.3 — inductive step DONE, base cases 0/1/2 DONE, ranks 3–4 OPEN**
   (`SKEFTHawking/OddFormDiagonalization.lean`). `odd_indefinite_unit_peel` is UNCONDITIONAL: an odd
   indefinite unimodular form of rank `≥ 5` peels a unit block whose residual is again ODD and
   INDEFINITE. **CORRECTION to the earlier framing — this was NOT bookkeeping.** A naive unit peel can
   strand an EVEN residual (the `⟨1⟩ ⊕ E₈` phenomenon), and absorbing it is not available: the
   absorptions `intCongr_I18_oneNegE8` / `intCongr_oneHyp_I21` only handle the *named* blocks `−E₈`
   and `H`, whereas the stranded residual is an ARBITRARY even unimodular form — identifying it is the
   classification itself. The fix is to move the VECTOR: an even residual is even unimodular AND
   indefinite, hence carries a hyperbolic pair `(v, w)`, and `y := x + w` has `y·y = ε` while
   `z := x − ε·v` sits in `y^⊥` with ODD self-product `ε`. Peeling `y` preserves rank, signature AND
   parity. Consequence: **this route uses neither absorption identity** and needs no block
   re-association.
3. **The rank-3/4 base cases — DONE** (`SKEFTHawking/OddSmallRankHM.lean`, unconditional,
   kernel-pure). `OddRank34Diagonalizable` is now the THEOREM
   `SKEFTHawking.oddRank34Diagonalizable`, so `odd_indefinite_pmDiagonal_unconditional` /
   `odd_indefinite_intCongr_unconditional` are the hypothesis-free rank-and-signature classification
   the assembly consumes. What made it work: `RokhlinHMRankFour`'s *theorem* is even- and
   square-discriminant-specific, but its **tooling is not** —
   `isotropic_padicInt_of_unit_det` needs only rank `≥ 3`, `p ≠ 2` and a unit determinant, so the odd
   places are free at both ranks; `ℝ` is indefiniteness; and the place `2` splits by rank:
   * rank 3 — a TERNARY form's local obstruction at every place is the SINGLE Hilbert symbol
     `(−d₀d₂, −d₁d₂)_v`, so `hilbertPrime_two_eq_one_of_real_odd` pins the `2`-factor from the
     others. **No square-discriminant hypothesis** — that was a rank-4 artifact.
   * rank 4, `det = +1` (`σ = 0`) — square discriminant, so
     `quaternary_sqdisc_solvable_of_local_no_two` applies verbatim; evenness entered
     `weakIsotropic_rank_four` ONLY through `det_eq_one_of_evenUnimodular_four`, i.e. as the
     determinant value.
   * rank 4, `det = −1` (`σ = ±2`) — non-square discriminant, so reciprocity does NOT close it and
     the place `2` is done directly in `ℚ_[2]`: with `α = −d₀d₁`, `β = −d₂d₃` and `αβ = −s²`, either
     `α` or `β` is a square (then that binary is already isotropic) or `α, −α` are both non-squares,
     and `exists_hilbert2Int_witness` (canonical class `c·σ²`, `g = 2` for `c ≡ 3,5 (mod 8)`,
     `g = 5` for `c = 2·odd`) realizes every prescription of `((t,α)₂, (t,−1)₂)`, giving a common
     represented value.
4. **Wall's characteristic-vector transitivity — the LAST open leaf.** In `⟨1⟩^p ⊕ ⟨−1⟩^q` indefinite, the
   automorphism group is transitive on characteristic vectors of self-product `1`. This is what
   performs the `⟨1⟩`-cancellation in the assembly. Elementary (reflections only) — NOT genus theory —
   so it stays inside this route. -/
def StableNegRank16 : Prop :=
  ∀ (D : Matrix (Fin 16) (Fin 16) ℤ) (e : Fin 2 ⊕ Fin 16 ≃ Fin 18),
    IsEvenUnimodular D → latticeSig D = -16 →
    sigPos (D.map (Int.cast : ℤ → ℝ)).toQuadraticMap' = 0 →
    IntCongr (Matrix.reindex e e (Matrix.fromBlocks Hyp 0 0 D))
      (Matrix.reindex e e (Matrix.fromBlocks Hyp 0 0 (SpinSigmaRoute.blockDiag (-E8lit) (-E8lit))))

/-- **The block-reordering brick (pure permutation bookkeeping) — PROVED.** The peeled form `3H ⊕ 2(−E₈)`
(three hyperbolic planes stacked over `2(−E₈)`, in the reindexings `e₁,e₂,e₃` the split produces) is
congruent to `k3Form = 2(−E₈) ⊕ 3H`. No geometry: the arbitrary peel reindexings `eᵢ` are relabelled to the
canonical `blockDiag` shape (`IntCongr.hyp_block` + `intCongr_reindex_reindex`), then the `2(−E₈)` block is
rotated from the inside to the front by three `blockDiag`-swap congruences (`blockDiag_swap_eq` +
`intCongr_submatrix_self`, threaded by `blockDiag_congr`). Discharges the former `ReblockToK3` interface, so
`hk3_of_stable16` now depends on `StableNegRank16` alone. -/
theorem reblockToK3
    (e₁ : Fin 2 ⊕ Fin 20 ≃ Fin 22) (e₂ : Fin 2 ⊕ Fin 18 ≃ Fin 20) (e₃ : Fin 2 ⊕ Fin 16 ≃ Fin 18) :
    IntCongr (Matrix.reindex e₁ e₁ (Matrix.fromBlocks Hyp 0 0
      (Matrix.reindex e₂ e₂ (Matrix.fromBlocks Hyp 0 0
        (Matrix.reindex e₃ e₃ (Matrix.fromBlocks Hyp 0 0 (SpinSigmaRoute.blockDiag (-E8lit) (-E8lit)))))))) k3Form := by
  -- Step 1: relabel the arbitrary peel reindexings `eᵢ` to the canonical `blockDiag` shape.
  have h3 : IntCongr
      (Matrix.reindex e₃ e₃ (Matrix.fromBlocks Hyp 0 0 (SpinSigmaRoute.blockDiag (-E8lit) (-E8lit))))
      (SpinSigmaRoute.blockDiag Hyp (SpinSigmaRoute.blockDiag (-E8lit) (-E8lit))) :=
    intCongr_reindex_reindex (Matrix.fromBlocks Hyp 0 0 (SpinSigmaRoute.blockDiag (-E8lit) (-E8lit))) e₃ finSumFinEquiv
  have h2 : IntCongr
      (Matrix.reindex e₂ e₂ (Matrix.fromBlocks Hyp 0 0
        (Matrix.reindex e₃ e₃ (Matrix.fromBlocks Hyp 0 0 (SpinSigmaRoute.blockDiag (-E8lit) (-E8lit))))))
      (SpinSigmaRoute.blockDiag Hyp (SpinSigmaRoute.blockDiag Hyp (SpinSigmaRoute.blockDiag (-E8lit) (-E8lit)))) :=
    (IntCongr.hyp_block e₂ h3).trans
      (intCongr_reindex_reindex
        (Matrix.fromBlocks Hyp 0 0 (SpinSigmaRoute.blockDiag Hyp (SpinSigmaRoute.blockDiag (-E8lit) (-E8lit)))) e₂ finSumFinEquiv)
  have h1 : IntCongr
      (Matrix.reindex e₁ e₁ (Matrix.fromBlocks Hyp 0 0
        (Matrix.reindex e₂ e₂ (Matrix.fromBlocks Hyp 0 0
          (Matrix.reindex e₃ e₃ (Matrix.fromBlocks Hyp 0 0 (SpinSigmaRoute.blockDiag (-E8lit) (-E8lit))))))))
      (SpinSigmaRoute.blockDiag Hyp (SpinSigmaRoute.blockDiag Hyp (SpinSigmaRoute.blockDiag Hyp (SpinSigmaRoute.blockDiag (-E8lit) (-E8lit))))) :=
    (IntCongr.hyp_block e₁ h2).trans
      (intCongr_reindex_reindex
        (Matrix.fromBlocks Hyp 0 0 (SpinSigmaRoute.blockDiag Hyp (SpinSigmaRoute.blockDiag Hyp (SpinSigmaRoute.blockDiag (-E8lit) (-E8lit)))))
        e₁ finSumFinEquiv)
  -- Step 2: rotate the `2(−E₈)` block from the inside to the front (three `blockDiag` swaps,
  -- threaded through the outer hyperbolic planes by `blockDiag_congr`).
  have cW' : @IntCongr 18 (SpinSigmaRoute.blockDiag Hyp (SpinSigmaRoute.blockDiag (-E8lit) (-E8lit)))
      (SpinSigmaRoute.blockDiag (SpinSigmaRoute.blockDiag (-E8lit) (-E8lit)) Hyp) := by
    rw [blockDiag_swap_eq Hyp (SpinSigmaRoute.blockDiag (-E8lit) (-E8lit))]
    exact intCongr_submatrix_self _ _
  have cW : @IntCongr 20
      (SpinSigmaRoute.blockDiag Hyp (SpinSigmaRoute.blockDiag Hyp (SpinSigmaRoute.blockDiag (-E8lit) (-E8lit))))
      (SpinSigmaRoute.blockDiag (SpinSigmaRoute.blockDiag Hyp (SpinSigmaRoute.blockDiag (-E8lit) (-E8lit))) Hyp) := by
    rw [blockDiag_swap_eq Hyp (SpinSigmaRoute.blockDiag Hyp (SpinSigmaRoute.blockDiag (-E8lit) (-E8lit)))]
    exact intCongr_submatrix_self _ _
  have cTop : @IntCongr 22
      (SpinSigmaRoute.blockDiag Hyp
        (SpinSigmaRoute.blockDiag Hyp (SpinSigmaRoute.blockDiag Hyp (SpinSigmaRoute.blockDiag (-E8lit) (-E8lit)))))
      (SpinSigmaRoute.blockDiag
        (SpinSigmaRoute.blockDiag Hyp (SpinSigmaRoute.blockDiag Hyp (SpinSigmaRoute.blockDiag (-E8lit) (-E8lit)))) Hyp) := by
    rw [blockDiag_swap_eq Hyp
      (SpinSigmaRoute.blockDiag Hyp (SpinSigmaRoute.blockDiag Hyp (SpinSigmaRoute.blockDiag (-E8lit) (-E8lit))))]
    exact intCongr_submatrix_self _ _
  have hmid : @IntCongr 20
      (SpinSigmaRoute.blockDiag Hyp (SpinSigmaRoute.blockDiag Hyp (SpinSigmaRoute.blockDiag (-E8lit) (-E8lit))))
      (SpinSigmaRoute.blockDiag (SpinSigmaRoute.blockDiag (SpinSigmaRoute.blockDiag (-E8lit) (-E8lit)) Hyp) Hyp) :=
    cW.trans (blockDiag_congr cW' (IntCongr.rfl Hyp))
  have htop : @IntCongr 22
      (SpinSigmaRoute.blockDiag Hyp
        (SpinSigmaRoute.blockDiag Hyp (SpinSigmaRoute.blockDiag Hyp (SpinSigmaRoute.blockDiag (-E8lit) (-E8lit)))))
      (SpinSigmaRoute.blockDiag (SpinSigmaRoute.blockDiag
        (SpinSigmaRoute.blockDiag (SpinSigmaRoute.blockDiag (-E8lit) (-E8lit)) Hyp) Hyp) Hyp) :=
    cTop.trans (blockDiag_congr hmid (IntCongr.rfl Hyp))
  exact h1.trans htop

/-- **The K8b consumer stub** (deliverable 3): `IntCongr M k3Form` for any even unimodular rank-22 form of
signature `−16`, reduced to the interior brick `StableNegRank16` ALONE (the permutation reblock is now the
proved `reblockToK3`). This is the one-line reduction wiring the interior interface: `k3_candidate_split`
peels three hyperbolic planes off `M` down to a negative-definite rank-16 residual `D`; `StableNegRank16`
stabilizes `H ⊕ D` to `H ⊕ 2(−E₈)`; `IntCongr.hyp_block` lifts that through the three peeled `H`'s;
`reblockToK3` reorders the result into `k3Form`. Once the escalation proves `StableNegRank16`, this
discharges the `hk3` field of `K3RealizingElement` unconditionally. -/
theorem hk3_of_stable16 (hstable : StableNegRank16)
    (M : Matrix (Fin 22) (Fin 22) ℤ) (heu : IsEvenUnimodular M) (hsig : latticeSig M = -16) :
    IntCongr M k3Form := by
  obtain ⟨D, e₁, e₂, e₃, hD, hDsig, hDdef, hcong⟩ := k3_candidate_split M heu hsig
  have hstab := hstable D e₃ hD hDsig hDdef
  exact (hcong.trans (IntCongr.hyp_block e₁ (IntCongr.hyp_block e₂ hstab))).trans
    (reblockToK3 e₁ e₂ e₃)

end SKEFTHawking
