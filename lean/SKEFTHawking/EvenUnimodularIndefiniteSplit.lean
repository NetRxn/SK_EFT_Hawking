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

/-! ### The consumer stub: reducing `IntCongr M k3Form` to the interior brick (deliverable 3)

`k3_candidate_split` reduces any even unimodular rank-22 σ=−16 form `M` to `3H ⊕ D` with `D` a
negative-definite rank-16 even unimodular residual. Reaching `k3Form = 2(−E₈) ⊕ 3H` needs one more input —
the hard interior brick, exposed here as a `Prop` interface so its exact statement is concrete and
consumable BEFORE it is proved (a later escalation owns it; NOT this dispatch).

The interface has two parts, cleanly separated:
* `StableNegRank16` — THE geometric content: the **one-hyperbolic stabilization** `H ⊕ D ≅ H ⊕ 2(−E₈)`
  for any negative-definite even unimodular rank-16 `D`. Note rank-16 *definite* uniqueness is FALSE
  (`E₈² ≇ D₁₆⁺`); only the `H`-stabilized statement is true, which is why the extra `H` is essential.
* `ReblockToK3` — pure permutation bookkeeping: the block-reordering `3H ⊕ 2(−E₈) ≅ 2(−E₈) ⊕ 3H = k3Form`
  (no geometry — an orthogonal-summand reordering congruence; an isolable ≤1-brick cleanup).

`hk3_of_stable16` wires them: `k3_candidate_split` (2) → `IntCongr.hyp_block` reassembly lifting the
rank-18 stabilization through the three peeled `H`'s → the reblock. -/

/-- **The interior brick interface (the one-hyperbolic stabilization).** For any negative-definite even
unimodular rank-16 form `D` (`σ = −16`, `sigPos = 0`), adding a hyperbolic plane yields a form congruent to
`H ⊕ 2(−E₈)`: `H ⊕ D ≅ H ⊕ 2(−E₈)` at rank 18, in the reindexing `e` the split produces. This is THE hard
content the K8b escalation must discharge (rank-16 definite uniqueness `E₈² ≟ D₁₆⁺` is FALSE — the `H` is
essential). Stated as a `Prop` so `hk3_of_stable16` can consume it before it is proved. -/
def StableNegRank16 : Prop :=
  ∀ (D : Matrix (Fin 16) (Fin 16) ℤ) (e : Fin 2 ⊕ Fin 16 ≃ Fin 18),
    IsEvenUnimodular D → latticeSig D = -16 →
    sigPos (D.map (Int.cast : ℤ → ℝ)).toQuadraticMap' = 0 →
    IntCongr (Matrix.reindex e e (Matrix.fromBlocks Hyp 0 0 D))
      (Matrix.reindex e e (Matrix.fromBlocks Hyp 0 0 (blockDiag (-E8lit) (-E8lit))))

/-- **The block-reordering interface (pure permutation bookkeeping).** The peeled form `3H ⊕ 2(−E₈)` (three
hyperbolic planes stacked over `2(−E₈)`, in the reindexings `e₁,e₂,e₃` the split produces) is congruent to
`k3Form = 2(−E₈) ⊕ 3H`. No geometry — an orthogonal-summand reordering congruence (an isolable ≤1-brick
permutation cleanup). Separated from `StableNegRank16` to keep the geometric interior brick's interface
clean. -/
def ReblockToK3 : Prop :=
  ∀ (e₁ : Fin 2 ⊕ Fin 20 ≃ Fin 22) (e₂ : Fin 2 ⊕ Fin 18 ≃ Fin 20) (e₃ : Fin 2 ⊕ Fin 16 ≃ Fin 18),
    IntCongr (Matrix.reindex e₁ e₁ (Matrix.fromBlocks Hyp 0 0
      (Matrix.reindex e₂ e₂ (Matrix.fromBlocks Hyp 0 0
        (Matrix.reindex e₃ e₃ (Matrix.fromBlocks Hyp 0 0 (blockDiag (-E8lit) (-E8lit)))))))) k3Form

/-- **The K8b consumer stub** (deliverable 3): `IntCongr M k3Form` for any even unimodular rank-22 form of
signature `−16`, reduced to the interior brick `StableNegRank16` (+ the permutation reblock `ReblockToK3`).
This is the one-line reduction wiring the interior interface: `k3_candidate_split` peels three hyperbolic
planes off `M` down to a negative-definite rank-16 residual `D`; `StableNegRank16` stabilizes `H ⊕ D` to
`H ⊕ 2(−E₈)`; `IntCongr.hyp_block` lifts that through the three peeled `H`'s; `ReblockToK3` reorders the
result into `k3Form`. Once the escalation proves `StableNegRank16` (and the trivial `ReblockToK3`), this
discharges the `hk3` field of `K3RealizingElement` unconditionally. -/
theorem hk3_of_stable16 (hstable : StableNegRank16) (hreblock : ReblockToK3)
    (M : Matrix (Fin 22) (Fin 22) ℤ) (heu : IsEvenUnimodular M) (hsig : latticeSig M = -16) :
    IntCongr M k3Form := by
  obtain ⟨D, e₁, e₂, e₃, hD, hDsig, hDdef, hcong⟩ := k3_candidate_split M heu hsig
  have hstab := hstable D e₃ hD hDsig hDdef
  exact (hcong.trans (IntCongr.hyp_block e₁ (IntCongr.hyp_block e₂ hstab))).trans
    (hreblock e₁ e₂ e₃)

end SKEFTHawking
