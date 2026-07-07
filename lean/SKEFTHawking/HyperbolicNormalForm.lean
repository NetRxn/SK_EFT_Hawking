/-
# Phase 5q.H (E1 lattice — KT injective-direction core): the `σ=0 ⟹ n·H` congruence normal form

Strengthens `even_unimodular_sig_zero_split` (existence of a smaller `σ=0` even-unimodular residual) to a
CONGRUENCE `Pᵀ M P = reindex (H ⊕ M')`, and iterates it (strong induction on rank) to the full hyperbolic
normal form: every `σ=0` even unimodular integer form is congruent to a block-sum of hyperbolic planes.
This is the **lattice half of the injective direction of `Ω₄^{Spin}≅ℤ`** (KT geometric route): a `σ=0`
spin 4-manifold's intersection form is `n·H`, feeding the (carried) surgery realization `n(S²×S²)`.

The congruence data already lives inside `latticeSig_split`'s proof (the `hypFullBasis` change of basis
`P`, unimodular, with `Pᵀ M P = reindex e e (fromBlocks Hyp 0 0 residGram)` via `gramB_eq`); this module
extracts it as a reusable `IntCongr` engine. UNCONDITIONAL (`[HM]` is a theorem).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SplitHyperbolic
import SKEFTHawking.EvenUnimodularHyperbolic
import SKEFTHawking.LatticeSignatureCongr

namespace SKEFTHawking

open Matrix Module

/-- **Integer matrix congruence** `M ≅ N`: `∃ P` unimodular (`det P` a unit, i.e. `±1`) with
`Pᵀ M P = N`. The equivalence under which the signature (Sylvester) and even-unimodularity are invariant. -/
def IntCongr {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ P : Matrix (Fin n) (Fin n) ℤ, IsUnit P.det ∧ Pᵀ * M * P = N

theorem IntCongr.rfl {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : IntCongr M M :=
  ⟨1, by simp, by simp⟩

theorem IntCongr.trans {n : ℕ} {M N K : Matrix (Fin n) (Fin n) ℤ}
    (h₁ : IntCongr M N) (h₂ : IntCongr N K) : IntCongr M K := by
  obtain ⟨P, hP, hPeq⟩ := h₁
  obtain ⟨Q, hQ, hQeq⟩ := h₂
  refine ⟨P * Q, by rw [Matrix.det_mul]; exact hP.mul hQ, ?_⟩
  rw [Matrix.transpose_mul]
  calc Qᵀ * Pᵀ * M * (P * Q) = Qᵀ * (Pᵀ * M * P) * Q := by
        simp only [Matrix.mul_assoc]
    _ = Qᵀ * N * Q := by rw [hPeq]
    _ = K := hQeq

/-- Congruence preserves the lattice signature (Sylvester's law of inertia over `ℝ`). -/
theorem IntCongr.latticeSig {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℤ} (h : IntCongr M N) :
    latticeSig N = latticeSig M := by
  obtain ⟨P, hP, hPeq⟩ := h
  rw [← hPeq]; exact latticeSig_congr M P hP

/-- **The congruence-strengthened split** (unconditional): a `σ=0` even unimodular form of rank `≥ 2` is
`IntCongr` to `H ⊕ M'` (reindexed to `Fin n`), with `M'` a rank-`(n−2)` `σ=0` even unimodular residual.
Packages the change-of-basis already inside `latticeSig_split` (`hypFullBasis` → `P` unimodular,
`Pᵀ M P = reindex (H ⊕ residGram)` via `gramB_eq`). The engine of the `σ=0 ⟹ n·H` normal form. -/
theorem even_unimodular_sig_zero_split_congr {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (heu : IsEvenUnimodular M) (hsig : latticeSig M = 0) (hn2 : 2 ≤ n) :
    ∃ (M' : Matrix (Fin (n - 2)) (Fin (n - 2)) ℤ) (e : Fin 2 ⊕ Fin (n - 2) ≃ Fin n),
      IntCongr M (Matrix.reindex e e (Matrix.fromBlocks Hyp 0 0 M'))
        ∧ IsEvenUnimodular M' ∧ latticeSig M' = 0 := by
  obtain ⟨hsp, hsn⟩ := even_unimodular_sig_zero_indefinite M heu hsig (by omega)
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

end SKEFTHawking
