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
import SKEFTHawking.EvenLatticeForm

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

/-- **Congruence is symmetric**: a unimodular change of basis inverts over `ℤ`
(`Matrix.invertibleOfIsUnitDet`), and `(⅟P)ᵀ N ⅟P = M`. -/
theorem IntCongr.symm {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℤ} (h : IntCongr M N) :
    IntCongr N M := by
  obtain ⟨P, hP, hPMP⟩ := h
  letI := P.invertibleOfIsUnitDet hP
  refine ⟨⅟P, ?_, ?_⟩
  · exact IsUnit.of_mul_eq_one P.det
      (by rw [← Matrix.det_mul, invOf_mul_self, Matrix.det_one])
  · rw [← hPMP]
    calc (⅟P)ᵀ * (Pᵀ * M * P) * ⅟P = ((⅟P)ᵀ * Pᵀ) * M * (P * ⅟P) := by
          simp only [Matrix.mul_assoc]
      _ = M := by
          rw [← Matrix.transpose_mul, mul_invOf_self, Matrix.transpose_one,
            Matrix.one_mul, Matrix.mul_one]

/-- **Even-unimodularity is a congruence invariant.** Symmetry and `det = ±1` transport directly
(`(det P)² = 1`); evenness of the diagonal transports because an even symmetric form takes even
values (`EvenLattice.even_form_dvd`) and the congruent diagonal entries ARE values of the form:
`N i i = Pᵢᵀ M Pᵢ` for the `i`-th column `Pᵢ`. -/
theorem IntCongr.isEvenUnimodular {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℤ} (h : IntCongr M N)
    (heu : IsEvenUnimodular M) : IsEvenUnimodular N := by
  obtain ⟨P, hP, hPMP⟩ := h
  obtain ⟨hsym, hdet, heven⟩ := heu
  refine ⟨?_, ?_, ?_⟩
  · rw [← hPMP]
    calc (Pᵀ * M * P)ᵀ = Pᵀ * (Pᵀ * M)ᵀ := Matrix.transpose_mul _ _
      _ = Pᵀ * (Mᵀ * P) := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
      _ = Pᵀ * M * P := by rw [hsym, Matrix.mul_assoc]
  · have hdP := Int.isUnit_iff.mp hP
    rw [IsUnimodular, ← hPMP, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    rcases hdet with h1 | h1 <;> rcases hdP with h2 | h2 <;> rw [h1, h2] <;> norm_num
  · intro i
    have hentry : N i i = (fun j => P j i) ⬝ᵥ M *ᵥ (fun j => P j i) := by
      rw [← hPMP]
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr (Eq.refl _) fun x _ =>
        Finset.sum_congr (Eq.refl _) fun y _ => by ring
    rw [hentry]
    exact EvenLattice.even_form_dvd hsym heven _

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

/-- **Congruence extends through the hyperbolic block**: if `M' ≅ N'` then `H ⊕ M' ≅ H ⊕ N'` (reindexed),
via the block change of basis `1 ⊕ Q`. The inductive step of the `σ=0 ⟹ n·H` normal form. -/
theorem IntCongr.hyp_block {p q : ℕ} (e : Fin 2 ⊕ Fin q ≃ Fin p)
    {M' N' : Matrix (Fin q) (Fin q) ℤ} (h : IntCongr M' N') :
    IntCongr (Matrix.reindex e e (Matrix.fromBlocks Hyp 0 0 M'))
        (Matrix.reindex e e (Matrix.fromBlocks Hyp 0 0 N')) := by
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

/-- **A hyperbolic-standard form**: a reindexed iterated block-sum of hyperbolic planes `H` (the
integral shape of `n·H`). The `cons` step allows any target cardinality `p` (the equiv itself pins
`p = m + 2`), which sidesteps the `Nat`-subtraction casts of the rank induction. -/
inductive IsHyperbolicForm : {n : ℕ} → Matrix (Fin n) (Fin n) ℤ → Prop
  | empty : IsHyperbolicForm (0 : Matrix (Fin 0) (Fin 0) ℤ)
  | cons {m p : ℕ} (e : Fin 2 ⊕ Fin m ≃ Fin p) {N : Matrix (Fin m) (Fin m) ℤ}
      (h : IsHyperbolicForm N) :
      IsHyperbolicForm (Matrix.reindex e e (Matrix.fromBlocks Hyp 0 0 N))

/-- **The `σ=0 ⟹ n·H` hyperbolic normal form (unconditional).** Every `σ=0` even unimodular integer
form is `IntCongr` to a hyperbolic-standard form (a reindexed block-sum of `H`'s). Strong induction on
rank: peel one `H` by the congruence-split, recurse on the residual, and re-block via `IntCongr.hyp_block`.
This is the **lattice half of the injective direction of `Ω₄^{Spin}≅ℤ`** — a `σ=0` spin 4-manifold's
intersection form is `n·H`. (Rank `1` is impossible: `M 0 0` is even yet `±1`.) -/
theorem exists_hyperbolic_congr : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ),
    IsEvenUnimodular M → latticeSig M = 0 →
    ∃ N : Matrix (Fin n) (Fin n) ℤ, IsHyperbolicForm N ∧ IntCongr M N := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro M heu hsig
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · interval_cases n
      · exact ⟨0, Subsingleton.elim (0 : Matrix (Fin 0) (Fin 0) ℤ) 0 ▸ IsHyperbolicForm.empty,
          Subsingleton.elim M 0 ▸ IntCongr.rfl _⟩
      · exfalso
        have hdet : M.det = M 0 0 := by simp
        have heven : (2 : ℤ) ∣ M 0 0 := heu.2.2 0
        rcases heu.2.1 with h | h <;> rw [hdet] at h <;> omega
    · obtain ⟨M', e, hcong, heu', hsig'⟩ := even_unimodular_sig_zero_split_congr M heu hsig hge
      obtain ⟨N', hN'form, hN'cong⟩ := IH (n - 2) (by omega) M' heu' hsig'
      exact ⟨Matrix.reindex e e (Matrix.fromBlocks Hyp 0 0 N'),
        IsHyperbolicForm.cons e hN'form, hcong.trans (IntCongr.hyp_block e hN'cong)⟩

/-! ### Hyperbolic-summand bookkeeping — the converse invariants of the normal form

`IsHyperbolicForm` was introduced above as the *target* of the `σ=0 ⟹ n·H` normal form; these
lemmas pin down what a hyperbolic-standard form *is*: even unimodular (`isEvenUnimodular`), of
signature `0` (`latticeSig_eq_zero`), and of even rank (`two_dvd_rank` — `q = n/2` hyperbolic
summands, the count the `n(S²×S²)` realization statement consumes). Together with
`exists_hyperbolic_congr` they make the normal form a genuine characterization of the σ=0 even
unimodular congruence class, and they are the lattice-side bookkeeping of the KT injective
direction (DR route `Lit-Search/Phase-5qH/Omega4Spin_Z_formalization_route_20260706.md`). -/

/-- The zero matrix has signature `0` (in any rank): `σ(−0) = −σ(0)` forces it. -/
theorem latticeSig_zero_matrix {n : ℕ} : latticeSig (0 : Matrix (Fin n) (Fin n) ℤ) = 0 := by
  have h := latticeSig_neg (0 : Matrix (Fin n) (Fin n) ℤ)
  rw [neg_zero] at h
  omega

/-- **Even-unimodularity ⟹ the real form is nondegenerate** (`radical = ⊥`): `det = ±1 ≠ 0` casts
to a nondegenerate symmetric real matrix. The reusable bridge to the block-additivity theorems. -/
theorem IsEvenUnimodular.radical_eq_bot {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ}
    (heu : IsEvenUnimodular M) :
    (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥ := by
  have hsymmR : (M.map (Int.cast : ℤ → ℝ))ᵀ = M.map (Int.cast : ℤ → ℝ) := by
    rw [← Matrix.transpose_map, heu.1]
  have hdet : M.det ≠ 0 := by rcases heu.2.1 with h | h <;> rw [h] <;> norm_num
  exact nondeg_radical_eq_bot _ hsymmR (cast_nondegenerate M hdet)

/-- **A hyperbolic-standard form is even unimodular** (bookkeeping converse): each `H` block is
symmetric/unimodular/even and all three properties pass through `fromBlocks` + `reindex`. -/
theorem IsHyperbolicForm.isEvenUnimodular {n : ℕ} {N : Matrix (Fin n) (Fin n) ℤ}
    (h : IsHyperbolicForm N) : IsEvenUnimodular N := by
  induction h with
  | empty =>
    exact ⟨Matrix.transpose_zero, Or.inl (Matrix.det_fin_zero (A := (0 : Matrix (Fin 0) (Fin 0) ℤ))),
      fun i => i.elim0⟩
  | cons e h ih =>
    obtain ⟨hsym, hdet, heven⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · show (Matrix.reindex e e _)ᵀ = _
      rw [Matrix.reindex_apply, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose,
        Matrix.transpose_zero, Matrix.transpose_zero, hyp_symm, hsym]
    · rw [IsUnimodular, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
        show Hyp.det = -1 from by decide]
      rcases hdet with h1 | h1 <;> rw [h1] <;> [exact Or.inr (by ring); exact Or.inl (by ring)]
    · intro i
      rw [Matrix.reindex_apply, Matrix.submatrix_apply]
      rcases e.symm i with j | j
      · exact hyp_even j
      · exact heven j

/-- **A hyperbolic-standard form has signature `0`** (bookkeeping converse): block additivity of
the signature (`latticeSigOf_fromBlocks`, both blocks nondegenerate) + `σ(H) = 0` per summand. -/
theorem IsHyperbolicForm.latticeSig_eq_zero {n : ℕ} {N : Matrix (Fin n) (Fin n) ℤ}
    (h : IsHyperbolicForm N) : latticeSig N = 0 := by
  induction h with
  | empty => exact latticeSig_zero_matrix
  | cons e h ih =>
    rw [← latticeSigOf_fin, latticeSigOf_reindex,
      latticeSigOf_fromBlocks _ _ hyp_radical h.isEvenUnimodular.radical_eq_bot,
      latticeSigOf_fin, latticeSigOf_fin, hyp_latticeSig, ih, add_zero]

/-- **A hyperbolic-standard form has even rank** — it is a block-sum of `q = n/2` rank-2 planes. -/
theorem IsHyperbolicForm.two_dvd_rank {n : ℕ} {N : Matrix (Fin n) (Fin n) ℤ}
    (h : IsHyperbolicForm N) : 2 ∣ n := by
  induction h with
  | empty => exact ⟨0, rfl⟩
  | cons e h ih =>
    have hcard := Fintype.card_congr e
    simp only [Fintype.card_sum, Fintype.card_fin] at hcard
    omega

/-- **A `σ=0` even unimodular form has even rank** (`q = n/2` hyperbolic summands) — the count
bookkeeping feeding the `n(S²×S²)` realization statement of the KT injective direction. -/
theorem even_unimodular_sig_zero_two_dvd_rank {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (heu : IsEvenUnimodular M) (hsig : latticeSig M = 0) : 2 ∣ n := by
  obtain ⟨N, hN, -⟩ := exists_hyperbolic_congr M heu hsig
  exact hN.two_dvd_rank

/-- **The hyperbolic normal form is a full characterization**: `M` is congruent to a
hyperbolic-standard form **iff** `M` is even unimodular of signature `0`. Forward: the bookkeeping
invariants transported back along the (symmetric) congruence; converse: `exists_hyperbolic_congr`.
The `σ=0` slice of the Milnor–Husemoller even-indefinite classification, as an iff. -/
theorem isHyperbolicForm_congr_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    (∃ N : Matrix (Fin n) (Fin n) ℤ, IsHyperbolicForm N ∧ IntCongr M N) ↔
      IsEvenUnimodular M ∧ latticeSig M = 0 := by
  constructor
  · rintro ⟨N, hN, hcong⟩
    refine ⟨hcong.symm.isEvenUnimodular hN.isEvenUnimodular, ?_⟩
    rw [← hcong.latticeSig]
    exact hN.latticeSig_eq_zero
  · rintro ⟨heu, hsig⟩
    exact exists_hyperbolic_congr M heu hsig

end SKEFTHawking
