/-
# Phase 5q.H (K8b interior) — Milnor–Husemoller II.4.3: diagonalizing an odd indefinite form

Piece (2) of the Milnor–Husemoller route to `EvenUnimodularIndefiniteSplit.StableNegRank16`:
an INDEFINITE ODD unimodular integer form is `⟨1⟩^p ⊕ ⟨−1⟩^q`.

**What is unconditional here (the headline).** `odd_indefinite_unit_peel`: an odd indefinite
unimodular form of rank `≥ 5` splits off a unit block **with an ODD indefinite unimodular residual**
of rank `n − 1`. Both adjectives matter: "indefinite" is what lets the induction keep running, and
"odd" is what stops it stalling on an even residual. The peel is the whole inductive content of
II.4.3, and it is proved here with no classification input.

The construction of the *odd* residual is the point. Peeling an arbitrary unit vector `x`
(`odd_indefinite_represents_±one`) can strand an EVEN residual `x^⊥` — that is exactly the `⟨1⟩ ⊕ E₈`
phenomenon. The fix is to move the vector rather than to absorb the residual: if `x^⊥` is even it is
also indefinite (by the signature choice `ε = sign σ`), hence carries a hyperbolic pair `(v, w)`
(`hasIsotropicVector` + `exists_hyperbolic_pair`, transported into `x^⊥ ⊆ ℤⁿ` by
`unitResidGram_transport`), and then

  `y := x + w`  has  `y·y = ε`,   and   `z := x − ε·v`  has  `z·y = 0`,  `z·z = ε` (ODD),

so `y^⊥` contains a vector of odd self-product and is therefore an odd form
(`unitResidGram_even_value`). Peeling `y` instead of `x` keeps rank, signature — and parity.
No block re-association, no `H`-absorption, no `E₈`-absorption is needed.

**What is NOT proved here — and the precise reason.** The induction bottoms out at rank `≤ 4`, where
`odd_indefinite_represents_one` is unavailable: it runs on Meyer/Hasse–Minkowski
(`weakIsotropic_of_five_le`), which needs rank `≥ 5`. Ranks `2, 3, 4` are therefore exposed as the
`Prop` interface `OddSmallRankDiagonalizable`, and `odd_indefinite_pmDiagonal` /
`odd_indefinite_intCongr` are stated relative to it.

That residue is **not** bookkeeping: an odd indefinite unimodular form of rank 3 or 4 need not
visibly represent `0`, and establishing that it does is a Hasse–Minkowski discharge of the same shape
as the (600-line, EVEN-and-square-discriminant-specific) `RokhlinHMRankFour` — a rank-3 Legendre
step and a rank-4 step covering the non-square-discriminant (`det = −1`, `σ = ±2`) shapes that the
banked square-discriminant machinery does not reach. See the module `## The remaining gap` section.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.UnitVectorSplit
import SKEFTHawking.OddIndefiniteUnitVector
import SKEFTHawking.RokhlinHMRankFour
import SKEFTHawking.EvenUnimodularIndefiniteSplit

namespace SKEFTHawking

open Matrix Module QuadraticForm

/-! ### `±1`-diagonal forms -/

/-- A form is **`±1`-diagonal** — the normal form `⟨1⟩^p ⊕ ⟨−1⟩^q` of Milnor–Husemoller II.4.3,
presented as a single diagonal matrix (the `p`'s and `q`'s interleaved in any order). -/
def IsPMDiagonal {n : ℕ} (N : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ d : Fin n → ℤ, (∀ i, d i = 1 ∨ d i = -1) ∧ N = Matrix.diagonal d

/-- The empty form is `±1`-diagonal. -/
theorem isPMDiagonal_zero : IsPMDiagonal (0 : Matrix (Fin 0) (Fin 0) ℤ) :=
  ⟨fun i => i.elim0, fun i => i.elim0, Subsingleton.elim _ _⟩

/-- A `±1`-diagonal has determinant `±1`. -/
theorem pmDiagonal_det {n : ℕ} (d : Fin n → ℤ) (hd : ∀ i, d i = 1 ∨ d i = -1) :
    (Matrix.diagonal d).det = 1 ∨ (Matrix.diagonal d).det = -1 := by
  have hsq : (∏ i, d i) * (∏ i, d i) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => by rcases hd i with h | h <;> rw [h] <;> ring
  rw [Matrix.det_diagonal]
  exact Int.isUnit_iff.mp (IsUnit.of_mul_eq_one _ hsq)

/-- A `±1`-diagonal is unimodular. -/
theorem IsPMDiagonal.isUnimodular {n : ℕ} {N : Matrix (Fin n) (Fin n) ℤ} (h : IsPMDiagonal N) :
    IsUnimodular N := by
  obtain ⟨d, hd, rfl⟩ := h; exact pmDiagonal_det d hd

/-- A `±1`-diagonal is symmetric. -/
theorem IsPMDiagonal.transpose_eq {n : ℕ} {N : Matrix (Fin n) (Fin n) ℤ} (h : IsPMDiagonal N) :
    Nᵀ = N := by
  obtain ⟨d, -, rfl⟩ := h; exact Matrix.diagonal_transpose d

/-- Casting a `±1`-diagonal to `ℝ` gives a nondegenerate form (the block-additivity side condition). -/
theorem pmDiagonal_radical {n : ℕ} (d : Fin n → ℤ) (hd : ∀ i, d i = 1 ∨ d i = -1) :
    ((Matrix.diagonal d).map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥ := by
  apply nondeg_radical_eq_bot
  · rw [← Matrix.transpose_map, Matrix.diagonal_transpose]
  · refine cast_nondegenerate _ ?_
    rcases pmDiagonal_det d hd with h | h <;> rw [h] <;> norm_num

/-- **Adjoining a unit block preserves `±1`-diagonality**: `⟨ε⟩ ⊕ N` (in any reindexing) is again a
`±1`-diagonal. The `cons` step of the diagonalization induction. -/
theorem isPMDiagonal_cons {q p : ℕ} (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (e : Fin 1 ⊕ Fin q ≃ Fin p)
    {N : Matrix (Fin q) (Fin q) ℤ} (hN : IsPMDiagonal N) :
    IsPMDiagonal (Matrix.reindex e e (Matrix.fromBlocks !![ε] 0 0 N)) := by
  obtain ⟨d, hd, rfl⟩ := hN
  have hblk : (!![ε] : Matrix (Fin 1) (Fin 1) ℤ) = Matrix.diagonal (fun _ => ε) := by
    ext i j; fin_cases i; fin_cases j; simp
  refine ⟨Sum.elim (fun _ => ε) d ∘ e.symm, ?_, ?_⟩
  · intro i
    show (Sum.elim (fun _ => ε) d) (e.symm i) = 1 ∨ (Sum.elim (fun _ => ε) d) (e.symm i) = -1
    rcases e.symm i with k | j
    · simpa using hε
    · simpa using hd j
  · rw [hblk, Matrix.fromBlocks_diagonal, Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]

/-- `σ(diagonal d) = d 0` at rank 1. -/
theorem latticeSig_pmDiagonal_one (d : Fin 1 → ℤ) (hd : ∀ i, d i = 1 ∨ d i = -1) :
    latticeSig (Matrix.diagonal d) = d 0 := by
  have hblk : (Matrix.diagonal d : Matrix (Fin 1) (Fin 1) ℤ) = !![d 0] := by
    ext i j; fin_cases i; fin_cases j; simp
  rw [hblk]; exact latticeSig_unitBlock (hd 0)

/-- **The signature of a `±1`-diagonal is the sum of its entries** — `σ = p − q`. Peels one entry at
a time through `latticeSigOf_fromBlocks` (both blocks nondegenerate by `pmDiagonal_radical`). -/
theorem latticeSig_pmDiagonal : ∀ {n : ℕ} (d : Fin n → ℤ), (∀ i, d i = 1 ∨ d i = -1) →
    latticeSig (Matrix.diagonal d) = ∑ i, d i := by
  intro n
  induction n with
  | zero =>
    intro d _
    rw [show (Matrix.diagonal d : Matrix (Fin 0) (Fin 0) ℤ) = 0 from Subsingleton.elim _ _,
      latticeSig_zero_matrix]
    simp
  | succ n ih =>
    intro d hd
    classical
    set e : Fin 1 ⊕ Fin n ≃ Fin (n + 1) := finSumFinEquiv.trans (finCongr (by omega)) with he
    set d₁ : Fin 1 → ℤ := fun k => d (e (Sum.inl k)) with hd₁
    set d₂ : Fin n → ℤ := fun k => d (e (Sum.inr k)) with hd₂
    have hd₁p : ∀ i, d₁ i = 1 ∨ d₁ i = -1 := fun i => hd _
    have hd₂p : ∀ i, d₂ i = 1 ∨ d₂ i = -1 := fun i => hd _
    have helim : Sum.elim d₁ d₂ = fun s => d (e s) := by
      funext s; rcases s with k | j <;> rfl
    have hkey : (Matrix.diagonal d : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
        = Matrix.reindex e e (Matrix.fromBlocks (Matrix.diagonal d₁) 0 0 (Matrix.diagonal d₂)) := by
      rw [Matrix.fromBlocks_diagonal, Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]
      congr 1
      funext i
      show d i = (Sum.elim d₁ d₂) (e.symm i)
      rw [helim]; simp
    rw [hkey, ← latticeSigOf_fin, latticeSigOf_reindex,
      latticeSigOf_fromBlocks _ _ (pmDiagonal_radical d₁ hd₁p) (pmDiagonal_radical d₂ hd₂p),
      latticeSigOf_fin, latticeSigOf_fin, ih d₂ hd₂p, latticeSig_pmDiagonal_one d₁ hd₁p]
    have hsum : ∑ i, d i = ∑ s : Fin 1 ⊕ Fin n, d (e s) := (Equiv.sum_comp e (fun i => d i)).symm
    rw [hsum, Fintype.sum_sum_type]
    simp [hd₁, hd₂]

/-! ### Uniqueness of the normal form -/

/-- The signature of a `±1`-diagonal determines how many `+1`s it has. -/
theorem pmDiagonal_sum_eq {n : ℕ} (d : Fin n → ℤ) (hd : ∀ i, d i = 1 ∨ d i = -1) :
    ∑ i, d i = 2 * (Finset.univ.filter (fun i => d i = 1)).card - n := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => d i = 1) d]
  have h1 : ∑ i ∈ Finset.univ.filter (fun i => d i = 1), d i
      = (Finset.univ.filter (fun i => d i = 1)).card := by
    rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]
    simp
  have h2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ (d i = 1)), d i
      = -((Finset.univ.filter (fun i => ¬ (d i = 1))).card : ℤ) := by
    have hneg : ∀ i ∈ Finset.univ.filter (fun i => ¬ (d i = 1)), d i = -1 := by
      intro i hi
      rcases hd i with h | h
      · exact absurd h (Finset.mem_filter.mp hi).2
      · exact h
    rw [Finset.sum_congr rfl hneg]
    simp
  have hcard : (Finset.univ.filter (fun i => d i = 1)).card
      + (Finset.univ.filter (fun i => ¬ (d i = 1))).card = n := by
    rw [Finset.filter_card_add_filter_neg_card_eq_card]; simp
  rw [h1, h2]
  omega

/-- **Two `±1`-tuples with equal sums differ by a permutation.** -/
theorem exists_perm_of_pm_sum_eq {n : ℕ} (d d' : Fin n → ℤ)
    (hd : ∀ i, d i = 1 ∨ d i = -1) (hd' : ∀ i, d' i = 1 ∨ d' i = -1)
    (hsum : ∑ i, d i = ∑ i, d' i) : ∃ σ : Fin n ≃ Fin n, ∀ i, d (σ i) = d' i := by
  classical
  have hcards : (Finset.univ.filter (fun i => d i = 1)).card
      = (Finset.univ.filter (fun i => d' i = 1)).card := by
    have h1 := pmDiagonal_sum_eq d hd
    have h2 := pmDiagonal_sum_eq d' hd'
    omega
  have hc1 : Fintype.card {i : Fin n // d' i = 1} = Fintype.card {i : Fin n // d i = 1} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]; exact hcards.symm
  have hc2 : Fintype.card {i : Fin n // ¬ (d' i = 1)} = Fintype.card {i : Fin n // ¬ (d i = 1)} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hc1]
  let e₁ : {i : Fin n // d' i = 1} ≃ {i : Fin n // d i = 1} := Fintype.equivOfCardEq hc1
  let e₂ : {i : Fin n // ¬ (d' i = 1)} ≃ {i : Fin n // ¬ (d i = 1)} := Fintype.equivOfCardEq hc2
  refine ⟨(Equiv.sumCompl (fun i => d' i = 1)).symm.trans
    ((Equiv.sumCongr e₁ e₂).trans (Equiv.sumCompl (fun i => d i = 1))), fun i => ?_⟩
  by_cases hi : d' i = 1
  · rw [Equiv.trans_apply, Equiv.trans_apply,
      Equiv.sumCompl_symm_apply_of_pos (p := fun j => d' j = 1) (a := i) hi]
    rw [Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
    rw [hi]
    exact (e₁ ⟨i, hi⟩).2
  · rw [Equiv.trans_apply, Equiv.trans_apply,
      Equiv.sumCompl_symm_apply_of_neg (p := fun j => d' j = 1) (a := i) hi]
    rw [Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
    have hval := (e₂ ⟨i, hi⟩).2
    rcases hd (e₂ ⟨i, hi⟩ : Fin n) with h | h
    · exact absurd h hval
    · rcases hd' i with h' | h'
      · exact absurd h' hi
      · rw [h, h']

/-- **The `±1`-diagonal normal form is unique up to congruence, given rank and signature.** Two
`±1`-diagonals of the same rank and signature have the same number of `+1`s
(`pmDiagonal_sum_eq`), hence differ by a coordinate permutation (`exists_perm_of_pm_sum_eq`), which
is a congruence (`intCongr_submatrix_self`). -/
theorem IsPMDiagonal.intCongr_of_latticeSig {n : ℕ} {N N' : Matrix (Fin n) (Fin n) ℤ}
    (h : IsPMDiagonal N) (h' : IsPMDiagonal N') (hs : latticeSig N = latticeSig N') :
    IntCongr N N' := by
  obtain ⟨d, hd, rfl⟩ := h
  obtain ⟨d', hd', rfl⟩ := h'
  rw [latticeSig_pmDiagonal d hd, latticeSig_pmDiagonal d' hd'] at hs
  obtain ⟨σ, hσ⟩ := exists_perm_of_pm_sum_eq d d' hd hd' hs
  have hsub : (Matrix.diagonal d' : Matrix (Fin n) (Fin n) ℤ)
      = (Matrix.diagonal d).submatrix σ σ := by
    rw [Matrix.submatrix_diagonal_equiv]
    congr 1; funext i; exact (hσ i).symm
  rw [hsub]
  exact intCongr_submatrix_self _ _

/-! ### Nondegeneracy bookkeeping for unimodular (not necessarily even) forms -/

/-- A symmetric unimodular form casts to a nondegenerate real form. The odd-form analogue of
`IsEvenUnimodular.radical_eq_bot`. -/
theorem unimodular_radical_eq_bot {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hsymm : Mᵀ = M)
    (hunim : IsUnimodular M) : (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥ := by
  apply nondeg_radical_eq_bot
  · rw [← Matrix.transpose_map, hsymm]
  · refine cast_nondegenerate _ ?_
    rcases hunim with h | h <;> rw [h] <;> norm_num

/-- **`|σ| < rank ⟹ indefinite`** for a symmetric unimodular form (no evenness needed). -/
theorem indefinite_of_abs_sig_lt {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hsymm : Mᵀ = M)
    (hunim : IsUnimodular M) (hlt : (latticeSig M).natAbs < n) :
    0 < sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' ∧
    0 < sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' := by
  have hsum := QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
  rw [unimodular_radical_eq_bot M hsymm hunim] at hsum
  simp only [finrank_bot, add_zero, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hsum
  unfold latticeSig at hlt
  omega

/-- **Indefinite ⟹ `|σ| + 2 ≤ rank`** for a symmetric unimodular form. -/
theorem abs_sig_add_two_le_of_indefinite {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hsymm : Mᵀ = M)
    (hunim : IsUnimodular M)
    (hsp : 0 < sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsn : 0 < sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap') :
    (latticeSig M).natAbs + 2 ≤ n := by
  have hsum := QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
  rw [unimodular_radical_eq_bot M hsymm hunim] at hsum
  simp only [finrank_bot, add_zero, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hsum
  unfold latticeSig
  omega

/-! ### The unconditional inductive step: a unit peel with an ODD indefinite residual -/

/-- **Correcting a unit vector against a hyperbolic pair in its complement.** For `x` with
`x·x = ε` and a hyperbolic pair `(v, w)` inside `x^⊥`, the vector `y = x + w` again has `y·y = ε`,
and `z = x − ε·v` is `M`-orthogonal to `y` with `z·z = ε` — an ODD value in `y^⊥`. This is the pure
vector-algebra core of `odd_indefinite_unit_peel`'s even branch. -/
theorem unit_correct_by_hyp_pair {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hsymm : Mᵀ = M)
    (ε : ℤ) (x v w : Fin n → ℤ) (hx : x ⬝ᵥ M *ᵥ x = ε)
    (hxv : x ⬝ᵥ M *ᵥ v = 0) (hxw : x ⬝ᵥ M *ᵥ w = 0)
    (hvv : v ⬝ᵥ M *ᵥ v = 0) (hvw : v ⬝ᵥ M *ᵥ w = 1) (hww : w ⬝ᵥ M *ᵥ w = 0) :
    (x + w) ⬝ᵥ M *ᵥ (x + w) = ε ∧
    (x + w) ⬝ᵥ M *ᵥ (x - ε • v) = 0 ∧
    (x - ε • v) ⬝ᵥ M *ᵥ (x - ε • v) = ε := by
  have hvx : v ⬝ᵥ M *ᵥ x = 0 := by rw [gramPair_comm hsymm]; exact hxv
  have hwx : w ⬝ᵥ M *ᵥ x = 0 := by rw [gramPair_comm hsymm]; exact hxw
  have hwv : w ⬝ᵥ M *ᵥ v = 1 := by rw [gramPair_comm hsymm]; exact hvw
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [gramPair_add_left, gramPair_add_right, gramPair_sub_left, gramPair_sub_right,
      gramPair_smul_left, gramPair_smul_right, hx, hxv, hxw, hvv, hvw, hww, hvx, hwx, hwv] <;>
    ring

/-- **The unconditional inductive step of Milnor–Husemoller II.4.3.**

An ODD INDEFINITE unimodular form `M` of rank `n ≥ 5` is `IntCongr` to `⟨ε⟩ ⊕ M'` where `ε = ±1` and
the residual `M'` is again **odd, indefinite and unimodular**, of rank `n − 1`.

Both residual adjectives are earned, not assumed:

* *indefinite* — `ε` is chosen as the sign of `σ(M)`, so `|σ(M') | = |σ(M) − ε| < n − 1` whenever
  `|σ(M)| ≤ n − 2` (`abs_sig_add_two_le_of_indefinite`), which `indefinite_of_abs_sig_lt` converts
  back into `0 < sigPos ∧ 0 < sigNeg`;
* *odd* — a first peel may strand an EVEN residual (the `⟨1⟩ ⊕ E₈` phenomenon). But an even residual
  is even unimodular AND indefinite, so it carries a hyperbolic pair `(v, w)`
  (`hasIsotropicVector` + `exists_hyperbolic_pair`), which transports into `x^⊥ ⊆ ℤⁿ`
  (`unitResidGram_transport`); replacing `x` by `y = x + w` keeps `y·y = ε` while putting
  `z = x − ε·v` of ODD self-product `ε` into `y^⊥` (`unit_correct_by_hyp_pair`), so the new residual
  cannot be even (`unitResidGram_even_value`).

Iterating this peel is the whole content of II.4.3 above rank 4. -/
theorem odd_indefinite_unit_peel {n : ℕ} (hge : 5 ≤ n) (M : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : Mᵀ = M) (hunim : IsUnimodular M) (i₀ : Fin n) (hodd : ¬ (2 ∣ M i₀ i₀))
    (hsp : 0 < sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsn : 0 < sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap') :
    ∃ (ε : ℤ) (M' : Matrix (Fin (n - 1)) (Fin (n - 1)) ℤ) (e : Fin 1 ⊕ Fin (n - 1) ≃ Fin n),
      (ε = 1 ∨ ε = -1) ∧
      IntCongr M (Matrix.reindex e e (Matrix.fromBlocks !![ε] 0 0 M')) ∧
      M'ᵀ = M' ∧ IsUnimodular M' ∧ (∃ j, ¬ (2 ∣ M' j j)) ∧
      0 < sigPos (M'.map (Int.cast : ℤ → ℝ)).toQuadraticMap' ∧
      0 < sigNeg (M'.map (Int.cast : ℤ → ℝ)).toQuadraticMap' := by
  classical
  have hle := abs_sig_add_two_le_of_indefinite M hsymm hunim hsp hsn
  obtain ⟨ε, hε, hres, x, hx⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (latticeSig M - ε).natAbs < n - 1
      ∧ ∃ x : Fin n → ℤ, x ⬝ᵥ M *ᵥ x = ε := by
    rcases le_or_gt 0 (latticeSig M) with h | h
    · obtain ⟨x, -, hx⟩ := odd_indefinite_represents_one hge M hsymm hunim i₀ hodd hsp hsn
      exact ⟨1, Or.inl rfl, by omega, x, hx⟩
    · obtain ⟨x, -, hx⟩ := odd_indefinite_represents_neg_one hge M hsymm hunim i₀ hodd hsp hsn
      exact ⟨-1, Or.inr rfl, by omega, x, hx⟩
  have hεε : ε * ε = 1 := by rcases hε with h | h <;> rw [h] <;> ring
  have hfr := unitPerp_finrank M x (unit_linearIndependent M x ε hx hεε)
    (unit_isCompl M x ε hx hεε)
  obtain ⟨e, hcong, hunim', hsig'⟩ := unit_split_congr_of_finrank M hsymm hunim ε hε x hx hfr
  have hsymm' : (unitResidGram M x hfr)ᵀ = unitResidGram M x hfr := unitResidGram_symm M hsymm x hfr
  have hlt' : (latticeSig (unitResidGram M x hfr)).natAbs < n - 1 := by rw [hsig']; exact hres
  obtain ⟨hsp', hsn'⟩ := indefinite_of_abs_sig_lt _ hsymm' hunim' hlt'
  by_cases hM'odd : ∃ j, ¬ (2 ∣ (unitResidGram M x hfr) j j)
  · exact ⟨ε, unitResidGram M x hfr, e, hε, hcong, hsymm', hunim', hM'odd, hsp', hsn'⟩
  -- even residual: correct the vector
  push_neg at hM'odd
  have heven' : ∀ j, 2 ∣ (unitResidGram M x hfr) j j := fun j => hM'odd j
  have heu' : IsEvenUnimodular (unitResidGram M x hfr) := ⟨hsymm', hunim', heven'⟩
  obtain ⟨v₀, hv₀p, hv₀iso⟩ := hasIsotropicVector _ heu' hsp' hsn'
  obtain ⟨w₀, -, hvw₀, hw₀⟩ :=
    exists_hyperbolic_pair _ hsymm' heven' v₀ hv₀p hv₀iso hunim'
  set v : Fin n → ℤ := ∑ i, v₀ i • (unitPerpBasis M x hfr i : Fin n → ℤ) with hv
  set w : Fin n → ℤ := ∑ i, w₀ i • (unitPerpBasis M x hfr i : Fin n → ℤ) with hw
  have hxv : x ⬝ᵥ M *ᵥ v = 0 := unitPerp_mem_sum M x hfr v₀
  have hxw : x ⬝ᵥ M *ᵥ w = 0 := unitPerp_mem_sum M x hfr w₀
  have hvv : v ⬝ᵥ M *ᵥ v = 0 := by rw [hv, unitResidGram_transport]; exact hv₀iso
  have hvw : v ⬝ᵥ M *ᵥ w = 1 := by rw [hv, hw, unitResidGram_transport]; exact hvw₀
  have hww : w ⬝ᵥ M *ᵥ w = 0 := by rw [hw, unitResidGram_transport]; exact hw₀
  obtain ⟨hy, hzy, hzz⟩ := unit_correct_by_hyp_pair M hsymm ε x v w hx hxv hxw hvv hvw hww
  set y : Fin n → ℤ := x + w with hydef
  set z : Fin n → ℤ := x - ε • v with hzdef
  have hfr2 := unitPerp_finrank M y (unit_linearIndependent M y ε hy hεε)
    (unit_isCompl M y ε hy hεε)
  obtain ⟨e2, hcong2, hunim2, hsig2⟩ := unit_split_congr_of_finrank M hsymm hunim ε hε y hy hfr2
  have hsymm2 : (unitResidGram M y hfr2)ᵀ = unitResidGram M y hfr2 :=
    unitResidGram_symm M hsymm y hfr2
  have hodd2 : ∃ j, ¬ (2 ∣ (unitResidGram M y hfr2) j j) := by
    by_contra hcon
    push_neg at hcon
    have hdvd := unitResidGram_even_value M hsymm y hfr2 (fun j => hcon j) z hzy
    rw [hzz] at hdvd
    rcases hε with h | h <;> rw [h] at hdvd <;> norm_num at hdvd
  have hlt2 : (latticeSig (unitResidGram M y hfr2)).natAbs < n - 1 := by rw [hsig2]; exact hres
  obtain ⟨hsp2, hsn2⟩ := indefinite_of_abs_sig_lt _ hsymm2 hunim2 hlt2
  exact ⟨ε, unitResidGram M y hfr2, e2, hε, hcong2, hsymm2, hunim2, hodd2, hsp2, hsn2⟩

/-! ### Base cases discharged here: ranks 0, 1 (vacuous) and 2 (constructive) -/

/-- The value of the real quadratic form attached to a real matrix. -/
theorem toQuadraticMap'_apply_real {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    A.toQuadraticMap' x = x ⬝ᵥ A *ᵥ x := by
  simp [Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply']

/-- `0 < sigNeg Q` exhibits an actual vector of negative value. -/
theorem exists_neg_value_of_sigNeg_pos {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (Q : QuadraticForm ℝ V) (h : 0 < sigNeg Q) : ∃ x : V, Q x < 0 := by
  rw [sigNeg] at h
  obtain ⟨W, hW, hWpos⟩ := exists_finrank_eq_sigPos_and_posDef (-Q)
  have hWne : W ≠ ⊥ := by intro hb; rw [hb, finrank_bot] at hW; omega
  obtain ⟨x, hxW, hx0⟩ := W.exists_mem_ne_zero_of_ne_bot hWne
  have hpos : 0 < (-Q) x := by
    have := hWpos ⟨x, hxW⟩ (by simpa [Subtype.ext_iff] using hx0)
    rwa [QuadraticMap.restrict_apply] at this
  exact ⟨x, by simpa using hpos⟩

/-- `0 < sigPos Q` exhibits an actual vector of positive value. -/
theorem exists_pos_value_of_sigPos_pos {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (Q : QuadraticForm ℝ V) (h : 0 < sigPos Q) : ∃ x : V, 0 < Q x := by
  obtain ⟨W, hW, hWpos⟩ := exists_finrank_eq_sigPos_and_posDef Q
  have hWne : W ≠ ⊥ := by intro hb; rw [hb, finrank_bot] at hW; omega
  obtain ⟨x, hxW, hx0⟩ := W.exists_mem_ne_zero_of_ne_bot hWne
  refine ⟨x, ?_⟩
  have := hWpos ⟨x, hxW⟩ (by simpa [Subtype.ext_iff] using hx0)
  rwa [QuadraticMap.restrict_apply] at this

/-- **A rank-2 indefinite unimodular form has `det = −1`.** If `det = +1` then
`a·q(x) = (a x₀ + b x₁)² + x₁² ≥ 0` for every real `x` (with `a = M 0 0`, `b = M 0 1`), so a vector of
negative value forces `a ≤ 0` and a vector of positive value forces `a ≥ 0`; then `a = 0` makes
`det = −b² = 1` impossible. This is the determinant-sign input the rank-2 isotropic construction needs. -/
theorem binary_det_eq_neg_one (M : Matrix (Fin 2) (Fin 2) ℤ) (hsymm : Mᵀ = M)
    (hunim : IsUnimodular M)
    (hsp : 0 < sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsn : 0 < sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap') : M.det = -1 := by
  have hb : M 1 0 = M 0 1 := by
    have h := congrFun (congrFun hsymm 0) 1; simpa [Matrix.transpose_apply] using h
  rcases hunim with h1 | h1
  · exfalso
    have hd : M 0 0 * M 1 1 - M 0 1 * M 0 1 = 1 := by
      rw [Matrix.det_fin_two, hb] at h1; exact h1
    have hval : ∀ x : Fin 2 → ℝ, (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' x
        = (M 0 0 : ℝ) * x 0 ^ 2 + 2 * (M 0 1 : ℝ) * x 0 * x 1 + (M 1 1 : ℝ) * x 1 ^ 2 := by
      intro x
      rw [toQuadraticMap'_apply_real]
      simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.map_apply, hb]
      ring
    have hnn : ∀ x : Fin 2 → ℝ, 0 ≤ (M 0 0 : ℝ) * (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' x := by
      intro x
      have hkey : (M 0 0 : ℝ) * (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' x
          = ((M 0 0 : ℝ) * x 0 + (M 0 1 : ℝ) * x 1) ^ 2
            + ((M 0 0 * M 1 1 - M 0 1 * M 0 1 : ℤ) : ℝ) * x 1 ^ 2 := by
        rw [hval]; push_cast; ring
      rw [hkey, hd]
      positivity
    obtain ⟨x, hx⟩ := exists_neg_value_of_sigNeg_pos _ hsn
    obtain ⟨y, hy⟩ := exists_pos_value_of_sigPos_pos _ hsp
    have hale : (M 0 0 : ℝ) ≤ 0 := by nlinarith [hnn x]
    have hage : (0 : ℝ) ≤ (M 0 0 : ℝ) := by nlinarith [hnn y]
    have ha0 : M 0 0 = 0 := by exact_mod_cast le_antisymm hale hage
    rw [ha0] at hd
    nlinarith [sq_nonneg (M 0 1), hd]
  · exact h1

/-- **A rank-2 symmetric form of determinant `−1` has an explicit nonzero isotropic vector.** With
`a = M 0 0`, `b = M 0 1`: if `a = 0` take `(1, 0)`; otherwise take `(1 − b, a)`, whose value is
`a·(1 − (b² − ac)) = 0` since `b² − ac = −det = 1`. Fully constructive — no local-global input. -/
theorem binary_isotropic_of_det_neg_one (M : Matrix (Fin 2) (Fin 2) ℤ) (hsymm : Mᵀ = M)
    (hdet : M.det = -1) : ∃ v : Fin 2 → ℤ, v ≠ 0 ∧ v ⬝ᵥ M *ᵥ v = 0 := by
  have hb : M 1 0 = M 0 1 := by
    have h := congrFun (congrFun hsymm 0) 1; simpa [Matrix.transpose_apply] using h
  have hd : M 0 0 * M 1 1 - M 0 1 * M 0 1 = -1 := by
    rw [Matrix.det_fin_two, hb] at hdet; exact hdet
  by_cases ha : M 0 0 = 0
  · refine ⟨![1, 0], ?_, ?_⟩
    · intro h; have := congrFun h 0; simp at this
    · simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons]
      rw [ha]; ring
  · refine ⟨![1 - M 0 1, M 0 0], ?_, ?_⟩
    · intro h
      have h1 := congrFun h 1
      simp only [Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply] at h1
      exact ha h1
    · simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, hb]
      linear_combination (M 0 0) * hd

/-- A rank-1 unimodular form is `±1`-diagonal. -/
theorem isPMDiagonal_of_rank_one (M : Matrix (Fin 1) (Fin 1) ℤ) (h : IsUnimodular M) :
    IsPMDiagonal M := by
  rw [IsUnimodular, Matrix.det_fin_one] at h
  refine ⟨fun _ => M 0 0, fun i => h, ?_⟩
  ext i j; fin_cases i; fin_cases j; simp

/-- **Rank ≤ 1 cannot be indefinite** — the vacuous base cases. -/
theorem not_indefinite_of_rank_le_one {n : ℕ} (hn : n ≤ 1) (M : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : Mᵀ = M) (hunim : IsUnimodular M)
    (hsp : 0 < sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsn : 0 < sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap') : False := by
  have hsum := QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
  rw [unimodular_radical_eq_bot M hsymm hunim] at hsum
  simp only [finrank_bot, add_zero, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hsum
  omega

/-- **The rank-2 base case, DISCHARGED.** An odd indefinite unimodular binary form is `±1`-diagonal
(necessarily `⟨1⟩ ⊕ ⟨−1⟩`). Chain: `binary_det_eq_neg_one` → `binary_isotropic_of_det_neg_one` →
`odd_unimodular_represents_one_of_isotropic` (the rank-free entry point) → `unit_split_congr`, whose
rank-1 residual is unimodular hence `⟨±1⟩`. -/
theorem oddBinary_pmDiagonal (M : Matrix (Fin 2) (Fin 2) ℤ) (hsymm : Mᵀ = M)
    (hunim : IsUnimodular M) (hodd : ∃ i, ¬ (2 ∣ M i i))
    (hsp : 0 < sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsn : 0 < sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap') :
    ∃ N, IsPMDiagonal N ∧ IntCongr M N := by
  obtain ⟨i₀, hi₀⟩ := hodd
  obtain ⟨v, hvne, hviso⟩ :=
    binary_isotropic_of_det_neg_one M hsymm (binary_det_eq_neg_one M hsymm hunim hsp hsn)
  obtain ⟨x, -, hx⟩ := odd_unimodular_represents_one_of_isotropic M hsymm hunim i₀ hi₀ v hvne hviso
  obtain ⟨M', e, hcong, -, hunim', -⟩ := unit_split_congr M hsymm hunim 1 (Or.inl rfl) x hx
  exact ⟨_, isPMDiagonal_cons 1 (Or.inl rfl) e (isPMDiagonal_of_rank_one M' hunim'), hcong⟩

/-! ### The remaining gap: ranks 3 and 4

`odd_indefinite_unit_peel` drives the induction from any rank down to rank 4, where
`odd_indefinite_represents_one` runs out (it consumes Meyer/Hasse–Minkowski
`weakIsotropic_of_five_le`, valid only at rank `≥ 5`). The small-rank residue is exposed as a `Prop`
interface, in the project's usual style (`HasWeakIsotropicVectorHyp`, `StableNegRank16`).

**What discharging it takes (do not mistake this for bookkeeping).** By the same
isotropic-vector-then-unit-vector chain that `odd_indefinite_represents_one` runs, each small rank
reduces to: *an odd indefinite unimodular form of that rank has a nonzero integer isotropic vector.*

* **Ranks 0 and 1** are vacuous (`not_indefinite_of_rank_le_one`) — DISCHARGED above.
* **Rank 2** is elementary and constructive (`oddBinary_pmDiagonal`) — DISCHARGED above:
  `det = ac − b² = −1` makes `(1 − b, a)` isotropic (`a·q(1−b, a) = a·(1 − (b² − ac)) = 0`), or
  `(1, 0)` when `a = 0`; the determinant sign itself comes from indefiniteness
  (`binary_det_eq_neg_one`), since `det = +1` makes `a·q = (ax+by)² + y²` semidefinite.
* **Ranks 3 and 4 REMAIN.** They are a genuine Hasse–Minkowski discharge, of the same shape as the ~600-line
  `RokhlinHMRankFour`, but NOT reducible to it: that file is specific to EVEN unimodular rank-4 forms,
  and specifically to the **square-discriminant** branch (it first proves `det = +1` from evenness,
  `det_eq_one_of_evenUnimodular_four`, in order to reach
  `quaternary_sqdisc_solvable_of_local_no_two`). An odd rank-4 indefinite unimodular form has
  `σ ∈ {0, ±2}`, i.e. `det ∈ {+1, −1}`, and the `σ = ±2` (`det = −1`, non-square-discriminant) shapes
  fall outside that machinery; rank 3 needs the ternary (Legendre) statement. Both are reachable from
  banked pieces — `isotropic_padicInt_of_unit_det` (odd `p`, rank `≥ 3`) plus the reciprocity step
  `hilbertPrime_two_eq_one_of_real_odd` that pins the place `2` — but each is a build, not a rewrite. -/

/-- **The rank-3/4 base-case interface — the ONLY residue (OPEN).** An odd indefinite unimodular form
of rank `3` or `4` is congruent to a `±1`-diagonal. Ranks `≤ 2` are discharged above
(`not_indefinite_of_rank_le_one`, `oddBinary_pmDiagonal`); see the section comment for exactly what
discharging ranks 3 and 4 costs. -/
def OddRank34Diagonalizable : Prop :=
  ∀ (n : ℕ), 3 ≤ n → n ≤ 4 → ∀ (M : Matrix (Fin n) (Fin n) ℤ), Mᵀ = M → IsUnimodular M →
    (∃ i, ¬ (2 ∣ M i i)) →
    0 < sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' →
    0 < sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' →
    ∃ N, IsPMDiagonal N ∧ IntCongr M N

/-- **Milnor–Husemoller II.4.3** (relative to the rank-3/4 base cases): an odd indefinite
unimodular integer form is congruent to `⟨1⟩^p ⊕ ⟨−1⟩^q`. Strong induction on rank: peel a unit block
with an odd indefinite residual (`odd_indefinite_unit_peel`, UNCONDITIONAL) while the rank exceeds 4,
and re-block through `IntCongr.block_left` + `isPMDiagonal_cons`. Ranks `0, 1` are vacuous and rank
`2` is discharged constructively, so `hsmall` carries only ranks 3 and 4. -/
theorem odd_indefinite_pmDiagonal (hsmall : OddRank34Diagonalizable) :
    ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ), Mᵀ = M → IsUnimodular M →
      (∃ i, ¬ (2 ∣ M i i)) →
      0 < sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' →
      0 < sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' →
      ∃ N, IsPMDiagonal N ∧ IntCongr M N := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro M hsymm hunim hodd hsp hsn
    rcases Nat.lt_or_ge n 5 with hlt | hge
    · rcases Nat.lt_or_ge n 2 with hlt1 | hge2
      · exact (not_indefinite_of_rank_le_one (by omega) M hsymm hunim hsp hsn).elim
      rcases Nat.eq_or_lt_of_le hge2 with heq | hgt2
      · subst heq; exact oddBinary_pmDiagonal M hsymm hunim hodd hsp hsn
      · exact hsmall n (by omega) (by omega) M hsymm hunim hodd hsp hsn
    · obtain ⟨i₀, hi₀⟩ := hodd
      obtain ⟨ε, M', e, hε, hcong, hsymm', hunim', hodd', hsp', hsn'⟩ :=
        odd_indefinite_unit_peel hge M hsymm hunim i₀ hi₀ hsp hsn
      obtain ⟨N, hN, hcongN⟩ := IH (n - 1) (by omega) M' hsymm' hunim' hodd' hsp' hsn'
      exact ⟨_, isPMDiagonal_cons ε hε e hN, hcong.trans (IntCongr.block_left e _ hcongN)⟩

/-- **Odd indefinite unimodular forms are classified by rank and signature** (relative to the
rank-`≤ 4` base cases) — the form of II.4.3 the `StableNegRank16` assembly consumes: both `M ⊕ ⟨1⟩`
and `N ⊕ ⟨1⟩` reduce to the same `⟨1⟩^p ⊕ ⟨−1⟩^q`. Combines `odd_indefinite_pmDiagonal` with the
uniqueness of the normal form (`IsPMDiagonal.intCongr_of_latticeSig`). -/
theorem odd_indefinite_intCongr (hsmall : OddRank34Diagonalizable) {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) ℤ)
    (hsymmM : Mᵀ = M) (hunimM : IsUnimodular M) (hoddM : ∃ i, ¬ (2 ∣ M i i))
    (hspM : 0 < sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsnM : 0 < sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsymmN : Nᵀ = N) (hunimN : IsUnimodular N) (hoddN : ∃ i, ¬ (2 ∣ N i i))
    (hspN : 0 < sigPos (N.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsnN : 0 < sigNeg (N.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsig : latticeSig M = latticeSig N) : IntCongr M N := by
  obtain ⟨D, hD, hMD⟩ := odd_indefinite_pmDiagonal hsmall M hsymmM hunimM hoddM hspM hsnM
  obtain ⟨D', hD', hND'⟩ := odd_indefinite_pmDiagonal hsmall N hsymmN hunimN hoddN hspN hsnN
  have hsigD : latticeSig D = latticeSig D' := by
    rw [hMD.latticeSig, hND'.latticeSig, hsig]
  exact (hMD.trans (hD.intCongr_of_latticeSig hD' hsigD)).trans hND'.symm

end SKEFTHawking
