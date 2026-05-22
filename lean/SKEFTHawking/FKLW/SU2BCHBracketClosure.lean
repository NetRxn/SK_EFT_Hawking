/-
SK_EFT_Hawking Phase 6p Wave 2c.4a-R4.2.d.4.3.d.2-Wedge-D / Phase 5 Step 13
Path (i) FINAL: substantive discharge of `CartanFinalStep_SU2_v4`.

## Mathematical content

For a closed subgroup `H ≤ SU(2)` and two ℝ-linearly-independent
`X₁, X₂ ∈ 𝔰𝔲(2) := tracelessSkewHermitian (Fin 2)` such that
`exp(ℝ•X₁) ⊆ H` and `exp(ℝ•X₂) ⊆ H` (in the pointwise sense from
`CartanFinalStep_SU2_v4`), we prove `H = ⊤ = SU(2)`.

The four steps:

  1. **BCH bracket closure (Trotter limit).** From
     `exp(ℝ•X₁), exp(ℝ•X₂) ⊆ H` and `H` closed under multiplication and
     topologically closed, we derive `exp(ℝ•[X₁, X₂]) ⊆ H` where
     `[X₁, X₂] := X₁ · X₂ - X₂ · X₁` is the matrix Lie bracket.

     The argument is the standard Trotter limit:
     `exp(t · [X₁, X₂]) = lim_{n→∞} (P_n)^n` where
     `P_n := exp(-s_n · X₁) · exp(-s_n · X₂) · exp(s_n · X₁) · exp(s_n · X₂)`
     and `s_n := √(t / n)`. Each `P_n ∈ H` by group-multiplicative closure
     (each exp factor is in H by hypothesis); each `(P_n)^n ∈ H` by power
     closure; H is topologically closed, so the limit `exp(t · [X₁, X₂]) ∈ H`.

     The per-step bound `‖P_n - exp(s_n² · [X₁, X₂])‖ ≤ 320 · δ³` is
     supplied by `SKEFTHawking.MatrixBCHCubic.bch_order_2_cubic_thm`.

  2. **Spanning (already shipped).** `{X₁, X₂, [X₁, X₂]}` is a basis of
     `𝔰𝔲(2)` whenever `X₁, X₂` are ℝ-LI; supplied by
     `SU2LieAlgebra.tracelessSkewHermitian_X_Y_bracket_spans`.

  3. **Local diffeomorphism `𝔰𝔲(2) → SU(2)` near 1 (already shipped).**
     `OneParameterSubgroupSU2.SU2_nhd_one_covered_by_exp_ts` gives a nbhd
     `W` of `1` in `Matrix _ _ ℂ` such that every `h ∈ W ∩ SU(2)` admits
     `Y ∈ 𝔰𝔲(2) ∩ source` with `expAmbient Y = h`.

  4. **Open subgroup containing 1 in interior ⟹ ⊤ (already shipped).**
     `OneParameterSubgroupSU2.SU2_subgroup_eq_top_of_one_mem_interior`.

The composition is THIS module's headline `CartanFinalStep_SU2_v4_holds`.
Combined with the shipped `H_Fib_v4_witness_unconditional`
(`OneParameterSubgroupSU2.lean §80`), `H_Fib_v4_witness_unconditional`-fed
F.21 chain becomes **fully unconditional**, closing the Phase 6p Wave
2c.4a-R4.2.d arc.

## Pipeline invariant compliance

- Invariant #10 (no `maxHeartbeats` in proofs): RESPECTED. Sub-lemmas
  decomposed to `have`-blocks ≤ 12 terms each.
- Invariant #15 (no new project-local axioms): RESPECTED. All bounds
  composed from shipped `MatrixBCHCubic` + standard `NormedSpace`
  topology. Standard kernel only (`propext`, `Classical.choice`,
  `Quot.sound`).
- ADR-006 note: prior session's "NOT Trotter" constraint was an invented
  rule (caught by ADR-006 retrospective). Trotter via the
  cubic-remainder bound `bch_order_2_cubic_thm` is the canonical path.

## What this module exports

  *Generic substrate:*
  - `grpComm a b := a · b · a⁻¹ · b⁻¹` (group commutator).
  - `bracketMatrix X Y := X · Y - Y · X` (matrix Lie bracket).

  *Bracket-closure substrate (Step 1):*
  - `fourfoldComm s X Y` — explicit four-fold matrix commutator
    `exp(-s X) · exp(-s Y) · exp(s X) · exp(s Y)`.
  - `fourfoldComm_mem_H` — when `exp(ℝ • X), exp(ℝ • Y) ⊆ H`,
    `∀ s, ∃ M ∈ H, M.val = fourfoldComm s X Y`.
  - `fourfoldComm_norm_le` — cubic bound on `‖fourfoldComm s X Y -
    expAmbient(s² · [X, Y])‖`.
  - `trotter_commutator_limit` — n-th power of `fourfoldComm √(t/n)`
    converges to `expAmbient(t · [X, Y])`.
  - `exp_bracket_mem_H` — main Step 1 theorem.

  *Final composition:*
  - `CartanFinalStep_SU2_v4_holds : CartanFinalStep_SU2_v4` — the
    headline discharge.
  - `fibonacci_density_F21_unconditional` — the final culmination, F.21
    Fibonacci density in SU(3)₂ ↪ SU(2) with zero remaining tracked Props.
-/

import SKEFTHawking.MatrixBCHCubic
import SKEFTHawking.FKLW.CartanSubstrate
import SKEFTHawking.FKLW.OneParameterSubgroupSU2

set_option autoImplicit false

namespace SKEFTHawking.FKLW

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## §1. Generic substrate

Reusable definitions: group commutator, matrix Lie bracket. -/

/-- Group commutator `a · b · a⁻¹ · b⁻¹`. -/
def grpComm {G : Type*} [Group G] (a b : G) : G := a * b * a⁻¹ * b⁻¹

/-- Matrix Lie bracket `X · Y - Y · X`. -/
noncomputable def bracketMatrix {d : ℕ} (X Y : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ := X * Y - Y * X

/-! ## §2. Four-fold matrix commutator and its BCH approximation

For `X, Y ∈ tracelessSkewHermitian (Fin 2)` and `s : ℝ`, the four-fold
matrix commutator `exp(-s X) · exp(-s Y) · exp(s X) · exp(s Y)`
approximates `exp(s² · [X, Y])` to cubic order in `s`. -/

/-- Four-fold matrix commutator of `exp(s X)` and `exp(s Y)`. -/
noncomputable def fourfoldComm (s : ℝ) (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  SU2MatrixExp.expAmbient (((-s : ℝ) : ℂ) • X) *
    SU2MatrixExp.expAmbient (((-s : ℝ) : ℂ) • Y) *
    SU2MatrixExp.expAmbient (((s : ℝ) : ℂ) • X) *
    SU2MatrixExp.expAmbient (((s : ℝ) : ℂ) • Y)

/-! ### §2.1. Group-closure of `fourfoldComm` under the v4 hypothesis

When `H ≤ SU(2)` contains `exp(ℝ•X)` and `exp(ℝ•Y)` (in the pointwise
sense from `CartanFinalStep_SU2_v4`), the four-fold matrix commutator
`fourfoldComm s X Y` is realized as the matrix value of some `M ∈ H`. -/

/-- `fourfoldComm s X Y` ∈ H.val when `exp(ℝ•X), exp(ℝ•Y) ⊆ H`. -/
lemma fourfoldComm_mem_H_val
    (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    {X Y : Matrix (Fin 2) (Fin 2) ℂ}
    (h_expX : ∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
        M ∈ H ∧ M.val = SU2MatrixExp.expAmbient (((t : ℝ) : ℂ) • X))
    (h_expY : ∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
        M ∈ H ∧ M.val = SU2MatrixExp.expAmbient (((t : ℝ) : ℂ) • Y))
    (s : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
      M ∈ H ∧ M.val = fourfoldComm s X Y := by
  obtain ⟨A, hA_mem, hA_val⟩ := h_expX (-s)
  obtain ⟨B, hB_mem, hB_val⟩ := h_expY (-s)
  obtain ⟨C, hC_mem, hC_val⟩ := h_expX s
  obtain ⟨D, hD_mem, hD_val⟩ := h_expY s
  refine ⟨A * B * C * D, ?_, ?_⟩
  · exact H.mul_mem (H.mul_mem (H.mul_mem hA_mem hB_mem) hC_mem) hD_mem
  · show (A * B * C * D : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val = fourfoldComm s X Y
    have h_val_mul : ∀ (P Q : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)),
        (P * Q : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val = P.val * Q.val := fun _ _ => rfl
    rw [h_val_mul, h_val_mul, h_val_mul, hA_val, hB_val, hC_val, hD_val]
    rfl

/-! ### §2.2. BCH per-step bound: `fourfoldComm` ↔ `expAmbient(s² • [X, Y])`

Apply `MatrixBCHCubic.bch_order_2_cubic_thm` with the substitution
`F := s • i • X`, `G := s • i • Y`. Then:
  - `Complex.I • F = Complex.I • (s • i • X) = -s • X`,
    so `exp(i·F) = exp(-s·X)`.
  - Similarly for the other 4 factors of the 4-fold commutator.
  - `-⁅F, G⁆ = -(s·i)²·[X,Y] = s²·[X,Y]`.

The cubic bound `320·δ³` with `δ = s·max(‖X‖, ‖Y‖)` follows directly. -/

/-- Algebraic identity: `fourfoldComm s X Y` equals the BCH 4-fold form. -/
private lemma fourfoldComm_eq_bch_form
    (s : ℝ) (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    fourfoldComm s X Y =
      NormedSpace.exp (Complex.I • ((s : ℂ) • Complex.I • X)) *
        NormedSpace.exp (Complex.I • ((s : ℂ) • Complex.I • Y)) *
        NormedSpace.exp (-(Complex.I • ((s : ℂ) • Complex.I • X))) *
        NormedSpace.exp (-(Complex.I • ((s : ℂ) • Complex.I • Y))) := by
  unfold fourfoldComm SU2MatrixExp.expAmbient
  -- For each factor, prove the smul argument equals the BCH form.
  -- Key: Complex.I • ((s : ℂ) • Complex.I • Z) = (Complex.I * s * Complex.I) • Z = -s • Z
  have h_neg (Z : Matrix (Fin 2) (Fin 2) ℂ) :
      (((-s : ℝ) : ℂ) • Z : Matrix (Fin 2) (Fin 2) ℂ)
      = Complex.I • ((s : ℂ) • Complex.I • Z) := by
    rw [smul_smul, smul_smul]
    congr 1
    have : Complex.I * (s : ℂ) * Complex.I = (s : ℂ) * (Complex.I * Complex.I) := by ring
    rw [this, Complex.I_mul_I]
    push_cast; ring
  have h_pos (Z : Matrix (Fin 2) (Fin 2) ℂ) :
      (((s : ℝ) : ℂ) • Z : Matrix (Fin 2) (Fin 2) ℂ)
      = -(Complex.I • ((s : ℂ) • Complex.I • Z)) := by
    rw [show -(Complex.I • ((s : ℂ) • Complex.I • Z))
          = ((-(Complex.I * (s : ℂ) * Complex.I)) : ℂ) • Z from by
      rw [smul_smul, smul_smul, neg_smul]]
    congr 1
    have : Complex.I * (s : ℂ) * Complex.I = (s : ℂ) * (Complex.I * Complex.I) := by ring
    rw [this, Complex.I_mul_I]
    ring
  rw [h_neg X, h_neg Y, h_pos X, h_pos Y]

/-- The Mathlib Lie bracket `⁅F, G⁆` of the substituted F, G expands to
`-(s²) • (X·Y - Y·X)`. So `-⁅F, G⁆ = s²·(X·Y - Y·X)`. -/
private lemma bch_substituted_neg_lie_bracket_eq
    (s : ℝ) (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    -⁅((s : ℂ) • Complex.I • X), ((s : ℂ) • Complex.I • Y)⁆
    = ((s^2 : ℝ) : ℂ) • (X * Y - Y * X) := by
  show -((((s : ℂ) • Complex.I • X) * ((s : ℂ) • Complex.I • Y)) -
        (((s : ℂ) • Complex.I • Y) * ((s : ℂ) • Complex.I • X)))
      = ((s^2 : ℝ) : ℂ) • (X * Y - Y * X)
  have h_smul_mul_smul : ∀ (a b : ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ),
      (a • A) * (b • B) = (a * b) • (A * B) := by
    intros a b A B
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [h_smul_mul_smul, h_smul_mul_smul]
  rw [h_smul_mul_smul, h_smul_mul_smul]
  rw [Complex.I_mul_I]
  -- After Complex.I_mul_I: smul args become (↑s * ↑s) • -1 • (X·Y) etc.
  rw [smul_smul, smul_smul]
  -- Goal: -((↑s * ↑s) * -1 • (X·Y) - (↑s * ↑s) * -1 • (Y·X)) = ↑(s^2) • (X·Y - Y·X)
  rw [show (s : ℂ) * (s : ℂ) * (-1 : ℂ) = -((s^2 : ℝ) : ℂ) from by push_cast; ring]
  rw [smul_sub]
  module

/-- **Per-step bound**: `‖fourfoldComm s X Y - expAmbient(s² • [X,Y])‖ ≤ 320·(s·M)³`
when `s · M ≤ 1` and `‖X‖, ‖Y‖ ≤ M`. -/
lemma fourfoldComm_norm_le
    {X Y : Matrix (Fin 2) (Fin 2) ℂ}
    {s M : ℝ} (hs_nn : 0 ≤ s) (hM_nn : 0 ≤ M)
    (hsM_le_one : s * M ≤ 1)
    (hX_le : ‖X‖ ≤ M) (hY_le : ‖Y‖ ≤ M) :
    ‖fourfoldComm s X Y -
        SU2MatrixExp.expAmbient (((s^2 : ℝ) : ℂ) • (X * Y - Y * X))‖
    ≤ 320 * (s * M)^3 := by
  set F : Matrix (Fin 2) (Fin 2) ℂ := (s : ℂ) • Complex.I • X with hF_def
  set G : Matrix (Fin 2) (Fin 2) ℂ := (s : ℂ) • Complex.I • Y with hG_def
  set δ : ℝ := s * M with hδ_def
  have hδ_nn : 0 ≤ δ := mul_nonneg hs_nn hM_nn
  have hF_norm_eq : ‖F‖ = s * ‖X‖ := by
    rw [hF_def, norm_smul, norm_smul]
    rw [Complex.norm_real, Complex.norm_I, one_mul]
    rw [show ‖(s : ℝ)‖ = s from Real.norm_of_nonneg hs_nn]
  have hG_norm_eq : ‖G‖ = s * ‖Y‖ := by
    rw [hG_def, norm_smul, norm_smul]
    rw [Complex.norm_real, Complex.norm_I, one_mul]
    rw [show ‖(s : ℝ)‖ = s from Real.norm_of_nonneg hs_nn]
  have hF_le : ‖F‖ ≤ δ := by
    rw [hF_norm_eq, hδ_def]
    exact mul_le_mul_of_nonneg_left hX_le hs_nn
  have hG_le : ‖G‖ ≤ δ := by
    rw [hG_norm_eq, hδ_def]
    exact mul_le_mul_of_nonneg_left hY_le hs_nn
  -- Apply bch_order_2_cubic_thm at F, G, δ.
  have h_bch :=
    SKEFTHawking.MatrixBCHCubic.bch_order_2_cubic_thm δ hδ_nn hsM_le_one F G hF_le hG_le
  -- Translate the result to fourfoldComm + exp(s²•[X,Y]) form.
  rw [fourfoldComm_eq_bch_form, ← hF_def, ← hG_def]
  rw [show SU2MatrixExp.expAmbient (((s^2 : ℝ) : ℂ) • (X * Y - Y * X))
        = NormedSpace.exp (-⁅F, G⁆) from by
    unfold SU2MatrixExp.expAmbient
    rw [hF_def, hG_def, bch_substituted_neg_lie_bracket_eq]]
  exact h_bch

/-! ## §3. Step 1 — BCH bracket closure (Trotter limit)

The substantive Trotter argument: for a closed `H ≤ SU(2)` containing
`exp(ℝ•X)` and `exp(ℝ•Y)`, we have `exp(ℝ•[X,Y]) ⊆ H`.

**Proof strategy.** Per the `bch_order_2_cubic_thm` per-step bound + the
n-th-power telescoping + closure of H. Detailed proof deferred to next
session — substrate scaffolding is in this section, ready for the
explicit ε–δ + sequential closure argument.

The Mathematical statement is unconditionally true (classical Lie theory
result, "closed subgroup theorem implies Lie subalgebra closed under
brackets"). The Lean discharge requires the standard matrix Trotter
formula, which is not in Mathlib4 v4.29.0 and is shipped here as
**first-formalization-quality** substrate. -/

/-! ### §3.0. Trotter limit substrate (sub-lemma decomposition)

The matrix Trotter convergence is decomposed into four explicit sub-lemmas
+ a final composition. All bodies are now shipped kernel-only via the
non-commutative telescoping identity + linftyOp absolute SU(2) bound.

**Architecture.** The per-step BCH cubic bound (§2.2 `fourfoldComm_norm_le`)
gives `‖P_n - Q_n‖_linfty = O(n^{-3/2})` where `P_n := fourfoldComm √(t/n) X Y`
and `Q_n := expAmbient((t/n) • [X,Y])`. To conclude `(P_n)^n → exp(t•[X,Y])`,
the n-th-power telescoping must be carried out in a sub-multiplicative norm
where unitary matrices have norm = 1 — namely the L²-operator (spectral)
norm, available in Mathlib via `Matrix.instL2OpNormedRing` +
`CStarRing.norm_of_mem_unitary` (in `Mathlib.Analysis.CStarAlgebra.Matrix`).

Sub-lemma roadmap:
1. `linfty_le_l2_norm_two_dim` + `l2_le_linfty_norm_two_dim`: norm
   equivalence on `Matrix (Fin 2) (Fin 2) ℂ` with explicit `√2` constants
   (~50-100 LoC; standard but not in Mathlib v4.29.0).
2. `pow_l2_norm_sub_bound`: `‖A^n - B^n‖_l2 ≤ n · max(‖A‖_l2, ‖B‖_l2)^{n-1} · ‖A-B‖_l2`
   — standard telescoping in any normed ring (~30 LoC).
3. `q_n_pow_eq_exp_t`: `(expAmbient((t/n) • Z))^n = expAmbient(t • Z)` —
   scalar-power identity for matrix exp (~20 LoC).
4. `trotter_sequence_tendsto`: the assembly. With sub-lemmas 1-3 +
   `fourfoldComm_norm_le`, prove `(fourfoldComm √(t/n) X Y)^n →
   expAmbient(t • [X,Y])` in matrix topology (~50-100 LoC).
5. Final: apply `IsClosed.mem_of_tendsto` + `Subgroup.pow_mem` /
   `fourfoldComm_mem_H_val`. -/

/-! ### §3.1a. Non-commutative telescoping sum identity (Mathlib-PR-quality)

The Trotter-friendly form `‖A^n - B^n‖ ≤ n · K_A · K_B · ‖A - B‖` requires
the explicit telescoping sum identity:
  `A^n - B^n = Σ_{k=0}^{n-1} A^k · (A - B) · B^(n-1-k)`
provable by induction on `n` via
`A^{n+1} - B^{n+1} = A · (A^n - B^n) + (A - B) · B^n` and re-indexing.

This gives the linftyOp Trotter bound `4n · ‖P_n - Q_n‖_∞` for SU(2)
elements (K_A = K_B = 2), avoiding the l2-op-norm detour. -/

/-- **Non-commutative telescoping sum identity** in any `Ring`:
`A^n - B^n = Σ_{k=0}^{n-1} A^k · (A - B) · B^(n-1-k)`.

**Mathlib upstream PR target.** Provable by induction via the recursion
`A^{n+1} - B^{n+1} = A·(A^n - B^n) + (A - B)·B^n` and re-indexing the sum. -/
private lemma pow_sub_pow_telescoping_eq
    {𝔸 : Type*} [Ring 𝔸] (A B : 𝔸) (n : ℕ) :
    A^n - B^n = ∑ k ∈ Finset.range n, A^k * (A - B) * B^(n - 1 - k) := by
  induction n with
  | zero => simp
  | succ k ih =>
    -- A^(k+1) - B^(k+1) = A·(A^k - B^k) + (A - B)·B^k
    have h_split : A^(k+1) - B^(k+1) = A * (A^k - B^k) + (A - B) * B^k := by
      rw [pow_succ', pow_succ']; noncomm_ring
    rw [h_split, ih, Finset.mul_sum]
    -- LHS: ∑ i in range k, A·(A^i·(A-B)·B^(k-1-i)) + (A-B)·B^k
    -- RHS: ∑ k_1 in range (k+1), A^k_1·(A-B)·B^(k+1-1-k_1)
    have h_sub_succ : k + 1 - 1 = k := by omega
    simp only [h_sub_succ]
    -- Now RHS: ∑ k_1 in range (k+1), A^k_1·(A-B)·B^(k-k_1)
    -- Split RHS using sum_range_succ' (extracts the k_1=0 term out)
    rw [Finset.sum_range_succ' (fun k_1 => A^k_1 * (A - B) * B^(k - k_1)) k]
    -- After: RHS = (∑ k_1 in range k, A^(k_1+1)·(A-B)·B^(k-(k_1+1))) + A^0·(A-B)·B^(k-0)
    simp only [pow_zero, one_mul, Nat.sub_zero]
    -- Goal: ∑ + (A-B)·B^k = ∑' + (A-B)·B^k, just need sums equal
    congr 1
    apply Finset.sum_congr rfl
    intros j hj
    have hj_lt : j < k := Finset.mem_range.mp hj
    have h_sub_j : k - (j + 1) = k - 1 - j := by omega
    rw [h_sub_j, pow_succ']
    noncomm_ring

/-- **Telescoping bound with absolute power bounds**: in any `NormedRing`,
if `‖A^k‖ ≤ K_A` and `‖B^k‖ ≤ K_B` for all `k < n`, then
`‖A^n - B^n‖ ≤ n · K_A · K_B · ‖A - B‖`.

This is the Trotter-friendly form: avoids the recursive `max(‖A‖,‖B‖)^(n-1)`
blowup that `pow_norm_sub_bound` incurs. Composes
`pow_sub_pow_telescoping_eq` with triangle inequality + sub-multiplicativity.

**Mathlib upstream PR target.** -/
private lemma pow_sub_pow_norm_le_of_pow_bounds
    {𝔸 : Type*} [NormedRing 𝔸] (A B : 𝔸) (n : ℕ)
    {K_A K_B : ℝ} (hK_A_nn : 0 ≤ K_A) (_hK_B_nn : 0 ≤ K_B)
    (hA_pow : ∀ k, k < n → ‖A^k‖ ≤ K_A)
    (hB_pow : ∀ k, k < n → ‖B^k‖ ≤ K_B) :
    ‖A^n - B^n‖ ≤ n * K_A * K_B * ‖A - B‖ := by
  rw [pow_sub_pow_telescoping_eq]
  have h_term_le : ∀ k ∈ Finset.range n,
      ‖A^k * (A - B) * B^(n - 1 - k)‖ ≤ K_A * K_B * ‖A - B‖ := by
    intros k hk
    have hk_lt_n : k < n := Finset.mem_range.mp hk
    have hAk_le : ‖A^k‖ ≤ K_A := hA_pow k hk_lt_n
    have h_sub_lt : n - 1 - k < n := by omega
    have hBk_le : ‖B^(n - 1 - k)‖ ≤ K_B := hB_pow (n - 1 - k) h_sub_lt
    -- ‖A^k * (A - B) * B^(n-1-k)‖ ≤ ‖A^k‖ · ‖A - B‖ · ‖B^(n-1-k)‖
    have h1 : ‖A^k * (A - B) * B^(n - 1 - k)‖
        ≤ ‖A^k * (A - B)‖ * ‖B^(n - 1 - k)‖ := norm_mul_le _ _
    have h2 : ‖A^k * (A - B)‖ ≤ ‖A^k‖ * ‖A - B‖ := norm_mul_le _ _
    have hAB_nn : 0 ≤ ‖A - B‖ := norm_nonneg _
    have hBnn : 0 ≤ ‖B^(n - 1 - k)‖ := norm_nonneg _
    calc ‖A^k * (A - B) * B^(n - 1 - k)‖
        ≤ ‖A^k * (A - B)‖ * ‖B^(n - 1 - k)‖ := h1
      _ ≤ (‖A^k‖ * ‖A - B‖) * ‖B^(n - 1 - k)‖ :=
          mul_le_mul_of_nonneg_right h2 hBnn
      _ ≤ (K_A * ‖A - B‖) * K_B := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right hAk_le hAB_nn
          · exact hBk_le
          · exact hBnn
          · exact mul_nonneg hK_A_nn hAB_nn
      _ = K_A * K_B * ‖A - B‖ := by ring
  calc ‖∑ k ∈ Finset.range n, A^k * (A - B) * B^(n - 1 - k)‖
      ≤ ∑ k ∈ Finset.range n, ‖A^k * (A - B) * B^(n - 1 - k)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range n, K_A * K_B * ‖A - B‖ :=
        Finset.sum_le_sum h_term_le
    _ = (n : ℝ) * (K_A * K_B * ‖A - B‖) := by
        rw [Finset.sum_const, Finset.card_range]; ring
    _ = n * K_A * K_B * ‖A - B‖ := by ring

/-- **Sub-lemma 3.1 (n-th power telescoping in any normed ring)**:
`‖A^n - B^n‖ ≤ n · max(‖A‖, ‖B‖)^(n-1) · ‖A - B‖`.

Standard telescoping via `A^n - B^n = Σ_{k=0}^{n-1} A^k · (A-B) · B^{n-1-k}`,
using sub-multiplicativity. Generic in the normed ring instance.

**Mathlib upstream PR target.** -/
private lemma pow_norm_sub_bound
    {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸]
    (A B : 𝔸) (n : ℕ) :
    ‖A^n - B^n‖ ≤ n * (max ‖A‖ ‖B‖)^(n-1) * ‖A - B‖ := by
  -- Induction on n. Base: n = 0 gives 0 ≤ 0. Step: A^{n+1} - B^{n+1}
  -- = A · (A^n - B^n) + (A - B) · B^n; triangle inequality + sub-mult.
  set M : ℝ := max ‖A‖ ‖B‖ with hM_def
  have hM_nn : 0 ≤ M := le_max_of_le_left (norm_nonneg _)
  have hA_le : ‖A‖ ≤ M := le_max_left _ _
  have hB_le : ‖B‖ ≤ M := le_max_right _ _
  have h_AB_nn : 0 ≤ ‖A - B‖ := norm_nonneg _
  induction n with
  | zero =>
    simp
  | succ k ih =>
    have h_split : A^(k+1) - B^(k+1) = A * (A^k - B^k) + (A - B) * B^k := by
      rw [pow_succ', pow_succ']; noncomm_ring
    have h_norm : ‖A^(k+1) - B^(k+1)‖ ≤ ‖A‖ * ‖A^k - B^k‖ + ‖A - B‖ * ‖B^k‖ := by
      rw [h_split]
      refine (norm_add_le _ _).trans ?_
      exact add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    have h_Bk_le : ‖B^k‖ ≤ M^k := by
      refine (norm_pow_le _ _).trans ?_
      exact pow_le_pow_left₀ (norm_nonneg _) hB_le _
    have h_M_Bk : ‖A - B‖ * ‖B^k‖ ≤ ‖A - B‖ * M^k :=
      mul_le_mul_of_nonneg_left h_Bk_le h_AB_nn
    by_cases hk : k = 0
    · -- k = 0 case: A^1 - B^1 = A - B, bound = (0+1) * M^0 * ‖A-B‖ = ‖A-B‖
      subst hk
      simp [pow_succ, pow_zero]
    · -- k ≥ 1: use IH (which gives bound with M^{k-1}).
      have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
      have h_ih_norm : ‖A‖ * ‖A^k - B^k‖ ≤ M * (k * M^(k-1) * ‖A - B‖) := by
        have h_A_ih : ‖A‖ * ‖A^k - B^k‖ ≤ ‖A‖ * (k * M^(k-1) * ‖A - B‖) :=
          mul_le_mul_of_nonneg_left ih (norm_nonneg _)
        refine h_A_ih.trans ?_
        exact mul_le_mul_of_nonneg_right hA_le (by positivity)
      have h_M_pow : M * M^(k-1) = M^k := by
        rw [← pow_succ', Nat.sub_add_cancel hk_pos]
      calc ‖A^(k+1) - B^(k+1)‖
          ≤ ‖A‖ * ‖A^k - B^k‖ + ‖A - B‖ * ‖B^k‖ := h_norm
        _ ≤ M * (k * M^(k-1) * ‖A - B‖) + ‖A - B‖ * M^k :=
            add_le_add h_ih_norm h_M_Bk
        _ = (k+1 : ℕ) * M^((k+1) - 1) * ‖A - B‖ := by
            push_cast
            have h_mul : M * (↑k * M^(k-1) * ‖A - B‖) = ↑k * M^k * ‖A - B‖ := by
              rw [show M * (↑k * M^(k-1) * ‖A - B‖)
                    = ↑k * (M * M^(k-1)) * ‖A - B‖ from by ring,
                  h_M_pow]
            rw [h_mul]; ring

/-- **Sub-lemma 3.2 (scalar power of matrix exp)**:
`(expAmbient(c • Z))^n = expAmbient((n • c) • Z)` since `c • Z` commutes
with itself. Via `NormedSpace.exp_nsmul_eq_pow_exp` or repeated application
of `NormedSpace.exp_add_of_commute` with `Commute.refl`. -/
lemma expAmbient_smul_pow_eq
    (c : ℂ) (Z : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    (SU2MatrixExp.expAmbient (c • Z))^n
      = SU2MatrixExp.expAmbient (((n : ℂ) * c) • Z) := by
  unfold SU2MatrixExp.expAmbient
  rw [← Matrix.exp_nsmul]
  congr 1
  rw [← smul_smul, ← Nat.cast_smul_eq_nsmul ℂ]

/-! ### §3.3. SU(2) membership + absolute linfty-norm bounds for the Trotter step

The Trotter telescoping needs absolute power bounds. For `M ∈ SU(2)`,
`‖M^k‖_linfty ≤ 2` for all `k` (since SU(2) is closed under products).
This bypasses the l2-op-norm detour. -/

/-- Both factors in `fourfoldComm s X Y` are exp of real-smul of ts elements,
hence each ∈ SU(2). Product of 4 SU(2) is SU(2). -/
private lemma fourfoldComm_mem_specialUnitary
    {X Y : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (hY : Y ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (s : ℝ) :
    fourfoldComm s X Y ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  unfold fourfoldComm
  have h_negX : ((-s : ℝ) : ℂ) • X ∈
      SU2LieAlgebra.tracelessSkewHermitian (Fin 2) :=
    OneParameterSubgroupSU2.real_smul_tracelessSkewHermitian hX (-s)
  have h_negY : ((-s : ℝ) : ℂ) • Y ∈
      SU2LieAlgebra.tracelessSkewHermitian (Fin 2) :=
    OneParameterSubgroupSU2.real_smul_tracelessSkewHermitian hY (-s)
  have h_posX : ((s : ℝ) : ℂ) • X ∈
      SU2LieAlgebra.tracelessSkewHermitian (Fin 2) :=
    OneParameterSubgroupSU2.real_smul_tracelessSkewHermitian hX s
  have h_posY : ((s : ℝ) : ℂ) • Y ∈
      SU2LieAlgebra.tracelessSkewHermitian (Fin 2) :=
    OneParameterSubgroupSU2.real_smul_tracelessSkewHermitian hY s
  have hA : SU2MatrixExp.expAmbient (((-s : ℝ) : ℂ) • X) ∈
      Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    OneParameterSubgroupSU2.expAmbient_mem_specialUnitary_of_DetExpZeroOnSu2
      OneParameterSubgroupSU2.DetExpZeroOnSu2_SU2_discharged h_negX
  have hB : SU2MatrixExp.expAmbient (((-s : ℝ) : ℂ) • Y) ∈
      Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    OneParameterSubgroupSU2.expAmbient_mem_specialUnitary_of_DetExpZeroOnSu2
      OneParameterSubgroupSU2.DetExpZeroOnSu2_SU2_discharged h_negY
  have hC : SU2MatrixExp.expAmbient (((s : ℝ) : ℂ) • X) ∈
      Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    OneParameterSubgroupSU2.expAmbient_mem_specialUnitary_of_DetExpZeroOnSu2
      OneParameterSubgroupSU2.DetExpZeroOnSu2_SU2_discharged h_posX
  have hD : SU2MatrixExp.expAmbient (((s : ℝ) : ℂ) • Y) ∈
      Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    OneParameterSubgroupSU2.expAmbient_mem_specialUnitary_of_DetExpZeroOnSu2
      OneParameterSubgroupSU2.DetExpZeroOnSu2_SU2_discharged h_posY
  exact (Matrix.specialUnitaryGroup (Fin 2) ℂ).mul_mem
    ((Matrix.specialUnitaryGroup (Fin 2) ℂ).mul_mem
      ((Matrix.specialUnitaryGroup (Fin 2) ℂ).mul_mem hA hB) hC) hD

/-- For X ∈ ts and r : ℝ, `expAmbient((r : ℂ) • X) ∈ SU(2)`. -/
private lemma expAmbient_real_smul_mem_specialUnitary
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (r : ℝ) :
    SU2MatrixExp.expAmbient (((r : ℝ) : ℂ) • X) ∈
      Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  OneParameterSubgroupSU2.expAmbient_mem_specialUnitary_of_DetExpZeroOnSu2
    OneParameterSubgroupSU2.DetExpZeroOnSu2_SU2_discharged
    (OneParameterSubgroupSU2.real_smul_tracelessSkewHermitian hX r)

/-- Absolute linfty-norm bound on powers of SU(2) elements: `M ∈ SU(2)` ⟹ `‖M^k‖ ≤ 2`. -/
private lemma specialUnitary_pow_linfty_le_two
    {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : M ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) (k : ℕ) :
    ‖M^k‖ ≤ 2 := by
  -- M^k ∈ SU(2) by Submonoid pow closure
  have hMk : M^k ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
    induction k with
    | zero => rw [pow_zero]; exact (Matrix.specialUnitaryGroup (Fin 2) ℂ).one_mem
    | succ j ih => rw [pow_succ]; exact
        (Matrix.specialUnitaryGroup (Fin 2) ℂ).mul_mem ih hM
  exact specialUnitaryGroup_two_linfty_opNorm_le_two ⟨M^k, hMk⟩

/-- **Sub-lemma 3.4 (Trotter sequence convergence — THE gravity well)**:
For `X, Y ∈ ts` and `0 ≤ t`, the n-th power of the four-fold commutator
at scale `√(t/n)` converges to `expAmbient(t • [X, Y])` in matrix topology.

The statement requires `0 ≤ t` because `Real.sqrt (t / (n+1)) = 0` for `t < 0`,
making the sequence trivially constant at 1 — which does NOT equal
`expAmbient(t • [X, Y])` for arbitrary t. The `t < 0` case is handled
downstream in `exp_bracket_mem_H` via the X ↔ Y swap (the bracket
identity `[Y, X] = -[X, Y]` flips sign).

**Proof strategy (purely linfty-op-norm based; no l2 detour):**
- Per-step: by §2.2 `fourfoldComm_norm_le`, `‖P_n - Q_n‖_linfty ≤ 320·(s_n·M)³`
  where `s_n = √(t/(n+1))` and `M = max(‖X‖, ‖Y‖)`. Requires `s_n·M ≤ 1`,
  which holds eventually since `s_n → 0`.
- Both `P_n` and `Q_n` are in SU(2), so `‖P_n^k‖, ‖Q_n^k‖ ≤ 2` for all k
  (by `specialUnitary_pow_linfty_le_two`).
- Telescoping (§3.1a `pow_sub_pow_norm_le_of_pow_bounds`):
  `‖P_n^(n+1) - Q_n^(n+1)‖ ≤ 4(n+1) · ‖P_n - Q_n‖ ≤ 4(n+1) · 320 · (s_n·M)³`
  `= 1280 · M³ · (n+1) · (t/(n+1))^{3/2} = 1280·M³·t^{3/2} · (n+1)^{-1/2} → 0`.
- §3.2 `expAmbient_smul_pow_eq`: `Q_n^(n+1) = expAmbient(t • [X,Y])`.
- Squeeze + `tendsto_iff_norm_sub_tendsto_zero` ⟹ conclusion. -/
theorem trotter_sequence_tendsto
    {X Y : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (hY : Y ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    {t : ℝ} (ht : 0 ≤ t) :
    Filter.Tendsto
      (fun n : ℕ => (fourfoldComm (Real.sqrt (t / (n + 1 : ℕ))) X Y)^(n + 1))
      Filter.atTop
      (nhds (SU2MatrixExp.expAmbient (((t : ℝ) : ℂ) • (X * Y - Y * X)))) := by
  -- Setup: M := max(‖X‖, ‖Y‖), C := 1280·M³·t·√t (= 1280·M³·t^{3/2}).
  set M : ℝ := max ‖X‖ ‖Y‖ with hM_def
  have hM_nn : 0 ≤ M := le_max_of_le_left (norm_nonneg _)
  have hX_le_M : ‖X‖ ≤ M := le_max_left _ _
  have hY_le_M : ‖Y‖ ≤ M := le_max_right _ _
  have hZ_ts : (X * Y - Y * X) ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2) :=
    SU2LieAlgebra.tracelessSkewHermitian_mul_sub_mul_mem hX hY
  set Z_lim : Matrix (Fin 2) (Fin 2) ℂ :=
    SU2MatrixExp.expAmbient (((t : ℝ) : ℂ) • (X * Y - Y * X)) with hZ_lim_def
  set C : ℝ := 1280 * M^3 * t * Real.sqrt t with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]; positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- N0 must satisfy: (n+1) > t·M² (for cubic bound) AND (n+1) > (C/ε)² (for ε bound).
  set N0 : ℕ := ⌈max (t * M^2) ((C / ε)^2)⌉₊ + 1 with hN0_def
  refine ⟨N0, ?_⟩
  intro n hn
  rw [dist_eq_norm]
  set s_n : ℝ := Real.sqrt (t / (n + 1 : ℕ)) with hs_n_def
  have hn1_pos : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
  have hn1_ne : ((n + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hn1_pos
  have hs_n_nn : 0 ≤ s_n := Real.sqrt_nonneg _
  have hs_n_sq : s_n^2 = t / (n + 1 : ℕ) := by
    rw [hs_n_def, Real.sq_sqrt]; exact div_nonneg ht hn1_pos.le
  set P_n : Matrix (Fin 2) (Fin 2) ℂ := fourfoldComm s_n X Y with hP_n_def
  set Q_n : Matrix (Fin 2) (Fin 2) ℂ :=
    SU2MatrixExp.expAmbient (((s_n^2 : ℝ) : ℂ) • (X * Y - Y * X)) with hQ_n_def
  -- Q_n^(n+1) = Z_lim
  have hQ_pow : Q_n^(n+1) = Z_lim := by
    rw [hQ_n_def, expAmbient_smul_pow_eq, hZ_lim_def]
    congr 1; rw [hs_n_sq]; push_cast; field_simp
  -- Memberships
  have hP_n_su : P_n ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    fourfoldComm_mem_specialUnitary hX hY s_n
  have hQ_n_su : Q_n ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    expAmbient_real_smul_mem_specialUnitary hZ_ts (s_n^2)
  -- N0 ≤ n+1 + bounds extracted
  have h_n1_ge_N0 : (N0 : ℕ) ≤ n + 1 := Nat.le_succ_of_le hn
  have h_N0_eq : ((N0 : ℕ) : ℝ) = (⌈max (t * M^2) ((C / ε)^2)⌉₊ : ℝ) + 1 := by
    rw [hN0_def]; push_cast; rfl
  have h_n1_ge_tM2 : (t * M^2 : ℝ) ≤ (n + 1 : ℕ) := by
    have h0 : (t * M^2 : ℝ) ≤ ⌈max (t * M^2) ((C / ε)^2)⌉₊ :=
      (le_max_left _ _).trans (Nat.le_ceil _)
    have h2 : ((N0 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast h_n1_ge_N0
    linarith
  -- Cubic bound: s_n · M ≤ 1
  have hs_n_M_le_one : s_n * M ≤ 1 := by
    have h_sq : (s_n * M)^2 ≤ 1 := by
      rw [mul_pow, hs_n_sq, div_mul_eq_mul_div, div_le_one hn1_pos]
      exact h_n1_ge_tM2
    have hsM_nn : 0 ≤ s_n * M := mul_nonneg hs_n_nn hM_nn
    nlinarith [hsM_nn, h_sq]
  have h_cubic : ‖P_n - Q_n‖ ≤ 320 * (s_n * M)^3 := by
    rw [hP_n_def, hQ_n_def]
    exact fourfoldComm_norm_le hs_n_nn hM_nn hs_n_M_le_one hX_le_M hY_le_M
  -- Telescoping
  have h_telescope :
      ‖P_n^(n+1) - Q_n^(n+1)‖ ≤ (n + 1 : ℕ) * 2 * 2 * ‖P_n - Q_n‖ := by
    apply pow_sub_pow_norm_le_of_pow_bounds P_n Q_n (n+1)
      (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (0:ℝ) ≤ 2)
    · intro k _; exact specialUnitary_pow_linfty_le_two hP_n_su k
    · intro k _; exact specialUnitary_pow_linfty_le_two hQ_n_su k
  -- Combined bound: ‖P_n^(n+1) - Q_n^(n+1)‖ ≤ 1280·(n+1)·s_n³·M³
  --                                      = 1280·M³·t·s_n  (using s_n²=t/(n+1))
  have h_combined : ‖P_n^(n+1) - Q_n^(n+1)‖ ≤ 1280 * M^3 * t * s_n := by
    calc ‖P_n^(n+1) - Q_n^(n+1)‖
        ≤ (n + 1 : ℕ) * 2 * 2 * ‖P_n - Q_n‖ := h_telescope
      _ ≤ (n + 1 : ℕ) * 2 * 2 * (320 * (s_n * M)^3) :=
          mul_le_mul_of_nonneg_left h_cubic (by positivity)
      _ = 1280 * (n + 1 : ℕ) * s_n^3 * M^3 := by ring
      _ = 1280 * (n + 1 : ℕ) * (s_n * s_n^2) * M^3 := by ring
      _ = 1280 * (n + 1 : ℕ) * (s_n * (t / (n + 1 : ℕ))) * M^3 := by rw [hs_n_sq]
      _ = 1280 * M^3 * t * s_n := by field_simp
  -- s_n = √(t/(n+1)) = √t / √(n+1)
  have h_sqrt_n1_pos : 0 < Real.sqrt (n + 1 : ℕ) := by
    apply Real.sqrt_pos.mpr; exact_mod_cast hn1_pos
  have h_s_n_split : s_n = Real.sqrt t / Real.sqrt (n + 1 : ℕ) := by
    rw [hs_n_def, Real.sqrt_div ht]
  -- 1280·M³·t·s_n = 1280·M³·t·√t / √(n+1) = C / √(n+1)
  have h_C_form : 1280 * M^3 * t * s_n = C / Real.sqrt (n + 1 : ℕ) := by
    rw [h_s_n_split, hC_def]; ring
  rw [h_C_form] at h_combined
  -- Now (C/ε)² < n+1, so √(n+1) > C/ε, so C/√(n+1) < ε.
  have h_n1_gt_Csq : ((C / ε)^2 : ℝ) < (n + 1 : ℕ) := by
    have h0 : ((C / ε)^2 : ℝ) ≤ ⌈max (t * M^2) ((C / ε)^2)⌉₊ :=
      (le_max_right _ _).trans (Nat.le_ceil _)
    have h2 : ((N0 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast h_n1_ge_N0
    linarith
  -- Bound C/√(n+1) by ε strictly
  have h_C_div_strict : C / Real.sqrt (n + 1 : ℕ) < ε := by
    rcases eq_or_lt_of_le hC_nn with hC_zero | hC_pos
    · rw [← hC_zero, zero_div]; exact hε
    · have h_Cε_pos : 0 < C / ε := div_pos hC_pos hε
      have h_sqrt_lt : C / ε < Real.sqrt (n + 1 : ℕ) := by
        rw [show (C / ε : ℝ) = Real.sqrt ((C / ε)^2) from
          (Real.sqrt_sq h_Cε_pos.le).symm]
        exact Real.sqrt_lt_sqrt (by positivity) h_n1_gt_Csq
      rw [div_lt_iff₀ h_sqrt_n1_pos]
      have h_eq : C = ε * (C / ε) := by field_simp
      calc C = ε * (C / ε) := h_eq
        _ < ε * Real.sqrt (n + 1 : ℕ) :=
            mul_lt_mul_of_pos_left h_sqrt_lt hε
  -- Final: ‖P_n^(n+1) - Z_lim‖ < ε via P_n^(n+1) - Q_n^(n+1) and hQ_pow.
  rw [← hQ_pow]
  exact lt_of_le_of_lt h_combined h_C_div_strict

/-! ### §3.5. Step 1 — BCH bracket closure (final composition)

For a closed subgroup `H ≤ SU(2)` with `exp(ℝ•X), exp(ℝ•Y) ⊆ H` (X, Y ∈ ts),
`exp(ℝ•[X,Y]) ⊆ H`. The proof decomposes into:
- `exp_bracket_mem_H_pos` for `t ≥ 0`: direct Trotter discharge.
- `exp_bracket_mem_H` for arbitrary `t : ℝ`: case-splits and uses the
  X ↔ Y swap for `t < 0`, exploiting `[Y, X] = -[X, Y]`. -/

/-- **Step 1 (positive-t core)**: for `0 ≤ t` and a closed `H ≤ SU(2)` with
`exp(ℝ•X), exp(ℝ•Y) ⊆ H` (X, Y ∈ ts), `expAmbient(t • [X, Y]) ∈ H.val`.

This is the direct Trotter discharge. The general `t : ℝ` version
(`exp_bracket_mem_H`) handles `t < 0` via the X ↔ Y swap. -/
private lemma exp_bracket_mem_H_pos
    (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (hH_closed : IsClosed (H : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)))
    {X Y : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (hY : Y ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (h_expX : ∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
        M ∈ H ∧ M.val = SU2MatrixExp.expAmbient (((t : ℝ) : ℂ) • X))
    (h_expY : ∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
        M ∈ H ∧ M.val = SU2MatrixExp.expAmbient (((t : ℝ) : ℂ) • Y))
    {t : ℝ} (ht : 0 ≤ t) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
      M ∈ H ∧ M.val = SU2MatrixExp.expAmbient
        (((t : ℝ) : ℂ) • (X * Y - Y * X)) := by
  have hZ_ts : (X * Y - Y * X) ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2) :=
    SU2LieAlgebra.tracelessSkewHermitian_mul_sub_mul_mem hX hY
  have h_smul_ts : ((t : ℂ) • (X * Y - Y * X)) ∈
      SU2LieAlgebra.tracelessSkewHermitian (Fin 2) := by
    have h_real_smul : ((t : ℂ) • (X * Y - Y * X) : Matrix (Fin 2) (Fin 2) ℂ)
        = (t : ℝ) • (X * Y - Y * X) := by
      ext i j; simp [Matrix.smul_apply, Complex.real_smul]
    rw [h_real_smul]
    exact (SU2LieAlgebra.tracelessSkewHermitian (Fin 2)).smul_mem _ hZ_ts
  have hExpZ_su :
      SU2MatrixExp.expAmbient (((t : ℝ) : ℂ) • (X * Y - Y * X)) ∈
        Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    OneParameterSubgroupSU2.expAmbient_mem_specialUnitary_of_DetExpZeroOnSu2
      OneParameterSubgroupSU2.DetExpZeroOnSu2_SU2_discharged h_smul_ts
  set M_lim : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
    ⟨SU2MatrixExp.expAmbient (((t : ℝ) : ℂ) • (X * Y - Y * X)), hExpZ_su⟩
  refine ⟨M_lim, ?_, rfl⟩
  choose M_n hM_n_mem hM_n_val using fun n : ℕ =>
    fourfoldComm_mem_H_val H h_expX h_expY (Real.sqrt (t / (n + 1 : ℕ)))
  have hM_pow_val : ∀ n : ℕ, ((M_n n) ^ (n+1)).val =
      (fourfoldComm (Real.sqrt (t / (n + 1 : ℕ))) X Y) ^ (n+1) := fun n => by
    rw [SubmonoidClass.coe_pow]; congr 1; exact hM_n_val n
  have h_subtype_tendsto :
      Filter.Tendsto (fun n => (M_n n) ^ (n+1)) Filter.atTop (nhds M_lim) := by
    rw [tendsto_subtype_rng]
    show Filter.Tendsto (fun n => ((M_n n) ^ (n+1) :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val)
      Filter.atTop (nhds M_lim.val)
    simp_rw [hM_pow_val]
    exact trotter_sequence_tendsto hX hY ht
  have hM_pow_mem : ∀ n : ℕ, (M_n n) ^ (n+1) ∈ H := fun n =>
    H.pow_mem (hM_n_mem n) _
  exact hH_closed.mem_of_tendsto h_subtype_tendsto
    (Filter.Eventually.of_forall hM_pow_mem)

theorem exp_bracket_mem_H
    (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (hH_closed : IsClosed (H : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)))
    {X Y : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (hY : Y ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (h_expX : ∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
        M ∈ H ∧ M.val = SU2MatrixExp.expAmbient (((t : ℝ) : ℂ) • X))
    (h_expY : ∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
        M ∈ H ∧ M.val = SU2MatrixExp.expAmbient (((t : ℝ) : ℂ) • Y))
    (t : ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
      M ∈ H ∧ M.val = SU2MatrixExp.expAmbient
        (((t : ℝ) : ℂ) • (X * Y - Y * X)) := by
  rcases le_or_gt 0 t with ht | ht
  · -- t ≥ 0: direct application
    exact exp_bracket_mem_H_pos H hH_closed hX hY h_expX h_expY ht
  · -- t < 0: use X ↔ Y swap on -t ≥ 0, then [Y,X] = -[X,Y].
    have h_neg_nn : 0 ≤ -t := neg_nonneg.mpr ht.le
    obtain ⟨M, hM_mem, hM_val⟩ :=
      exp_bracket_mem_H_pos H hH_closed hY hX h_expY h_expX h_neg_nn
    refine ⟨M, hM_mem, ?_⟩
    rw [hM_val]
    -- expAmbient((-t) • (Y*X - X*Y)) = expAmbient(t • (X*Y - Y*X))
    congr 1
    push_cast
    module

/-! ## §4. Step 2/3/4 composition — IFT 3-direction discharge

The composition: given the v4 hypothesis (`exp(ℝ•X_i) ⊆ H` for two
ℝ-LI `X₁, X₂ ∈ ts`), apply Step 1 to get `exp(ℝ•[X₁,X₂]) ⊆ H`, then use
spanning + IFT to derive `1 ∈ interior(H)` ⟹ `H = ⊤`. -/

/-! ### §4.1. The 3-direction product map and its derivative

For two ℝ-LI `X₁, X₂ ∈ 𝔰𝔲(2)`, define
`Φ(a, b, c) := expAmbient(a • X₁) · expAmbient(b • X₂) · expAmbient(c • [X₁, X₂])`.
Φ has strict Fréchet derivative at `0 : ℝ × ℝ × ℝ` equal to
`Λ(δa, δb, δc) := δa • X₁ + δb • X₂ + δc • [X₁, X₂]`.

This map will be the IFT seed: composed with `su2Log`, we get a map
`ψ : ℝ³ → ts` whose derivative at 0 is the basis-change CLE
`ℝ³ ≃L[ℝ] ↥𝔰𝔲(2)`, hence IFT-invertible. -/

/-- The 3-direction product map. -/
noncomputable def threeDirProduct (X₁ X₂ : Matrix (Fin 2) (Fin 2) ℂ) :
    (ℝ × ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℂ :=
  fun v => SU2MatrixExp.expAmbient ((v.1 : ℂ) • X₁)
    * SU2MatrixExp.expAmbient ((v.2.1 : ℂ) • X₂)
    * SU2MatrixExp.expAmbient ((v.2.2 : ℂ) • (X₁ * X₂ - X₂ * X₁))

/-- `threeDirProduct X₁ X₂ 0 = 1`. -/
lemma threeDirProduct_zero (X₁ X₂ : Matrix (Fin 2) (Fin 2) ℂ) :
    threeDirProduct X₁ X₂ (0, 0, 0) = 1 := by
  unfold threeDirProduct SU2MatrixExp.expAmbient
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, mul_one]

/-- For all `v : ℝ³`, `threeDirProduct X₁ X₂ v ∈ specialUnitaryGroup` when
`X₁, X₂ ∈ ts`. -/
lemma threeDirProduct_mem_specialUnitary
    {X₁ X₂ : Matrix (Fin 2) (Fin 2) ℂ}
    (hX₁ : X₁ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (hX₂ : X₂ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (v : ℝ × ℝ × ℝ) :
    threeDirProduct X₁ X₂ v ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  unfold threeDirProduct
  have hX₃ : (X₁ * X₂ - X₂ * X₁) ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2) :=
    SU2LieAlgebra.tracelessSkewHermitian_mul_sub_mul_mem hX₁ hX₂
  have h1 := expAmbient_real_smul_mem_specialUnitary hX₁ v.1
  have h2 := expAmbient_real_smul_mem_specialUnitary hX₂ v.2.1
  have h3 := expAmbient_real_smul_mem_specialUnitary hX₃ v.2.2
  exact (Matrix.specialUnitaryGroup (Fin 2) ℂ).mul_mem
    ((Matrix.specialUnitaryGroup (Fin 2) ℂ).mul_mem h1 h2) h3

/-- **Strict derivative of `a ↦ expAmbient((a : ℂ) • X)` at `a = 0`** is `X`.

Composition: `(a : ℝ) → (a : ℂ) • X → expAmbient(_)`.
- Linear in `a`, so derivative at any `a` is `X`.
- Chain with `expAmbient`'s identity derivative at 0. -/
lemma expAmbient_smul_real_hasStrictDerivAt_zero (X : Matrix (Fin 2) (Fin 2) ℂ) :
    HasStrictDerivAt
      (fun a : ℝ => SU2MatrixExp.expAmbient ((a : ℂ) • X)) X 0 := by
  -- Step 1: `gx : a ↦ (a : ℂ) • X` is linear with derivative X.
  have h_lin : (fun a : ℝ => ((a : ℂ) • X : Matrix (Fin 2) (Fin 2) ℂ))
      = fun a : ℝ => a • X := by
    funext a
    -- (↑a : ℂ) • X = a • X by IsScalarTower (ℝ → ℂ → Matrix).
    exact IsScalarTower.algebraMap_smul ℂ a X
  have hgx : HasStrictDerivAt (fun a : ℝ => ((a : ℂ) • X : Matrix (Fin 2) (Fin 2) ℂ))
      X 0 := by
    rw [h_lin]
    simpa using (hasStrictDerivAt_id (0 : ℝ)).smul_const X
  -- Step 2: expAmbient has strict derivative identity at 0.
  have hexp : HasStrictFDerivAt (SU2MatrixExp.expAmbient :
      Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
      (1 : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ)
      (((0 : ℝ) : ℂ) • X) := by
    have hzero : ((0 : ℝ) : ℂ) • X = (0 : Matrix (Fin 2) (Fin 2) ℂ) := by simp
    rw [hzero]
    exact SU2LocalDiffeo.expAmbient_hasStrictFDerivAt_zero
  -- Chain rule: HasStrictDerivAt (expAmbient ∘ gx) (1 X = X) 0
  have h_comp := hexp.comp_hasStrictDerivAt 0 hgx
  -- The derivative is (1 : Matrix →L Matrix) applied to X = X.
  simpa using h_comp

/-- Per-direction strict derivative for the i-th factor of `threeDirProduct`. -/
private lemma expAmbient_proj_hasStrictFDerivAt_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Matrix (Fin 2) (Fin 2) ℂ) (proj : E →L[ℝ] ℝ) :
    HasStrictFDerivAt (fun v : E => SU2MatrixExp.expAmbient ((proj v : ℂ) • X))
      (proj.smulRight X) 0 := by
  -- h_inner : HasStrictDerivAt at 0 ∈ ℝ.
  -- Convert to HasStrictFDerivAt at proj 0 = 0.
  have h_inner_F : HasStrictFDerivAt
      (fun a : ℝ => SU2MatrixExp.expAmbient ((a : ℂ) • X))
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) X) (proj 0) := by
    rw [proj.map_zero]
    exact (expAmbient_smul_real_hasStrictDerivAt_zero X).hasStrictFDerivAt
  -- proj has strict F-deriv = proj.
  have h_proj : HasStrictFDerivAt (proj : E → ℝ) proj 0 := proj.hasStrictFDerivAt
  -- Compose via HasStrictFDerivAt.comp.
  have h_comp := h_inner_F.comp (0 : E) h_proj
  -- h_comp : HasStrictFDerivAt (...) ((smulRight 1 X).comp proj) 0
  -- Want: HasStrictFDerivAt (...) (proj.smulRight X) 0. Show equality of CLMs.
  have h_CLM_eq : (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) X).comp proj
      = proj.smulRight X := by
    ext v
    simp
  rw [← h_CLM_eq]
  exact h_comp

/-- The three coordinate projections `(ℝ × ℝ × ℝ) → ℝ` as CLMs. -/
private noncomputable def proj1 : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)
private noncomputable def proj2 : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
private noncomputable def proj3 : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- **The 3-direction linear map `Λ : ℝ³ →L[ℝ] Matrix _ _ ℂ`**: the candidate
strict Fréchet derivative of `threeDirProduct` at 0. -/
private noncomputable def threeDirDerivCLM (X₁ X₂ : Matrix (Fin 2) (Fin 2) ℂ) :
    (ℝ × ℝ × ℝ) →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  proj1.smulRight X₁ + proj2.smulRight X₂
    + proj3.smulRight (X₁ * X₂ - X₂ * X₁)

/-- `threeDirDerivCLM` evaluated at `(a, b, c)` (in ℝ-smul form). -/
private lemma threeDirDerivCLM_apply (X₁ X₂ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : ℝ × ℝ × ℝ) :
    threeDirDerivCLM X₁ X₂ v = v.1 • X₁ + v.2.1 • X₂
      + v.2.2 • (X₁ * X₂ - X₂ * X₁) := by
  unfold threeDirDerivCLM proj1 proj2 proj3
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply]
  rfl

/-- **The strict Fréchet derivative of `threeDirProduct X₁ X₂` at 0 equals
the 3-direction linear map `threeDirDerivCLM X₁ X₂`.**

**Proof sketch** (`HasStrictFDerivAt.mul'` chain):
- Each per-direction factor `fun v => expAmbient((proj_i v : ℂ) • X_i)` has
  strict F-derivative `proj_i.smulRight X_i` at 0 (via
  `expAmbient_proj_hasStrictFDerivAt_zero`).
- Composing via `HasStrictFDerivAt.mul'` twice for the 3-fold product, at 0
  each factor evaluates to 1, so the cross-terms drop and the derivative is
  the sum `proj_1.smulRight X_1 + proj_2.smulRight X_2 + proj_3.smulRight [X_1,X_2]`
  = `threeDirDerivCLM X_1 X_2`.

**Discharge.** Two `.mul'` applications chain the per-direction derivatives.
At `x = 0` each factor evaluates to `1`, so the resulting CLM expression
`1 • d₃ + op 1 • (1 • d₂ + op 1 • d₁)` simplifies to `d₁ + d₂ + d₃ =
threeDirDerivCLM X₁ X₂` via `MulOpposite.op_one`, `one_smul`, and `abel`.

The product-of-functions form `(f₁ * f₂) * f₃` agrees with `threeDirProduct
X₁ X₂` pointwise by `funext + rfl` (matrix left-associative multiplication).
-/
private lemma threeDirProduct_hasStrictFDerivAt_zero
    (X₁ X₂ : Matrix (Fin 2) (Fin 2) ℂ) :
    HasStrictFDerivAt (threeDirProduct X₁ X₂)
      (threeDirDerivCLM X₁ X₂) (0 : ℝ × ℝ × ℝ) := by
  -- Per-direction strict F-derivatives.
  have hf1 : HasStrictFDerivAt
      (fun v : ℝ × ℝ × ℝ => SU2MatrixExp.expAmbient ((proj1 v : ℂ) • X₁))
      (proj1.smulRight X₁) (0 : ℝ × ℝ × ℝ) :=
    expAmbient_proj_hasStrictFDerivAt_zero X₁ proj1
  have hf2 : HasStrictFDerivAt
      (fun v : ℝ × ℝ × ℝ => SU2MatrixExp.expAmbient ((proj2 v : ℂ) • X₂))
      (proj2.smulRight X₂) (0 : ℝ × ℝ × ℝ) :=
    expAmbient_proj_hasStrictFDerivAt_zero X₂ proj2
  have hf3 : HasStrictFDerivAt
      (fun v : ℝ × ℝ × ℝ =>
        SU2MatrixExp.expAmbient ((proj3 v : ℂ) • (X₁ * X₂ - X₂ * X₁)))
      (proj3.smulRight (X₁ * X₂ - X₂ * X₁)) (0 : ℝ × ℝ × ℝ) :=
    expAmbient_proj_hasStrictFDerivAt_zero _ proj3
  -- Chain via .mul'.
  have h12 := hf1.mul' hf2
  have h123 := h12.mul' hf3
  -- Pointwise product equals threeDirProduct (associativity of matrix mul).
  have h_fun_eq :
      ((fun v : ℝ × ℝ × ℝ => SU2MatrixExp.expAmbient ((proj1 v : ℂ) • X₁)) *
          fun v => SU2MatrixExp.expAmbient ((proj2 v : ℂ) • X₂)) *
        (fun v => SU2MatrixExp.expAmbient ((proj3 v : ℂ) • (X₁ * X₂ - X₂ * X₁)))
        = threeDirProduct X₁ X₂ := by
    funext v; rfl
  -- proj_i 0 = 0, so each expAmbient factor at 0 equals 1.
  have hexp_zero : SU2MatrixExp.expAmbient (0 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    unfold SU2MatrixExp.expAmbient; exact NormedSpace.exp_zero
  have hp1_zero : proj1 (0 : ℝ × ℝ × ℝ) = 0 := rfl
  have hp2_zero : proj2 (0 : ℝ × ℝ × ℝ) = 0 := rfl
  have hp3_zero : proj3 (0 : ℝ × ℝ × ℝ) = 0 := rfl
  have hf12_zero :
      (((fun v : ℝ × ℝ × ℝ => SU2MatrixExp.expAmbient ((proj1 v : ℂ) • X₁)) *
          fun v => SU2MatrixExp.expAmbient ((proj2 v : ℂ) • X₂)) 0
            : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    show SU2MatrixExp.expAmbient ((proj1 (0 : ℝ × ℝ × ℝ) : ℂ) • X₁) *
        SU2MatrixExp.expAmbient ((proj2 (0 : ℝ × ℝ × ℝ) : ℂ) • X₂) = 1
    rw [hp1_zero, hp2_zero]
    simp [hexp_zero]
  have hf1_zero :
      SU2MatrixExp.expAmbient ((proj1 (0 : ℝ × ℝ × ℝ) : ℂ) • X₁) = 1 := by
    rw [hp1_zero]; simp [hexp_zero]
  have hf2_zero :
      SU2MatrixExp.expAmbient ((proj2 (0 : ℝ × ℝ × ℝ) : ℂ) • X₂) = 1 := by
    rw [hp2_zero]; simp [hexp_zero]
  have hf3_zero :
      SU2MatrixExp.expAmbient
        ((proj3 (0 : ℝ × ℝ × ℝ) : ℂ) • (X₁ * X₂ - X₂ * X₁)) = 1 := by
    rw [hp3_zero]; simp [hexp_zero]
  rw [hf12_zero, hf3_zero, hf1_zero, hf2_zero] at h123
  -- Now h123 has CLM: 1 • d₃ + op 1 • (1 • d₂ + op 1 • d₁) at the right function.
  rw [← h_fun_eq]
  refine h123.congr_fderiv ?_
  -- Final CLM equality after collapsing units.
  simp only [MulOpposite.op_one, one_smul]
  unfold threeDirDerivCLM
  abel

/-- When `exp(ℝ•X₁), exp(ℝ•X₂), exp(ℝ•[X₁,X₂]) ⊆ H.val`, each
`threeDirProduct X₁ X₂ v` is the matrix value of some element of `H`. -/
lemma threeDirProduct_mem_H_val
    (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    {X₁ X₂ : Matrix (Fin 2) (Fin 2) ℂ}
    (h_expX₁ : ∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
        M ∈ H ∧ M.val = SU2MatrixExp.expAmbient (((t : ℝ) : ℂ) • X₁))
    (h_expX₂ : ∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
        M ∈ H ∧ M.val = SU2MatrixExp.expAmbient (((t : ℝ) : ℂ) • X₂))
    (h_expBracket : ∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
        M ∈ H ∧ M.val = SU2MatrixExp.expAmbient
          (((t : ℝ) : ℂ) • (X₁ * X₂ - X₂ * X₁)))
    (v : ℝ × ℝ × ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
      M ∈ H ∧ M.val = threeDirProduct X₁ X₂ v := by
  obtain ⟨A, hA_mem, hA_val⟩ := h_expX₁ v.1
  obtain ⟨B, hB_mem, hB_val⟩ := h_expX₂ v.2.1
  obtain ⟨C, hC_mem, hC_val⟩ := h_expBracket v.2.2
  refine ⟨A * B * C, ?_, ?_⟩
  · exact H.mul_mem (H.mul_mem hA_mem hB_mem) hC_mem
  · show (A * B * C : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val =
      threeDirProduct X₁ X₂ v
    have h_val_mul : ∀ (P Q : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)),
        (P * Q : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val = P.val * Q.val :=
      fun _ _ => rfl
    rw [h_val_mul, h_val_mul, hA_val, hB_val, hC_val]
    rfl

/-! ### §4.5. IFT composition substrate

Build the CLE `(ℝ × ℝ × ℝ) ≃L[ℝ] ↥𝔰𝔲(2)` from the ℝ-LI + spanning
hypotheses, the lifted map `ψ_ts := su2Log ∘ Φ : ℝ³ → ↥𝔰𝔲(2)` (defined
on a neighborhood of `0`), and its strict Fréchet derivative.
-/

/-- Bridge: ℝ-smul on Matrix coincides with the algebra-map'd ℂ-smul. -/
private lemma smul_eq_smul_complex_coe (a : ℝ)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    a • X = (a : ℂ) • X :=
  (IsScalarTower.algebraMap_smul ℂ a X).symm

/-- `threeDirDerivCLM X₁ X₂ v ∈ 𝔰𝔲(2)` whenever `X₁, X₂ ∈ 𝔰𝔲(2)`
(closure under add + scalar + bracket). -/
private lemma threeDirDerivCLM_apply_mem_ts
    {X₁ X₂ : Matrix (Fin 2) (Fin 2) ℂ}
    (hX₁ : X₁ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (hX₂ : X₂ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (v : ℝ × ℝ × ℝ) :
    threeDirDerivCLM X₁ X₂ v ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2) := by
  rw [threeDirDerivCLM_apply]
  have hbr : X₁ * X₂ - X₂ * X₁ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2) :=
    SU2LieAlgebra.tracelessSkewHermitian_mul_sub_mul_mem hX₁ hX₂
  exact Submodule.add_mem _
    (Submodule.add_mem _
      (Submodule.smul_mem _ _ hX₁)
      (Submodule.smul_mem _ _ hX₂))
    (Submodule.smul_mem _ _ hbr)

/-- Codomain-restriction of `threeDirDerivCLM X₁ X₂` to `↥𝔰𝔲(2)`. -/
private noncomputable def threeDirDerivCLM_ts
    {X₁ X₂ : Matrix (Fin 2) (Fin 2) ℂ}
    (hX₁ : X₁ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (hX₂ : X₂ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2)) :
    (ℝ × ℝ × ℝ) →L[ℝ] ↥(SU2LieAlgebra.tracelessSkewHermitian (Fin 2)) :=
  (threeDirDerivCLM X₁ X₂).codRestrict
    (SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (threeDirDerivCLM_apply_mem_ts hX₁ hX₂)

private lemma threeDirDerivCLM_ts_apply_coe
    {X₁ X₂ : Matrix (Fin 2) (Fin 2) ℂ}
    (hX₁ : X₁ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (hX₂ : X₂ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (v : ℝ × ℝ × ℝ) :
    ((threeDirDerivCLM_ts hX₁ hX₂ v) : Matrix (Fin 2) (Fin 2) ℂ)
      = threeDirDerivCLM X₁ X₂ v := rfl

/-- `threeDirDerivCLM_ts` is injective when `X₁, X₂` are ℝ-LI (via `h3LI`). -/
private lemma threeDirDerivCLM_ts_injective
    {X₁ X₂ : Matrix (Fin 2) (Fin 2) ℂ}
    (hX₁ : X₁ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (hX₂ : X₂ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (h_LI : ∀ (a b : ℝ), (a : ℂ) • X₁ + (b : ℂ) • X₂ = 0 → a = 0 ∧ b = 0) :
    Function.Injective (threeDirDerivCLM_ts hX₁ hX₂) := by
  intro v₁ v₂ h_eq
  have h_eq_val : (threeDirDerivCLM X₁ X₂ v₁ : Matrix (Fin 2) (Fin 2) ℂ)
      = threeDirDerivCLM X₁ X₂ v₂ := by
    have := congrArg (Subtype.val) h_eq
    exact this
  have h_diff : threeDirDerivCLM X₁ X₂ (v₁ - v₂) = 0 := by
    rw [map_sub, h_eq_val]; exact sub_self _
  rw [threeDirDerivCLM_apply] at h_diff
  set a := (v₁ - v₂).1
  set b := (v₁ - v₂).2.1
  set c := (v₁ - v₂).2.2
  -- The 3-vector (a, b, c) has all components zero.
  have h_zero_cmps : a = 0 ∧ b = 0 ∧ c = 0 := by
    apply SU2LieAlgebra.tracelessSkewHermitian_X_Y_bracket_lin_indep hX₁ hX₂ h_LI a b c
    rw [← smul_eq_smul_complex_coe a X₁,
        ← smul_eq_smul_complex_coe b X₂,
        ← smul_eq_smul_complex_coe c (X₁ * X₂ - X₂ * X₁)]
    exact h_diff
  -- So v₁ - v₂ = 0 hence v₁ = v₂.
  obtain ⟨ha, hb, hc⟩ := h_zero_cmps
  have h_v_eq : v₁ - v₂ = 0 := by
    ext
    · exact ha
    · exact hb
    · exact hc
  exact sub_eq_zero.mp h_v_eq

/-- `threeDirDerivCLM_ts` is surjective (every Y ∈ 𝔰𝔲(2) is the image
of some `(a, b, c) ∈ ℝ³`, via `h3spans`). -/
private lemma threeDirDerivCLM_ts_surjective
    {X₁ X₂ : Matrix (Fin 2) (Fin 2) ℂ}
    (hX₁ : X₁ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (hX₂ : X₂ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (h_LI : ∀ (a b : ℝ), (a : ℂ) • X₁ + (b : ℂ) • X₂ = 0 → a = 0 ∧ b = 0) :
    Function.Surjective (threeDirDerivCLM_ts hX₁ hX₂) := by
  intro ⟨Y, hY⟩
  obtain ⟨a, b, c, h_Y_eq⟩ :=
    SU2LieAlgebra.tracelessSkewHermitian_X_Y_bracket_spans hX₁ hX₂ h_LI hY
  refine ⟨(a, b, c), ?_⟩
  apply Subtype.ext
  show threeDirDerivCLM X₁ X₂ (a, b, c) = Y
  rw [threeDirDerivCLM_apply, h_Y_eq,
      smul_eq_smul_complex_coe a X₁,
      smul_eq_smul_complex_coe b X₂,
      smul_eq_smul_complex_coe c (X₁ * X₂ - X₂ * X₁)]

/-- `(ℝ × ℝ × ℝ) ≃ₗ[ℝ] ↥𝔰𝔲(2)` from `threeDirDerivCLM_ts` bijectivity. -/
private noncomputable def threeDirDerivLE
    {X₁ X₂ : Matrix (Fin 2) (Fin 2) ℂ}
    (hX₁ : X₁ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (hX₂ : X₂ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (h_LI : ∀ (a b : ℝ), (a : ℂ) • X₁ + (b : ℂ) • X₂ = 0 → a = 0 ∧ b = 0) :
    (ℝ × ℝ × ℝ) ≃ₗ[ℝ] ↥(SU2LieAlgebra.tracelessSkewHermitian (Fin 2)) :=
  LinearEquiv.ofBijective ((threeDirDerivCLM_ts hX₁ hX₂) : (ℝ × ℝ × ℝ) →ₗ[ℝ] _)
    ⟨threeDirDerivCLM_ts_injective hX₁ hX₂ h_LI,
     threeDirDerivCLM_ts_surjective hX₁ hX₂ h_LI⟩

/-- `(ℝ × ℝ × ℝ) ≃L[ℝ] ↥𝔰𝔲(2)` — the basis-change CLE. -/
private noncomputable def threeDirDerivCLE
    {X₁ X₂ : Matrix (Fin 2) (Fin 2) ℂ}
    (hX₁ : X₁ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (hX₂ : X₂ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (h_LI : ∀ (a b : ℝ), (a : ℂ) • X₁ + (b : ℂ) • X₂ = 0 → a = 0 ∧ b = 0) :
    (ℝ × ℝ × ℝ) ≃L[ℝ] ↥(SU2LieAlgebra.tracelessSkewHermitian (Fin 2)) :=
  (threeDirDerivLE hX₁ hX₂ h_LI).toContinuousLinearEquiv

private lemma threeDirDerivCLE_apply
    {X₁ X₂ : Matrix (Fin 2) (Fin 2) ℂ}
    (hX₁ : X₁ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (hX₂ : X₂ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (h_LI : ∀ (a b : ℝ), (a : ℂ) • X₁ + (b : ℂ) • X₂ = 0 → a = 0 ∧ b = 0)
    (v : ℝ × ℝ × ℝ) :
    ((threeDirDerivCLE hX₁ hX₂ h_LI v) : Matrix (Fin 2) (Fin 2) ℂ)
      = threeDirDerivCLM X₁ X₂ v := rfl

private lemma threeDirDerivCLE_toCLM_eq
    {X₁ X₂ : Matrix (Fin 2) (Fin 2) ℂ}
    (hX₁ : X₁ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (hX₂ : X₂ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (h_LI : ∀ (a b : ℝ), (a : ℂ) • X₁ + (b : ℂ) • X₂ = 0 → a = 0 ∧ b = 0) :
    ((threeDirDerivCLE hX₁ hX₂ h_LI) :
        (ℝ × ℝ × ℝ) →L[ℝ] ↥(SU2LieAlgebra.tracelessSkewHermitian (Fin 2)))
      = threeDirDerivCLM_ts hX₁ hX₂ := by
  apply ContinuousLinearMap.ext
  intro v
  apply Subtype.ext
  rfl

/-! ### §4.6. Continuous projection onto `𝔰𝔲(2)`

Pick any ℝ-linear complement of `𝔰𝔲(2)` in `Matrix _ _ ℂ`, obtain the
continuous linear projection `tsProj : Matrix →L[ℝ] ↥𝔰𝔲(2)`. The
projection is identity on `𝔰𝔲(2)` (as a Submodule) and a CLM by
finite-dim auto-continuity.
-/

private noncomputable def tsCompl :
    Submodule ℝ (Matrix (Fin 2) (Fin 2) ℂ) :=
  Classical.choose (Submodule.exists_isCompl
    (SU2LieAlgebra.tracelessSkewHermitian (Fin 2)))

private lemma ts_isCompl_tsCompl :
    IsCompl (SU2LieAlgebra.tracelessSkewHermitian (Fin 2)) tsCompl :=
  Classical.choose_spec (Submodule.exists_isCompl
    (SU2LieAlgebra.tracelessSkewHermitian (Fin 2)))

private noncomputable def tsProj :
    Matrix (Fin 2) (Fin 2) ℂ →L[ℝ]
      ↥(SU2LieAlgebra.tracelessSkewHermitian (Fin 2)) :=
  LinearMap.toContinuousLinearMap
    ((SU2LieAlgebra.tracelessSkewHermitian (Fin 2)).linearProjOfIsCompl
      tsCompl ts_isCompl_tsCompl)

/-- `tsProj` is identity on `↥𝔰𝔲(2)` (after the subtype inclusion). -/
private lemma tsProj_apply_of_mem
    {Y : Matrix (Fin 2) (Fin 2) ℂ}
    (hY : Y ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2)) :
    tsProj Y = ⟨Y, hY⟩ := by
  show LinearMap.toContinuousLinearMap _ Y = _
  rw [LinearMap.coe_toContinuousLinearMap']
  -- linearProjOfIsCompl on a member of `ts` returns the canonical lift.
  exact Submodule.linearProjOfIsCompl_apply_left ts_isCompl_tsCompl ⟨Y, hY⟩

/-- `tsProj ∘ threeDirDerivCLM = threeDirDerivCLM_ts` (since the image of the
derivative lies in `𝔰𝔲(2)`). -/
private lemma tsProj_comp_threeDirDerivCLM_eq
    {X₁ X₂ : Matrix (Fin 2) (Fin 2) ℂ}
    (hX₁ : X₁ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (hX₂ : X₂ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2)) :
    tsProj.comp (threeDirDerivCLM X₁ X₂) = threeDirDerivCLM_ts hX₁ hX₂ := by
  apply ContinuousLinearMap.ext
  intro v
  have hmem := threeDirDerivCLM_apply_mem_ts hX₁ hX₂ v
  rw [ContinuousLinearMap.comp_apply, tsProj_apply_of_mem hmem]
  rfl


/-- **Headline — Cartan v4 final step discharge**.

Given a closed subgroup `H ≤ SU(2)` and two ℝ-LI `X₁, X₂ ∈ 𝔰𝔲(2)` with
`exp(ℝ•X_i) ⊆ H`, we have `H = ⊤`.

**Proof structure.**

1. Apply `exp_bracket_mem_H` (Step 1) to extend to `exp(ℝ•[X₁,X₂]) ⊆ H`.
2. The triple `(X₁, X₂, [X₁,X₂])` spans `𝔰𝔲(2)` (by
   `tracelessSkewHermitian_X_Y_bracket_spans`).
3. By the local diffeomorphism `expAmbient : 𝔰𝔲(2) ∩ source → SU(2) ∩ target`
   (`SU2_nhd_one_covered_by_exp_ts`), every SU(2) element near 1 = exp Y for some Y ∈ ts.
4. The 3-direction parametrization
   `f(a, b, c) := exp(a • X₁) · exp(b • X₂) · exp(c • [X₁, X₂])`
   has injective ℝ-LI Jacobian at 0 (so by IFT, its image covers a nbhd
   of 1 in SU(2)). Each `f(a, b, c) ∈ H` by Step 1 + group closure.
5. So `1 ∈ interior(H)`, hence by
   `SU2_subgroup_eq_top_of_one_mem_interior`, `H = ⊤`. -/
theorem CartanFinalStep_SU2_v4_holds : CartanFinalStep_SU2_v4 := by
  intro H hH_closed h_witness
  obtain ⟨X₁, X₂, hX₁_ts, hX₂_ts, h_expX₁, h_expX₂, h_LI⟩ := h_witness
  -- Step 1: extend to exp(ℝ•[X₁,X₂]) ⊆ H
  have h_expBracket : ∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
      M ∈ H ∧ M.val = SU2MatrixExp.expAmbient
        (((t : ℝ) : ℂ) • (X₁ * X₂ - X₂ * X₁)) :=
    fun t => exp_bracket_mem_H H hH_closed hX₁_ts hX₂_ts h_expX₁ h_expX₂ t
  -- Step 2: by group closure, every threeDirProduct value is in H.val.
  have h_Φ_in_H : ∀ v : ℝ × ℝ × ℝ,
      ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
        M ∈ H ∧ M.val = threeDirProduct X₁ X₂ v :=
    threeDirProduct_mem_H_val H h_expX₁ h_expX₂ h_expBracket
  -- Step 3: ℝ-LI of (X₁, X₂, [X₁, X₂]) via shipped substrate.
  have h3LI : ∀ a b c : ℝ,
      (a : ℂ) • X₁ + (b : ℂ) • X₂ + (c : ℂ) • (X₁ * X₂ - X₂ * X₁) = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 :=
    SU2LieAlgebra.tracelessSkewHermitian_X_Y_bracket_lin_indep hX₁_ts hX₂_ts h_LI
  -- Step 4: spanning lemma (any Y ∈ ts is a real linear combination).
  have h3spans : ∀ {Y : Matrix (Fin 2) (Fin 2) ℂ},
      Y ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2) →
      ∃ a b c : ℝ, Y = (a : ℂ) • X₁ + (b : ℂ) • X₂
        + (c : ℂ) • (X₁ * X₂ - X₂ * X₁) :=
    fun {Y} hY =>
      SU2LieAlgebra.tracelessSkewHermitian_X_Y_bracket_spans hX₁_ts hX₂_ts h_LI hY
  -- Step 5: IFT composition. Show 1 ∈ interior(H) in ↥SU(2).
  apply SKEFTHawking.FKLW.OneParameterSubgroupSU2.SU2_subgroup_eq_top_of_one_mem_interior
  -- Φ has strict F-derivative threeDirDerivCLM at 0.
  have h_Φ_deriv :
      HasStrictFDerivAt (threeDirProduct X₁ X₂) (threeDirDerivCLM X₁ X₂) 0 :=
    threeDirProduct_hasStrictFDerivAt_zero X₁ X₂
  -- su2Log has strict F-derivative = identity at 1 (shipped substrate).
  have h_su2Log_deriv :
      HasStrictFDerivAt OneParameterSubgroupSU2.su2Log
        (ContinuousLinearMap.id ℝ (Matrix (Fin 2) (Fin 2) ℂ)) 1 :=
    OneParameterSubgroupSU2.su2Log_hasStrictFDerivAt_one
  -- Ψ := su2Log ∘ Φ has strict F-derivative threeDirDerivCLM at 0.
  have h_Φ_zero : threeDirProduct X₁ X₂ 0 = 1 := threeDirProduct_zero X₁ X₂
  have h_Ψ_deriv :
      HasStrictFDerivAt (fun v => OneParameterSubgroupSU2.su2Log (threeDirProduct X₁ X₂ v))
        ((ContinuousLinearMap.id ℝ _).comp (threeDirDerivCLM X₁ X₂)) 0 := by
    have hpre : HasStrictFDerivAt OneParameterSubgroupSU2.su2Log
        (ContinuousLinearMap.id ℝ (Matrix (Fin 2) (Fin 2) ℂ))
        (threeDirProduct X₁ X₂ 0) := by rw [h_Φ_zero]; exact h_su2Log_deriv
    exact hpre.comp 0 h_Φ_deriv
  have h_Ψ_deriv' :
      HasStrictFDerivAt (fun v => OneParameterSubgroupSU2.su2Log (threeDirProduct X₁ X₂ v))
        (threeDirDerivCLM X₁ X₂) 0 := by
    have h_eq : (ContinuousLinearMap.id ℝ _).comp (threeDirDerivCLM X₁ X₂)
        = threeDirDerivCLM X₁ X₂ := ContinuousLinearMap.id_comp _
    rw [← h_eq]; exact h_Ψ_deriv
  -- ψ_ts := tsProj ∘ Ψ : ℝ³ → ↥𝔰𝔲(2) has derivative threeDirDerivCLM_ts at 0.
  have h_ψ_ts_deriv :
      HasStrictFDerivAt
        (fun v => tsProj (OneParameterSubgroupSU2.su2Log (threeDirProduct X₁ X₂ v)))
        (threeDirDerivCLM_ts hX₁_ts hX₂_ts) 0 := by
    have h_clm_comp : tsProj.comp (threeDirDerivCLM X₁ X₂)
        = threeDirDerivCLM_ts hX₁_ts hX₂_ts :=
      tsProj_comp_threeDirDerivCLM_eq hX₁_ts hX₂_ts
    rw [← h_clm_comp]
    exact tsProj.hasStrictFDerivAt.comp 0 h_Ψ_deriv'
  -- Convert to CLE form for IFT.
  have h_ψ_ts_deriv_CLE :
      HasStrictFDerivAt
        (fun v => tsProj (OneParameterSubgroupSU2.su2Log (threeDirProduct X₁ X₂ v)))
        ((threeDirDerivCLE hX₁_ts hX₂_ts h_LI :
            (ℝ × ℝ × ℝ) →L[ℝ]
              ↥(SU2LieAlgebra.tracelessSkewHermitian (Fin 2)))) 0 := by
    rw [threeDirDerivCLE_toCLM_eq]
    exact h_ψ_ts_deriv
  -- Apply IFT to get an open partial homeomorphism.
  set ψ_ts : (ℝ × ℝ × ℝ) → ↥(SU2LieAlgebra.tracelessSkewHermitian (Fin 2)) :=
    fun v => tsProj (OneParameterSubgroupSU2.su2Log (threeDirProduct X₁ X₂ v)) with hψ_ts_def
  let φ_ph := h_ψ_ts_deriv_CLE.toOpenPartialHomeomorph ψ_ts
  have hφ_ph_src : (0 : ℝ × ℝ × ℝ) ∈ φ_ph.source :=
    h_ψ_ts_deriv_CLE.mem_toOpenPartialHomeomorph_source
  have hφ_ph_coe : (φ_ph : (ℝ × ℝ × ℝ) → _) = ψ_ts :=
    HasStrictFDerivAt.toOpenPartialHomeomorph_coe h_ψ_ts_deriv_CLE
  -- ψ_ts(0) = 0 in ↥𝔰𝔲(2).
  have h_ψ_ts_zero : ψ_ts 0 = (0 : ↥(SU2LieAlgebra.tracelessSkewHermitian (Fin 2))) := by
    simp only [hψ_ts_def, h_Φ_zero, OneParameterSubgroupSU2.su2Log_one, map_zero]
  -- φ_ph.target is an open nbhd of 0 in ↥𝔰𝔲(2).
  have hφ_target_open : IsOpen φ_ph.target := φ_ph.open_target
  have h_zero_in_target :
      (0 : ↥(SU2LieAlgebra.tracelessSkewHermitian (Fin 2))) ∈ φ_ph.target := by
    rw [← h_ψ_ts_zero, ← hφ_ph_coe]; exact φ_ph.map_source hφ_ph_src
  -- Now construct a nbhd V of 1 in Matrix such that for h ∈ V ∩ SU(2), h ∈ H.val.
  -- V := (su2Log)⁻¹(tsProj⁻¹(φ_ph.target))
  --      ∩ target_of_expAmbientPartialHomeo
  --      ∩ V_log (the §9.11 nbhd where su2Log h ∈ ts).
  obtain ⟨V_log, hV_log_nhd, hV_log_su2Log_ts⟩ :=
    OneParameterSubgroupSU2.Su2LogMem_on_nhd_one
  -- W is the §81 nbhd where SU(2)-elements are exp(Y) for Y ∈ ts ∩ source.
  obtain ⟨W, hW_nhd, hW_cover⟩ :=
    SKEFTHawking.FKLW.OneParameterSubgroupSU2.SU2_nhd_one_covered_by_exp_ts
  -- χ : Matrix → ↥ts defined by χ h := tsProj (su2Log h). Continuous at 1.
  have h_χ_cont :
      ContinuousAt (fun h => tsProj (OneParameterSubgroupSU2.su2Log h))
        (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    have h_su2Log_contAt :
        ContinuousAt OneParameterSubgroupSU2.su2Log
          (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
      OneParameterSubgroupSU2.su2Log_continuousOn.continuousAt
        OneParameterSubgroupSU2.expAmbientPartialHomeo_target_mem_nhds_one
    exact tsProj.continuous.continuousAt.comp h_su2Log_contAt
  have h_χ_one : tsProj (OneParameterSubgroupSU2.su2Log
      (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      (0 : ↥(SU2LieAlgebra.tracelessSkewHermitian (Fin 2))) := by
    rw [OneParameterSubgroupSU2.su2Log_one, map_zero]
  -- Preimage of φ_ph.target under χ is a nbhd of 1.
  have h_χ_pullback :
      (fun h => tsProj (OneParameterSubgroupSU2.su2Log h)) ⁻¹' φ_ph.target ∈
        nhds (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    apply h_χ_cont.preimage_mem_nhds
    rw [h_χ_one]
    exact hφ_target_open.mem_nhds h_zero_in_target
  -- Composite map F : Matrix → Matrix, F h = Φ(φ_ph.symm(tsProj(su2Log h))).
  -- F(1) = 1 (since su2Log 1 = 0, tsProj 0 = 0, φ_ph.symm 0 = 0, Φ 0 = 1).
  -- F continuous at 1 — composition of continuous maps.
  have h_φ_symm_zero : φ_ph.symm
      (0 : ↥(SU2LieAlgebra.tracelessSkewHermitian (Fin 2))) = (0 : ℝ × ℝ × ℝ) := by
    have h0_src : (0 : ℝ × ℝ × ℝ) ∈ φ_ph.source := hφ_ph_src
    have h_left := φ_ph.left_inv h0_src
    have h_eq : (φ_ph : (ℝ × ℝ × ℝ) → _) (0 : ℝ × ℝ × ℝ) =
        (0 : ↥(SU2LieAlgebra.tracelessSkewHermitian (Fin 2))) := by
      rw [hφ_ph_coe, h_ψ_ts_zero]
    rw [← h_eq]
    exact h_left
  -- Continuity of the composite F at 1.
  have h_F_one : threeDirProduct X₁ X₂ (φ_ph.symm
      (tsProj (OneParameterSubgroupSU2.su2Log (1 : Matrix (Fin 2) (Fin 2) ℂ)))) = 1 := by
    rw [OneParameterSubgroupSU2.su2Log_one, map_zero, h_φ_symm_zero, h_Φ_zero]
  have h_F_cont :
      ContinuousAt (fun h => threeDirProduct X₁ X₂ (φ_ph.symm
          (tsProj (OneParameterSubgroupSU2.su2Log h))))
        (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    have h_su2Log_contAt :
        ContinuousAt OneParameterSubgroupSU2.su2Log
          (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
      OneParameterSubgroupSU2.su2Log_continuousOn.continuousAt
        OneParameterSubgroupSU2.expAmbientPartialHomeo_target_mem_nhds_one
    have h_tsProj_su2Log :
        ContinuousAt (fun h => tsProj (OneParameterSubgroupSU2.su2Log h))
          (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
      tsProj.continuous.continuousAt.comp h_su2Log_contAt
    -- φ_ph.symm is continuous at (tsProj (su2Log 1)) = 0.
    -- To avoid ambiguity in ContinuousAt.comp, we provide the factoring explicitly.
    set χ : Matrix (Fin 2) (Fin 2) ℂ →
        ↥(SU2LieAlgebra.tracelessSkewHermitian (Fin 2)) :=
      fun h => tsProj (OneParameterSubgroupSU2.su2Log h) with hχ_def
    have h_χ_cont' : ContinuousAt χ (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
      h_tsProj_su2Log
    have h_one_target :
        (0 : ↥(SU2LieAlgebra.tracelessSkewHermitian (Fin 2))) ∈ φ_ph.target := by
      rw [← h_ψ_ts_zero, ← hφ_ph_coe]; exact φ_ph.map_source hφ_ph_src
    have h_φsym_at_chi1 : ContinuousAt φ_ph.symm (χ (1 : Matrix _ _ ℂ)) := by
      show ContinuousAt φ_ph.symm (tsProj (OneParameterSubgroupSU2.su2Log _))
      rw [h_χ_one]
      exact φ_ph.continuousAt_symm h_one_target
    have h_φsym_su2Log :
        ContinuousAt (fun h => φ_ph.symm (χ h))
          (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
      h_φsym_at_chi1.comp h_χ_cont'
    -- threeDirProduct has strict F-deriv at 0, hence continuous at 0.
    set R : Matrix (Fin 2) (Fin 2) ℂ → ℝ × ℝ × ℝ :=
      fun h => φ_ph.symm (χ h) with hR_def
    have h_R_cont : ContinuousAt R (1 : Matrix _ _ ℂ) := h_φsym_su2Log
    have h_Φ_cont_at_zero :
        ContinuousAt (threeDirProduct X₁ X₂) (0 : ℝ × ℝ × ℝ) :=
      h_Φ_deriv.continuousAt
    have hR_one_eq_zero : R 1 = (0 : ℝ × ℝ × ℝ) := by
      show φ_ph.symm (tsProj (OneParameterSubgroupSU2.su2Log 1)) = 0
      rw [OneParameterSubgroupSU2.su2Log_one, map_zero, h_φ_symm_zero]
    have h_Φ_cont_at_R1 :
        ContinuousAt (threeDirProduct X₁ X₂) (R 1) := by
      rw [hR_one_eq_zero]; exact h_Φ_cont_at_zero
    exact h_Φ_cont_at_R1.comp h_R_cont
  -- F⁻¹(target ∩ V_log) is a nbhd of 1.
  have h_F_pullback :
      (fun h => threeDirProduct X₁ X₂ (φ_ph.symm
          (tsProj (OneParameterSubgroupSU2.su2Log h)))) ⁻¹'
        (OneParameterSubgroupSU2.expAmbientPartialHomeo.target ∩ V_log) ∈
        nhds (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    apply h_F_cont.preimage_mem_nhds
    rw [h_F_one]
    exact Filter.inter_mem
      OneParameterSubgroupSU2.expAmbientPartialHomeo_target_mem_nhds_one
      hV_log_nhd
  -- Take intersection: V includes F-preimage condition.
  set V := (fun h => tsProj (OneParameterSubgroupSU2.su2Log h)) ⁻¹' φ_ph.target
      ∩ OneParameterSubgroupSU2.expAmbientPartialHomeo.target ∩ V_log ∩ W
      ∩ ((fun h => threeDirProduct X₁ X₂ (φ_ph.symm
          (tsProj (OneParameterSubgroupSU2.su2Log h)))) ⁻¹'
        (OneParameterSubgroupSU2.expAmbientPartialHomeo.target ∩ V_log)) with hV_def
  have hV_nhd : V ∈ nhds (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    refine Filter.inter_mem
      (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem h_χ_pullback ?_) ?_) hW_nhd)
      h_F_pullback
    · exact OneParameterSubgroupSU2.expAmbientPartialHomeo_target_mem_nhds_one
    · exact hV_log_nhd
  -- Show 1 ∈ interior(H) via the nhds reformulation.
  rw [mem_interior_iff_mem_nhds]
  -- Show H.val ∈ nhds (1 : ↥SU(2)) by superset: (Subtype.val ⁻¹' V) ∈ nhds 1 ⊆ H.val.
  apply Filter.mem_of_superset
  · -- (Subtype.val ⁻¹' V) ∈ nhds (1 : ↥SU(2)).
    exact continuous_subtype_val.continuousAt.preimage_mem_nhds (by
      show V ∈ nhds (Subtype.val (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)))
      have : (Subtype.val (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix _ _ ℂ) = 1 := rfl
      rw [this]; exact hV_nhd)
  · -- Subset of H.val.
    intro g hg
    -- g : ↥SU(2) with g.val ∈ V.
    have hg_χ : tsProj (OneParameterSubgroupSU2.su2Log
        (g : Matrix (Fin 2) (Fin 2) ℂ)) ∈ φ_ph.target := hg.1.1.1.1
    have hg_target : (g : Matrix (Fin 2) (Fin 2) ℂ) ∈
        OneParameterSubgroupSU2.expAmbientPartialHomeo.target := hg.1.1.1.2
    have hg_Vlog : (g : Matrix (Fin 2) (Fin 2) ℂ) ∈ V_log := hg.1.1.2
    have hg_su2 : (g : Matrix (Fin 2) (Fin 2) ℂ) ∈
        Matrix.specialUnitaryGroup (Fin 2) ℂ := g.property
    have hg_F : threeDirProduct X₁ X₂ (φ_ph.symm
        (tsProj (OneParameterSubgroupSU2.su2Log (g : Matrix (Fin 2) (Fin 2) ℂ)))) ∈
        OneParameterSubgroupSU2.expAmbientPartialHomeo.target ∩ V_log := hg.2
    -- Y := su2Log(g.val) ∈ ts (by §9.11).
    have hY_ts : OneParameterSubgroupSU2.su2Log (g : Matrix (Fin 2) (Fin 2) ℂ) ∈
        SU2LieAlgebra.tracelessSkewHermitian (Fin 2) :=
      hV_log_su2Log_ts (g : Matrix (Fin 2) (Fin 2) ℂ) hg_Vlog hg_target hg_su2
    -- tsProj Y = ⟨Y, hY_ts⟩.
    have h_tsProj_Y : tsProj (OneParameterSubgroupSU2.su2Log
        (g : Matrix (Fin 2) (Fin 2) ℂ)) =
        ⟨OneParameterSubgroupSU2.su2Log (g : Matrix (Fin 2) (Fin 2) ℂ), hY_ts⟩ :=
      tsProj_apply_of_mem hY_ts
    -- ⟨Y, hY_ts⟩ ∈ φ_ph.target.
    have h_lift_in_target : (⟨OneParameterSubgroupSU2.su2Log
        (g : Matrix (Fin 2) (Fin 2) ℂ), hY_ts⟩ :
        ↥(SU2LieAlgebra.tracelessSkewHermitian (Fin 2))) ∈ φ_ph.target := by
      rw [← h_tsProj_Y]; exact hg_χ
    -- Recover v with ψ_ts v = ⟨Y, _⟩.
    set v : ℝ × ℝ × ℝ := φ_ph.symm
      ⟨OneParameterSubgroupSU2.su2Log (g : Matrix (Fin 2) (Fin 2) ℂ), hY_ts⟩ with hv_def
    have hv_source : v ∈ φ_ph.source := φ_ph.map_target h_lift_in_target
    have h_ψ_ts_v : ψ_ts v = ⟨OneParameterSubgroupSU2.su2Log
        (g : Matrix (Fin 2) (Fin 2) ℂ), hY_ts⟩ := by
      have h_eq : (φ_ph : (ℝ × ℝ × ℝ) → _) v = _ := φ_ph.right_inv h_lift_in_target
      rw [hφ_ph_coe] at h_eq
      exact h_eq
    -- v = φ_ph.symm (tsProj (su2Log g.val)), so the F-preimage gives Φ v ∈ target ∩ V_log.
    have h_v_eq : v = φ_ph.symm
        (tsProj (OneParameterSubgroupSU2.su2Log (g : Matrix (Fin 2) (Fin 2) ℂ))) := by
      rw [hv_def, h_tsProj_Y]
    have hΦv_target : threeDirProduct X₁ X₂ v ∈
        OneParameterSubgroupSU2.expAmbientPartialHomeo.target := by
      rw [h_v_eq]; exact hg_F.1
    have hΦv_Vlog : threeDirProduct X₁ X₂ v ∈ V_log := by
      rw [h_v_eq]; exact hg_F.2
    have hΦv_su2 : threeDirProduct X₁ X₂ v ∈
        Matrix.specialUnitaryGroup (Fin 2) ℂ :=
      threeDirProduct_mem_specialUnitary hX₁_ts hX₂_ts v
    -- su2Log(Φ v) ∈ ts by §9.11.
    have hsu2LogΦv_ts : OneParameterSubgroupSU2.su2Log (threeDirProduct X₁ X₂ v) ∈
        SU2LieAlgebra.tracelessSkewHermitian (Fin 2) :=
      hV_log_su2Log_ts (threeDirProduct X₁ X₂ v) hΦv_Vlog hΦv_target hΦv_su2
    -- tsProj(su2Log(Φ v)) = ⟨su2Log(Φ v), hsu2LogΦv_ts⟩.
    have h_tsProj_Φv : tsProj (OneParameterSubgroupSU2.su2Log (threeDirProduct X₁ X₂ v))
        = ⟨OneParameterSubgroupSU2.su2Log (threeDirProduct X₁ X₂ v), hsu2LogΦv_ts⟩ :=
      tsProj_apply_of_mem hsu2LogΦv_ts
    -- ψ_ts v = tsProj (su2Log (Φ v)).
    have h_ψ_ts_v_eq : ψ_ts v = tsProj
        (OneParameterSubgroupSU2.su2Log (threeDirProduct X₁ X₂ v)) := rfl
    -- Combining: ⟨su2Log(Φ v), _⟩ = ⟨Y, _⟩, so su2Log(Φ v) = Y = su2Log(g.val).
    have h_log_eq : OneParameterSubgroupSU2.su2Log (threeDirProduct X₁ X₂ v)
        = OneParameterSubgroupSU2.su2Log (g : Matrix (Fin 2) (Fin 2) ℂ) := by
      have h1 : (⟨OneParameterSubgroupSU2.su2Log (threeDirProduct X₁ X₂ v),
          hsu2LogΦv_ts⟩ :
          ↥(SU2LieAlgebra.tracelessSkewHermitian (Fin 2))) =
          ⟨OneParameterSubgroupSU2.su2Log (g : Matrix (Fin 2) (Fin 2) ℂ), hY_ts⟩ := by
        rw [← h_tsProj_Φv, ← h_ψ_ts_v_eq, h_ψ_ts_v]
      exact Subtype.mk_eq_mk.mp h1
    -- Apply expAmbient: Φ v = g.val (both in target).
    have h_Φv_eq_g : threeDirProduct X₁ X₂ v = (g : Matrix (Fin 2) (Fin 2) ℂ) := by
      have h1 := OneParameterSubgroupSU2.expAmbient_su2Log hΦv_target
      have h2 := OneParameterSubgroupSU2.expAmbient_su2Log hg_target
      rw [h_log_eq] at h1
      exact h1.symm.trans h2
    -- Now: Φ v ∈ H.val, so g ∈ H.
    obtain ⟨M, hM_mem, hM_val⟩ := h_Φ_in_H v
    have h_M_eq : (M : Matrix (Fin 2) (Fin 2) ℂ) = (g : Matrix _ _ ℂ) := by
      rw [hM_val]; exact h_Φv_eq_g
    have h_M_g : M = g := Subtype.ext h_M_eq
    exact h_M_g ▸ hM_mem

/-! ## §5. F.21 unconditional culmination

Combining `CartanFinalStep_SU2_v4_holds` (this module) with
`H_Fib_v4_witness_unconditional` (`OneParameterSubgroupSU2.lean §80`)
and the shipped chain `fibonacci_density_F21_from_cartan_v4_only`,
F.21 Fibonacci density in SU(3)₂ ↪ SU(2) becomes **fully unconditional**.

This is the **culmination of the Phase 6p Wave 2c.4a-R4.2.d arc** (Phase
5 Step 13 Path (i) FINAL ship), bringing the project's tracked-Prop count
on the F.21 chain to zero. -/

/-- **F.21 Fibonacci density UNCONDITIONAL** (culminating headline).

Composes `CartanFinalStep_SU2_v4_holds` (this module's Step 1+2/3/4
discharge) with `H_Fib_v4_witness_unconditional` (the H_Fib-specific
v4 witness from §80) and the shipped chain
`fibonacci_density_F21_from_cartan_v4_only`. -/
theorem fibonacci_density_F21_unconditional :
    AharonovAradBridge.DenseInSpecialUnitary 3 2
      (fun b => (ρ_Fib_SU2 b : Matrix (Fin 2) (Fin 2) ℂ)) :=
  SKEFTHawking.FKLW.OneParameterSubgroupSU2.fibonacci_density_F21_from_cartan_v4_only
    CartanFinalStep_SU2_v4_holds

end SKEFTHawking.FKLW
