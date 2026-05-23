/-
SK_EFT_Hawking Phase 6t Path A SHIP (2026-05-22 PM):
**Constructive Dawson-Nielsen Solovay-Kitaev recursion** for the Fibonacci-anyon
braid representation in SU(2).

This module ships the CONSTRUCTIVE variant of the per-step Solovay-Kitaev
refinement: instead of `Classical.choose`-based existence (used by
`SolovayKitaevRecursion.solovayKitaev_compile_strict`), the output braid
word is a VISIBLE Dawson-Nielsen composition

    skApproxC (n+1) U = V_n_braid * groupCommutator A_F_braid A_G_braid

where `V_n_braid = skApproxC n U`, and `A_F_braid, A_G_braid` are recursive
approximations of `exp(i•F)` and `exp(i•G)` respectively, with `F, G`
provided by the traceless balanced commutator construction
(`balanced_commutator_general_axis_lie_traceless`, Path A Step 1).

## Path A overview

  - Step 1 (SHIPPED in SU2BalancedCommutator.lean):
    `balanced_commutator_general_axis_lie_traceless` — traceless companion.
  - Step 2 (this module §1): SU(2) lifting helper `expIsu2`.
  - Step 3 (this module §2): Constructive `skApproxC` definition.
  - Step 4 (this module §3): 11-step inductive error bound proof.
  - Step 5 (this module §4): Constructive strict headline.

## Pipeline Invariant compliance

  - Invariant #10 (no `maxHeartbeats`): RESPECTED.
  - Invariant #15 (no new axioms): RESPECTED.

Primary source: Dawson & Nielsen, *Quantum Info. & Comp.* 6 (2006), 81–95;
                arXiv:quant-ph/0505030, §3.1-3.2 (the recursion).
-/

import Mathlib
import SKEFTHawking.FKLW.SolovayKitaevRecursion
import SKEFTHawking.FKLW.OneParameterSubgroupSU2

set_option autoImplicit false

namespace SKEFTHawking.FKLW.SolovayKitaevPathA

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

open Matrix SKEFTHawking SKEFTHawking.FKLW
  SKEFTHawking.FKLW.SU2BalancedCommutator
  SKEFTHawking.FKLW.FibonacciEpsilonNet
  SKEFTHawking.FKLW.SolovayKitaevRecursion
  SKEFTHawking.FKLW.OneParameterSubgroupSU2

/-! ## 1. SU(2) lifting helper for traceless Hermitian Lie-algebra elements

For `F : Matrix (Fin 2) (Fin 2) ℂ` Hermitian + traceless, `Complex.I • F` is
in the Lie algebra `𝔰𝔲(2) = tracelessSkewHermitian (Fin 2)` and therefore
`exp(I • F) ∈ SU(2)` via the unconditionally-discharged determinant lemma
`DetExpZeroOnSu2_SU2_discharged` (shipped 2026-05-22 PM). -/

/-- For `F : Matrix (Fin 2) (Fin 2) ℂ` Hermitian and traceless,
`Complex.I • F ∈ tracelessSkewHermitian (Fin 2)`. -/
lemma I_smul_mem_tracelessSkewHermitian_of_hermitian_traceless
    {F : Matrix (Fin 2) (Fin 2) ℂ} (hF : F.IsHermitian) (htr : F.trace = 0) :
    (Complex.I • F) ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2) := by
  refine ⟨?_, ?_⟩
  · -- (Complex.I • F).conjTranspose = -(Complex.I • F)
    show (Complex.I • F).conjTranspose = -(Complex.I • F)
    rw [Matrix.conjTranspose_smul]
    rw [show F.conjTranspose = F from hF]
    rw [show (star Complex.I : ℂ) = -Complex.I from by
        rw [Complex.star_def]; rw [Complex.conj_I]]
    rw [neg_smul]
  · -- (Complex.I • F).trace = 0
    show (Complex.I • F).trace = 0
    rw [Matrix.trace_smul, htr, smul_zero]

/-- **Path A Step 2 — SU(2) lift of `exp(I • F)` for F Hermitian + traceless**.

For F Hermitian and traceless in `Matrix (Fin 2) (Fin 2) ℂ`, the matrix
exponential `exp(I • F)` lies in `SU(2)`. This is the constructive lift
needed by `skApproxC`'s recursive case to call itself on the SU(2)-valued
intermediates `exp(I • F)` and `exp(I • G)` produced by the traceless
balanced commutator. -/
noncomputable def expIsu2
    (F : Matrix (Fin 2) (Fin 2) ℂ) (hF : F.IsHermitian) (htr : F.trace = 0) :
    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  ⟨SU2MatrixExp.expAmbient (Complex.I • F),
   expAmbient_mem_specialUnitary_of_DetExpZeroOnSu2
     DetExpZeroOnSu2_SU2_discharged
     (I_smul_mem_tracelessSkewHermitian_of_hermitian_traceless hF htr)⟩

/-- `expIsu2` value equals `expAmbient (I • F)`. -/
@[simp]
theorem expIsu2_val (F : Matrix (Fin 2) (Fin 2) ℂ) (hF : F.IsHermitian)
    (htr : F.trace = 0) :
    (expIsu2 F hF htr : Matrix (Fin 2) (Fin 2) ℂ) =
      SU2MatrixExp.expAmbient (Complex.I • F) := rfl

/-! ## 2. Small substrate for the per-step Dawson-Nielsen composition

Helper lemmas for normalizing the residual matrix log into the unit-norm
Hermitian traceless form required by `balanced_commutator_general_axis_lie_traceless`. -/

/-- Real-scalar multiplication preserves the Hermitian property. -/
lemma IsHermitian_real_smul {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : M.IsHermitian) (c : ℝ) : ((c : ℂ) • M).IsHermitian := by
  show ((c : ℂ) • M).conjTranspose = (c : ℂ) • M
  rw [Matrix.conjTranspose_smul,
      show star (c : ℂ) = (c : ℂ) from by
        rw [Complex.star_def, Complex.conj_ofReal],
      show M.conjTranspose = M from hM]

/-- Scalar multiplication of a traceless matrix is traceless. -/
lemma smul_trace_zero {M : Matrix (Fin 2) (Fin 2) ℂ}
    (htr : M.trace = 0) (c : ℂ) : (c • M).trace = 0 := by
  rw [Matrix.trace_smul, htr, smul_zero]

/-- Norm of a real-scalar multiple. -/
lemma norm_real_smul (c : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖((c : ℂ) • M)‖ = |c| * ‖M‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]

/-- Normalizing a nonzero matrix gives unit norm. -/
lemma norm_normalize {M : Matrix (Fin 2) (Fin 2) ℂ} (h : 0 < ‖M‖) :
    ‖((1 / ‖M‖ : ℝ) : ℂ) • M‖ = 1 := by
  rw [norm_real_smul, abs_of_pos (by positivity : (0:ℝ) < 1 / ‖M‖)]
  field_simp

/-- For `h ∈ SU(2)`, `(-Complex.I) • Y_h h` is Hermitian.

The Bloch-sphere matrix log `Y_h h` lands in `tracelessSkewHermitian (Fin 2)`
(per `SU2_Y_h_mem_tracelessSkewHermitian`). Multiplying by `-i` flips
skew-Hermitian to Hermitian. -/
lemma neg_I_smul_Y_h_isHermitian
    {h : Matrix (Fin 2) (Fin 2) ℂ}
    (hh : h ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ((-Complex.I) • Y_h h).IsHermitian := by
  have hY_skew : (Y_h h).IsSkewHermitian :=
    (SU2_Y_h_mem_tracelessSkewHermitian hh).1
  show ((-Complex.I) • Y_h h).conjTranspose = ((-Complex.I) • Y_h h)
  rw [Matrix.conjTranspose_smul,
      show (star (-Complex.I) : ℂ) = Complex.I from by
        rw [star_neg, Complex.star_def, Complex.conj_I, neg_neg],
      show (Y_h h).conjTranspose = -(Y_h h) from hY_skew,
      smul_neg, neg_smul]

/-- For `h ∈ SU(2)`, `(-Complex.I) • Y_h h` is traceless. -/
lemma neg_I_smul_Y_h_trace_zero
    {h : Matrix (Fin 2) (Fin 2) ℂ}
    (hh : h ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ((-Complex.I) • Y_h h).trace = 0 := by
  have hY_tr : (Y_h h).trace = 0 :=
    (SU2_Y_h_mem_tracelessSkewHermitian hh).2
  rw [Matrix.trace_smul, hY_tr, smul_zero]

/-! ## 3. Constructive `skApproxC` definition (Path A Step 3b)

The Dawson-Nielsen recursion implemented as a visible compositional
function. At level 0, `skApproxC` falls back to the Wave 3 ε₀-net. At
level (n+1), `skApproxC` performs ONE explicit Dawson-Nielsen step:

  V_{n+1} := V_n · groupCommutator (skApproxC n A_F) (skApproxC n A_G)

where `V_n := skApproxC n U`, `A_F := exp(I•F)`, `A_G := exp(I•G)`, and
F, G are the traceless balanced commutator decomposition of the
normalized residual log `H_unit := (1/θ)·H` with `H := -i·Y_h(U·V_n⁻¹)`.

The validity branch (θ in `(0, 1]`) covers the inductive regime when
the level-n error is bounded by `2·ε₀`; outside this regime the
function falls back to V_n_braid (this happens at level 0 when the
ε₀-net already exhausts the precision budget).

Decidability of `0 < θ ∧ θ ≤ 1` is provided by `Classical.propDecidable`
via `open Classical in`.

The F, G extraction logic is factored into the helper `dnStepFG` (returning
a `DNStepData` struct that bundles F, G with their Hermitian + traceless
properties) so that the recursive `skApproxC` body stays small enough to
avoid elaboration timeouts. -/

/-- Bundle of (F, G) matrices with Hermitian + traceless properties,
returned by `dnStepFG`. -/
structure DNStepData where
  F : Matrix (Fin 2) (Fin 2) ℂ
  G : Matrix (Fin 2) (Fin 2) ℂ
  hF_herm : F.IsHermitian
  hG_herm : G.IsHermitian
  hF_tr : F.trace = 0
  hG_tr : G.trace = 0

open Classical in
/-- **Path A — F, G extraction helper for one Dawson-Nielsen step**.

Given the current level-n braid word `V_n_braid` and target `U`, extract
the (F, G) pair (with Hermitian + traceless proofs) used to build the
level-(n+1) composition via the traceless balanced commutator. Falls back
to `(0, 0)` when the residual is outside the valid regime
(`‖H‖ ∉ (0, 1]`). -/
noncomputable def dnStepFG
    (V_n_braid : FibonacciBraidWord)
    (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) : DNStepData :=
  let V_n : ↥(specialUnitaryGroup (Fin 2) ℂ) := ρ_Fib_SU2 V_n_braid
  -- Δ := V_n⁻¹ U is the residual; V_n · Δ = U ensures the level-(n+1)
  -- composition `V_n · groupCommutator(A_F, A_G) ≈ V_n · Δ = U`
  let Δ : ↥(specialUnitaryGroup (Fin 2) ℂ) := V_n⁻¹ * U
  let H : Matrix (Fin 2) (Fin 2) ℂ := ((-Complex.I) : ℂ) • Y_h Δ.val
  let θ : ℝ := ‖H‖
  if h : 0 < θ ∧ θ ≤ 1 then
    let H_unit : Matrix (Fin 2) (Fin 2) ℂ := ((1 / θ : ℝ) : ℂ) • H
    let hH_herm : H.IsHermitian := neg_I_smul_Y_h_isHermitian Δ.property
    let hH_tr : H.trace = 0 := neg_I_smul_Y_h_trace_zero Δ.property
    let hH_unit_herm : H_unit.IsHermitian :=
      IsHermitian_real_smul hH_herm (1 / θ)
    let hH_unit_tr : H_unit.trace = 0 := smul_trace_zero hH_tr _
    let hH_unit_norm : ‖H_unit‖ = 1 := norm_normalize h.1
    let ex := balanced_commutator_general_axis_lie_traceless
                H_unit hH_unit_herm hH_unit_tr hH_unit_norm θ h.1.le h.2
    { F := ex.choose
      G := ex.choose_spec.choose
      hF_herm := ex.choose_spec.choose_spec.1
      hG_herm := ex.choose_spec.choose_spec.2.1
      hF_tr := ex.choose_spec.choose_spec.2.2.1
      hG_tr := ex.choose_spec.choose_spec.2.2.2.1 }
  else
    { F := 0, G := 0
      hF_herm := Matrix.isHermitian_zero
      hG_herm := Matrix.isHermitian_zero
      hF_tr := Matrix.trace_zero (Fin 2) ℂ
      hG_tr := Matrix.trace_zero (Fin 2) ℂ }

/-- **Path A Step 3 — Constructive Dawson-Nielsen Solovay-Kitaev recursion**.

For every level `n` and target `U ∈ SU(2)`, `skApproxC n U` returns a
Fibonacci braid word constructed as a level-n Dawson-Nielsen composition.

  - Level 0: the Wave 3 ε₀-net's nearest-neighbor approximation.
  - Level (n+1): the visible composition
    `V_n · groupCommutator (skApproxC n (expIsu2 F)) (skApproxC n (expIsu2 G))`
    where F, G are the traceless balanced commutator decomposition
    of the residual matrix log (via `dnStepFG`).

This makes the per-step DN structure visible in the output type, in
contrast to `solovayKitaev_compile_strict`'s `Classical.choose`-based
opaque extraction. -/
noncomputable def skApproxC :
    ℕ → ↥(specialUnitaryGroup (Fin 2) ℂ) → FibonacciBraidWord
  | 0, U => fibonacciEpsilonNet_findNearest U ε₀ ε₀_pos
  | n + 1, U =>
    let V_n_braid : FibonacciBraidWord := skApproxC n U
    let data : DNStepData := dnStepFG V_n_braid U
    let A_F : ↥(specialUnitaryGroup (Fin 2) ℂ) :=
      expIsu2 data.F data.hF_herm data.hF_tr
    let A_G : ↥(specialUnitaryGroup (Fin 2) ℂ) :=
      expIsu2 data.G data.hG_herm data.hG_tr
    let A_F_braid : FibonacciBraidWord := skApproxC n A_F
    let A_G_braid : FibonacciBraidWord := skApproxC n A_G
    V_n_braid * (A_F_braid * A_G_braid * A_F_braid⁻¹ * A_G_braid⁻¹)

/-- Level-0 unfolding: the base case is the ε₀-net's nearest-neighbor word. -/
lemma skApproxC_zero (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) :
    skApproxC 0 U = fibonacciEpsilonNet_findNearest U ε₀ ε₀_pos := rfl

/-- Level-(n+1) unfolding: the visible DN composition structure. -/
lemma skApproxC_succ (n : ℕ) (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) :
    skApproxC (n + 1) U =
      let V_n_braid := skApproxC n U
      let data := dnStepFG V_n_braid U
      let A_F := expIsu2 data.F data.hF_herm data.hF_tr
      let A_G := expIsu2 data.G data.hG_herm data.hG_tr
      V_n_braid * (skApproxC n A_F * skApproxC n A_G *
                    (skApproxC n A_F)⁻¹ * (skApproxC n A_G)⁻¹) := rfl

/-! ## 4. Inductive error bound (Path A Step 4)

The level-n error bound: for every level `n`, `‖ρ_Fib_SU2 (skApproxC n U) - U‖
≤ ε_seq K_compose (2·ε₀) n`, where `ε_seq` is the Dawson-Nielsen recurrence
sequence (defined in `EpsilonSeq.lean`).

Level-0 (base case) is shipped here. The level-(n+1) inductive case (the
substantive Dawson-Nielsen analysis) is deferred to Step 4b (next session,
~250-400 LoC).

Per-step error bound chain (Step 4b plan, per memory file
`project_phase6t_strict_headline_2026_05_22.md`):

  1. IH: ‖V_n - U‖ ≤ ε_n
  2. ‖Δ - 1‖ ≤ √2·ε_n via `SU2_linftyOpNorm_le_sqrt_two` on V_n⁻¹
  3. Verify ‖Δ - 1‖ < 1/4 (holds since √2·ε_n ≤ √2·2·ε₀ ≪ 1/4)
  4. §82: ‖H_skew‖ ≤ 4·‖Δ-1‖ ≤ 4√2·ε_n  (via `Y_h_norm_le_four_norm_sub_one`)
  5. H = -i·H_skew Hermitian + traceless (via §2 substrate)
  6. θ := ‖H‖ ≤ 4√2·ε_n
  7. Verify θ ≤ 1 (holds for ε_n ≪ 1/(4√2) ≈ 0.177)
  8. Task #34 (strengthened, §1 Step 1): F, G with ‖F‖,‖G‖ ≤ √(θ/2)
  9. Recurse: ‖ρ A_F - exp(iF)‖ ≤ ε_n, ‖ρ A_G - exp(iG)‖ ≤ ε_n via IH
  10. Compose: ρ A_{n+1} = V_n · groupCommutator(ρ A_F, ρ A_G)
  11. Error: ‖result - U‖ ≤ cubic + stability ≤ K_compose · ε_n^(3/2)
-/

/-- **Level-0 base case of `skApproxC` error bound (UNCONDITIONAL)**.

The base case approximation is exactly the Wave 3 ε₀-net nearest-neighbor,
which is guaranteed within `2·ε₀` of any target. This matches the
`ε_seq K_compose (2·ε₀) 0` value (= `2·ε₀` by `ε_seq_zero`). -/
theorem skApproxC_zero_error_bound
    (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) :
    ‖(ρ_Fib_SU2 (skApproxC 0 U) : Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
      SKEFTHawking.FKLW.EpsilonSeq.ε_seq K_compose (2 * ε₀) 0 := by
  rw [SKEFTHawking.FKLW.EpsilonSeq.ε_seq_zero, skApproxC_zero]
  -- ε₀-net base case: nearest-neighbor approximation within 2·ε₀
  have h := fibonacciEpsilonNet_findNearest_approx_opNorm U ε₀ ε₀_pos
  -- The bound is exactly 2·ε₀
  exact h

/-! ## 5. Step 4 substrate lemmas

Reusable substrate for the level-(n+1) inductive error bound. Each lemma
encapsulates one of the 11 sub-steps of the DN error analysis. -/

/-- **Residual norm bound**: for `V, U ∈ SU(2)`, the residual `V⁻¹·U - 1`
has linftyOp norm at most `√2 · ‖V - U‖`.

Proof: `V⁻¹·U - 1 = V⁻¹·(U - V)`, then ‖V⁻¹‖ ≤ √2 (SU(2) bound) and
`‖U - V‖ = ‖V - U‖` by norm symmetry. -/
lemma residual_norm_le_sqrt_two_mul
    (V U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ‖((V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) - (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
      Real.sqrt 2 *
        ‖(V : Matrix (Fin 2) (Fin 2) ℂ) - (U : Matrix (Fin 2) (Fin 2) ℂ)‖ := by
  -- Use subtype-level mul-val to expose V⁻¹.val * U.val
  have h_mul_val : ((V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) =
                   (V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val *
                   U.val := rfl
  rw [h_mul_val]
  -- V⁻¹.val * U.val - 1 = V⁻¹.val * (U.val - V.val)  (since V⁻¹.val * V.val = 1)
  have h_V_inv_mem : (V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val ∈
                      Matrix.specialUnitaryGroup (Fin 2) ℂ := (V⁻¹).property
  have h_V_inv_norm : ‖(V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val‖ ≤
                      Real.sqrt 2 := SU2_linftyOpNorm_le_sqrt_two h_V_inv_mem
  -- V⁻¹.val * V.val = (V⁻¹ * V).val = (1 : SU(2)).val = 1
  have h_inv_left : (V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val * V.val = 1 := by
    have h := inv_mul_cancel V
    have : ((V⁻¹ * V : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ) =
           (V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val * V.val := rfl
    rw [← this, h]
    rfl
  -- Rewrite V⁻¹.val * U.val - 1 = V⁻¹.val * (U.val - V.val)
  have h_factor : (V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val * U.val -
                    (1 : Matrix (Fin 2) (Fin 2) ℂ) =
                  (V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val *
                    (U.val - V.val) := by
    rw [Matrix.mul_sub]
    rw [h_inv_left]
  rw [h_factor]
  -- ‖V⁻¹.val * (U.val - V.val)‖ ≤ ‖V⁻¹.val‖ · ‖U.val - V.val‖
  -- (sub-multiplicativity of linftyOp norm on matrices)
  have h_sub_mul := norm_mul_le
    ((V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val) (U.val - V.val)
  -- ‖U.val - V.val‖ = ‖V.val - U.val‖ by norm_sub_rev
  have h_norm_sub_sym : ‖U.val - V.val‖ = ‖V.val - U.val‖ := norm_sub_rev _ _
  calc ‖(V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val * (U.val - V.val)‖
      ≤ ‖(V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val‖ * ‖U.val - V.val‖
        := h_sub_mul
    _ ≤ Real.sqrt 2 * ‖U.val - V.val‖ := by
        gcongr
    _ = Real.sqrt 2 * ‖V.val - U.val‖ := by rw [h_norm_sub_sym]

/-- **H norm bound**: for `Δ ∈ SU(2)` with `‖Δ.val - 1‖ < 1/4`,
the `H = (-Complex.I) • Y_h Δ.val` matrix has linftyOp norm at most
`4 · ‖Δ.val - 1‖`.

Proof: `‖(-i) • Y_h Δ‖ = |i| · ‖Y_h Δ‖ = 1 · ‖Y_h Δ‖`, then apply
`Y_h_norm_le_four_norm_sub_one`. -/
lemma H_norm_le_four_norm_sub_one
    {Δ : Matrix (Fin 2) (Fin 2) ℂ}
    (hΔ : Δ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (h_small : ‖Δ - (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ < 1 / 4) :
    ‖((-Complex.I) • Y_h Δ : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
      4 * ‖Δ - (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ := by
  -- ‖(-i) • Y_h Δ‖ = ‖-i‖ · ‖Y_h Δ‖ = 1 · ‖Y_h Δ‖
  rw [norm_smul]
  have h_norm_neg_I : ‖(-Complex.I)‖ = 1 := by
    rw [norm_neg, Complex.norm_I]
  rw [h_norm_neg_I, one_mul]
  -- Apply Y_h_norm_le_four_norm_sub_one
  exact Y_h_norm_le_four_norm_sub_one hΔ h_small

/-- **Composite H norm bound from V_n - U residual**: for `V, U ∈ SU(2)`
with `√2·‖V - U‖ < 1/4`, the matrix `H = (-i)•Y_h(V⁻¹·U)` has linftyOp
norm at most `4√2·‖V - U‖`.

Composes `residual_norm_le_sqrt_two_mul` (Step 2) with
`H_norm_le_four_norm_sub_one` (Step 4). Captures Steps 2-4 of the DN
chain in a single substrate lemma. -/
lemma H_norm_bound_from_V_diff
    (V U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (h_small : Real.sqrt 2 *
        ‖(V : Matrix (Fin 2) (Fin 2) ℂ) - (U : Matrix (Fin 2) (Fin 2) ℂ)‖ < 1/4) :
    ‖((-Complex.I) • Y_h ((V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val)
        : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
      4 * Real.sqrt 2 *
        ‖(V : Matrix (Fin 2) (Fin 2) ℂ) - (U : Matrix (Fin 2) (Fin 2) ℂ)‖ := by
  set Δ := (V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) with hΔ_def
  have h_residual : ‖(Δ : Matrix (Fin 2) (Fin 2) ℂ) -
                      (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
                    Real.sqrt 2 *
                      ‖(V : Matrix (Fin 2) (Fin 2) ℂ) -
                        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ :=
    residual_norm_le_sqrt_two_mul V U
  have h_residual_lt : ‖(Δ : Matrix (Fin 2) (Fin 2) ℂ) -
                          (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ < 1/4 :=
    lt_of_le_of_lt h_residual h_small
  have h_H := H_norm_le_four_norm_sub_one Δ.property h_residual_lt
  calc ‖((-Complex.I) • Y_h Δ.val : Matrix (Fin 2) (Fin 2) ℂ)‖
      ≤ 4 * ‖(Δ : Matrix (Fin 2) (Fin 2) ℂ) -
              (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ := h_H
    _ ≤ 4 * (Real.sqrt 2 *
            ‖(V : Matrix (Fin 2) (Fin 2) ℂ) -
              (U : Matrix (Fin 2) (Fin 2) ℂ)‖) := by gcongr
    _ = 4 * Real.sqrt 2 *
        ‖(V : Matrix (Fin 2) (Fin 2) ℂ) -
          (U : Matrix (Fin 2) (Fin 2) ℂ)‖ := by ring

/-- **dnStepFG F-norm bound**: the F matrix extracted by `dnStepFG` has
norm bounded by `√(θ/2)` where `θ := ‖(-Complex.I) • Y_h Δ.val‖` (Δ is
the residual `V_n⁻¹·U`).

Proof: case-split on the validity branch.
  - Valid case (`0 < θ ∧ θ ≤ 1`): F comes from
    `balanced_commutator_general_axis_lie_traceless`, which gives
    `‖F‖ ≤ √(θ/2)` directly.
  - Invalid case: F = 0, so `‖F‖ = 0 ≤ √(θ/2)` (since θ ≥ 0). -/
lemma dnStepFG_F_norm_le_sqrt_theta_half
    (V_n_braid : FibonacciBraidWord)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    let V_n := ρ_Fib_SU2 V_n_braid
    let Δ := (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    let θ := ‖((-Complex.I) • Y_h Δ.val : Matrix (Fin 2) (Fin 2) ℂ)‖
    ‖(dnStepFG V_n_braid U).F‖ ≤ Real.sqrt (θ / 2) := by
  simp only [dnStepFG]
  split_ifs with h_valid
  · -- Valid branch: extract from balanced_commutator_general_axis_lie_traceless
    set Δ_local := (((ρ_Fib_SU2 V_n_braid)⁻¹ * U :
                       ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)))
    set H_local : Matrix (Fin 2) (Fin 2) ℂ :=
      ((-Complex.I) : ℂ) • Y_h Δ_local.val
    set θ_local : ℝ := ‖H_local‖
    -- The choose-spec gives ‖F‖ ≤ √(θ_local/2)
    have h_ex_spec :=
      (balanced_commutator_general_axis_lie_traceless
        (((1 / θ_local : ℝ) : ℂ) • H_local)
        (IsHermitian_real_smul (neg_I_smul_Y_h_isHermitian Δ_local.property)
          (1 / θ_local))
        (smul_trace_zero (neg_I_smul_Y_h_trace_zero Δ_local.property) _)
        (norm_normalize h_valid.1)
        θ_local h_valid.1.le h_valid.2).choose_spec.choose_spec
    exact h_ex_spec.2.2.2.2.1
  · -- Invalid branch: F = 0
    show ‖(0 : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ _
    rw [norm_zero]
    exact Real.sqrt_nonneg _

/-- **dnStepFG G-norm bound**: symmetric to `dnStepFG_F_norm_le_sqrt_theta_half`. -/
lemma dnStepFG_G_norm_le_sqrt_theta_half
    (V_n_braid : FibonacciBraidWord)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    let V_n := ρ_Fib_SU2 V_n_braid
    let Δ := (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    let θ := ‖((-Complex.I) • Y_h Δ.val : Matrix (Fin 2) (Fin 2) ℂ)‖
    ‖(dnStepFG V_n_braid U).G‖ ≤ Real.sqrt (θ / 2) := by
  simp only [dnStepFG]
  split_ifs with h_valid
  · set Δ_local := (((ρ_Fib_SU2 V_n_braid)⁻¹ * U :
                       ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)))
    set H_local : Matrix (Fin 2) (Fin 2) ℂ :=
      ((-Complex.I) : ℂ) • Y_h Δ_local.val
    set θ_local : ℝ := ‖H_local‖
    have h_ex_spec :=
      (balanced_commutator_general_axis_lie_traceless
        (((1 / θ_local : ℝ) : ℂ) • H_local)
        (IsHermitian_real_smul (neg_I_smul_Y_h_isHermitian Δ_local.property)
          (1 / θ_local))
        (smul_trace_zero (neg_I_smul_Y_h_trace_zero Δ_local.property) _)
        (norm_normalize h_valid.1)
        θ_local h_valid.1.le h_valid.2).choose_spec.choose_spec
    exact h_ex_spec.2.2.2.2.2.1
  · show ‖(0 : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ _
    rw [norm_zero]
    exact Real.sqrt_nonneg _

/-! ## 6. (next ship) Constructive strict headline

Step 5 of Path A. -/

end SKEFTHawking.FKLW.SolovayKitaevPathA
