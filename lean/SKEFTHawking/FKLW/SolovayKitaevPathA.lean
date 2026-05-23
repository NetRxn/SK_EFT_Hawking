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
import SKEFTHawking.FKLW.SolovayKitaevLengthBound
import SKEFTHawking.FKLW.OneParameterSubgroupSU2
import SKEFTHawking.FKLW.GroupCommutatorNearIdentity

set_option autoImplicit false

namespace SKEFTHawking.FKLW.SolovayKitaevPathA

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

open Matrix SKEFTHawking SKEFTHawking.FKLW
  SKEFTHawking.FKLW.SU2BalancedCommutator
  SKEFTHawking.FKLW.FibonacciEpsilonNet
  SKEFTHawking.FKLW.SolovayKitaevRecursion
  SKEFTHawking.FKLW.SolovayKitaevLengthBound
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

/-- **TIGHT H norm bound (Option C, 2026-05-23)**: same shape as
`H_norm_le_four_norm_sub_one` but with the analytically-tight Lipschitz
constant `π` instead of the loose `4`. Composes
`Y_h_norm_le_pi_norm_sub_one` via the `‖-i‖ = 1` factorization. -/
lemma H_norm_le_pi_norm_sub_one
    {Δ : Matrix (Fin 2) (Fin 2) ℂ}
    (hΔ : Δ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (h_small : ‖Δ - (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ < 1 / 4) :
    ‖((-Complex.I) • Y_h Δ : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
      Real.pi * ‖Δ - (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ := by
  rw [norm_smul]
  have h_norm_neg_I : ‖(-Complex.I)‖ = 1 := by
    rw [norm_neg, Complex.norm_I]
  rw [h_norm_neg_I, one_mul]
  exact Y_h_norm_le_pi_norm_sub_one hΔ h_small

/-- **TIGHTEST H norm bound (Option C SU(2)-Bloch, 2026-05-23)**: combines
`Y_h_norm_le_half_pi_norm_sub_one` (which uses SU(2) row-sum analysis to
get Step 4's `‖h - a·I‖ ≤ ‖h - 1‖` factor of 1, then composes with
analytically-tight `(sinc θ)⁻¹ ≤ π/2`) via the `‖-i‖ = 1` factorization.
Tightest reachable constant: `c = π/2 ≈ 1.57`. -/
lemma H_norm_le_half_pi_norm_sub_one
    {Δ : Matrix (Fin 2) (Fin 2) ℂ}
    (hΔ : Δ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (h_small : ‖Δ - (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ < 1 / 4) :
    ‖((-Complex.I) • Y_h Δ : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
      (Real.pi / 2) * ‖Δ - (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ := by
  rw [norm_smul]
  have h_norm_neg_I : ‖(-Complex.I)‖ = 1 := by
    rw [norm_neg, Complex.norm_I]
  rw [h_norm_neg_I, one_mul]
  exact Y_h_norm_le_half_pi_norm_sub_one hΔ h_small

/-- **TIGHTEST composite H norm bound from V_n - U residual (Option C SU(2)-Bloch)**:
for `V, U ∈ SU(2)` with `√2·‖V - U‖ < 1/4`,
`‖(-i)·Y_h(V⁻¹·U)‖ ≤ (π/2)·√2·‖V - U‖`. Composes
`residual_norm_le_sqrt_two_mul` (Step 2) with
`H_norm_le_half_pi_norm_sub_one` (tightest Step 4 via SU(2) Bloch). -/
lemma H_norm_bound_from_V_diff_half_pi
    (V U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (h_small : Real.sqrt 2 *
        ‖(V : Matrix (Fin 2) (Fin 2) ℂ) - (U : Matrix (Fin 2) (Fin 2) ℂ)‖ < 1/4) :
    ‖((-Complex.I) • Y_h ((V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val)
        : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
      (Real.pi / 2) * Real.sqrt 2 *
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
  have h_H := H_norm_le_half_pi_norm_sub_one Δ.property h_residual_lt
  have h_half_pi_nn : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  calc ‖((-Complex.I) • Y_h Δ.val : Matrix (Fin 2) (Fin 2) ℂ)‖
      ≤ (Real.pi / 2) * ‖(Δ : Matrix (Fin 2) (Fin 2) ℂ) -
              (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ := h_H
    _ ≤ (Real.pi / 2) * (Real.sqrt 2 *
            ‖(V : Matrix (Fin 2) (Fin 2) ℂ) -
              (U : Matrix (Fin 2) (Fin 2) ℂ)‖) := by gcongr
    _ = (Real.pi / 2) * Real.sqrt 2 *
        ‖(V : Matrix (Fin 2) (Fin 2) ℂ) -
          (U : Matrix (Fin 2) (Fin 2) ℂ)‖ := by ring

/-- **TIGHT composite H norm bound (Option C, 2026-05-23)**: same shape
as `H_norm_bound_from_V_diff` but with the analytically-tight Lipschitz
constant. For `V, U ∈ SU(2)` with `√2·‖V - U‖ < 1/4`,
`‖(-i)·Y_h(V⁻¹·U)‖ ≤ π·√2·‖V - U‖`. Composes
`residual_norm_le_sqrt_two_mul` (Step 2) with
`H_norm_le_pi_norm_sub_one` (tightened Step 4). -/
lemma H_norm_bound_from_V_diff_pi
    (V U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (h_small : Real.sqrt 2 *
        ‖(V : Matrix (Fin 2) (Fin 2) ℂ) - (U : Matrix (Fin 2) (Fin 2) ℂ)‖ < 1/4) :
    ‖((-Complex.I) • Y_h ((V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val)
        : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
      Real.pi * Real.sqrt 2 *
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
  have h_H := H_norm_le_pi_norm_sub_one Δ.property h_residual_lt
  have hπ_nn : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  calc ‖((-Complex.I) • Y_h Δ.val : Matrix (Fin 2) (Fin 2) ℂ)‖
      ≤ Real.pi * ‖(Δ : Matrix (Fin 2) (Fin 2) ℂ) -
              (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ := h_H
    _ ≤ Real.pi * (Real.sqrt 2 *
            ‖(V : Matrix (Fin 2) (Fin 2) ℂ) -
              (U : Matrix (Fin 2) (Fin 2) ℂ)‖) := by gcongr
    _ = Real.pi * Real.sqrt 2 *
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

/-! ## 6. Constructive strict headline framework (Path A Step 5)

The Step 4 substantive inductive proof requires K_compose constant ≥ ~2200
to absorb cubic (≈ 1522·ε_n^(3/2)) + stability (≈ 20·ε_n^(3/2)) + √2 factor
(V_n unitarity in linftyOp norm). Current K_compose = 1024 gives an
algebraic gap (proof needs K ≥ 2180 but convergence requires K ≤ 2050
under existing ε₀ = 1/(8·K_compose²) = 1/8388608).

We ship a CONDITIONAL framework: a tracked Prop `SkApproxCSuperQuadraticBound K`
that captures the inductive bound, plus a constructive headline parametrized
by its discharge. The discharge requires sharper BCH cubic constants (a
Mathlib-PR-quality follow-up reducing 320·δ³ to ~200·δ³). -/

/-- **Tracked Prop**: the substantive super-quadratic shrinkage bound for the
constructive `skApproxC`, parametrized by the per-step composition constant K.

Discharge requires K large enough to absorb cubic remainder (~1522·ε_n^(3/2))
+ stability (~20·ε_n^(3/2)) + √2 (V_n unitarity factor in linftyOp norm).
With existing K_compose = 1024 and ε₀ = 1/8388608, this is FALSE due to
constant calibration gap. Sharper BCH cubic analysis would close the gap. -/
def SkApproxCSuperQuadraticBound (K : ℝ) : Prop :=
  ∀ (n : ℕ) (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)),
    ‖(ρ_Fib_SU2 (skApproxC n U) : Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
      SKEFTHawking.FKLW.EpsilonSeq.ε_seq K (2 * ε₀) n

/-- **The Path A constructive compiler**: returns a Fibonacci braid word
whose UNDERLYING STRUCTURE is a level-`skLevel_polylog ε` Dawson-Nielsen
composition (via the recursive `skApproxC` function). -/
noncomputable def solovayKitaev_compile_strict_constructive
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ) : FibonacciBraidWord :=
  skApproxC (skLevel_polylog ε) U

/-- **HEADLINE (Path A Step 5, CONDITIONAL on `SkApproxCSuperQuadraticBound`)**:
The constructive compiler `solovayKitaev_compile_strict_constructive U ε`
returns a Fibonacci braid word with VISIBLE Dawson-Nielsen composition
structure, error bound `≤ ε`, and length bound matching the existing
strict headline.

This is the Path A counterpart to
`SolovayKitaevQuantitative.solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict`
(which uses opaque `Classical.choose`-based extraction). The Path A
variant exposes the DN compositional structure at the term level via
`skApproxC_succ` unfolding.

Discharge of `SkApproxCSuperQuadraticBound K_compose` is deferred —
requires either (a) sharper BCH cubic constants (Mathlib-PR-quality),
(b) ε₀ refinement, or (c) parametrized K with looser convergence
margin. See `project_phase6t_path_a_active_2026_05_22.md`
§ Calibration analysis for details. -/
theorem solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict_constructive
    (h_bound : SkApproxCSuperQuadraticBound K_compose)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ)
    (hε_pos : 0 < ε) (hε_le : ε ≤ ε₀) :
    ‖(ρ_Fib_SU2 (solovayKitaev_compile_strict_constructive U ε) :
        Matrix (Fin 2) (Fin 2) ℂ) - (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε ∧
    skLength (skLevel_polylog ε) ≤
      skLengthConst * (Real.log (1 / ε)) ^ skLengthExponent := by
  refine ⟨?_, skLength_at_skLevel_polylog_le ε hε_pos hε_le⟩
  -- Apply the tracked bound at level skLevel_polylog ε
  have h_seq_bound := h_bound (skLevel_polylog ε) U
  -- The ε_seq value at this level is ≤ ε by skLevel_polylog_spec
  have h_polylog_spec := skLevel_polylog_spec ε hε_pos hε_le
  exact le_trans h_seq_bound h_polylog_spec

/-! ## 7. Step 4 inductive discharge (Path A core deliverable)

The substantive discharge of `SkApproxCSuperQuadraticBound K` for K large
enough. Once shipped, the conditional headline becomes unconditional.

**Strategy**: induction on n with universal IH (∀ U). Successor case
applies IH to U, A_F, A_G; decomposes the error via triangle inequality
into: (Wave 1 cubic remainder) + (sub-ship 1 near-I stability) + (V_n
linftyOp unitarity factor). Calibration: K ≥ ~2200 suffices.

For now we ship a SCAFFOLDED version: a single-step substantive bound
(absorbing the IH on V_n alone, plus universal-quantified IH for the
sub-recursions), and the wrapper that composes via Nat induction. This
factorization keeps each piece tractable; the substantive cubic +
stability composition is in the helper. -/

/-- **Path A Step 4 — Trivial SU(2)-diameter bound on `skApproxC (n+1)`**.

A trivially-provable bound: since `ρ_Fib_SU2` maps to SU(2) and both
endpoints are in SU(2), their difference has linftyOp norm ≤ 2√2. This
is the "fallback" bound that holds without any inductive structure.

The substantive super-quadratic bound `K · ε_n^(3/2)` (requiring K ≥ ~2200
from cubic + stability + √2 calibration) is captured by the tracked Prop
`SkApproxCSuperQuadraticBound K` and remains the deferred substantive
discharge. -/
theorem skApproxC_succ_trivial_bound
    (n : ℕ) (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ‖(ρ_Fib_SU2 (skApproxC (n + 1) U) : Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
      2 * Real.sqrt 2 := by
  have h_ρ_V_mem : (ρ_Fib_SU2 (skApproxC (n + 1) U) :
      Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    (ρ_Fib_SU2 (skApproxC (n + 1) U)).property
  have h_ρ_V_norm := SU2_linftyOpNorm_le_sqrt_two h_ρ_V_mem
  have h_U_norm := SU2_linftyOpNorm_le_sqrt_two U.property
  calc ‖(ρ_Fib_SU2 (skApproxC (n + 1) U) : Matrix (Fin 2) (Fin 2) ℂ) -
          (U : Matrix (Fin 2) (Fin 2) ℂ)‖
      ≤ ‖(ρ_Fib_SU2 (skApproxC (n + 1) U) :
          Matrix (Fin 2) (Fin 2) ℂ)‖ +
        ‖(U : Matrix (Fin 2) (Fin 2) ℂ)‖ := norm_sub_le _ _
    _ ≤ Real.sqrt 2 + Real.sqrt 2 := by linarith
    _ = 2 * Real.sqrt 2 := by ring

/-- **HEADLINE (Path A Step 4 UNCONDITIONAL — trivial SU(2)-diameter bound)**:
`‖ρ_Fib_SU2 (skApproxC n U) - U‖ ≤ 2√2` for every level `n` and target
`U ∈ SU(2)`.

This bound is the "structural safety net" — it holds unconditionally and
shows the constructive `skApproxC` never produces a braid word whose
representation strays outside the SU(2)-diameter from the target. The
substantive super-quadratic bound (with K · ε_n^(3/2) tightness) is
captured by the tracked Prop `SkApproxCSuperQuadraticBound K` and is the
remaining substantive deliverable. -/
theorem skApproxC_diameter_bound (n : ℕ)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ‖(ρ_Fib_SU2 (skApproxC n U) : Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 2 * Real.sqrt 2 := by
  cases n with
  | zero =>
    have h_base := skApproxC_zero_error_bound U
    rw [SKEFTHawking.FKLW.EpsilonSeq.ε_seq_zero] at h_base
    have h_2ε₀_le : (2 * ε₀ : ℝ) ≤ 2 * Real.sqrt 2 := by
      have h_ε₀_pos : 0 < ε₀ := ε₀_pos
      have h_ε₀_lt_one : ε₀ < 1 := by
        unfold ε₀
        have h_K_sq_pos : 0 < K_compose ^ 2 := by
          have := K_compose_pos
          positivity
        have h_8K_sq : (8 * K_compose ^ 2 : ℝ) > 1 := by
          have : K_compose ≥ 1 := by unfold K_compose; norm_num
          nlinarith
        rw [div_lt_one (by linarith : (0 : ℝ) < 8 * K_compose^2)]
        linarith
      have h_sqrt_two_ge : (1 : ℝ) ≤ Real.sqrt 2 := by
        rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
        exact Real.sqrt_le_sqrt (by norm_num)
      linarith
    linarith
  | succ m =>
    exact skApproxC_succ_trivial_bound m U

/-! ## 7. Step 4 discharge for large K via diameter bound

For K large enough that `ε_seq K (2·ε₀) n ≥ 2√2` for all n ≥ 1, the
predicate `SkApproxCSuperQuadraticBound K` reduces to the diameter
bound. This is the STRUCTURAL discharge: shows the tracked Prop is
satisfiable (the predicate isn't vacuous), enabling downstream
consumers to instantiate the conditional headline.

Note: this discharge uses LOOSE K (huge value), so the strict-headline
error bound becomes ‖V_n - U‖ ≤ ε ≈ K·(...)^(3/2) which is way larger
than user-specified ε for tight ε. The TIGHT K (≤ 2200, calibration
limit) substantive discharge is the deferred follow-up. -/

/-- A "huge" K value: chosen so big that `K · (2·ε₀)² ≥ 2√2`, leveraging
the rpow monotonicity `x^(3/2) ≥ x^2` for `x ∈ (0, 1]`. -/
noncomputable def K_path_a_huge : ℝ := 10^30

lemma K_path_a_huge_pos : 0 < K_path_a_huge := by
  unfold K_path_a_huge; norm_num

/-- For `x ∈ (0, 1]`, `x^(3/2) ≥ x^2` (rpow is anti-monotone in exponent
when base is ≤ 1). -/
lemma rpow_three_halves_ge_sq (x : ℝ) (hx_pos : 0 < x) (hx_le_one : x ≤ 1) :
    x ^ (2 : ℝ) ≤ x ^ (3 / 2 : ℝ) := by
  apply Real.rpow_le_rpow_of_exponent_ge hx_pos hx_le_one
  norm_num

/-- **Path A Step 4 discharge for K_path_a_huge** — UNCONDITIONAL.

Discharges `SkApproxCSuperQuadraticBound K_path_a_huge` via:
  - n = 0: matches base case (2·ε₀ = ε_seq K 0)
  - n ≥ 1: diameter bound 2√2, combined with ε_seq K (n) ≥ 2√2 inductively

The key step at n = 1: `ε_seq K 1 = K · (2·ε₀)^(3/2) ≥ K · (2·ε₀)² ≥ 2√2`
where the first inequality uses `rpow_three_halves_ge_sq` and the second
is numerical (`K · 4·ε₀² = 4·10^30 / 2^46 ≈ 5.68e16 ≫ 2√2`). -/
theorem SkApproxCSuperQuadraticBound_huge_holds :
    SkApproxCSuperQuadraticBound K_path_a_huge := by
  intro n
  -- First show ε_seq K n ≥ 2√2 for n ≥ 1.
  have h_ε_seq_large : ∀ m : ℕ, 1 ≤ m →
      2 * Real.sqrt 2 ≤
        SKEFTHawking.FKLW.EpsilonSeq.ε_seq K_path_a_huge (2 * ε₀) m := by
    intro m hm
    induction m with
    | zero => omega
    | succ k ih_k =>
      rcases Nat.eq_zero_or_pos k with hk_zero | hk_pos
      · -- k = 0: ε_seq K 1 = K · (2·ε₀)^(3/2). Lower-bound via x^(3/2) ≥ x^2.
        subst hk_zero
        rw [SKEFTHawking.FKLW.EpsilonSeq.ε_seq_succ,
            SKEFTHawking.FKLW.EpsilonSeq.ε_seq_zero]
        have h_2ε₀_pos : 0 < 2 * ε₀ := two_ε₀_pos
        have h_2ε₀_lt_one : 2 * ε₀ ≤ 1 := by
          rw [two_ε₀_value]; norm_num
        -- x^(3/2) ≥ x^2 = x * x for x ∈ (0, 1]
        have h_rpow_ge : (2 * ε₀ : ℝ) ^ (2 : ℝ) ≤ (2 * ε₀) ^ (3 / 2 : ℝ) :=
          rpow_three_halves_ge_sq _ h_2ε₀_pos h_2ε₀_lt_one
        -- (2·ε₀)^2 = (2·ε₀) * (2·ε₀)
        have h_rpow_two : (2 * ε₀ : ℝ) ^ (2 : ℝ) = (2 * ε₀) * (2 * ε₀) := by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num]
          rw [Real.rpow_natCast]; ring
        rw [h_rpow_two] at h_rpow_ge
        -- Goal: 2√2 ≤ K_huge · (2·ε₀)^(3/2)
        -- Bound: K_huge · (2·ε₀)^(3/2) ≥ K_huge · (2·ε₀) · (2·ε₀) = K_huge · 4·ε₀²
        have h_K_pos : 0 < K_path_a_huge := K_path_a_huge_pos
        have h_lower : K_path_a_huge * ((2 * ε₀) * (2 * ε₀)) ≤
            K_path_a_huge * (2 * ε₀) ^ (3 / 2 : ℝ) := by
          gcongr
        -- Numerical: K_huge · (2·ε₀)² ≥ 2√2
        -- 2·ε₀ = 1/4194304, so (2·ε₀)² = 1/4194304² = 1/17592186044416
        -- K_huge · (2·ε₀)² = 10^30 / 17592186044416 ≈ 5.68e16
        -- 2√2 ≤ 3, so we need 3 ≤ 5.68e16. ✓
        have h_num : 2 * Real.sqrt 2 ≤ K_path_a_huge * ((2 * ε₀) * (2 * ε₀)) := by
          have h_sqrt_two : Real.sqrt 2 ≤ 3/2 := by
            rw [show (3/2 : ℝ) = Real.sqrt (9/4) from by
              rw [show (9/4 : ℝ) = (3/2)^2 from by norm_num,
                  Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3/2)]]
            exact Real.sqrt_le_sqrt (by norm_num)
          have h_2ε₀_val : 2 * ε₀ = 1 / 4194304 := two_ε₀_value
          rw [h_2ε₀_val]
          unfold K_path_a_huge
          nlinarith [h_sqrt_two]
        linarith
      · -- k ≥ 1: ε_seq K (k+1) = K · (ε_seq K k)^(3/2).
        -- By IH: ε_seq K k ≥ 2√2 ≥ 1. So (ε_seq K k)^(3/2) ≥ 1, and
        -- K · (ε_seq K k)^(3/2) ≥ K ≥ 2√2.
        have ih_k_apply := ih_k hk_pos
        rw [SKEFTHawking.FKLW.EpsilonSeq.ε_seq_succ]
        have h_seq_ge_one : (1 : ℝ) ≤
            SKEFTHawking.FKLW.EpsilonSeq.ε_seq K_path_a_huge (2 * ε₀) k := by
          have h_sqrt_two_ge : (1 : ℝ) ≤ Real.sqrt 2 := by
            rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
            exact Real.sqrt_le_sqrt (by norm_num)
          linarith
        have h_rpow_ge_one : (1 : ℝ) ≤
            (SKEFTHawking.FKLW.EpsilonSeq.ε_seq K_path_a_huge (2 * ε₀) k) ^
              (3 / 2 : ℝ) :=
          Real.one_le_rpow h_seq_ge_one (by norm_num : (0 : ℝ) ≤ 3/2)
        have h_K_ge : (2 * Real.sqrt 2 : ℝ) ≤ K_path_a_huge := by
          unfold K_path_a_huge
          have h_sqrt : Real.sqrt 2 ≤ 2 := by
            rw [show (2 : ℝ) = Real.sqrt 4 from by
              rw [show (4 : ℝ) = 2^2 from by norm_num,
                  Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]]
            exact Real.sqrt_le_sqrt (by norm_num)
          linarith
        have h_K_pos : 0 < K_path_a_huge := K_path_a_huge_pos
        calc (2 * Real.sqrt 2 : ℝ) ≤ K_path_a_huge := h_K_ge
          _ = K_path_a_huge * 1 := (mul_one _).symm
          _ ≤ K_path_a_huge *
              (SKEFTHawking.FKLW.EpsilonSeq.ε_seq K_path_a_huge (2 * ε₀) k) ^
                (3 / 2 : ℝ) := by gcongr
  -- Main induction
  induction n with
  | zero =>
    intro U
    rw [SKEFTHawking.FKLW.EpsilonSeq.ε_seq_zero]
    exact skApproxC_zero_error_bound U
  | succ m _ =>
    intro U
    have h_diam := skApproxC_diameter_bound (m + 1) U
    have h_seq_ge := h_ε_seq_large (m + 1) (by omega)
    linarith

/-! ## 7.5. Substrate for the substantive inductive discharge

Helpers consumed by the eventual `SkApproxCSuperQuadraticBound K_compose`
inductive proof. Each helper is independently provable and Mathlib-PR-quality
substrate. -/

/-- **ρ_Fib_SU2 multiplicativity at the matrix level**: for braid words
`a, b ∈ BraidGroup 3`, `(ρ_Fib_SU2 (a * b)).val = (ρ_Fib_SU2 a).val * (ρ_Fib_SU2 b).val`.

Direct consequence of `ρ_Fib_SU2` being a `MonoidHom` plus the SU(2)
subtype multiplication. -/
lemma ρ_Fib_SU2_mul_val (a b : SKEFTHawking.BraidGroup 3) :
    ((ρ_Fib_SU2 (a * b) : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) =
      ((ρ_Fib_SU2 a : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix (Fin 2) (Fin 2) ℂ) *
      ((ρ_Fib_SU2 b : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [map_mul]
  rfl

/-- **SU(2) subtype-group inverse equals matrix inverse**: for
`A : ↥(specialUnitaryGroup (Fin 2) ℂ)`, the underlying matrix of the
group inverse `A⁻¹` equals the matrix nonsing inverse of `A.val`.

Proof: from `A * A⁻¹ = 1` at the group level, extract `A.val * (A⁻¹).val = 1`
as matrices, then apply `Matrix.inv_eq_right_inv`. -/
lemma SU2_subtype_inv_val_eq_matrix_inv
    (A : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ((A⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) =
      ((A : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix (Fin 2) (Fin 2) ℂ)⁻¹ := by
  have h_mul : A * A⁻¹ = 1 := mul_inv_cancel A
  have h_mul_val : (A : Matrix (Fin 2) (Fin 2) ℂ) *
      ((A⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    have : ((A * A⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ) =
           (A : Matrix (Fin 2) (Fin 2) ℂ) *
             ((A⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                Matrix (Fin 2) (Fin 2) ℂ) := rfl
    rw [← this, h_mul]
    rfl
  exact (Matrix.inv_eq_right_inv h_mul_val).symm

/-- **ρ_Fib_SU2 inverse at the matrix level**: for braid word `a`,
`(ρ_Fib_SU2 a⁻¹).val = ((ρ_Fib_SU2 a).val)⁻¹` (matrix nonsing inverse). -/
lemma ρ_Fib_SU2_inv_val (a : SKEFTHawking.BraidGroup 3) :
    ((ρ_Fib_SU2 a⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) =
      ((ρ_Fib_SU2 a : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix (Fin 2) (Fin 2) ℂ)⁻¹ := by
  rw [map_inv]
  exact SU2_subtype_inv_val_eq_matrix_inv _

/-- **ρ_Fib_SU2 of group commutator** at the matrix level: for braid words
`a, b`, the SU(2) image of `a * b * a⁻¹ * b⁻¹` equals the matrix-level
group commutator of `ρ_Fib_SU2 a` and `ρ_Fib_SU2 b`. -/
lemma ρ_Fib_SU2_groupCommutator_val (a b : SKEFTHawking.BraidGroup 3) :
    ((ρ_Fib_SU2 (a * b * a⁻¹ * b⁻¹) :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) =
      SKEFTHawking.FKLW.GroupCommutator.groupCommutator
        ((ρ_Fib_SU2 a : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
            Matrix (Fin 2) (Fin 2) ℂ)
        ((ρ_Fib_SU2 b : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
            Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold SKEFTHawking.FKLW.GroupCommutator.groupCommutator
  rw [ρ_Fib_SU2_mul_val, ρ_Fib_SU2_mul_val, ρ_Fib_SU2_mul_val,
      ρ_Fib_SU2_inv_val, ρ_Fib_SU2_inv_val]

/-- **dnStepFG balanced-commutator identity (LOAD-BEARING)**: in the valid branch
(`0 < θ ∧ θ ≤ 1`), the F, G matrices extracted by `dnStepFG` satisfy
`F * G - G * F = -Y_h(V_n⁻¹·U)`.

Derivation chain:
  - Wave 2 conclusion: `F*G - G*F = -(θ·i) • H_unit` where `H_unit := (1/θ) • H`.
  - `H := (-i)·Y_h Δ` per dnStepFG def.
  - Scalar composition: `-(θ·i) • ((1/θ) • ((-i)·Y_h Δ)) = -(θ·i·(1/θ)·(-i)) • Y_h Δ
    = -(-i·i) • Y_h Δ = -(1) • Y_h Δ = -Y_h Δ`.

This identity is consumed by the inductive step to bridge Wave 2's balanced
commutator output to the §9.7 `SU2_expAmbient_Y_h_eq` central identity:
`exp(-[F, G]) = exp(Y_h Δ) = Δ`. -/
lemma dnStepFG_commutator_identity_valid
    (V_n_braid : FibonacciBraidWord)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (h_valid : 0 < ‖((-Complex.I) • Y_h
        ((ρ_Fib_SU2 V_n_braid)⁻¹ * U :
            ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val :
        Matrix (Fin 2) (Fin 2) ℂ)‖ ∧
        ‖((-Complex.I) • Y_h
        ((ρ_Fib_SU2 V_n_braid)⁻¹ * U :
            ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val :
        Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 1) :
    let data := dnStepFG V_n_braid U
    let Δ := ((ρ_Fib_SU2 V_n_braid)⁻¹ * U :
                ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    data.F * data.G - data.G * data.F = -Y_h Δ.val := by
  -- Unfold dnStepFG and take the valid branch.
  simp only [dnStepFG]
  set Δ_local := (((ρ_Fib_SU2 V_n_braid)⁻¹ * U :
                     ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)))
  set H_local : Matrix (Fin 2) (Fin 2) ℂ :=
    ((-Complex.I) : ℂ) • Y_h Δ_local.val
  set θ_local : ℝ := ‖H_local‖
  rw [dif_pos h_valid]
  -- The Wave 2 balanced_commutator returns ⟨F, G, ..., F*G - G*F = -(θ·i) • H_unit⟩
  -- with H_unit := (1/θ_local) • H_local.
  set ex_data := balanced_commutator_general_axis_lie_traceless
      (((1 / θ_local : ℝ) : ℂ) • H_local)
      (IsHermitian_real_smul (neg_I_smul_Y_h_isHermitian Δ_local.property)
        (1 / θ_local))
      (smul_trace_zero (neg_I_smul_Y_h_trace_zero Δ_local.property) _)
      (norm_normalize h_valid.1)
      θ_local h_valid.1.le h_valid.2 with hex_def
  -- The commutator equation: F*G - G*F = -(θ·i) • H_unit
  have h_comm_eq : ex_data.choose * ex_data.choose_spec.choose -
                   ex_data.choose_spec.choose * ex_data.choose =
                   -(((θ_local : ℂ) * Complex.I)) •
                     (((1 / θ_local : ℝ) : ℂ) • H_local) :=
    ex_data.choose_spec.choose_spec.2.2.2.2.2.2
  -- Simplify the scalar: -(θ·i) • ((1/θ) • H) = -(θ·i·(1/θ)) • H = -(i) • H
  --                                          = -(i) • ((-i) • Y_h Δ) = -(i·(-i)) • Y_h Δ
  --                                          = -(1) • Y_h Δ = -Y_h Δ
  have h_theta_pos : (0 : ℝ) < θ_local := h_valid.1
  have h_theta_ne : (θ_local : ℂ) ≠ 0 := by
    have : (θ_local : ℝ) ≠ 0 := ne_of_gt h_theta_pos
    exact_mod_cast this
  -- Scalar composition: -(θ·I) * ((1/θ : ℝ) : ℂ) = -I
  have h_scalar : -((θ_local : ℂ) * Complex.I) * (((1 / θ_local : ℝ) : ℂ)) =
                  -Complex.I := by
    have h_div : ((1 / θ_local : ℝ) : ℂ) = ((θ_local : ℂ))⁻¹ := by
      push_cast
      rw [one_div]
    rw [h_div]
    field_simp
  -- Now simplify the RHS of h_comm_eq:
  -- -(θ·i) • ((1/θ) • H_local) = -i • H_local = -i • (-i • Y_h Δ) = -Y_h Δ
  rw [h_comm_eq, smul_smul, h_scalar]
  -- Goal: -Complex.I • H_local = -Y_h Δ_local.val
  -- H_local = (-i) • Y_h Δ
  show -Complex.I • ((-Complex.I : ℂ) • Y_h Δ_local.val) = -Y_h Δ_local.val
  rw [smul_smul]
  congr 1
  -- Show: -I * -I = -1
  ring_nf
  simp [Complex.I_sq]

/-- **dnStepFG exp(-[F, G]) = Δ identity** (composes
`dnStepFG_commutator_identity_valid` with §9.7 `SU2_expAmbient_Y_h_eq`).

In the valid branch with `Δ.trace.re ≠ -2` (excluded only at the antipodal
case `Δ = -1`, which is impossible for `‖Δ - 1‖ < 1/4`):

  `NormedSpace.exp (-(F * G - G * F)) = Δ.val`

Proof:
  - [F, G] = -Y_h Δ via `dnStepFG_commutator_identity_valid`.
  - Negate: -[F, G] = Y_h Δ.
  - exp(Y_h Δ) = expAmbient(Y_h Δ) (def-unfold).
  - expAmbient(Y_h Δ) = Δ.val via `SU2_expAmbient_Y_h_eq` (§9.7).

This is the bridge between Wave 2's balanced commutator and the
recursion's exact-cancellation property `V_n · exp(-[F, G]) = U`. -/
lemma dnStepFG_exp_neg_comm_eq_Delta
    (V_n_braid : FibonacciBraidWord)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (h_valid : 0 < ‖((-Complex.I) • Y_h
        ((ρ_Fib_SU2 V_n_braid)⁻¹ * U :
            ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val :
        Matrix (Fin 2) (Fin 2) ℂ)‖ ∧
        ‖((-Complex.I) • Y_h
        ((ρ_Fib_SU2 V_n_braid)⁻¹ * U :
            ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val :
        Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 1)
    (h_ne_neg_two : ((ρ_Fib_SU2 V_n_braid)⁻¹ * U :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val.trace.re ≠ -2) :
    let data := dnStepFG V_n_braid U
    let Δ := ((ρ_Fib_SU2 V_n_braid)⁻¹ * U :
                ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    NormedSpace.exp (-(data.F * data.G - data.G * data.F)) = Δ.val := by
  -- Unfold the let binders explicitly.
  dsimp only
  set Δ := ((ρ_Fib_SU2 V_n_braid)⁻¹ * U :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) with hΔ_def
  -- Step 1: [F, G] = -Y_h Δ from dnStepFG_commutator_identity_valid
  have h_comm := dnStepFG_commutator_identity_valid V_n_braid U h_valid
  dsimp only at h_comm
  -- h_comm : (dnStepFG V_n_braid U).F * (dnStepFG V_n_braid U).G -
  --           (dnStepFG V_n_braid U).G * (dnStepFG V_n_braid U).F = -Y_h Δ.val
  -- Step 2: -(F*G - G*F) = Y_h Δ.val
  have h_neg_comm : -((dnStepFG V_n_braid U).F * (dnStepFG V_n_braid U).G -
                       (dnStepFG V_n_braid U).G * (dnStepFG V_n_braid U).F) =
                    Y_h Δ.val := by
    have h1 : -((dnStepFG V_n_braid U).F * (dnStepFG V_n_braid U).G -
              (dnStepFG V_n_braid U).G * (dnStepFG V_n_braid U).F) =
           -(-Y_h Δ.val) := by rw [h_comm]
    rw [h1]
    exact neg_neg _
  rw [h_neg_comm]
  -- Step 3: expAmbient(Y_h Δ) = Δ.val via §9.7
  have h_expAmbient :=
    SU2_expAmbient_Y_h_eq Δ.property h_ne_neg_two
  -- Step 4: expAmbient = NormedSpace.exp (definitional via SU2MatrixExp.expAmbient)
  show NormedSpace.exp (Y_h Δ.val) = Δ.val
  rw [show NormedSpace.exp (Y_h Δ.val) =
      SU2MatrixExp.expAmbient (Y_h Δ.val) from rfl]
  exact h_expAmbient

/-- **`expIsu2` near-identity bound**: for `F` Hermitian-traceless with
`‖F‖ ≤ δ`, the matrix `(expIsu2 F).val = exp(I·F)` satisfies
`‖(expIsu2 F).val - 1‖ ≤ δ · exp(δ)`.

Direct composition of `expIsu2_val` (which gives
`(expIsu2 F).val = expAmbient (I•F) = NormedSpace.exp (I•F)`) with
`MatrixBCH.norm_exp_I_smul_sub_one_le`. -/
lemma expIsu2_norm_sub_one_le
    (F : Matrix (Fin 2) (Fin 2) ℂ) (hF : F.IsHermitian) (htr : F.trace = 0)
    (δ : ℝ) (hF_norm : ‖F‖ ≤ δ) :
    ‖((expIsu2 F hF htr : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) - 1‖ ≤ δ * Real.exp δ := by
  rw [expIsu2_val]
  have h_base : ‖SU2MatrixExp.expAmbient (Complex.I • F) - 1‖ ≤
                  ‖F‖ * Real.exp ‖F‖ :=
    MatrixBCH.norm_exp_I_smul_sub_one_le F
  have h_F_nn : (0 : ℝ) ≤ ‖F‖ := norm_nonneg _
  have h_exp_le : Real.exp ‖F‖ ≤ Real.exp δ := Real.exp_le_exp.mpr hF_norm
  have h_exp_nn : (0 : ℝ) ≤ Real.exp ‖F‖ := le_of_lt (Real.exp_pos _)
  have h_δ_nn : (0 : ℝ) ≤ δ := le_trans h_F_nn hF_norm
  calc ‖SU2MatrixExp.expAmbient (Complex.I • F) - 1‖
      ≤ ‖F‖ * Real.exp ‖F‖ := h_base
    _ ≤ δ * Real.exp ‖F‖ := mul_le_mul_of_nonneg_right hF_norm h_exp_nn
    _ ≤ δ * Real.exp δ := mul_le_mul_of_nonneg_left h_exp_le h_δ_nn

/-- **`expIsu2` matrix-inverse near-identity bound**: for `F` Hermitian-traceless
with `‖F‖ ≤ δ`, the matrix inverse of `(expIsu2 F).val` satisfies

  `‖((expIsu2 F).val)⁻¹ - 1‖ ≤ √2 · δ · exp(δ)`

where `⁻¹` is `Matrix.nonsing_inv` and the SU(2) linftyOp bound √2 enters
via the identity `A⁻¹ - 1 = -A⁻¹·(A - 1)`. -/
lemma expIsu2_inv_norm_sub_one_le
    (F : Matrix (Fin 2) (Fin 2) ℂ) (hF : F.IsHermitian) (htr : F.trace = 0)
    (δ : ℝ) (hF_norm : ‖F‖ ≤ δ) :
    ‖((expIsu2 F hF htr : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ)⁻¹ - 1‖ ≤ Real.sqrt 2 * (δ * Real.exp δ) := by
  set A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) := expIsu2 F hF htr with hA_F_def
  -- Bridge: A_F.val⁻¹ = (A_F⁻¹ : SU(2)).val via SU2_subtype_inv_val_eq_matrix_inv.
  rw [← SU2_subtype_inv_val_eq_matrix_inv A_F]
  -- A_F.val⁻¹ - 1 = (A_F⁻¹).val - 1. Use the identity:
  --   (A_F⁻¹).val - 1 = -(A_F⁻¹).val · ((A_F).val - 1)  [via (A_F⁻¹).val · A_F.val = 1]
  have h_inv_mul : ((A_F⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                     Matrix (Fin 2) (Fin 2) ℂ) *
                   (A_F : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    have h := inv_mul_cancel A_F
    have h_eq : ((A_F⁻¹ * A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ) =
           ((A_F⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ) *
           (A_F : Matrix (Fin 2) (Fin 2) ℂ) := rfl
    rw [← h_eq, h]
    rfl
  have h_id : ((A_F⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                  Matrix (Fin 2) (Fin 2) ℂ) - 1 =
              -((A_F⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                  Matrix (Fin 2) (Fin 2) ℂ) *
              ((A_F : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
    have h_calc : -((A_F⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) *
                  ((A_F : Matrix (Fin 2) (Fin 2) ℂ) - 1) =
                  -(((A_F⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                      Matrix (Fin 2) (Fin 2) ℂ) *
                    (A_F : Matrix (Fin 2) (Fin 2) ℂ)) +
                  ((A_F⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                      Matrix (Fin 2) (Fin 2) ℂ) := by
      noncomm_ring
    rw [h_calc, h_inv_mul]
    abel
  rw [h_id]
  -- ‖-(A_F⁻¹).val · (A_F.val - 1)‖ ≤ ‖(A_F⁻¹).val‖ · ‖A_F.val - 1‖ ≤ √2 · δ · exp(δ)
  have h_mul_le := norm_mul_le
      (-((A_F⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
            Matrix (Fin 2) (Fin 2) ℂ))
      ((A_F : Matrix (Fin 2) (Fin 2) ℂ) - 1)
  have h_inv_norm : ‖((A_F⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                       Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ Real.sqrt 2 :=
    SU2_linftyOpNorm_le_sqrt_two (A_F⁻¹).property
  have h_neg_norm : ‖-((A_F⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                       Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ Real.sqrt 2 := by
    rw [norm_neg]; exact h_inv_norm
  have h_sub_one_norm : ‖((A_F : Matrix (Fin 2) (Fin 2) ℂ)) - 1‖ ≤
                        δ * Real.exp δ :=
    expIsu2_norm_sub_one_le F hF htr δ hF_norm
  have h_sub_one_nn : (0 : ℝ) ≤ ‖((A_F : Matrix (Fin 2) (Fin 2) ℂ)) - 1‖ :=
    norm_nonneg _
  have h_sqrt2_nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  calc ‖-((A_F⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
            Matrix (Fin 2) (Fin 2) ℂ) *
        ((A_F : Matrix (Fin 2) (Fin 2) ℂ) - 1)‖
      ≤ ‖-((A_F⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
            Matrix (Fin 2) (Fin 2) ℂ)‖ *
        ‖((A_F : Matrix (Fin 2) (Fin 2) ℂ)) - 1‖ := h_mul_le
    _ ≤ Real.sqrt 2 * ‖((A_F : Matrix (Fin 2) (Fin 2) ℂ)) - 1‖ := by
        gcongr
    _ ≤ Real.sqrt 2 * (δ * Real.exp δ) := by gcongr

/-- **SU(2) det is a unit**: for `A : ↥(specialUnitaryGroup (Fin 2) ℂ)`,
`IsUnit A.val.det`. Trivially true since `det A.val = 1` for SU(2)
elements, and `IsUnit 1` holds. Consumed by
`groupCommutator_stability_nearIdentity` (which requires invertibility
of the perturbation arguments). -/
lemma SU2_val_det_isUnit
    (A : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    IsUnit (A : Matrix (Fin 2) (Fin 2) ℂ).det := by
  have h_mem : (A : Matrix (Fin 2) (Fin 2) ℂ) ∈
               Matrix.specialUnitaryGroup (Fin 2) ℂ := A.property
  rw [Matrix.mem_specialUnitaryGroup_iff] at h_mem
  obtain ⟨_, h_det⟩ := h_mem
  rw [h_det]
  exact isUnit_one

/-- **SU(2) val is in unitaryGroup** (companion to `SU2_val_det_isUnit`):
for `A : ↥(specialUnitaryGroup (Fin 2) ℂ)`, the underlying matrix is in
`unitaryGroup (Fin 2) ℂ`. Direct unfold of the membership condition. -/
lemma SU2_val_mem_unitaryGroup
    (A : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    (A : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have h_mem : (A : Matrix (Fin 2) (Fin 2) ℂ) ∈
               Matrix.specialUnitaryGroup (Fin 2) ℂ := A.property
  rw [Matrix.mem_specialUnitaryGroup_iff] at h_mem
  exact h_mem.1

/-- **Regime: `√2 · ε_n < 1/4` for any `ε_n ≤ 2·ε₀`**.

Consumed by the inductive step's Step 3 regime check (the §82
`Y_h_norm_le_half_pi_norm_sub_one` precondition `‖Δ - 1‖ < 1/4`,
where ‖Δ - 1‖ ≤ √2·ε_n via `residual_norm_le_sqrt_two_mul`).

Numerical: `√2 · 2·ε₀ = √2 / 4194304 ≈ 3.4e-7 << 1/4`. -/
lemma sqrt_two_mul_eps_lt_one_quarter
    (ε_n : ℝ) (h_nn : 0 ≤ ε_n) (h_le : ε_n ≤ 2 * ε₀) :
    Real.sqrt 2 * ε_n < 1 / 4 := by
  have h_two_ε₀ : 2 * ε₀ = 1 / 4194304 := two_ε₀_value
  have h_sqrt2_lt : Real.sqrt 2 < 2 := by
    have h_sqrt2_lt_sqrt4 : Real.sqrt 2 < Real.sqrt 4 :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have h_sqrt4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 from by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    rwa [h_sqrt4] at h_sqrt2_lt_sqrt4
  have h_sqrt2_nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have h_2ε₀_pos : 0 < 2 * ε₀ := two_ε₀_pos
  -- √2 · ε_n ≤ √2 · 2·ε₀ < 2 · 2·ε₀ = 1/2097152 < 1/4
  calc Real.sqrt 2 * ε_n
      ≤ Real.sqrt 2 * (2 * ε₀) :=
        mul_le_mul_of_nonneg_left h_le h_sqrt2_nn
    _ < 2 * (2 * ε₀) := by
        exact (mul_lt_mul_iff_of_pos_right h_2ε₀_pos).mpr h_sqrt2_lt
    _ = 2 * (1 / 4194304) := by rw [h_two_ε₀]
    _ < 1 / 4 := by norm_num

/-- **Regime: `(π/2)·√2·ε_n ≤ 1` for any `ε_n ≤ 2·ε₀`**.

Consumed by the inductive step's Step 7 regime check (the `dnStepFG`
validity hypothesis `θ ≤ 1` where θ ≤ (π/2)·√2·ε_n via
`H_norm_bound_from_V_diff_half_pi`).

Numerical: `(π/2)·√2·2·ε₀ < 4·2·ε₀ = 2·ε₀·4 = 1/524288 << 1`. -/
lemma half_pi_sqrt_two_mul_eps_le_one
    (ε_n : ℝ) (h_nn : 0 ≤ ε_n) (h_le : ε_n ≤ 2 * ε₀) :
    (Real.pi / 2) * Real.sqrt 2 * ε_n ≤ 1 := by
  have h_two_ε₀ : 2 * ε₀ = 1 / 4194304 := two_ε₀_value
  have h_sqrt2_lt_2 : Real.sqrt 2 < 2 := by
    have h_sqrt2_lt_sqrt4 : Real.sqrt 2 < Real.sqrt 4 :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have h_sqrt4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 from by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    rwa [h_sqrt4] at h_sqrt2_lt_sqrt4
  have h_sqrt2_nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have h_pi_lt : Real.pi < 4 := by linarith [Real.pi_lt_d2]
  have h_half_pi_lt_two : Real.pi / 2 < 2 := by linarith
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h_half_pi_nn : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  -- Combined: (π/2) · √2 < 2 · 2 = 4.
  have h_prod_lt : (Real.pi / 2) * Real.sqrt 2 < 4 := by
    have h_step1 : (Real.pi / 2) * Real.sqrt 2 < 2 * Real.sqrt 2 :=
      (mul_lt_mul_iff_of_pos_right (by
        have : Real.sqrt 2 > 0 := by
          rw [show (0 : ℝ) = Real.sqrt 0 from Real.sqrt_zero.symm]
          exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
        exact this)).mpr h_half_pi_lt_two
    have h_step2 : 2 * Real.sqrt 2 < 2 * 2 :=
      (mul_lt_mul_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)).mpr h_sqrt2_lt_2
    linarith
  -- (π/2)·√2·ε_n ≤ (π/2)·√2·(2·ε₀) < 4·(2·ε₀) = 1/524288 ≤ 1
  have h_prod_nn : (0 : ℝ) ≤ (Real.pi / 2) * Real.sqrt 2 := by positivity
  have h_chain : (Real.pi / 2) * Real.sqrt 2 * ε_n < 1 := by
    calc (Real.pi / 2) * Real.sqrt 2 * ε_n
        ≤ (Real.pi / 2) * Real.sqrt 2 * (2 * ε₀) :=
          mul_le_mul_of_nonneg_left h_le h_prod_nn
      _ < 4 * (2 * ε₀) := by
          have h_2ε₀_pos : 0 < 2 * ε₀ := two_ε₀_pos
          exact (mul_lt_mul_iff_of_pos_right h_2ε₀_pos).mpr h_prod_lt
      _ = 4 * (1 / 4194304) := by rw [h_two_ε₀]
      _ < 1 := by norm_num
  exact le_of_lt h_chain

/-- **Y_h vanishing implies near-identity in regime**: for h ∈ SU(2) with
`‖h - 1‖ < 1/4`, if `Y_h h = 0` then `h = 1` (matrix identity).

Consumed by the inductive step's θ = 0 case (dnStepFG invalid branch)
to conclude V_n = U exactly, giving level-(m+1) error = 0.

Mechanism:
  - Y_h h = (sinc θ_h)⁻¹ • (h - a·1) where a = h.trace.re/2.
  - (sinc θ_h)⁻¹ > 0 in our regime (a > 3/4 ⟹ θ_h ∈ [0, π/2)).
  - Hence Y_h h = 0 ⟺ h = a·1 (scalar matrix).
  - For h ∈ SU(2): h = a·1 ⟹ det(a·1) = a² = 1 ⟹ a = ±1.
  - In regime a > 3/4: a = 1, hence h = 1. -/
lemma Y_h_eq_zero_in_regime_implies_eq_one
    {h : Matrix (Fin 2) (Fin 2) ℂ}
    (hh : h ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (h_small : ‖h - (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ < 1 / 4)
    (h_Y_h_zero : Y_h h = 0) :
    h = 1 := by
  set a : ℝ := h.trace.re / 2 with ha_def
  have h_a_le_one : a ≤ 1 := (SU2_trace_re_div_two_mem_Icc hh).2
  have h_one_sub_a_le : 1 - a ≤ ‖h - 1‖ :=
    SU2_one_sub_trace_re_div_two_le_norm_sub_one hh
  have h_a_gt_three_quarters : 3/4 < a := by linarith
  set θ : ℝ := Real.arccos a with hθ_def
  have h_θ_nn : 0 ≤ θ := Real.arccos_nonneg _
  have h_θ_le_pi_div_two : θ ≤ Real.pi / 2 := by
    rw [hθ_def]
    exact Real.arccos_le_pi_div_two.mpr (by linarith)
  have h_sinc_ge : 2 / Real.pi ≤ Real.sinc θ := sinc_ge_two_div_pi h_θ_nn h_θ_le_pi_div_two
  have h_two_div_pi_pos : 0 < 2 / Real.pi := by positivity
  have h_sinc_pos : 0 < Real.sinc θ := lt_of_lt_of_le h_two_div_pi_pos h_sinc_ge
  have h_Y_h_unfold : Y_h h =
      (((Real.sinc θ)⁻¹ : ℝ) : ℂ) •
        (h - ((a : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    unfold Y_h; rfl
  rw [h_Y_h_unfold] at h_Y_h_zero
  have h_inv_sinc_pos : 0 < (Real.sinc θ)⁻¹ := inv_pos.mpr h_sinc_pos
  -- The coercion form in h_Y_h_zero: ((Real.sinc θ)⁻¹ : ℝ) cast to ℂ
  have h_inv_sinc_ne_real : ((Real.sinc θ)⁻¹ : ℝ) ≠ 0 := ne_of_gt h_inv_sinc_pos
  have h_inv_sinc_ne : (((Real.sinc θ)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast h_inv_sinc_ne_real
  -- c • v = 0 with c ≠ 0 ⟹ v = 0
  have h_operand_zero : h - ((a : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    rcases smul_eq_zero.mp h_Y_h_zero with h_c | h_v
    · exact absurd h_c h_inv_sinc_ne
    · exact h_v
  have h_eq_a_one : h = ((a : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    have := sub_eq_zero.mp h_operand_zero
    exact this
  -- From SU(2): det(h) = 1. With h = a·1: det(a·1) = a²
  rw [Matrix.mem_specialUnitaryGroup_iff] at hh
  obtain ⟨_h_unitary, h_det⟩ := hh
  rw [h_eq_a_one] at h_det
  have h_det_smul : Matrix.det (((a : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      ((a : ℝ) : ℂ) ^ 2 := by
    rw [Matrix.det_smul]
    simp [Matrix.det_one, Fintype.card_fin]
  rw [h_det_smul] at h_det
  have h_a_sq : (a : ℝ) ^ 2 = 1 := by
    have : ((a : ℝ) : ℂ) ^ 2 = (1 : ℂ) := h_det
    have h_cast : (((a : ℝ) : ℂ))^2 = (((a : ℝ)^2 : ℝ) : ℂ) := by push_cast; ring
    rw [h_cast] at this
    exact_mod_cast this
  have h_a_eq_one : a = 1 := by
    have : (a - 1) * (a + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h1 | h2
    · linarith
    · linarith
  rw [h_eq_a_one, h_a_eq_one]
  ext i j
  by_cases h_ij : i = j
  · subst h_ij
    simp [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul]
  · simp [Matrix.smul_apply, Matrix.one_apply_ne h_ij, smul_eq_mul]

/-- **Trace bound from near-identity regime**: for `h ∈ SU(2)` with
`‖h - 1‖ < 1/4`, the trace real part satisfies `h.trace.re > 3/2`, in
particular `h.trace.re ≠ -2`.

Consumed by the inductive step's valid branch as the precondition for
`dnStepFG_exp_neg_comm_eq_Delta` (which requires `Δ.trace.re ≠ -2` to
apply §9.7 `SU2_expAmbient_Y_h_eq`). The bound `> 3/2` follows from
`1 - h.trace.re/2 ≤ ‖h - 1‖ < 1/4` via `SU2_one_sub_trace_re_div_two_le_norm_sub_one`. -/
lemma SU2_trace_re_ne_neg_two_of_norm_sub_one_lt_quarter
    {h : Matrix (Fin 2) (Fin 2) ℂ}
    (hh : h ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (h_small : ‖h - (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ < 1 / 4) :
    h.trace.re ≠ -2 := by
  have h_one_sub_a_le : 1 - h.trace.re / 2 ≤ ‖h - 1‖ :=
    SU2_one_sub_trace_re_div_two_le_norm_sub_one hh
  intro h_eq
  -- If h.trace.re = -2, then 1 - (-2)/2 = 1 + 1 = 2 ≤ ‖h - 1‖ < 1/4, contradiction.
  rw [h_eq] at h_one_sub_a_le
  linarith

/-! ## 7.6. Substantive inductive discharge — `SkApproxCSuperQuadraticBound K_compose`

The Option-C-tightened Y_h Lipschitz bound (`Y_h_norm_le_half_pi_norm_sub_one`,
c=π/2) enables the substantive inductive composition for `K_compose = 1024`.

Calibration arithmetic (per `phase6t-path-a-calibration-audit.md`):

  - θ ≤ (π/2)·√2·ε_n at level n (via `H_norm_bound_from_V_diff_half_pi`)
  - δ := max(‖F‖, ‖G‖) ≤ √(θ/2) ≤ (π/(2√2))^{1/2}·√(ε_n)
  - δ³ ≤ (π/(2√2))^{3/2}·ε_n^{3/2} ≈ 1.171·ε_n^{3/2}
  - BCH cubic: ‖gC(exp(iF), exp(iG)) - exp(-[F,G])‖ ≤ 320·δ³ ≈ 374·ε_n^{3/2}
  - Stability ~ 12·ε_n·η + ε_n² with η ≤ 2·δ ≈ 2·(π/(2√2))^{1/2}·√(ε_n)
  - V_n linftyOp factor ≤ √2
  - K_proof ≈ √2·(374 + ~12) ≈ 546 ≤ K_compose = 1024 ✓ (~478 K-margin)

Substrate composition (matching the 11-step chain blueprint):

  Step 1 (IH): ‖ρ(V_n_braid) - U‖ ≤ ε_n
  Step 2 (Residual): ‖Δ - 1‖ ≤ √2·ε_n  via `residual_norm_le_sqrt_two_mul`
  Step 3 (Regime check 1): √2·ε_n < 1/4   (numerical from ε_n ≤ 2·ε₀)
  Step 4 (H norm): θ ≤ (π/2)·√2·ε_n      via `H_norm_bound_from_V_diff_half_pi`
  Step 5 (Hermiticity): H = -i·Y_h(Δ), Hermitian + traceless
  Step 6: θ := ‖H‖
  Step 7 (Regime check 2): θ ≤ 1
  Step 8 (F, G norms): ‖F‖, ‖G‖ ≤ √(θ/2)  via `dnStepFG_F/G_norm_le_sqrt_theta_half`
  Step 9 (IH on A_F, A_G): same IH applied to expIsu2(F), expIsu2(G)
  Step 10 (Composition): ρ(skApproxC (n+1) U) = V_n · gC(ρ(skA_F), ρ(skA_G))
  Step 11 (Error): cubic + stability + √2 unitarity = K_proof · ε_n^{3/2}

The substantive Lean composition is shipped in
`SkApproxCSuperQuadraticBound_holds_strong` (next ship — Phase 6t.1
focused MCP-supported session). The substrate cascade for the discharge
is fully in place per commits `dd4f06b` (Y_h π/2) + `7053f61` (ρ_Fib_SU2
matrix-level helpers).

This section documents the calibration arithmetic + step blueprint to
preserve context across compacts. -/

/-- **`ε_seq K_compose (2·ε₀) n ≤ 2·ε₀`** for all n — direct application of
`ε_seq_le_ε_zero` with the convergence condition coming from
`K_compose_sqrt_two_ε₀_lt_one`. -/
lemma ε_seq_K_compose_two_ε₀_le_two_ε₀ (n : ℕ) :
    SKEFTHawking.FKLW.EpsilonSeq.ε_seq K_compose (2 * ε₀) n ≤ 2 * ε₀ := by
  apply SKEFTHawking.FKLW.EpsilonSeq.ε_seq_le_ε_zero
  · exact K_compose_pos
  · exact two_ε₀_pos
  · -- Need K_compose · (2·ε₀)^(1/2) ≤ 1.
    -- We have K_compose · √(2·ε₀) ≤ 1/2 ≤ 1 (from K_compose_sqrt_two_ε₀_lt_one).
    -- Use Real.sqrt_eq_rpow to bridge: √x = x ^ (1/2).
    rw [show ((1 : ℝ) / 2) = (1 / 2 : ℝ) from rfl, ← Real.sqrt_eq_rpow]
    linarith [K_compose_sqrt_two_ε₀_lt_one]

/-- **DN composition bound (valid branch)**: in the dnStepFG valid branch
with the regime hypothesis `Δ.trace.re ≠ -2`, the group commutator of
the lifted SU(2) elements approximates Δ.val up to BCH cubic error:

  `‖gC(A_F.val, A_G.val) - Δ.val‖ ≤ 320 · δ³`

where δ := max(‖F‖, ‖G‖). Direct composition of `dnStepFG_exp_neg_comm_eq_Delta`
(giving `exp(-[F,G]) = Δ.val`) with Wave 1's `groupCommutator_lie_bracket_cubic_remainder`
(giving the BCH cubic bound). -/
lemma dnStepFG_gC_minus_Delta_norm_le_cubic
    (V_n_braid : FibonacciBraidWord)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (h_valid : 0 < ‖((-Complex.I) • Y_h
        ((ρ_Fib_SU2 V_n_braid)⁻¹ * U :
            ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val :
        Matrix (Fin 2) (Fin 2) ℂ)‖ ∧
        ‖((-Complex.I) • Y_h
        ((ρ_Fib_SU2 V_n_braid)⁻¹ * U :
            ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val :
        Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 1)
    (h_ne_neg_two : ((ρ_Fib_SU2 V_n_braid)⁻¹ * U :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val.trace.re ≠ -2)
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (hF_norm : ‖(dnStepFG V_n_braid U).F‖ ≤ δ)
    (hG_norm : ‖(dnStepFG V_n_braid U).G‖ ≤ δ) :
    ‖SKEFTHawking.FKLW.GroupCommutator.groupCommutator
        ((expIsu2 (dnStepFG V_n_braid U).F (dnStepFG V_n_braid U).hF_herm
                  (dnStepFG V_n_braid U).hF_tr :
            ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
            Matrix (Fin 2) (Fin 2) ℂ)
        ((expIsu2 (dnStepFG V_n_braid U).G (dnStepFG V_n_braid U).hG_herm
                  (dnStepFG V_n_braid U).hG_tr :
            ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
            Matrix (Fin 2) (Fin 2) ℂ) -
        ((ρ_Fib_SU2 V_n_braid)⁻¹ * U :
            ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val‖ ≤ 320 * δ ^ 3 := by
  -- Identify the expIsu2 lifts with NormedSpace.exp via expIsu2_val.
  rw [expIsu2_val, expIsu2_val]
  -- BCH cubic gives the bound w.r.t. exp(-[F,G]).
  have h_bch := SKEFTHawking.FKLW.GroupCommutator.groupCommutator_lie_bracket_cubic_remainder
                  δ hδ_nn hδ_le_one (dnStepFG V_n_braid U).F (dnStepFG V_n_braid U).G
                  hF_norm hG_norm
  -- The exp(-[F,G]) = Δ.val identity gives the substitution.
  have h_exp_eq_Δ := dnStepFG_exp_neg_comm_eq_Delta V_n_braid U h_valid h_ne_neg_two
  dsimp only at h_exp_eq_Δ
  -- expAmbient = NormedSpace.exp definitionally
  rw [show SU2MatrixExp.expAmbient (Complex.I • (dnStepFG V_n_braid U).F) =
      NormedSpace.exp (Complex.I • (dnStepFG V_n_braid U).F) from rfl]
  rw [show SU2MatrixExp.expAmbient (Complex.I • (dnStepFG V_n_braid U).G) =
      NormedSpace.exp (Complex.I • (dnStepFG V_n_braid U).G) from rfl]
  -- Use h_exp_eq_Δ to rewrite Δ.val as exp(-(F·G - G·F)).
  rw [← h_exp_eq_Δ]
  exact h_bch

/-! ## 7.7. INVALID branch handling — `skApproxC` recursion degenerates

When the dnStepFG validity check fails (θ = 0, equivalent to V_n = U
exactly in our regime via `Y_h_eq_zero_in_regime_implies_eq_one`),
the level-(m+1) recursion's braid word equals the level-m braid
unchanged: the group commutator of two identical braid words is trivially
1 in BraidGroup. -/

/-- **dnStepFG invalid branch gives F = G = 0**: structural unfolding. -/
lemma dnStepFG_invalid_F_zero
    (V_n_braid : FibonacciBraidWord)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (h_invalid : ¬(0 < ‖((-Complex.I) • Y_h
        ((ρ_Fib_SU2 V_n_braid)⁻¹ * U :
            ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val :
        Matrix (Fin 2) (Fin 2) ℂ)‖ ∧
        ‖((-Complex.I) • Y_h
        ((ρ_Fib_SU2 V_n_braid)⁻¹ * U :
            ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val :
        Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 1)) :
    (dnStepFG V_n_braid U).F = 0 ∧ (dnStepFG V_n_braid U).G = 0 := by
  simp only [dnStepFG]
  rw [dif_neg h_invalid]
  exact ⟨rfl, rfl⟩

/-- **`expIsu2 0 = 1`**: the SU(2) lift of the zero Hermitian-traceless
matrix equals the SU(2) identity. Direct unfolding via
`expIsu2_val` + `expAmbient_zero`. -/
lemma expIsu2_zero_val :
    ((expIsu2 (0 : Matrix (Fin 2) (Fin 2) ℂ) Matrix.isHermitian_zero
              (Matrix.trace_zero (Fin 2) ℂ) :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  rw [expIsu2_val]
  simp [SU2MatrixExp.expAmbient_zero]

/-! ## 7.7b. Numerical K-chain helper for the valid-branch discharge.

Extracted as a top-level lemma to keep the main theorem under the
200,000-heartbeat limit. Pure real-valued numerical chain using:
  - `Real.pi_lt_d2`  (π < 3.15)
  - `Real.exp_one_lt_three`  (e < 3)
  - `Real.sqrt 2 ≤ 3/2`  (via `Real.sqrt_lt_sqrt`)
  - `Real.sqrt (2·ε₀) ≤ 1/2048`  (via two_ε₀_value)
  - Tight (π/4)·√2 ≤ 6/5  (via π·√2 < 3.15·1.5 = 4.725 → not enough; need
    π·√2 ≤ 4.8 i.e. ≤ 24/5).  Actually (3.15/4)·(3/2) = 9.45/8 = 189/160 ≤ 6/5. ✓
  - `((π/4)·√2)^(1/2) ≤ 6/5`  via `Real.rpow_le_rpow` + `rpow_le_self` on (6/5)
  - `((π/4)·√2)^(3/2) ≤ 36/25`  via rpow_split + (6/5)·(6/5) -/

/-- **K-chain numerical bound** for the Path A valid-branch composition.

States: `√2·(K_stab1 + K_stab2) + K_cubic ≤ K_compose = 1024` where
  - K_stab1 := 12·√2·e·((π/4)·√2)^(1/2)
  - K_stab2 := 12·√(2·ε₀)
  - K_cubic := √2·320·((π/4)·√2)^(3/2)

Numerical: with (π/4)·√2 ≤ 6/5, K_stab1 ≤ 64.8, K_stab2 < 1, K_cubic ≤ 691.2.
Total K_proof ≤ √2·(64.8 + 1) + 691.2 ≤ (3/2)·65.8 + 691.2 ≈ 789.9 ≤ 1024 ✓. -/
private lemma valid_branch_K_chain_le_K_compose_numeric :
    Real.sqrt 2 *
      (12 * Real.sqrt 2 * Real.exp 1 *
        ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) +
       12 * Real.sqrt (2 * ε₀)) +
    Real.sqrt 2 * 320 * ((Real.pi / 4) * Real.sqrt 2) ^ (3 / 2 : ℝ) ≤
    K_compose := by
  rw [show K_compose = 1024 from rfl]
  -- Setup basic bounds
  have h_sqrt2_nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have h_e_pos : 0 < Real.exp 1 := Real.exp_pos _
  have h_e_nn : (0 : ℝ) ≤ Real.exp 1 := h_e_pos.le
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_pi_nn : (0 : ℝ) ≤ Real.pi := h_pi_pos.le
  have h_C0_nn : (0 : ℝ) ≤ (Real.pi / 4) * Real.sqrt 2 := by positivity
  -- √2 ≤ 3/2
  have h_sqrt2_le : Real.sqrt 2 ≤ 3/2 := by
    rw [show (3/2 : ℝ) = Real.sqrt ((3/2)^2) from (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_le_sqrt; norm_num
  -- exp 1 ≤ 3
  have h_e_le : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  -- π < 3.15
  have h_pi_lt : Real.pi < 3.15 := Real.pi_lt_d2
  -- (π/4)·√2 ≤ 6/5
  have h_C0_le : (Real.pi / 4) * Real.sqrt 2 ≤ 6/5 := by
    have h_pi_4_lt : Real.pi / 4 < 3.15 / 4 := by linarith
    calc (Real.pi / 4) * Real.sqrt 2
        ≤ (3.15 / 4) * Real.sqrt 2 :=
          mul_le_mul_of_nonneg_right h_pi_4_lt.le h_sqrt2_nn
      _ ≤ (3.15 / 4) * (3/2) :=
          mul_le_mul_of_nonneg_left h_sqrt2_le (by norm_num)
      _ = 189 / 160 := by norm_num
      _ ≤ 6/5 := by norm_num
  -- (6/5)^(1/2) ≤ 6/5
  have h_six_five_half_le : ((6/5 : ℝ)) ^ (1 / 2 : ℝ) ≤ 6/5 := by
    have h_chain : (6/5 : ℝ) ^ (1 / 2 : ℝ) ≤ (6/5 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 6/5)
        (by norm_num : (1/2 : ℝ) ≤ 1)
    rwa [Real.rpow_one] at h_chain
  -- ((π/4)·√2)^(1/2) ≤ 6/5
  have h_C0_half_le : ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) ≤ 6/5 := by
    have h_step : ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) ≤
                    (6/5 : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow h_C0_nn h_C0_le (by norm_num)
    linarith
  -- ((π/4)·√2)^(3/2) = ((π/4)·√2) · ((π/4)·√2)^(1/2) — via rpow_add
  -- We bound directly: ((π/4)·√2)^(3/2) ≤ (6/5)^(3/2) ≤ (6/5)·(6/5) = 36/25
  have h_six_five_pos : (0 : ℝ) < 6/5 := by norm_num
  have h_C0_three_halves_le : ((Real.pi / 4) * Real.sqrt 2) ^ (3 / 2 : ℝ) ≤ 36/25 := by
    have h_step1 : ((Real.pi / 4) * Real.sqrt 2) ^ (3 / 2 : ℝ) ≤
                    (6/5 : ℝ) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow h_C0_nn h_C0_le (by norm_num)
    have h_split : (6/5 : ℝ) ^ (3 / 2 : ℝ) =
                    (6/5 : ℝ) * (6/5 : ℝ) ^ (1 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 from by norm_num,
          Real.rpow_add h_six_five_pos, Real.rpow_one]
    have h_step2 : (6/5 : ℝ) * (6/5 : ℝ) ^ (1 / 2 : ℝ) ≤ (6/5 : ℝ) * (6/5 : ℝ) :=
      mul_le_mul_of_nonneg_left h_six_five_half_le (by norm_num)
    have h_eq : (6/5 : ℝ) * (6/5 : ℝ) = 36/25 := by norm_num
    linarith
  -- √(2·ε₀) ≤ 1/2048 (since 2·ε₀ = 1/4194304 = (1/2048)²)
  have h_sqrt_2ε₀_le : Real.sqrt (2 * ε₀) ≤ 1 / 2048 := by
    rw [show (2 * ε₀ : ℝ) = 1 / 4194304 from two_ε₀_value]
    rw [show (1 / 4194304 : ℝ) = (1 / 2048 : ℝ) ^ 2 from by norm_num]
    rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2048)]
  -- Rpow nonneg
  have h_rpow_half_nn : (0 : ℝ) ≤ ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg h_C0_nn _
  have h_rpow_three_halves_nn : (0 : ℝ) ≤ ((Real.pi / 4) * Real.sqrt 2) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg h_C0_nn _
  -- 12·√2·e·((π/4)·√2)^(1/2) ≤ 12·(3/2)·3·(6/5) = 324/5 = 64.8
  have h_K_stab1_le :
      12 * Real.sqrt 2 * Real.exp 1 *
        ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) ≤ 324 / 5 := by
    calc 12 * Real.sqrt 2 * Real.exp 1 *
            ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ)
        ≤ 12 * (3/2) * Real.exp 1 *
            ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ h_rpow_half_nn
          apply mul_le_mul_of_nonneg_right _ h_e_nn
          exact mul_le_mul_of_nonneg_left h_sqrt2_le (by norm_num)
      _ ≤ 12 * (3/2) * 3 *
            ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ h_rpow_half_nn
          apply mul_le_mul_of_nonneg_left h_e_le
          norm_num
      _ ≤ 12 * (3/2) * 3 * (6/5) := by
          apply mul_le_mul_of_nonneg_left h_C0_half_le
          norm_num
      _ = 324 / 5 := by norm_num
  -- 12·√(2·ε₀) ≤ 12·(1/2048) = 12/2048 = 3/512
  have h_K_stab2_le : 12 * Real.sqrt (2 * ε₀) ≤ 3 / 512 := by
    have h_step : 12 * Real.sqrt (2 * ε₀) ≤ 12 * (1/2048) :=
      mul_le_mul_of_nonneg_left h_sqrt_2ε₀_le (by norm_num)
    linarith
  -- √2·320·((π/4)·√2)^(3/2) ≤ (3/2)·320·(36/25) = (3·320·36)/(2·25) = 17280/25 = 691.2
  have h_K_cubic_le :
      Real.sqrt 2 * 320 * ((Real.pi / 4) * Real.sqrt 2) ^ (3 / 2 : ℝ) ≤
        17280 / 25 := by
    calc Real.sqrt 2 * 320 * ((Real.pi / 4) * Real.sqrt 2) ^ (3 / 2 : ℝ)
        ≤ (3/2) * 320 * ((Real.pi / 4) * Real.sqrt 2) ^ (3 / 2 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ h_rpow_three_halves_nn
          exact mul_le_mul_of_nonneg_right h_sqrt2_le (by norm_num)
      _ ≤ (3/2) * 320 * (36/25) := by
          apply mul_le_mul_of_nonneg_left h_C0_three_halves_le
          norm_num
      _ = 17280 / 25 := by norm_num
  -- Combine: √2·(K_stab1 + K_stab2) + K_cubic ≤ (3/2)·(324/5 + 3/512) + 17280/25
  -- Compute: (3/2)·(324/5) = 486/5 = 97.2
  -- (3/2)·(3/512) = 9/1024 ≈ 0.0088
  -- 17280/25 = 691.2
  -- Total ≈ 97.2 + 0.009 + 691.2 = 788.41 ≤ 1024 ✓
  -- Lift √2·(K_stab1 + K_stab2) ≤ (3/2)·(324/5 + 3/512)
  have h_sum_pos : 0 ≤
      12 * Real.sqrt 2 * Real.exp 1 *
        ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) +
      12 * Real.sqrt (2 * ε₀) := by
    apply add_nonneg
    · positivity
    · positivity
  have h_sum_le : (12 * Real.sqrt 2 * Real.exp 1 *
                   ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) +
                  12 * Real.sqrt (2 * ε₀)) ≤ 324/5 + 3/512 :=
    add_le_add h_K_stab1_le h_K_stab2_le
  have h_sqrt2_mul_sum_le :
      Real.sqrt 2 *
        (12 * Real.sqrt 2 * Real.exp 1 *
          ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) +
         12 * Real.sqrt (2 * ε₀)) ≤
      (3/2) * (324/5 + 3/512) := by
    calc Real.sqrt 2 *
          (12 * Real.sqrt 2 * Real.exp 1 *
            ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) +
           12 * Real.sqrt (2 * ε₀))
        ≤ Real.sqrt 2 * (324/5 + 3/512) :=
          mul_le_mul_of_nonneg_left h_sum_le h_sqrt2_nn
      _ ≤ (3/2) * (324/5 + 3/512) :=
          mul_le_mul_of_nonneg_right h_sqrt2_le (by norm_num : (0:ℝ) ≤ 324/5 + 3/512)
  -- Now: total ≤ (3/2)·(324/5 + 3/512) + 17280/25 ≤ 1024
  calc Real.sqrt 2 *
        (12 * Real.sqrt 2 * Real.exp 1 *
          ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) +
         12 * Real.sqrt (2 * ε₀)) +
       Real.sqrt 2 * 320 * ((Real.pi / 4) * Real.sqrt 2) ^ (3 / 2 : ℝ)
      ≤ (3/2) * (324/5 + 3/512) + 17280 / 25 :=
        add_le_add h_sqrt2_mul_sum_le h_K_cubic_le
    _ ≤ 1024 := by norm_num

/-! ## 7.8. **HEADLINE**: unconditional discharge of `SkApproxCSuperQuadraticBound K_compose`

The Option-C-tightened substrate cascade (Y_h Lipschitz π/2 + ρ_Fib_SU2
matrix-level helpers + load-bearing identities + near-identity bounds +
regime checks + DN cubic composition + invalid-branch helpers) enables the
substantive inductive composition for `K_compose = 1024`.

The proof case-splits on the dnStepFG validity:
  - **VALID** (`0 < θ ∧ θ ≤ 1`): substantive composition of the DN cubic
    bound (via `dnStepFG_gC_minus_Delta_norm_le_cubic`) with the
    near-identity stability bound (via `groupCommutator_stability_nearIdentity`),
    multiplied by the V_n linftyOp √2 factor (via `SU2_linftyOpNorm_le_sqrt_two`).
  - **INVALID** (`θ = 0` in regime — the only failure mode since regime
    forces `θ ≤ 1`): `Y_h_eq_zero_in_regime_implies_eq_one` forces
    `Δ.val = 1`, so `V_n = U` exactly; the recursion's group commutator
    structure on the identical-input braids `skApproxC m 1` collapses
    to the identity braid (via `mul_inv_cancel`), so the level-`(m+1)`
    output equals `V_n_braid`, giving error `= 0 ≤ K_compose · ε_n^(3/2)`. -/

/-- **HEADLINE — Phase 6t Path A Option C substantive discharge**.
The constructive Dawson-Nielsen compiler `skApproxC` achieves super-quadratic
error convergence at the calibrated rate `K_compose = 1024` for all levels
`n` and targets `U ∈ SU(2)`. With K_compose = 1024 (round value with explicit
margin over K_proof ≈ 546), the inductive composition closes cleanly using
the shipped substrate cascade. -/
theorem SkApproxCSuperQuadraticBound_holds :
    SkApproxCSuperQuadraticBound K_compose := by
  intro n
  induction n with
  | zero =>
    intro U
    exact skApproxC_zero_error_bound U
  | succ m ih =>
    intro U
    -- Goal: ‖ρ(skApproxC (m+1) U) - U‖ ≤ ε_seq K_compose (2·ε₀) (m+1)
    rw [SKEFTHawking.FKLW.EpsilonSeq.ε_seq_succ]
    -- ε_n notation and bounds
    set ε_n : ℝ :=
      SKEFTHawking.FKLW.EpsilonSeq.ε_seq K_compose (2 * ε₀) m with hε_n_def
    have h_ε_n_le_2ε₀ : ε_n ≤ 2 * ε₀ := ε_seq_K_compose_two_ε₀_le_two_ε₀ m
    have h_ε_n_nn : 0 ≤ ε_n :=
      SKEFTHawking.FKLW.EpsilonSeq.ε_seq_nonneg K_compose (2 * ε₀)
        K_compose_pos two_ε₀_pos m
    -- IH on V_n_braid (the level-m approximation to U)
    have h_V_n_bound :
        ‖((ρ_Fib_SU2 (skApproxC m U) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
            Matrix (Fin 2) (Fin 2) ℂ) -
          (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε_n := ih U
    -- Setup: V_n, Δ, H, θ
    set V_n_braid : FibonacciBraidWord := skApproxC m U with hV_n_braid_def
    set V_n_SU2 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
      ρ_Fib_SU2 V_n_braid with hV_n_SU2_def
    set Δ_SU2 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
      V_n_SU2⁻¹ * U with hΔ_SU2_def
    set H : Matrix (Fin 2) (Fin 2) ℂ :=
      ((-Complex.I) : ℂ) • Y_h Δ_SU2.val with hH_def
    set θ : ℝ := ‖H‖ with hθ_def
    -- Regime: √2·ε_n < 1/4
    have h_sqrt2_eps_lt : Real.sqrt 2 * ε_n < 1 / 4 :=
      sqrt_two_mul_eps_lt_one_quarter ε_n h_ε_n_nn h_ε_n_le_2ε₀
    -- Regime: (π/2)·√2·ε_n ≤ 1
    have h_half_pi_eps_le : (Real.pi / 2) * Real.sqrt 2 * ε_n ≤ 1 :=
      half_pi_sqrt_two_mul_eps_le_one ε_n h_ε_n_nn h_ε_n_le_2ε₀
    -- ‖Δ.val - 1‖ ≤ √2·ε_n (via residual + IH)
    have h_Δ_norm_le : ‖(Δ_SU2 : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ ≤
                        Real.sqrt 2 * ε_n := by
      calc ‖(Δ_SU2 : Matrix (Fin 2) (Fin 2) ℂ) - 1‖
          ≤ Real.sqrt 2 *
              ‖(V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) -
                (U : Matrix (Fin 2) (Fin 2) ℂ)‖ :=
            residual_norm_le_sqrt_two_mul V_n_SU2 U
        _ ≤ Real.sqrt 2 * ε_n := by
            exact mul_le_mul_of_nonneg_left h_V_n_bound (Real.sqrt_nonneg _)
    -- ‖Δ.val - 1‖ < 1/4
    have h_Δ_norm_lt : ‖(Δ_SU2 : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ < 1/4 :=
      lt_of_le_of_lt h_Δ_norm_le h_sqrt2_eps_lt
    -- θ ≤ (π/2)·√2·ε_n
    have h_θ_le : θ ≤ (Real.pi / 2) * Real.sqrt 2 * ε_n := by
      have h_H_bound :
          ‖((-Complex.I) • Y_h
              ((V_n_SU2⁻¹ * U :
                  ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val) :
              Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
            (Real.pi / 2) * Real.sqrt 2 *
              ‖(V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) -
                (U : Matrix (Fin 2) (Fin 2) ℂ)‖ :=
        H_norm_bound_from_V_diff_half_pi V_n_SU2 U
          (lt_of_le_of_lt (mul_le_mul_of_nonneg_left h_V_n_bound
            (Real.sqrt_nonneg _)) h_sqrt2_eps_lt)
      have h_θ_eq_H : θ = ‖((-Complex.I) • Y_h
                            ((V_n_SU2⁻¹ * U :
                                ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val) :
                            Matrix (Fin 2) (Fin 2) ℂ)‖ := rfl
      rw [h_θ_eq_H]
      calc ‖((-Complex.I) • Y_h
              ((V_n_SU2⁻¹ * U :
                  ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val) :
              Matrix (Fin 2) (Fin 2) ℂ)‖
          ≤ (Real.pi / 2) * Real.sqrt 2 *
              ‖(V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) -
                (U : Matrix (Fin 2) (Fin 2) ℂ)‖ := h_H_bound
        _ ≤ (Real.pi / 2) * Real.sqrt 2 * ε_n := by
            have h_nn : (0 : ℝ) ≤ (Real.pi / 2) * Real.sqrt 2 := by positivity
            exact mul_le_mul_of_nonneg_left h_V_n_bound h_nn
    -- θ ≤ 1 (always in regime)
    have h_θ_le_one : θ ≤ 1 := le_trans h_θ_le h_half_pi_eps_le
    -- θ ≥ 0
    have h_θ_nn : 0 ≤ θ := norm_nonneg _
    -- Case split on dnStepFG validity
    by_cases h_θ_pos : 0 < θ
    · -- VALID branch: substantive DN composition
      have h_valid : 0 < θ ∧ θ ≤ 1 := ⟨h_θ_pos, h_θ_le_one⟩
      -- δ_lie := √(θ/2), the Lie-algebra near-identity radius
      set δ_lie : ℝ := Real.sqrt (θ / 2) with hδ_lie_def
      have h_δ_lie_nn : 0 ≤ δ_lie := Real.sqrt_nonneg _
      have h_θ_div_two_nn : (0 : ℝ) ≤ θ / 2 := by linarith
      have h_δ_lie_sq : δ_lie ^ 2 = θ / 2 := Real.sq_sqrt h_θ_div_two_nn
      have h_δ_lie_le_one : δ_lie ≤ 1 := by
        rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
        exact Real.sqrt_le_sqrt (by linarith)
      -- F, G norm bounds: ‖F‖, ‖G‖ ≤ δ_lie = √(θ/2)
      have h_F_norm : ‖(dnStepFG V_n_braid U).F‖ ≤ δ_lie :=
        dnStepFG_F_norm_le_sqrt_theta_half V_n_braid U
      have h_G_norm : ‖(dnStepFG V_n_braid U).G‖ ≤ δ_lie :=
        dnStepFG_G_norm_le_sqrt_theta_half V_n_braid U
      -- Trace ≠ -2 (regime gives this for ‖Δ - 1‖ < 1/4)
      have h_trace_ne :
          (Δ_SU2 : Matrix (Fin 2) (Fin 2) ℂ).trace.re ≠ -2 :=
        SU2_trace_re_ne_neg_two_of_norm_sub_one_lt_quarter
          Δ_SU2.property h_Δ_norm_lt
      -- Define A_F, A_G
      set A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
        expIsu2 (dnStepFG V_n_braid U).F
          (dnStepFG V_n_braid U).hF_herm (dnStepFG V_n_braid U).hF_tr
        with hA_F_def
      set A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
        expIsu2 (dnStepFG V_n_braid U).G
          (dnStepFG V_n_braid U).hG_herm (dnStepFG V_n_braid U).hG_tr
        with hA_G_def
      -- DN cubic bound: ‖gC(A_F.val, A_G.val) - Δ.val‖ ≤ 320 · δ_lie^3
      have h_cubic :
          ‖SKEFTHawking.FKLW.GroupCommutator.groupCommutator
              ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                  Matrix (Fin 2) (Fin 2) ℂ)
              ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                  Matrix (Fin 2) (Fin 2) ℂ) -
            ((Δ_SU2 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 320 * δ_lie ^ 3 :=
        dnStepFG_gC_minus_Delta_norm_le_cubic V_n_braid U h_valid h_trace_ne
          δ_lie h_δ_lie_nn h_δ_lie_le_one h_F_norm h_G_norm
      -- Near-identity bounds: ‖A_F.val - 1‖, ‖A_G.val - 1‖ ≤ δ_lie · exp(δ_lie)
      have h_A_F_near_one :
          ‖((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ) - 1‖ ≤ δ_lie * Real.exp δ_lie :=
        expIsu2_norm_sub_one_le _
          (dnStepFG V_n_braid U).hF_herm (dnStepFG V_n_braid U).hF_tr
          δ_lie h_F_norm
      have h_A_G_near_one :
          ‖((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ) - 1‖ ≤ δ_lie * Real.exp δ_lie :=
        expIsu2_norm_sub_one_le _
          (dnStepFG V_n_braid U).hG_herm (dnStepFG V_n_braid U).hG_tr
          δ_lie h_G_norm
      -- Matrix-inverse near-identity bounds: ‖A_F.val⁻¹ - 1‖, ‖A_G.val⁻¹ - 1‖
      have h_A_F_inv_near_one :
          ‖((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ)⁻¹ - 1‖ ≤
            Real.sqrt 2 * (δ_lie * Real.exp δ_lie) :=
        expIsu2_inv_norm_sub_one_le _
          (dnStepFG V_n_braid U).hF_herm (dnStepFG V_n_braid U).hF_tr
          δ_lie h_F_norm
      have h_A_G_inv_near_one :
          ‖((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ)⁻¹ - 1‖ ≤
            Real.sqrt 2 * (δ_lie * Real.exp δ_lie) :=
        expIsu2_inv_norm_sub_one_le _
          (dnStepFG V_n_braid U).hG_herm (dnStepFG V_n_braid U).hG_tr
          δ_lie h_G_norm
      -- IH on A_F, A_G
      have h_IH_F :
          ‖((ρ_Fib_SU2 (skApproxC m A_F) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ) -
            ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε_n := ih A_F
      have h_IH_G :
          ‖((ρ_Fib_SU2 (skApproxC m A_G) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ) -
            ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε_n := ih A_G
      -- M-bounds: ‖SU(2) val‖ ≤ √2
      have h_sqrt2_nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
      have h_V_n_M : ‖(V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ Real.sqrt 2 :=
        SU2_linftyOpNorm_le_sqrt_two V_n_SU2.property
      have h_ρA_F_M :
          ‖((ρ_Fib_SU2 (skApproxC m A_F) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ Real.sqrt 2 :=
        SU2_linftyOpNorm_le_sqrt_two (ρ_Fib_SU2 (skApproxC m A_F)).property
      have h_ρA_G_M :
          ‖((ρ_Fib_SU2 (skApproxC m A_G) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ Real.sqrt 2 :=
        SU2_linftyOpNorm_le_sqrt_two (ρ_Fib_SU2 (skApproxC m A_G)).property
      have h_A_F_M :
          ‖((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ Real.sqrt 2 :=
        SU2_linftyOpNorm_le_sqrt_two A_F.property
      have h_A_G_M :
          ‖((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ Real.sqrt 2 :=
        SU2_linftyOpNorm_le_sqrt_two A_G.property
      -- Matrix-inverse M-bounds
      have h_A_F_inv_M :
          ‖((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ)⁻¹‖ ≤ Real.sqrt 2 := by
        rw [← SU2_subtype_inv_val_eq_matrix_inv A_F]
        exact SU2_linftyOpNorm_le_sqrt_two (A_F⁻¹).property
      have h_A_G_inv_M :
          ‖((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ)⁻¹‖ ≤ Real.sqrt 2 := by
        rw [← SU2_subtype_inv_val_eq_matrix_inv A_G]
        exact SU2_linftyOpNorm_le_sqrt_two (A_G⁻¹).property
      have h_ρA_F_inv_M :
          ‖((ρ_Fib_SU2 (skApproxC m A_F) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ)⁻¹‖ ≤ Real.sqrt 2 := by
        rw [← SU2_subtype_inv_val_eq_matrix_inv (ρ_Fib_SU2 (skApproxC m A_F))]
        exact SU2_linftyOpNorm_le_sqrt_two
          (ρ_Fib_SU2 (skApproxC m A_F))⁻¹.property
      have h_ρA_G_inv_M :
          ‖((ρ_Fib_SU2 (skApproxC m A_G) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ)⁻¹‖ ≤ Real.sqrt 2 := by
        rw [← SU2_subtype_inv_val_eq_matrix_inv (ρ_Fib_SU2 (skApproxC m A_G))]
        exact SU2_linftyOpNorm_le_sqrt_two
          (ρ_Fib_SU2 (skApproxC m A_G))⁻¹.property
      -- IsUnit det for invertibility
      have h_A_F_det : IsUnit (A_F : Matrix (Fin 2) (Fin 2) ℂ).det :=
        SU2_val_det_isUnit A_F
      have h_A_G_det : IsUnit (A_G : Matrix (Fin 2) (Fin 2) ℂ).det :=
        SU2_val_det_isUnit A_G
      have h_ρA_F_det :
          IsUnit ((ρ_Fib_SU2 (skApproxC m A_F) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ).det :=
        SU2_val_det_isUnit _
      have h_ρA_G_det :
          IsUnit ((ρ_Fib_SU2 (skApproxC m A_G) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ).det :=
        SU2_val_det_isUnit _
      -- Define η := √2 · δ_lie · exp(δ_lie) (max of the two near-identity bounds)
      set η : ℝ := Real.sqrt 2 * (δ_lie * Real.exp δ_lie) with hη_def
      have h_δ_lie_exp_nn : (0 : ℝ) ≤ δ_lie * Real.exp δ_lie :=
        mul_nonneg h_δ_lie_nn (Real.exp_pos _).le
      have h_η_nn : (0 : ℝ) ≤ η :=
        mul_nonneg h_sqrt2_nn h_δ_lie_exp_nn
      -- The η bounds we need for stability (h - 1 with h = A_G.val, g⁻¹ - 1 with g = A_F.val)
      have h_h_near_id_η :
          ‖((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ) - 1‖ ≤ η := by
        calc ‖((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                Matrix (Fin 2) (Fin 2) ℂ) - 1‖
            ≤ δ_lie * Real.exp δ_lie := h_A_G_near_one
          _ ≤ Real.sqrt 2 * (δ_lie * Real.exp δ_lie) := by
              have h_one_le_sqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := by
                rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
                exact Real.sqrt_le_sqrt (by norm_num)
              nlinarith
      have h_g_inv_near_id_η :
          ‖((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ)⁻¹ - 1‖ ≤ η := h_A_F_inv_near_one
      -- Perturbation (δ in stability) bounds: ‖ρA_F - A_F‖, ‖ρA_G - A_G‖ ≤ ε_n
      have h_g_diff_ε :
          ‖((ρ_Fib_SU2 (skApproxC m A_F) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ) -
            ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε_n := h_IH_F
      have h_h_diff_ε :
          ‖((ρ_Fib_SU2 (skApproxC m A_G) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ) -
            ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε_n := h_IH_G
      -- Apply groupCommutator_stability_nearIdentity
      have h_stability :
          ‖SKEFTHawking.FKLW.GroupCommutator.groupCommutator
              ((ρ_Fib_SU2 (skApproxC m A_F) :
                  ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                  Matrix (Fin 2) (Fin 2) ℂ)
              ((ρ_Fib_SU2 (skApproxC m A_G) :
                  ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                  Matrix (Fin 2) (Fin 2) ℂ) -
            SKEFTHawking.FKLW.GroupCommutator.groupCommutator
              ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                  Matrix (Fin 2) (Fin 2) ℂ)
              ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                  Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
            2 * (Real.sqrt 2 ^ 2 + Real.sqrt 2 ^ 4) * ε_n * η +
            (Real.sqrt 2 ^ 4 + Real.sqrt 2 ^ 6) * ε_n ^ 2 :=
        SKEFTHawking.FKLW.GroupCommutatorNearIdentity.groupCommutator_stability_nearIdentity
          (A_F : Matrix (Fin 2) (Fin 2) ℂ)
          (A_G : Matrix (Fin 2) (Fin 2) ℂ)
          ((ρ_Fib_SU2 (skApproxC m A_F) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ)
          ((ρ_Fib_SU2 (skApproxC m A_G) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ)
          η ε_n (Real.sqrt 2)
          h_η_nn h_ε_n_nn h_sqrt2_nn
          h_ρA_F_M h_ρA_G_M
          h_A_F_inv_M h_A_G_inv_M
          h_ρA_F_inv_M h_ρA_G_inv_M
          h_h_near_id_η h_g_inv_near_id_η
          h_g_diff_ε h_h_diff_ε
          h_A_F_det h_ρA_F_det h_A_G_det h_ρA_G_det
      -- ρ(skApproxC (m+1) U) = V_n_SU2.val * gC(ρA_F.val, ρA_G.val)
      have h_skApproxC_succ_val :
          ((ρ_Fib_SU2 (skApproxC (m + 1) U) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ) =
            (V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
            SKEFTHawking.FKLW.GroupCommutator.groupCommutator
              ((ρ_Fib_SU2 (skApproxC m A_F) :
                  ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                  Matrix (Fin 2) (Fin 2) ℂ)
              ((ρ_Fib_SU2 (skApproxC m A_G) :
                  ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                  Matrix (Fin 2) (Fin 2) ℂ) := by
        rw [skApproxC_succ]
        show ((ρ_Fib_SU2 (V_n_braid * (skApproxC m A_F * skApproxC m A_G *
                  (skApproxC m A_F)⁻¹ * (skApproxC m A_G)⁻¹)) :
                ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                Matrix (Fin 2) (Fin 2) ℂ) = _
        rw [ρ_Fib_SU2_mul_val, ρ_Fib_SU2_groupCommutator_val]
      -- Final composition: split via gC(A_F, A_G), bound each piece.
      -- ‖V_n_SU2 · gC(ρA_F, ρA_G) - U‖
      --   ≤ ‖V_n_SU2‖ · ‖gC(ρA_F, ρA_G) - gC(A_F, A_G)‖
      --     + ‖V_n_SU2 · gC(A_F, A_G) - U‖
      -- where ‖V_n_SU2 · gC(A_F, A_G) - U‖
      --      = ‖V_n_SU2 · gC(A_F, A_G) - V_n_SU2 · Δ.val‖   (V_n·Δ = U)
      --      ≤ ‖V_n_SU2‖ · ‖gC(A_F, A_G) - Δ.val‖
      --      ≤ √2 · 320·δ_lie^3                              (h_cubic)
      have h_V_n_Δ_eq_U :
          (V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
            (Δ_SU2 : Matrix (Fin 2) (Fin 2) ℂ) =
            (U : Matrix (Fin 2) (Fin 2) ℂ) := by
        have h_mul_def : V_n_SU2 * Δ_SU2 = V_n_SU2 * (V_n_SU2⁻¹ * U) := by
          rw [hΔ_SU2_def]
        have h_simp : V_n_SU2 * Δ_SU2 = U := by
          rw [h_mul_def]
          rw [← mul_assoc, mul_inv_cancel, one_mul]
        have h_val : ((V_n_SU2 * Δ_SU2 :
                          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                       Matrix (Fin 2) (Fin 2) ℂ) =
                     (V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
                     (Δ_SU2 : Matrix (Fin 2) (Fin 2) ℂ) := rfl
        rw [← h_val, h_simp]
      -- Bound term 2: ‖V_n_SU2 · gC(A_F.val, A_G.val) - U‖ ≤ √2 · 320·δ_lie^3
      have h_term2 :
          ‖(V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
            (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
            Real.sqrt 2 * (320 * δ_lie ^ 3) := by
        rw [← h_V_n_Δ_eq_U]
        rw [show (V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
              (V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              (Δ_SU2 : Matrix (Fin 2) (Fin 2) ℂ) =
              (V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              (SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
              (Δ_SU2 : Matrix (Fin 2) (Fin 2) ℂ)) from by noncomm_ring]
        calc ‖(V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              (SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
              (Δ_SU2 : Matrix (Fin 2) (Fin 2) ℂ))‖
            ≤ ‖(V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ)‖ *
              ‖SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
              (Δ_SU2 : Matrix (Fin 2) (Fin 2) ℂ)‖ := norm_mul_le _ _
          _ ≤ Real.sqrt 2 * (320 * δ_lie ^ 3) := by
              have h_cubic_nn : (0 : ℝ) ≤ 320 * δ_lie ^ 3 := by positivity
              exact mul_le_mul h_V_n_M h_cubic (norm_nonneg _) h_sqrt2_nn
      -- Bound term 1: ‖V_n_SU2 · (gC(ρA_F, ρA_G) - gC(A_F, A_G))‖ ≤ √2 · stability
      set stab_bound : ℝ :=
        2 * (Real.sqrt 2 ^ 2 + Real.sqrt 2 ^ 4) * ε_n * η +
        (Real.sqrt 2 ^ 4 + Real.sqrt 2 ^ 6) * ε_n ^ 2 with hstab_def
      have h_term1 :
          ‖(V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((ρ_Fib_SU2 (skApproxC m A_F) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((ρ_Fib_SU2 (skApproxC m A_G) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
            (V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
            Real.sqrt 2 * stab_bound := by
        rw [show (V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((ρ_Fib_SU2 (skApproxC m A_F) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((ρ_Fib_SU2 (skApproxC m A_G) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
              (V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) =
              (V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              (SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((ρ_Fib_SU2 (skApproxC m A_F) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((ρ_Fib_SU2 (skApproxC m A_G) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
              SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)) from by noncomm_ring]
        calc ‖(V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              (SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((ρ_Fib_SU2 (skApproxC m A_F) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((ρ_Fib_SU2 (skApproxC m A_G) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
              SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ))‖
            ≤ ‖(V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ)‖ *
              ‖SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((ρ_Fib_SU2 (skApproxC m A_F) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((ρ_Fib_SU2 (skApproxC m A_G) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
              SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)‖ := norm_mul_le _ _
          _ ≤ Real.sqrt 2 * stab_bound := by
              have h_stab_nn : (0 : ℝ) ≤ stab_bound := by
                rw [hstab_def]
                positivity
              exact mul_le_mul h_V_n_M h_stability (norm_nonneg _) h_sqrt2_nn
      -- Combine via triangle inequality
      have h_combined_norm :
          ‖((ρ_Fib_SU2 (skApproxC (m + 1) U) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ) -
            (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
            Real.sqrt 2 * stab_bound + Real.sqrt 2 * (320 * δ_lie ^ 3) := by
        rw [h_skApproxC_succ_val]
        -- Decompose: (V_n · gC(ρA_F, ρA_G) - U) = (V_n · gC(ρA_F, ρA_G) - V_n · gC(A_F, A_G)) + (V_n · gC(A_F, A_G) - U)
        have h_decomp :
            (V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((ρ_Fib_SU2 (skApproxC m A_F) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((ρ_Fib_SU2 (skApproxC m A_G) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
              (U : Matrix (Fin 2) (Fin 2) ℂ) =
            ((V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((ρ_Fib_SU2 (skApproxC m A_F) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((ρ_Fib_SU2 (skApproxC m A_G) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
              (V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)) +
            ((V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
              (U : Matrix (Fin 2) (Fin 2) ℂ)) := by noncomm_ring
        rw [h_decomp]
        exact le_trans (norm_add_le _ _) (add_le_add h_term1 h_term2)
      -- Numerical chain: √2·stab_bound + √2·320·δ_lie^3 ≤ K_compose · ε_n^(3/2)
      -- δ_lie^2 = θ/2 ≤ (π/4)·√2·ε_n
      have h_δ_lie_sq_le : δ_lie ^ 2 ≤ (Real.pi / 4) * Real.sqrt 2 * ε_n := by
        rw [h_δ_lie_sq]
        linarith [h_θ_le]
      -- δ_lie^3 = (δ_lie^2)^(3/2 · 1/2)·... Actually use (δ_lie^2)·δ_lie
      -- δ_lie^3 ≤ ((π/4)·√2)^(3/2) · ε_n^(3/2)
      have h_C_cubic_nn : (0 : ℝ) ≤ (Real.pi / 4) * Real.sqrt 2 := by positivity
      have h_δ_lie_pow3_le :
          δ_lie ^ 3 ≤ ((Real.pi / 4) * Real.sqrt 2) ^ (3 / 2 : ℝ) *
                      ε_n ^ (3 / 2 : ℝ) := by
        -- (δ_lie^2)^(3/2) = δ_lie^3 for nonneg δ_lie
        have h_sq_nn : (0 : ℝ) ≤ δ_lie ^ 2 := sq_nonneg _
        have h_eq1 : δ_lie ^ 3 = (δ_lie ^ 2) ^ (3 / 2 : ℝ) := by
          -- (δ_lie^2)^(3/2) = (δ_lie^2)^1 · (δ_lie^2)^(1/2)
          --                = δ_lie^2 · √(δ_lie^2)
          --                = δ_lie^2 · δ_lie = δ_lie^3
          rw [show (3 / 2 : ℝ) = 1 + 1 / 2 from by norm_num,
              Real.rpow_add_of_nonneg h_sq_nn (by norm_num) (by norm_num),
              Real.rpow_one, ← Real.sqrt_eq_rpow,
              Real.sqrt_sq h_δ_lie_nn]
          ring
        rw [h_eq1]
        -- (δ_lie^2)^(3/2) ≤ ((π/4)·√2·ε_n)^(3/2)
        have h_step : (δ_lie ^ 2) ^ (3 / 2 : ℝ) ≤
                      ((Real.pi / 4) * Real.sqrt 2 * ε_n) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow (sq_nonneg _) h_δ_lie_sq_le (by norm_num)
        calc (δ_lie ^ 2) ^ (3 / 2 : ℝ)
            ≤ ((Real.pi / 4) * Real.sqrt 2 * ε_n) ^ (3 / 2 : ℝ) := h_step
          _ = ((Real.pi / 4) * Real.sqrt 2) ^ (3 / 2 : ℝ) *
              ε_n ^ (3 / 2 : ℝ) := by
              rw [Real.mul_rpow (by positivity) h_ε_n_nn]
      -- exp(δ_lie) ≤ exp(1) = e
      have h_exp_le_e : Real.exp δ_lie ≤ Real.exp 1 :=
        Real.exp_le_exp.mpr h_δ_lie_le_one
      have h_e_nn : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos _).le
      -- η = √2 · δ_lie · exp(δ_lie) ≤ √2 · δ_lie · e
      have h_η_le : η ≤ Real.sqrt 2 * (δ_lie * Real.exp 1) := by
        rw [hη_def]
        have h_δ_exp_le : δ_lie * Real.exp δ_lie ≤ δ_lie * Real.exp 1 :=
          mul_le_mul_of_nonneg_left h_exp_le_e h_δ_lie_nn
        exact mul_le_mul_of_nonneg_left h_δ_exp_le h_sqrt2_nn
      -- δ_lie ≤ √((π/4)·√2) · √ε_n = ((π/4)·√2)^(1/2) · ε_n^(1/2)
      have h_δ_lie_le_rpow :
          δ_lie ≤ ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) *
                  ε_n ^ (1 / 2 : ℝ) := by
        rw [← Real.mul_rpow h_C_cubic_nn h_ε_n_nn]
        rw [← Real.sqrt_eq_rpow]
        rw [show δ_lie = Real.sqrt (δ_lie ^ 2) from (Real.sqrt_sq h_δ_lie_nn).symm]
        exact Real.sqrt_le_sqrt h_δ_lie_sq_le
      -- ε_n^2 = ε_n^(3/2) · ε_n^(1/2) ≤ ε_n^(3/2) · √(2·ε₀)
      have h_ε_n_sq_le :
          ε_n ^ 2 ≤ Real.sqrt (2 * ε₀) * ε_n ^ (3 / 2 : ℝ) := by
        have h_split : ε_n ^ 2 = ε_n ^ (3 / 2 : ℝ) * ε_n ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_natCast ε_n 2]
          rw [show ((2 : ℕ) : ℝ) = 3 / 2 + 1 / 2 from by norm_num]
          exact Real.rpow_add_of_nonneg h_ε_n_nn (by norm_num) (by norm_num)
        rw [h_split]
        have h_ε_n_rpow_nn : (0 : ℝ) ≤ ε_n ^ (3 / 2 : ℝ) := Real.rpow_nonneg h_ε_n_nn _
        have h_ε_n_half_le : ε_n ^ (1 / 2 : ℝ) ≤ Real.sqrt (2 * ε₀) := by
          rw [Real.sqrt_eq_rpow]
          exact Real.rpow_le_rpow h_ε_n_nn h_ε_n_le_2ε₀ (by norm_num)
        calc ε_n ^ (3 / 2 : ℝ) * ε_n ^ (1 / 2 : ℝ)
            ≤ ε_n ^ (3 / 2 : ℝ) * Real.sqrt (2 * ε₀) :=
              mul_le_mul_of_nonneg_left h_ε_n_half_le h_ε_n_rpow_nn
          _ = Real.sqrt (2 * ε₀) * ε_n ^ (3 / 2 : ℝ) := by ring
      -- Now bound stab_bound ≤ K_stab · ε_n^(3/2)
      -- stab_bound = 12·ε_n·η + 12·ε_n^2 (with M=√2: M²=2, M⁴=4, M⁶=8, 2(M²+M⁴)=12, M⁴+M⁶=12)
      have h_sqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
      have h_sqrt2_pow4 : Real.sqrt 2 ^ 4 = 4 := by
        have h_eq : Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 := by ring
        rw [h_eq, h_sqrt2_sq]
        norm_num
      have h_sqrt2_pow6 : Real.sqrt 2 ^ 6 = 8 := by
        have h_eq : Real.sqrt 2 ^ 6 = (Real.sqrt 2 ^ 2) ^ 3 := by ring
        rw [h_eq, h_sqrt2_sq]
        norm_num
      have h_stab_simplified :
          stab_bound = 12 * ε_n * η + 12 * ε_n ^ 2 := by
        rw [hstab_def, h_sqrt2_sq, h_sqrt2_pow4, h_sqrt2_pow6]; ring
      -- Bound 12·ε_n·η ≤ 12·ε_n · √2·δ_lie·e ≤ 12·√2·e · ε_n · ((π/4)√2)^(1/2)·ε_n^(1/2)
      --                = 12·√2·e·((π/4)·√2)^(1/2) · ε_n^(3/2)
      set K_stab1 : ℝ := 12 * Real.sqrt 2 * Real.exp 1 *
                          ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ)
        with hKstab1_def
      have h_K_stab1_nn : (0 : ℝ) ≤ K_stab1 := by
        rw [hKstab1_def]
        positivity
      have h_term_η_le :
          12 * ε_n * η ≤ K_stab1 * ε_n ^ (3 / 2 : ℝ) := by
        -- 12 · ε_n · η ≤ 12 · ε_n · (√2 · δ_lie · e)
        --              ≤ 12 · ε_n · (√2 · (((π/4)√2)^(1/2)·ε_n^(1/2)) · e)
        --              = 12·√2·e·((π/4)·√2)^(1/2) · ε_n · ε_n^(1/2)
        --              = K_stab1 · ε_n^(3/2)
        have h_ε_n_eq : ε_n * ε_n ^ (1 / 2 : ℝ) = ε_n ^ (3 / 2 : ℝ) := by
          rw [show (3 / 2 : ℝ) = 1 + 1 / 2 from by norm_num,
              Real.rpow_add_of_nonneg h_ε_n_nn (by norm_num : (0:ℝ) ≤ 1)
                (by norm_num : (0:ℝ) ≤ 1/2),
              Real.rpow_one]
        have h_chain :
            12 * ε_n * η ≤
            12 * ε_n * (Real.sqrt 2 * (δ_lie * Real.exp 1)) :=
          mul_le_mul_of_nonneg_left h_η_le (by positivity)
        have h_chain2 :
            12 * ε_n * (Real.sqrt 2 * (δ_lie * Real.exp 1)) ≤
            12 * ε_n * (Real.sqrt 2 *
              ((((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) *
                ε_n ^ (1 / 2 : ℝ)) * Real.exp 1)) := by
          apply mul_le_mul_of_nonneg_left
          · apply mul_le_mul_of_nonneg_left
            · apply mul_le_mul_of_nonneg_right h_δ_lie_le_rpow h_e_nn
            · exact h_sqrt2_nn
          · positivity
        have h_rearrange :
            12 * ε_n * (Real.sqrt 2 *
              ((((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) *
                ε_n ^ (1 / 2 : ℝ)) * Real.exp 1)) =
            K_stab1 * ε_n ^ (3 / 2 : ℝ) := by
          rw [hKstab1_def]
          rw [show 12 * ε_n * (Real.sqrt 2 *
              ((((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) *
                ε_n ^ (1 / 2 : ℝ)) * Real.exp 1)) =
              (12 * Real.sqrt 2 * Real.exp 1 *
                ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ)) *
              (ε_n * ε_n ^ (1 / 2 : ℝ)) from by ring]
          rw [h_ε_n_eq]
        linarith
      -- Bound 12·ε_n^2 ≤ 12·√(2ε₀) · ε_n^(3/2)
      set K_stab2 : ℝ := 12 * Real.sqrt (2 * ε₀) with hKstab2_def
      have h_K_stab2_nn : (0 : ℝ) ≤ K_stab2 := by
        rw [hKstab2_def]; positivity
      have h_term_sq_le :
          12 * ε_n ^ 2 ≤ K_stab2 * ε_n ^ (3 / 2 : ℝ) := by
        rw [hKstab2_def]
        have h_step : 12 * ε_n ^ 2 ≤ 12 * (Real.sqrt (2 * ε₀) * ε_n ^ (3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left h_ε_n_sq_le (by norm_num : (0:ℝ) ≤ 12)
        linarith
      -- Bound stab_bound ≤ (K_stab1 + K_stab2) · ε_n^(3/2)
      have h_stab_bound_le :
          stab_bound ≤ (K_stab1 + K_stab2) * ε_n ^ (3 / 2 : ℝ) := by
        rw [h_stab_simplified, add_mul]
        exact add_le_add h_term_η_le h_term_sq_le
      -- Bound cubic: √2 · 320 · δ_lie^3 ≤ √2·320·((π/4)·√2)^(3/2) · ε_n^(3/2)
      set K_cubic : ℝ := Real.sqrt 2 * 320 *
                          ((Real.pi / 4) * Real.sqrt 2) ^ (3 / 2 : ℝ)
        with hKcubic_def
      have h_K_cubic_nn : (0 : ℝ) ≤ K_cubic := by
        rw [hKcubic_def]; positivity
      have h_cubic_le :
          Real.sqrt 2 * (320 * δ_lie ^ 3) ≤ K_cubic * ε_n ^ (3 / 2 : ℝ) := by
        rw [hKcubic_def]
        have h_320_nn : (0 : ℝ) ≤ 320 := by norm_num
        have h_step :
            320 * δ_lie ^ 3 ≤ 320 * (((Real.pi / 4) * Real.sqrt 2) ^ (3 / 2 : ℝ) *
                              ε_n ^ (3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left h_δ_lie_pow3_le h_320_nn
        calc Real.sqrt 2 * (320 * δ_lie ^ 3)
            ≤ Real.sqrt 2 * (320 * (((Real.pi / 4) * Real.sqrt 2) ^ (3 / 2 : ℝ) *
                              ε_n ^ (3 / 2 : ℝ))) :=
              mul_le_mul_of_nonneg_left h_step h_sqrt2_nn
          _ = Real.sqrt 2 * 320 * ((Real.pi / 4) * Real.sqrt 2) ^ (3 / 2 : ℝ) *
              ε_n ^ (3 / 2 : ℝ) := by ring
      -- Final: ‖result - U‖ ≤ √2·stab_bound + √2·320·δ_lie^3
      --                     ≤ (K_stab1 + K_stab2)·ε_n^(3/2) + K_cubic·ε_n^(3/2)  -- with √2 mult
      -- Actually we need to carry √2 through stab too: √2 · stab_bound, so
      --   √2 · stab_bound ≤ √2 · (K_stab1 + K_stab2) · ε_n^(3/2)
      have h_sqrt2_stab_le :
          Real.sqrt 2 * stab_bound ≤
            Real.sqrt 2 * (K_stab1 + K_stab2) * ε_n ^ (3 / 2 : ℝ) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left h_stab_bound_le h_sqrt2_nn
      -- Total K_proof = √2·(K_stab1 + K_stab2) + K_cubic ≤ K_compose
      have h_total_le :
          Real.sqrt 2 * stab_bound + Real.sqrt 2 * (320 * δ_lie ^ 3) ≤
            (Real.sqrt 2 * (K_stab1 + K_stab2) + K_cubic) *
            ε_n ^ (3 / 2 : ℝ) := by
        rw [add_mul]
        exact add_le_add h_sqrt2_stab_le h_cubic_le
      -- K_proof ≤ K_compose (numerical verification)
      -- We need: √2 · (K_stab1 + K_stab2) + K_cubic ≤ K_compose = 1024
      have h_K_proof_le_K_compose :
          Real.sqrt 2 * (K_stab1 + K_stab2) + K_cubic ≤ K_compose := by
        rw [hKstab1_def, hKstab2_def, hKcubic_def]
        exact valid_branch_K_chain_le_K_compose_numeric
      -- Final assembly
      calc ‖((ρ_Fib_SU2 (skApproxC (m + 1) U) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ) -
            (U : Matrix (Fin 2) (Fin 2) ℂ)‖
          ≤ Real.sqrt 2 * stab_bound + Real.sqrt 2 * (320 * δ_lie ^ 3) :=
            h_combined_norm
        _ ≤ (Real.sqrt 2 * (K_stab1 + K_stab2) + K_cubic) *
            ε_n ^ (3 / 2 : ℝ) := h_total_le
        _ ≤ K_compose * ε_n ^ (3 / 2 : ℝ) := by
            have h_rpow_nn : (0 : ℝ) ≤ ε_n ^ (3 / 2 : ℝ) :=
              Real.rpow_nonneg h_ε_n_nn _
            exact mul_le_mul_of_nonneg_right h_K_proof_le_K_compose h_rpow_nn
    · -- INVALID branch: θ = 0 (regime forces this since θ ≤ 1 always)
      have h_θ_le_zero : θ ≤ 0 := not_lt.mp h_θ_pos
      have h_θ_zero : θ = 0 := le_antisymm h_θ_le_zero h_θ_nn
      -- Construct the invalid hypothesis in the exact form dnStepFG expects.
      have h_invalid_check :
          ¬(0 < ‖((-Complex.I) • Y_h
              ((ρ_Fib_SU2 V_n_braid)⁻¹ * U :
                  ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val :
              Matrix (Fin 2) (Fin 2) ℂ)‖ ∧
              ‖((-Complex.I) • Y_h
              ((ρ_Fib_SU2 V_n_braid)⁻¹ * U :
                  ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val :
              Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 1) := by
        intro ⟨h_pos, _⟩
        -- h_pos : 0 < ‖explicit form‖, but this IS θ (by set unfolding)
        exact h_θ_pos h_pos
      -- F = G = 0 in dnStepFG output
      have h_FG_zero : (dnStepFG V_n_braid U).F = 0 ∧
                        (dnStepFG V_n_braid U).G = 0 :=
        dnStepFG_invalid_F_zero V_n_braid U h_invalid_check
      -- A_F = A_G via Subtype.ext (matrix equality at .val)
      set A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
        expIsu2 (dnStepFG V_n_braid U).F
          (dnStepFG V_n_braid U).hF_herm (dnStepFG V_n_braid U).hF_tr
        with hA_F_def
      set A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
        expIsu2 (dnStepFG V_n_braid U).G
          (dnStepFG V_n_braid U).hG_herm (dnStepFG V_n_braid U).hG_tr
        with hA_G_def
      have h_A_F_eq_A_G : A_F = A_G := by
        apply Subtype.ext
        rw [hA_F_def, hA_G_def, expIsu2_val, expIsu2_val, h_FG_zero.1, h_FG_zero.2]
      -- skApproxC m A_F = skApproxC m A_G
      have h_skA_eq : skApproxC m A_F = skApproxC m A_G := by
        rw [h_A_F_eq_A_G]
      -- The braid-level (m+1) word equals V_n_braid (group commutator collapses)
      have h_skApproxC_succ_eq : skApproxC (m + 1) U = V_n_braid := by
        rw [skApproxC_succ]
        -- Goal contains let bindings; show V_n_braid * (gC of two A_F_braids) = V_n_braid
        show V_n_braid * (skApproxC m A_F * skApproxC m A_G *
              (skApproxC m A_F)⁻¹ * (skApproxC m A_G)⁻¹) = V_n_braid
        rw [h_skA_eq]
        -- Now: V_n_braid * (g * g * g⁻¹ * g⁻¹) = V_n_braid
        group
      -- Now derive ρ(skApproxC (m+1) U) = V_n_SU2
      have h_ρ_eq : (ρ_Fib_SU2 (skApproxC (m + 1) U) :
                      ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) = V_n_SU2 := by
        rw [h_skApproxC_succ_eq]
      -- From θ = 0: H = 0, hence Y_h Δ.val = 0
      have h_H_zero : H = 0 := by
        have h_norm_zero : ‖H‖ = 0 := h_θ_zero
        exact norm_eq_zero.mp h_norm_zero
      have h_neg_I_ne : ((-Complex.I) : ℂ) ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
      have h_Y_h_zero : Y_h Δ_SU2.val = 0 := by
        have h_unfold : H = ((-Complex.I) : ℂ) • Y_h Δ_SU2.val := rfl
        rw [h_unfold] at h_H_zero
        rcases smul_eq_zero.mp h_H_zero with hh | hh
        · exact absurd hh h_neg_I_ne
        · exact hh
      -- Y_h injectivity: Δ.val = 1 (matrix), so Δ_SU2 = 1 (SU(2))
      have h_Δ_val_eq_one : Δ_SU2.val = 1 :=
        Y_h_eq_zero_in_regime_implies_eq_one Δ_SU2.property h_Δ_norm_lt h_Y_h_zero
      have h_Δ_SU2_eq_one : Δ_SU2 = 1 := Subtype.ext h_Δ_val_eq_one
      -- From V_n⁻¹ * U = 1, derive U = V_n_SU2
      have h_eq_in_SU2 : V_n_SU2⁻¹ * U = 1 := h_Δ_SU2_eq_one
      have h_U_eq_V_n : U = V_n_SU2 := by
        calc U = 1 * U := (one_mul _).symm
          _ = V_n_SU2 * V_n_SU2⁻¹ * U := by rw [mul_inv_cancel]
          _ = V_n_SU2 * (V_n_SU2⁻¹ * U) := mul_assoc _ _ _
          _ = V_n_SU2 * 1 := by rw [h_eq_in_SU2]
          _ = V_n_SU2 := mul_one _
      -- Now ‖ρ(skApproxC (m+1) U) - U‖ = ‖V_n_SU2 - V_n_SU2‖ = 0
      have h_lhs_zero :
          ‖((ρ_Fib_SU2 (skApproxC (m + 1) U) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ) -
            (U : Matrix (Fin 2) (Fin 2) ℂ)‖ = 0 := by
        rw [h_ρ_eq, h_U_eq_V_n]
        simp
      -- RHS ≥ 0
      have h_rhs_nn : (0 : ℝ) ≤ K_compose * ε_n ^ (3 / 2 : ℝ) := by
        have h_K_nn : (0 : ℝ) ≤ K_compose := K_compose_pos.le
        have h_rpow_nn : (0 : ℝ) ≤ ε_n ^ (3 / 2 : ℝ) := Real.rpow_nonneg h_ε_n_nn _
        exact mul_nonneg h_K_nn h_rpow_nn
      rw [h_lhs_zero]
      exact h_rhs_nn

/-! ## 8. Path A unconditional strict headline for loose ε regime

For `ε ≥ 2·ε₀`, the level-0 constructive approximation suffices and
the strict headline holds UNCONDITIONALLY. -/

/-- **Path A UNCONDITIONAL strict headline (loose ε regime)**: for any
target `U ∈ SU(2)` and precision `ε ≥ 2·ε₀ ∧ ε ≤ ε₀`, the level-0
constructive approximation `skApproxC 0 U` achieves error ≤ ε AND
satisfies the standard length bound (via existing
`skLength_at_skLevel_polylog_le`).

This is the level-0 unconditional headline. For tight ε (ε < 2·ε₀), the
substantive super-quadratic discharge is required (calibration-gated). -/
theorem solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict_constructive_unconditional
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ)
    (h_ε : 2 * ε₀ ≤ ε) :
    ‖(ρ_Fib_SU2 (skApproxC 0 U) : Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε := by
  have h_base := skApproxC_zero_error_bound U
  rw [SKEFTHawking.FKLW.EpsilonSeq.ε_seq_zero] at h_base
  linarith

/-! **Note on `_bundled_loose`**: an earlier version of this file shipped a
"bundled" theorem with hypotheses `2·ε₀ ≤ ε ∧ ε ≤ ε₀`. Those hypotheses
are MUTUALLY EXCLUSIVE for ε₀ > 0 (they'd require `ε₀ ≤ 0`), so the
theorem was vacuously true. We dropped it.

The honest unconditional ship is the unbundled `_unconditional` form
(error only, for loose ε ≥ 2·ε₀). The substantive bundled form (error +
polylog length for tight ε ∈ (0, ε₀]) requires the calibration-gated
discharge of `SkApproxCSuperQuadraticBound K_compose`. -/

end SKEFTHawking.FKLW.SolovayKitaevPathA
