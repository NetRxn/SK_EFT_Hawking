/-
Phase 6p Wave 2d.5-followup-full (Z-axis single-step ship): the substantive
Dawson-Nielsen single-step refinement for the qubit Z-axis case, composing
Wave 2d.3-followup (`qubit_balanced_commutator_z_axis`) with the order-2
BCH cubic-remainder theorem (`MatrixBCHCubic.bch_order_2_cubic_thm`).

The composition discharges the **substantive content** of one Dawson-Nielsen
recursive refinement step for the Z-axis coordinate case:

  ∀ θ ∈ [0, 1], setting
    F := √(θ/2) · σ_y,   G := √(θ/2) · σ_x,    H := θ · σ_z,
  we have:

  ‖exp(iF) · exp(iG) · exp(-iF) · exp(-iG)  -  exp(i · H)‖  ≤  320 · (θ/2)^{3/2}.

This is the qubit case of D-N Theorem 1 §4.1 Eq. (10-13) composed with D-N
Lemma 3 §4.2 (cubic remainder).  Concretely:

  - **Construction**: Wave 2d.3-followup provides `F, G` hermitian with norms
    `√(θ/2)` and `F·G - G·F = -(θ·i)•σ_z = -i·H`.
  - **BCH bound**: Wave 2d.2-followup-R5.2b gives
    `‖exp(iF)exp(iG)exp(-iF)exp(-iG) - exp(-[F,G])‖ ≤ 320·δ³` for `‖F‖,‖G‖ ≤ δ ≤ 1`.
  - **Substitution**: `-[F,G] = (θ·i)•σ_z = i·H`, so
    `exp(-[F,G]) = exp(i·H)`.  Plug in `δ = √(θ/2)` ⇒ `δ³ = (θ/2)^{3/2}`.

**Convergence rate**: starting with target `H` of operator norm `θ` ≤ 1, one
recursion step produces an approximation of `exp(iH)` with error
`320·(θ/2)^{3/2} = 320·θ^{3/2}/(2√2) ≈ 113·θ^{3/2}`.  For SK convergence,
the initial error after the base case must be small enough; with the (loose)
K = 320 bound the threshold is `θ_0 < 1/10^5` approximately.  D-N's
sharp K ≤ 4 (deferred to R5.2c) admits the textbook `θ_0 ~ 1/(K²) = 1/16`.

**Scope of this wave (2d.5-followup-full Z-axis ship):**

  - **Z-axis single-step refinement** — fully proved (this module).
  - **Full SU(2) recursion** — requires general-axis Lemma 2 (deferred,
    Wave 2d.3-followup-general predicate already declared).
  - **ε-net base case** — separate sub-wave (Wave 2d.3, also deferred).
  - **`SolovayKitaevWithLengthBound` constructive discharge** — requires
    composing this step (recursive) with the ε-net base case.

Zero new project-local axioms.  All content grounded in
`PauliMatrices` + `MatrixBCHCubic` + `QubitBalancedCommutator`.

References:
  - Dawson & Nielsen, arXiv:quant-ph/0505030 §4.1 Eq. 10-13 (Lemma 2),
    §4.2 (Lemma 3, cubic remainder).
  - `SKEFTHawking.FKLW.QubitBalancedCommutator.qubit_balanced_commutator_z_axis`
  - `SKEFTHawking.MatrixBCHCubic.bch_order_2_cubic_thm`
-/

import Mathlib
import SKEFTHawking.PauliMatrices
import SKEFTHawking.MatrixBCHCubic
import SKEFTHawking.FKLW.QubitBalancedCommutator

set_option autoImplicit false

namespace SKEFTHawking.FKLW

open SKEFTHawking Matrix Complex

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. The substantive D-N Lemma 3 single-step for Z-axis

Given `θ ∈ [0, 1]` and the Z-axis construction `F := √(θ/2)·σ_y`,
`G := √(θ/2)·σ_x`, the group commutator of `exp(iF), exp(iG)` approximates
`exp(i·H)` (where `H := θ·σ_z`) within the BCH cubic remainder
`320 · (θ/2)^{3/2}`. -/

/-- **D-N Lemma 3 single-step (Z-axis case, substantive ship).**
For any `θ : ℝ` with `0 ≤ θ ≤ 1`, the explicit construction

  `F := (Real.sqrt (θ/2) : ℂ) • σ_y`,
  `G := (Real.sqrt (θ/2) : ℂ) • σ_x`,
  `H := (θ : ℂ) • σ_z`

yields the group-commutator approximation

  `‖exp(iF) · exp(iG) · exp(-iF) · exp(-iG)  -  exp(i·H)‖`
    `≤ 320 · (θ/2)^{3/2}`.

This is the **substantive content** of Dawson-Nielsen §4.1 Eq. 10-13
(Lemma 2 + Lemma 3) for the Z-axis coordinate case. -/
theorem dn_lemma3_z_axis (θ : ℝ) (hθ_nn : 0 ≤ θ) (hθ_le_one : θ ≤ 1) :
    ‖NormedSpace.exp (Complex.I • ((Real.sqrt (θ/2) : ℂ) • σ_y)) *
       NormedSpace.exp (Complex.I • ((Real.sqrt (θ/2) : ℂ) • σ_x)) *
       NormedSpace.exp (-(Complex.I • ((Real.sqrt (θ/2) : ℂ) • σ_y))) *
       NormedSpace.exp (-(Complex.I • ((Real.sqrt (θ/2) : ℂ) • σ_x))) -
       NormedSpace.exp (Complex.I • ((θ : ℂ) • σ_z))‖ ≤
    320 * (Real.sqrt (θ/2))^3 := by
  set α := Real.sqrt (θ/2)
  set F := (α : ℂ) • σ_y
  set G := (α : ℂ) • σ_x
  -- α = √(θ/2), so α² = θ/2 and α ≤ 1 (since θ ≤ 1 ⟹ θ/2 ≤ 1 ⟹ √(θ/2) ≤ 1)
  have hα_nn : 0 ≤ α := Real.sqrt_nonneg _
  have hα_sq : α^2 = θ/2 := by
    rw [sq]; exact Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ θ/2)
  have hα_le_one : α ≤ 1 := by
    have h1 : θ/2 ≤ 1 := by linarith
    have h2 : α ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_one] at h2
  -- The norm bounds: ‖F‖, ‖G‖ ≤ α
  have hF_norm : ‖F‖ ≤ α := by
    have := smul_σ_y_norm_le α
    rwa [abs_of_nonneg hα_nn] at this
  have hG_norm : ‖G‖ ≤ α := by
    have := smul_σ_x_norm_le α
    rwa [abs_of_nonneg hα_nn] at this
  -- Commutator identity: F * G - G * F = -(θ · I) • σ_z (from 2d.3 core)
  have h_comm : F * G - G * F = (-(2 * α^2 * Complex.I)) • σ_z :=
    balanced_commutator_z_core α
  -- -[F, G] = (2α² · i) • σ_z = (θ · i) • σ_z = i · H (using α² = θ/2)
  have h_2α2_eq_θ : (2 * (α : ℂ)^2 : ℂ) = (θ : ℂ) := by
    have h_real : (2 * α^2 : ℝ) = θ := by rw [hα_sq]; ring
    have : ((2 * α^2 : ℝ) : ℂ) = ((θ : ℝ) : ℂ) := by exact_mod_cast h_real
    rw [show ((2 * α^2 : ℝ) : ℂ) = 2 * (α : ℂ)^2 from by push_cast; ring] at this
    exact this
  have h_neg_comm : -(F * G - G * F) = Complex.I • ((θ : ℂ) • σ_z) := by
    rw [h_comm]
    show -(-(2 * (α : ℂ)^2 * Complex.I) • σ_z) = Complex.I • ((θ : ℂ) • σ_z)
    rw [neg_smul]
    -- Goal: -(-((2 * α^2 * I) • σ_z)) = I • (θ : ℂ) • σ_z
    rw [show -(-((2 * (α : ℂ)^2 * Complex.I) • σ_z))
          = (2 * (α : ℂ)^2 * Complex.I) • σ_z from neg_neg _]
    -- Goal: (2 * α^2 * I) • σ_z = I • (θ : ℂ) • σ_z
    rw [smul_smul]
    congr 1
    rw [show (2 : ℂ) * (α : ℂ)^2 * Complex.I = Complex.I * (2 * (α : ℂ)^2) from by ring,
        h_2α2_eq_θ]
  -- Mathlib commutator notation `⁅F, G⁆ = F * G - G * F` (Lean Mathlib)
  -- We use the BCH cubic theorem with δ := α
  have h_bch := MatrixBCHCubic.bch_order_2_cubic_thm (d := 2) α hα_nn hα_le_one F G hF_norm hG_norm
  -- h_bch : ‖exp(iF)·exp(iG)·exp(-iF)·exp(-iG) - exp(-⁅F,G⁆)‖ ≤ 320·α³
  -- Convert `-⁅F, G⁆` to `Complex.I • H`
  have h_bracket_eq : (⁅F, G⁆ : Matrix (Fin 2) (Fin 2) ℂ) = F * G - G * F := by
    rw [Ring.lie_def]
  have h_neg_bracket : -(⁅F, G⁆ : Matrix (Fin 2) (Fin 2) ℂ) = Complex.I • ((θ : ℂ) • σ_z) := by
    rw [h_bracket_eq]; exact h_neg_comm
  rw [h_neg_bracket] at h_bch
  -- h_bch : ‖... - exp(i • (θ • σ_z))‖ ≤ 320 · α^3
  exact h_bch

/-! ## 2. Group-commutator predicate level scaffold for full SK recursion

The full `SolovayKitaevWithLengthBound` discharge would require:

  (a) An ε-net base case (Wave 2d.3 = `EpsilonNet.lean`, deferred).
  (b) The general-axis Lemma 2 (Wave 2d.3-followup-general predicate).
  (c) Iterated recursion (this module's `dn_lemma3_z_axis` for one step).

We expose a **predicate scaffold** for the Z-axis SK recursion structure.
This is consumed by future Wave 2d.5-followup-recursion to produce the
full `SolovayKitaevWithLengthBound` discharge.
-/

/-- The Z-axis Dawson-Nielsen single-step predicate: there exist
hermitian `F, G` of bounded norm such that the group-commutator
`exp(iF)·exp(iG)·exp(-iF)·exp(-iG)` approximates `exp(i·H)`
within cubic-in-‖H‖ error.  Discharged by `dn_lemma3_z_axis`. -/
def DNSingleStepZAxis (θ : ℝ) : Prop :=
  ∃ (F G : Matrix (Fin 2) (Fin 2) ℂ),
    F.IsHermitian ∧ G.IsHermitian ∧
    ‖F‖ ≤ Real.sqrt (θ/2) ∧ ‖G‖ ≤ Real.sqrt (θ/2) ∧
    ‖NormedSpace.exp (Complex.I • F) *
       NormedSpace.exp (Complex.I • G) *
       NormedSpace.exp (-(Complex.I • F)) *
       NormedSpace.exp (-(Complex.I • G)) -
       NormedSpace.exp (Complex.I • ((θ : ℂ) • σ_z))‖ ≤ 320 * (Real.sqrt (θ/2))^3

/-- The Z-axis single-step predicate holds for all `θ ∈ [0, 1]`,
discharged by the explicit construction `F = √(θ/2)·σ_y`, `G = √(θ/2)·σ_x`.

This is the **substantive predicate-level discharge** of the Dawson-Nielsen
single-step refinement for the Z-axis coordinate case. -/
theorem dnSingleStepZAxis_of_θ_le_one (θ : ℝ) (hθ_nn : 0 ≤ θ) (hθ_le_one : θ ≤ 1) :
    DNSingleStepZAxis θ := by
  refine ⟨(Real.sqrt (θ/2) : ℂ) • σ_y, (Real.sqrt (θ/2) : ℂ) • σ_x,
          ?_, ?_, ?_, ?_, ?_⟩
  · exact smul_σ_y_isHermitian _
  · exact smul_σ_x_isHermitian _
  · have := smul_σ_y_norm_le (Real.sqrt (θ/2))
    rwa [abs_of_nonneg (Real.sqrt_nonneg _)] at this
  · have := smul_σ_x_norm_le (Real.sqrt (θ/2))
    rwa [abs_of_nonneg (Real.sqrt_nonneg _)] at this
  · exact dn_lemma3_z_axis θ hθ_nn hθ_le_one

/-! ## 3. Module summary

`SKZAxisStep.lean` (Phase 6p Wave 2d.5-followup-full Z-axis ship,
2026-05-14): the substantive Dawson-Nielsen single-step refinement
for the qubit Z-axis case.

**Shipped (zero new axioms):**

  - **§1** `dn_lemma3_z_axis`: the SUBSTANTIVE composition of
    `qubit_balanced_commutator_z_axis` (Wave 2d.3-followup) +
    `bch_order_2_cubic_thm` (Wave 2d.2-followup-R5.2b), giving the
    full D-N single-step bound `‖VWV†W† - exp(iH)‖ ≤ 320·(θ/2)^{3/2}`
    for the Z-axis target `H = θ·σ_z`.

  - **§2** `DNSingleStepZAxis` predicate + `dnSingleStepZAxis_of_θ_le_one`
    discharge for all `θ ∈ [0, 1]`: the substantive predicate-level
    ship for the Z-axis single-step refinement.

**Cross-module bridge integrity** (Stage-3a pipeline check #6):
  Body calls (not just docstring):
  - `balanced_commutator_z_core` (Wave 2d.3-followup) — load-bearing.
  - `smul_σ_y_norm_le`, `smul_σ_x_norm_le` (Wave 2d.3-followup) —
    load-bearing.
  - `smul_σ_y_isHermitian`, `smul_σ_x_isHermitian` (Wave 2d.3-followup) —
    load-bearing.
  - `MatrixBCHCubic.bch_order_2_cubic_thm` (Wave 2d.2-followup-R5.2b) —
    load-bearing.

**Substantive content** (going beyond `dn_single_refinement_substantive`
in `SolovayKitaevConstructive.lean`):
  (a) Provides the EXPLICIT CONSTRUCTION `F = √(θ/2)·σ_y`, `G = √(θ/2)·σ_x`
      (the existing `dn_single_refinement_substantive` takes F, G as inputs).
  (b) Cubic bound `320·(θ/2)^{3/2}` (the existing single-step substantive
      lemma uses linear `200·δ`).
  (c) Direct connection to the target `exp(i·H)` for `H = θ·σ_z`.

**Deferred items** (for future sub-waves):
  - General-axis case (predicate `QubitBalancedCommutatorGeneralAxis` exists;
    proof needs SU(2) Bloch parametrization).
  - ε-net base case (Wave 2d.3 `EpsilonNet.lean`).
  - Iterated recursion + `SolovayKitaevWithLengthBound` constructive discharge.

**Pipeline-Invariant compliance:**
  - Zero new project-local axioms.
  - Zero `maxHeartbeats` overrides; proofs decomposed into small `have`s.
  - Pipeline Invariant #15 (no new axioms without sign-off) ✓.
-/

end SKEFTHawking.FKLW
