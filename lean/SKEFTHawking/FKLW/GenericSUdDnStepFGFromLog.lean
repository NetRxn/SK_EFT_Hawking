/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — log-agnostic Dawson-Nielsen step `dnStepFG_fromLog` (re-point R4 foundation)

`dnStepFG_sud` (S82) builds its generator `H = (-i)·matrixLog (n+2) Δ.val` from the
**IFT** matrix log, whose regime conjuncts (Hermitian, traceless, θ-bound, `Δ ∈ target`)
are only available on an *existential* radius — the last blocker to an UNCONDITIONAL
`h_regime` (see the Phase 6y roadmap §"Re-point sub-brick breakdown (R0–R4)"). The fix is
to **re-point** the step to the concrete-radius Mercator log `matrixMercatorLog (Δ − 1)`,
whose regime conjuncts hold on a *named* ball (S120–S128, all CONCRETE-RADIUS UNCONDITIONAL).

The key structural observation enabling the re-point **without duplicating the whole
super-quad chain**: the DN step is **log-agnostic**. `matrixLog (n+2) Δ.val` enters
`dnStepFG_sud` purely as a matrix `M` such that `H = (-i)·M` is fed to the bounded
keystone, and the only matrix-log-*specific* fact the downstream error analysis uses is
the round-trip `exp M = Δ`. So we factor the step over an arbitrary `M`:

  `dnStepFG_fromLog M` — the keystone-`(F,G)` extraction from a generator `H = (-i)·M`,

and prove the keystone-algebraic identities (`[F,G] = -M`, invalid branch `(0,0)`, and the
round-trip-conditional `exp(-[F,G]) = Δ`) **once**, generic in `M`. Because the body of
`dnStepFG_fromLog (matrixLog (n+2) Δ.val)` is *definitionally* `dnStepFG_sud V_n U`
(`dnStepFG_sud_eq_fromLog`, by `rfl`), the existing IFT chain is recovered for free, and
instantiating `M := matrixMercatorLog (Δ.val − 1)` gives the **concrete** DN step whose
regime is dischargeable by S120–S128 — the route to the UNCONDITIONAL headline.

## Substantive content shipped

  * `dnStepFG_fromLog` — log-agnostic DN step (generator from an arbitrary `M`).
  * `dnStepFG_sud_eq_fromLog` — `dnStepFG_sud V_n U = dnStepFG_fromLog (matrixLog …)` (`rfl`).
  * `dnStepFG_fromLog_commutator_identity_valid` — `[F,G] = -M` in the valid regime.
  * `dnStepFG_fromLog_invalid_F_G_zero` — invalid branch gives `F = G = 0`.
  * `dnStepFG_fromLog_exp_neg_comm_eq_Delta` — `exp(-[F,G]) = Δ` given `exp M = Δ`
    (round-trip), with the `‖(-i)·M‖ = 0` degenerate branch handled internally.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Re-point sub-brick breakdown (R0–R4)" — R4 foundation: log-agnostic
factoring of the DN step, enabling the re-point to `matrixMercatorLog` without duplicating
the super-quad chain.

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdDnStepFGCommutator

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. The log-agnostic Dawson-Nielsen step -/

open Classical in
/-- **Log-agnostic SU(d) Dawson-Nielsen step**: extract the keystone `(F, G)` pair from a
generator `H = (-i)·M` built from an *arbitrary* matrix `M` (the "log" of the residual).
Identical to `dnStepFG_sud` except the residual log `matrixLog (n+2) Δ.val` is abstracted
to a parameter `M`. Falls back to `(0, 0)` outside the valid regime
(`0 < ‖H‖ ≤ 1 ∧ H Hermitian ∧ H traceless`). -/
noncomputable def dnStepFG_fromLog {n : ℕ} (M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) :
    DNStepData_SUd (n + 2) :=
  let H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ := ((-Complex.I) : ℂ) • M
  let θ : ℝ := ‖H‖
  if h : 0 < θ ∧ θ ≤ 1 ∧ H.IsHermitian ∧ H.trace = 0 then
    let ex := symmetric_balanced_commutator_hermitian_unconditional_bounded
                (((1 / θ : ℝ) : ℂ) • H)
                (IsHermitian_real_smul_sud h.2.2.1 (1 / θ))
                (smul_trace_zero_sud h.2.2.2 _)
                (normalize_smul_norm_le_one H h.1)
                θ h.1.le h.2.1
    { F := ex.choose
      G := ex.choose_spec.choose
      hF_herm := ex.choose_spec.choose_spec.1
      hG_herm := ex.choose_spec.choose_spec.2.1
      hF_tr := ex.choose_spec.choose_spec.2.2.1
      hG_tr := ex.choose_spec.choose_spec.2.2.2.1 }
  else
    { F := 0
      G := 0
      hF_herm := Matrix.isHermitian_zero
      hG_herm := Matrix.isHermitian_zero
      hF_tr := by simp
      hG_tr := by simp }

/-- **`dnStepFG_sud` is `dnStepFG_fromLog` at the IFT log** (`rfl`): the existing
S82 step is definitionally the log-agnostic step instantiated at
`M = matrixLog (n+2) (V_n⁻¹·U).val`. This recovers the entire IFT super-quad chain for
free and lets the same `dnStepFG_fromLog` identities serve the concrete re-point. -/
theorem dnStepFG_sud_eq_fromLog {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
    dnStepFG_sud V_n U =
      dnStepFG_fromLog (matrixLog (n + 2)
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val) :=
  rfl

/-! ## 2. Commutator identity (valid branch) -/

/-- **`dnStepFG_fromLog` commutator identity (valid branch)**: `[F, G] = -M` in the valid
regime (`0 < ‖(-i)·M‖ ≤ 1 ∧ (-i)·M Hermitian ∧ traceless`). The bounded keystone gives
`F·G − G·F = -((θ:ℂ)·I)·((1/θ)·H)` with `H = (-i)·M`; the scalar collapses
`-(θ·i)·(1/θ)·(-i) = -1`. Log-agnostic generalization of
`dnStepFG_sud_commutator_identity_valid` (S83). -/
theorem dnStepFG_fromLog_commutator_identity_valid {n : ℕ}
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (h_valid : 0 < ‖((-Complex.I) • M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ∧
        ‖((-Complex.I) • M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ≤ 1 ∧
        ((-Complex.I) • M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ).IsHermitian ∧
        ((-Complex.I) • M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ).trace = 0) :
    (dnStepFG_fromLog M).F * (dnStepFG_fromLog M).G -
        (dnStepFG_fromLog M).G * (dnStepFG_fromLog M).F = -M := by
  simp only [dnStepFG_fromLog]
  set H_local : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ := ((-Complex.I) : ℂ) • M with hH_def
  set θ_local : ℝ := ‖H_local‖ with hθ_def
  rw [dif_pos h_valid]
  set ex_data := symmetric_balanced_commutator_hermitian_unconditional_bounded
      (((1 / θ_local : ℝ) : ℂ) • H_local)
      (IsHermitian_real_smul_sud h_valid.2.2.1 (1 / θ_local))
      (smul_trace_zero_sud h_valid.2.2.2 _)
      (normalize_smul_norm_le_one H_local h_valid.1)
      θ_local h_valid.1.le h_valid.2.1 with hex_def
  have h_comm_eq : ex_data.choose * ex_data.choose_spec.choose -
                   ex_data.choose_spec.choose * ex_data.choose =
                   -((θ_local : ℂ) * Complex.I) • (((1 / θ_local : ℝ) : ℂ) • H_local) :=
    ex_data.choose_spec.choose_spec.2.2.2.2.1
  have h_theta_pos : (0 : ℝ) < θ_local := h_valid.1
  have h_theta_ne : (θ_local : ℂ) ≠ 0 := by
    have : (θ_local : ℝ) ≠ 0 := ne_of_gt h_theta_pos
    exact_mod_cast this
  have h_scalar : -((θ_local : ℂ) * Complex.I) * (((1 / θ_local : ℝ) : ℂ)) = -Complex.I := by
    have h_div : ((1 / θ_local : ℝ) : ℂ) = ((θ_local : ℂ))⁻¹ := by push_cast; rw [one_div]
    rw [h_div]; field_simp
  rw [h_comm_eq, smul_smul, h_scalar, hH_def]
  show -Complex.I • ((-Complex.I : ℂ) • M) = -M
  rw [smul_smul]
  ring_nf
  simp [Complex.I_sq]

/-- **`dnStepFG_fromLog` invalid branch gives `F = G = 0`**: outside the valid regime,
the step falls back to `(0, 0)`. Log-agnostic generalization of
`dnStepFG_sud_invalid_F_G_zero`. -/
theorem dnStepFG_fromLog_invalid_F_G_zero {n : ℕ}
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (h_invalid : ¬(0 < ‖((-Complex.I) • M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ∧
        ‖((-Complex.I) • M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ≤ 1 ∧
        ((-Complex.I) • M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ).IsHermitian ∧
        ((-Complex.I) • M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ).trace = 0)) :
    (dnStepFG_fromLog M).F = 0 ∧ (dnStepFG_fromLog M).G = 0 := by
  simp only [dnStepFG_fromLog]
  rw [dif_neg h_invalid]
  exact ⟨rfl, rfl⟩

/-! ## 3. Round-trip-conditional exp(-[F,G]) = Δ -/

/-- **`dnStepFG_fromLog` exp(-[F,G]) = Δ given the round-trip `exp M = Δ`**: log-agnostic
generalization of `dnStepFG_sud_exp_neg_comm_eq_Delta` (S84). The matrix-log-specific
round-trip `expAmbient_matrixLog Δ` (valid only on the existential `target`) is replaced by
the **abstract hypothesis** `exp M = Δ` — which the **concrete** log satisfies on the
*named* ball via `exp_matrixMercatorLog` (S118), making this the re-point's exp-delta brick.

Internally case-splits on `‖(-i)·M‖`:
  * **valid branch** (`0 < ‖(-i)·M‖`): `[F,G] = -M` (commutator identity above), so
    `exp(-[F,G]) = exp M = Δ`.
  * **degenerate branch** (`‖(-i)·M‖ = 0`, i.e. `M = 0`, `Δ = exp 0 = 1`): the step is
    `(0,0)`, so `exp(-[0,0]) = exp 0 = 1 = Δ`. -/
theorem dnStepFG_fromLog_exp_neg_comm_eq_Delta {n : ℕ}
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (Δ : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (h_regime3 : ‖((-Complex.I) • M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ≤ 1 ∧
        ((-Complex.I) • M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ).IsHermitian ∧
        ((-Complex.I) • M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ).trace = 0)
    (h_roundtrip : NormedSpace.exp M = Δ) :
    NormedSpace.exp (-((dnStepFG_fromLog M).F * (dnStepFG_fromLog M).G -
        (dnStepFG_fromLog M).G * (dnStepFG_fromLog M).F)) = Δ := by
  by_cases h_pos : 0 < ‖((-Complex.I) • M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖
  · have h_comm := dnStepFG_fromLog_commutator_identity_valid M
      ⟨h_pos, h_regime3.1, h_regime3.2.1, h_regime3.2.2⟩
    have h_neg_comm : -((dnStepFG_fromLog M).F * (dnStepFG_fromLog M).G -
        (dnStepFG_fromLog M).G * (dnStepFG_fromLog M).F) = M := by
      rw [h_comm]; exact neg_neg _
    rw [h_neg_comm, h_roundtrip]
  · have hFG := dnStepFG_fromLog_invalid_F_G_zero M (fun h => h_pos h.1)
    have hH0 : ((-Complex.I) • M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) = 0 := by
      rw [← norm_le_zero_iff]; exact not_lt.mp h_pos
    have hM0 : M = 0 := by
      have h2 : (-Complex.I)⁻¹ • ((-Complex.I) • M) = 0 := by rw [hH0, smul_zero]
      rwa [smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero), one_smul] at h2
    have hΔ1 : Δ = 1 := by rw [← h_roundtrip, hM0, NormedSpace.exp_zero]
    rw [hFG.1, hFG.2, hΔ1]
    simp

end SKEFTHawking.FKLW.GenericSUd
