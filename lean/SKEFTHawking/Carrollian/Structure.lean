import Mathlib
import SKEFTHawking.Basic

/-!
# Phase 6o′ Wave 1a′ C1 — Carrollian structure + the acoustic-horizon instance

The ultra-relativistic (Carroll) degenerate boundary geometry of a horizon
(Donnay–Marteau; C0 verdict `Lit-Search/Phase-6o-prime/C0_horizon_BMS_charge_algebra_verdict_20260720.md`).
A **Carrollian structure** on a real vector space `V` (the model tangent space of the null
boundary) is a symmetric, positive-semidefinite ℝ-bilinear form `h` that is **degenerate
precisely along** a distinguished nowhere-zero direction `n` — i.e. the radical (null space) of
`h` is exactly the line `ℝ·n`. This IS the horizon geometry: `h` is the induced cross-section
metric, `n` the null generator.

## The acoustic-horizon instance

The 2+1 acoustic (sonic) horizon per the C0 verdict is `ℝ × S¹` — null-generator time `u` times
the `S¹` cross-section. Its tangent geometry at any point is the degenerate first-fundamental-form
on the 2-dimensional tangent model `ℝ × ℝ` (the `(∂_u, ∂_θ)` split): `h((a,b),(c,d)) = b·d` kills
the null generator `∂_u = (1,0)` and is Euclidean on the cross-section direction `∂_θ = (0,1)`.
Keeping the metric on the (algebraic) tangent model — not a smooth section over `ℝ × S¹` — is the
honest, scope-fenced content: no tangent-bundle / smooth-manifold machinery, exactly the degenerate
bilinear-form data the C0 verdict makes load-bearing.

The physical wrapper `AcousticHorizonBoundary` carries the **surface gravity κ** tied to the
in-tree `SKEFTHawking.SonicHorizon.surfaceGravity`, and bakes the C4 charge slot:
Penna's membrane supertranslation charge density `p = κ/8π` (eq 3.3/3.13), so the C4 target
`Q_f = ∫ f·κ/8π` plugs straight in.

## Non-vacuity pins (preemptive-strengthening discipline)

* `acoustic_h_kills_n` — kernel witness: `h` genuinely annihilates `n`.
* `acoustic_h_nondegenerate_offKernel` — off-kernel witness: an explicit `v` with `h v v = 1 ≠ 0`.
* `acoustic_h_eval` — a falsifiable `norm_num`-backed evaluation of the form.
* `acoustic_radical_eq_line` — the corank-1 statement: radical = `ℝ·n` exactly.

## References
- Donnay–Marteau, "Carrollian physics at the black hole horizon," arXiv:1903.09654.
- Penna, "BMS invariance and the membrane paradigm," arXiv:1508.06577 (charge density `p = κ/8π`).
- C0 verdict, `Lit-Search/Phase-6o-prime/C0_horizon_BMS_charge_algebra_verdict_20260720.md`.
-/

noncomputable section

namespace SKEFTHawking.Carrollian

/-! ## §1. The Carrollian structure class -/

/-- A **Carrollian structure** on a real vector space `V`: a symmetric, positive-semidefinite
ℝ-bilinear form `h` degenerate *precisely* along a nowhere-zero direction `n` (its radical is the
line `ℝ·n`). The ultra-relativistic degenerate boundary geometry of a horizon (Donnay–Marteau). -/
structure CarrollianStructure (V : Type*) [AddCommGroup V] [Module ℝ V] where
  /-- The degenerate cross-section metric (a symmetric ℝ-bilinear form). -/
  h : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  /-- `h` is symmetric. -/
  isSymm : ∀ u v, h u v = h v u
  /-- The distinguished null generator. -/
  n : V
  /-- The null generator is nonzero. -/
  n_ne_zero : n ≠ 0
  /-- `h` is positive-semidefinite. -/
  psd : ∀ v, 0 ≤ h v v
  /-- **Degenerate precisely along `n`**: the radical of `h` is exactly the line `ℝ·n`. -/
  radical_eq : ∀ v, (∀ w, h v w = 0) ↔ v ∈ Submodule.span ℝ ({n} : Set V)

namespace CarrollianStructure

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (C : CarrollianStructure V)

/-- `h` degenerates along `n`: the null generator lies in the radical. -/
theorem h_degenerate_n (w : V) : C.h C.n w = 0 :=
  (C.radical_eq C.n).mpr (Submodule.mem_span_singleton_self _) w

/-- `n` is a genuine null vector: `h n n = 0`. -/
theorem h_n_n : C.h C.n C.n = 0 := C.h_degenerate_n C.n

end CarrollianStructure

/-! ## §2. The acoustic-horizon instance -/

/-- The degenerate horizon form on the `(∂_u, ∂_θ)` tangent model `ℝ × ℝ`:
`h((a,b),(c,d)) = b·d`. Degenerate in the null-generator (time) direction, Euclidean on the
`S¹` cross-section direction. -/
def acousticHorizonForm : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun v w => v.2 * w.2)
    (fun v₁ v₂ w => by simp [Prod.snd_add, add_mul])
    (fun c v w => by simp [Prod.smul_snd, smul_eq_mul, mul_assoc])
    (fun v w₁ w₂ => by simp [Prod.snd_add, mul_add])
    (fun c v w => by simp [Prod.smul_snd, smul_eq_mul]; ring)

@[simp] theorem acousticHorizonForm_apply (v w : ℝ × ℝ) :
    acousticHorizonForm v w = v.2 * w.2 := rfl

/-- The Carrollian structure on the acoustic (sonic) horizon tangent model. `n = ∂_u = (1,0)` is
the null generator; the cross-section direction `∂_θ = (0,1)` is where `h` is non-degenerate. -/
def acousticHorizonCarrollian : CarrollianStructure (ℝ × ℝ) where
  h := acousticHorizonForm
  isSymm := fun u v => by simp [mul_comm]
  n := (1, 0)
  n_ne_zero := by
    intro hcon
    exact one_ne_zero (congrArg Prod.fst hcon)
  psd := fun v => by simp only [acousticHorizonForm_apply]; exact mul_self_nonneg _
  radical_eq := fun v => by
    constructor
    · intro hv
      have h1 : v.2 = 0 := by have := hv (0, 1); simpa using this
      rw [Submodule.mem_span_singleton]
      refine ⟨v.1, ?_⟩
      apply Prod.ext <;> simp [h1]
    · intro hv w
      rw [Submodule.mem_span_singleton] at hv
      obtain ⟨c, rfl⟩ := hv
      simp

/-! ## §3. Non-vacuity pins -/

/-- Kernel witness: `h` genuinely annihilates the null generator `n = ∂_u`. -/
theorem acoustic_h_kills_n (w : ℝ × ℝ) :
    acousticHorizonCarrollian.h acousticHorizonCarrollian.n w = 0 :=
  acousticHorizonCarrollian.h_degenerate_n w

/-- Off-kernel witness: `h` is genuinely non-degenerate on the cross-section direction —
`h (0,1) (0,1) = 1 ≠ 0`. Together with `acoustic_h_kills_n` this pins corank exactly 1. -/
theorem acoustic_h_nondegenerate_offKernel :
    acousticHorizonCarrollian.h ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) = 1 ∧
    acousticHorizonCarrollian.h ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) ≠ 0 := by
  have hval : acousticHorizonCarrollian.h ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) = 1 := by
    show acousticHorizonForm ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) = 1
    simp
  exact ⟨hval, by rw [hval]; norm_num⟩

/-- A falsifiable evaluation of the horizon form. -/
theorem acoustic_h_eval :
    acousticHorizonForm ((3, 2) : ℝ × ℝ) ((4, 5) : ℝ × ℝ) = 10 := by
  simp; norm_num

/-- The corank-1 statement, explicit: the radical of the acoustic horizon form is exactly the
null line `ℝ·(1,0)`. -/
theorem acoustic_radical_eq_line (v : ℝ × ℝ) :
    (∀ w, acousticHorizonForm v w = 0) ↔ v ∈ Submodule.span ℝ ({((1 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ)) :=
  acousticHorizonCarrollian.radical_eq v

/-! ## §4. The physical wrapper — surface gravity κ + the C4 charge slot -/

/-- Penna's membrane **supertranslation charge density** at the horizon: `p = κ/8π`
(Penna eq 3.3/3.13; C0 verdict §3). The C4 supertranslation charge target is
`Q_f = ∫ f · membranePressure κ`; this bakes the κ slot in now. -/
def membranePressure (κ : ℝ) : ℝ := κ / (8 * Real.pi)

/-- The acoustic-horizon Carrollian boundary: the degenerate tangent geometry (κ-independent)
packaged with the physical surface gravity `κ` and its membrane charge density `κ/8π`. -/
structure AcousticHorizonBoundary where
  /-- Surface gravity of the sonic horizon (Basic.lean `SonicHorizon.surfaceGravity`). -/
  κ : ℝ
  /-- Non-degenerate horizon: κ > 0. -/
  κ_pos : 0 < κ
  /-- The Carrollian tangent geometry. -/
  carroll : CarrollianStructure (ℝ × ℝ)

/-- Build the acoustic-horizon boundary from an in-tree sonic horizon: `κ` is that horizon's
surface gravity, tying the Carrollian boundary to the project's formalized acoustic substrate. -/
def AcousticHorizonBoundary.ofSonicHorizon {bg : SKEFTHawking.FluidBackground}
    (H : SKEFTHawking.SonicHorizon bg) : AcousticHorizonBoundary where
  κ := H.surfaceGravity
  κ_pos := H.surfaceGravity_pos
  carroll := acousticHorizonCarrollian

/-- The membrane charge density is positive (κ > 0). Falsifiable κ-tied pin baking the C4 slot. -/
theorem AcousticHorizonBoundary.membranePressure_pos (A : AcousticHorizonBoundary) :
    0 < membranePressure A.κ :=
  div_pos A.κ_pos (by positivity)

/-- On the boundary built from a sonic horizon, κ IS the horizon's surface gravity. -/
theorem AcousticHorizonBoundary.ofSonicHorizon_κ {bg : SKEFTHawking.FluidBackground}
    (H : SKEFTHawking.SonicHorizon bg) :
    (AcousticHorizonBoundary.ofSonicHorizon H).κ = H.surfaceGravity := rfl

end SKEFTHawking.Carrollian
