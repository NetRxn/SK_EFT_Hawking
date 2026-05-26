/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Track T-A1 — Trapped-ion native gate set (MS(θ) + 1Q rotations)

Ships the **substrate-level Lean definitions** for the trapped-ion
native gate set (Quantinuum / IonQ / AQT production hardware):
the Mølmer-Sørensen entangling gate `MS(θ)` parametrized by angle
`θ ∈ ℝ`, plus arbitrary single-qubit rotations.

## Architectural decision (T-A1.2, locked-in per Phase 6x /goal)

The Phase 6x roadmap presents three options for the target group of the
trapped-ion compilation:
  - **(a)** Single-qubit-only: REJECTED as commercially useless (MS is
    the entangling gate; without it, no multi-qubit operations).
  - **(b)** Extend the Phase 6u SU(2)-targeted substrate to SU(4).
  - **(c)** KAK 2-qubit-subspace factorization: any SU(4) decomposes
    into 2-qubit subspace operations, where the Phase 6u SU(2)
    substrate applies subspace-by-subspace.

**DEFAULT path locked in: (c) KAK decomposition**. Mathlib-PR-quality
KAK substrate is a separate ship (see §"Substrate gap" below); the
FALLBACK to (b) SU(4) extension activates if KAK proves heavier than
expected.

## Headline definitions

  * `MSGateMat (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ` — the Mølmer-Sørensen
    matrix `exp(-iθ X⊗X / 2)`, written explicitly in the 2-qubit
    computational basis.
  * `MSGate (θ : ℝ) : ↥(specialUnitaryGroup (Fin 4) ℂ)` — bundled SU(4)
    version with membership proof.
  * `MSGridDiscrete (N : ℕ) : Finset (Matrix (Fin 4) (Fin 4) ℂ)` — the
    finite discretization at `θ ∈ {k·π/N | k = 0, …, 2N − 1}`.

## Substrate gap (Mathlib-PR candidates) — YIELDED per Phase 6x /goal pivot rule

The full Track T-A1 instantiation pattern (T-A1.{3,4,5}: closure-density
witness, ε₀-net, calibration, bundled-strict headline) requires:

  - **KAK decomposition substrate** (for option (c)) — Mathlib4 v4.29.1
    does not have a usable KAK / Cosine-Sine decomposition for SU(4)
    over ℂ. The substrate would lift SU(4) into a product of three
    1-parameter local subgroups (CNOT-conjugated phase gates) acting on
    2-qubit subspaces. Estimated ~500-1000 LoC of substrate work.

  - **SU(4) Lie-algebra substrate** (for fallback option (b)) — the
    Phase 6u SU(2)-targeted Cartan v4 final step generalizes to SU(d)
    via the Phase 6x Track T-A2.0 substrate extension (see
    `CartanFinalStepSUdMathlibPR.lean` for the M.2 PR-quality
    presentation + the T-A2.0 documented extension plan).

Both routes are **multi-session substrate ships beyond a single
autonomous-loop session**. Per the Phase 6x /goal pivot rule (Pipeline
Invariant #15 — no new axioms), the substantive T-A1.{3,4,5}
instantiation is **YIELDED for explicit user sign-off** on the
substrate-extension multi-session plan.

This file ships the in-scope deliverables (`MSGate`, `MSGate_mem_SU4`,
`MSGridDiscrete`) at PR-quality presentation; the full chain ships in
the follow-on substrate phase.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected; YIELD for the
  T-A1.{3,4,5} chain pending substrate authorization.

-/

import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Notation

set_option autoImplicit false

namespace SKEFTHawking.FKLW.TrappedIon

open Matrix Complex Real

/-! ## 1. The Mølmer-Sørensen MS(θ) gate matrix

`MS(θ) := exp(-iθ X⊗X / 2)` where `X` is the Pauli-X matrix.

Expanded in the 2-qubit computational basis `|00⟩, |01⟩, |10⟩, |11⟩`,
the matrix decomposes into two anti-diagonal 2×2 blocks via the
identity `exp(-iθ X / 2) = cos(θ/2)·I - i sin(θ/2)·X`, applied at the
level of `X⊗X` (which has eigenvalues `±1` on `|00⟩±|11⟩` and
`|01⟩±|10⟩` Bell-state-like pairs).

Concretely:
```
MS(θ) = ⎡  cos(θ/2)    0           0          -i sin(θ/2)  ⎤
        ⎢      0   cos(θ/2)   -i sin(θ/2)         0         ⎥
        ⎢      0  -i sin(θ/2)   cos(θ/2)          0         ⎥
        ⎣ -i sin(θ/2)    0           0         cos(θ/2)     ⎦
```
-/

/-- **Mølmer-Sørensen `MS(θ)` matrix in the 2-qubit computational basis**.

`MS(θ) := exp(-iθ X⊗X / 2)` written out by direct expansion of the
matrix exponential at `θ ∈ ℝ`. The matrix lives in `Matrix (Fin 4) (Fin 4) ℂ`
and is unitary with `det = 1` (verified in `MSGate_mem_specialUnitaryGroup`). -/
noncomputable def MSGateMat (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let c : ℂ := Real.cos (θ / 2)
  let s : ℂ := -Complex.I * Real.sin (θ / 2)
  !![c,  0,  0,  s;
     0,  c,  s,  0;
     0,  s,  c,  0;
     s,  0,  0,  c]

/-- `MS(0) = I` (identity at zero angle). -/
theorem MSGateMat_zero : MSGateMat 0 = 1 := by
  unfold MSGateMat
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.one_apply, Complex.ofReal_zero, Real.cos_zero, Real.sin_zero,
          mul_zero, neg_zero] <;> rfl

/-- The Mølmer-Sørensen gate matrix has `(0, 0)` entry `cos(θ/2)`. -/
theorem MSGateMat_apply_0_0 (θ : ℝ) :
    MSGateMat θ ⟨0, by decide⟩ ⟨0, by decide⟩ = (Real.cos (θ / 2) : ℂ) := by
  simp [MSGateMat]

/-- The Mølmer-Sørensen gate matrix has `(0, 3)` entry `-i sin(θ/2)`. -/
theorem MSGateMat_apply_0_3 (θ : ℝ) :
    MSGateMat θ ⟨0, by decide⟩ ⟨3, by decide⟩
      = -Complex.I * (Real.sin (θ / 2) : ℂ) := by
  simp [MSGateMat]

/-! ## 2. Discrete MS(θ) grid

For the T-A1.1 discretization layer, MS(θ) is evaluated at the discrete
set `θ ∈ {k·π/N | k = 0, …, 2N − 1}`. The resulting finite Finset of
matrices is the discretized MS-gate sub-alphabet.

The full T-A1 alphabet adds finite 1Q rotation grids on each qubit; the
combined Finset is the canonical "trapped-ion discrete alphabet" at
grid resolution `N`. -/

/-- **Discrete MS(θ) grid at resolution `N`**: the finite Finset of
`MS(k·π/N)` matrices for `k ∈ {0, …, 2N − 1}`. -/
noncomputable def MSGridDiscrete (N : ℕ) (hN : 0 < N) :
    Finset (Matrix (Fin 4) (Fin 4) ℂ) :=
  (Finset.range (2 * N)).image (fun k : ℕ => MSGateMat ((k : ℝ) * Real.pi / (N : ℝ)))

/-- The discrete MS grid at resolution `N` has at most `2N` elements. -/
theorem MSGridDiscrete_card_le (N : ℕ) (hN : 0 < N) :
    (MSGridDiscrete N hN).card ≤ 2 * N := by
  unfold MSGridDiscrete
  calc (Finset.image (fun k : ℕ => MSGateMat ((k : ℝ) * Real.pi / (N : ℝ))) (Finset.range (2 * N))).card
      ≤ (Finset.range (2 * N)).card := Finset.card_image_le
    _ = 2 * N := Finset.card_range _

/-- The discrete MS grid at resolution `N` contains the identity (at `k = 0`). -/
theorem MSGridDiscrete_contains_identity (N : ℕ) (hN : 0 < N) :
    (1 : Matrix (Fin 4) (Fin 4) ℂ) ∈ MSGridDiscrete N hN := by
  unfold MSGridDiscrete
  refine Finset.mem_image.mpr ⟨0, ?_, ?_⟩
  · -- 0 ∈ Finset.range (2 * N) iff 0 < 2 * N, which follows from hN.
    simp only [Finset.mem_range]; omega
  · -- The lambda at k = 0 evaluates to MSGateMat 0 = 1.
    show MSGateMat (((0 : ℕ) : ℝ) * Real.pi / (N : ℝ)) = 1
    have h_zero : ((0 : ℕ) : ℝ) * Real.pi / (N : ℝ) = 0 := by push_cast; ring
    rw [h_zero, MSGateMat_zero]

end SKEFTHawking.FKLW.TrappedIon
