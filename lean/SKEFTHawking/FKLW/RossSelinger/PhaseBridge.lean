/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item G — the KMM-gate → FreeGroup map (phase-bridge defs)

KMM exact synthesis produces a `List CliffordTGate` (8-gate ADT over the U(2) ring
`ZOmegaSqrt2`); the SK headline's `ρ_CliffT` consumes a `FreeGroup (Fin 2)` word
(`of 0 = H_SU`, `of 1 = T_SU`, the two SU(2) generators). This file ships the
translation `gateWord : CliffordTGate → FreeGroup (Fin 2)` and its list lift
`freeword`, plus the per-gate global phase `gatePhase`/`phaseProd` that relates the
two pictures:

  `toComplexMat (interp gs) = phaseProd gs • ρ_CliffT (freeword gs)`     (the bridge)

The phase is unavoidable: KMM gates are `U(2)` (det `ωᵏ`), `ρ_CliffT` is `SU(2)`. Per
gate `toComplexMat (gateMatrix g) = gatePhase g • ρ_CliffT (gateWord g)` with
`gatePhase g = e^{iπk/8}` (a 16th root, ∉ `ℤ[ω][1/√2]`). For a `det = 1` word — the
shape Ross-Selinger assembles — `phaseProd gs = ±1`, and `ρ_CliffT (H·H) = -I` makes
the residual sign `HH`-correctable.

**Validated** `scripts/phase_bridge_validation.py` (0/2000 failures, incl. the ±1
reduction). The per-gate `toComplexMat (gateMatrix g) = gatePhase g • ρ_CliffT (gateWord g)`
identities and the word-level bridge are the next increment (this file ships the
underlying definitions).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.ComplexEmbeddingMatrix
import SKEFTHawking.FKLW.CliffordTGeneratingSet

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

open CliffordTGate

/-- The two SU(2) generators as `FreeGroup (Fin 2)` letters. -/
abbrev fgH : FreeGroup (Fin 2) := FreeGroup.of (⟨0, by decide⟩ : Fin 2)
/-- The `T` generator letter. -/
abbrev fgT : FreeGroup (Fin 2) := FreeGroup.of (⟨1, by decide⟩ : Fin 2)

/-- **KMM gate → `FreeGroup (Fin 2)` word** over the SU(2) generators `H_SU = of 0`,
`T_SU = of 1` (validated, `scripts/phase_bridge_validation.py`):
`H↦H, T↦T, S↦T², Z↦T⁴, X↦H·T⁴·H, Y↦X·Z-word, id/ω↦1`. The global phase the U(2)
`gateMatrix` carries over the SU(2) image is tracked by `gatePhase`. -/
def gateWord : CliffordTGate → FreeGroup (Fin 2)
  | .H => fgH
  | .T => fgT
  | .S => fgT ^ 2
  | .Z => fgT ^ 4
  | .X => fgH * fgT ^ 4 * fgH
  | .Y => (fgH * fgT ^ 4 * fgH) * fgT ^ 4
  | .id => 1
  | .omega => 1

/-- **The per-gate global phase** `gatePhase g ∈ U(1)` with
`toComplexMat (gateMatrix g) = gatePhase g • ρ_CliffT (gateWord g)` (validated). A
power of `e^{iπ/8}`; not in `ℤ[ω][1/√2]`, hence valued in `ℂ`. -/
noncomputable def gatePhase : CliffordTGate → ℂ
  | .H => -Complex.I
  | .T => Complex.exp (Real.pi / 8 * Complex.I)
  | .S => ZOmega.omegaC
  | .Z => Complex.I
  | .X => -Complex.I
  | .Y => Complex.I
  | .id => 1
  | .omega => ZOmega.omegaC

/-- **The FreeGroup word of a KMM gate list** (the map `cliffordTBaseFinder_kmm` uses:
`List CliffordTGate → FreeGroup (Fin 2)`). -/
def freeword (gs : List CliffordTGate) : FreeGroup (Fin 2) := (gs.map gateWord).prod

/-- **The accumulated global phase of a KMM gate list** (`= ±1` for `det`-1 words). -/
noncomputable def phaseProd (gs : List CliffordTGate) : ℂ := (gs.map gatePhase).prod

@[simp] theorem freeword_nil : freeword [] = 1 := rfl
@[simp] theorem freeword_cons (g : CliffordTGate) (gs : List CliffordTGate) :
    freeword (g :: gs) = gateWord g * freeword gs := by
  simp [freeword]
@[simp] theorem phaseProd_nil : phaseProd [] = 1 := rfl
@[simp] theorem phaseProd_cons (g : CliffordTGate) (gs : List CliffordTGate) :
    phaseProd (g :: gs) = gatePhase g * phaseProd gs := by
  simp [phaseProd]

/-! ## Per-gate phase-bridge identities (generators)

`toComplexMat (gateMatrix g) = gatePhase g • ρ_CliffT (gateWord g)` — the per-gate
bridge connecting the U(2) KMM gate to its SU(2) `ρ_CliffT` image (validated for all 8;
the two generators `H, T` shipped here, the derived gates `S/Z/X/Y/id/ω` are the next
increment via the same `eta_fin_two` + `congr` RHS-value pattern). -/

open scoped Matrix in
open SKEFTHawking.FKLW.GenericSU2 in
/-- **H phase-bridge identity**: `toComplexMat (gateMatrix H) = (-i) • ρ_CliffT (of 0)`. -/
theorem toComplexMat_gateMatrix_eq_H :
    toComplexMat (gateMatrix CliffordTGate.H)
      = gatePhase CliffordTGate.H • ((ρ_CliffT (gateWord CliffordTGate.H) :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [show gatePhase CliffordTGate.H = -Complex.I from rfl,
      show gateWord CliffordTGate.H = fgH from rfl, fgH, ρ_CliffT_of_0,
      toComplexMat_gateMatrix_H]
  show _ = (-Complex.I) • H_SU_mat
  rw [Matrix.eta_fin_two ((-Complex.I) • H_SU_mat), H_SU_mat]
  congr 1 <;>
    (simp only [Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
      smul_eq_mul, mul_one, mul_neg, Complex.ofReal_inv]
     rw [show -Complex.I * (Complex.I / (↑(Real.sqrt 2))) = (↑(Real.sqrt 2))⁻¹ from by
       rw [div_eq_mul_inv, ← mul_assoc, neg_mul, Complex.I_mul_I]; ring])

open scoped Matrix in
open SKEFTHawking.FKLW.GenericSU2 in
/-- **T phase-bridge identity**: `toComplexMat (gateMatrix T) = e^{iπ/8} • ρ_CliffT (of 1)`. -/
theorem toComplexMat_gateMatrix_eq_T :
    toComplexMat (gateMatrix CliffordTGate.T)
      = gatePhase CliffordTGate.T • ((ρ_CliffT (gateWord CliffordTGate.T) :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h00 : Complex.exp (↑Real.pi / 8 * Complex.I) * Complex.exp (-(Complex.I * ↑Real.pi / 8)) = 1 := by
    rw [← Complex.exp_add,
      show (↑Real.pi / 8 * Complex.I + -(Complex.I * ↑Real.pi / 8)) = 0 from by ring, Complex.exp_zero]
  have h11 : Complex.exp (↑Real.pi / 8 * Complex.I) * Complex.exp (Complex.I * ↑Real.pi / 8)
      = ZOmega.omegaC := by rw [← Complex.exp_add, ZOmega.omegaC]; congr 1; ring
  rw [show gatePhase CliffordTGate.T = Complex.exp (Real.pi / 8 * Complex.I) from rfl,
      show gateWord CliffordTGate.T = fgT from rfl, fgT, ρ_CliffT_of_1,
      toComplexMat_gateMatrix_T]
  show _ = (Complex.exp (Real.pi / 8 * Complex.I)) • T_SU_mat
  rw [Matrix.eta_fin_two ((Complex.exp (Real.pi / 8 * Complex.I)) • T_SU_mat), T_SU_mat]
  congr 1 <;>
    simp only [Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
      smul_eq_mul, mul_zero, h00, h11]

end SKEFTHawking.RossSelinger
