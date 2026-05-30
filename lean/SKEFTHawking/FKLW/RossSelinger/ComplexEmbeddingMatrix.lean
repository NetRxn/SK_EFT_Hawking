/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item G — the matrix-level `ℤ[ω][1/√2] → ℂ` embedding

Lifts `ZOmegaSqrt2.toComplex : ZOmegaSqrt2 →+* ℂ` to `2×2` matrices via
`RingHom.mapMatrix`, and records that it is a ring homomorphism (so it carries the
KMM gate word `interp gs` — a product of `gateMatrix`es over `ZOmegaSqrt2` — to the
product of the per-gate complex matrices). This is the matrix-level abstract↔analytic
bridge for Item G: the KMM exact synthesis output `interp (kmmReduce M) = M`
(`Mat2` over `ZOmegaSqrt2`) maps into `Matrix (Fin 2) (Fin 2) ℂ`, where the
`SU(2, ℂ)` operator-norm approximation of `cliffordTBaseFinder_kmm` lives.

## Global-phase caveat (the U(2)↔SU(2) gap, handled downstream)

The KMM `gateMatrix`es are `U(2)` matrices over `ℤ[ω][1/√2]` (determinant `ωᵏ`),
while the SK headline's `cliffordTGeneratingSet.ρ_hom` lands in `SU(2)`. Per gate the
two differ by a global phase: e.g. `toComplexMat (gateMatrix H) = -i·H_SU` (phase in
`ℤ[ω]`) but `toComplexMat (gateMatrix T) = e^{iπ/8}·T_SU` (phase `ω^{1/2} ∉ ℤ[ω][1/√2]`).
So `toComplexMat (interp gs)` equals `ρ_hom (word gs)` only up to a global phase
`e^{iθ}`; aligning that phase is the job of the base-finder construction (Item G's
`cliffordTBaseFinder_kmm`), not of this embedding.

## Headline results

  * `toComplexMat : Matrix (Fin 2) (Fin 2) ZOmegaSqrt2 → Matrix (Fin 2) (Fin 2) ℂ`.
  * `toComplexMat_interp` — `toComplexMat (interp gs) = ∏ toComplexMat (gateMatrix g)`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.ComplexEmbeddingSqrt2
import SKEFTHawking.FKLW.RossSelinger.CliffordTGate

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

open CliffordTGate
open scoped Matrix

/-- **The matrix-level `ℤ[ω][1/√2] → ℂ` embedding** (entrywise `ZOmegaSqrt2.toComplex`). -/
noncomputable def toComplexMat (M : Matrix (Fin 2) (Fin 2) ZOmegaSqrt2) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ZOmegaSqrt2.toComplex.mapMatrix M

/-- **`toComplexMat` carries a KMM gate word to the product of per-gate complex
matrices**: `toComplexMat (interp gs) = ∏ toComplexMat (gateMatrix g)`. (`mapMatrix`
of the ring hom is a ring hom, so it preserves the `interp` product.) -/
theorem toComplexMat_interp (gs : List CliffordTGate) :
    toComplexMat (interp gs) = (gs.map (fun g => toComplexMat (gateMatrix g))).prod := by
  simp only [toComplexMat]
  induction gs with
  | nil => rw [interp_nil, List.map_nil, List.prod_nil, map_one]
  | cons g gs ih => rw [interp_cons, map_mul, List.map_cons, List.prod_cons, ih]

/-! ## Per-gate-entry complex values

The complex images of the three non-trivial `ZOmegaSqrt2` constants appearing in the
KMM `gateMatrix`es (`ωS = ω`, `iS = ω² = i`, `invSqrt2 = 1/√2`). These are the
building blocks for the per-gate matrix values and the `gateMatrix ↔ ρ_CliffT`
phase bridge (the next Item-G sub-step). -/

/-- `toComplex ωS = e^{iπ/4}` (the `T`-gate phase). -/
theorem toComplex_omegaS : ZOmegaSqrt2.toComplex ωS = ZOmega.omegaC := by
  rw [ωS, ZOmegaSqrt2.of, ZOmegaSqrt2.toComplex_mk, pow_zero, div_one, ZOmega.toComplex_apply]
  simp [ZOmega.ω, ZOmega.omegaC]

/-- `toComplex iS = i` (the `S`-gate / `Y`-gate phase, `ω² = i`). -/
theorem toComplex_iS : ZOmegaSqrt2.toComplex iS = Complex.I := by
  rw [iS, map_mul, toComplex_omegaS, ← sq, ZOmega.omegaC_sq]

/-- `toComplex invSqrt2 = (√2)⁻¹` (the `H`-gate entry). -/
theorem toComplex_invSqrt2 :
    ZOmegaSqrt2.toComplex ZOmegaSqrt2.invSqrt2 = ((Real.sqrt 2)⁻¹ : ℂ) := by
  rw [ZOmegaSqrt2.invSqrt2, ZOmegaSqrt2.toComplex_mk, map_one, pow_one, ZOmegaSqrt2.s2C_eq, one_div]

/-! ## Per-gate complex matrix values

The explicit `Matrix (Fin 2) (Fin 2) ℂ` value of each KMM `gateMatrix` under
`toComplexMat`. These are the U(2) targets the `gateMatrix ↔ ρ_CliffT` phase bridge
matches against (next Item-G sub-step). `eta_fin_two` + `congr 1` resolves the matrix
indexing; the entries reduce by the per-gate-entry lemmas above. -/

/-- Shared entry-reduction tactic for the per-gate matrix values. -/
local macro "gateval" : tactic =>
  `(tactic| (congr 1 <;>
    simp only [toComplexMat, gateMatrix, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.one_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.of_apply, Matrix.smul_apply, Matrix.smul_cons, Matrix.smul_empty, smul_eq_mul,
      map_one, map_zero, map_neg, mul_one, mul_zero,
      toComplex_omegaS, toComplex_iS, toComplex_invSqrt2, Complex.ofReal_inv]))

theorem toComplexMat_gateMatrix_H : toComplexMat (gateMatrix CliffordTGate.H)
    = !![((Real.sqrt 2)⁻¹ : ℂ), (Real.sqrt 2)⁻¹; (Real.sqrt 2)⁻¹, -(Real.sqrt 2)⁻¹] := by
  rw [Matrix.eta_fin_two (toComplexMat _)]; gateval

theorem toComplexMat_gateMatrix_S : toComplexMat (gateMatrix CliffordTGate.S) = !![1, 0; 0, Complex.I] := by
  rw [Matrix.eta_fin_two (toComplexMat _)]; gateval

theorem toComplexMat_gateMatrix_T : toComplexMat (gateMatrix CliffordTGate.T) = !![1, 0; 0, ZOmega.omegaC] := by
  rw [Matrix.eta_fin_two (toComplexMat _)]; gateval

theorem toComplexMat_gateMatrix_X : toComplexMat (gateMatrix CliffordTGate.X) = !![0, 1; 1, 0] := by
  rw [Matrix.eta_fin_two (toComplexMat _)]; gateval

theorem toComplexMat_gateMatrix_Y : toComplexMat (gateMatrix CliffordTGate.Y) = !![0, -Complex.I; Complex.I, 0] := by
  rw [Matrix.eta_fin_two (toComplexMat _)]; gateval

theorem toComplexMat_gateMatrix_Z : toComplexMat (gateMatrix CliffordTGate.Z) = !![1, 0; 0, -1] := by
  rw [Matrix.eta_fin_two (toComplexMat _)]; gateval

theorem toComplexMat_gateMatrix_id : toComplexMat (gateMatrix CliffordTGate.id) = !![1, 0; 0, 1] := by
  rw [Matrix.eta_fin_two (toComplexMat _)]; gateval

theorem toComplexMat_gateMatrix_omega :
    toComplexMat (gateMatrix CliffordTGate.omega) = !![ZOmega.omegaC, 0; 0, ZOmega.omegaC] := by
  rw [Matrix.eta_fin_two (toComplexMat _)]; gateval

end SKEFTHawking.RossSelinger
