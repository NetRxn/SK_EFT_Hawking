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

end SKEFTHawking.RossSelinger
