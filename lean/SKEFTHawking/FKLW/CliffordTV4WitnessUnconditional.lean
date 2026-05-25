/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6u Track T-S.2 — Clifford+T v4-witness UNCONDITIONAL discharge + Track T-S.5 unconditional headline

Composes the conditional v4-witness discharge
(`cliffordT_v4_witness_from_accPt`, commit `2fa0330`) with the
substantive Niven-based AccPt 1 proof
(`cliffordT_accPt_one_unconditional`, commit `0448366`) to discharge
`cliffordT_v4_witness_tracked` UNCONDITIONALLY.

This closes Phase 6u Track T-S.2 — all tracked Props for Clifford+T are
now discharged, and the T-S.5 Clifford+T bundled-strict headline
`solovayKitaev_dawson_nielsen_quantitative_cliffordT_strict_constructive_tight`
becomes FULLY UNCONDITIONAL.

## Headlines (all UNCONDITIONAL, kernel-only)

  * `cliffordT_v4_witness_discharged` — `cliffordT_v4_witness_tracked`
    holds. Composes the case-analysis substrate (Agent A) with the
    Niven-based infinite-order proof (Agent B) via the standard Phase 5
    Step 13 substrate (vonNeumann + ts_Ad_LI + expAmbient_unitary_conj).

  * `cliffordT_density_unconditional` — Clifford+T density in SU(2)
    via `IsDenseInSU2_gs cliffordTGeneratingSet`.

  * `cliffordT_H_of_G_eq_top_unconditional` —
    `H_of_G cliffordTGeneratingSet = ⊤`.

  * `solovayKitaev_dawson_nielsen_quantitative_cliffordT_strict_constructive_tight_unconditional`
    — the Phase 6u Track T-S.5 UNCONDITIONAL bundled-strict Clifford+T
    headline. Conjoins:
      - Error: `‖ρ_CliffT (compile U ε) - U‖ ≤ ε`
      - Length: polylog `O(log(1/ε)^skLengthExponent)` word length
    at the SAME compile level `skLevel_polylog ε`. The canonical
    Dawson-Nielsen form for Clifford+T, kernel-only.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new axioms): respected.
- **Strengthening discipline**: substantive composition; load-bearing
  unconditional discharge of `cliffordT_v4_witness_tracked` closes the
  last remaining tracked Prop on the Clifford+T chain.

-/

import SKEFTHawking.FKLW.CliffordTV4WitnessDischarge
import SKEFTHawking.FKLW.CliffordTInfiniteOrder
import SKEFTHawking.FKLW.CliffordTQuantitative

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

open Matrix SKEFTHawking SKEFTHawking.FKLW
  SKEFTHawking.FKLW.SolovayKitaevRecursion
  SKEFTHawking.FKLW.SolovayKitaevLengthBound

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## Unconditional v4-witness discharge

Composes the conditional discharge with the Niven-based AccPt 1 proof. -/

/-- **UNCONDITIONAL Clifford+T v4-witness discharge** (Phase 6u T-S.2
culmination). -/
theorem cliffordT_v4_witness_discharged : cliffordT_v4_witness_tracked :=
  cliffordT_v4_witness_from_accPt cliffordT_accPt_one_unconditional

/-- **UNCONDITIONAL Clifford+T density in SU(2)**. -/
theorem cliffordT_density_unconditional :
    IsDenseInSU2_gs cliffordTGeneratingSet :=
  cliffordT_density_of_tracked cliffordT_v4_witness_discharged

/-- **UNCONDITIONAL `H_of_G cliffordTGeneratingSet = ⊤`**. -/
theorem cliffordT_H_of_G_eq_top_unconditional :
    H_of_G cliffordTGeneratingSet = ⊤ :=
  cliffordT_H_of_G_eq_top_of_tracked cliffordT_v4_witness_discharged

/-! ## T-S.5 UNCONDITIONAL Clifford+T strict headline

Composes the unconditional v4-witness discharge with the conditional
Track T-S.5 headline to produce the fully unconditional Clifford+T
canonical quantitative Solovay-Kitaev statement. -/

/-- **Phase 6u Track T-S.5 UNCONDITIONAL HEADLINE**.

For any target `U ∈ SU(2)` and precision `ε ∈ (0, ε₀]`, the Clifford+T
constructive Dawson-Nielsen Solovay-Kitaev compiler returns a
`FreeGroup (Fin 2)` word over `{of 0 ↦ H_SU, of 1 ↦ T_SU}` with BOTH:

  - **Error**: `‖ρ_CliffT (compile U ε) - U‖ ≤ ε`
  - **Length**: polylog `O(log(1/ε)^skLengthExponent)` word length

Both bounds at the SAME algorithmic compile level `skLevel_polylog ε`.

This is the canonical Clifford+T Dawson-Nielsen 2006 quantitative
statement, instantiated via the Phase 6u generic substrate (Waves 1-6 +
Wave 4b) and discharged UNCONDITIONALLY via the Niven-based infinite-
order chain. Standard kernel only `{propext, Classical.choice, Quot.sound}`.

**Closes Phase 6u Track T-S.5**: the last tracked Prop
(`cliffordT_v4_witness_tracked`) is now substantively discharged. -/
theorem solovayKitaev_dawson_nielsen_quantitative_cliffordT_strict_constructive_tight_unconditional
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ)
    (hε_pos : 0 < ε) (hε_le : ε ≤ ε₀) :
    ‖((cliffordTGeneratingSet.ρ_hom
            (solovayKitaev_compile_strict_constructive_generic
              cliffordTGeneratingSet
              (cliffordTBaseFinder cliffordT_v4_witness_discharged) U ε) :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε ∧
    skLength (skLevel_polylog ε) ≤
      skLengthConst * (Real.log (1 / ε)) ^ skLengthExponent :=
  solovayKitaev_dawson_nielsen_quantitative_cliffordT_strict_constructive_tight
    cliffordT_v4_witness_discharged U ε hε_pos hε_le

end SKEFTHawking.FKLW.GenericSU2
