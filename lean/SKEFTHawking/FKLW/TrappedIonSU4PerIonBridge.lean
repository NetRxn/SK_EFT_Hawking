/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A1′.2 (D) witness substrate — per-ion embedding ↔ alphabet generators

Bridges the per-ion embeddings `ion1Embed` / `ion2Embed` (continuous monoid homs
`SU(2) → SU(4)`) to the actual trapped-ion alphabet generators: the embedding of each
Clifford+T generator (`H_SU`, `T_SU`) is exactly the corresponding per-ion SU(4) gate
(`H_SU_on_ion{1,2}_SU4`, `T_SU_on_ion{1,2}_SU4`), which are tokens 0–3 of
`trappedIonGeneratingSetSU4`.

These identities are the link that lets the already-shipped SU(2) Clifford+T density
(`cliffordT_density_unconditional`) flow through `ion{1,2}Embed` into
`H_of_G (trappedIonGeneratingSetSU4 N hN)`: each embedded Clifford+T generator is in the
range of the trapped-ion representation, so the embedded Clifford+T subgroup sits inside the
trapped-ion generated subgroup, and its closure (= the embedded SU(2)) lands in the closed
`H_of_G`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A1′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.2 PROPER — (D) witness substrate
(per-ion embedding ↔ generator bridge). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.TrappedIonSU4IonEmbed
import SKEFTHawking.FKLW.CliffordTGeneratingSet

set_option autoImplicit false

namespace SKEFTHawking.FKLW.TrappedIonSU4

open Matrix

/-- `ion1Embed H_SU = H_SU_on_ion1_SU4` (the ion-1 Hadamard alphabet generator). -/
theorem ion1Embed_H_SU :
    ion1Embed SKEFTHawking.FKLW.GenericSU2.H_SU = H_SU_on_ion1_SU4 := by
  apply Subtype.ext; rfl

/-- `ion1Embed T_SU = T_SU_on_ion1_SU4` (the ion-1 T alphabet generator). -/
theorem ion1Embed_T_SU :
    ion1Embed SKEFTHawking.FKLW.GenericSU2.T_SU = T_SU_on_ion1_SU4 := by
  apply Subtype.ext; rfl

/-- `ion2Embed H_SU = H_SU_on_ion2_SU4` (the ion-2 Hadamard alphabet generator). -/
theorem ion2Embed_H_SU :
    ion2Embed SKEFTHawking.FKLW.GenericSU2.H_SU = H_SU_on_ion2_SU4 := by
  apply Subtype.ext; rfl

/-- `ion2Embed T_SU = T_SU_on_ion2_SU4` (the ion-2 T alphabet generator). -/
theorem ion2Embed_T_SU :
    ion2Embed SKEFTHawking.FKLW.GenericSU2.T_SU = T_SU_on_ion2_SU4 := by
  apply Subtype.ext; rfl

end SKEFTHawking.FKLW.TrappedIonSU4
