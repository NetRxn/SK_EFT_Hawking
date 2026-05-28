/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A2′ — universal Clifford+CCZ+T SU(8) gate substrate (T-gates + embedding bridges)

The literal `{H_q1,H_q2,H_q3, CCZ}` alphabet is non-universal (OF-1: every word is a global phase
times a real orthogonal matrix, so the group is dense only in SO(8), not SU(8)). The genuinely
universal alphabet is **Clifford+CCZ+T** `{H_qi, T_qi, CNOT_{ij}, CCZ}`: the `T` gate is the
single-qubit infinite-order resource ({H,S} alone is the *finite* Clifford group), and lets the
per-qubit `𝔰𝔲(2)` flow lines reuse the Phase 6u Clifford+T SU(2) density
(`cliffordT_H_of_G_eq_top_unconditional`) pushed through the per-qubit embeddings.

This module ships the per-qubit **T-gates** `T_SU_on_qubit{1,2,3}_SU8 := qubit{1,2,3}Embed T_SU`
and records that the existing per-qubit **Hadamards** are literally the embedded images of `H_SU`
(`H_SU_on_qubit_i_SU8 = qubit_iEmbed H_SU`), so all per-qubit generators are uniformly
`qubit_iEmbed` images of the Clifford+T generators `{H_SU, T_SU}`. (CNOT_SU8 ships separately.)

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A2′ provenance

Phase 6y Roadmap §"Track T-A2′ detail" sub-wave T-A2′.1 PROPER — universal-alphabet gate substrate
(per-qubit T-gates + Hadamard-embedding bridges). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8QubitEmbed
import SKEFTHawking.FKLW.CliffordCCZSU8Substrate
import SKEFTHawking.FKLW.CliffordTGeneratingSet

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix

/-! ## 1. Per-qubit T-gates (SU(8)) via the per-qubit embedding -/

/-- **T-gate on qubit 1 (SU(8))**: `T_SU ⊗ I₄` = `qubit1Embed T_SU`. -/
noncomputable def T_SU_on_qubit1_SU8 : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ) :=
  qubit1Embed SKEFTHawking.FKLW.GenericSU2.T_SU

/-- **T-gate on qubit 2 (SU(8))**: `I₂ ⊗ T_SU ⊗ I₂` = `qubit2Embed T_SU`. -/
noncomputable def T_SU_on_qubit2_SU8 : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ) :=
  qubit2Embed SKEFTHawking.FKLW.GenericSU2.T_SU

/-- **T-gate on qubit 3 (SU(8))**: `I₄ ⊗ T_SU` = `qubit3Embed T_SU`. -/
noncomputable def T_SU_on_qubit3_SU8 : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ) :=
  qubit3Embed SKEFTHawking.FKLW.GenericSU2.T_SU

/-! ## 2. The existing per-qubit Hadamards are the embedded images of `H_SU` -/

/-- `H_SU_on_qubit1_SU8 = qubit1Embed H_SU`. -/
theorem H_SU_on_qubit1_SU8_eq_embed :
    H_SU_on_qubit1_SU8 = qubit1Embed SKEFTHawking.FKLW.GenericSU2.H_SU := Subtype.ext rfl

/-- `H_SU_on_qubit2_SU8 = qubit2Embed H_SU`. -/
theorem H_SU_on_qubit2_SU8_eq_embed :
    H_SU_on_qubit2_SU8 = qubit2Embed SKEFTHawking.FKLW.GenericSU2.H_SU := Subtype.ext rfl

/-- `H_SU_on_qubit3_SU8 = qubit3Embed H_SU`. -/
theorem H_SU_on_qubit3_SU8_eq_embed :
    H_SU_on_qubit3_SU8 = qubit3Embed SKEFTHawking.FKLW.GenericSU2.H_SU := Subtype.ext rfl

end SKEFTHawking.FKLW.CliffordCCZSU8
