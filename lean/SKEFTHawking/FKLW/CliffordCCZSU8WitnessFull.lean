/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A2′.2/.5 (D) witness — SU(8) `ClosureDenseWitness` + UNCONDITIONAL headline

Assembles the substantive `ClosureDenseWitness cliffordCCZGeneratingSetSU8` from the three shipped
halves and feeds it to `cliffordCCZSU8_headline_of_witness`, closing the FULL multi-qubit
Solovay-Kitaev headline at SU(8) UNCONDITIONALLY:

  * `hX_in_sud` — `suEightTangent_in_sud` (the 63 tensor-Pauli tangents are traceless skew-Herm);
  * `hX_spans`  — `suEightTangent_spans`  (Hilbert-Schmidt completeness — they ℝ-span `𝔰𝔲(8)`);
  * `hX_flow`   — `suEightTangent_flow`   (9 per-qubit flows + 54 entangling spread flows).

## Honest scope (what this ship is, and is NOT)

The generating set `cliffordCCZGeneratingSetSU8` is the **universal Clifford+CCZ+T** alphabet
`{H_qi, T_qi, CNOT_ij, CCZ}`. Its closure-density — and hence this headline — rests **entirely on
the `{H,T,CNOT}` (Clifford+T) sub-alphabet**: the per-qubit flow lines come from the shipped Phase 6u
Clifford+T SU(2) density (the `T` gate is the single-qubit ∞-order resource), spread to the 63
tangents by Clifford/CNOT conjugation. **`CCZ` is over-complete and is not used in the witness
construction.** So this ships *Clifford+T-at-SU(8)* (with `CCZ` present in the alphabet), a universal
3-qubit compiler — NOT the stronger "`CCZ` as the essential non-Clifford resource" statement (literal
Clifford+CCZ without `T`), which needs a von-Neumann/Kronecker irrational seed and is tracked as a
strengthening follow-on (`Lit-Search/Tasks/phase6y_literal_cliffordCCZ_su8_irrational_seed_spike.md`).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected — the witness is a plain `def`; the tracked Prop
    `cliffordCCZSU8_v4_witness_tracked` is now a discharged THEOREM, not a hypothesis.

## Phase 6y Track T-A2′ provenance

Phase 6y Roadmap §"Track T-A2′ detail" sub-wave T-A2′.2 PROPER (witness assembly) + T-A2′.5
(UNCONDITIONAL headline). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8EntanglerFlow
import SKEFTHawking.FKLW.CliffordCCZSU8TangentSpan
import SKEFTHawking.FKLW.CliffordCCZSU8WitnessTracked
import SKEFTHawking.FKLW.GenericSUdPerAlphabetHeadlineFromWitness

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix SKEFTHawking.FKLW.GenericSUd

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. The substantive `ClosureDenseWitness` -/

/-- **The substantive SU(8) Clifford+CCZ(+T) closure-density witness**: the 63 tensor-Pauli tangents
`X_{abc}`, traceless skew-Hermitian (`hX_in_sud`), spanning `𝔰𝔲(8)` (`hX_spans`), each with a full
1-parameter flow line in `H_of_G` (`hX_flow`). -/
noncomputable def cliffordCCZSU8ClosureDenseWitness :
    ClosureDenseWitness cliffordCCZGeneratingSetSU8 where
  n := 63
  X := suEightTangent
  hX_in_sud := suEightTangent_in_sud
  hX_spans := suEightTangent_spans
  hX_flow := suEightTangent_flow

/-! ## 2. The tracked v4-witness Prop is now a discharged THEOREM -/

/-- **The Clifford+CCZ SU(8) v4-witness tracked Prop is discharged.** This converts every
`…_of_tracked` consumer in `CliffordCCZSU8WitnessTracked` into an UNCONDITIONAL statement. -/
theorem cliffordCCZSU8_v4_witness_tracked_holds : cliffordCCZSU8_v4_witness_tracked :=
  ⟨63, suEightTangent, suEightTangent_in_sud, suEightTangent_spans, suEightTangent_flow⟩

/-! ## 3. UNCONDITIONAL SU(8) Clifford+CCZ(+T) Solovay-Kitaev headline -/

/-- **UNCONDITIONAL `SolovayKitaevHeadline_FreeGroup_SUd` for SU(8) Clifford+CCZ(+T)**: the
bundled-strict headline (error bound + F#4 word-length conjunct, honest `log 5/log(3/2)` exponent)
follows from the substantive `ClosureDenseWitness` alone. -/
theorem cliffordCCZSU8_solovayKitaev_headline_unconditional :
    SolovayKitaevHeadline_FreeGroup_SUd cliffordCCZGeneratingSetSU8 rfl :=
  cliffordCCZSU8_headline_of_witness cliffordCCZSU8ClosureDenseWitness

end SKEFTHawking.FKLW.CliffordCCZSU8
