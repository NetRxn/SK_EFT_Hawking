/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A1′.2/.5 (D) witness — SU(4) trapped-ion `ClosureDenseWitness` + UNCONDITIONAL headline

Assembles the substantive `ClosureDenseWitness (trappedIonGeneratingSetSU4 N hN)` for EVEN `N`
from the three shipped halves:

  * `hX_in_sud`  — `suFourTangent_in_sud`  (the 15 tensor-Pauli tangents are traceless skew-Herm);
  * `hX_spans`   — `suFourTangent_spans`   (Hilbert-Schmidt completeness — they ℝ-span `𝔰𝔲(4)`);
  * `hX_flow`    — `suFourTangent_flow`    (per-ion flows D1 + Clifford-spread entangling flows §7).

Feeding the witness to the shipped `trappedIonSU4_headline_of_witness` closes the FULL trapped-ion
SU(4) Solovay-Kitaev headline `SolovayKitaevHeadline_FreeGroup_SUd` UNCONDITIONALLY (for even `N`):
both the error bound `‖ρ_hom(compile U ε) − U‖ ≤ ε` AND the F#4 concrete word-length conjunct
`(compile U ε).toWord.length ≤ c·log(1/ε)^(log 5/log(3/2))`. The named `trappedIonSU4FullHeadline`
Prop is closed identically.

`N` even is required because the witness's entangling half conjugates the per-ion `X₃₀` flow by
`MS(π/2)`, which is a grid generator only when `π/2 = (N/2)·π/N` lies on the alphabet's `kπ/N` MS
grid (`k = N/2 ∈ ℕ`); at odd `N` (e.g. `N = 1`, where `MS(π)` is local) the entangler is absent.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected — the witness is a plain `def`; the tracked
    Prop `trappedIonSU4_v4_witness_tracked` is now a discharged THEOREM, not a hypothesis.

## Phase 6y Track T-A1′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.2 PROPER (witness assembly) + T-A1′.5
(UNCONDITIONAL headline). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.TrappedIonSU4EntanglerSpread
import SKEFTHawking.FKLW.TrappedIonSU4TangentSpan
import SKEFTHawking.FKLW.TrappedIonSU4WitnessTracked
import SKEFTHawking.FKLW.TrappedIonSU4FullHeadlineForm
import SKEFTHawking.FKLW.GenericSUdPerAlphabetHeadlineFromWitness

set_option autoImplicit false

namespace SKEFTHawking.FKLW.TrappedIonSU4

open Matrix SKEFTHawking.FKLW.GenericSUd

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. The substantive `ClosureDenseWitness` (even `N`) -/

/-- **The substantive trapped-ion SU(4) closure-density witness** (for even `N`): the 15
tensor-Pauli tangents `X_{ab}`, traceless skew-Hermitian (`hX_in_sud`), spanning `𝔰𝔲(4)`
(`hX_spans`), each with full 1-parameter flow line in `H_of_G` (`hX_flow`). -/
noncomputable def trappedIonSU4ClosureDenseWitness (N : ℕ) (hN : 0 < N) (hN2 : 2 ∣ N) :
    ClosureDenseWitness (trappedIonGeneratingSetSU4 N hN) where
  n := 15
  X := suFourTangent
  hX_in_sud := suFourTangent_in_sud
  hX_spans := suFourTangent_spans
  hX_flow := suFourTangent_flow N hN hN2

/-! ## 2. The tracked v4-witness Prop is now a discharged THEOREM (even `N`) -/

/-- **The trapped-ion SU(4) v4-witness tracked Prop is discharged** (for even `N`). This converts
every `…_of_tracked` consumer in `TrappedIonSU4WitnessTracked` into an UNCONDITIONAL statement. -/
theorem trappedIonSU4_v4_witness_tracked_holds (N : ℕ) (hN : 0 < N) (hN2 : 2 ∣ N) :
    trappedIonSU4_v4_witness_tracked N hN :=
  ⟨15, suFourTangent, suFourTangent_in_sud, suFourTangent_spans, suFourTangent_flow N hN hN2⟩

/-! ## 3. UNCONDITIONAL SU(4) trapped-ion Solovay-Kitaev headline (even `N`) -/

/-- **UNCONDITIONAL `SolovayKitaevHeadline_FreeGroup_SUd` for trapped-ion SU(4)** (even `N`):
the bundled-strict headline (error bound + F#4 word-length conjunct, honest `log 5/log(3/2)`
exponent) follows from the substantive `ClosureDenseWitness` alone. -/
theorem trappedIonSU4_solovayKitaev_headline_unconditional (N : ℕ) (hN : 0 < N) (hN2 : 2 ∣ N) :
    SolovayKitaevHeadline_FreeGroup_SUd (trappedIonGeneratingSetSU4 N hN) rfl :=
  trappedIonSU4_headline_of_witness N hN (trappedIonSU4ClosureDenseWitness N hN hN2)

/-- **UNCONDITIONAL `trappedIonSU4FullHeadline`** (even `N`): the named T-A1′.5 PROPER headline
Prop, discharged from the witness via the bundled-strict headline. -/
theorem trappedIonSU4FullHeadline_holds (N : ℕ) (hN : 0 < N) (hN2 : 2 ∣ N) :
    trappedIonSU4FullHeadline N hN := by
  obtain ⟨ε₀, c, compile, hε₀, hc, hmain⟩ :=
    trappedIonSU4_solovayKitaev_headline_unconditional N hN hN2
  exact ⟨ε₀, c, compile, hε₀, hc, hmain⟩

end SKEFTHawking.FKLW.TrappedIonSU4
