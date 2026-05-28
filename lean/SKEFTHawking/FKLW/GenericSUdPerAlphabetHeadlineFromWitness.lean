/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Tracks T-A1′.5 / T-A2′.5 — per-alphabet headline reduced to the (D) witness ALONE

Composes the 2026-05-28 ships:
  * `skHeadline_FreeGroup_SUd_from_density` (headline from (D) density + word-length bundle,
    with (B), regime, and F#4 length all discharged internally), and
  * `densityFromWitness` (UNCONDITIONAL `IsDenseInSUd_gs` from a `ClosureDenseWitness`, since the
    Cartan step S.2g is unconditionally discharged),

to reduce each per-alphabet UNCONDITIONAL SK headline to **exactly one** remaining substantive
input: a `ClosureDenseWitness` for the per-alphabet generating set. The word-length bundle is the
existing per-alphabet `freeGroup_wordLength_su{4,8}_isFreeGroupLike`; the length constant is chosen
internally.

After this, the *only* thing standing between the project and the named UNCONDITIONAL headlines
`solovayKitaev_dawson_nielsen_quantitative_su{4,8}_..._tight` is the unconditional discharge of the
per-alphabet `ClosureDenseWitness` (Brylinski-Brylinski 2002 SU(4) entangler universality /
Clifford+T-at-SU(8) universality, Boykin et al 1999 — the SU(8) witness is the universal
Clifford+CCZ+T alphabet with density from its Clifford+T sub-alphabet; A-G 2004 is stabilizer
simulability, NOT a universality cite) — currently carried as the tracked Props
`trappedIonSU4_v4_witness_tracked` / `cliffordCCZSU8_v4_witness_tracked`.

## Substantive content shipped

  * `skHeadline_FreeGroup_SUd_from_density_auto` — generic: headline from (D) density + word-length
    bundle, choosing the length constant internally.
  * `trappedIonSU4_headline_of_witness` — SU(4) headline from a `ClosureDenseWitness` ALONE.
  * `cliffordCCZSU8_headline_of_witness` — SU(8) headline from a `ClosureDenseWitness` ALONE.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Wave 1" remaining item (b) plumbing: reduce per-alphabet headlines to the (D)
density witness alone. 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdConcreteLengthPolylog
import SKEFTHawking.FKLW.GenericSUdDischargeUnconditional
import SKEFTHawking.FKLW.GenericSUdLengthBoundPerAlphabet

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **Headline from (D) density + word-length bundle**, choosing the length constant internally
(`c := 5·N₀ + 1`, `N₀` = the constructive cover's max word length). A thin auto-`c` wrapper over
`skHeadline_FreeGroup_SUd_from_density`. -/
theorem skHeadline_FreeGroup_SUd_from_density_auto
    {n : ℕ} {α : Type} [DecidableEq α] [Nonempty (Fin (n + 2))]
    (gs : GeneratingSet (n + 2)) (h_eq : gs.W = FreeGroup α)
    (h_dense : IsDenseInSUd_gs gs)
    (h_wl : WordLengthFreeGroupLike gs (fun w => (h_eq ▸ w : FreeGroup α).toWord.length)) :
    SolovayKitaevHeadline_FreeGroup_SUd gs h_eq :=
  skHeadline_FreeGroup_SUd_from_density gs h_eq h_dense h_wl
    (5 * ((maxWordLengthInCover_sud (fun w => (h_eq ▸ w : FreeGroup α).toWord.length)
        (constructiveEpsilonCover_SUd gs h_dense (ε₀_sud (n + 2))
          (ε₀_sud_pos (by omega))) : ℕ) : ℝ) + 1)
    (by positivity)
    (le_add_of_nonneg_right (by norm_num))

/-- **SU(4) trapped-ion headline from a `ClosureDenseWitness` ALONE.**

The full UNCONDITIONAL bundled-strict SK headline `SolovayKitaevHeadline_FreeGroup_SUd` for the
trapped-ion SU(4) generating set follows from a single input — a closure-density witness for the
alphabet. (B) super-quad bound, regime, F#4 word-length conjunct, and density-from-witness are all
discharged internally. The remaining substantive ingredient is the witness itself
(Brylinski-Brylinski 2002 entangler universality). -/
theorem trappedIonSU4_headline_of_witness (N : ℕ) (hN : 0 < N)
    (w : ClosureDenseWitness (SKEFTHawking.FKLW.TrappedIonSU4.trappedIonGeneratingSetSU4 N hN)) :
    SolovayKitaevHeadline_FreeGroup_SUd
      (SKEFTHawking.FKLW.TrappedIonSU4.trappedIonGeneratingSetSU4 N hN) rfl :=
  skHeadline_FreeGroup_SUd_from_density_auto (n := 2)
    (SKEFTHawking.FKLW.TrappedIonSU4.trappedIonGeneratingSetSU4 N hN) rfl
    (densityFromWitness (by norm_num) w)
    (freeGroup_wordLength_su4_isFreeGroupLike N hN)

/-- **SU(8) Clifford+CCZ headline from a `ClosureDenseWitness` ALONE.**

As `trappedIonSU4_headline_of_witness`, at SU(8): the UNCONDITIONAL headline follows from a single
closure-density witness for the universal Clifford+CCZ+T alphabet (density from its Clifford+T
sub-alphabet — Clifford+T universality is BMPRV 1999; CCZ universality is Shi 2002 / Aharonov 2003,
with the Brylinski-Brylinski 2001 entangling-gate criterion; the shipped witness uses Clifford+T —
A-G 2004 is simulability, not universality). -/
theorem cliffordCCZSU8_headline_of_witness
    (w : ClosureDenseWitness SKEFTHawking.FKLW.CliffordCCZSU8.cliffordCCZGeneratingSetSU8) :
    SolovayKitaevHeadline_FreeGroup_SUd
      SKEFTHawking.FKLW.CliffordCCZSU8.cliffordCCZGeneratingSetSU8 rfl :=
  skHeadline_FreeGroup_SUd_from_density_auto (n := 6)
    SKEFTHawking.FKLW.CliffordCCZSU8.cliffordCCZGeneratingSetSU8 rfl
    (densityFromWitness (by norm_num) w)
    freeGroup_wordLength_su8_isFreeGroupLike

end SKEFTHawking.FKLW.GenericSUd
