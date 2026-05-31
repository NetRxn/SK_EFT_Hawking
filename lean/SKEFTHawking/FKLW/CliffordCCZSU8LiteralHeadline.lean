/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6z.5 closeout — literal Clifford+CCZ (no-`T`) SU(8) Solovay–Kitaev headline

Phase 6z shipped `cliffordCCZLiteral_dense`: the literal `⟨H, S, CNOT, CCZ⟩` (no-`T`)
alphabet is dense in SU(8), with `CCZ` the **essential** non-Clifford resource
(`⟨H, S, CNOT⟩` alone is finite). Wave 6z.5 was scoped to also instantiate the *named*
quantitative Solovay–Kitaev headline `SolovayKitaevHeadline_FreeGroup_SUd` for that exact
alphabet via the generic density→length-bound bridge, but the ship stopped at the density
witness — leaving the headline (the resource-bound compilation guarantee a downstream
consumer would cite) un-instantiated for the literal set. This module closes that gap.

It is the trivial wrap, no new mathematics: a word-length submultiplicativity bundle for
the literal generating set, fed (together with the shipped density) into
`skHeadline_FreeGroup_SUd_from_density_auto`. All substantive content — density itself,
the generic (B) super-quadratic bound, the regime discharge, and the length-exponent
cascade — is discharged upstream in Phase 6y/6z.

This is the CCZ-essential, **`T`-free** counterpart of
`cliffordCCZSU8_solovayKitaev_headline_unconditional` (whose density routes through the
Clifford+`T` sub-alphabet — i.e. `T` does the density work there, `CCZ` only rides along
for membership). Here `CCZ` is load-bearing for universality.

## Substantive content shipped

  * `freeGroup_wordLength_su8_literal` + `freeGroup_wordLength_su8_literal_isFreeGroupLike`
    — word-length submultiplicativity bundle for the literal no-`T` SU(8) generating set
    (mirrors `freeGroup_wordLength_su8` for the universal Clifford+CCZ+`T` set).
  * `cliffordCCZLiteral_solovayKitaev_headline_unconditional` — the UNCONDITIONAL
    bundled-strict quantitative Solovay–Kitaev headline for `⟨H, S, CNOT, CCZ⟩` (no `T`)
    at SU(8): every `U ∈ SU(8)` and `ε ∈ (0, ε₀]` admits a literal-alphabet word
    approximating `U` to error `≤ ε` with FreeGroup word-length
    `≤ c · (log (1/ε)) ^ (log 5 / log (3/2))` (the honest project exponent ≈ 3.97).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected. `#print axioms` on the headline
    is kernel-pure `[propext, Classical.choice, Quot.sound]` — no `native_decide` /
    `Lean.ofReduceBool` on the dependency path (verified 2026-05-29).
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8Density
import SKEFTHawking.FKLW.GenericSUdPerAlphabetHeadlineFromWitness

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

/-- **Word-length function for the literal no-`T` Clifford+CCZ SU(8) generating set**:
since `cliffordCCZLiteralGeneratingSetSU8.W = FreeGroup (Fin 10)` definitionally, this is
just `toWord.length`. Mirrors `freeGroup_wordLength_su8` (universal Clifford+CCZ+`T` set). -/
noncomputable def freeGroup_wordLength_su8_literal :
    (SKEFTHawking.FKLW.CliffordCCZSU8.cliffordCCZLiteralGeneratingSetSU8).W → ℕ :=
  fun w => (w : FreeGroup (Fin 10)).toWord.length

/-- **Submultiplicativity bundle for the literal no-`T` Clifford+CCZ SU(8) wordLength**. -/
theorem freeGroup_wordLength_su8_literal_isFreeGroupLike :
    WordLengthFreeGroupLike
      SKEFTHawking.FKLW.CliffordCCZSU8.cliffordCCZLiteralGeneratingSetSU8
      freeGroup_wordLength_su8_literal where
  mul_le := by
    intro w₁ w₂
    unfold freeGroup_wordLength_su8_literal
    exact FreeGroup.norm_mul_le _ _
  inv_eq := by
    intro w
    unfold freeGroup_wordLength_su8_literal
    exact FreeGroup.norm_inv_eq

/-- **Literal no-`T` Clifford+CCZ SU(8) Solovay–Kitaev headline (UNCONDITIONAL).**

The bundled-strict quantitative Solovay–Kitaev headline for the literal
`⟨H, S, CNOT, CCZ⟩` (no `T`) generating set on SU(8), discharged from the shipped density
(`cliffordCCZLiteral_dense`) ALONE: the (B) super-quadratic bound, regime, the F#4
word-length conjunct, and density-from-witness are all discharged internally by the
generic bridge `skHeadline_FreeGroup_SUd_from_density_auto`. CCZ-essential, `T`-free
counterpart of `cliffordCCZSU8_solovayKitaev_headline_unconditional`. -/
theorem cliffordCCZLiteral_solovayKitaev_headline_unconditional :
    SolovayKitaevHeadline_FreeGroup_SUd
      SKEFTHawking.FKLW.CliffordCCZSU8.cliffordCCZLiteralGeneratingSetSU8 rfl :=
  skHeadline_FreeGroup_SUd_from_density_auto (n := 6)
    SKEFTHawking.FKLW.CliffordCCZSU8.cliffordCCZLiteralGeneratingSetSU8 rfl
    SKEFTHawking.FKLW.CliffordCCZSU8.cliffordCCZLiteral_dense
    freeGroup_wordLength_su8_literal_isFreeGroupLike

end SKEFTHawking.FKLW.GenericSUd
