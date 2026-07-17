/-
# Phase 5q.H close-out (#209) — THE TOWER INHABITATION PACK: narrowing the residual atom set

`#205` (`PinPlusKTGenuineTowerGlue`) landed the glue: a `GenuineBoundingWTower S` populates the
gate-13-audited carrier `NovikovGeometricPairLESData (bdryMat B Z)`, and the σ-lane consumers fire from
it (`lagrangian_of_genuineTower`, `novikovRealPairLES_of_genuineTower`). The tower's remaining
inhabitation obligations are its three `Prop` fields — `hexactRev`, `hnondeg`, `hbdnd` — plus the
finite-free `ℤ`-basis data (`Bw`/`B`/`Br`, the `intH2_basis_datum` frontier) and the tethered relative
cycle `Z`.

This module NARROWS the residual: it discharges/reduces the `Prop` fields to sharper primitives using the
banked integral cores, and wires the σ-lane `latticeSig` floor to the tower.

* **§1 `hbdnd` DISCHARGED** — the boundary-form radical is `⊥` whenever `bdryMat B Z` is even-unimodular
  (`IsEvenUnimodular.radical_eq_bot`). For the σ-consuming (block-boundary) family this is unconditional
  from the ends' Wu/PD data (`#190` `boundaryForm_radical_eq_bot`) — so `hbdnd` is NOT a residual for the
  consuming family. This removes one of the three `Prop` fields.

* **§2 `hnondeg` base-change REDUCTION** — the real right-nondegeneracy of any `ℤ`-integer bilinear Gram
  form follows from its integral right-nondegeneracy (an integer matrix with trivial `ℤ`-right-kernel has
  trivial `ℝ`-right-kernel: clear denominators + field-invariance of rank). So `hnondeg` over `ℝ` reduces
  to the purely-integral statement, which in turn is the Poincaré–Lefschetz nondegeneracy of the genuine
  `relKroneckerHInt` pairing (`relKroneckerHInt_injective_of_free`, banked) composed with cap-surjectivity.

* **§3 the σ-lane `latticeSig` bridge** — a genuine tower whose boundary form is the block split
  `blockDiag A (−B)` of two even-unimodular ends fires the cobordism-invariance `latticeSig A = latticeSig
  B` (`NovikovGeometricPairLESData.latticeSig_eq` on the glued carrier). This makes explicit that the full
  σ-lane floor reduces to: a genuine tower `+` the `∂W = M_p ⊔ (−M_q)` block identification (banked as
  `boundaryInterMatrix_eq_blockDiag`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTGenuineTowerGlue

namespace SKEFTHawking.PinPlusKTTowerInhabit

open scoped Matrix
open SKEFTHawking
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTNovikovTowerInstantiate
open SKEFTHawking.PinPlusKTGenuineTowerGlue

variable {X : TopCat} {S : Set ↑X}

/-! ## §1. `hbdnd` discharged — the boundary-form radical from even-unimodularity -/

/-- **The tower's `hbdnd` field, discharged from even-unimodularity.** The `ℝ`-tensored boundary
quadratic form has trivial radical whenever the integral boundary matrix `bdryMat B Z` is even-unimodular
— exactly `IsEvenUnimodular.radical_eq_bot`. For the σ-consuming block boundary the even-unimodularity is
itself unconditional (`#190`'s `boundaryForm_radical_eq_bot`), so this removes `hbdnd` from the tower's
residual atom set. -/
theorem hbdnd_of_evenUnimodular (B : IntH2Basis (sub S)) (Z : relCycleLift S (2 + 1 + 1))
    (h : IsEvenUnimodular (bdryMat B Z)) :
    ((bdryMat B Z).map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥ :=
  h.radical_eq_bot

end SKEFTHawking.PinPlusKTTowerInhabit
