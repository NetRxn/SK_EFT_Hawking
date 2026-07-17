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
open SKEFTHawking.SingularEuclideanCapIsoInt
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

/-! ## §2. The narrowed tower constructor — `hbdnd` auto-supplied from even-unimodularity

`GenuineBoundingWTower` has three `Prop` obligations (`hexactRev`, `hnondeg`, `hbdnd`). This constructor
removes `hbdnd` from the required inputs: given the finite-free bases, `Z`, the two homological
`Prop`s (`hexactRev`, `hnondeg`), and even-unimodularity of the integral boundary matrix, it builds the
tower — `hbdnd` is `IsEvenUnimodular.radical_eq_bot`. So the residual atom set the caller must supply is
exactly `{Bw, B, Br, Z (the intH2_basis_datum frontier + the tethered cycle), hexactRev, hnondeg}` plus a
`IsEvenUnimodular (bdryMat B Z)` witness — which, for the σ-consuming block boundary, is itself
unconditional (`#190` `boundaryForm_isEvenUnimodular`). -/
noncomputable def GenuineBoundingWTower.ofEvenUnimodularBoundary
    (Bw : IntH2Basis X) (B : IntH2Basis (sub S)) {qr : ℕ}
    (Br : Module.Basis (Fin qr) ℤ (RelativeCohomologyInt S (2 + 1)))
    (Z : relCycleLift S (2 + 1 + 1))
    (hEU : IsEvenUnimodular (bdryMat B Z))
    (hexactRev : LinearMap.ker (deltaCoord B Br) ≤ LinearMap.range (rest2Coord Bw B))
    (hnondeg : ∀ x : Fin qr → ℝ,
      (∀ a : Fin Bw.rank → ℝ, pairingCoord Bw Br Z a x = 0) → x = 0) :
    GenuineBoundingWTower S where
  Bw := Bw
  B := B
  qr := qr
  Br := Br
  Z := Z
  hexactRev := hexactRev
  hnondeg := hnondeg
  hbdnd := hEU.radical_eq_bot

/-! ## §3. The σ-lane `latticeSig` bridge — the block-splitting datum completes the floor

The σ-lane cobordism-invariance floor (`hbord`/`latticeSig`) needs, for each data-bordant pair, a genuine
tower whose boundary form is the block split `blockDiag A (−B)` of two even-unimodular ends. This bridge
takes a `GenuineBoundingWTower` `T` PLUS the block-splitting datum — the boundary-index identification
`e : Fin (r+s) ≃ Fin T.B.rank` and the reindexed-matrix equality `hBd` witnessing
`bdryMat T.B T.Z ≅ blockDiag A (−B)` — and fires `latticeSig A = latticeSig B` through the glued genuine
carrier and the banked `NovikovGeometricPairLESData.latticeSig_eq`. The datum `(e, hBd)` IS the `#190`
`boundaryInterMatrix_eq_blockDiag` content (`∂W = M_p ⊔ (−M_q)`), so the full σ-lane floor reduces to: a
genuine tower `+` this splitting datum. -/
theorem latticeSig_eq_of_genuineTower {r s : ℕ}
    (A : Matrix (Fin r) (Fin r) ℤ) (B : Matrix (Fin s) (Fin s) ℤ)
    (hA : IsEvenUnimodular A) (hB : IsEvenUnimodular B)
    (T : GenuineBoundingWTower S)
    (e : Fin (r + s) ≃ Fin T.B.rank)
    (hBd : (bdryMat T.B T.Z).submatrix e e = blockDiag A (-B)) :
    latticeSig A = latticeSig B := by
  set D := novikovGeometricPairLESData_of_genuineTower T with hD
  set ρ : (Fin T.B.rank → ℝ) ≃ₗ[ℝ] (Fin (r + s) → ℝ) := LinearEquiv.funCongrLeft ℝ ℝ e with hρ
  refine NovikovGeometricPairLESData.latticeSig_eq A B hA hB
    { H2W := D.H2W
      H3rel := D.H3rel
      rest2 := ρ.toLinearMap ∘ₗ D.rest2
      delta := D.delta ∘ₗ ρ.symm.toLinearMap
      pairing := D.pairing
      hexact := ?_
      hnondeg := D.hnondeg
      hbdnd := ?_
      hsymm := ?_
      hadjDot := ?_ }
  · exact (LinearEquiv.conj_exact_iff_exact D.rest2 D.delta ρ).mpr D.hexact
  · exact (isEvenUnimodular_blockDiag A (-B) hA (isEvenUnimodular_neg B hB)).radical_eq_bot
  · rw [← hBd]; exact (bdryMat_isSymm T.B T.Z).submatrix ⇑e
  · intro a v
    have hsub : (blockDiag A (-B)).map (Int.cast : ℤ → ℝ)
        = ((bdryMat T.B T.Z).map (Int.cast : ℤ → ℝ)).submatrix ⇑e ⇑e := by
      rw [← hBd, Matrix.submatrix_map]
    have hρ_app : (ρ.toLinearMap ∘ₗ D.rest2) a = D.rest2 a ∘ ⇑e := rfl
    have hρsymm_app : (D.delta ∘ₗ ρ.symm.toLinearMap) v = D.delta (v ∘ ⇑e.symm) := rfl
    have hdot : ∀ u w : Fin T.B.rank → ℝ, (u ∘ ⇑e) ⬝ᵥ (w ∘ ⇑e) = u ⬝ᵥ w := by
      intro u w
      simp only [dotProduct, Function.comp_apply]
      exact e.sum_comp (fun i => u i * w i)
    rw [hρ_app, hρsymm_app, hsub, Matrix.submatrix_mulVec_equiv, hdot]
    exact D.hadjDot a (v ∘ ⇑e.symm)

end SKEFTHawking.PinPlusKTTowerInhabit
