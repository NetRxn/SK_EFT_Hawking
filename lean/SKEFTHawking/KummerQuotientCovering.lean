/-
# Phase 5q.H — K7 residual (a): the covering substrate of the free quotient `qmk : T⁴° ↠ Q`

The covering-map layer for the Q-side `H₂` computation: `qmk : ↥puncturedTorus ↠ FreeQuotient` is a
covering map (the free, properly discontinuous `ℤˣ`-action banked in `KummerFreeQuotient`), with the
deck involution `tauC` and the two-point fibre certificate `fiber_pair` — the exact mirror of
`KummerRP3CoveringMap` one dimension up. Feeds the Smith-sequence transfer
(`KummerQuotientTransferInt`) that solves `H₂(Q;ℤ) ≅ ℤ⁶` for the K7 `b₂ = 22` window.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerFreeQuotient

namespace SKEFTHawking.KummerQuotientCovering

open SKEFTHawking.KummerPuncturedTorus
open SKEFTHawking.KummerFreeQuotient
open SKEFTHawking.KummerInvolution (torusFourInvolution torusFourInvolution_involutive)

noncomputable section

/-! ## §1. Carriers and the deck involution -/

/-- The punctured torus `T⁴°` as a `TopCat` carrier. -/
def PTtop : TopCat := TopCat.of (↥puncturedTorus)

/-- The free quotient `Q = T⁴°/τ` as a `TopCat` carrier. -/
def Qtop : TopCat := TopCat.of FreeQuotient

/-- The deck involution as a plain function on the subtype. -/
noncomputable def tauFun : ↥puncturedTorus → ↥puncturedTorus := fun x => (-1 : ℤˣ) • x

theorem tauFun_continuous : Continuous tauFun := continuous_const_smul _

/-- **The deck involution** `τ : T⁴° → T⁴°` as a bundled continuous map (the `(-1 : ℤˣ)`-action). -/
noncomputable def tauC : C(PTtop, PTtop) :=
  ⟨tauFun, tauFun_continuous⟩

theorem tauFun_apply (x : ↥puncturedTorus) : tauFun x = (-1 : ℤˣ) • x := rfl

@[simp] theorem tauC_apply (x : ↥puncturedTorus) : tauC x = tauFun x := rfl

/-- The deck involution squares to the identity, at the subtype level. -/
theorem tauFun_involutive (x : ↥puncturedTorus) : tauFun (tauFun x) = x := by
  show (-1 : ℤˣ) • ((-1 : ℤˣ) • x) = x
  rw [smul_smul]
  norm_num

/-- `τ² = id` (the deck group is `ℤ/2`). -/
theorem tauC_comp_self : tauC.comp tauC = ContinuousMap.id PTtop :=
  ContinuousMap.ext fun x => tauFun_involutive x

/-- **Freeness**: the deck involution is fixed-point-free on `T⁴°`. -/
theorem tauC_free (x : ↥puncturedTorus) : tauC x ≠ x := neg_one_smul_ne x

theorem qmk_continuous : Continuous qmk := continuous_quotient_mk'

/-- The quotient map `qmk` as a bundled continuous map. -/
noncomputable def qmkC : C(PTtop, Qtop) :=
  ⟨qmk, qmk_continuous⟩

@[simp] theorem qmkC_apply (x : ↥puncturedTorus) : qmkC x = qmk x := rfl

/-- The projection coequalizes the deck involution: `qmk ∘ τ = qmk`. -/
theorem qmkC_comp_tauC : qmkC.comp tauC = qmkC := by
  ext x
  exact qmk_neg_one_smul x

/-! ## §2. The covering-map certificate -/

/-- **The `ℤˣ`-action on `T⁴°` is cancellative/free** (`τ` is fixed-point-free after excision). -/
instance : IsCancelSMul ℤˣ (↥puncturedTorus) where
  left_cancel' u x y h := by
    have h1 : (u⁻¹ * u) • x = (u⁻¹ * u) • y := by
      rw [mul_smul, mul_smul, h]
    simpa using h1
  right_cancel' u v x h := by
    rcases Int.units_eq_one_or u with hu | hu <;> rcases Int.units_eq_one_or v with hv | hv <;>
      subst hu <;> subst hv
    · rfl
    · exfalso
      rw [one_smul] at h
      exact neg_one_smul_ne x h.symm
    · exfalso
      rw [one_smul] at h
      exact neg_one_smul_ne x h
    · rfl

/-- **`qmk : T⁴° ↠ Q` is a covering map** — the quotient by the free, properly discontinuous
`ℤˣ`-action. The lifting input for the integral Smith-sequence transfer of `H_*(Q;ℤ)`. -/
theorem qmk_isCoveringMap : IsCoveringMap qmk :=
  (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul (G := ℤˣ)
    (E := ↥puncturedTorus)).isCoveringMap

/-- **The fibre is the deck pair**: two points of `T⁴°` with the same class in `Q` are equal or
`τ`-related. -/
theorem fiber_pair {e y : ↥puncturedTorus} (h : qmk e = qmk y) : e = y ∨ e = tauC y := by
  rcases (qmk_eq_iff e y).mp h with h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1

end

end SKEFTHawking.KummerQuotientCovering
