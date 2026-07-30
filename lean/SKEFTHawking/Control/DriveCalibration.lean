/-
Phase 6EE Wave 2: projected-drive calibration algebra.

Calibration is where control claims silently break, and they break in two specific ways that a
magnitude-only treatment cannot express:

  * the drive matrix element can VANISH — then no pulse duration produces any rotation at all; and
  * the element is SIGNED (indeed complex) — assuming the wrong sign rotates the wrong way.

Every identity here therefore carries its fail condition as an EXPLICIT hypothesis rather than
absorbing it into a magnitude. The elements themselves are read off the drive operator as matrix
entries and then *proved* equal to their Pauli-coefficient forms, so the definitions are not
assertions.

Conventions: drive operator and rotation-angle convention are inherited from `Control.RotatingWave`
(`θ` is the exponent parameter; the Bloch-sphere angle is `2θ`).
-/

import Mathlib
import SKEFTHawking.PauliMatrices
import SKEFTHawking.Control.RotatingWave

set_option autoImplicit false

namespace SKEFTHawking.Control

open Matrix Complex

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

noncomputable section

/-! ## 1. The drive elements, read off the operator -/

/-- The transverse (raising) drive element `⟨0|O|1⟩`, read directly off the operator. -/
def transverseElement (O : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := O 0 1

/-- The longitudinal drive element `(⟨0|O|0⟩ - ⟨1|O|1⟩)/2`, read directly off the operator. -/
def longitudinalElement (O : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := (O 0 0 - O 1 1) / 2

/-- The transverse element of a Pauli-basis drive is the SIGNED complex `b - i·c`.
This is a theorem, not a definition: `projectedDriveElement` is pinned to an actual matrix entry. -/
theorem transverseElement_driveOp (a b c d : ℝ) :
    transverseElement (driveOp a b c d) = projectedDriveElement b c := by
  simp [transverseElement, driveOp, projectedDriveElement, σ_x, σ_y, σ_z]
  ring

/-- The longitudinal element of a Pauli-basis drive is `d` — the `σ_z` coefficient alone. -/
theorem longitudinalElement_driveOp (a b c d : ℝ) :
    longitudinalElement (driveOp a b c d) = (d : ℂ) := by
  simp [longitudinalElement, driveOp, σ_x, σ_y, σ_z]

/-! ## 2. Transverse duration calibration, with its fail conditions -/

/-- **Transverse duration calibration.** Driving for `T = 2θ/(m·Ω)` achieves exactly the target
angle `θ`. The two fail conditions are explicit hypotheses, not absorbed magnitudes. -/
theorem calibrated_duration_transverse (Ω b c θ : ℝ)
    (hm : ‖projectedDriveElement b c‖ ≠ 0) (hΩ : Ω ≠ 0) :
    rwaRotationAngle Ω b c (2 * θ / (‖projectedDriveElement b c‖ * Ω)) = θ := by
  rw [rwaRotationAngle_eq_projected]
  field_simp

/-- **Fail condition 1 — a vanishing matrix element.** If the projected drive element is zero, NO
duration produces any rotation: the calibration equation has no solution for a nonzero target.
This is why the duration identity must carry `m ≠ 0` rather than dividing and hoping. -/
theorem rotationAngle_eq_zero_of_zero_element (Ω b c T : ℝ)
    (hm : ‖projectedDriveElement b c‖ = 0) :
    rwaRotationAngle Ω b c T = 0 := by
  rw [rwaRotationAngle_eq_projected, hm]
  ring

/-- **Fail condition 2 — a sign-inverted target.** If the target angle and the drive amplitude
carry opposite signs, the calibrated duration is NEGATIVE, i.e. unphysical. A magnitude-only
calibration silently returns `|T|` here and rotates the wrong way. -/
theorem calibrated_duration_neg_of_sign_mismatch (Ω b c θ : ℝ)
    (hm : 0 < ‖projectedDriveElement b c‖) (hsign : θ * Ω < 0) :
    2 * θ / (‖projectedDriveElement b c‖ * Ω) < 0 := by
  rcases lt_or_gt_of_ne (fun h : Ω = 0 => by simp [h] at hsign) with hΩ | hΩ
  · have hθ : 0 < θ := by nlinarith
    have : ‖projectedDriveElement b c‖ * Ω < 0 := mul_neg_of_pos_of_neg hm hΩ
    exact div_neg_of_pos_of_neg (by linarith) this
  · have hθ : θ < 0 := by nlinarith
    have : 0 < ‖projectedDriveElement b c‖ * Ω := mul_pos hm hΩ
    exact div_neg_of_neg_of_pos (by linarith) this

/-! ## 3. Longitudinal (detuning) duration calibration -/

/-- The longitudinal rotation angle accumulated over `T` at detuning `Δ`, in the same exponent
convention: the `(Δ/2)·σ_z` term of `rwaGenerator` gives `θ_z = (Δ/2)·T`. -/
def longitudinalRotationAngle (Δ T : ℝ) : ℝ := (Δ / 2) * T

/-- **Longitudinal duration calibration** — the dual of the transverse identity, with its own
fail condition (`Δ = 0`: at zero detuning no longitudinal phase accumulates). -/
theorem calibrated_duration_longitudinal (Δ θ : ℝ) (hΔ : Δ ≠ 0) :
    longitudinalRotationAngle Δ (2 * θ / Δ) = θ := by
  unfold longitudinalRotationAngle
  field_simp

/-- **Longitudinal fail condition.** At zero detuning no duration accumulates any phase. -/
theorem longitudinalRotationAngle_eq_zero_of_zero_detuning (T : ℝ) :
    longitudinalRotationAngle 0 T = 0 := by
  unfold longitudinalRotationAngle
  ring

/-! ## 4. Matrix-element suppression -/

/-- **Suppression bound.** The projected drive element never exceeds the operator norm of the
drive. The gap between them is the physics that makes a naive `θ = Ω·T` calibration wrong. -/
theorem transverseElement_norm_le (a b c d : ℝ) :
    ‖projectedDriveElement b c‖ ≤ ‖driveOp a b c d‖ := by
  have hentry : projectedDriveElement b c = driveOp a b c d 0 1 :=
    (transverseElement_driveOp a b c d).symm
  rw [hentry, Matrix.linfty_opNorm_def]
  -- The single entry is at most its row sum, which is at most the sup over rows.
  have hrow : ‖driveOp a b c d 0 1‖₊ ≤ ∑ j : Fin 2, ‖driveOp a b c d 0 j‖₊ :=
    Finset.single_le_sum (f := fun j : Fin 2 => ‖driveOp a b c d 0 j‖₊)
      (fun j _ => by positivity) (Finset.mem_univ (1 : Fin 2))
  have hsup : (∑ j : Fin 2, ‖driveOp a b c d 0 j‖₊)
      ≤ Finset.univ.sup (fun i : Fin 2 => ∑ j : Fin 2, ‖driveOp a b c d i j‖₊) :=
    Finset.le_sup (f := fun i : Fin 2 => ∑ j : Fin 2, ‖driveOp a b c d i j‖₊)
      (Finset.mem_univ (0 : Fin 2))
  exact_mod_cast le_trans hrow hsup

/-- **Strict-suppression witness.** A concrete frame where the drive is large in norm but its
projected element is `11×` smaller — a mostly-identity drive barely couples the two levels. -/
theorem transverseElement_strictly_suppressed :
    ‖projectedDriveElement 1 0‖ < ‖driveOp 10 1 0 0‖ := by
  rw [Matrix.linfty_opNorm_def]
  simp [driveOp, projectedDriveElement, σ_x, σ_y, σ_z, Matrix.one_apply, Fin.sum_univ_two]

end

end SKEFTHawking.Control
