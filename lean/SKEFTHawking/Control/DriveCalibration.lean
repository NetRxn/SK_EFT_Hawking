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

/-- **Transverse duration calibration, ON RESONANCE.** Driving for `T = 2θ/(m·Ω)` achieves exactly
the target angle `θ` **when `ω₀ = ω`**. The two fail conditions are explicit hypotheses, not
absorbed magnitudes.

⚠️ The resonance restriction is not decorative: `rwaRotationAngle` ignores detuning, so off
resonance the achieved angle is strictly larger (`rwaRotationAngle_lt_generalRotationAngle`) and a
duration computed from this identity UNDER-rotates. Use `calibrated_duration_general` off
resonance. -/
theorem calibrated_duration_transverse (Ω b c θ : ℝ)
    (hm : ‖projectedDriveElement b c‖ ≠ 0) (hΩ : Ω ≠ 0) :
    rwaRotationAngle Ω b c (2 * θ / (‖projectedDriveElement b c‖ * Ω)) = θ := by
  rw [rwaRotationAngle_eq_projected]
  field_simp

/-- **Transverse duration calibration at GENERAL detuning** — the physically correct form. The
generator magnitude is `√(Δ² + Ω²m²)/2` (`rwaGenerator_sq`), so the calibrated duration is
`T = 2θ/√(Δ² + Ω²m²)`. Its fail condition is that the generator not vanish. -/
theorem calibrated_duration_general (Δ Ω b c θ : ℝ)
    (hgen : Real.sqrt (Δ ^ 2 + Ω ^ 2 * (b ^ 2 + c ^ 2)) ≠ 0) :
    generalRotationAngle Δ Ω b c (2 * θ / Real.sqrt (Δ ^ 2 + Ω ^ 2 * (b ^ 2 + c ^ 2))) = θ := by
  unfold generalRotationAngle
  field_simp

/-- **Fail condition 1 — a vanishing matrix element.** If the projected drive element is zero, NO
duration produces any rotation: the calibration equation has no solution for a nonzero target.
This is why the duration identity must carry `m ≠ 0` rather than dividing and hoping. -/
theorem rotationAngle_eq_zero_of_zero_element (Ω b c T : ℝ)
    (hm : ‖projectedDriveElement b c‖ = 0) :
    rwaRotationAngle Ω b c T = 0 := by
  rw [rwaRotationAngle_eq_projected, hm]
  ring

/-- **The fail condition's actual claim: the calibration equation has NO SOLUTION.** With a
vanishing matrix element, no duration whatsoever achieves a nonzero target angle. The preceding
`= 0` lemma is the computation; this is the statement that justifies carrying `m ≠ 0` as a
hypothesis rather than dividing and hoping. -/
theorem no_duration_achieves_nonzero_angle_of_zero_element (Ω b c θ : ℝ)
    (hm : ‖projectedDriveElement b c‖ = 0) (hθ : θ ≠ 0) :
    ∀ T, rwaRotationAngle Ω b c T ≠ θ := by
  intro T h
  exact hθ (by rw [← h, rotationAngle_eq_zero_of_zero_element Ω b c T hm])

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

/-- **What the sign inversion actually costs.** A magnitude-only calibration, faced with the
negative duration above, takes `|T|` — and then rotates to `-θ`, i.e. exactly the wrong way. This
is the physical failure the signed treatment prevents, stated as a theorem about the achieved
angle rather than as a fact about the sign of a quotient. -/
theorem magnitude_calibration_rotates_backwards (Ω b c θ : ℝ)
    (hm : 0 < ‖projectedDriveElement b c‖) (hsign : θ * Ω < 0) :
    rwaRotationAngle Ω b c |2 * θ / (‖projectedDriveElement b c‖ * Ω)| = -θ := by
  have hneg := calibrated_duration_neg_of_sign_mismatch Ω b c θ hm hsign
  rw [abs_of_neg hneg, rwaRotationAngle_eq_projected]
  have hΩ : Ω ≠ 0 := by
    intro h; rw [h] at hsign; simp at hsign
  field_simp

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
projected element is `11×` smaller.

The drive is `10·σ_z + σ_x`, deliberately TRACELESS. An earlier version used `10·1 + σ_x`, which
gives the same `11×` ratio but inflates `‖O‖` with the identity — a global phase, which generates
no dynamics at all and (by `rwaGenerator`) contributes nothing to the rotation. That witness was an
artifact. Here the suppression is genuinely due to a longitudinal-dominant drive: the `σ_z`
component is physical, and it is exactly what makes a naive `θ = Ω·T` calibration wrong. -/
theorem transverseElement_strictly_suppressed :
    ‖projectedDriveElement 1 0‖ < ‖driveOp 0 1 0 10‖ := by
  rw [Matrix.linfty_opNorm_def]
  simp [driveOp, projectedDriveElement, σ_x, σ_y, σ_z, Fin.sum_univ_two]

/-! ## 5. Kramers degeneracy

Built from first principles. The repo's `MajoranaKramers` module has NO `Θ`-algebra to reuse:
its `kramers_anticommutation` is `eq_neg_of_add_eq_zero_left` on two REALS, and its
`kramers_pfaffian_definite_sign` is `mul_nonneg` under a self-admitted placeholder hypothesis
(`∀ a : ℝ, a = a`). Both are true theorems whose names and docstrings claim matrix/Pfaffian content
they do not state. Nothing here is cited as reused from them.

An antiunitary `Θ` is characterised by `⟪Θ x, Θ y⟫ = ⟪y, x⟫` (conjugating the inner product) — note
this already forces `Θ` to be isometric, since `‖Θ x‖² = ⟪Θx,Θx⟫ = ⟪x,x⟫ = ‖x‖²`. Time reversal for
half-integer spin additionally satisfies `Θ² = -1`, and THAT is what produces the degeneracy. -/

section Kramers

open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- An antiunitary map sends `0` to `0` (from conjugate-homogeneity at `z = 0`). -/
theorem antiunitary_map_zero {Θ : V → V}
    (hconj : ∀ (z : ℂ) (x : V), Θ (z • x) = (starRingEnd ℂ) z • Θ x) : Θ 0 = 0 := by
  have h := hconj 0 0
  simpa using h

/-- **Kramers orthogonality — the heart of the theorem.** For antiunitary `Θ` with `Θ² = -1`,
every vector is orthogonal to its own image. This is what forbids `Θ v` from being a multiple of
`v`, and hence what makes the degeneracy genuine rather than a relabelling.

Note `Θ` need not be assumed linear or semilinear for this: the two stated properties suffice. -/
theorem kramers_inner_eq_zero {Θ : V → V}
    (hanti : ∀ x y, ⟪Θ x, Θ y⟫_ℂ = ⟪y, x⟫_ℂ)
    (hsq : ∀ x, Θ (Θ x) = -x) (v : V) :
    ⟪Θ v, v⟫_ℂ = 0 := by
  have h := hanti v (Θ v)
  rw [hsq v, inner_neg_right] at h
  -- `h : -⟪Θ v, v⟫ = ⟪Θ v, v⟫`; ℂ has characteristic zero, so the value vanishes.
  linear_combination (-1 / 2 : ℂ) * h

/-- With `Θ² = -1`, `Θ` kills nothing but `0`. -/
theorem kramers_apply_ne_zero {Θ : V → V}
    (hconj : ∀ (z : ℂ) (x : V), Θ (z • x) = (starRingEnd ℂ) z • Θ x)
    (hsq : ∀ x, Θ (Θ x) = -x) {v : V} (hv : v ≠ 0) : Θ v ≠ 0 := by
  intro h
  apply hv
  have hz := hsq v
  rw [h, antiunitary_map_zero hconj] at hz
  exact neg_eq_zero.mp hz.symm

/-- **The Kramers partner is an eigenvector with the SAME eigenvalue.** Conjugate-linearity would
normally send `λ` to `conj λ`; for a real eigenvalue — i.e. the physical case of a self-adjoint
Hamiltonian — the eigenvalue is preserved. -/
theorem kramers_partner_eigenvector {Θ : V → V} {H : V →ₗ[ℂ] V}
    (hconj : ∀ (z : ℂ) (x : V), Θ (z • x) = (starRingEnd ℂ) z • Θ x)
    (hcomm : ∀ x, Θ (H x) = H (Θ x))
    {lam : ℂ} (hreal : (starRingEnd ℂ) lam = lam) {v : V} (hv : H v = lam • v) :
    H (Θ v) = lam • Θ v := by
  rw [← hcomm, hv, hconj, hreal]

/-- **Kramers degeneracy.** For a `Θ`-symmetric Hamiltonian with antiunitary `Θ`, `Θ² = -1`, every
real eigenvalue carries a SECOND eigenvector orthogonal to the first — so no eigenvalue is simple
and every level is (at least) doubly degenerate.

The partner is exhibited (`Θ v`), not merely asserted to exist. -/
theorem kramers_degeneracy {Θ : V → V} {H : V →ₗ[ℂ] V}
    (hanti : ∀ x y, ⟪Θ x, Θ y⟫_ℂ = ⟪y, x⟫_ℂ)
    (hconj : ∀ (z : ℂ) (x : V), Θ (z • x) = (starRingEnd ℂ) z • Θ x)
    (hsq : ∀ x, Θ (Θ x) = -x) (hcomm : ∀ x, Θ (H x) = H (Θ x))
    {lam : ℂ} (hreal : (starRingEnd ℂ) lam = lam) {v : V} (hv0 : v ≠ 0) (hv : H v = lam • v) :
    Θ v ≠ 0 ∧ H (Θ v) = lam • Θ v ∧ ⟪Θ v, v⟫_ℂ = 0 :=
  ⟨kramers_apply_ne_zero hconj hsq hv0,
   kramers_partner_eigenvector hconj hcomm hreal hv,
   kramers_inner_eq_zero hanti hsq v⟩

/-- **Non-vacuity witness.** The hypothesis bundle is inhabited: on `ℂ²` the map
`Θ (z₀, z₁) = (-conj z₁, conj z₀)` — i.e. `-iσ_y ∘ (complex conjugation)`, the standard spin-½
time reversal — is antiunitary with `Θ² = -1`. Without this the degeneracy theorem could be
vacuously true. -/
theorem kramers_hypotheses_inhabited :
    ∃ Θ : EuclideanSpace ℂ (Fin 2) → EuclideanSpace ℂ (Fin 2),
      (∀ x y, ⟪Θ x, Θ y⟫_ℂ = ⟪y, x⟫_ℂ) ∧
      (∀ x, Θ (Θ x) = -x) ∧
      (∀ (z : ℂ) (x : EuclideanSpace ℂ (Fin 2)), Θ (z • x) = (starRingEnd ℂ) z • Θ x) := by
  refine ⟨fun x => WithLp.toLp 2
      ![-(starRingEnd ℂ) (WithLp.ofLp x 1), (starRingEnd ℂ) (WithLp.ofLp x 0)], ?_, ?_, ?_⟩
  · intro x y
    simp [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]
    ring
  · intro x
    ext i
    fin_cases i <;> simp
  · intro z x
    ext i
    fin_cases i <;> simp

end Kramers

end

end SKEFTHawking.Control
