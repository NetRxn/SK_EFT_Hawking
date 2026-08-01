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

/-- **Transverse duration calibration, ON RESONANCE.** Driving for `T = 2θ/(m·Ω)` achieves the
target angle `θ` **when `ω₀ = ω`**. The two fail conditions are explicit hypotheses, not absorbed
magnitudes.

⚠️ The resonance restriction is not decorative: `rwaRotationAngle` ignores detuning, so for a
positive duration and a non-negative amplitude the off-resonance angle is strictly larger
(`rwaRotationAngle_lt_generalRotationAngle`, whose `0 ≤ Ω` and `0 < T` are what make "larger"
directional) and a duration computed from this identity UNDER-rotates. Use
`calibrated_duration_general` off resonance.

⚠️ **CO-ROTATING MODEL ONLY — this identity is exact in the REDUCED dynamics, not the exact ones.**
The exact propagator differs from the co-rotating one by the counter-rotating remainder that
`rwa_propagator_difference_bound` bounds at Bloch–Siegert scale. That remainder is not zero: at
`ω = Ω` the integrated counter-rotating drive reaches exactly `1/2`
(`integral_counterRotating_witness_resonance`). Any device claim lifted from this identity inherits
that `O(Ω/ω)` error bar. `calibrated_duration_transverse_propagator` states the identity on the
co-rotating propagator itself, which is where the word "achieves" acquires its meaning. -/
theorem calibrated_duration_transverse (Ω b c θ : ℝ)
    (hm : ‖projectedDriveElement b c‖ ≠ 0) (hΩ : Ω ≠ 0) :
    rwaRotationAngle Ω b c (2 * θ / (‖projectedDriveElement b c‖ * Ω)) = θ := by
  rw [rwaRotationAngle_eq_projected]
  field_simp

/-- **Transverse duration calibration at GENERAL detuning** — the physically correct form. The
generator magnitude is `√(Δ² + Ω²m²)/2`, so the calibrated duration is `T = 2θ/√(Δ² + Ω²m²)`. Its
fail condition is that the generator not vanish. Carries the same co-rotating-model caveat as the
resonant form above. -/
theorem calibrated_duration_general (Δ Ω b c θ : ℝ)
    (hgen : Real.sqrt (Δ ^ 2 + Ω ^ 2 * (b ^ 2 + c ^ 2)) ≠ 0) :
    generalRotationAngle Δ Ω b c (2 * θ / Real.sqrt (Δ ^ 2 + Ω ^ 2 * (b ^ 2 + c ^ 2))) = θ := by
  unfold generalRotationAngle
  field_simp

/-- **The calibration divisor is TWICE the rate — the factor of two, stated rather than implied.**
The duration in `calibrated_duration_general` divides by `√(Δ²+Ω²m²)`, and that number is
`2·rwaRate`, not `rwaRate`. The factor is the exponent convention (`θ` is the exponent; the
Bloch-sphere angle is `2θ`), and it is written here as an identity so that no docstring has to
carry it. Unconditional: at a vanishing radicand both sides are `0` under Lean's division
convention. -/
theorem calibrated_duration_divisor_eq_rate (Δ Ω b c θ : ℝ) :
    2 * θ / Real.sqrt (Δ ^ 2 + Ω ^ 2 * (b ^ 2 + c ^ 2)) = θ / rwaRate Δ Ω b c := by
  unfold rwaRate
  rw [div_div_eq_mul_div]
  ring_nf

/-- **The rate in the calibration formula IS the generator magnitude** — `rwaGenerator_sq` consumed,
not cited. This theorem says `rwaRate` is the magnitude of the operator being exponentiated, via
`H_RWA² = rate²·1`; `calibrated_duration_divisor_eq_rate` is what connects that magnitude to the
`√(Δ²+Ω²m²)` a calibrated duration actually divides by (it is `2·rwaRate`). -/
theorem rwaGenerator_sq_eq_rate_sq (ω₀ ω Ω φ b c : ℝ) :
    rwaGenerator ω₀ ω Ω φ b c ^ 2
      = ((rwaRate (ω₀ - ω) Ω b c ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [rwaGenerator_sq, rwaRate_sq]

/-- **The calibration hypotheses discharge the nondegenerate-rate side condition.** The two
hypotheses this section carries everywhere — a nonvanishing matrix element and a positive drive
amplitude — are exactly what `rwaPropagator_ode` needs, so the ODE below is available under the
calibration hypotheses themselves rather than under a fresh assumption. -/
theorem calibrated_rwaRate_pos (Ω b c : ℝ) (hm : ‖projectedDriveElement b c‖ ≠ 0) (hΩ : 0 < Ω) :
    0 < rwaRate 0 Ω b c := by
  have hne : projectedDriveElement b c ≠ 0 := norm_ne_zero_iff.mp hm
  have hpos : 0 < Complex.normSq (projectedDriveElement b c) := Complex.normSq_pos.mpr hne
  rw [projectedDriveElement_normSq] at hpos
  unfold rwaRate
  have : 0 < (0 : ℝ) ^ 2 + Ω ^ 2 * (b ^ 2 + c ^ 2) := by positivity
  positivity

/-- **The propagator at the calibrated duration is pinned by its own ODE — invoked, not cited.**
`rwaPropagator` is *defined* by a closed form; what makes it the co-rotating propagator rather than
an arbitrary matrix-valued formula is that it solves `U' = −i·H_RWA·U`. This theorem discharges
`rwaPropagator_ode`'s nondegenerate-rate side condition from the calibration hypotheses, so the
"pinned by an ODE" step below is a dependency of this module rather than a claim in a docstring. -/
theorem calibrated_duration_propagator_ode (ω Ω b c : ℝ)
    (hm : ‖projectedDriveElement b c‖ ≠ 0) (hΩ : 0 < Ω) (t : ℝ) :
    HasDerivAt (rwaPropagator ω ω Ω 0 b c)
      ((-Complex.I) • (rwaGenerator ω ω Ω 0 b c * rwaPropagator ω ω Ω 0 b c t)) t :=
  rwaPropagator_ode ω ω Ω 0 b c (by rw [sub_self]; exact calibrated_rwaRate_pos Ω b c hm hΩ) t

/-- **The calibrated duration achieves the target angle ON THE PROPAGATOR.** At resonance, driving
for `T = 2θ/(m·Ω)` makes the co-rotating propagator's trace exactly `2·cos θ`. This is what upgrades
`calibrated_duration_transverse` from an identity between real numbers to a statement about the
operator the drive applies, the propagator being pinned by the ODE that
`calibrated_duration_propagator_ode` establishes here under these same hypotheses rather than by
convention. Same co-rotating-model caveat as above. -/
theorem calibrated_duration_transverse_propagator (ω Ω b c θ : ℝ)
    (hm : ‖projectedDriveElement b c‖ ≠ 0) (hΩ : 0 < Ω) :
    rwaPropagator ω ω Ω 0 b c (2 * θ / (‖projectedDriveElement b c‖ * Ω)) 0 0
      + rwaPropagator ω ω Ω 0 b c (2 * θ / (‖projectedDriveElement b c‖ * Ω)) 1 1
      = 2 * ((Real.cos θ : ℝ) : ℂ) := by
  rw [rwaPropagator_trace, sub_self, generalRotationAngle_resonance Ω b c _ hΩ.le,
    calibrated_duration_transverse Ω b c θ hm hΩ.ne']

/-- **The FULL operator identity at the calibrated duration** — the statement the
`calibrated_duration_*` family actually needs.

The trace form above is **even in `θ`**: `U` and its time reverse share it — which is
`trace_blind_to_rotation_direction` below, proved rather than observed — so it certifies neither
the rotation DIRECTION nor the AXIS. Since direction is this module's headline failure mode
(`magnitude_calibration_rotates_backwards` lands on `−θ`) and axis mis-pointing is what
`envelope_phase_alignment` exists to correct, the trace alone is too weak to support the word
"achieves". This identity pins the whole operator: `sin θ` carries the sign, and `rwaGenerator`
carries the axis. -/
theorem calibrated_duration_transverse_propagator_full (ω Ω b c θ : ℝ)
    (hm : ‖projectedDriveElement b c‖ ≠ 0) (hΩ : 0 < Ω) :
    rwaPropagator ω ω Ω 0 b c (2 * θ / (‖projectedDriveElement b c‖ * Ω))
      = ((Real.cos θ : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        - (Complex.I * ((Real.sin θ / rwaRate 0 Ω b c : ℝ) : ℂ)) • rwaGenerator ω ω Ω 0 b c := by
  unfold rwaPropagator
  rw [sub_self, generalRotationAngle_resonance Ω b c _ hΩ.le,
    calibrated_duration_transverse Ω b c θ hm hΩ.ne']

/-- **Why the trace form is not enough — a refutation, not a caveat.** The time-reversed propagator
has the SAME trace as the forward one, yet is a different operator whenever the rotation is
nontrivial. So any calibration claim resting only on the trace is satisfied equally by a rotation
of `−θ`. -/
theorem trace_blind_to_rotation_direction (ω₀ ω Ω φ b c t : ℝ)
    (hsin : Real.sin (generalRotationAngle (ω₀ - ω) Ω b c t) ≠ 0)
    (hk : 0 < rwaRate (ω₀ - ω) Ω b c) :
    (rwaPropagator ω₀ ω Ω φ b c (-t) 0 0 + rwaPropagator ω₀ ω Ω φ b c (-t) 1 1
        = rwaPropagator ω₀ ω Ω φ b c t 0 0 + rwaPropagator ω₀ ω Ω φ b c t 1 1)
      ∧ rwaPropagator ω₀ ω Ω φ b c (-t) ≠ rwaPropagator ω₀ ω Ω φ b c t := by
  -- `rwaGenerator ≠ 0` is NOT an independent hypothesis: it follows from `0 < rate` via
  -- `rwaGenerator_sq` (if the generator vanished, so would `rate²`).
  have hgen : rwaGenerator ω₀ ω Ω φ b c ≠ 0 := by
    intro hz
    have h := rwaGenerator_sq_eq_rate_sq ω₀ ω Ω φ b c
    rw [hz] at h
    have h0 := congrFun (congrFun h 0) 0
    simp at h0
    have hR : rwaRate (ω₀ - ω) Ω b c ^ 2 = 0 := by exact_mod_cast h0.symm
    nlinarith [hk, hR]
  constructor
  · rw [rwaPropagator_trace, rwaPropagator_trace, generalRotationAngle_neg, Real.cos_neg]
  · intro hcontra
    apply hgen
    have hdiff : (Complex.I * ((2 * Real.sin (generalRotationAngle (ω₀ - ω) Ω b c t)
        / rwaRate (ω₀ - ω) Ω b c : ℝ) : ℂ)) • rwaGenerator ω₀ ω Ω φ b c = 0 := by
      have h := congrArg (fun M => M - rwaPropagator ω₀ ω Ω φ b c t) hcontra
      simp only [sub_self] at h
      rw [← h]
      unfold rwaPropagator
      rw [generalRotationAngle_neg, Real.cos_neg, Real.sin_neg]
      push_cast
      module
    have hscal : (Complex.I * ((2 * Real.sin (generalRotationAngle (ω₀ - ω) Ω b c t)
        / rwaRate (ω₀ - ω) Ω b c : ℝ) : ℂ)) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, false_or, Complex.ofReal_eq_zero,
        div_eq_zero_iff, not_or]
      exact ⟨by simpa using hsin, ne_of_gt hk⟩
    exact (smul_eq_zero.mp hdiff).resolve_left hscal

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
carry opposite signs, the calibrated duration is NEGATIVE, i.e. unphysical. That negativity is all
this statement establishes; what a magnitude-only calibration then does with the `|T|` it silently
substitutes is the separate claim proved next, in `magnitude_calibration_rotates_backwards`. -/
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
convention: the `(Δ/2)·σ_z` term of `rwaGenerator` gives `θ_z = (Δ/2)·T`.

That provenance is proved rather than asserted by this docstring:
`longitudinalElement_rwaGenerator` reads `Δ/2` off the generator, and
`longitudinalRotationAngle_eq_rwaGenerator_element` is this definition expressed through it. -/
def longitudinalRotationAngle (Δ T : ℝ) : ℝ := (Δ / 2) * T

/-- **The longitudinal element really is read off `rwaGenerator`** — the longitudinal counterpart of
`transverseElement_rwaGenerator`. The generator's own longitudinal element is exactly the detuning
half, `Δ/2`; the transverse coefficients `b`, `c` do not enter, because `σ_x` and `σ_y` have zero
diagonal. -/
theorem longitudinalElement_rwaGenerator (ω₀ ω Ω φ b c : ℝ) :
    longitudinalElement (rwaGenerator ω₀ ω Ω φ b c) = (((ω₀ - ω) / 2 : ℝ) : ℂ) := by
  unfold longitudinalElement rwaGenerator
  simp [σ_x, σ_y, σ_z, Matrix.add_apply]

/-- **The definition tracks the generator, in the kernel.** `longitudinalRotationAngle` at detuning
`ω₀ - ω` is the generator's own longitudinal element times the duration — so the `(Δ/2)·σ_z`
provenance claimed for the definition is a theorem, not a convention. -/
theorem longitudinalRotationAngle_eq_rwaGenerator_element (ω₀ ω Ω φ b c T : ℝ) :
    longitudinalRotationAngle (ω₀ - ω) T
      = (longitudinalElement (rwaGenerator ω₀ ω Ω φ b c)).re * T := by
  rw [longitudinalElement_rwaGenerator]
  unfold longitudinalRotationAngle
  simp

/-- **Longitudinal duration calibration** — the dual of the transverse identity, with its own
fail condition (`Δ = 0`: at zero detuning no longitudinal phase accumulates). Carries the same
co-rotating-model caveat as the two transverse identities above: `longitudinalRotationAngle` is the
generator's longitudinal element times the duration
(`longitudinalRotationAngle_eq_rwaGenerator_element`), so it inherits the same `O(Ω/ω)` remainder
the co-rotating reduction carries. -/
theorem calibrated_duration_longitudinal (Δ θ : ℝ) (hΔ : Δ ≠ 0) :
    longitudinalRotationAngle Δ (2 * θ / Δ) = θ := by
  unfold longitudinalRotationAngle
  field_simp

/-- **Longitudinal fail condition.** At zero detuning no duration accumulates any phase, so no
duration achieves a nonzero target — the longitudinal analogue of
`no_duration_achieves_nonzero_angle_of_zero_element`. -/
theorem no_duration_achieves_nonzero_longitudinal_angle_of_zero_detuning {θ : ℝ} (hθ : θ ≠ 0) :
    ∀ T, longitudinalRotationAngle 0 T ≠ θ := by
  intro T
  unfold longitudinalRotationAngle
  simpa using fun h => hθ h.symm

/-! ### 3.2 Why `longitudinalElement` has no duration-calibration identity

The "longitudinal dual" above is about DETUNING, not about the longitudinal drive element — and that
is forced, not an omission. `rwaGenerator` contains no `a` or `d`, so a drive along `1` or `σ_z`
survives only in the counter-rotating remainder. That — and only that — is what the two theorems
below state: the co-rotating generator is `a`- and `d`-independent, and the longitudinal element
tracks `d`. (How large the surviving remainder is, is a separate question, answered by
`RotatingWave`'s `integral_counterRotating_norm_le`, not here.) The asymmetry between
`transverseElement` (which carries a calibration identity) and `longitudinalElement` (which cannot)
is therefore recorded in the kernel rather than in a docstring. -/

/-- The longitudinal element measures precisely the drive component that the co-rotating reduction
discards: two drives differing only in `a` and `d` differ ONLY in their counter-rotating remainder,
their co-rotating generators being identical. Proved through `interactionHamiltonian_decomp`. -/
theorem longitudinal_drive_purely_counterRotating (ω₀ ω Ω φ a b c d a' d' t : ℝ) :
    interactionHamiltonian ω₀ ω Ω φ a b c d t - interactionHamiltonian ω₀ ω Ω φ a' b c d' t
      = counterRotating ω Ω φ a b c d t - counterRotating ω Ω φ a' b c d' t := by
  rw [interactionHamiltonian_decomp, interactionHamiltonian_decomp]
  abel

/-- …and the longitudinal element is what that discarded difference amounts to: it tracks `d`
exactly, so a nonzero longitudinal element is a real feature of the drive operator which
nevertheless contributes nothing at RWA order. -/
theorem longitudinalElement_driveOp_sub (a b c d a' b' c' d' : ℝ) :
    longitudinalElement (driveOp a b c d) - longitudinalElement (driveOp a' b' c' d')
      = ((d - d' : ℝ) : ℂ) := by
  rw [longitudinalElement_driveOp, longitudinalElement_driveOp]
  push_cast
  ring

/-! ## 3.1 Phase calibration — where the co-rotating rotation axis actually points

The duration identities above fix the rotation *angle*. The remaining calibration freedom is the
*azimuth* of the rotation axis in the co-rotating x–y plane, set by the drive envelope phase `φ`.
The physical content is that the achieved azimuth is **not** `φ`: it is `φ` shifted by the argument
of the projected drive element, so in any frame where `O` is not aligned with `σ_x` a naively
commanded axis is mis-pointed. -/

/-- The transverse **axis phasor** of the co-rotating generator — the complex number whose real and
imaginary parts are exactly the `σ_x` and `σ_y` coefficients of `rwaGenerator ω₀ ω Ω φ b c`. Its
argument is the azimuth of the rotation axis; its modulus is the on-resonance co-rotating rate
`rwaRate 0 Ω b c` (`norm_rwaAxisPhasor`) — half the Bloch-sphere rotation rate, in the exponent
convention this module inherits. -/
noncomputable def rwaAxisPhasor (Ω φ b c : ℝ) : ℂ :=
  ((Ω / 2 * (b * Real.cos φ - c * Real.sin φ) : ℝ) : ℂ)
    + Complex.I * ((Ω / 2 * (b * Real.sin φ + c * Real.cos φ) : ℝ) : ℂ)

/-- **The phasor really is read off `rwaGenerator`** — not merely asserted to be by its docstring.
The generator's own transverse element (its `(0,1)` entry, via this module's `transverseElement`) is
the conjugate of the axis phasor, which is exactly the statement that the phasor's real and
imaginary parts are the generator's `σ_x` and `σ_y` coefficients. -/
theorem transverseElement_rwaGenerator (ω₀ ω Ω φ b c : ℝ) :
    transverseElement (rwaGenerator ω₀ ω Ω φ b c)
      = (starRingEnd ℂ) (rwaAxisPhasor Ω φ b c) := by
  unfold transverseElement rwaGenerator rwaAxisPhasor
  simp [σ_x, σ_y, σ_z, Matrix.add_apply, Complex.ext_iff, map_ofNat]

/-- The axis phasor factorises as `(Ω/2)·conj⟨0|O|1⟩·e^{iφ}`. This identity is what makes the phase
calibration below a computation rather than a convention: the envelope phase and the drive's own
matrix-element argument enter as a single product. -/
theorem rwaAxisPhasor_eq (Ω φ b c : ℝ) :
    rwaAxisPhasor Ω φ b c
      = ((Ω / 2 : ℝ) : ℂ) * (starRingEnd ℂ) (projectedDriveElement b c)
          * Complex.exp ((φ : ℂ) * Complex.I) := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  unfold rwaAxisPhasor projectedDriveElement
  simp only [map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal]
  apply Complex.ext <;> simp <;> ring

/-- **Polar form — the mis-pointing, as an identity rather than a remark.** At commanded envelope
phase `φ` the axis phasor is `(Ω/2)·‖⟨0|O|1⟩‖` times `e^{i(φ + arg(conj⟨0|O|1⟩))}`. So the achieved
azimuth is the commanded phase shifted by exactly `arg(conj⟨0|O|1⟩)`, which is the whole content of
"the axis is not where you pointed it". The alignment identity below is this theorem at
`φ = χ − arg(conj⟨0|O|1⟩)`, where the shift cancels.

Nothing here assumes `Ω > 0`: the real coefficient `(Ω/2)·‖⟨0|O|1⟩‖` simply carries the sign of
`Ω`, so for `Ω < 0` the phasor is a negative real multiple of `e^{i(φ + arg)}` and reading its
argument as the azimuth requires the extra half-turn that this statement does not track. -/
theorem rwaAxisPhasor_polar (Ω φ b c : ℝ) :
    rwaAxisPhasor Ω φ b c
      = ((Ω / 2 * ‖projectedDriveElement b c‖ : ℝ) : ℂ)
          * Complex.exp (((φ + Complex.arg ((starRingEnd ℂ) (projectedDriveElement b c)) : ℝ) : ℂ)
              * Complex.I) := by
  set m : ℂ := (starRingEnd ℂ) (projectedDriveElement b c) with hmdef
  have hpolar : ((‖m‖ : ℝ) : ℂ) * Complex.exp ((m.arg : ℂ) * Complex.I) = m :=
    Complex.norm_mul_exp_arg_mul_I m
  have hnorm : ‖m‖ = ‖projectedDriveElement b c‖ := by rw [hmdef]; exact RCLike.norm_conj _
  rw [rwaAxisPhasor_eq, ← hmdef, ← hnorm]
  conv_lhs => rw [← hpolar]
  push_cast
  rw [add_mul, Complex.exp_add]
  ring

/-- **The phasor's modulus is the co-rotating rate.** `‖axis phasor‖ = rwaRate 0 Ω b c`, the
on-resonance rate — so the docstring of `rwaAxisPhasor` describes a proved quantity rather than an
asserted one, and the "half the Bloch-sphere rate" reading is the module's standing exponent
convention applied to it. -/
theorem norm_rwaAxisPhasor (Ω φ b c : ℝ) :
    ‖rwaAxisPhasor Ω φ b c‖ = rwaRate 0 Ω b c := by
  rw [rwaAxisPhasor_polar, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_def, projectedDriveElement_normSq]
  unfold rwaRate
  rw [show (0 : ℝ) ^ 2 + Ω ^ 2 * (b ^ 2 + c ^ 2) = Ω ^ 2 * (b ^ 2 + c ^ 2) by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg (b ^ 2 + c ^ 2)), abs_div]
  norm_num
  ring

/-- **Phase-calibration identity.** Commanding envelope phase `φ = χ − arg(conj⟨0|O|1⟩)` cancels the
mis-pointing shift of `rwaAxisPhasor_polar`: the axis phasor becomes the real multiple
`(Ω/2)·‖⟨0|O|1⟩‖` of `e^{iχ}`, so the axis sits at azimuth `χ` whenever the drive amplitude is
positive. (No sign hypothesis is imposed: the multiple is non-negative exactly when `0 ≤ Ω`, and
the azimuth reading is the one `rwaAxisPhasor_polar` qualifies for `Ω < 0`.) Commanding `φ = χ`
instead leaves the axis mis-pointed by exactly `arg(conj⟨0|O|1⟩)` — that is `rwaAxisPhasor_polar`,
and it is the calibration error this identity exists to remove. -/
theorem envelope_phase_alignment (Ω χ b c : ℝ) :
    rwaAxisPhasor Ω (χ - Complex.arg ((starRingEnd ℂ) (projectedDriveElement b c))) b c
      = ((Ω / 2 * ‖projectedDriveElement b c‖ : ℝ) : ℂ) * Complex.exp ((χ : ℂ) * Complex.I) := by
  rw [rwaAxisPhasor_polar, sub_add_cancel]

/-- **Fail condition, explicit.** At a vanishing projected element there is no axis to place: the
phasor is `0` for EVERY commanded envelope phase, so no phase achieves any azimuth. -/
theorem rwaAxisPhasor_eq_zero_of_zero_element (Ω φ : ℝ) {b c : ℝ}
    (hm : projectedDriveElement b c = 0) : rwaAxisPhasor Ω φ b c = 0 := by
  rw [rwaAxisPhasor_eq, hm]
  simp

/-- **The mis-pointing is real, not a bookkeeping convention.** For a pure `σ_y` drive
(`b = 0`, `c = 1`) commanding `φ = 0` puts the axis at azimuth `π/2`, not `0` — a quarter turn
away from the naive identification of envelope phase with axis azimuth.

The azimuth is the statement rather than a reading of one: the claim is about the phasor's
`arg`, so the quoted `π/2` is what the kernel checks. -/
theorem envelope_phase_misalignment_witness : (rwaAxisPhasor 2 0 0 1).arg = Real.pi / 2 := by
  have h : rwaAxisPhasor 2 0 0 1 = Complex.I := by
    unfold rwaAxisPhasor
    norm_num
  rw [h, Complex.arg_I]

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

/-- **The suppression factor, as an equality.** For the traceless drive `10·σ_z + σ_x` the operator
norm is exactly `11` times the norm of the projected element. The `11×` quoted below is therefore a
computed ratio in a statement, not a figure attached to a strict inequality. -/
theorem transverseElement_suppression_ratio :
    ‖driveOp 0 1 0 10‖ = 11 * ‖projectedDriveElement 1 0‖ := by
  rw [Matrix.linfty_opNorm_def]
  simp [driveOp, projectedDriveElement, σ_x, σ_y, σ_z, Finset.univ_fin2]
  norm_num

/-- **Strict-suppression witness.** A concrete frame where the drive is large in norm but its
projected element is `11×` smaller — the factor being `transverseElement_suppression_ratio`, which
this proof consumes.

The drive is `10·σ_z + σ_x`, deliberately TRACELESS. An earlier version used `10·1 + σ_x`, which
gives the same `11×` ratio but inflates `‖O‖` with the identity — and the identity component `a`
drops out of the co-rotating dynamics entirely, as `longitudinal_drive_purely_counterRotating`
proves above (drives differing only in `a` and `d` differ only in their counter-rotating
remainder). That witness was an artifact. Here the suppression is genuinely due to a
longitudinal-dominant drive: the `σ_z` component is physical, and it is exactly what makes a naive
`θ = Ω·T` calibration wrong. -/
theorem transverseElement_strictly_suppressed :
    ‖projectedDriveElement 1 0‖ < ‖driveOp 0 1 0 10‖ := by
  rw [transverseElement_suppression_ratio]
  have hpos : (0 : ℝ) < ‖projectedDriveElement 1 0‖ := by
    simp [projectedDriveElement]
  linarith

/-! ## 5. Kramers degeneracy

Built from first principles. The repo's `MajoranaKramers` module has NO `Θ`-algebra to reuse:
its `kramers_anticommutation` is a one-line `linarith` on two REALS (`a + b = 0 → a = -b`), and its
`kramers_pfaffian_definite_sign` is a `positivity` discharge of `pf₁ ≥ 0 → pf₂ ≥ 0 → pf₁·pf₂ ≥ 0`
carrying a self-admitted placeholder hypothesis (`∀ a : ℝ, a = a`). Both are true theorems whose
names and docstrings claim matrix/Pfaffian content they do not state. Nothing here is cited as
reused from them.

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

/-- **Two nonzero orthogonal vectors are linearly independent** — the step that turns "there is a
second eigenvector" into "the eigenspace has dimension ≥ 2". -/
theorem linearIndependent_of_inner_eq_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0)
    (horth : ⟪y, x⟫_ℂ = 0) : ∀ s t : ℂ, s • x + t • y = 0 → s = 0 ∧ t = 0 := by
  intro s t hst
  have hxx : ⟪x, x⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hx
  have hyy : ⟪y, y⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hy
  have hxy : ⟪x, y⟫_ℂ = 0 := by
    rw [← inner_conj_symm]; simp [horth]
  constructor
  · have h := congrArg (fun z => ⟪z, x⟫_ℂ) hst
    simp only [inner_add_left, inner_smul_left, inner_zero_left, horth] at h
    have h2 : s = 0 ∨ x = 0 := by simpa using h
    exact h2.resolve_right hx
  · have h := congrArg (fun z => ⟪z, y⟫_ℂ) hst
    simp only [inner_add_left, inner_smul_left, inner_zero_left, hxy] at h
    have h2 : t = 0 ∨ y = 0 := by simpa using h
    exact h2.resolve_right hy

/-- **Kramers degeneracy.** For a `Θ`-symmetric Hamiltonian with antiunitary `Θ`, `Θ² = -1`, every
real eigenvalue carries a SECOND eigenvector orthogonal to — and hence linearly independent of —
the first. So no eigenvalue is simple and every level is (at least) doubly degenerate.

The partner is exhibited (`Θ v`), not merely asserted to exist, and the final conjunct is the
degeneracy proper: no NONTRIVIAL scalar combination of the two vanishes, and both lie in the
`lam`-eigenspace by the second conjunct, so that eigenspace really does have dimension at least
two. -/
theorem kramers_degeneracy {Θ : V → V} {H : V →ₗ[ℂ] V}
    (hanti : ∀ x y, ⟪Θ x, Θ y⟫_ℂ = ⟪y, x⟫_ℂ)
    (hconj : ∀ (z : ℂ) (x : V), Θ (z • x) = (starRingEnd ℂ) z • Θ x)
    (hsq : ∀ x, Θ (Θ x) = -x) (hcomm : ∀ x, Θ (H x) = H (Θ x))
    {lam : ℂ} (hreal : (starRingEnd ℂ) lam = lam) {v : V} (hv0 : v ≠ 0) (hv : H v = lam • v) :
    Θ v ≠ 0 ∧ H (Θ v) = lam • Θ v ∧ ⟪Θ v, v⟫_ℂ = 0
      ∧ ∀ s t : ℂ, s • v + t • Θ v = 0 → s = 0 ∧ t = 0 :=
  ⟨kramers_apply_ne_zero hconj hsq hv0,
   kramers_partner_eigenvector hconj hcomm hreal hv,
   kramers_inner_eq_zero hanti hsq v,
   linearIndependent_of_inner_eq_zero hv0 (kramers_apply_ne_zero hconj hsq hv0)
     (kramers_inner_eq_zero hanti hsq v)⟩

/-- **Non-vacuity witness for the `Θ` hypotheses.** The three antiunitary conditions are inhabited:
on `ℂ²` the map `Θ (z₀, z₁) = (-conj z₁, conj z₀)` — i.e. `-iσ_y ∘ (complex conjugation)`, the
standard spin-½ time reversal — is antiunitary with `Θ² = -1`.

This covers the `Θ` hypotheses only. `kramers_degeneracy` additionally requires a commuting `H`, a
real eigenvalue and a nonzero eigenvector; `kramers_degeneracy_instantiated` below supplies those
too, and is what actually rules the degeneracy theorem out of vacuity. -/
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

/-- **Non-vacuity of the DEGENERACY theorem, not merely of its `Θ` hypotheses.**
`kramers_hypotheses_inhabited` inhabits three of `kramers_degeneracy`'s six hypotheses; the other
three — a commuting `H`, a real eigenvalue, a nonzero eigenvector — are supplied here, and
`kramers_degeneracy` is then run on the complete bundle. The final conjunct is its conclusion at a
concrete system, so the degeneracy theorem is exhibited rather than merely satisfiable-looking.

Scope, stated rather than implied: this exhibits ONE admissible system (`H = id`, `lam = 1`). It
certifies that `kramers_degeneracy` is not vacuous; it does not claim to characterise which `H`
are admissible on `ℂ²`, and nothing below rests on such a characterisation. -/
theorem kramers_degeneracy_instantiated :
    ∃ (Θ : EuclideanSpace ℂ (Fin 2) → EuclideanSpace ℂ (Fin 2))
      (H : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2))
      (lam : ℂ) (v : EuclideanSpace ℂ (Fin 2)),
      (∀ x y, ⟪Θ x, Θ y⟫_ℂ = ⟪y, x⟫_ℂ) ∧
      (∀ (z : ℂ) (x : EuclideanSpace ℂ (Fin 2)), Θ (z • x) = (starRingEnd ℂ) z • Θ x) ∧
      (∀ x, Θ (Θ x) = -x) ∧ (∀ x, Θ (H x) = H (Θ x)) ∧
      (starRingEnd ℂ) lam = lam ∧ v ≠ 0 ∧ H v = lam • v ∧
      (∀ s t : ℂ, s • v + t • Θ v = 0 → s = 0 ∧ t = 0) := by
  obtain ⟨Θ, hanti, hsq, hconj⟩ := kramers_hypotheses_inhabited
  set H : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) := LinearMap.id with hHdef
  set v : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![(1 : ℂ), 0] with hvdef
  have hv0 : v ≠ 0 := by
    intro h
    have h0 := congrFun (congrArg WithLp.ofLp h) 0
    rw [hvdef] at h0
    simp at h0
  have hcomm : ∀ x : EuclideanSpace ℂ (Fin 2), Θ (H x) = H (Θ x) := fun _ => rfl
  have hv : H v = (1 : ℂ) • v := by rw [hHdef]; simp
  exact ⟨Θ, H, 1, v, hanti, hconj, hsq, hcomm, by simp, hv0, hv,
    (kramers_degeneracy hanti hconj hsq hcomm (by simp) hv0 hv).2.2.2⟩

end Kramers

end

end SKEFTHawking.Control
