import SKEFTHawking.QuantumNetwork.CoherenceFidelity
import SKEFTHawking.QuantumNetwork.NumericalBounds

/-!
# Readout-window relaxation envelope (Phase 6AQ, Wave 1)

The assignment-error floor imposed by relaxation during a finite measurement window: for a
readout window of duration `t ≥ 0` on a qubit with relaxation time `T₁ > 0`, the excited-state
decay probability is `p_decay(t,T₁) = 1 − e^{−t/T₁}`. This completes the device-characterization
envelope family: the same universally-stated coherence parameters that bound *gate* performance
(`CoherenceFidelity` — coherence-limited fidelity ceiling) here bound *readout* performance. The
formal family link is `readoutDecayProb_eq_cohGamma`: the readout decay probability **is** the
amplitude-damping weight `γ(t,T₁)` of the coherence channel, evaluated at the readout window.

**Two-layer posture** (the established `plobBound`/coherence-ceiling discipline):

* *Lean-verified layer* — everything below: the decay formula, its range `[0,1)`, strict
  monotonicity in the window `t`, antitonicity in `T₁`, the endpoints (`p(0) = 0`,
  `p → 1` as `t → ∞`), the rational enclosure `(t/T₁)/(1+t/T₁) ≤ p ≤ t/T₁` (via
  `expNeg_enclosure` — both endpoints rational at rational `t/T₁`, no floating-point `exp`),
  and the averaged-assignment floor with the uniform-prior model prefactor `½`.
* *Literature-cited layer* — the identification of `p_decay` with the device's excited-branch
  misassignment probability `ε₁`. This holds under the standard dispersive-readout model
  (QND-ideal readout, no re-excitation, a relaxation event during the window flips the recorded
  outcome): Gambetta et al., PRA **76**, 012325 (2007); Walter et al., PRApplied **7**, 054020
  (2017). That identification is a modelling step and is **never** part of a theorem statement
  below — the floor theorems take `p_decay ≤ ε₁` as an explicit hypothesis.

Invariants (Phase 6AQ): kernel-pure `{propext, Classical.choice, Quot.sound}`; zero sorry;
no project-local axioms; no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Filter

/-- **Excited-state decay probability over a readout window** of duration `t` with relaxation
time `T₁`: `p_decay = 1 − e^{−t/T₁}`. Under the literature-cited decay-flips-outcome readout
model (module header) this is the model-level excited-branch misassignment. -/
noncomputable def readoutDecayProb (t T1 : ℝ) : ℝ := 1 - Real.exp (-t / T1)

/-- **Family link:** the readout decay probability is definitionally the amplitude-damping
weight `γ(t,T₁)` of the coherence channel (`CoherenceFidelity.cohGamma`) at the readout window —
the same coherence data that bounds gates bounds readout. Used below to import the gate-side
range lemma `cohGamma_nonneg` (the upper range ships sharper here: strict `< 1`). -/
theorem readoutDecayProb_eq_cohGamma (t T1 : ℝ) : readoutDecayProb t T1 = cohGamma t T1 := rfl

/-- The decay probability is nonnegative on physical windows (`t ≥ 0`, `T₁ > 0`). -/
theorem readoutDecayProb_nonneg {t T1 : ℝ} (ht : 0 ≤ t) (hT1 : 0 < T1) :
    0 ≤ readoutDecayProb t T1 :=
  readoutDecayProb_eq_cohGamma t T1 ▸ cohGamma_nonneg ht hT1

/-- The decay probability is **strictly** below `1` for every finite window (sharper than the
gate-side `cohGamma_le_one`): a finite readout window never decays the excited state with
certainty. -/
theorem readoutDecayProb_lt_one (t T1 : ℝ) : readoutDecayProb t T1 < 1 := by
  have := Real.exp_pos (-t / T1)
  unfold readoutDecayProb
  linarith

/-- **Zero-window endpoint:** an instantaneous readout suffers no relaxation, `p_decay(0) = 0`. -/
theorem readoutDecayProb_zero_time (T1 : ℝ) : readoutDecayProb 0 T1 = 0 := by
  simp [readoutDecayProb]

/-- Every strictly positive window has a strictly positive decay probability — the relaxation
floor cannot be evaded by any finite `T₁`. -/
theorem readoutDecayProb_pos {t T1 : ℝ} (ht : 0 < t) (hT1 : 0 < T1) :
    0 < readoutDecayProb t T1 := by
  have h : Real.exp (-t / T1) < 1 :=
    Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_lt_zero.mpr ht) hT1)
  unfold readoutDecayProb
  linarith

/-- **Strict monotonicity in the window:** a longer readout window strictly increases the decay
probability (full `StrictMono` on ℝ; the non-strict form is `.monotone`). -/
theorem readoutDecayProb_strictMono_time {T1 : ℝ} (hT1 : 0 < T1) :
    StrictMono fun t => readoutDecayProb t T1 := by
  intro t t' htt
  have h : Real.exp (-t' / T1) < Real.exp (-t / T1) := by
    apply Real.exp_lt_exp.mpr
    rw [neg_div, neg_div]
    exact neg_lt_neg ((div_lt_div_iff_of_pos_right hT1).mpr htt)
  simp only [readoutDecayProb]
  linarith

/-- **Antitonicity in the relaxation time:** better coherence hardware (larger `T₁`) gives a
smaller decay probability over the same window. -/
theorem readoutDecayProb_anti_relax {t T1 T1' : ℝ} (ht : 0 ≤ t) (hT1 : 0 < T1)
    (hTT : T1 ≤ T1') : readoutDecayProb t T1' ≤ readoutDecayProb t T1 := by
  have hdiv : t / T1' ≤ t / T1 := by gcongr
  have h : Real.exp (-t / T1) ≤ Real.exp (-t / T1') := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div]
    exact neg_le_neg hdiv
  unfold readoutDecayProb
  linarith

/-- **Strict antitonicity in the relaxation time** on positive windows: strictly better
coherence hardware strictly lowers the decay probability. -/
theorem readoutDecayProb_strictAnti_relax {t T1 T1' : ℝ} (ht : 0 < t) (hT1 : 0 < T1)
    (hTT : T1 < T1') : readoutDecayProb t T1' < readoutDecayProb t T1 := by
  have hdiv : t / T1' < t / T1 := by gcongr
  have h : Real.exp (-t / T1) < Real.exp (-t / T1') := by
    apply Real.exp_lt_exp.mpr
    rw [neg_div, neg_div]
    exact neg_lt_neg hdiv
  unfold readoutDecayProb
  linarith

/-- **Infinite-window endpoint:** the decay probability tends to `1` as the window grows —
relaxation eventually erases the excited state entirely. -/
theorem readoutDecayProb_tendsto_one {T1 : ℝ} (hT1 : 0 < T1) :
    Tendsto (fun t => readoutDecayProb t T1) atTop (nhds 1) := by
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(t / T1))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_div_const hT1)
  have h1 : Tendsto (fun t => readoutDecayProb t T1) atTop (nhds (1 - 0)) := by
    simpa only [readoutDecayProb, neg_div] using hexp.const_sub 1
  simpa using h1

/-- **Rational enclosure of the decay probability** (via the Phase-6AP `expNeg_enclosure`
Bernoulli bracket): `(t/T₁)/(1 + t/T₁) ≤ p_decay ≤ t/T₁`. Both endpoints are rational at
rational `t/T₁`, so every operating point admits a machine-checkable rational bracket with no
floating-point `exp`. The upper bound is the familiar short-window rule `p_decay ≲ t/T₁`,
proved as an exact inequality on the full physical domain. -/
theorem readoutDecayProb_enclosure {t T1 : ℝ} (ht : 0 ≤ t) (hT1 : 0 < T1) :
    t / T1 / (1 + t / T1) ≤ readoutDecayProb t T1 ∧ readoutDecayProb t T1 ≤ t / T1 := by
  have hr : 0 ≤ t / T1 := div_nonneg ht hT1.le
  obtain ⟨h1, h2⟩ := expNeg_enclosure hr
  have hpos : (0 : ℝ) < 1 + t / T1 := by linarith
  unfold readoutDecayProb
  rw [neg_div]
  constructor
  · have key : t / T1 / (1 + t / T1) = 1 - 1 / (1 + t / T1) := by field_simp; ring
    rw [key]
    linarith
  · linarith

/-! ## Averaged-assignment floor (uniform-prior model prefactor `½`) -/

/-- Model-level **averaged assignment error** of a binary readout with ground-branch
misassignment `e₀` and excited-branch misassignment `e₁`, under a uniform prior over the two
prepared states: `ε_avg = (e₀ + e₁)/2`. -/
noncomputable def avgAssignmentError (e0 e1 : ℝ) : ℝ := (e0 + e1) / 2

/-- **Relaxation floor on the averaged assignment error.** For any readout whose excited-branch
misassignment is at least the window decay probability (the literature-cited model hypothesis,
module header) and whose ground-branch error is nonnegative, the averaged assignment error is
floored at `p_decay/2` — the uniform-prior model prefactor is exactly `½`. -/
theorem avgAssignmentError_relaxation_floor {t T1 e0 e1 : ℝ} (he0 : 0 ≤ e0)
    (he1 : readoutDecayProb t T1 ≤ e1) :
    readoutDecayProb t T1 / 2 ≤ avgAssignmentError e0 e1 := by
  unfold avgAssignmentError
  linarith

/-- **Rational relaxation floor** — the composition of the averaged-assignment floor with the
lower enclosure endpoint: the averaged assignment error is at least `(t/T₁)/(2(1 + t/T₁))`, a
rational bound at rational `t/T₁` usable directly at device operating points. -/
theorem avgAssignmentError_rational_floor {t T1 e0 e1 : ℝ} (ht : 0 ≤ t) (hT1 : 0 < T1)
    (he0 : 0 ≤ e0) (he1 : readoutDecayProb t T1 ≤ e1) :
    t / T1 / (2 * (1 + t / T1)) ≤ avgAssignmentError e0 e1 := by
  have hfloor := avgAssignmentError_relaxation_floor he0 he1
  have hencl := (readoutDecayProb_enclosure ht hT1).1
  have hpos : (0 : ℝ) < 1 + t / T1 := by
    have := div_nonneg ht hT1.le
    linarith
  have hrw : t / T1 / (2 * (1 + t / T1)) = t / T1 / (1 + t / T1) / 2 := by
    field_simp
  rw [hrw]
  linarith

end SKEFTHawking.QuantumNetwork
