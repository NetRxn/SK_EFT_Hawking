import SKEFTHawking.QuantumNetwork.ReadoutRelaxationBound
import Physlib.StatisticalMechanics.CanonicalEnsemble.TwoState

/-!
# Thermal-population assignment floor (Phase 6AQ, Wave 2)

The thermal-excitation floor on assignment error: a qubit of transition energy `ℏω` thermalized
at temperature `T` has excited-state occupancy `p_th = 1/(1 + e^{βℏω})` (two-level
Boltzmann/detailed-balance form, `β = 1/(k_B T)`). The occupancy is **derived** here from the
PhysLib `CanonicalEnsemble.twoState` closed form (`twoState_probability_snd`) — reused, not
re-derived — via the tanh↔logistic identity `half_one_sub_tanh`. Together with Wave 1
(`ReadoutRelaxationBound`) this completes the device-characterization envelope family: the same
universally-stated parameters `(T₁, T, ω)` that bound gates bound readout.

**Two-layer posture** (the established `plobBound`/coherence-ceiling discipline):

* *Lean-verified layer* — everything below: the occupancy formula and its canonical-ensemble
  derivation, strict antitonicity in `x = βℏω` (hence monotone in `T`, antitone in `ω` — shipped
  as Temperature-indexed corollaries through the PhysLib `Temperature.β` bridge), the endpoints
  (`x → ∞`, i.e. `T → 0⁺`, gives `p_th → 0`; `x = 0`, the high-`T` limit by continuity, gives
  `p_th = ½`), and rational enclosures `(1−x)/(2−x) ≤ p_th ≤ 1/(2+x)` (both endpoints rational
  at rational `x`, via the Phase-6AP `expNeg_enclosure` Bernoulli bracket — no floating-point
  `exp`).
* *Literature-cited layer* — the reading of `p_th` as an assignment-error floor (residual
  thermal population indistinguishable from signal under the stated readout model, i.e. the
  qubit is found excited before the measurement begins): see e.g. Geerlings et al., PRL **110**,
  120501 (2013); Jin et al., PRL **114**, 240501 (2015). That identification is a modelling
  step and is **never** part of a theorem statement below — the floor theorems take
  `p_th ≤ ε₁` as an explicit hypothesis.

Invariants (Phase 6AQ): kernel-pure `{propext, Classical.choice, Quot.sound}`; zero sorry;
no project-local axioms; no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Filter

/-- **Two-level thermal excited-state occupancy** at dimensionless inverse temperature
`x = βℏω`: `p_th = 1/(1 + e^x)` (Boltzmann/detailed-balance form; the Fermi/logistic
function). -/
noncomputable def thermalExcitedPop (x : ℝ) : ℝ := 1 / (1 + Real.exp x)

/-- The tanh↔logistic identity `½(1 − tanh u) = 1/(1 + e^{2u})` — the bridge between the
PhysLib two-state closed form (in `tanh`) and the Boltzmann occupancy form. -/
theorem half_one_sub_tanh (u : ℝ) : 1 / 2 * (1 - Real.tanh u) = 1 / (1 + Real.exp (2 * u)) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have hee : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have h2u : Real.exp (2 * u) = Real.exp u * Real.exp u := by
    rw [← Real.exp_add]; congr 1; ring
  have hsum : (0 : ℝ) < Real.exp u + Real.exp (-u) := by positivity
  have h1p : (0 : ℝ) < 1 + Real.exp (2 * u) := by positivity
  field_simp
  linear_combination 2 * Real.exp u * hee + 2 * Real.exp (-u) * h2u

/-- **Canonical-ensemble derivation of the occupancy** (reuses PhysLib, does not re-derive): the
probability of state `1` of the PhysLib two-state ensemble with level splitting `E₀`
(state-`0` energy `0`, state-`1` energy `E₀` — the excited state for `E₀ > 0`; the identity
holds for all `E₀`) at temperature `T` **is** `thermalExcitedPop (β·E₀)`. The
Boltzmann/detailed-balance form of the floor is therefore a theorem of statistical
mechanics here, not a definition. -/
theorem twoState_excited_probability (E0 : ℝ) (T : Temperature) :
    (CanonicalEnsemble.twoState 0 E0).probability T 1
      = thermalExcitedPop ((Temperature.β T : ℝ) * E0) := by
  have h : 2 * ((Temperature.β T : ℝ) * E0 / 2) = (Temperature.β T : ℝ) * E0 := by ring
  rw [CanonicalEnsemble.twoState_probability_snd, sub_zero, half_one_sub_tanh, h,
    thermalExcitedPop]

/-- The thermal occupancy is strictly positive at every finite `x` — no finite temperature
fully empties the excited state. -/
theorem thermalExcitedPop_pos (x : ℝ) : 0 < thermalExcitedPop x := by
  unfold thermalExcitedPop
  positivity

/-- **High-temperature endpoint:** at `x = 0` (the `T → ∞` limit point, attained by continuity
`thermalExcitedPop_continuous`) the occupancy is exactly `½` — full thermal mixing. -/
theorem thermalExcitedPop_zero : thermalExcitedPop 0 = 1 / 2 := by
  norm_num [thermalExcitedPop]

/-- The occupancy is continuous (the denominator `1 + e^x` never vanishes). With
`thermalExcitedPop_zero` this gives the high-`T` endpoint `p_th → ½` as `x → 0`. -/
theorem thermalExcitedPop_continuous : Continuous thermalExcitedPop :=
  continuous_const.div (continuous_const.add Real.continuous_exp) fun x => by positivity

/-- **Strict antitonicity in `x = βℏω`** (full `StrictAnti` on ℝ): colder or stiffer qubits have
strictly smaller thermal occupancy. The Temperature- and frequency-indexed readings are the
corollaries `thermalExcitedPop_mono_temperature` / `thermalExcitedPop_anti_frequency`. -/
theorem thermalExcitedPop_strictAnti : StrictAnti thermalExcitedPop := by
  intro x y hxy
  unfold thermalExcitedPop
  have h1 : (0 : ℝ) < 1 + Real.exp x := by positivity
  have h2 : Real.exp x < Real.exp y := Real.exp_lt_exp.mpr hxy
  exact one_div_lt_one_div_of_lt h1 (by linarith)

/-- The occupancy never exceeds the fully-mixed value `½` on the physical domain `x ≥ 0`. -/
theorem thermalExcitedPop_le_half {x : ℝ} (hx : 0 ≤ x) : thermalExcitedPop x ≤ 1 / 2 :=
  thermalExcitedPop_zero ▸ thermalExcitedPop_strictAnti.antitone hx

/-- **Zero-temperature endpoint:** the occupancy vanishes as `x = βℏω → ∞` (i.e. `T → 0⁺` at
fixed `ω`) — the thermal floor, unlike the relaxation floor, can be frozen out. -/
theorem thermalExcitedPop_tendsto_zero : Tendsto thermalExcitedPop atTop (nhds 0) := by
  have h : Tendsto (fun x : ℝ => 1 + Real.exp x) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 Real.tendsto_exp_atTop
  exact h.inv_tendsto_atTop.congr fun x => by simp [thermalExcitedPop, one_div]

/-! ## Temperature- and frequency-indexed monotonicity (PhysLib `Temperature.β` bridge) -/

/-- The PhysLib inverse temperature `β = 1/(k_B T)` is antitone in `T` on positive
temperatures. -/
theorem temperature_beta_anti {T T' : Temperature} (hT : 0 < T.val)
    (hTT : T.val ≤ T'.val) : (Temperature.β T' : ℝ) ≤ (Temperature.β T : ℝ) := by
  have hβ : (Temperature.β T : ℝ) = 1 / (Constants.kB * (T : ℝ)) := rfl
  have hβ' : (Temperature.β T' : ℝ) = 1 / (Constants.kB * (T' : ℝ)) := rfl
  have hTr : (0 : ℝ) < (T : ℝ) := hT
  have hTTr : ((T : ℝ) : ℝ) ≤ (T' : ℝ) := by exact_mod_cast hTT
  rw [hβ, hβ']
  apply one_div_le_one_div_of_le (mul_pos Constants.kB_pos hTr)
  exact mul_le_mul_of_nonneg_left hTTr Constants.kB_nonneg

/-- **The thermal floor worsens monotonically with temperature:** for a fixed level splitting
`E₀ ≥ 0`, `T ≤ T'` implies `p_th(T) ≤ p_th(T')`. -/
theorem thermalExcitedPop_mono_temperature {E0 : ℝ} (hE0 : 0 ≤ E0) {T T' : Temperature}
    (hT : 0 < T.val) (hTT : T.val ≤ T'.val) :
    thermalExcitedPop ((Temperature.β T : ℝ) * E0)
      ≤ thermalExcitedPop ((Temperature.β T' : ℝ) * E0) :=
  thermalExcitedPop_strictAnti.antitone
    (mul_le_mul_of_nonneg_right (temperature_beta_anti hT hTT) hE0)

/-- **The thermal floor improves with qubit frequency:** a larger level splitting gives a
smaller occupancy (`ω ≤ ω'` ⟹ `p_th(ω') ≤ p_th(ω)`). No temperature hypothesis is needed —
`β ≥ 0` holds unconditionally (`Temperature.β` is `ℝ≥0`-valued), so the inequality survives
even the `β = 0` junk point. -/
theorem thermalExcitedPop_anti_frequency {E0 E0' : ℝ} {T : Temperature} (hE : E0 ≤ E0') :
    thermalExcitedPop ((Temperature.β T : ℝ) * E0')
      ≤ thermalExcitedPop ((Temperature.β T : ℝ) * E0) :=
  thermalExcitedPop_strictAnti.antitone
    (mul_le_mul_of_nonneg_left hE (Temperature.β T).coe_nonneg)

/-- Strict companion of `temperature_beta_anti`: strictly hotter means strictly smaller `β`. -/
theorem temperature_beta_strictAnti {T T' : Temperature} (hT : 0 < T.val)
    (hTT : T.val < T'.val) : (Temperature.β T' : ℝ) < (Temperature.β T : ℝ) := by
  have hβ : (Temperature.β T : ℝ) = 1 / (Constants.kB * (T : ℝ)) := rfl
  have hβ' : (Temperature.β T' : ℝ) = 1 / (Constants.kB * (T' : ℝ)) := rfl
  have hTr : (0 : ℝ) < (T : ℝ) := hT
  have hTTr : ((T : ℝ) : ℝ) < (T' : ℝ) := by exact_mod_cast hTT
  rw [hβ, hβ']
  apply one_div_lt_one_div_of_lt (mul_pos Constants.kB_pos hTr)
  exact mul_lt_mul_of_pos_left hTTr Constants.kB_pos

/-- Strict companion of `thermalExcitedPop_mono_temperature`: at a strictly positive splitting,
strictly hotter means a strictly worse thermal floor. -/
theorem thermalExcitedPop_strictMono_temperature {E0 : ℝ} (hE0 : 0 < E0) {T T' : Temperature}
    (hT : 0 < T.val) (hTT : T.val < T'.val) :
    thermalExcitedPop ((Temperature.β T : ℝ) * E0)
      < thermalExcitedPop ((Temperature.β T' : ℝ) * E0) :=
  thermalExcitedPop_strictAnti
    (mul_lt_mul_of_pos_right (temperature_beta_strictAnti hT hTT) hE0)

/-- Strict companion of `thermalExcitedPop_anti_frequency`: at fixed `T > 0`, a strictly larger
splitting strictly lowers the occupancy. -/
theorem thermalExcitedPop_strictAnti_frequency {E0 E0' : ℝ} {T : Temperature}
    (hT : 0 < T.val) (hE : E0 < E0') :
    thermalExcitedPop ((Temperature.β T : ℝ) * E0')
      < thermalExcitedPop ((Temperature.β T : ℝ) * E0) :=
  thermalExcitedPop_strictAnti (mul_lt_mul_of_pos_left hE (Temperature.beta_pos T hT))

/-! ## Rational enclosures (Phase-6AP `expNeg_enclosure` Bernoulli bracket) -/

/-- The occupancy in decaying-exponential form: `p_th = e^{−x}/(1 + e^{−x})` — the form the
`expNeg_enclosure` bracket applies to. -/
theorem thermalExcitedPop_expNeg_form (x : ℝ) :
    thermalExcitedPop x = Real.exp (-x) / (1 + Real.exp (-x)) := by
  unfold thermalExcitedPop
  have hee : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have h1 : (0 : ℝ) < 1 + Real.exp x := by positivity
  have h2 : (0 : ℝ) < 1 + Real.exp (-x) := by positivity
  field_simp
  linear_combination -hee

/-- **Rational upper enclosure** `p_th ≤ 1/(2 + x)` on the physical domain `x ≥ 0` (via the
upper `expNeg_enclosure` endpoint `e^{−x} ≤ 1/(1+x)`); rational at rational `x`. -/
theorem thermalExcitedPop_rational_upper {x : ℝ} (hx : 0 ≤ x) :
    thermalExcitedPop x ≤ 1 / (2 + x) := by
  obtain ⟨-, h2⟩ := expNeg_enclosure hx
  have hu : (0 : ℝ) < Real.exp (-x) := Real.exp_pos _
  have hux : Real.exp (-x) * (1 + x) ≤ 1 := (le_div_iff₀ (by linarith)).mp h2
  rw [thermalExcitedPop_expNeg_form, div_le_div_iff₀ (by positivity) (by linarith)]
  nlinarith

/-- **Rational lower enclosure** `(1−x)/(2−x) ≤ p_th` for `0 ≤ x < 2` (via the lower
`expNeg_enclosure` endpoint `1 − x ≤ e^{−x}`); rational at rational `x`. Sharp at `x = 0`
(both sides `½`). -/
theorem thermalExcitedPop_rational_lower {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x < 2) :
    (1 - x) / (2 - x) ≤ thermalExcitedPop x := by
  obtain ⟨h1, -⟩ := expNeg_enclosure hx0
  have hu : (0 : ℝ) < Real.exp (-x) := Real.exp_pos _
  rw [thermalExcitedPop_expNeg_form, div_le_div_iff₀ (by linarith) (by positivity)]
  nlinarith

/-! ## Averaged-assignment floor (family capstone with Wave 1) -/

/-- **Thermal floor on the averaged assignment error.** For any readout whose excited-branch
misassignment is at least the thermal occupancy (the literature-cited model hypothesis, module
header) and whose ground-branch error is nonnegative, the averaged assignment error is floored
at `p_th/2`. -/
theorem avgAssignmentError_thermal_floor {x e0 e1 : ℝ} (he0 : 0 ≤ e0)
    (he1 : thermalExcitedPop x ≤ e1) :
    thermalExcitedPop x / 2 ≤ avgAssignmentError e0 e1 := by
  unfold avgAssignmentError
  linarith

/-- **Rational thermal floor** — the W2 companion of `avgAssignmentError_rational_floor`: the
composition of the thermal floor with the lower enclosure endpoint gives the rational
operating-point bound `(1−x)/(2(2−x)) ≤ ε_avg` for `0 ≤ x < 2`. -/
theorem avgAssignmentError_thermal_rational_floor {x e0 e1 : ℝ} (hx0 : 0 ≤ x) (hx2 : x < 2)
    (he0 : 0 ≤ e0) (he1 : thermalExcitedPop x ≤ e1) :
    (1 - x) / (2 * (2 - x)) ≤ avgAssignmentError e0 e1 := by
  have hfloor := avgAssignmentError_thermal_floor he0 he1
  have hencl := thermalExcitedPop_rational_lower hx0 hx2
  have hne : (2 : ℝ) - x ≠ 0 := by linarith
  have hrw : (1 - x) / (2 * (2 - x)) = (1 - x) / (2 - x) / 2 := by
    field_simp
  rw [hrw]
  linarith

/-- **Combined relaxation + thermal floor** — the envelope-family capstone: a readout subject to
both mechanisms (excited-branch misassignment at least the window decay probability *and* at
least the thermal occupancy) has averaged assignment error floored by the *worse* of the two:
`max(p_decay, p_th)/2 ≤ ε_avg`. -/
theorem avgAssignmentError_combined_floor {t T1 x e0 e1 : ℝ} (he0 : 0 ≤ e0)
    (hd : readoutDecayProb t T1 ≤ e1) (hth : thermalExcitedPop x ≤ e1) :
    max (readoutDecayProb t T1) (thermalExcitedPop x) / 2 ≤ avgAssignmentError e0 e1 := by
  rcases max_cases (readoutDecayProb t T1) (thermalExcitedPop x) with ⟨h, -⟩ | ⟨h, -⟩ <;>
    rw [h] <;> unfold avgAssignmentError <;> linarith

end SKEFTHawking.QuantumNetwork
