import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Code-distance error suppression (Phase 6AK, Wave 6AK.5)

The textbook stabilizer-QEC relation between a physical error rate `p` and the logical error rate of a
distance-`d` code below threshold `p_th`: a distance-`d` code corrects `t = ⌊(d+1)/2⌋ − 1` errors, and
the standard suppression form bounds the logical error rate by `A·(p/p_th)^{⌊(d+1)/2⌋}`. We formalize
the abstract `(A, p, p_th, d)` suppression function and its two load-bearing properties:

* **threshold suppression** — below threshold (`p ≤ p_th`) the bound is monotone *decreasing* in the
  code distance: a larger code suppresses logical errors at least as well;
* **the threshold theorem** — *strictly* below threshold (`p < p_th`) the bound tends to `0` as the
  code distance grows without bound.

This is neutral code-capacity / threshold mathematics only — no device- or compiler-specific content.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Filter Topology

/-- The exponent in the suppression bound for a distance-`d` code: `⌊(d+1)/2⌋` (one more than the
number `t = ⌊(d−1)/2⌋` of correctable errors). Monotone and unbounded in `d`. -/
def suppressionExponent (d : ℕ) : ℕ := (d + 1) / 2

theorem suppressionExponent_mono : Monotone suppressionExponent := fun _ _ h =>
  Nat.div_le_div_right (Nat.add_le_add_right h 1)

theorem suppressionExponent_tendsto_atTop : Tendsto suppressionExponent atTop atTop := by
  refine tendsto_atTop_atTop.2 fun N => ⟨2 * N, fun d hd => ?_⟩
  calc N = (2 * N + 1) / 2 := by omega
    _ ≤ (d + 1) / 2 := Nat.div_le_div_right (by omega)

/-- The **logical error bound** of a distance-`d` stabilizer code at physical error rate `p`,
threshold `p_th`, prefactor `A`: `A·(p/p_th)^{⌊(d+1)/2⌋}`. -/
noncomputable def logicalErrorBound (A p p_th : ℝ) (d : ℕ) : ℝ :=
  A * (p / p_th) ^ suppressionExponent d

theorem logicalErrorBound_nonneg {A p p_th : ℝ} (hA : 0 ≤ A) (hp : 0 ≤ p) (hpth : 0 ≤ p_th)
    (d : ℕ) : 0 ≤ logicalErrorBound A p p_th d :=
  mul_nonneg hA (pow_nonneg (div_nonneg hp hpth) _)

/-- **Below threshold the bound never exceeds the prefactor:** `A·(p/p_th)^t ≤ A` for `p ≤ p_th`. -/
theorem logicalErrorBound_le_prefactor {A p p_th : ℝ} (hA : 0 ≤ A) (hp : 0 ≤ p) (hpth : 0 < p_th)
    (hle : p ≤ p_th) (d : ℕ) : logicalErrorBound A p p_th d ≤ A := by
  refine (mul_le_of_le_one_right hA (pow_le_one₀ (div_nonneg hp hpth.le) ?_))
  rw [div_le_one hpth]; exact hle

/-- **Threshold suppression:** below threshold (`p ≤ p_th`), the logical error bound is monotone
decreasing in the code distance — a larger code suppresses logical errors at least as well. -/
theorem logicalErrorBound_antitone_distance {A p p_th : ℝ} (hA : 0 ≤ A) (hp : 0 ≤ p)
    (hpth : 0 < p_th) (hle : p ≤ p_th) {d d' : ℕ} (hd : d ≤ d') :
    logicalErrorBound A p p_th d' ≤ logicalErrorBound A p p_th d := by
  refine mul_le_mul_of_nonneg_left ?_ hA
  refine pow_le_pow_of_le_one (div_nonneg hp hpth.le) ?_ (suppressionExponent_mono hd)
  rw [div_le_one hpth]; exact hle

/-- **The threshold theorem:** strictly below threshold (`p < p_th`), the logical error bound tends to
`0` as the code distance grows without bound. -/
theorem logicalErrorBound_tendsto_zero {A p p_th : ℝ} (hp : 0 ≤ p) (hlt : p < p_th)
    (hpth : 0 < p_th) :
    Tendsto (fun d => logicalErrorBound A p p_th d) atTop (𝓝 0) := by
  have hb0 : 0 ≤ p / p_th := div_nonneg hp hpth.le
  have hb1 : p / p_th < 1 := (div_lt_one hpth).mpr hlt
  have hpow : Tendsto (fun n : ℕ => (p / p_th) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hb0 hb1
  have hcomp : Tendsto (fun d => (p / p_th) ^ suppressionExponent d) atTop (𝓝 0) :=
    hpow.comp suppressionExponent_tendsto_atTop
  have := hcomp.const_mul A
  simpa [logicalErrorBound, mul_zero] using this

end SKEFTHawking.QuantumNetwork
