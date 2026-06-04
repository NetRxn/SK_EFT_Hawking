import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Repeaterless rate bound: the loss-penalty function (Phase 6AK, Wave 6AK.2 — surrogate)

The Pirandola–Laurenza–Ottaviani–Banchi (PLOB) repeaterless bound caps the two-way-assisted
secret-key / entanglement rate of a lossy channel of transmissivity `η` at `−log₂(1−η)` bits per
channel use. The full theorem rests on continuous-variable channel-capacity theory (relative entropy
of entanglement of bosonic Gaussian channels) that is far from Mathlib's current library.

This wave formalizes the **rate-bound function** `plobBound η = −log₂(1−η)` and its rigorous
loss-penalty properties — the mathematically tractable surrogate that captures the *physical content*
of the no-go (the rate cap is finite, vanishes at total loss, grows monotonically with transmissivity,
is at least linear in `η`, and decays to `0` over a fiber whose transmissivity falls exponentially with
distance). It is **not** a derivation of the PLOB theorem from quantum mechanics; it is the analytic
behaviour of the bound itself, honestly scoped.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Real Filter Topology

/-- The **PLOB repeaterless rate-bound function**: `−log₂(1−η)` bits per channel use, for a lossy
channel of transmissivity `η ∈ [0,1)`. -/
noncomputable def plobBound (η : ℝ) : ℝ := -Real.logb 2 (1 - η)

/-- At zero transmissivity the rate cap is zero: no transmission permits no key. -/
theorem plobBound_zero : plobBound 0 = 0 := by simp [plobBound]

/-- **The rate cap is nonnegative** for a physical transmissivity `η ∈ [0,1)`. -/
theorem plobBound_nonneg {η : ℝ} (h0 : 0 ≤ η) (h1 : η < 1) : 0 ≤ plobBound η := by
  rw [plobBound, neg_nonneg]
  apply Real.logb_nonpos (by norm_num) (by linarith)
  linarith

/-- **The loss-penalty lower bound:** the repeaterless rate cap is at least linear in the
transmissivity, `η / ln 2 ≤ plobBound η`. (Equivalently `−ln(1−η) ≥ η`.) This is the quantitative
loss penalty: even the *upper bound* on the achievable rate cannot beat `η`-linear scaling. -/
theorem linear_le_plobBound {η : ℝ} (h1 : η < 1) : η / Real.log 2 ≤ plobBound η := by
  have hlog : Real.log (1 - η) ≤ -η := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 - η by linarith)
    linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [plobBound, Real.logb, ← neg_div, div_le_div_iff_of_pos_right hl2]
  linarith

/-- **Strict monotonicity:** a less lossy channel (higher transmissivity) permits a strictly higher
rate cap. -/
theorem plobBound_strictMonoOn : StrictMonoOn plobBound (Set.Iio 1) := by
  intro a ha b hb hab
  simp only [Set.mem_Iio] at ha hb
  rw [plobBound, plobBound, neg_lt_neg_iff]
  exact Real.logb_lt_logb (by norm_num) (by linarith) (by linarith)

/-- **Exponential distance decay:** along a fiber whose transmissivity falls exponentially with
distance, `η(L) = e^{−L/L_att}`, the repeaterless rate cap tends to `0` as `L → ∞`. -/
theorem plobBound_tendsto_zero_of_exp_decay {Latt : ℝ} (hLatt : 0 < Latt) :
    Tendsto (fun L : ℝ => plobBound (Real.exp (-L / Latt))) atTop (𝓝 0) := by
  have hη : Tendsto (fun L : ℝ => Real.exp (-L / Latt)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    apply Tendsto.atBot_div_const hLatt
    exact tendsto_neg_atBot_iff.mpr tendsto_id
  have : Tendsto (fun η : ℝ => plobBound η) (𝓝 0) (𝓝 (plobBound 0)) := by
    rw [plobBound]
    apply Tendsto.neg
    apply (Real.continuousAt_logb (by norm_num)).comp
    · exact (continuous_const.sub continuous_id).continuousAt
  rw [plobBound_zero] at this
  exact this.comp hη

end SKEFTHawking.QuantumNetwork
