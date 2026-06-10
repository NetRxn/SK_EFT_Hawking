import SKEFTHawking.QuantumNetwork.PLOBRateBound

/-!
# Erasure-channel two-way rate-bound formula (Phase 6AP, Wave 4)

The **rate-bound function** of the quantum erasure channel: `erasureBound p = 1 − p` for
erasure probability `p` — the two-way (LOCC-assisted) quantum/secret-key capacity of the
erasure channel (Bennett–DiVincenzo–Smolin, PRL 78, 3217 (1997); also Pirandola–Laurenza–
Ottaviani–Banchi, Nat. Commun. 8, 15043 (2017), §V).

**Two-layer status (mirrors `PLOBRateBound.lean` exactly):** what is formalized here is the
FORMULA and its rigorous properties (range, strict antitonicity, endpoints, and the
loss-channel comparison). The CONVERSE semantics — that no two-way-assisted protocol over
the erasure channel exceeds `1 − p` — rests on the teleportation-stretching / relative-
entropy-of-entanglement machinery and remains a literature-cited layer until that
machinery is formalized. This module is the analytic substrate, not a derivation of the
capacity theorem from quantum mechanics.

Invariants: kernel-pure, zero sorry, zero project-local axioms, no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

/-- **Erasure-channel two-way rate-bound formula** `erasureBound p = 1 − p`
(BDS 1997 / PLOB 2017 §V; formula layer — see module header for the converse layer). -/
noncomputable def erasureBound (p : ℝ) : ℝ := 1 - p

@[simp] theorem erasureBound_zero : erasureBound 0 = 1 := by simp [erasureBound]

@[simp] theorem erasureBound_one : erasureBound 1 = 0 := by simp [erasureBound]

/-- The erasure rate bound is nonnegative on physical erasure probabilities. -/
theorem erasureBound_nonneg {p : ℝ} (hp : p ≤ 1) : 0 ≤ erasureBound p := by
  simp only [erasureBound]; linarith

/-- The erasure rate bound is at most one bit per use. -/
theorem erasureBound_le_one {p : ℝ} (hp : 0 ≤ p) : erasureBound p ≤ 1 := by
  simp only [erasureBound]; linarith

/-- The erasure rate bound is **strictly antitone**: more erasure, strictly less rate.
(The monotonicity content that makes the formula adjudication-usable: a claimed rate
above `1 − p` at a HIGHER erasure probability is a fortiori impossible.) -/
theorem erasureBound_strictAnti : StrictAnti erasureBound := by
  intro a b hab
  simp only [erasureBound]
  linarith

/-- **Loss dominates erasure at matched parameter:** a pure-loss channel of transmissivity
`η` has rate-bound formula at least the erasure formula at erasure probability `1 − η`:

  `erasureBound (1 − η) = η ≤ −log₂(1 − η) = plobBound η`.

Chains through the existing `linear_le_plobBound` (`η/log 2 ≤ plobBound η`) using
`0 < log 2 ≤ 1`. Operationally: treating photon loss as mere erasure UNDERESTIMATES the
loss channel's rate ceiling — the two formulas are NOT interchangeable, and the comparison
direction is now kernel-checked. -/
theorem erasureBound_le_plobBound {η : ℝ} (h0 : 0 ≤ η) (h1 : η < 1) :
    erasureBound (1 - η) ≤ plobBound η := by
  have hlin := linear_le_plobBound h1
  have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (x := 2) (by norm_num)
    linarith
  have hstep : η ≤ η / Real.log 2 := by
    rw [le_div_iff₀ hlog_pos]
    nlinarith
  simp only [erasureBound, sub_sub_cancel]
  linarith

end SKEFTHawking.QuantumNetwork
