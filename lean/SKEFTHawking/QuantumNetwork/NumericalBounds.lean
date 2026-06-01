import Mathlib.Analysis.SpecialFunctions.Exp
import SKEFTHawking.QuantumNetwork.Channels

/-!
# Kernel-only transcendental bounds (Phase 6AA, Wave 2)

The Wave-2 technique (DR-INT): two-sided enclosures of the `Real.exp(−x)` factors
that appear in fiber-loss / memory-decoherence channels, proved **kernel-only**
from Mathlib's existing exponential lemmas — **no `native_decide`, no external
interval library**. A representative bound at a sample operating point is given
here using the Bernoulli envelopes `Real.add_one_le_exp`; tighter targets use the
`Real.exp_bound` Taylor-squeeze with a per-precision Taylor order (DR-INT §3(c)),
the same `norm_num1`-discharged pattern as Mathlib's `ExponentialBounds.lean`.

Invariants (Phase 6AA): kernel-pure, zero sorry, no project-local axioms,
no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

open Real

/-- Representative fiber-loss factor enclosure: at `α = 0.046 Np/km`, `L = 10 km`
the transmission factor is `exp(−0.46)`, kernel-only bracketed via the Bernoulli
envelopes `x+1 ≤ exp x`. (This is the `exp`-form value of `fiberTransmission` at
0.2 dB/km × 10 km, through the dB↔Np identity `fiberTransmission_eq_exp_neg_attenuationNp`.) -/
theorem expNeg046_enclosure :
    (0.54 : ℝ) ≤ Real.exp (-0.46) ∧ Real.exp (-0.46) ≤ 1 / 1.46 := by
  refine ⟨by linarith [Real.add_one_le_exp (-0.46 : ℝ)], ?_⟩
  rw [Real.exp_neg, show (1 / 1.46 : ℝ) = (1.46 : ℝ)⁻¹ by norm_num]
  exact inv_anti₀ (by norm_num) (by linarith [Real.add_one_le_exp (0.46 : ℝ)])

/-! ## Tight Taylor-squeeze (Wave 1 macro-layer pattern)

The tight enclosure via Mathlib's `Real.exp_bound` (degree-`n` Taylor remainder
`|exp x − Σ_{m<n} xᵐ/m!| ≤ |x|ⁿ·(n+1)/(n!·n)`), kernel-only. Per DR-INT §3(c) the
Taylor order for `|x| ≤ 1` to reach a target precision `ε` is roughly the least `n`
with `|x|ⁿ/n! ≤ ε` (e.g. `x=−0.46` ⟹ `n=5` for `±2·10⁻⁴`). The pattern below is the
reusable squeeze; a full `exp_squeeze`/`log_squeeze` elaborator macro emitting it in
one line is the documented metaprogramming extension. -/

/-- Tight enclosure of the representative fiber-loss factor `exp(−0.46)` to ~3
decimals via the degree-5 Taylor squeeze (cf. the loose Bernoulli `expNeg046_enclosure`). -/
theorem expNeg046_tight :
    (0.631 : ℝ) ≤ Real.exp (-0.46) ∧ Real.exp (-0.46) ≤ 0.632 := by
  have h := Real.exp_bound (x := (-0.46 : ℝ)) (by norm_num) (n := 5) (by norm_num)
  rw [abs_le] at h
  obtain ⟨hlo, hhi⟩ := h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlo hhi
  norm_num at hlo hhi
  constructor <;> linarith

end SKEFTHawking.QuantumNetwork
