import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance

/-!
# Standard Gaussian moments (Phase 6AG, Ask 4 — foundation for the Haar twirl)

Foundational moment lemmas for the standard 1-D Gaussian `N(0,1)`, the seed of the degree-4
sphere-moment / unitary-2-design identity behind the average-gate-fidelity formula
`F_avg = (d·F_e + 1)/(d+1)`. These are the building blocks the Gaussian→sphere polar route consumes;
the Weingarten/2-design machinery is absent from Mathlib at this pin, so it is built from the
moment level up.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open MeasureTheory ProbabilityTheory

/-- **Second moment of the standard 1-D Gaussian:** `∫ x² ∂N(0,1) = 1`. Since `N(0,1)` has mean `0`,
the second moment equals the variance, which is `1` (`variance_id_gaussianReal`). -/
theorem integral_sq_gaussianReal : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have hv := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [ProbabilityTheory.variance_eq_integral aemeasurable_id] at hv
  simp only [id_eq] at hv
  rw [integral_id_gaussianReal] at hv
  simpa using hv

end SKEFTHawking.QuantumNetwork
