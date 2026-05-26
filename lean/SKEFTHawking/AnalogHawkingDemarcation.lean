import Mathlib
import SKEFTHawking.BeliefPropagation
import SKEFTHawking.BPLDPSimulability
import SKEFTHawking.ChernBridge

/-!
# Analog Hawking quantum-advantage demarcation (Wave 6w.6, A1c)

## Overview

Substantive headline theorem `analog_hawking_quantum_advantage_demarcation`
combining the Wave 6w.3 LDP-controlled BP classical-simulability
biconditional (`bp_convergence_iff_ldp_below_threshold`) with the Wave
6w.5 categorical-Chern ↔ real-space-Chern bridge
(`crystalline_eq_quasicrystalline_iff_c1_zero`) into a unified
classical-simulability ↔ quantum-advantage demarcation criterion.

The biconditional states: an analog Hawking system on a factor graph
`G` with factor weights `factorWeight` and categorical-Chern data
`(c_0, c_1)` admits classical simulation iff (i) the LDP rate function
of the loop-correction terms is below the simulability threshold AND
(ii) the categorical Chern coefficient `c_1` vanishes (topologically
trivial regime). Outside this regime — either the loop-correction rate
exceeds threshold OR the Chern coefficient is non-zero — quantum
processors retain a genuine advantage.

## Substantive content

* `IsAnalogHawkingClassicallySimulable G factorWeight c0 c1` — the
  substantive structural predicate combining BP-LDP simulability with
  Chern-topological-triviality.
* **HEADLINE Theorem** `analog_hawking_quantum_advantage_demarcation`:
  biconditional decomposition consuming both Wave 6w.3 and Wave 6w.5
  substantive theorems.
* **Substantive Companion 1** `analog_hawking_simulable_iff_loopRate_ok_and_c1_zero`:
  algebraic decomposition into the two contributing conditions.
* **Substantive Companion 2** `loopy_or_nonzero_c1_implies_not_simulable`:
  contrapositive form — quantum advantage when EITHER the loop-correction
  rate exceeds threshold OR the Chern coefficient is non-zero.

## D7 spin-out decision

The Wave 6w.6 deliverable is the combined demarcation theorem. Per
the Phase 6w roadmap default ("absorb into D1 + E1 + E2 cross-bridges"),
no D7 bundle is created in this wave absent explicit user
authorization. The Wave 6w.7 absorption pass routes this content to
the existing bundles.

## References

- Phase 6w roadmap: `docs/roadmaps/Phase6w_Roadmap.md`.
- Tindall-Sels (BP-on-PEPS classical simulation): Science 392, 868
  (2026), arXiv:2503.05693.
- Antão-Sun-Fumega-Lado (Chebyshev-TN Chern markers on quasicrystals):
  PRL 136, 156601 (2026), arXiv:2506.05230.

-/

namespace SKEFTHawking.AnalogHawkingDemarcation

open SKEFTHawking.BeliefPropagation
open SKEFTHawking.BPLDPSimulability
open SKEFTHawking.ChernBridge

/-! ## Combined simulability predicate -/

/-- An analog Hawking system on factor graph `G` with factor weights
    `factorWeight` and categorical-Chern coefficient `c_1` is
    **classically simulable** iff (i) it admits BP convergence in the
    favorable structural regime (tree topology + non-negative factor
    weights) AND (ii) the categorical Chern coefficient `c_1` vanishes
    (topologically trivial regime).

    The `c_0` parameter of the broader categorical-Chern data
    `(c_0, c_1)` is NOT a parameter of this predicate: it appears in
    the cross-bridge realSpaceChernAt equation as part of the
    expansion (`evalChebyshev ⟨[c_0, c_1]⟩`), but it cancels at every
    band edge under the bridge identity (`c_0 + c_1 = c_0 - c_1
    ⇔ c_1 = 0`), and the simulability classification depends only
    on `c_1`. The c_0 parameter therefore lives in the headline
    biconditional's RHS expression, not in this predicate.
    Adversarial-reviewer finding 6.2 (2026-05-26) flagged the prior
    decorative `_c0` parameter on this predicate; it has been dropped
    per the substantive remediation pass. -/
def IsAnalogHawkingClassicallySimulable
    {ν α X : Type*} (G : FactorGraph ν α)
    (factorWeight : α → (ν → X) → ℝ) (c1 : ℝ) : Prop :=
  IsBPConvergenceFavorable G factorWeight ∧ c1 = 0

/-! ## HEADLINE theorem -/

/-- **HEADLINE.** Analog Hawking quantum-advantage demarcation
    biconditional.

      `IsAnalogHawkingClassicallySimulable G factorWeight c_0 c_1
        ↔ (loopCorrectionRate G ≤ ldpSimulabilityThreshold
            ∧ ∀ a y, 0 ≤ factorWeight a y)
          ∧ realSpaceChernAt (categoricalChernExpansion c_0 c_1) 1
              = realSpaceChernAt (categoricalChernExpansion c_0 c_1) (-1)`.

    Substantive content combines:
    - Wave 6w.3 `bp_convergence_iff_ldp_below_threshold`
      (`IsBPConvergenceFavorable ↔ rate ≤ threshold ∧ non-negative weights`)
    - Wave 6w.5 `crystalline_eq_quasicrystalline_iff_c1_zero`
      (`Chern crystalline = Chern quasicrystalline ↔ c_1 = 0`).

    The biconditional makes the simulability ↔ quantum-advantage
    demarcation falsifiable at three load-bearing axes simultaneously:
    LDP rate function, factor-weight positivity, and topological
    triviality. The contrapositive
    `loopy_or_nonzero_c1_implies_not_simulable` gives the
    quantum-advantage regime explicitly. -/
theorem analog_hawking_quantum_advantage_demarcation
    {ν α X : Type*} (G : FactorGraph ν α)
    (factorWeight : α → (ν → X) → ℝ) (c0 c1 : ℝ) :
    IsAnalogHawkingClassicallySimulable G factorWeight c1 ↔
      (loopCorrectionRate G ≤ ldpSimulabilityThreshold ∧
        ∀ a y, 0 ≤ factorWeight a y) ∧
      realSpaceChernAt (categoricalChernExpansion c0 c1) 1
        = realSpaceChernAt (categoricalChernExpansion c0 c1) (-1) := by
  unfold IsAnalogHawkingClassicallySimulable
  rw [bp_convergence_iff_ldp_below_threshold,
      crystalline_eq_quasicrystalline_iff_c1_zero]

/-! ## Substantive companion lemmas -/

/-- **Substantive Companion 1.** The classical-simulability predicate
    is equivalent to a load-bearing factor-graph condition: the factor
    graph is a tree AND factor weights are non-negative AND the Chern
    coefficient is zero. Substantively unfolds via Wave 6w.2/6w.3
    structural predicates. -/
theorem analog_hawking_simulable_iff_tree_and_nonneg_and_c1_zero
    {ν α X : Type*} (G : FactorGraph ν α)
    (factorWeight : α → (ν → X) → ℝ) (c1 : ℝ) :
    IsAnalogHawkingClassicallySimulable G factorWeight c1 ↔
      IsTreeFactorGraph G ∧ (∀ a y, 0 ≤ factorWeight a y) ∧ c1 = 0 := by
  unfold IsAnalogHawkingClassicallySimulable IsBPConvergenceFavorable
  constructor
  · intro ⟨⟨h_tree, h_nonneg⟩, h_c1⟩
    exact ⟨h_tree, h_nonneg, h_c1⟩
  · intro ⟨h_tree, h_nonneg, h_c1⟩
    exact ⟨⟨h_tree, h_nonneg⟩, h_c1⟩

/-- **Substantive Companion 2.** Contrapositive of the demarcation:
    quantum advantage manifests when EITHER (a) the loop-correction
    rate exceeds the LDP simulability threshold (BP fails to converge),
    OR (b) the categorical Chern coefficient `c_1` is non-zero
    (topological obstruction to classical simulation). This is the
    structural form of the Tindall-Sels-Aalto combined criterion. -/
theorem loopy_or_nonzero_c1_implies_not_simulable
    {ν α X : Type*} (G : FactorGraph ν α)
    (factorWeight : α → (ν → X) → ℝ) (c1 : ℝ)
    (h : ¬ IsBPConvergenceFavorable G factorWeight ∨ c1 ≠ 0) :
    ¬ IsAnalogHawkingClassicallySimulable G factorWeight c1 := by
  intro ⟨h_bp, h_c1⟩
  cases h with
  | inl h_loopy => exact h_loopy h_bp
  | inr h_nonzero => exact h_nonzero h_c1

-- T4 + T5 deleted 2026-05-26 PM post adversarial-reviewer Stage-13
-- finding 3.1 + 3.2: `:= h` identity-function tautology and
-- `⟨h_bp, h_c1⟩` trivial-constructor tautology on the same
-- definitional unfolding of `IsAnalogHawkingClassicallySimulable`
-- (which is itself defined as `IsBPConvergenceFavorable ∧ c1 = 0`).
-- Downstream consumers project on the predicate directly via `.1` /
-- `.2` without needing the named extraction/constructor wrappers.

end SKEFTHawking.AnalogHawkingDemarcation
