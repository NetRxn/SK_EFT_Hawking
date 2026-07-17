import Mathlib
import SKEFTHawking.BeliefPropagation
import SKEFTHawking.BPLDPSimulability
import SKEFTHawking.ChernBridge

/-!
# Analog Hawking quantum-advantage demarcation (Wave 6w.6, A1c)

## Overview

Substantive headline theorem `analog_hawking_fourCycleFree_demarcation`
combining the Wave 6w.3 four-cycle-free / zero-loop-rate biconditional
(`fourCycleFree_nonneg_iff_ldp_rate_zero`) with the Wave 6w.5
categorical-Chern ↔ real-space-Chern bridge
(`crystalline_eq_quasicrystalline_iff_c1_zero`) into a unified
structural demarcation criterion.

The biconditional states: an analog Hawking system on a finite factor
graph `G` with factor weights `factorWeight` and categorical-Chern
data `(c_0, c_1)` satisfies the combined structural screen iff (i) the
loop-correction rate function — the Cramér/Legendre transform of the
Bernoulli loop-presence log-MGF at zero deviation (review-2026-06-05
D7-EV3 upgrade of the former `{0,1}` indicator) — vanishes AND
(ii) the categorical Chern coefficient `c_1` vanishes (topologically
trivial regime). Outside this regime — either the loop-correction rate
is strictly positive (a 4-cycle is present) OR the Chern coefficient is
non-zero — the screen fails.

**Honesty scope (remediation B-04, 2026-07-17).** The structural
condition is *four-cycle-freeness* (+ non-negative weights + trivial
Chern), NOT genuine acyclicity/tree-ness and NOT a proof of classical
simulability or a quantum-advantage lower bound. Zero loop-correction
rate ⟺ four-cycle-free (a bipartite 6-cycle is four-cycle-free yet
loopy), which is a *necessary combinatorial screen* for BP/Bethe
exactness — a genuine tree is strictly stronger. The
"classically simulable" / "quantum advantage" reading is the physical
interpretation of this screen, carried in the surrounding prose (papers
/ README), not established by the Lean statements here.

## Substantive content

* `IsAnalogHawkingFourCycleFreeSimulable G factorWeight c1` — the
  substantive structural predicate combining the four-cycle-free /
  non-negative-weight screen with Chern-topological-triviality.
* **HEADLINE Theorem** `analog_hawking_fourCycleFree_demarcation`:
  biconditional decomposition consuming both Wave 6w.3 and Wave 6w.5
  substantive theorems.
* **Substantive Companion 1** `analog_hawking_simulable_iff_fourCycleFree_and_nonneg_and_c1_zero`:
  algebraic decomposition into the three contributing conditions.
* **Substantive Companion 2** `not_fourCycleFreeNonneg_or_nonzero_c1_implies_not_simulable`:
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
    `factorWeight` and categorical-Chern coefficient `c_1` satisfies the
    **four-cycle-free simulability screen** iff (i) it lies in the
    four-cycle-free / non-negative-weight structural regime
    (`IsFourCycleFreeNonnegWeighted`) AND (ii) the categorical Chern
    coefficient `c_1` vanishes (topologically trivial regime).

    **Honesty scope (B-04).** The structural condition is
    four-cycle-freeness — strictly weaker than a tree (a bipartite
    6-cycle qualifies) — and does NOT by itself establish BP convergence
    or classical simulability; it is a necessary combinatorial screen
    (see `IsFourCycleFreeNonnegWeighted`). The "classically simulable"
    reading is the physical interpretation carried in the surrounding
    papers/README prose, not proved by this predicate.

    The `c_0` parameter of the broader categorical-Chern data
    `(c_0, c_1)` is NOT a parameter of this predicate: it appears in
    the cross-bridge realSpaceChernAt equation as part of the
    expansion (`evalChebyshev ⟨[c_0, c_1]⟩`), but it cancels at every
    band edge under the bridge identity (`c_0 + c_1 = c_0 - c_1
    ⇔ c_1 = 0`), and the classification depends only on `c_1`. The c_0
    parameter therefore lives in the headline biconditional's RHS
    expression, not in this predicate. Adversarial-reviewer finding 6.2
    (2026-05-26) flagged the prior decorative `_c0` parameter on this
    predicate; it has been dropped per the substantive remediation
    pass. -/
def IsAnalogHawkingFourCycleFreeSimulable
    {ν α X : Type*} (G : FactorGraph ν α)
    (factorWeight : α → (ν → X) → ℝ) (c1 : ℝ) : Prop :=
  IsFourCycleFreeNonnegWeighted G factorWeight ∧ c1 = 0

/-! ## HEADLINE theorem -/

/-- **HEADLINE.** Analog Hawking four-cycle-free / trivial-Chern
    demarcation biconditional.

      `IsAnalogHawkingFourCycleFreeSimulable G factorWeight c_1
        ↔ (loopCorrectionRate G = 0
            ∧ ∀ a y, 0 ≤ factorWeight a y)
          ∧ realSpaceChernAt (categoricalChernExpansion c_0 c_1) 1
              = realSpaceChernAt (categoricalChernExpansion c_0 c_1) (-1)`.

    Substantive content combines:
    - Wave 6w.3 `fourCycleFree_nonneg_iff_ldp_rate_zero`
      (`IsFourCycleFreeNonnegWeighted ↔ rate = 0 ∧ non-negative weights`,
      where the rate is the Cramér/Legendre transform of the Bernoulli
      loop-presence log-MGF at zero deviation; the zero-rate ⟺
      four-cycle-free equivalence is proven through the Legendre
      evaluation, NOT definitional — review-2026-06-05 D7-EV3 upgrade)
    - Wave 6w.5 `crystalline_eq_quasicrystalline_iff_c1_zero`
      (`Chern crystalline = Chern quasicrystalline ↔ c_1 = 0`).

    The biconditional is falsifiable at three load-bearing axes
    simultaneously: vanishing of the loop-correction rate function,
    factor-weight positivity, and topological triviality. The
    contrapositive
    `not_fourCycleFreeNonneg_or_nonzero_c1_implies_not_simulable` gives
    the screen-failure regime explicitly. **Honesty scope (B-04):** the
    structural side is four-cycle-freeness (a necessary combinatorial
    screen, strictly weaker than a tree), NOT a proof of classical
    simulability; the "simulability ↔ quantum-advantage" reading is the
    physical interpretation carried in the papers/README, not
    established by this statement. -/
theorem analog_hawking_fourCycleFree_demarcation
    {ν α X : Type*}
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α)
    (factorWeight : α → (ν → X) → ℝ) (c0 c1 : ℝ) :
    IsAnalogHawkingFourCycleFreeSimulable G factorWeight c1 ↔
      (loopCorrectionRate G = 0 ∧
        ∀ a y, 0 ≤ factorWeight a y) ∧
      realSpaceChernAt (categoricalChernExpansion c0 c1) 1
        = realSpaceChernAt (categoricalChernExpansion c0 c1) (-1) := by
  unfold IsAnalogHawkingFourCycleFreeSimulable
  rw [fourCycleFree_nonneg_iff_ldp_rate_zero,
      crystalline_eq_quasicrystalline_iff_c1_zero]

/-! ## Substantive companion lemmas -/

/-- **Substantive Companion 1.** The four-cycle-free simulability screen
    is equivalent to a load-bearing factor-graph condition: the factor
    graph is four-cycle-free AND factor weights are non-negative AND the
    Chern coefficient is zero. Substantively unfolds via Wave 6w.2/6w.3
    structural predicates. -/
theorem analog_hawking_simulable_iff_fourCycleFree_and_nonneg_and_c1_zero
    {ν α X : Type*} (G : FactorGraph ν α)
    (factorWeight : α → (ν → X) → ℝ) (c1 : ℝ) :
    IsAnalogHawkingFourCycleFreeSimulable G factorWeight c1 ↔
      IsFourCycleFreeFactorGraph G ∧ (∀ a y, 0 ≤ factorWeight a y) ∧ c1 = 0 := by
  unfold IsAnalogHawkingFourCycleFreeSimulable IsFourCycleFreeNonnegWeighted
  constructor
  · intro ⟨⟨h_c4Free, h_nonneg⟩, h_c1⟩
    exact ⟨h_c4Free, h_nonneg, h_c1⟩
  · intro ⟨h_c4Free, h_nonneg, h_c1⟩
    exact ⟨⟨h_c4Free, h_nonneg⟩, h_c1⟩

/-- **Substantive Companion 2.** Contrapositive of the demarcation: the
    four-cycle-free simulability screen fails when EITHER (a) the
    four-cycle-free / non-negative-weight structural regime fails
    (a 4-cycle is present or some factor weight is negative — the
    strictly-positive-loop-rate side of
    `loopCorrectionRate_pos_of_not_fourCycleFree`), OR (b) the
    categorical Chern coefficient `c_1` is non-zero (topological
    obstruction). This is the structural form of the Tindall-Sels-Aalto
    combined criterion; the "quantum advantage" reading of screen
    failure is the physical interpretation carried in the papers/README,
    not proved here. -/
theorem not_fourCycleFreeNonneg_or_nonzero_c1_implies_not_simulable
    {ν α X : Type*} (G : FactorGraph ν α)
    (factorWeight : α → (ν → X) → ℝ) (c1 : ℝ)
    (h : ¬ IsFourCycleFreeNonnegWeighted G factorWeight ∨ c1 ≠ 0) :
    ¬ IsAnalogHawkingFourCycleFreeSimulable G factorWeight c1 := by
  intro ⟨h_screen, h_c1⟩
  cases h with
  | inl h_notScreen => exact h_notScreen h_screen
  | inr h_nonzero => exact h_nonzero h_c1

-- T4 + T5 deleted 2026-05-26 PM post adversarial-reviewer Stage-13
-- finding 3.1 + 3.2: `:= h` identity-function tautology and
-- `⟨h_bp, h_c1⟩` trivial-constructor tautology on the same
-- definitional unfolding of `IsAnalogHawkingFourCycleFreeSimulable`
-- (which is itself defined as `IsFourCycleFreeNonnegWeighted ∧ c1 = 0`).
-- Downstream consumers project on the predicate directly via `.1` /
-- `.2` without needing the named extraction/constructor wrappers.

/-! ## Genuine tree / BP-convergence layer (remediation B-04, 2026-07-17)

The four-cycle-free demarcation above is the honest *weaker* screen. This
section adds the genuine **tree** layer that the "tree / BP-convergence"
claim actually requires, and wires it end-to-end. The tree predicate is
`SKEFTHawking.BeliefPropagation.IsTreeFactorGraph` — real acyclicity of
the bipartite incidence graph, strictly stronger than four-cycle-freeness.

`analog_hawking_tree_simulable_demarcation` backs the claim end-to-end: a
tree-simulable analog-Hawking system (i) passes the four-cycle-free screen,
(ii) has zero loop-correction rate, and (iii) — equipped with its
topological rank certificate — runs BP to a genuine fixed point in
bounded (diameter) rounds (`bp_converges_on_ranked_acyclic`). The
implication is one-directional (tree ⟹ screen), NOT a biconditional: the
screen is genuinely weaker (a 6-cycle passes it but is not a tree), so no
false equivalence is asserted. The only piece not proved in-tree is the
existence of the rank certificate from `IsTreeFactorGraph` (a finite
subtree-depth construction), documented at `bp_converges_on_ranked_acyclic`. -/

/-- **Genuine tree-simulability predicate.** An analog-Hawking system on a
    factor graph `G` is *tree-simulable* iff (i) `G` is a genuine tree
    (acyclic + connected bipartite incidence graph), (ii) factor weights
    are non-negative, and (iii) the categorical Chern coefficient `c₁`
    vanishes. Strictly stronger than `IsAnalogHawkingFourCycleFreeSimulable`
    — the structural conjunct is real tree-ness, on which BP genuinely
    converges (`bp_converges_on_ranked_acyclic`). -/
def IsAnalogHawkingTreeSimulable
    {ν α X : Type*} (G : FactorGraph ν α)
    (factorWeight : α → (ν → X) → ℝ) (c1 : ℝ) : Prop :=
  IsTreeFactorGraph G ∧ (∀ a y, 0 ≤ factorWeight a y) ∧ c1 = 0

/-- Tree-simulability implies the four-cycle-free simulability screen:
    genuine tree-ness passes the weaker structural screen. (Via
    `IsTreeFactorGraph.isAcyclic` then `isAcyclicFactorGraph_imp_fourCycleFree`.) -/
theorem analog_hawking_tree_simulable_imp_fourCycleFree_simulable
    {ν α X : Type*} (G : FactorGraph ν α)
    (factorWeight : α → (ν → X) → ℝ) (c1 : ℝ)
    (h : IsAnalogHawkingTreeSimulable G factorWeight c1) :
    IsAnalogHawkingFourCycleFreeSimulable G factorWeight c1 := by
  obtain ⟨htree, hnonneg, hc1⟩ := h
  exact ⟨⟨isAcyclicFactorGraph_imp_fourCycleFree G htree.isAcyclic, hnonneg⟩, hc1⟩

/-- Tree-simulability implies zero loop-correction rate: on a genuine tree
    the Cramér loop-correction rate vanishes (through the four-cycle-free
    screen and `fourCycleFree_nonneg_iff_ldp_rate_zero`). -/
theorem analog_hawking_tree_simulable_imp_loopRate_zero
    {ν α X : Type*} [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) (factorWeight : α → (ν → X) → ℝ) (c1 : ℝ)
    (h : IsAnalogHawkingTreeSimulable G factorWeight c1) :
    loopCorrectionRate G = 0 :=
  ((fourCycleFree_nonneg_iff_ldp_rate_zero G factorWeight).mp
    (analog_hawking_tree_simulable_imp_fourCycleFree_simulable G factorWeight c1 h).1).1

/-- **End-to-end tree / BP-convergence demarcation.** A tree-simulable
    analog-Hawking system, equipped with the topological rank certificate
    of its tree, simultaneously: (i) passes the four-cycle-free
    simulability screen, (ii) has zero loop-correction rate, and (iii)
    runs synchronous belief propagation from ANY initial message bundle
    `m` to a genuine `IsBPFixedPoint` after `convergenceHorizon cert.rank`
    (= diameter) sweeps. This is the genuine end-to-end backing of the
    "tree / BP-convergence" claim — the structural conjunct is real
    tree-ness (not four-cycle-freeness) and the convergence is about the
    actual `bpUpdate` dynamics. The rank certificate is the only piece
    supplied as a hypothesis rather than derived from tree-ness (the
    documented `bp_converges_on_ranked_acyclic` gap). -/
theorem analog_hawking_tree_simulable_demarcation
    {ν α X : Type*} [Fintype ν] [Fintype α] [Fintype X]
    [DecidableEq ν] [DecidableEq α] [DecidableEq X]
    (G : FactorGraph ν α) (factorWeight : α → (ν → X) → ℝ) (c1 : ℝ)
    (cert : BPRankCert G)
    (h : IsAnalogHawkingTreeSimulable G factorWeight c1)
    (m : BPMessages ν α G X) :
    IsAnalogHawkingFourCycleFreeSimulable G factorWeight c1
      ∧ loopCorrectionRate G = 0
      ∧ IsBPFixedPoint
          ((fun m' => bpUpdate m' factorWeight)^[convergenceHorizon cert.rank] m)
          factorWeight :=
  ⟨analog_hawking_tree_simulable_imp_fourCycleFree_simulable G factorWeight c1 h,
   analog_hawking_tree_simulable_imp_loopRate_zero G factorWeight c1 h,
   (bp_converges_on_ranked_acyclic cert factorWeight m).2⟩

end SKEFTHawking.AnalogHawkingDemarcation
