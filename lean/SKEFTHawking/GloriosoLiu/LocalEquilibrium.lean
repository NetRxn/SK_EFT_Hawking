/-
# Phase 6n.γ Wave (Glorioso–Liu axiomatic) — Module: LocalEquilibrium

Local equilibrium / slow-mode infrastructure for the LE axiom of the
GloriosoLiu six-axiom skeleton.

**Stage 2-3 substantive form (Phase 6n session 5).** The placeholder
`LocalEquilibriumAt (Φ : ContourField M) (pattern) := pattern.currentCount > 0`
is superseded by parameterization over an actual `SKDoubling.SKAction`,
with the LE predicate substantively tied to the polynomial-action shape
via `hasLocalEquilibrium` (existence of `FirstOrderCoeffs` reproducing
the action's Lagrangian).

References:
- Glorioso–Liu §II axiom (LE): arXiv:1612.07705
- Crossley–Glorioso–Liu I §3: arXiv:1511.03646 (hydrodynamic modes)
- Phase 6n DR §5 risk axis 3 (LE axiom too vague — predicate-design iteration)
-/
import SKEFTHawking.GloriosoLiu.Axioms
import SKEFTHawking.SKDoubling
import Mathlib.Tactic.Basic

namespace SKEFTHawking.GloriosoLiu

open SKEFTHawking.SKDoubling

/-- The conservation pattern parameterizes the LE axiom. Different
hydrodynamic theories (energy conservation only, energy+momentum,
energy+momentum+charge, etc.) instantiate different LE predicates. -/
inductive ConservationPattern
  | energy
  | energyMomentum
  | energyMomentumCharge
  | custom (n : ℕ)

/-- The conserved-current count for each pattern. -/
def ConservationPattern.currentCount : ConservationPattern → ℕ
  | .energy => 1
  | .energyMomentum => 5  -- 1 energy + 4 momentum
  | .energyMomentumCharge => 6  -- + 1 charge
  | .custom n => n

/--
**Local equilibrium predicate for a SKDoubling.SKAction at a given
conservation pattern.**

Substantive content: (i) the action admits a polynomial first-order
representation (via `hasLocalEquilibrium`); AND (ii) the conservation
pattern carries at least one conserved current. Both clauses are
load-bearing — (i) ties LE to the actual SKDoubling polynomial-action
machinery, (ii) excludes the empty `custom 0` pattern.
-/
def LocalEquilibriumAt (action : SKAction) (pattern : ConservationPattern) : Prop :=
  hasLocalEquilibrium action ∧ pattern.currentCount > 0

/--
**Substantive: the zero action has a polynomial first-order representation.**

This is the load-bearing content underlying the LE axiom for the zero-action
witness chain: there exist `FirstOrderCoeffs` (the all-zero ones) whose
`firstOrderAction` reproduces `zeroAction.lagrangian` on every `SKFields`
configuration. No hypothesis about the conservation pattern is required —
the polynomial-form claim is independent of the pattern's current count.

This theorem is what makes `LocalEquilibrium_zero_action` non-vacuous;
the wrapper below pairs it with the pattern-non-vacuity hypothesis. -/
theorem hasLocalEquilibrium_zero_action : hasLocalEquilibrium zeroAction := by
  refine ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ?_⟩
  intro f
  simp [zeroAction, firstOrderAction]

/--
**LE wrapper for the zero action under any nontrivial pattern.**

API-shaped wrapper combining the substantive polynomial-form witness
(`hasLocalEquilibrium_zero_action`) with the pattern-non-vacuity
hypothesis. The substantive content lives in
`hasLocalEquilibrium_zero_action`; this theorem just bundles the two
clauses of `LocalEquilibriumAt` together.

Stage-2-3a refactor (Phase 6n Wave 2a follow-up, 2026-05-05): split off
the substantive polynomial-form witness as `hasLocalEquilibrium_zero_action`
to satisfy the preemptive-strengthening checklist (P2: drop the conjunct
that's just a hypothesis extraction). -/
theorem LocalEquilibrium_zero_action
    (pattern : ConservationPattern) (h : pattern.currentCount > 0) :
    LocalEquilibriumAt zeroAction pattern :=
  ⟨hasLocalEquilibrium_zero_action, h⟩

end SKEFTHawking.GloriosoLiu
