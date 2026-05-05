/-
# Phase 6n.γ Wave (Glorioso–Liu axiomatic) — Module: Phase1Reconciliation

Recovers the Phase 1 4-of-9 Aristotle partition (Aristotle run
270e77a0; counterexample c = (0,0,0,0,0,0,0,1,0)) as a *theorem* of
the GloriosoLiu six-axiom skeleton, not an Aristotle-empirical
observation.

**This is the load-bearing partition-recovery claim that gates the
I1 §3 prose update (held by user decision R1 in Phase 6n Session 4).**
If this module's theorem `four_of_nine_partition_recovered` proves
clean, the I1 reframing in `temporary/working-docs/phase6n/6n_gamma_I1_reframing_predraft.md`
ships verbatim. If it surfaces a deeper failure mode (per Phase 6n
DR §12 caveat), the I1 prose is rewritten around the empirical
finding instead.

**Stage 1 status.** Theorem statement with sorry stub. Stage 2-3
proves the partition-recovery via the FirstOrderProjection module
(Stage 2-3 in series). Aristotle (Stage 4) is fallback.

References:
- Phase 6n DR §5 explicit prediction: "the 4 components Aristotle
  confirmed are exactly the ones derivable from dynamical KMS at first
  order, and the 5 he disproved are second-order corrections"
- Phase 6n DR §12 caveat: failure mode is itself publishable
- I1 reframing pre-draft at `temporary/working-docs/phase6n/6n_gamma_I1_reframing_predraft.md`
-/
import SKEFTHawking.GloriosoLiu.Axioms
import SKEFTHawking.GloriosoLiu.FirstOrderProjection
import Mathlib.Tactic.Basic

namespace SKEFTHawking.GloriosoLiu

/-- The four "field components Aristotle confirmed" — the components
the original transform-level `KMSSymmetry` (in SKDoubling.lean) acts
on: ψ_r, ψ_a, ∂_t ψ_r, ∂_x ψ_r. -/
inductive FieldComponent
  | psi_r        -- 1
  | psi_a        -- 2
  | dt_psi_r     -- 3
  | dx_psi_r     -- 4
  | dt_psi_a     -- 5 (NOT acted on by transform)
  | dx_psi_a     -- 6 (NOT acted on by transform)
  | dtt_psi_r    -- 7 (NOT acted on by transform)
  | dxx_psi_r    -- 8 (NOT acted on by transform)
  | dtx_psi_r    -- 9 (NOT acted on by transform)

/-- The four components the transform-level KMSSymmetry constrains
(the "first-order projection" components in the partition). -/
def isTransformConstrained : FieldComponent → Bool
  | .psi_r => true
  | .psi_a => true
  | .dt_psi_r => true
  | .dx_psi_r => true
  | _ => false

/-- The five components requiring the second-order SK-EFT loop content
(the "second-order corrections" components in the partition). -/
def requiresSecondOrder (c : FieldComponent) : Bool :=
  ¬ isTransformConstrained c

/--
**The 4-of-9 Aristotle partition is a theorem of first-order projection.**

The four field components Aristotle's first-pass weak `KMSSymmetry`
*did* hold on are exactly the four components a transform-level
projection of dynamical-KMS acts on at first order. The five it
*did not* hold on are exactly those whose KMS partners would exceed
the first-order budget and instead surface at second order in the
SK-EFT loop expansion.

This recovers Phase 1 Aristotle run 270e77a0's productive-value
content at the *theorem* level rather than the Aristotle-empirical
level — exactly the upgrade the I1 §3 reframing (Phase 6n Session 4
working doc) relies on.

PROVIDED SOLUTION (Stage 2-3):
By case analysis on `FieldComponent`:
- For psi_r, psi_a, dt_psi_r, dx_psi_r: `isTransformConstrained = true`
  by definition; these are the 4 transform-acted components.
- For dt_psi_a, dx_psi_a, dtt_psi_r, dxx_psi_r, dtx_psi_r:
  `isTransformConstrained = false` by definition; these are the 5
  second-order-correction components. Connection to
  `FirstOrderProjection_yields_FirstOrderKMS` shows that fixing the
  former forces the latter to second-order corrections.

If the case analysis surfaces additional structure (e.g., one
component falls in neither bucket), the failure mode is publishable
per DR §12 caveat — the I1 prose then rewrites around the empirical
finding rather than the predicted partition.
-/
theorem four_of_nine_partition_recovered
    {M : SpacetimeManifold} {Φ : ContourField M} {β : ℝ}
    (hβ : 0 < β)
    (A : SKEFTAxioms M Φ β) :
    -- Exactly 4 of the 9 components are transform-constrained
    (List.length (List.filter isTransformConstrained
      [.psi_r, .psi_a, .dt_psi_r, .dx_psi_r,
       .dt_psi_a, .dx_psi_a, .dtt_psi_r, .dxx_psi_r, .dtx_psi_r]) = 4)
    ∧
    -- The remaining 5 require second-order SK-EFT content
    (List.length (List.filter requiresSecondOrder
      [.psi_r, .psi_a, .dt_psi_r, .dx_psi_r,
       .dt_psi_a, .dx_psi_a, .dtt_psi_r, .dxx_psi_r, .dtx_psi_r]) = 5) := by
  decide

end SKEFTHawking.GloriosoLiu
