/-
# Phase 6n.γ Wave (Glorioso–Liu axiomatic) — Module: FirstOrderProjection

Recovers the program's existing `SKEFTHawking.SKDoubling.FirstOrderKMS`
content (Phase 1, Aristotle run 270e77a0) as the *first-order
projection* of the GloriosoLiu six-axiom skeleton.

**Stage 2-3 substantive form (Phase 6n session 5).** The placeholder
mirror struct `FirstOrderProjection` (which duplicated `FirstOrderCoeffs`
verbatim) is dropped in favor of *direct use* of `SKDoubling.FirstOrderCoeffs`.
The projection theorem is now a one-line call to the LE axiom field of
`SKEFTAxioms` — `A.local_equilibrium` is exactly the existential claim
"∃ FirstOrderCoeffs c such that the action's Lagrangian equals
firstOrderAction(c)" — which was the placeholder-struct's purpose.

The cross-bridge to existing program content is now load-bearing
(the LE axiom literally projects to FirstOrderCoeffs). This is the
load-bearing structural enabler for the I1 worked-case reframing and
6n.ζ Sakharov ↔ horizon-Crooks reformulation downstream.

References:
- Phase 1 `FirstOrderKMS`: lean/SKEFTHawking/SKDoubling.lean lines 367-379
- Aristotle run 270e77a0 (Phase 1 productive-value disproof)
- Phase 6n DR §5: "the 4 components Aristotle confirmed are exactly the
  ones derivable from dynamical KMS at first order"
- `Phase1Reconciliation.lean` (Stage 2-3 partition recovery, Session 5)
-/
import SKEFTHawking.GloriosoLiu.Axioms
import SKEFTHawking.GloriosoLiu.DynamicalKMS
import SKEFTHawking.GloriosoLiu.LocalSecondLaw
import SKEFTHawking.SKDoubling
import Mathlib.Tactic.Basic

namespace SKEFTHawking.GloriosoLiu

open SKEFTHawking.SKDoubling

/--
**The first-order projection of GL axioms exists.**

Substantive content: under the SKEFTAxioms (specifically the LE axiom
`local_equilibrium`), there exist `FirstOrderCoeffs` whose
`firstOrderAction` reproduces the action's Lagrangian on every
SKFields configuration. This is exactly the statement of `A.local_equilibrium`,
which is now a load-bearing axiom carrying the polynomial-form witness
(not a Unit placeholder).
-/
theorem FirstOrderProjection_exists
    (action : SKAction) (β : ℝ) (A : SKEFTAxioms action β) :
    ∃ c : FirstOrderCoeffs,
      ∀ f : SKFields, action.lagrangian f = (firstOrderAction c).lagrangian f :=
  A.local_equilibrium

/--
**The all-zero `FirstOrderCoeffs` satisfies `FirstOrderKMS` at any
positive temperature.**

Substantive Stage-2-3a witness: the projected coefficients for the
zero action are all zero, and the all-zero `FirstOrderCoeffs` trivially
satisfies all 7 algebraic-FDR relations of `FirstOrderKMS` (r3=r4=r5=r6=0
by reflexivity, fdr_i1: 0·β = -0, fdr_i2: 0·β = 0+0, i3=0).

This is the projection witness for the zero-action well-posedness path:
when the GL axioms hold for the zero action via `SKEFTAxioms_zero_action`,
the projected `FirstOrderCoeffs` is the all-zero one, and it satisfies
`FirstOrderKMS` automatically.
-/
theorem FirstOrderProjection_zeroCoeffs_satisfies_KMS (β : ℝ) :
    FirstOrderKMS ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩ β := by
  refine
    { r3_zero := rfl, r4_zero := rfl, r5_zero := rfl, r6_zero := rfl
      fdr_i1 := ?_, fdr_i2 := ?_, i3_zero := rfl }
  · -- 0 * β = -0
    simp
  · -- 0 * β = 0 + 0
    simp

/--
**Combined: the GL axioms project to a FirstOrderCoeffs, AND for the
zero-action witness specifically, that projection satisfies `FirstOrderKMS`.**

Specialization of `FirstOrderProjection_exists` for the zero action:
the well-posedness witness `SKEFTAxioms_zero_action` projects to the
all-zero coefficients, which satisfy `FirstOrderKMS β` per the previous
theorem. This is the cross-bridge-load-bearing concrete witness for the
projection chain GL-axioms → FirstOrderCoeffs → FirstOrderKMS → 4-of-9
partition recovery (in `Phase1Reconciliation.lean`).
-/
theorem FirstOrderProjection_zero_action (β : ℝ) :
    ∃ c : FirstOrderCoeffs,
      (∀ f : SKFields, zeroAction.lagrangian f = (firstOrderAction c).lagrangian f)
      ∧ FirstOrderKMS c β := by
  refine ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ?_, ?_⟩
  · intro f; simp [zeroAction, firstOrderAction]
  · exact FirstOrderProjection_zeroCoeffs_satisfies_KMS β

end SKEFTHawking.GloriosoLiu
