/-
# Phase 6n.γ Wave (Glorioso–Liu axiomatic) — Module: EntropyCurrent

The Noether-style entropy current `J^μ_S` constructed from the
dynamical-KMS Z₂ symmetry, per Glorioso–Liu (arXiv:1612.07705 Prop. III.1).

**Stage 1 status.** Skeleton with sorry stubs. The `entropy_current_exists`
theorem is the Stage 2-3 deliverable (existence + Noether-construction
identification). The substantive divergence statement
`∂_μ J^μ_S ≥ 0` is in `LocalSecondLaw.lean`.

References:
- Glorioso–Liu §III: arXiv:1612.07705
- Crossley–Glorioso–Liu II Theorem 3: arXiv:1701.07817
- Liu–Glorioso TASI §5: arXiv:1805.09331
-/
import SKEFTHawking.GloriosoLiu.Axioms
import SKEFTHawking.GloriosoLiu.DynamicalKMS
import Mathlib.Tactic.Basic

namespace SKEFTHawking.GloriosoLiu

/-- Abstract entropy-current placeholder. Stage 2-3 replaces with the
program's Lorentzian-vector-field machinery on the spacetime
manifold. -/
structure EntropyCurrent (M : SpacetimeManifold) (Φ : ContourField M) where
  /-- Stage 1 placeholder; Stage 2-3 unfolds to a vector field. -/
  placeholder : Unit := ()

/-- Placeholder for the standard thermodynamic entropy current at zeroth
order (the equilibrium entropy density × velocity). -/
def thermodynamicEntropyCurrent {M : SpacetimeManifold} (Φ : ContourField M) :
    EntropyCurrent M Φ := ⟨()⟩

/--
**Existence of the Noether-style entropy current under the GL axioms.**

Per Glorioso–Liu Prop. III.1: under the six SKEFTAxioms, there exists
an entropy current `J^μ_S`, constructed Noether-style from the
dynamical-KMS Z₂ symmetry, such that at zeroth order in derivatives
`J^μ_S` reduces to the standard thermodynamic entropy current.

PROVIDED SOLUTION (Stage 2-3):
The Noether construction takes the dynamical-KMS Z₂ involution Θ and
extracts the conserved current via the standard Noether procedure on
the SK-EFT effective action. At zeroth order, the construction reduces
to the equilibrium s · u^μ form (where s is entropy density, u^μ is
the hydrodynamic velocity).
-/
theorem entropy_current_exists
    {M : SpacetimeManifold} {Φ : ContourField M} {β : ℝ}
    (_A : SKEFTAxioms M Φ β) :
    ∃ J : EntropyCurrent M Φ, J = thermodynamicEntropyCurrent Φ := by
  sorry

end SKEFTHawking.GloriosoLiu
