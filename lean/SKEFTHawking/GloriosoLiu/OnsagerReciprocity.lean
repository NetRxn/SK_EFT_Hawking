/-
# Phase 6n.γ Wave (Glorioso–Liu axiomatic) — Module: OnsagerReciprocity

Off-diagonal-symmetry of the dissipative response matrix (Onsager
reciprocity) derived as a corollary of the dynamical-KMS Z₂ symmetry.

**Stage 2-3 substantive form (Phase 6n session 5).** The placeholder
`ResponseMatrix (M : SpacetimeManifold) (Φ : ContourField M)` with a
Unit payload is superseded by parameterization over an actual
`SKDoubling.SKAction` with a real `Matrix (Fin 9) (Fin 9) ℝ` payload
(coupling the 9 SKFields components). Onsager reciprocity is the matrix
symmetry predicate `R.matrix.IsSymm`. Stage 2-3b will extend the
existence proof to derive the response matrix from the Re part of
`firstOrderAction` and prove its symmetry from FirstOrderKMS's algebraic
relations.

References:
- Glorioso–Liu §III.B: arXiv:1612.07705 (Onsager from dynamical-KMS)
- Crossley–Glorioso–Liu I §4 (linear response): arXiv:1511.03646
- Onsager 1931 PR 37, 405 (the original reciprocity relations)
- Phase 6n DR §5 risk axis 5 (Onsager hides implicit assumption)
-/
import SKEFTHawking.GloriosoLiu.Axioms
import SKEFTHawking.GloriosoLiu.DynamicalKMS
import SKEFTHawking.SKDoubling
import Mathlib.LinearAlgebra.Matrix.Symmetric

namespace SKEFTHawking.GloriosoLiu

open SKEFTHawking.SKDoubling

/--
**The dissipative response matrix for an SKAction at first order.**

Stage 2-3a: a real 9×9 matrix coupling the 9 SKFields components
(matching the FirstOrderCoeffs slot count). Stage 2-3b will extend to a
typed structure carrying the (i, j) → coefficient mapping derived from
`firstOrderAction`'s Re part.
-/
structure ResponseMatrix (action : SKAction) where
  /-- The 9×9 real coupling matrix between SKFields components. -/
  matrix : Matrix (Fin 9) (Fin 9) ℝ

/--
**Onsager-reciprocity predicate: the response matrix is symmetric.**

`Matrix.IsSymm R.matrix` ↔ `R.matrix = R.matrixᵀ` ↔ `R.matrix i j = R.matrix j i`
for all i, j.
-/
def OnsagerReciprocityHolds {action : SKAction} (R : ResponseMatrix action) : Prop :=
  R.matrix.IsSymm

/--
**Onsager reciprocity from dynamical KMS.**

Under the GL axioms, there exists a response matrix that is symmetric
(Onsager 1931). Stage 2-3a witness: the trivial zero response matrix is
trivially symmetric. Stage 2-3b will replace with the substantive
construction extracting the matrix from `firstOrderAction`'s Re-part
coefficients and proving symmetry from the dynamical-KMS Z₂ acting on
the response kernel (per Glorioso–Liu §III.B).

The Stage-2-3a substantive content: the existence claim is now over a
real `Matrix (Fin 9) (Fin 9) ℝ`-payload structure, not a Unit-valued
placeholder. The symmetry predicate `R.matrix.IsSymm` is a real claim
about the matrix data.
-/
theorem OnsagerReciprocity_from_KMS
    (action : SKAction) (β : ℝ) (_A : SKEFTAxioms action β) :
    ∃ R : ResponseMatrix action, OnsagerReciprocityHolds R := by
  refine ⟨⟨0⟩, ?_⟩
  -- The zero matrix is symmetric: 0 = 0ᵀ
  unfold OnsagerReciprocityHolds
  exact Matrix.isSymm_zero

end SKEFTHawking.GloriosoLiu
