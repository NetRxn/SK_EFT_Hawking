/-
# Phase 6n.γ Wave (Glorioso–Liu axiomatic) — Module: EntropyCurrent

The Noether-style entropy current `J^μ_S` constructed from the
dynamical-KMS Z₂ symmetry, per Glorioso–Liu (arXiv:1612.07705 Prop. III.1).

**Stage 2-3 substantive form (Phase 6n session 5).** The
`EntropyCurrent (M : SpacetimeManifold) (Φ : ContourField M)` placeholder
with a `Unit` payload is superseded by parameterization over an actual
`SKDoubling.SKAction` and a real `density : SKFields → ℝ` field. The
existence theorem now invokes the Stage-2-3 substantive `SKEFTAxioms`
(parameterized over a SKAction).

References:
- Glorioso–Liu §III: arXiv:1612.07705
- Crossley–Glorioso–Liu II Theorem 3: arXiv:1701.07817
- Liu–Glorioso TASI §5: arXiv:1805.09331
-/
import SKEFTHawking.GloriosoLiu.Axioms
import SKEFTHawking.GloriosoLiu.DynamicalKMS
import SKEFTHawking.SKDoubling
import Mathlib.Tactic.Basic

namespace SKEFTHawking.GloriosoLiu

open SKEFTHawking.SKDoubling

/--
**An entropy current for a SKDoubling.SKAction is a real-valued density
on `SKFields`.**

Stage 2-3a layer: carries the local entropy density only. Stage 2-3b
will extend to a Lorentzian 4-current (entropy density + 3-current
components) once the Lorentzian-vector-bundle infrastructure is wired up.
The Stage-2-3a form is sufficient for the local second law (which only
uses the divergence at a SKFields point, not the full 4-current shape).
-/
structure EntropyCurrent (action : SKAction) where
  /-- The local entropy density as a function of SKFields. -/
  density : SKFields → ℝ

/-- The trivial zero entropy current for any action. Used as the
substantive existence witness for `entropy_current_exists`. -/
def zeroEntropyCurrent (action : SKAction) : EntropyCurrent action where
  density := fun _ => 0

/-- The zero entropy current's density vanishes pointwise on `SKFields`. -/
@[simp]
theorem zeroEntropyCurrent_density (action : SKAction) (f : SKFields) :
    (zeroEntropyCurrent action).density f = 0 := rfl

/--
**Existence of a Noether-style entropy current under the GL axioms.**

Per Glorioso–Liu Prop. III.1: under the six SKEFTAxioms, there exists
an entropy current `J^μ_S` constructed Noether-style from the
dynamical-KMS Z₂ symmetry. Stage 2-3a witnesses existence via the
trivial `zeroEntropyCurrent` (substantively typed against the action,
not Unit-valued). **Stage 2-3b (intentional placeholder) will extend
to the substantive Noether construction extracting a non-trivial density
from the dynamical-KMS Z₂ involution; the `_A : SKEFTAxioms` hypothesis
becomes load-bearing at that point** (the Noether density is constructed
from `A.dynamical_KMS`'s coefficient witness). The current trivial form
is held intentionally as a Stage-2-3b fill-in target — see
`SORRY_GAPS["entropy_current_exists"]` in `aristotle_interface.py`.
-/
theorem entropy_current_exists
    (action : SKAction) (β : ℝ) (_A : SKEFTAxioms action β) :
    ∃ J : EntropyCurrent action, J = zeroEntropyCurrent action :=
  ⟨zeroEntropyCurrent action, rfl⟩

end SKEFTHawking.GloriosoLiu
