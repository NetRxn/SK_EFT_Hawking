/-
# Phase 6n.γ Wave (Glorioso–Liu axiomatic) — Module: DynamicalKMS

Typeclass-parameterized family for the dynamical-KMS Z₂ symmetry,
indexed by UV realization (per Jain–Kovtun JHEP 01 (2024) 162,
arXiv:2309.00511 — the dynamical-KMS condition admits multiple
inequivalent UV realizations fixing the same IR symmetry).

This is the *hard kernel* of the GloriosoLiu axiom skeleton. The
typeclass form mirrors the program's existing methodology of
hypothesis-tracked Props (per `feedback_strengthening_discipline.md`
question 3): every UV-realization choice is explicit, no implicit
choice forces a vacuous theorem.

**Stage 1 status.** Skeleton with sorry stubs. The substantive content
of this module — the `DynamicalKMS_well_posed` theorem under each
UV-realization typeclass instance — is the load-bearing Stage 2-3
deliverable. Phase 1 reconciliation (the 4-of-9 partition) ships in
`Phase1Reconciliation.lean` as a corollary of this module's content
under the first-order projection of `FirstOrderProjection.lean`.

References:
- Jain–Kovtun: arXiv:2309.00511 §3-§4 (UV realizations)
- Glorioso–Liu §II: arXiv:1612.07705
- Phase 6n DR §5 risk axis 2 (UV-ambiguity deeper than typeclass handles)
-/
import SKEFTHawking.GloriosoLiu.Axioms
import Mathlib.Tactic.Basic

namespace SKEFTHawking.GloriosoLiu

/-- A UV realization chooses a specific microscopic completion that
fixes the dynamical-KMS Z₂ at the IR level. Per Jain–Kovtun
arXiv:2309.00511, multiple inequivalent UV realizations exist; this
typeclass exposes the choice explicitly so that downstream theorems
carry the realization as a parameter. -/
class UVRealization (M : SpacetimeManifold) (Φ : ContourField M) where
  /-- The UV-realization tag (Stage 1 placeholder; Stage 2-3 unfolds
  to a concrete UV-completion type). -/
  tag : Unit := ()

/-- The Glorioso–Liu / CGL realization (the canonical choice for
dissipative hydrodynamics; Crossley–Glorioso–Liu I+II). -/
instance gloriosoLiuRealization (M : SpacetimeManifold) (Φ : ContourField M) :
    UVRealization M Φ := ⟨()⟩

/-- The Jain–Kovtun causal-stable realization (alternative UV
completion preserving causality + stability bounds; arXiv:2309.00511). -/
def jainKovtunRealization (M : SpacetimeManifold) (Φ : ContourField M) :
    UVRealization M Φ := ⟨()⟩

/--
**Dynamical KMS predicate parameterized over UV-realization.**

The dynamical-KMS Z₂ symmetry depends on the UV-realization choice.
This predicate makes the dependence explicit, so any downstream theorem
invoking dynamical KMS must declare which realization it works in.

PROVIDED SOLUTION (Stage 2-3):
Stage 2-3 unfolds to: ∃ Θ : involution, S ∘ Θ = S where Θ acts as
complexified time-reversal at inverse temperature β. The realization
typeclass instance fixes the precise form of Θ (e.g., for
gloriosoLiuRealization, Θ is the CGL II classical-limit involution).
-/
def DynamicalKMSAt (M : SpacetimeManifold) (Φ : ContourField M) (β : ℝ)
    [_uv : UVRealization M Φ] : Prop :=
  0 < β

/--
**The dynamical-KMS predicate is preserved under realization swap when
both realizations agree at the IR level.**

This is the load-bearing structural theorem that justifies the
typeclass parameterization: although different UV realizations exist,
they agree on the IR-level dynamical-KMS content. This is what allows
downstream theorems to use *any* realization without committing to a
specific UV choice (per Jain–Kovtun §5 IR-equivalence).

PROVIDED SOLUTION (downstream Aristotle hint):
The proof reduces to showing both realizations admit the same IR
involution Θ_IR. For Stage 1, both placeholder realizations are
trivially equal at the IR level (both reduce to `0 < β`).
-/
theorem DynamicalKMS_realization_invariant
    (M : SpacetimeManifold) (Φ : ContourField M) (β : ℝ) (hβ : 0 < β)
    [uv1 : UVRealization M Φ] [uv2 : UVRealization M Φ] :
    @DynamicalKMSAt M Φ β uv1 ↔ @DynamicalKMSAt M Φ β uv2 := by
  sorry

end SKEFTHawking.GloriosoLiu
