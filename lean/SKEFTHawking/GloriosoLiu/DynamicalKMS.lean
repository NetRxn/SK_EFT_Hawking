/-
# Phase 6n.γ Wave (Glorioso–Liu axiomatic) — Module: DynamicalKMS

Typeclass-parameterized family for the dynamical-KMS Z₂ symmetry,
indexed by UV realization (per Jain–Kovtun JHEP 01 (2024) 162,
arXiv:2309.00511 — the dynamical-KMS condition admits multiple
inequivalent UV realizations fixing the same IR symmetry).

**Stage 2-3 substantive form (Phase 6n session 5).** The placeholder
`UVRealization` parameterized over abstract (M, Φ) is superseded by
parameterization over (`SKDoubling.SKAction`, β). The realization
typeclass now carries an *actual* `SKDoubling.KMSSymmetry` witness,
not just a Unit tag. The IR-equivalence theorem is correspondingly
substantive: any two realizations for the same (action, β) yield the
same dynamical-KMS predicate (`Nonempty (KMSSymmetry action β)`).

References:
- Jain–Kovtun: arXiv:2309.00511 §3-§4 (UV realizations)
- Glorioso–Liu §II: arXiv:1612.07705
- Phase 6n DR §5 risk axis 2 (UV-ambiguity deeper than typeclass handles)
-/
import SKEFTHawking.GloriosoLiu.Axioms
import SKEFTHawking.SKDoubling
import Mathlib.Tactic.Basic

namespace SKEFTHawking.GloriosoLiu

open SKEFTHawking.SKDoubling

/-- A UV realization for a given (action, β) is a *witness* of the
`KMSSymmetry` structure. Per Jain–Kovtun arXiv:2309.00511, multiple
inequivalent UV realizations can coexist for the same IR-level
dynamical-KMS predicate; this typeclass exposes the choice explicitly so
that downstream theorems carry the realization as a parameter. -/
class UVRealization (action : SKAction) (β : ℝ) where
  /-- The witness `KMSSymmetry` instance for this realization. -/
  witness : KMSSymmetry action β

/-- **The Glorioso–Liu / CGL realization for the zero action** (canonical
choice for the structural well-posedness witness; the canonical KMS
transform `kmsCanonicalTransform β` leaves the zero action invariant
trivially). -/
instance gloriosoLiuRealizationForZero (β : ℝ) :
    UVRealization zeroAction β := ⟨kmsForZeroAction β⟩

/--
**Dynamical KMS predicate parameterized over UV-realization.**

With a UVRealization in scope (i.e., a concrete KMSSymmetry witness),
the dynamical-KMS predicate reduces to the existence of *any*
KMSSymmetry instance for this (action, β). The typeclass realization
provides such an instance by construction.

**Stage 2-3b (intentional placeholder).** The current Stage 2-3a form
makes `DynamicalKMSAt` independent of the typeclass parameter at the
IR level (it discards the realization tag). The Stage 2-3b refactor
will replace this with a realization-dependent form (e.g., capturing
the specific kms_transform shape or the correlator-level realization
data), at which point `DynamicalKMS_realization_invariant` becomes
substantive (Jain–Kovtun §5 IR-equivalence).
-/
def DynamicalKMSAt (action : SKAction) (β : ℝ)
    [_uv : UVRealization action β] : Prop :=
  Nonempty (KMSSymmetry action β)

/--
**The dynamical-KMS predicate is realization-invariant.**

Any two UV realizations for the same (action, β) agree on the dynamical-KMS
predicate. This is the load-bearing structural theorem: although different
UV realizations carry distinct concrete KMSSymmetry witnesses, they all
project onto the same IR-level `Nonempty (KMSSymmetry action β)` predicate.
This is what allows downstream theorems to use *any* realization without
committing to a specific UV choice (per Jain–Kovtun §5 IR-equivalence).

**Stage-2-3a status: structural identity (`Iff.rfl`).** Substantive at
Stage 2-3b once `DynamicalKMSAt` is refactored to depend on the
realization tag; until then, this theorem documents the intended
realization-invariance contract and serves as the Stage-2-3b fill-in
target. -/
theorem DynamicalKMS_realization_invariant
    (action : SKAction) (β : ℝ)
    [uv1 : UVRealization action β] [uv2 : UVRealization action β] :
    @DynamicalKMSAt action β uv1 ↔ @DynamicalKMSAt action β uv2 :=
  Iff.rfl

/-- **The dynamical-KMS predicate is non-vacuous given a UV realization.**

The realization itself is a witness, so the Nonempty claim is
discharged trivially via the typeclass instance. -/
theorem DynamicalKMSAt_holds (action : SKAction) (β : ℝ)
    [uv : UVRealization action β] :
    @DynamicalKMSAt action β uv :=
  ⟨uv.witness⟩

/--
**Additive cross-module bridge (Phase 6n Wave 2a follow-up, 2026-05-05):
a UV realization implies the strict-invariance dynamical-KMS predicate
from `Axioms.lean`.**

Substantive content: the typeclass field is precisely a `KMSSymmetry`
witness, which exists ↔ `hasDynamicalKMS_strict action β` holds. This
theorem makes the connection from the typeclass-based UVRealization
infrastructure (this module) to the predicate-based axiom infrastructure
(`Axioms.lean`) explicit, satisfying the P6 cross-module bridge integrity
discipline.

NOTE on substantive scope: this bridge connects to the **strict-invariance**
form `hasDynamicalKMS_strict`, not the substantive algebraic-FDR form
`hasDynamicalKMS_algebraic`. Per the KMS framework finding
(`temporary/working-docs/phase6n/6n_gamma_kms_framework_finding.md`),
no general bridge from UVRealization (a strict-invariance witness) to
`hasDynamicalKMS_algebraic` exists — the canonical KMS shift is
generically not a strict invariance for non-trivial dissipative actions.
For the algebraic-FDR form, the action must be polynomial-form-witnessed
and the FDR must be verified at the coefficient level (see
`SKEFTAxioms_for_dissipative` in `Axioms.lean`). -/
theorem hasDynamicalKMS_strict_of_realization
    (action : SKAction) (β : ℝ) [uv : UVRealization action β] :
    hasDynamicalKMS_strict action β :=
  ⟨uv.witness⟩

end SKEFTHawking.GloriosoLiu
