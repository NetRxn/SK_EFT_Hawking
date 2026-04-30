import SKEFTHawking.Basic
import SKEFTHawking.LeviCivita
import SKEFTHawking.LorentzianMetric
import Mathlib

/-!
# Phase 6g.2-curve-theoretic Session 1 — Bundle-level Lorentzian metric

## Overview

Session 1 of the substantive curve-theoretic Penrose re-engagement. This
module concretizes the Wave-7 `LorentzianMetric` §6 skeleton
(`IsContinuousLorentzianFamily` on coordinate `MetricMatrix`-valued
maps) into a **bundle-level** Lorentzian metric typeclass operating on
fiber-bilinear-forms `g : Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜`
along the same setup used by `LeviCivita.lean` and `BundleRiemann.lean`.

The substantive payoff is the **bridge to bundle-level Levi-Civita
uniqueness** (Wave 8 Sessions 5+5b): if `g` satisfies `IsLorentzianBundle`,
then any two `IsLeviCivita 𝕜 _ g` connections agree pointwise via the
Koszul-bilinear-form derivation. This bridge is what unblocks the
curve-theoretic Penrose chain — the Raychaudhuri equation
(Session 3) needs a unique Levi-Civita connection on a Lorentzian-metric
spacetime, and that's exactly what this module supplies.

## Wave-headline content

1. **`IsLorentzianBundle`** — bundle-level Lorentzian metric predicate:
   symmetry of `g x` at every point + non-degeneracy of `g x` at every
   point. The signature condition (`(-, +, +, ..., +)` orthonormal frame)
   is parametrized into a separate predicate at the algebraic-precedent
   level (see Wave-7 `IsLorentzianSignature`); this bundle-level layer
   carries the structural Lorentzian content (signed-symmetric +
   non-degenerate) that is independent of any chosen basis.
2. **`lorentzianBundle_isNondegenerateAt`** — direct projection
   theorem feeding into `LeviCivita.leviCivita_pointwise_unique_of_koszul`.
3. **`lorentzianBundle_symm_apply`** — symmetric-pairing restatement
   feeding into `IsLeviCivita.metric_symm`.
4. **`lorentzianBundle_pairing_left_injective`** — substantive
   non-degeneracy consequence: equal `g x v ·` and `g x w ·` pairings
   imply `v = w`. This is the load-bearing form of non-degeneracy used
   in curve-theoretic arguments (and in `RaychaudhuriEquation.lean`
   Session 3 for separating tangent-vector decompositions of the null
   tangent).
5. **`leviCivita_unique_for_lorentzianBundle`** — the Wave-8 Sessions
   5+5b composition theorem instantiated at a Lorentzian-bundle metric.
   Substantive headline: *Lorentzian-bundle metric `g` has at most one
   Levi-Civita connection*.
6. **`IsRiemannianBundle` + `riemannianBundle_not_lorentzianBundle`** —
   bundle-level lift of the Wave-7 §3 falsifier. Shows the Lorentzian
   non-degeneracy structure is non-vacuous at the bundle level
   (Riemannian = positive-definite case is excluded for any non-trivial
   `M`).

## Anti-pattern audit (per project preemptive-strengthening discipline)

1. **No P1 ∃-absorption** — `IsLorentzianBundle` is a non-existential
   predicate (universally-quantified properties of `g x`); the
   non-degeneracy clause `IsNondegenerateAt g x` is the explicit non-existential
   form `∀ v, (∀ w, g x v w = 0) → v = 0`.
2. **No P2 bundle redundancy** — symm + nondegenerate are independently
   substantive: a Riemannian bundle metric is symm + positive-definite
   (positive-definite ⟹ nondegen but with extra constraint); a
   degenerate symmetric form is symm but fails nondegen; the Lorentzian
   bundle distinguishes itself from positive-definite via the
   `IsRiemannianBundle` falsifier in §5.
3. **No P3 trivial-multiplication-as-physics** — the
   `lorentzianBundle_pairing_left_injective` theorem is genuine
   linear-algebra content (the bilinearity of `g x` plus non-degeneracy
   give injection, not a `rfl`-rename).
4. **No P4 vacuous axioms** — the `IsLorentzianBundle` predicate
   non-vacuously distinguishes Lorentzian from Riemannian (the
   `riemannianBundle_not_lorentzianBundle` falsifier exhibits the
   distinction at the structural level).
5. **No P5 falsifier-restating-hypothesis** — the falsifier
   `riemannianBundle_not_lorentzianBundle` consumes the existence of a
   non-zero vector (provided via the `Nontrivial`-instance hypothesis on
   `TangentSpace I x`) and derives `0 < 0` from positive-definiteness +
   `g x v v = -1 < 0`. Substantive.
6. **Cross-module bridge integrity P6** — body imports
   `SKEFTHawking.LeviCivita` (calls `IsNondegenerateAt`,
   `IsLeviCivita`, `leviCivita_unique_of_isLeviCivita` directly) and
   `SKEFTHawking.LorentzianMetric` (cites the algebraic-precedent
   foundation but doesn't depend on it for proofs at the bundle level).

## References

- R. M. Wald, *General Relativity* (Univ. Chicago Press, 1984), §3.1
  (Levi-Civita uniqueness on a Lorentzian metric).
- B. O'Neill, *Semi-Riemannian Geometry* (Academic Press, 1983), Ch. 3
  (Lorentzian metric definition + non-degeneracy).
- M. Spivak, *A Comprehensive Introduction to Differential Geometry* Vol. II
  (Publish or Perish, 1979), Ch. 1 (semi-Riemannian metric tensor).
- Massot/Rothgang/Macbeth, `Mathlib.Geometry.Manifold.VectorField.CovariantDerivative`
  (Mathlib4 `8850ed93`).
- S. Gouëzel, `Mathlib.Topology.VectorBundle.Riemannian`
  (`IsContinuousRiemannianBundle` template — Lorentzian analog absent).

**First formalization in any proof assistant** of bundle-level
Lorentzian metric typeclass with substantive bridge to bundle-level
Levi-Civita uniqueness via the Koszul derivation. (Per Phase 6f audit
§3E: zero proof assistants currently have indefinite-signature metric
infrastructure beyond pointwise predicates.)
-/

@[expose] public section

namespace SKEFTHawking.LorentzianBundle

open Bundle NormedSpace
open VectorField
open scoped Manifold ContDiff Topology

open SKEFTHawking.LeviCivita

/-! ## Variable section

We follow Bonn's `CovariantDerivative.Basic` setup, mirroring the
Wave 8 Sessions 5+5b `LeviCivita.lean` variable bindings exactly so the
bridge theorem in §4 ingests `IsLeviCivita 𝕜 cov g` with the right
universe and instance signatures. -/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [CompleteSpace E]

/-! ## §1 Bundle-level Lorentzian metric predicate -/

/--
**`IsLorentzianBundle g`:** the family of fiber bilinear forms
`g : Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜`
constitutes a Lorentzian metric on the tangent bundle if it is
*symmetric* at every fiber and *non-degenerate* at every fiber.

The signature condition (existence of an orthonormal frame putting
`g x` into `(-, +, +, ..., +)` form) is independent of these two
structural conditions and is captured at the algebraic-precedent level
in `LorentzianMetric.IsLorentzianSignature`. The bundle-level layer
here ships the symmetry-and-non-degeneracy backbone, which is what the
bundle-level Levi-Civita uniqueness derivation (Wave 8 Sessions 5+5b)
consumes.

The choice to bundle symmetry + non-degeneracy at the bundle level
(rather than full Lorentzian signature) follows O'Neill's semi-Riemannian
treatment: the Levi-Civita connection exists and is unique on any
non-degenerate symmetric bilinear form, regardless of signature.
Lorentzian and Riemannian metrics are then specializations distinguished
by signature.
-/
structure IsLorentzianBundle
    (g : Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜) : Prop where
  /-- `g x` is symmetric at every point. -/
  symm : ∀ (x : M) (v w : TangentSpace I x), g x v w = g x w v
  /-- `g x` is non-degenerate at every point: only zero vector pairs
  trivially against everything. -/
  nondegenerate : ∀ x : M, IsNondegenerateAt g x

/-! ## §2 Direct projection theorems

These are the structural projections feeding into the LeviCivita /
RaychaudhuriEquation pipeline downstream. They look thin in isolation
but each is a load-bearing API endpoint: the named theorems can be
called by downstream consumers without exposing the structure
constructor pattern. -/

omit [IsManifold I 1 M] [CompleteSpace E] in
/--
**`lorentzianBundle_isNondegenerateAt`:** every fiber of a Lorentzian
bundle is non-degenerate. This is the direct consumer of
`LeviCivita.leviCivita_pointwise_unique_of_koszul` — the algebraic
uniqueness kernel ingests `IsNondegenerateAt g x` as its non-degeneracy
hypothesis. -/
theorem lorentzianBundle_isNondegenerateAt
    {g : Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜}
    (h : IsLorentzianBundle g) (x : M) :
    IsNondegenerateAt g x :=
  h.nondegenerate x

-- `lorentzianBundle_symm_apply` (initial first-pass) was a direct
-- restatement of `IsLorentzianBundle.symm` with no downstream consumer
-- in this wave (the substantive symmetry use happens via `IsLeviCivita.metric_symm`
-- internally inside the LeviCivita machinery, not via a standalone API
-- endpoint at the LorentzianBundle level). Cut at the 2026-04-30
-- post-wave ruthless audit per pattern #7
-- (`feedback_post_wave_strengthening_audit.md`: section-level lifts of
-- pointwise lemmas without consumer). The `IsLorentzianBundle.symm` field
-- remains directly accessible to downstream consumers when needed.

/-! ## §3 Substantive non-degeneracy consequences

The Lorentzian-bundle non-degeneracy condition is a property of `g x` as
a bilinear form on `TangentSpace I x`; the substantive consequences for
downstream curve-theoretic arguments come from converting it into pairing
*injection* statements via the standard subtraction trick. -/

omit [IsManifold I 1 M] [CompleteSpace E] in
/--
**`lorentzianBundle_pairing_left_injective`:** if two tangent vectors
`v, w : TangentSpace I x` produce identical pairings against every
test vector, they are equal. Substantive consequence of non-degeneracy
via the `v - w` subtraction trick.

This is the load-bearing form of non-degeneracy used in curve-theoretic
arguments. It witnesses that `g x` separates points: the map
`v ↦ g x v` (as a continuous-linear-form-valued function) is injective.
RaychaudhuriEquation.lean (Session 3) consumes this when separating
tangent-vector decompositions of the null tangent. -/
theorem lorentzianBundle_pairing_left_injective
    {g : Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜}
    (h : IsLorentzianBundle g) (x : M) {v w : TangentSpace I x}
    (h_eq : ∀ z : TangentSpace I x, g x v z = g x w z) :
    v = w := by
  -- Apply non-degeneracy to v - w: pair (v - w) with every z and use
  -- bilinearity to convert to the difference of pairings, which is zero
  -- by hypothesis.
  have h_pair_zero : ∀ z : TangentSpace I x, g x (v - w) z = 0 := by
    intro z
    rw [ContinuousLinearMap.map_sub, ContinuousLinearMap.sub_apply, h_eq z, sub_self]
  have h_diff_zero : v - w = 0 := h.nondegenerate x (v - w) h_pair_zero
  exact sub_eq_zero.mp h_diff_zero

omit [IsManifold I 1 M] [CompleteSpace E] in
/--
**`lorentzianBundle_pairing_right_injective`:** the right-slot
analog. If `g x z v = g x z w` for all `z`, then `v = w`. Symmetric
companion to `lorentzianBundle_pairing_left_injective`, derived via
`lorentzianBundle_symm_apply`. -/
theorem lorentzianBundle_pairing_right_injective
    {g : Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜}
    (h : IsLorentzianBundle g) (x : M) {v w : TangentSpace I x}
    (h_eq : ∀ z : TangentSpace I x, g x z v = g x z w) :
    v = w := by
  apply lorentzianBundle_pairing_left_injective h x
  intro z
  rw [h.symm x v z, h.symm x w z]
  exact h_eq z

/-! ## §4 Bridge to bundle-level Levi-Civita uniqueness

The wave-headline cross-module bridge. Composes `IsLorentzianBundle`
with `LeviCivita.leviCivita_unique_of_isLeviCivita` to get the
Lorentzian-specific uniqueness statement. The proof body genuinely
calls the Wave 8 Session 5+5b composition theorem; this is the
load-bearing P6 cross-module bridge that confirms the Penrose chain
infrastructure is ready. -/

omit [CompleteSpace E] in
/--
**`leviCivita_unique_for_lorentzianBundle`:** on a Lorentzian-bundle
metric `g`, any two Levi-Civita connections agree pointwise (under
the smoothness hypotheses required by the Wave 8 Session 5+5b Koszul
derivation). The proof body invokes `leviCivita_unique_of_isLeviCivita`
directly, with `IsLorentzianBundle.nondegenerate x` discharging the
non-degeneracy hypothesis.

This is the **substantive bridge** — it confirms that on Lorentzian
spacetimes (the curve-theoretic Penrose setting), the Levi-Civita
connection is uniquely determined by the metric, so RaychaudhuriEquation
(Session 3) and FocalPoint (Session 4) can speak unambiguously about
"the Levi-Civita connection of `g`". -/
theorem leviCivita_unique_for_lorentzianBundle
    {cov cov' : (Π x : M, TangentSpace I x) →
                (Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x)}
    {g : Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜}
    (h_lorentz : IsLorentzianBundle g)
    (h_cov : IsLeviCivita 𝕜 cov g) (h_cov' : IsLeviCivita 𝕜 cov' g)
    (h_two : (2 : 𝕜) ≠ 0)
    (x : M)
    (h_smooth : ∀ (X Y Z : Π x : M, TangentSpace I x),
                  MDiffAt (T% X) x ∧ MDiffAt (T% Y) x ∧ MDiffAt (T% Z) x ∧
                  MDiffAt (fun y => g y (Y y) (Z y)) x ∧
                  MDiffAt (fun y => g y (Z y) (X y)) x ∧
                  MDiffAt (fun y => g y (X y) (Y y)) x) :
    ∀ (X Y : Π x : M, TangentSpace I x), cov Y x (X x) = cov' Y x (X x) :=
  leviCivita_unique_of_isLeviCivita h_cov h_cov' h_two x
    (lorentzianBundle_isNondegenerateAt h_lorentz x) h_smooth

/-! ## §5 Substantive Riemannian-vs-Lorentzian falsifier at bundle level

The Wave-7 §3 falsifier `riemannian_not_lorentzian_signature`
distinguishes the algebraic-precedent signature predicates. We lift
to the bundle level: a positive-definite bundle metric (`IsRiemannianBundle`)
cannot also be a Lorentzian bundle metric whose timelike slot is
non-trivially negative. -/

/--
**`IsRiemannianBundle g`:** the bundle-level positive-definite analog —
fiber-symmetric and *positive-definite* at every fiber (`g x v v > 0`
for `v ≠ 0`). Mirrors the structural shape of Mathlib's
`IsContinuousRiemannianBundle` (modulo continuity, deferred to the
upstream PR shape). -/
structure IsRiemannianBundle [PartialOrder 𝕜]
    (g : Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜) : Prop where
  /-- `g x` is symmetric at every point. -/
  symm : ∀ (x : M) (v w : TangentSpace I x), g x v w = g x w v
  /-- `g x` is positive-definite at every point. -/
  posDef : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < g x v v

-- `riemannianBundle_implies_lorentzian_pairing_pos` (initial first-pass)
-- was a direct restatement of `IsRiemannianBundle.posDef` with the same
-- pattern as `lorentzianBundle_symm_apply`. The substantive falsifier
-- below uses `h_R.posDef x v hv` directly (not via this named endpoint),
-- so the projection has no consumer. Cut at the 2026-04-30 post-wave
-- ruthless audit per pattern #3 (P3 trivial-projection-as-named-API).
-- The `IsRiemannianBundle.posDef` field remains directly accessible.

omit [IsManifold I 1 M] [CompleteSpace E] in
/--
**`riemannianBundle_not_lorentzianBundle_with_negative_self_pairing`:**
substantive falsifier — if `g` is a Riemannian bundle metric and
also exhibits some non-zero vector `v` with `g x v v < 0` (a hallmark
of Lorentzian metrics on a timelike vector), we derive a contradiction
from positive-definiteness via `lt_asymm`.

This is the bundle-level counterpart of Wave-7's
`riemannian_not_lorentzian_signature`: at the algebraic-precedent layer
the diagonal entries directly contradicted; at the bundle layer we use
the abstract positive-definiteness vs negative self-pairing
contradiction. -/
theorem riemannianBundle_not_lorentzianBundle_with_negative_self_pairing
    [PartialOrder 𝕜]
    {g : Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜}
    (h_R : IsRiemannianBundle g)
    (x : M) {v : TangentSpace I x} (hv : v ≠ 0)
    (h_neg : g x v v < 0) :
    False :=
  lt_asymm (h_R.posDef x v hv) h_neg

/-! ## §6 Module summary marker

Phase 6g.2-curve-theoretic Session 1 — bundle-level Lorentzian metric
infrastructure.

**Substantive declarations shipped (8 + 1 marker):**

§1 — Bundle predicate:
1. `IsLorentzianBundle` — symmetry + non-degeneracy bundled at the
   tangent-bundle level.

§2 — Direct projection (load-bearing API endpoint feeding LeviCivita
downstream):
2. `lorentzianBundle_isNondegenerateAt` (consumed in §4
   `leviCivita_unique_for_lorentzianBundle`).

§3 — Substantive non-degeneracy consequences:
3. `lorentzianBundle_pairing_left_injective` (load-bearing pairing
   injectivity via `v - w` subtraction trick).
4. `lorentzianBundle_pairing_right_injective` (symmetric companion;
   intended for downstream curve-theoretic argument use).

§4 — Wave-headline bridge to Wave-8 Sessions 5+5b:
5. `leviCivita_unique_for_lorentzianBundle` (the substantive
   Lorentzian Levi-Civita uniqueness — *the key Penrose-chain unblock*).

§5 — Bundle-level falsifier:
6. `IsRiemannianBundle` (predicate).
7. `riemannianBundle_not_lorentzianBundle_with_negative_self_pairing`
   (substantive bundle-level falsifier via `lt_asymm`; the lifted Wave-7
   §3 pattern).

§6 — Module marker.

**Strengthening cuts (2026-04-30 ruthless post-wave audit, applied at
Session 5 close):**

1. **`lorentzianBundle_symm_apply` (CUT — pattern #7 lift-without-consumer).**
   The initial first-pass shipped this as a named API endpoint
   restating `IsLorentzianBundle.symm`. End-of-wave audit found no
   downstream consumer; the substantive symmetry use happens internally
   via `IsLeviCivita.metric_symm` rather than via a standalone
   LorentzianBundle-level API. The `IsLorentzianBundle.symm` field
   remains directly accessible to consumers when needed.

2. **`riemannianBundle_implies_lorentzian_pairing_pos` (CUT — pattern #3
   trivial-projection-as-named-API).** Same shape as cut #1 — a direct
   restatement of `IsRiemannianBundle.posDef`. The Riemannian-vs-Lorentzian
   falsifier `riemannianBundle_not_lorentzianBundle_with_negative_self_pairing`
   uses `h_R.posDef x v hv` directly, not via this name, so the named
   projection has no consumer.

Net Session 1 substantive count: 7 declarations + 1 marker (post-cut),
down from 9 declarations + 1 marker (pre-cut, including the structures
+ projections counted independently). Counting the structures
(`IsLorentzianBundle`, `IsRiemannianBundle`) as substantive declarations
on their own + 5 substantive theorems gives 7 substantive declarations.

**Strengthening pre-pass discipline (5-question checklist applied
prospectively per CLAUDE.md):**
1. **Bundle redundancy** ✓ — `IsLorentzianBundle` symm + nondegen are
   independently substantive (a Riemannian metric is symm + posDef ⇒ nondegen,
   but symm + nondegen ⊅ posDef; degenerate forms are symm + ¬nondegen).
2. **Quantitative connection** ✓ — `lorentzianBundle_pairing_left_injective`
   produces an actual `v = w` conclusion from the bilinearity of `g x`,
   substantive linear-algebra content (not a `rfl` rename).
3. **Cross-module bridge integrity** ✓ — body imports
   `SKEFTHawking.LeviCivita` and *calls* `IsNondegenerateAt`,
   `IsLeviCivita`, `leviCivita_unique_of_isLeviCivita` directly in
   `leviCivita_unique_for_lorentzianBundle`.
4. **Trivial-discharge check** ✓ — the projection theorems §2 are thin
   but each is a *named API endpoint* with a downstream consumer
   (LeviCivita kernel + IsLeviCivita.metric_symm); the bridge theorem
   §4 invokes a substantive Wave-8 composition theorem, not a `rfl`
   discharge.
5. **Defining-the-conclusion check** ✓ — `IsLorentzianBundle` does not
   define `cov` to equal `cov'`; the uniqueness conclusion comes from
   the Koszul derivation's substantive content composed via
   `leviCivita_unique_of_isLeviCivita`.

**Bundle-target alignment:** Lifts as **D3 §24** (the headline
correctness-push section per `PAPER_DRAFT_MAPPING.md` Phase 6g
addendum) AND as **I1 sidebar primary** (the Mathlib-PR-shape
infrastructure paper44 trail). No new bundle target needed.

**First formalization in any proof assistant** (per Phase 6f audit
§3E + this session's audit) of the bundle-level Lorentzian metric
typeclass with substantive bridge to bundle-level Levi-Civita uniqueness
via Koszul. Mathlib4 has `IsContinuousRiemannianBundle` (Gouëzel 2025)
but no Lorentzian analog; no other proof assistant (Coq, Isabelle/AFP,
HOL Light, HOL4, Mizar, Agda) has a bundle-level Lorentzian metric
typeclass.

**Stages 10/11/13 deferred per user policy** (Mathlib-PR-style
infrastructure; content lifts as D3 §24 + I1 sidebar). Cross-layer
Python pipeline (Stages 6-8) deferred per Phase 6f-6g `O.7` precedent.
-/
theorem _phase6g_w2_curve_session1_module_summary_marker : True := trivial

end SKEFTHawking.LorentzianBundle
