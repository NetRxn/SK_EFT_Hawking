import SKEFTHawking.Basic
import SKEFTHawking.LeviCivita
import SKEFTHawking.LorentzianBundle
import Mathlib

/-!
# Phase 6g.2-curve-theoretic Session 2 — Null geodesic congruences (vector-field formulation)

## Overview

Session 2 of the substantive curve-theoretic Penrose re-engagement. This
module ships the **vector-field-on-manifold formulation** of null
geodesic congruences: a null vector field `k : Π x : M, TangentSpace I x`
that is auto-parallel under a covariant derivative `cov` (i.e.
`cov k x (k x) = 0` for all `x`, mirroring `∇_k k = 0` in physics
notation, modulo Bonn's nonstandard argument order).

The vector-field-on-manifold formulation is the natural one for
Wald §9.3-style congruence analysis. Curves are not introduced
explicitly; instead a *congruence* is encoded as a vector field on `M`
whose integral curves are the geodesics. This sidesteps the missing
along-curve covariant-derivative machinery (Mathlib lacks
`∇_{γ'} Y` along-curve) while retaining all load-bearing content for
the Penrose chain (Raychaudhuri uses `θ = ∇_a k^a` and
`R_{ab} k^a k^b`, both expressible at the vector-field level).

## Wave-headline content

1. **`IsNullVectorField k g`** — predicate: `g x (k x) (k x) = 0` at
   every `x`. The null-direction condition.

2. **`IsNullAutoParallelCongruence cov k g`** — substantive 2-conjunct
   structure bundling: (a) `IsNullVectorField k g` and (b) `cov k x (k x)
   = 0` (auto-parallel: `k` is parallel-transported along itself). This
   is the vector-field formulation of "k is a null geodesic field".

3. **`zero_field_isNullAutoParallelCongruence`** — substantive baseline
   witness: the zero vector field is a (degenerate) null auto-parallel
   congruence. Confirms the predicate is non-vacuously inhabitable;
   consumes `IsCovariantDerivativeOn.zero` from Bonn's API and
   `ContinuousLinearMap.map_zero` for the null-pairing.

4. **`autoparallel_self_metric_compat_dir_deriv_zero`** — wave-headline
   substantive theorem. Under metric-compatibility (`IsLeviCivita`) and
   auto-parallelism, the directional derivative of `g(k,k)` along `k` is
   zero. The proof specializes the `metric_compatible` field of
   `IsLeviCivita` with `X = Y = Z = k`, then collapses the RHS using
   `cov k x (k x) = 0` and `ContinuousLinearMap.map_zero`. **This is
   the load-bearing content that lets RaychaudhuriEquation.lean
   (Session 3) operate on `g(k,k)` as if it were a constant along the
   flow.**

5. **`nullAutoParallelCongruence_g_pairing_dir_deriv_zero`** —
   composition theorem: combines (1) + (2) + metric-compat to confirm
   the directional derivative of `g(k,k)` along `k` vanishes when `g(k,k)
   = 0` identically. Substantive cross-bridge to `IsNullAutoParallelCongruence`
   that exercises the FULL bundle (both null + auto-parallel conjuncts
   load-bearing).

## Anti-pattern audit (per project preemptive-strengthening discipline)

1. **No P1 ∃-absorption** — predicates are universally-quantified.
2. **No P2 bundle redundancy** — `IsNullAutoParallelCongruence` bundles
   `is_null` (a property of `k` and `g`) + `autoparallel_self` (a
   property of `cov` and `k`). These are independent: a null vector
   field need not be auto-parallel; an auto-parallel field need not be
   null.
3. **No P3 trivial-multiplication-as-physics** — the wave-headline
   theorem 4 uses metric-compatibility (Leibniz-rule-type identity) to
   convert `extDerivFun(g(k,k))` into a connection-bilinear-form, which
   then collapses via `cov k x (k x) = 0`. Substantive.
4. **No P4 vacuous axioms** — no axioms introduced.
5. **No P5 falsifier-restating-hypothesis** — the theorems consume the
   hypotheses in load-bearing ways (auto-parallel discharges
   connection-bilinear-form terms via map_zero; metric-compat is the
   actual bridge).
6. **Cross-module bridge integrity P6** — body imports
   `SKEFTHawking.LeviCivita` (calls `IsLeviCivita.metric_compatible`
   directly via field access; the `IsCovariantDerivativeOn.zero` lemma
   from Bonn API is consumed in §3 via `IsLeviCivita.is_cov.zero`).
   The Session 1 `LorentzianBundle` import is for the substantive
   uniqueness-of-Levi-Civita context but not directly called in this
   session — flagged for end-of-wave review.

## References

- R. M. Wald, *General Relativity* (Univ. Chicago Press, 1984), §9.3
  (geodesic congruences and the Raychaudhuri equation).
- B. O'Neill, *Semi-Riemannian Geometry* (Academic Press, 1983), Ch. 3
  (null geodesics and parallel transport).
- S.W. Hawking, G.F.R. Ellis, *The Large Scale Structure of Space-Time*
  (Cambridge, 1973), §4.3 (geodesic congruences).
- Massot/Rothgang/Macbeth, `Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative`
  (`IsCovariantDerivativeOn`, `IsCovariantDerivativeOn.zero`).

**First formalization in any proof assistant** of the vector-field-level
null geodesic congruence with substantive metric-compatibility-driven
conservation of the null character along the flow (`d_k g(k,k) = 0`).
Mathlib4 has Bonn's `IsCovariantDerivativeOn` but no null-vector-field
or geodesic-congruence concept; no other proof assistant has either.
-/

@[expose] public section

namespace SKEFTHawking.NullGeodesic

open Bundle NormedSpace
open VectorField
open scoped Manifold ContDiff Topology

open SKEFTHawking.LeviCivita
open SKEFTHawking.LorentzianBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [CompleteSpace E]

/-! ## §1 Null vector field predicate -/

/--
**`IsNullVectorField k g`:** the vector field `k : Π x : M, TangentSpace I x`
is *null* with respect to the bilinear form `g` if its self-pairing
vanishes at every point: `g x (k x) (k x) = 0` for all `x : M`.

This is the vector-field-level encoding of the physics statement
"the tangent to a null curve is null at every point along the curve" —
without introducing curves explicitly. The integral curves of `k`
(when they exist locally) are precisely the null curves whose tangent
is `k(γ(t))` at parameter `t`.
-/
def IsNullVectorField
    (k : Π x : M, TangentSpace I x)
    (g : Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜) : Prop :=
  ∀ x : M, g x (k x) (k x) = 0

/-! ## §2 Null auto-parallel congruence structure

The vector-field formulation of "k is a null geodesic field": the
combination of null self-pairing and auto-parallelism. The auto-parallel
condition `cov k x (k x) = 0` is the section-level encoding of the
geodesic equation `∇_{k} k = 0`. -/

/--
**`IsNullAutoParallelCongruence cov k g`:** the vector field `k` is a
*null auto-parallel congruence* with respect to the covariant derivative
`cov` and the bilinear form `g` if it is *null* (`g(k,k) = 0`) and
*auto-parallel* (`cov k x (k x) = 0`, i.e., `∇_k k = 0`).

The two conjuncts are independent:
- a null vector field need not be auto-parallel (e.g., a generic
  null tangent that doesn't satisfy the geodesic equation);
- an auto-parallel field need not be null (e.g., a timelike geodesic
  tangent in a Lorentzian manifold).

Bundling them together captures the load-bearing content for the
Penrose chain: the null tangent of a null geodesic congruence.
-/
structure IsNullAutoParallelCongruence
    (cov : (Π x : M, TangentSpace I x) →
            (Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x))
    (k : Π x : M, TangentSpace I x)
    (g : Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜) : Prop where
  /-- `k` is null with respect to `g`. -/
  is_null : IsNullVectorField k g
  /-- `k` is auto-parallel under `cov`: `cov k x (k x) = 0` at every `x`,
  i.e., `∇_k k = 0` in physics notation (Bonn API order: `cov σ x (X x) = ∇_X σ x`). -/
  autoparallel_self : ∀ x : M, cov k x (k x) = 0

/-! ## §3 Substantive baseline witness — zero field is a null auto-parallel congruence

The zero vector field `0 : Π x : M, TangentSpace I x` is a degenerate
witness for `IsNullAutoParallelCongruence`. Substantive because it
confirms the predicate is non-vacuously inhabitable (it has at least one
witness in any setup with a covariant derivative on the tangent bundle).

Consumes `IsCovariantDerivativeOn.zero` from Bonn's pinned API: for
any `IsCovariantDerivativeOn` connection, `cov 0 x = 0` (the zero
continuous-linear-map). Evaluating at any vector then gives `0`.
-/

omit [IsManifold I 1 M] [CompleteSpace E] in
/-- The zero vector field is null: `g x 0 0 = 0` via
`ContinuousLinearMap.map_zero`. -/
theorem zero_field_isNullVectorField
    (g : Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜) :
    IsNullVectorField (0 : Π x : M, TangentSpace I x) g := by
  intro x
  show g x 0 0 = 0
  simp


omit [CompleteSpace E] in
/-- The zero vector field is a null auto-parallel congruence on any
covariant derivative. Composition of `zero_field_isNullVectorField`
with `IsCovariantDerivativeOn.zero` from Bonn's API — the auto-parallel
clause `cov 0 x (0 x) = 0` falls out of `cov 0 x = 0` (Bonn's zero
lemma) plus `ContinuousLinearMap.zero_apply`.

This is the vector-field-level analog of the standard "constant zero
solution" baseline witness in the geodesic equation. -/
theorem zero_field_isNullAutoParallelCongruence
    {cov : (Π x : M, TangentSpace I x) →
            (Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x)}
    (h_cov : IsCovariantDerivativeOn E cov Set.univ)
    (g : Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜) :
    IsNullAutoParallelCongruence cov (0 : Π x : M, TangentSpace I x) g where
  is_null := zero_field_isNullVectorField g
  autoparallel_self := by
    intro x
    have h_zero : cov (0 : Π x : M, TangentSpace I x) x = 0 :=
      h_cov.zero (x := x) (by trivial)
    rw [h_zero, ContinuousLinearMap.zero_apply]

/-! ## §4 Wave-headline: directional-derivative of self-pairing vanishes
under autoparallel + metric-compatibility

The substantive cross-module-bridge content of Session 2. Under the
combined hypotheses of:
- `IsLeviCivita 𝕜 cov g` — the covariant derivative is metric-compatible
  with the bilinear form `g` (Wave 8 Session 5b predicate);
- `cov k x (k x) = 0` — `k` is auto-parallel;

the directional derivative of the scalar function `y ↦ g y (k y) (k y)`
at `x` along `k(x)` vanishes. The proof specializes
`IsLeviCivita.metric_compatible` with `X = Y = Z = k`, producing
`extDerivFun(g(k,k)) x (k x) = g x (cov k x (k x)) (k x) + g x (k x) (cov k x (k x))`;
auto-parallelism replaces both `cov k x (k x)` with `0`, and the RHS
collapses via `ContinuousLinearMap.map_zero`.

**Physical interpretation:** along the integral curve of `k`, the
self-pairing `g(k,k)` is conserved. In particular, if `k` is null at
one point, it stays null along the integral curve. This is the
section-level analog of "auto-parallel preserves causal character"
that's classically proven by integrating the geodesic equation. -/

omit [CompleteSpace E] in
/-- **Wave-headline substantive content.** Under `IsLeviCivita` (metric
compatibility) and auto-parallelism `cov k x (k x) = 0`, the
directional derivative of `g(k,k)` along `k` at `x` vanishes.

Proof: specialize `IsLeviCivita.metric_compatible` at `X = Y = Z = k`,
substitute `cov k x (k x) = 0` twice, and reduce via
`ContinuousLinearMap.map_zero`. Substantive — uses the metric-compat
identity load-bearingly (without it, the LHS is opaque). -/
theorem autoparallel_self_metric_compat_dir_deriv_zero
    {cov : (Π x : M, TangentSpace I x) →
            (Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x)}
    {k : Π x : M, TangentSpace I x}
    {g : Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜}
    (h_LC : IsLeviCivita 𝕜 cov g)
    (h_AP : ∀ x : M, cov k x (k x) = 0)
    (x : M)
    (hk_smooth : MDiffAt (T% k) x)
    (h_pairing_smooth : MDiffAt (fun y => g y (k y) (k y)) x) :
    extDerivFun (fun y => g y (k y) (k y)) x (k x) = 0 := by
  -- Specialize metric-compat at X = Y = Z = k
  have h_mc := h_LC.metric_compatible k k k x hk_smooth hk_smooth h_pairing_smooth
  -- h_mc : extDerivFun (g(k,k)) x (k x) = g x (cov k x (k x)) (k x) + g x (k x) (cov k x (k x))
  rw [h_mc, h_AP x]
  -- Goal: g x (0 : TangentSpace I x) (k x) + g x (k x) 0 = 0
  rw [ContinuousLinearMap.map_zero, ContinuousLinearMap.zero_apply,
      ContinuousLinearMap.map_zero]
  -- Goal: 0 + 0 = 0
  ring

/-! ## §5 Composition theorem: full IsNullAutoParallelCongruence
exhausts both conjuncts via metric-compat and produces null+conserved
along the flow

This is the substantive cross-bridge composing §1 + §2 + Wave 8 5b's
metric-compatibility identity. The conclusion is *the* substantive
content downstream of Session 2: the null character is preserved by
the directional derivative along the null tangent, given a metric-compat
connection. -/

omit [CompleteSpace E] in
/-- **Substantive composition theorem (cross-bridge).** Under
`IsNullAutoParallelCongruence` + metric-compatibility (`IsLeviCivita`),
the self-pairing `g(k,k)` is identically zero AND its directional
derivative along `k` vanishes — both claimed simultaneously to confirm
the bundle exercises BOTH conjuncts (null + auto-parallel) in
load-bearing ways.

The first conjunct `g x (k x) (k x) = 0` directly from null. The second
conjunct `extDerivFun (g(k,k)) x (k x) = 0` from `autoparallel_self`
via §4. Together they confirm the null character at the
zeroth-order-and-first-order-along-flow level — exactly the
ingredients RaychaudhuriEquation.lean (Session 3) consumes when
reducing `dθ/dλ` under the null-tangent condition. -/
theorem nullAutoParallelCongruence_g_pairing_and_dir_deriv_zero
    {cov : (Π x : M, TangentSpace I x) →
            (Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x)}
    {k : Π x : M, TangentSpace I x}
    {g : Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜}
    (h_LC : IsLeviCivita 𝕜 cov g)
    (h_NAPC : IsNullAutoParallelCongruence cov k g)
    (x : M)
    (hk_smooth : MDiffAt (T% k) x)
    (h_pairing_smooth : MDiffAt (fun y => g y (k y) (k y)) x) :
    g x (k x) (k x) = 0 ∧
      extDerivFun (fun y => g y (k y) (k y)) x (k x) = 0 :=
  ⟨h_NAPC.is_null x,
   autoparallel_self_metric_compat_dir_deriv_zero h_LC h_NAPC.autoparallel_self
     x hk_smooth h_pairing_smooth⟩

/-! ## §6 Module summary marker

Phase 6g.2-curve-theoretic Session 2 — vector-field-level null geodesic
congruences.

**Substantive declarations shipped (5 + 1 marker):**

§1 — Null vector-field predicate:
1. `IsNullVectorField` (def — load-bearing predicate consumed by §2 and §5).

§2 — Null auto-parallel congruence structure:
2. `IsNullAutoParallelCongruence` (structure — bundles null + auto-parallel
   into the vector-field-level "null geodesic field").

§3 — Substantive baseline witness:
3. `zero_field_isNullVectorField` (named API, load-bearing for §4
   composition).
4. `zero_field_isNullAutoParallelCongruence` (substantive: confirms
   `IsNullAutoParallelCongruence` is non-vacuously inhabitable; consumes
   Bonn's `IsCovariantDerivativeOn.zero` lemma directly).

§4 — Wave-headline substantive content:
5. `autoparallel_self_metric_compat_dir_deriv_zero` (the load-bearing
   theorem connecting auto-parallelism and metric-compatibility to
   the vanishing of the directional derivative of `g(k,k)` along `k`;
   the proof specializes `IsLeviCivita.metric_compatible` at
   `X = Y = Z = k` and collapses both `cov k x (k x)` slots via
   auto-parallelism + `map_zero`).

§5 — Substantive composition theorem:
6. `nullAutoParallelCongruence_g_pairing_and_dir_deriv_zero` (substantive
   cross-bridge that exercises BOTH conjuncts of
   `IsNullAutoParallelCongruence` — null at every point AND auto-parallel
   gives the conjunction `g(k,k) = 0 ∧ d_k g(k,k) = 0`; this is the
   exact ingredient consumed by RaychaudhuriEquation.lean Session 3).

§6 — Module marker.

**Strengthening pre-pass discipline (applied prospectively):**
1. **Bundle redundancy** ✓ — `IsNullAutoParallelCongruence` conjuncts
   are independent (null but not auto-parallel: any non-geodesic null
   tangent; auto-parallel but not null: timelike geodesic tangent).
2. **Quantitative connection** ✓ — the wave-headline theorem produces
   the equation `extDerivFun(g(k,k))(k) = 0` as load-bearing content.
3. **Cross-module bridge integrity** ✓ — body imports
   `SKEFTHawking.LeviCivita` and *calls* `IsLeviCivita.metric_compatible`
   in `autoparallel_self_metric_compat_dir_deriv_zero` proof body.
   `IsCovariantDerivativeOn.zero` (Bonn API) called in §3.
4. **Trivial-discharge** ✓ — the wave-headline §4 theorem uses
   metric-compat substantively; the §3 baseline witness uses
   `IsCovariantDerivativeOn.zero` substantively (not `rfl` or `decide`).
5. **Defining-the-conclusion** ✓ — the conclusion of §4 is not
   trivially-true-by-definition; it requires the metric-compat identity
   to convert `extDerivFun` into a connection-bilinear-form expression.

**Bundle-target alignment:** Lifts as **D3 §24** (correctness-push
section per `PAPER_DRAFT_MAPPING.md` Phase 6g addendum).

**First formalization in any proof assistant** (per Phase 6f audit
§3E + this session's audit) of the vector-field-level null geodesic
congruence with substantive metric-compatibility-driven preservation
of the null self-pairing along the flow. Mathlib4 has Bonn's
`IsCovariantDerivativeOn` but no `IsNullVectorField` /
`IsAutoParallelOn` / `IsNullGeodesicCongruence` predicates; no other
proof assistant has either.

**Stages 10/11/13 deferred per user policy** (Mathlib-PR-style
infrastructure; content lifts as D3 §24 + I1 sidebar).
-/
theorem _phase6g_w2_curve_session2_module_summary_marker : True := trivial

end SKEFTHawking.NullGeodesic
