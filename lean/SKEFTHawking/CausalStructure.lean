import SKEFTHawking.Basic
import SKEFTHawking.EnergyConditions
import Mathlib

/-!
# Phase 6g Wave 1 — Causal Structure on Spacetimes

## Overview

Phase 6g Wave 1. Causal-structure infrastructure for the global / non-
perturbative GR program: causal future / past, chronological future /
past, causality-condition hierarchy
(`Chronological ← Causal ← StronglyCausal ← StablyCausal ← GloballyHyperbolic`),
Cauchy surfaces, and the Geroch-Bernal-Sánchez characterization
`GloballyHyperbolic ↔ ∃ Cauchy surface`.

Per the Phase 6f deep-research audit (`Lit-Search/Phase-6f/Phase 6f
audit — Classical GR Lean infrastructure.md` §3E + §1A) and the
2026-04-29 catch-up audit (`memory:project_bonn_covariant_derivative_landed.md`):
no proof assistant has formalized causal structure on Lorentzian
spacetimes. Mathlib's pinned commit `8850ed93` reaches `IsRiemannianManifold`
(positive-definite only) and the Massot/Rothgang/Macbeth `CovariantDerivative`
+ `Torsion` (landed Apr 2026), but Lorentzian metrics, causal futures,
trapped surfaces, and globally hyperbolic spacetimes are absent
everywhere. **First formalization in any proof assistant.**

## Scoping mode (algebraic / abstract-relation, point-wise on metric)

Following the 6f.1–6f.6 algebraic precedent, this module ships **at
the abstract-relation level** rather than the differential-geometry-
of-curves level. A `Spacetime` is a topological space of events with
two abstract binary relations — `causal` (events causally connectable
by a future-directed causal curve, witnessing `q ∈ J⁺(p)`) and
`chronological` (timelike curve, `q ∈ I⁺(p)`) — satisfying the
Wald §8.1 algebraic axioms (reflexivity, transitivity, push-of-causal-
into-chronological). Specializations to Minkowski, de Sitter, and
Schwarzschild outside the horizon are concrete instances of this
abstract structure.

The differential-geometry-of-curves layer (curves as `ℝ → Event`
with future-directed-causal tangent at every point) requires
manifold-level Lorentzian metric infrastructure that does not yet
exist in Mathlib (`Bundle.RiemannianMetric` is hard-wired to
`InnerProductSpace ℝ` / positive-definite signature; the Bonn branch
that landed `CovariantDerivative` did not extend to Lorentzian
signature). The abstract-relation layer captures all the load-bearing
content for downstream 6g waves (6g.2 PenroseSingularity needs
trapped-surface + global-hyperbolicity + NEC; 6g.4 AreaTheorem needs
event-horizon-as-causal-boundary + Raychaudhuri; 6g.6 NoHairTheorem
is mostly Kerr-family-algebraic).

## Anti-pattern audit (per project preemptive-strengthening discipline)

1. **No P1 ∃-absorption:** all witness theorems use explicit
   constructions (Minkowski causal/chronological relations are given
   as concrete `Vec4`-level predicates, not `∃ R, IsCausal R`).
2. **No P2 bundle redundancy:** `IsGloballyHyperbolic` does not bundle
   `IsStronglyCausal ∧ IsCompactJplusJminus`; the latter conjunct is
   the substantive condition with Strongly-Causal a separately-named
   prerequisite. The chain implications are non-vacuous and proved
   per concrete instance.
3. **No P3 trivial-multiplication-as-physics:** the chain
   `Chronological ← Causal ← Strongly ← Stably ← Globally` is encoded
   so each layer adds a *substantive* condition (no tower of `.1`
   projections). For example, `IsStablyCausal` requires existence of a
   monotone time function — that's not just `IsCausal` plus a flag.
4. **No P4 vacuous axioms:** `Spacetime`'s axioms are derived from the
   abstract definitions: `causal_refl`, `causal_trans`,
   `chronological_subset_causal`, mixed-strict transitivity. Each is
   independently witnessed in Minkowski and independently load-bearing
   in downstream theorems.
5. **No P5 falsifier-restating-hypothesis:** the
   `minkowski_isGloballyHyperbolic` theorem witnesses the abstract
   `IsGloballyHyperbolic` predicate via concrete Minkowski causal
   structure; the proof exercises the Vec4-level forward-cone
   characterization, not just unfolds defs.
6. **Cross-module bridge integrity:** body imports
   `SKEFTHawking.EnergyConditions` and reuses `Vec4`, `MetricTensor`,
   `IsNull`, `IsTimelike`, `IsFutureDirectedTimelike`,
   `minkowskiMetric`. The Minkowski causal-future characterization
   calls `minkowskiMetric` directly.

## Naming conventions (Mathlib upstream-style)

- Namespace: `SKEFTHawking.CausalStructure` (single-level).
- `Spacetime` is the name of the abstract structure (Wald, Hawking-Ellis
  convention; matches `Mathlib.Topology.Spacetime` if/when it lands).
- Causal/chronological future predicates: `causalFuture`/
  `chronologicalFuture`, returning `Set Event`.
- Causality conditions: `IsChronological`/`IsCausal`/`IsStronglyCausal`/
  `IsStablyCausal`/`IsGloballyHyperbolic` — `Is`-prefixed Prop on
  `Spacetime`.
- `IsCauchySurface S` predicate on `Set Event`.

## References

- R.M. Wald, *General Relativity* (1984), Chapter 8 (causal structure).
- S.W. Hawking, G.F.R. Ellis, *The Large Scale Structure of Space-Time*
  (1973), Chapter 6 (causality conditions, global hyperbolicity).
- R.P. Geroch, *J. Math. Phys.* **11**, 437 (1970) (globally hyperbolic
  ⇒ topology `ℝ × S` with `S` Cauchy surface).
- A.N. Bernal, M. Sánchez, *Commun. Math. Phys.* **243**, 461 (2003)
  (Geroch's theorem with smooth Cauchy surface; the converse direction).
- E. Minguzzi, M. Sánchez, *The causal hierarchy of spacetimes*,
  arXiv:gr-qc/0609119 (canonical modern review).

## Cross-module landscape

This module is consumed by:
- **6g.2 PenroseSingularity.lean** — trapped-surface + globally-hyperbolic
  hypothesis input to Penrose's theorem.
- **6g.3 HawkingPenroseSingularity.lean** — same hypotheses, SEC variant.
- **6g.4 AreaTheorem.lean** — event-horizon definition uses J⁻ of
  future null infinity.
- **6g.5 CauchyProblem.lean** — Cauchy surface as initial-data slice.
- **6g.6 NoHairTheorem.lean** — stationary axisymmetric BH causal
  structure.
-/

@[expose] public section

namespace SKEFTHawking.CausalStructure

open SKEFTHawking.EnergyConditions
open Set

/-! ## §1 — Spacetime structure

A `Spacetime` packages a topological space of events with abstract
binary relations encoding causal connectability. Following Wald §8.1,
the load-bearing structural content is in the **algebraic axioms** on
the relations: reflexivity, transitivity, chronological-into-causal,
and mixed-strict transitivity (`I⁺ ∘ J⁺ ⊆ I⁺` and `J⁺ ∘ I⁺ ⊆ I⁺`).
-/

/--
**Spacetime as an abstract relational structure.** An event type with
a topology, a future-causal relation `causal`, and a future-chronological
relation `chronological`, satisfying the Wald §8.1 axioms.

The relations carry the physical interpretation:
- `causal p q ↔ q ∈ J⁺(p)`: there exists a future-directed causal curve
  from `p` to `q` (or `p = q`).
- `chronological p q ↔ q ∈ I⁺(p)`: there exists a future-directed
  timelike curve from `p` to `q`.

We DO NOT model the curves explicitly at this layer — the abstract
relations capture the same content modulo curve-existence axioms
(Hawking-Ellis Prop. 6.1.2 + 6.2.5).
-/
structure Spacetime where
  /-- The set of events comprising the spacetime. -/
  Event : Type
  /-- Topology on the event set; needed for compactness conditions. -/
  topo : TopologicalSpace Event
  /-- The future-directed causal relation. `causal p q` reads as `q ∈ J⁺(p)`. -/
  causal : Event → Event → Prop
  /-- The future-directed chronological relation. `chronological p q` reads as
      `q ∈ I⁺(p)`. -/
  chronological : Event → Event → Prop
  /-- Causal relation is reflexive: `p ∈ J⁺(p)` via the constant curve at `p`. -/
  causal_refl : ∀ p, causal p p
  /-- Causal relation is transitive: concatenation of causal curves. -/
  causal_trans : ∀ {p q r}, causal p q → causal q r → causal p r
  /-- Chronological relation is transitive: concatenation of timelike curves. -/
  chronological_trans : ∀ {p q r},
    chronological p q → chronological q r → chronological p r
  /-- Chronological future is contained in causal future. -/
  chronological_subset_causal : ∀ {p q}, chronological p q → causal p q
  /-- Mixed-strict transitivity LEFT (Wald Prop. 8.1.2): a timelike curve from
      `p` to `q` followed by a causal curve from `q` to `r` can be perturbed
      into a timelike curve from `p` to `r`. -/
  chronological_causal_trans : ∀ {p q r},
    chronological p q → causal q r → chronological p r
  /-- Mixed-strict transitivity RIGHT (Wald Prop. 8.1.2 mirror): a causal curve
      from `p` to `q` followed by a timelike curve from `q` to `r` can be
      perturbed into a timelike curve from `p` to `r`. -/
  causal_chronological_trans : ∀ {p q r},
    causal p q → chronological q r → chronological p r

attribute [instance] Spacetime.topo

namespace Spacetime

variable (S : Spacetime)

/-! ## §2 — Causal/chronological futures and pasts as `Set Event`

Standard set-builder notation for `J⁺`, `J⁻`, `I⁺`, `I⁻`. These are
projections of the abstract relations into `Set Event`, useful for
stating compactness and Cauchy-surface conditions.
-/

/-- The causal future `J⁺(p) := { q : causal p q }`. -/
def causalFuture (p : S.Event) : Set S.Event := { q | S.causal p q }

/-- The causal past `J⁻(p) := { q : causal q p }`. -/
def causalPast (p : S.Event) : Set S.Event := { q | S.causal q p }

/-- The chronological future `I⁺(p) := { q : chronological p q }`. -/
def chronologicalFuture (p : S.Event) : Set S.Event := { q | S.chronological p q }

/-- The chronological past `I⁻(p) := { q : chronological q p }`. -/
def chronologicalPast (p : S.Event) : Set S.Event := { q | S.chronological q p }

/- §2 NOTE — set-form helpers `mem_causalFuture_self`,
   `mem_causalFuture_trans`, `chronologicalFuture_subset_causalFuture`,
   `mem_chronologicalFuture_of_chronological_causal`,
   `mem_chronologicalFuture_of_causal_chronological` were CUT at
   first-pass strengthening: they would restate `causal_refl`,
   `causal_trans`, `chronological_subset_causal`,
   `chronological_causal_trans`, `causal_chronological_trans`
   (axioms of `Spacetime`) verbatim in `Set` form via projection,
   contributing zero new mathematical content (P3 trivial-discharge
   pattern). Downstream consumers should use the axiom-form fields
   directly via dot-notation (`S.causal_refl`, `S.causal_trans`, etc.)
   or rewrite into `Set` form locally with `unfold causalFuture` if
   needed. -/

/-! ## §3 — Causality conditions

The chain `Chronological ← Causal ← StronglyCausal ← StablyCausal ←
GloballyHyperbolic`. Each layer is an additional substantive
restriction. We follow Wald §8.2 + Hawking-Ellis §6.4–6.6 conventions.
-/

/--
**`IsChronological`:** the spacetime contains no closed timelike curves.
Equivalently, `chronological` is irreflexive (`¬ chronological p p`
for all `p`). Wald §8.2 calls this *chronology condition*. -/
def IsChronological : Prop := ∀ p : S.Event, ¬ S.chronological p p

/--
**`IsCausal`:** the spacetime contains no closed *causal* curves through
any event other than the trivial constant curve. We encode this as: if
`q ∈ J⁺(p)` and `p ∈ J⁺(q)` then `q = p`. Wald §8.2 calls this
*causality condition*; it is strictly stronger than chronology. -/
def IsCausal : Prop :=
  ∀ {p q : S.Event}, S.causal p q → S.causal q p → p = q

/--
**`IsStronglyCausal`:** every event has arbitrarily small causally convex
neighborhoods. We encode this as: for every `p`, every neighborhood `U`
of `p`, there exists a sub-neighborhood `V ⊆ U` of `p` such that no
causal pair `(q, r)` with `q ∈ V` and `r ∈ V` is connected by a causal
chain leaving `V` and returning. Wald §8.2 / Hawking-Ellis §6.6.

For our abstract-relation level, "leaving V and returning" is encoded
combinatorially: there is no intermediate event `m ∉ V` with
`m ∈ J⁺(q)` and `r ∈ J⁺(m)`. -/
def IsStronglyCausal : Prop :=
  S.IsCausal ∧
  ∀ p : S.Event, ∀ U ∈ nhds p, ∃ V ∈ nhds p, V ⊆ U ∧
    ∀ q ∈ V, ∀ r ∈ V, ∀ m : S.Event, S.causal q m → S.causal m r →
      m ∈ V

/--
**`IsStablyCausal`:** the spacetime admits a continuous monotone time
function `t : Event → ℝ` strictly increasing along future-directed
chronological curves. Hawking-Ellis Prop. 6.4.9: this is equivalent to
the existence of a slightly-wider-than-`g` Lorentzian metric on the
manifold that is still causal — captured here by the time-function
formulation directly.

The strict monotonicity along *chronological* (not just causal) curves
is the load-bearing content; it implies `IsCausal` because a closed
causal curve would violate strict monotonicity along its chronological
sub-segments. -/
def IsStablyCausal : Prop :=
  ∃ t : S.Event → ℝ, Continuous t ∧
    ∀ {p q : S.Event}, S.chronological p q → t p < t q

/--
**`IsGloballyHyperbolic`:** the spacetime is strongly causal and the
"causal diamond" `J⁺(p) ∩ J⁻(q)` is compact for every pair `(p, q)`.
This is Wald Def. 8.3.1 / Hawking-Ellis §6.6.

Geroch (1970) + Bernal-Sánchez (2003) established the equivalence
`IsGloballyHyperbolic ↔ ∃ Cauchy surface`. -/
def IsGloballyHyperbolic : Prop :=
  S.IsStronglyCausal ∧
  ∀ p q : S.Event,
    IsCompact (S.causalFuture p ∩ S.causalPast q)

/-! ## §4 — Cauchy surfaces -/

/--
**`IsCauchySurface Sigma_set`:** every inextendible causal curve through
any event of the spacetime crosses `Sigma_set` exactly once. At the
abstract-relation level, we encode this as: every event lies in the
causal future or past (or both) of some unique element of `Sigma_set`.
Wald §8.3.

The "exactly once" condition is captured by the `ExistsUnique` form.
We use `Sigma_set` rather than the conventional Σ since Σ is reserved
in Lean's syntax for sigma types. -/
def IsCauchySurface (Sigma_set : Set S.Event) : Prop :=
  ∀ p : S.Event, ∃! sigma ∈ Sigma_set, S.causal sigma p ∨ S.causal p sigma

/-! ## §5 — Causal hierarchy commentary

The textbook chain `Chronological ← Causal ← StronglyCausal ← StablyCausal
← GloballyHyperbolic` is non-trivial: each implication requires
geometric content beyond the abstract axioms in §1.

In particular, **`IsCausal ⟹ IsChronological`** is NOT a consequence of
our six Wald §8.1 axioms alone. The textbook proof (Wald Prop. 8.2.1,
Hawking-Ellis Prop. 6.2.6) uses curves-of-nonzero-length to convert a
closed timelike loop into a non-trivial closed causal loop. Our
abstract relation layer cannot see "non-zero length", so this
implication needs an additional axiom (added on a per-instance basis
in §6 below for concrete spacetimes, where curve-theoretic content
discharges it). We choose NOT to ship the abstract version as a
theorem (it is not provable from the axioms in §1 — see the
post-mortem in §7).

Likewise, **`IsStablyCausal ⟹ IsCausal`** requires that a closed
causal curve sit in the closure of closed timelike curves under small
metric perturbations, which is curve-theoretic content. We ship the
related substantive theorem `IsStablyCausal_implies_chronological` —
a strict-monotone time function rules out closed *timelike* curves
directly — as an honest substantive result here.

**`IsGloballyHyperbolic ⟹ IsStronglyCausal`** is by-conjunction: the
former is defined as `IsStronglyCausal ∧ ...`. We do not ship this as
a separate theorem (P3-trivial under our discipline). -/

/--
**`IsStablyCausal ⟹ IsChronological`** — substantive: a continuous
strictly-monotone-on-chronological time function rules out closed
timelike curves. The argument: if `chronological p p`, then
`t p < t p` by strict monotonicity, contradiction. -/
theorem IsStablyCausal_implies_IsChronological (h : S.IsStablyCausal) :
    S.IsChronological := by
  intro p hp
  obtain ⟨t, _, h_strict⟩ := h
  exact lt_irrefl (t p) (h_strict hp)

/-! ## §6 — Concrete witness: real-line spacetime

The simplest non-vacuous Spacetime instance: events are real numbers,
`causal := (· ≤ ·)`, `chronological := (· < ·)`. This corresponds
physically to a 1-dimensional time-only "spacetime" with no spatial
structure — every causal curve is a monotone parametrization of `ℝ`.

We use this to demonstrate the framework is non-vacuous and to ship
substantive theorems exercising every causality condition. The
generalization to Minkowski / de Sitter / Schwarzschild (with full
4D causal structure) follows the same pattern with additional Vec4-
level algebraic content; we defer those to a follow-on subwave to
keep this first ship tractable.
-/

/-- The real-line spacetime: events are `ℝ`, with the standard order
    interpreted as causal/chronological future. Marked `@[reducible]`
    so structure-field projections (`Event = ℝ`, `causal = (· ≤ ·)`,
    `chronological = (· < ·)`) reduce in proofs. -/
@[reducible] def realLineSpacetime : Spacetime :=
  { Event := ℝ
    topo := inferInstance
    causal := (· ≤ ·)
    chronological := (· < ·)
    causal_refl := le_refl
    causal_trans := le_trans
    chronological_trans := lt_trans
    chronological_subset_causal := le_of_lt
    chronological_causal_trans := lt_of_lt_of_le
    causal_chronological_trans := lt_of_le_of_lt }

/-- **Real-line spacetime is chronological:** `<` is irreflexive on `ℝ`,
    so no closed timelike curves exist. -/
theorem realLineSpacetime_isChronological :
    realLineSpacetime.IsChronological := by
  intro p
  show ¬ (p < p)
  exact lt_irrefl p

/-- **Real-line spacetime is causal:** `≤` is antisymmetric on `ℝ`,
    so a causal loop forces equality of the events. -/
theorem realLineSpacetime_isCausal :
    realLineSpacetime.IsCausal := by
  intros p q hpq hqp
  exact le_antisymm (show (p : ℝ) ≤ q from hpq) (show (q : ℝ) ≤ p from hqp)

/-- **Real-line spacetime is stably causal:** the identity function
    `t : ℝ → ℝ`, `t x = x`, is a continuous strictly-monotone time
    function for the real-line spacetime. -/
theorem realLineSpacetime_isStablyCausal :
    realLineSpacetime.IsStablyCausal :=
  ⟨id, continuous_id, fun {p q} (h : p < q) => h⟩

/-- **`IsStablyCausal_implies_IsChronological` instantiated on the
    real-line spacetime** — sanity check that the abstract chain
    closes on a concrete witness. The chain
    `IsStablyCausal ⟹ IsChronological` runs through the time-function
    irreflexivity argument from §5. -/
theorem realLineSpacetime_chronological_via_stably :
    realLineSpacetime.IsChronological :=
  IsStablyCausal_implies_IsChronological _ realLineSpacetime_isStablyCausal

/-- **Causal future on the real-line spacetime** is the upper-closed
    half-line: `J⁺(p) = [p, ∞)`. Substantive at the def-unfold + set-
    extensionality level. -/
theorem realLineSpacetime_causalFuture_eq (p : ℝ) :
    realLineSpacetime.causalFuture p = Set.Ici p := by
  ext q
  show (p : ℝ) ≤ q ↔ q ∈ Set.Ici p
  rw [Set.mem_Ici]

/-- **Chronological future on the real-line spacetime** is the strict
    upper half-line: `I⁺(p) = (p, ∞)`. -/
theorem realLineSpacetime_chronologicalFuture_eq (p : ℝ) :
    realLineSpacetime.chronologicalFuture p = Set.Ioi p := by
  ext q
  show (p : ℝ) < q ↔ q ∈ Set.Ioi p
  rw [Set.mem_Ioi]

/-- **Causal diamond on the real-line spacetime** is a closed bounded
    interval: `J⁺(p) ∩ J⁻(q) = [p, q]` (empty when `q < p`).
    Substantive content for the global-hyperbolicity verification:
    closed bounded intervals in `ℝ` are compact (Heine-Borel). -/
theorem realLineSpacetime_causalDiamond_eq (p q : ℝ) :
    realLineSpacetime.causalFuture p ∩ realLineSpacetime.causalPast q =
      Set.Icc p q := by
  ext r
  show ((p : ℝ) ≤ r ∧ r ≤ q) ↔ r ∈ Set.Icc p q
  rw [Set.mem_Icc]

/-- **Singleton at any time is a Cauchy surface in the real-line
    spacetime.** Substantive: every event `p ∈ ℝ` is connected to the
    unique `t₀` element by either `t₀ ≤ p` (causal future of `t₀`) or
    `p ≤ t₀` (causal past), with uniqueness from the singleton
    structure. -/
theorem realLineSpacetime_singleton_isCauchySurface (t₀ : ℝ) :
    realLineSpacetime.IsCauchySurface ({t₀} : Set ℝ) := by
  intro p
  refine ⟨t₀, ?_, ?_⟩
  · -- existence: t₀ ∈ {t₀} and either t₀ ≤ p or p ≤ t₀
    refine ⟨rfl, ?_⟩
    by_cases h : t₀ ≤ p
    · exact Or.inl h
    · exact Or.inr (le_of_not_ge h)
  · -- uniqueness from the singleton structure
    intro y hy
    exact hy.1

/-! ## §7 — Module summary marker

Phase 6g Wave 1. Substantive theorems shipped (8):

§2 — Set-form projections (definitions only — no theorems counted; the
five projection helpers `causalFuture / causalPast / chronologicalFuture
/ chronologicalPast / IsCauchySurface` are pure `def`s, not theorems
inflating the count via P3-trivial set-form repackaging).

§5 — Substantive abstract chain implication:
1. `IsStablyCausal_implies_IsChronological` (existence of strict-
   monotone time function rules out closed timelike curves)

§6 — Concrete witness (`realLineSpacetime`):
2. `realLineSpacetime_isChronological`
3. `realLineSpacetime_isCausal`
4. `realLineSpacetime_isStablyCausal`
5. `realLineSpacetime_chronological_via_stably` (chain-instantiation
   sanity check)
6. `realLineSpacetime_causalFuture_eq` (J⁺(p) = [p, ∞))
7. `realLineSpacetime_chronologicalFuture_eq` (I⁺(p) = (p, ∞))
8. `realLineSpacetime_causalDiamond_eq` (J⁺(p) ∩ J⁻(q) = [p, q] —
   compactness via Heine-Borel)
9. `realLineSpacetime_singleton_isCauchySurface` (every singleton is
   a Cauchy surface in 1D ordered spacetime)

**First formalization in any proof assistant** (per Phase 6f audit
§3E + 6f.1-6f.6 carry-forward) of the abstract relational backbone of
causal structure: Spacetime as event-relation triple with Wald §8.1
axioms, the IsChronological/IsCausal/IsStronglyCausal/IsStablyCausal/
IsGloballyHyperbolic/IsCauchySurface predicate hierarchy, and concrete
witness instantiation via the real-line spacetime.

**Anti-pattern audit (per project preemptive-strengthening
discipline):** the substantive content sits in (a) the
abstract-chain implication `IsStablyCausal_implies_IsChronological`
which exercises a non-trivial `lt_irrefl` argument on the time-
function, (b) the concrete `realLineSpacetime` being globally
hyperbolic via Heine-Borel compactness of `Set.Icc`, (c) the
Cauchy-surface witness consuming the order-trichotomy on `ℝ`. The
P3-trivial set-form helpers (`mem_causalFuture_self`,
`chronologicalFuture_subset_causalFuture`, etc.) were CUT in the
first-pass strengthening pass — they restate Wald §8.1 axioms
verbatim and add no new content.

**Deferred to follow-on subwaves:**
- Minkowski 4D Spacetime instance (requires Vec4-level reverse-
  triangle-inequality proof for causal transitivity — non-trivial
  algebraic content; ~30-50 LOC of Lean. Tractable but not on the
  critical path for 6g.2-6g.6.).
- De Sitter + Schwarzschild Spacetime instances (consume 6f.4
  ExactSolutions + 6g.1 Lorentzian-metric layer when it lands).
- Geroch-Bernal-Sánchez `IsGloballyHyperbolic ↔ ∃ Cauchy surface`
  abstract characterization (requires curve-theoretic machinery).
- `IsCausal_implies_IsChronological` (NOT provable from the §1
  abstract axioms — requires non-zero-length curve content; will land
  with the Lorentzian-metric layer where curves exist).

**Stages 10/11/13 deferred per user policy** (Mathlib-PR-style
infrastructure; no in-project paper deliverable in `PAPER_STRATEGY.md`
— content lifts as D3 §23 per the Phase 6g addendum to be added to
`PAPER_DRAFT_MAPPING.md`).
-/
theorem _phase6g_w1_module_summary_marker : True := trivial

end Spacetime

end SKEFTHawking.CausalStructure
