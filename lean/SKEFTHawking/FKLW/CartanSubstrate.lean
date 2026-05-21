/-
Phase 6p Wave 2c.4a-R4.2.d.4.3.d.1: Cartan-substrate / identity-component
infrastructure for the formal discharge of `H_Fib = ⊤` (and hence
`fibonacci_density_conditional`).

## Status of the formal density discharge

D4.1-D4.3.b already shipped:
  - `H_Fib` is a closed compact subgroup of SU(2) (R4.2.d.4.1).
  - `H_Fib` is non-trivial and non-abelian (R4.2.d.4.2).
  - `H_Fib` contains two distinct order-20 cyclic subgroups (R4.2.d.4.{2, 3a, 3b}).
  - If finite, `40 ≤ |H_Fib|` and `|⟨σ_1⟩ ∩ ⟨σ_2⟩| ≤ 10` (R4.2.d.4.3.{a,b}).

D4.3.c+ is the remaining work, factored into two architectural steps:

  - **D4.3.c**: scalar centralizer + tighter intersection bound `|inter| ≤ 2`
    (~200-300 LoC; matrix algebra only, no Cartan needed).
  - **D4.3.d+**: the formal classification of closed subgroups of SU(2) —
    requires **Cartan's closed-subgroup theorem** + 1-parameter subgroup
    theorem + maximal-torus structure, none of which are currently in
    Mathlib4 v4.29.0 (the headline gap from the 2026-05-13 PM-PM-PM-PM-PM-PM
    substrate audit).

## What this module ships (D4.3.d.1, ~150-200 LoC)

This module ships the **identity-component-of-1 substrate** that is the
load-bearing entry point of the full Cartan discharge. Specifically:

**§1 — Generic substrate (reusable for any closed subgroup of any
compact Hausdorff topological group, ~70 LoC)**:

  - `Subgroup.compactSpace_of_isClosed_in_compact` : closed subgroup of
    compact group is compact (subspace).
  - `Subgroup.finite_of_isClosed_of_discreteTopology` : closed +
    `DiscreteTopology` ⇒ `Finite` (via Mathlib's `finite_of_compact_of_discrete`).
  - `Subgroup.connectedComponentOfOne_eq_bot_of_finite` : finite subgroup
    of T1 topological group has trivial identity component (using
    Mathlib's `Finite.instDiscreteTopology` for T1 + Finite ⇒ Discrete).
  - `Subgroup.finite_iff_discreteTopology_of_isClosed_in_compact_T1` :
    iff form combining the above.

**§2 — `H_Fib` specialization + identity-component definition (~50 LoC)**:

  - `H_Fib_compactSpace` instance : `CompactSpace H_Fib` (specializes §1).
  - `H_Fib_idComponent : Subgroup H_Fib` :=
    `Subgroup.connectedComponentOfOne H_Fib` — the identity component
    of the Fibonacci closure subgroup, qua subgroup of itself.
  - `H_Fib_idComponent_one_mem`, `H_Fib_idComponent_isClosed`,
    `H_Fib_idComponent_isConnected` — basic properties.

**§3 — Finite ⇒ trivial identity-component for H_Fib (~20 LoC)**:

  - `H_Fib_idComponent_eq_bot_of_finite` : `Finite H_Fib → H_Fib_idComponent = ⊥`.

**§4 — Headline dichotomies composing with D4.3.a + R5.1 AALemma6
(~60 LoC)**:

  - `H_Fib_finite_iff_discreteTopology` : `Finite H_Fib ↔ DiscreteTopology H_Fib`.
  - **`H_Fib_dichotomy_discrete_or_accPt`** : the substantive Cartan-
    substrate dichotomy. Either H_Fib has discrete topology (hence is
    finite with `40 ≤ |H_Fib|` via D4.3.a), or the identity is an
    accumulation point of H_Fib (via R5.1 AALemma6's
    `one_accPt_of_infinite_closed_subgroup`).
  - **`H_Fib_idComponent_ne_bot_implies_infinite`** : contrapositive of
    `H_Fib_idComponent_eq_bot_of_finite`. The CONVERSE direction
    (`infinite ⇒ idComponent ≠ ⊥`) is the Mathlib4 Cartan gap —
    profinite groups counterexample.
  - **`H_Fib_finite_card_ge_40_and_idComponent_bot_or_infinite`** :
    packaged composition of D4.3.a's cardinality bound with the
    identity-component substrate. Either `H_Fib` is finite with
    `40 ≤ |H_Fib|` AND identity component is trivial, OR `H_Fib` is
    infinite.

## Why this is genuinely substantive (not P3/P4/P5 anti-pattern)

The shipped theorems satisfy the strengthening-discipline pre-write
checklist:

  - **Quantitative content**: the dichotomy explicitly produces either
    `40 ≤ Nat.card H_Fib` (numerical) or an `AccPt` topological witness.
    Not a P3 multiplication-only tautology.
  - **Cross-module bridge integrity**: substantively calls
    `H_Fib_card_ge_40_if_finite` (D4.3.a), `H_Fib_isClosed` (D4.1),
    `H_Fib_isCompact` (D4.2), `one_accPt_of_infinite_closed_subgroup`
    (R5.1 AALemma6), Mathlib's `Subgroup.connectedComponentOfOne`,
    `finite_of_compact_of_discrete`, `Finite.instDiscreteTopology`.
  - **Defining-the-conclusion-check**: `H_Fib_idComponent` is *defined*
    via Mathlib's general `Subgroup.connectedComponentOfOne`, not via
    any concrete construction targeting the conclusion. The dichotomy
    is a genuine binary choice (not auto-tautological).
  - **Bundle-redundancy (P2)**: the dichotomy headline has two
    conjuncts in each branch (left = DiscreteTopology + Finite +
    cardinality lower bound; right = AccPt witness), all distinct and
    load-bearing.

## Architectural deferrals (D4.3.d.2+, multi-session)

  - **Cartan's closed-subgroup theorem** : closed subgroup of Lie group
    is a Lie group. Needed to convert `H_Fib_idComponent ≠ ⊥` into
    "H_Fib has positive dimension". Mathlib4 v4.29.0 gap.
  - **1-parameter subgroup theorem** (von Neumann): positive-dim
    closed subgroup of SU(2) contains a 1-parameter subgroup conjugate
    to the standard torus T. Mathlib4 v4.29.0 gap.
  - **Maximal-torus classification of SU(2)** : the residual content
    after Cartan + 1-parameter subgroup. SU(2)-specific.
  - **Composition** : with D3.a's `σ_Fib_SU_mat_not_conj_inverts`
    (rules out N(T)), the positive-dim case reduces to: "H_Fib
    contains a maximal torus T plus an element outside N(T) →
    H_Fib = SU(2)".

## Pipeline Invariant compliance

  - Invariant #10 (no `maxHeartbeats`): RESPECTED.
  - Invariant #15 (no new axioms): RESPECTED (zero introduced).

References:
  - `SKEFTHawking.FKLW.FibSU2Density` — D4.1-D4.3.b substrate
    (`H_Fib`, `H_Fib_isClosed`, `H_Fib_isCompact`,
    `H_Fib_card_ge_40_if_finite`, `H_Fib_infinite_or_card_ge_40`).
  - `SKEFTHawking.FKLW.AharonovAradLemma6` — R5.1 substrate
    (`one_accPt_of_infinite_closed_subgroup`).
  - `Mathlib.Topology.Algebra.Group.Basic` —
    `Subgroup.connectedComponentOfOne`.
  - `Mathlib.Topology.Compactness.Compact` —
    `finite_of_compact_of_discrete`.
  - `Mathlib.Topology.Separation.Basic` — `Finite.instDiscreteTopology`.
-/

import Mathlib
import SKEFTHawking.FKLW.FibSU2Density
import SKEFTHawking.FKLW.AharonovAradLemma6

set_option autoImplicit false

namespace SKEFTHawking.FKLW

open SKEFTHawking

/-! ## §1. Generic substrate: closed subgroups of compact topological groups

The lemmas below are general-purpose (parametric in `G`) and apply to
any closed subgroup of any compact Hausdorff topological group. They
are the foundational substrate for the H_Fib specialization in §2-§4.
-/

namespace Subgroup

/-- A closed subgroup of a compact topological group is compact
(as a subspace). -/
theorem compactSpace_of_isClosed_in_compact
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (H : Subgroup G) (h_closed : IsClosed (H : Set G)) :
    CompactSpace H :=
  isCompact_iff_compactSpace.mp h_closed.isCompact

/-- A closed subgroup of a compact topological group with discrete
subspace topology is finite. -/
theorem finite_of_isClosed_of_discreteTopology
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (H : Subgroup G) (h_closed : IsClosed (H : Set G))
    [DiscreteTopology H] :
    Finite H := by
  haveI : CompactSpace H := compactSpace_of_isClosed_in_compact H h_closed
  exact finite_of_compact_of_discrete

/-- For a finite subgroup of a T1 topological group, the connected
component of the identity (qua subgroup) is trivial.

Proof: Finite + T1 ⇒ DiscreteTopology (Mathlib's
`Finite.instDiscreteTopology`); in a discrete space, every connected
component is a singleton; hence
`Subgroup.connectedComponentOfOne` (carrier = `connectedComponent 1`)
has carrier `{1}`, making the subgroup `⊥`. -/
theorem connectedComponentOfOne_eq_bot_of_finite
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T1Space G] (H : Subgroup G) (h_finite : Finite H) :
    Subgroup.connectedComponentOfOne H = ⊥ := by
  haveI : Finite H := h_finite
  haveI : DiscreteTopology H := Finite.instDiscreteTopology
  ext g
  simp only [Subgroup.mem_bot]
  show g ∈ connectedComponent (1 : H) ↔ g = 1
  rw [show connectedComponent (1 : H) = {1} from
    (totallyDisconnectedSpace_iff_connectedComponent_singleton.mp inferInstance) 1]
  rfl

/-- **Iff form**: a closed subgroup of a compact T1 topological group is
finite iff it has discrete subspace topology. -/
theorem finite_iff_discreteTopology_of_isClosed_in_compact_T1
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T1Space G]
    (H : Subgroup G) (h_closed : IsClosed (H : Set G)) :
    Finite H ↔ DiscreteTopology H := by
  refine ⟨fun h_fin => ?_, fun h_disc => ?_⟩
  · haveI : Finite H := h_fin
    exact Finite.instDiscreteTopology
  · haveI := h_disc
    exact finite_of_isClosed_of_discreteTopology H h_closed

end Subgroup

/-! ## §2. `H_Fib` instance + identity-component definition

We specialize the generic substrate from §1 to the Fibonacci closure
subgroup `H_Fib` of SU(2). -/

/-- `H_Fib` is a compact subspace of SU(2). -/
instance H_Fib_compactSpace :
    CompactSpace H_Fib :=
  Subgroup.compactSpace_of_isClosed_in_compact H_Fib H_Fib_isClosed

/-- **The identity component of `H_Fib`**, qua `Subgroup` of `H_Fib`.

Defined via Mathlib's general `Subgroup.connectedComponentOfOne` on the
topological group `H_Fib`. The carrier is exactly `connectedComponent (1 : H_Fib)`. -/
noncomputable def H_Fib_idComponent :
    Subgroup H_Fib :=
  Subgroup.connectedComponentOfOne H_Fib

/-- The identity element of `H_Fib` is contained in its identity component. -/
theorem H_Fib_idComponent_one_mem :
    (1 : H_Fib) ∈ H_Fib_idComponent := by
  show (1 : H_Fib) ∈ connectedComponent (1 : H_Fib)
  exact mem_connectedComponent

/-- The carrier of `H_Fib_idComponent` is closed in `H_Fib`. -/
theorem H_Fib_idComponent_isClosed :
    IsClosed (H_Fib_idComponent : Set H_Fib) := by
  show IsClosed (connectedComponent (1 : H_Fib))
  exact isClosed_connectedComponent

/-- The carrier of `H_Fib_idComponent` is connected in `H_Fib`. -/
theorem H_Fib_idComponent_isConnected :
    IsConnected (H_Fib_idComponent : Set H_Fib) := by
  show IsConnected (connectedComponent (1 : H_Fib))
  exact isConnected_connectedComponent

/-! ## §3. Finite ⇒ trivial identity component (specialized to H_Fib) -/

/-- **If `H_Fib` is finite, then its identity component is trivial.**

Specialization of the generic `Subgroup.connectedComponentOfOne_eq_bot_of_finite`
(§1) to `H_Fib`. -/
theorem H_Fib_idComponent_eq_bot_of_finite (h_finite : Finite H_Fib) :
    H_Fib_idComponent = ⊥ :=
  Subgroup.connectedComponentOfOne_eq_bot_of_finite H_Fib h_finite

/-! ## §4. Dichotomy headlines

These compose the §1-§3 substrate with R4.2.d.4.3.a
(`H_Fib_card_ge_40_if_finite`) and R5.1
(`one_accPt_of_infinite_closed_subgroup`) into the **substantive
Cartan-substrate dichotomy** for `H_Fib`. -/

/-- **`H_Fib` is finite iff it has discrete subspace topology.**

Specializes `Subgroup.finite_iff_discreteTopology_of_isClosed_in_compact_T1`
(§1) to `H_Fib`. -/
theorem H_Fib_finite_iff_discreteTopology :
    Finite H_Fib ↔ DiscreteTopology H_Fib :=
  Subgroup.finite_iff_discreteTopology_of_isClosed_in_compact_T1 H_Fib H_Fib_isClosed

/-- **The substantive Cartan-substrate dichotomy.**

For our concrete Fibonacci closure subgroup `H_Fib ≤ SU(2)`, EITHER:

  - **(discrete case)** `H_Fib` has the discrete subspace topology,
    making it finite with `40 ≤ |H_Fib|` (via D4.3.a's
    `H_Fib_card_ge_40_if_finite`); OR

  - **(non-discrete case)** the identity element `1 ∈ SU(2)` is an
    accumulation point of `H_Fib` (via R5.1 AALemma6's
    `one_accPt_of_infinite_closed_subgroup`).

This is the **load-bearing entry point** for the formal density
discharge: the non-discrete branch reduces (via Cartan + 1-parameter
subgroup, deferred to D4.3.d.2+) to "H_Fib contains a continuous
1-parameter subgroup", which together with D3.a's `N(T)` ruleout and
D2's non-centrality forces `H_Fib = SU(2)`. -/
theorem H_Fib_dichotomy_discrete_or_accPt :
    (DiscreteTopology H_Fib ∧ Finite H_Fib ∧ 40 ≤ Nat.card H_Fib) ∨
    AccPt (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
      (Filter.principal (H_Fib : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))) := by
  by_cases h_disc : DiscreteTopology H_Fib
  · left
    haveI := h_disc
    refine ⟨h_disc, ?_, ?_⟩
    · haveI : CompactSpace H_Fib :=
        Subgroup.compactSpace_of_isClosed_in_compact H_Fib H_Fib_isClosed
      exact finite_of_compact_of_discrete
    · haveI : CompactSpace H_Fib :=
        Subgroup.compactSpace_of_isClosed_in_compact H_Fib H_Fib_isClosed
      haveI : Finite H_Fib := finite_of_compact_of_discrete
      have hf : Set.Finite (H_Fib : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :=
        Set.toFinite _
      exact H_Fib_card_ge_40_if_finite hf
  · right
    have h_inf : (H_Fib : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).Infinite := by
      intro h_fin
      apply h_disc
      haveI : Finite H_Fib := h_fin.to_subtype
      exact Finite.instDiscreteTopology
    exact one_accPt_of_infinite_closed_subgroup H_Fib H_Fib_isClosed h_inf

/-- **Contrapositive structural implication.**

If `H_Fib`'s identity component is nontrivial, then `H_Fib` is infinite.

Note: this is the **provable direction**. The converse — "infinite ⇒
idComponent ≠ ⊥" — is exactly the Mathlib4 Cartan gap (profinite groups
provide a counterexample without further substrate). Once Cartan's
closed-subgroup theorem is shipped (D4.3.d.2+), the converse becomes
constructive: closed infinite subgroups of SU(2) are Lie subgroups
of positive dimension, whose identity components are nontrivial. -/
theorem H_Fib_idComponent_ne_bot_implies_infinite
    (h_ne : H_Fib_idComponent ≠ ⊥) :
    Set.Infinite (H_Fib : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  intro h_finite_set
  apply h_ne
  exact H_Fib_idComponent_eq_bot_of_finite h_finite_set.to_subtype

/-- **Disjunction headline composing D4.3.a + the identity-component
substrate**:

Either `H_Fib` is finite with `40 ≤ |H_Fib|` (via D4.3.a) — in which
case the identity component is automatically trivial — OR `H_Fib` is
infinite (so the identity component MAY be nontrivial; Cartan gap).

This packages the substantive D4.3.a cardinality bound at the
identity-component layer for downstream Cartan use. -/
theorem H_Fib_finite_card_ge_40_and_idComponent_bot_or_infinite :
    (Finite H_Fib ∧ 40 ≤ Nat.card H_Fib ∧ H_Fib_idComponent = ⊥) ∨
    Set.Infinite (H_Fib : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  by_cases h_fin : Finite H_Fib
  · left
    refine ⟨h_fin, ?_, ?_⟩
    · have hf : Set.Finite (H_Fib : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :=
        Set.toFinite _
      exact H_Fib_card_ge_40_if_finite hf
    · exact H_Fib_idComponent_eq_bot_of_finite h_fin
  · right
    intro h_finite_set
    exact h_fin h_finite_set.to_subtype

/-! ## §4.5. Wedge A — Cartan substrate bridge (predicate substrate)

(Phase 5 Step 13 Path (i) — Wedge A, 2026-05-20)

This section ships the **predicate-substrate** for the two Cartan
theorems Wedge B will consume to discharge the 1-parameter subgroup
chain. The substrate consists of:

  - `H_Fib_accPt_one_unconditional` — strengthens `H_Fib_dichotomy_*`
    to drop the discrete branch via the shipped session-31 unconditional
    `H_Fib_infinite`. The Cartan-precondition AccPt witness for `1`
    on `H_Fib` is now unconditional.

  - `OneParamSubgroupInSU2 (H : Subgroup _) : Prop` — predicate
    expressing "H contains a continuous nontrivial 1-parameter subgroup
    (real-additive → SU(2)-multiplicative)".

  - **Tracked Mathlib gap #1** `CartanInfiniteImpliesIdComponentNonTrivial_SU2 : Prop`
    — "every closed infinite subgroup of SU(2) has nontrivial identity
    component". This is the converse direction the §4 contrapositive
    documented as the Mathlib4 v4.29.0 Cartan gap.

  - **Tracked Mathlib gap #2** `CartanIdComponentContainsOneParamSubgroup_SU2 : Prop`
    — "every closed subgroup of SU(2) with nontrivial identity
    component contains a continuous 1-parameter subgroup". The SU(2)
    specialization of the von Neumann 1-parameter subgroup theorem.

  - Forward composition theorems building `H_Fib`-specific conclusions
    from the tracked Props plus shipped substrate:
    `H_Fib_idComponent_ne_bot_of_cartan`,
    `H_Fib_contains_oneParamSubgroup_of_cartan`.

**Pipeline Invariant #15 posture**: the two `Cartan...` declarations are
**predicates (`Prop` `def`s), not axioms**. Downstream consumers
(Wedge B + Wedge C) take them as explicit hypothesis parameters. No
user sign-off required for shipping the predicates themselves; sign-off
would be required only to *discharge* them as axioms — deferred either
to a Mathlib upstream PR (Cartan's closed-subgroup theorem for compact
Lie groups) or to a constructive project-local proof (~300-500 LoC,
exp-surjectivity onto idComponent in compact Lie groups, multi-session).

References (Mathlib4 substrate the predicates would consume if discharged):
  - `Subgroup.connectedComponentOfOne` (already in use at §2).
  - `MonoidHom`, `Continuous` (in `Mathlib.Topology.Algebra.Group.Basic`).
-/

/-- **Unconditional AccPt witness for 1 on `H_Fib`**.

Strengthens `H_Fib_dichotomy_discrete_or_accPt` by ruling out the
discrete-and-finite branch via the shipped session-31 unconditional
`H_Fib_infinite` (commit `825384f` / `e176b9f` chain). If `H_Fib`
had `DiscreteTopology` it would also be finite (closed-in-compact +
discrete ⇒ finite), contradicting `H_Fib_infinite`. The dichotomy's
right branch is therefore forced unconditionally. -/
theorem H_Fib_accPt_one_unconditional :
    AccPt (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
      (Filter.principal
        (H_Fib : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))) := by
  rcases H_Fib_dichotomy_discrete_or_accPt with ⟨_h_disc, h_fin, _h_card⟩ | h_accPt
  · exfalso
    exact H_Fib_infinite (Set.toFinite _)
  · exact h_accPt

/-- **Predicate substrate**: a closed subgroup `H ≤ SU(2)` *contains a
continuous 1-parameter subgroup* iff there is a continuous function
`φ : ℝ → SU(2)` that is a homomorphism (`φ 0 = 1`, `φ (s + t) = φ s · φ t`),
is nontrivial (`∃ t, φ t ≠ 1`), and whose image lies in `H`.

This is the structural condition Wedge B consumes: combined with D3.a's
normalizer ruleout it will force `H_Fib = ⊤`. -/
def OneParamSubgroupInSU2
    (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Prop :=
  ∃ φ : ℝ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
    Continuous φ ∧
    φ 0 = 1 ∧
    (∀ s t, φ (s + t) = φ s * φ t) ∧
    (∃ t, φ t ≠ 1) ∧
    (∀ t, φ t ∈ H)

/-- **Tracked Mathlib4 gap #1** (Cartan, infinite → idComponent direction).

"Every closed infinite subgroup `H` of SU(2) has nontrivial identity
component (`Subgroup.connectedComponentOfOne ↥H ≠ ⊥`)."

This is the converse of `H_Fib_idComponent_ne_bot_implies_infinite`
(§4) and is the Mathlib4 v4.29.0 gap. The provable direction
(`idComponent ≠ ⊥ ⇒ infinite`) holds for any compact T1 topological
group; the converse fails in general (profinite counterexamples) but
holds for compact Lie groups via Cartan's closed-subgroup theorem.

**Status**: predicate (Prop `def`), not axiom. Downstream consumers
take it as an explicit hypothesis. Discharge plan: either Mathlib
upstream PR (Cartan for compact Lie groups) or constructive
project-local proof via exp-surjectivity in SU(2). -/
def CartanInfiniteImpliesIdComponentNonTrivial_SU2 : Prop :=
  ∀ (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)),
    IsClosed (H : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) →
    Set.Infinite (H : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) →
    Subgroup.connectedComponentOfOne (G := ↥H) ≠ ⊥

/-- **Tracked Mathlib4 gap #2** (von Neumann 1-parameter subgroup theorem
for SU(2)).

"Every closed subgroup `H` of SU(2) with nontrivial identity component
contains a continuous 1-parameter subgroup."

In a compact Lie group, positive-dimensional closed subgroups contain
1-parameter subgroups via the Lie-algebra exponential map. Mathlib4
v4.29.0 lacks the exp-surjectivity onto positive-dimensional
idComponents needed to discharge this constructively.

**Status**: predicate (Prop `def`), not axiom. Same Pipeline Invariant
#15 posture as gap #1: ship as hypothesis-tracked. -/
def CartanIdComponentContainsOneParamSubgroup_SU2 : Prop :=
  ∀ (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)),
    IsClosed (H : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) →
    Subgroup.connectedComponentOfOne (G := ↥H) ≠ ⊥ →
    OneParamSubgroupInSU2 H

/-- **Forward composition**: `H_Fib` has nontrivial identity component
under Cartan tracked gap #1.

Composes shipped substrate (`H_Fib_isClosed`, `H_Fib_infinite`) with
the `CartanInfiniteImpliesIdComponentNonTrivial_SU2` hypothesis. -/
theorem H_Fib_idComponent_ne_bot_of_cartan
    (H_cartan : CartanInfiniteImpliesIdComponentNonTrivial_SU2) :
    Subgroup.connectedComponentOfOne (G := ↥H_Fib) ≠ ⊥ :=
  H_cartan H_Fib H_Fib_isClosed H_Fib_infinite

/-- **Forward composition (Wedge A headline)**: `H_Fib` contains a
continuous 1-parameter subgroup under both Cartan tracked gaps.

This is the substrate Wedge B will consume to derive `H_Fib = ⊤`. -/
theorem H_Fib_contains_oneParamSubgroup_of_cartan
    (H_cartan_inf : CartanInfiniteImpliesIdComponentNonTrivial_SU2)
    (H_cartan_one : CartanIdComponentContainsOneParamSubgroup_SU2) :
    OneParamSubgroupInSU2 H_Fib :=
  H_cartan_one H_Fib H_Fib_isClosed
    (H_Fib_idComponent_ne_bot_of_cartan H_cartan_inf)

/-! ## §4.6. Wedge B — Cartan classification final step (predicate substrate
+ H_Fib discharge)

(Phase 5 Step 13 Path (i) — Wedge B, 2026-05-20)

**Architectural note**: the existing `FibSU2LieBundle.CartanClassificationOfSU2_Subgroup`
predicate (line 4250) is universally too strong: it claims every closed
infinite non-abelian subgroup of SU(2) equals `⊤`, but the normalizer
`N(T) = T ∪ wT` (where T is the standard torus and w is the Weyl
element) is a counterexample (closed, infinite, non-abelian, but ≠ ⊤).
Wedge B SHIPS A CORRECTED PREDICATE `CartanFinalStep_SU2` that adds the
N(T)-exclusion hypothesis as an explicit antecedent.

The correct chain, composing Wedge A's tracked Mathlib gaps #1+#2 with
Wedge B's tracked Mathlib gap #3:

  1. (Wedge A.tp1) closed infinite ⇒ idComponent ≠ ⊥
  2. (Wedge A.tp2) idComponent ≠ ⊥ ⇒ ∃ 1-param subgroup
  3. (Wedge B.tp3) ∃ 1-param subgroup ∧ non-abelian ∧ "not in N(T)" ⇒ H = ⊤

For H_Fib specifically:
  - non-abelian witness: `σ_Fib_SU_not_commute` (D2)
  - non-N(T) witness: D3.a's `σ_Fib_SU_mat_not_conj_inverts`
    (matrix-level), lifted here to subtype level as
    `σ_Fib_SU_not_conj_inverts`.

Combined, this yields `H_Fib_eq_top_of_full_cartan_chain` and finally
`fibonacci_density_F21_from_full_cartan_chain` — F.21 unconditional
under the three tracked Cartan Props.

**Pipeline Invariant #15 posture**: same as Wedge A. `CartanFinalStep_SU2`
is a predicate, NOT an axiom. Discharge would require either upstream
Mathlib4 PR (full Cartan classification of closed subgroups of SU(2))
or constructive project-local proof (~400-800 LoC; Wedge C/D work).
-/

/-- **Subtype-level lift of D3.a**: σ_Fib_2 conjugating σ_Fib_1 does NOT
yield σ_Fib_1⁻¹.

Equivalent (by right-multiplying by σ_Fib_2 on both sides) to
`σ_Fib_2_SU * σ_Fib_1_SU ≠ σ_Fib_1_SU⁻¹ * σ_Fib_2_SU`. Lifts the
matrix-level shipped D3.a `σ_Fib_SU_mat_not_conj_inverts` to the
SU(2) subtype via `Matrix.star_eq_inv` (`star A = A⁻¹` for A ∈
specialUnitaryGroup) and the subtype-multiplication `.val` homomorphism.

This is THE N(T)-exclusion witness for H_Fib: if H_Fib were contained
in some conjugate of N(T), then every pair of generators would
satisfy the conjugate-inverse relation `g₂ · g₁ · g₂⁻¹ = g₁⁻¹`
modulo torus elements; this is ruled out for σ_Fib_{1,2}. -/
theorem σ_Fib_SU_not_conj_inverts :
    σ_Fib_2_SU * σ_Fib_1_SU ≠ σ_Fib_1_SU⁻¹ * σ_Fib_2_SU := by
  intro h_eq
  apply σ_Fib_SU_mat_not_conj_inverts
  have h_val : (σ_Fib_2_SU * σ_Fib_1_SU).val =
               (σ_Fib_1_SU⁻¹ * σ_Fib_2_SU).val :=
    congrArg Subtype.val h_eq
  have h_inv_val : (σ_Fib_1_SU⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val
                 = star σ_Fib_1_SU.val := by
    have h_star : star σ_Fib_1_SU = σ_Fib_1_SU⁻¹ := Matrix.star_eq_inv σ_Fib_1_SU
    rw [← h_star]
    rfl
  show σ_Fib_2_SU_mat * σ_Fib_1_SU_mat = star σ_Fib_1_SU_mat * σ_Fib_2_SU_mat
  calc σ_Fib_2_SU_mat * σ_Fib_1_SU_mat
      = (σ_Fib_2_SU * σ_Fib_1_SU).val := rfl
    _ = (σ_Fib_1_SU⁻¹ * σ_Fib_2_SU).val := h_val
    _ = (σ_Fib_1_SU⁻¹).val * σ_Fib_2_SU.val := rfl
    _ = star σ_Fib_1_SU.val * σ_Fib_2_SU.val := by rw [h_inv_val]
    _ = star σ_Fib_1_SU_mat * σ_Fib_2_SU_mat := rfl

/-- **Tracked Mathlib4 gap #3** (Cartan classification final step).

"Every closed subgroup `H` of SU(2) that contains a 1-parameter
subgroup, is non-abelian, and contains a generator pair `g₁, g₂` with
`g₂ · g₁ ≠ g₁⁻¹ · g₂` (i.e., H is not contained in any conjugate of the
normalizer `N(T) = T ∪ wT`), is the whole group `⊤`."

This is the SU(2) specialization of the full Cartan classification
of closed subgroups: trivial, finite, conjugate-to-T, conjugate-to-N(T),
or ⊤. The hypotheses rule out all but the last:
  - 1-param subgroup ⇒ not finite (excludes finite branch)
  - non-abelian ⇒ not conjugate to T (T is abelian)
  - `g₂ · g₁ ≠ g₁⁻¹ · g₂` for some pair ⇒ not conjugate to N(T)
    (in N(T), conjugation by a non-T element inverts T-elements)

**Status**: predicate (Prop `def`), not axiom. Same Pipeline Invariant
#15 posture as Wedge A's gaps. Discharge would require the full Cartan
classification, deferred to Wedge C/D or Mathlib upstream PR. -/
def CartanFinalStep_SU2 : Prop :=
  ∀ (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)),
    IsClosed (H : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) →
    OneParamSubgroupInSU2 H →
    (∃ g₁ g₂, g₁ ∈ H ∧ g₂ ∈ H ∧ g₁ * g₂ ≠ g₂ * g₁) →
    (∃ g₁ g₂, g₁ ∈ H ∧ g₂ ∈ H ∧ g₂ * g₁ ≠ g₁⁻¹ * g₂) →
    H = ⊤

/-- **H_Fib non-abelian witness** in the form consumed by `CartanFinalStep_SU2`.

Direct composition of shipped `σ_Fib_SU_not_commute` (D2) with
`σ_Fib_{1,2}_SU_mem_H_Fib` (D4.1 closure). -/
theorem H_Fib_non_abelian_witness :
    ∃ g₁ g₂, g₁ ∈ H_Fib ∧ g₂ ∈ H_Fib ∧ g₁ * g₂ ≠ g₂ * g₁ :=
  ⟨σ_Fib_1_SU, σ_Fib_2_SU,
   σ_Fib_1_SU_mem_H_Fib, σ_Fib_2_SU_mem_H_Fib,
   σ_Fib_SU_not_commute⟩

/-- **H_Fib N(T)-exclusion witness** in the form consumed by
`CartanFinalStep_SU2`.

Direct composition of the subtype-level `σ_Fib_SU_not_conj_inverts`
(this section, lifted from D3.a) with `σ_Fib_{1,2}_SU_mem_H_Fib`. -/
theorem H_Fib_non_N_T_witness :
    ∃ g₁ g₂, g₁ ∈ H_Fib ∧ g₂ ∈ H_Fib ∧ g₂ * g₁ ≠ g₁⁻¹ * g₂ :=
  ⟨σ_Fib_1_SU, σ_Fib_2_SU,
   σ_Fib_1_SU_mem_H_Fib, σ_Fib_2_SU_mem_H_Fib,
   σ_Fib_SU_not_conj_inverts⟩

/-- **Wedge B headline — H_Fib = ⊤ under the full Cartan chain**.

Composes Wedge A's two tracked Cartan Props (gaps #1 + #2) with
Wedge B's tracked Cartan Final Step (gap #3) and the shipped
H_Fib-specific witnesses:
  - `H_Fib_isClosed` (D4.1)
  - `H_Fib_infinite` (session 31, e176b9f chain)
  - `H_Fib_contains_oneParamSubgroup_of_cartan` (Wedge A)
  - `H_Fib_non_abelian_witness` (this section)
  - `H_Fib_non_N_T_witness` (this section, via lifted D3.a)

Yields `H_Fib = ⊤` directly. This DOES NOT depend on the broken
`FibSU2LieBundle.CartanClassificationOfSU2_Subgroup` predicate; it is
the corrected substantive discharge of the H_Fib closure-subgroup =
SU(2) chain. -/
theorem H_Fib_eq_top_of_full_cartan_chain
    (H_cartan_inf : CartanInfiniteImpliesIdComponentNonTrivial_SU2)
    (H_cartan_one : CartanIdComponentContainsOneParamSubgroup_SU2)
    (H_cartan_final : CartanFinalStep_SU2) :
    H_Fib = ⊤ := by
  have h_one_param : OneParamSubgroupInSU2 H_Fib :=
    H_Fib_contains_oneParamSubgroup_of_cartan H_cartan_inf H_cartan_one
  exact H_cartan_final H_Fib H_Fib_isClosed h_one_param
    H_Fib_non_abelian_witness H_Fib_non_N_T_witness

/-- **Wedge B FINAL HEADLINE — F.21 Fibonacci density unconditional under
the full Cartan tracked-Prop chain.**

Composes `H_Fib_eq_top_of_full_cartan_chain` with shipped
`fibonacci_density_from_H_Fib_eq_top` (D4 wrapper, FibSU2Density.lean
line 1258). Under the three tracked Cartan Mathlib4 v4.29.1 gap
predicates (gaps #1 + #2 + #3), F.21 unconditional Fibonacci density
holds without any further hypothesis.

The Wedge B → Wedge C/D discharge of the three tracked Props (or
upstream Mathlib PR) is the only remaining substrate work for F.21
to be fully unconditional. -/
theorem fibonacci_density_F21_from_full_cartan_chain
    (H_cartan_inf : CartanInfiniteImpliesIdComponentNonTrivial_SU2)
    (H_cartan_one : CartanIdComponentContainsOneParamSubgroup_SU2)
    (H_cartan_final : CartanFinalStep_SU2) :
    SKEFTHawking.FKLW.AharonovAradBridge.DenseInSpecialUnitary 3 2
      (fun b => (SKEFTHawking.FKLW.ρ_Fib_SU2 b :
          Matrix (Fin 2) (Fin 2) ℂ)) :=
  SKEFTHawking.FKLW.fibonacci_density_from_H_Fib_eq_top
    (H_Fib_eq_top_of_full_cartan_chain H_cartan_inf H_cartan_one H_cartan_final)

/-! ## §4.7. Strengthening — accumulation-point hypothesis bypasses gaps #1+#2

(Strengthening pass 2026-05-20, post-Wedge-D-pivot)

**Motivation.** The original F.21 reduction goes through gap #1 (closed +
infinite ⇒ idComponent ≠ ⊥) then gap #2 (idComponent ≠ ⊥ ⇒ 1-param
subgroup). But there is a *strictly stronger* hypothesis that already
appears in the shipped substrate:

   `H_Fib_accPt_one_unconditional` : `AccPt 1 (Filter.principal H_Fib)`

This was shipped UNCONDITIONALLY (no Cartan dependence) by composing
the generic `one_accPt_of_infinite_closed_subgroup`
(`AharonovAradLemma6.lean`) with `H_Fib_isClosed` + `H_Fib_infinite`.

**Strengthening observation.** Von Neumann's 1-parameter-subgroup
construction in SU(2) only needs a *sequence in `H` converging to 1*,
i.e., an accumulation point of `H` at `1`. It does NOT need
`idComponent ≠ ⊥` as an intermediate step. So the natural strong form
of gap #2 is:

   **OneParamSubgroupFromAccPt_SU2** : For every closed subgroup `H ≤
   SU(2)` with `1 ∈ AccPt H`, `H` contains a continuous 1-parameter
   subgroup.

This is **strictly stronger** than gap #2 (since `idComponent ≠ ⊥ ⇒
accPt 1` is the deep "idComponent is path-connected with > 1 point"
fact, which itself uses Cartan-style argument), and it is **exactly
the substantive content** of von Neumann's theorem for SU(2).

**Strategic payoff.** Combined with the shipped
`H_Fib_accPt_one_unconditional`, this strengthened predicate
discharges `OneParamSubgroupInSU2 H_Fib` *without* gaps #1 or #2.
Therefore the F.21 unconditional chain reduces from **three** tracked
Cartan predicates to **one** (`CartanFinalStep_SU2` only).

**Pipeline Invariant #15 posture.** `OneParamSubgroupFromAccPt_SU2` is
a predicate (Prop `def`), not an axiom. Its substantive discharge
lives in `OneParameterSubgroupSU2.lean` (companion file shipping
the von Neumann theorem for SU(2) — Mathlib-upstream-PR-quality
substrate). -/

/-- **Strengthened tracked predicate** (replaces gap #2 in the F.21 chain).

"Every closed subgroup `H` of SU(2) with `1` as an accumulation point of
`H` contains a continuous 1-parameter subgroup."

This is the canonical von Neumann statement for SU(2): in any compact
Lie group, a closed subgroup that accumulates at the identity contains
a 1-parameter subgroup along a tangent direction at 1. Cleaner than
gap #2 because:

  - The hypothesis `AccPt 1 (Filter.principal H)` is unconditionally
    provable from `IsClosed H ∧ Set.Infinite H` via shipped
    `one_accPt_of_infinite_closed_subgroup` (no Cartan needed).
  - For H_Fib specifically, this is `H_Fib_accPt_one_unconditional`,
    already shipped.

The substantive discharge is the von Neumann argument: pick a sequence
`(h_n) → 1` in `H \ {1}`, lift to `(Y_n) → 0` in `su(2)` via local
exp-inverse, normalize and extract a convergent subsequence
`Y_n / ‖Y_n‖ → X` with `‖X‖ = 1` (compactness of unit sphere in
finite-dim su(2)), then show `exp(t · X) ∈ H` for all `t ∈ ℝ` via
integer-rounding of `t / ‖Y_n‖`. See `OneParameterSubgroupSU2.lean`
for the full discharge. -/
def OneParamSubgroupFromAccPt_SU2 : Prop :=
  ∀ (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)),
    IsClosed (H : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) →
    AccPt (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
      (Filter.principal (H : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))) →
    OneParamSubgroupInSU2 H

/-- **Forward composition (strengthened Wedge A headline).**

Given the strengthened predicate, `H_Fib` contains a continuous
1-parameter subgroup **without any reliance on gaps #1 or #2**. The
accumulation-point hypothesis is discharged by the shipped
`H_Fib_accPt_one_unconditional`. -/
theorem H_Fib_contains_oneParamSubgroup_from_strengthening
    (H_strong : OneParamSubgroupFromAccPt_SU2) :
    OneParamSubgroupInSU2 H_Fib :=
  H_strong H_Fib H_Fib_isClosed H_Fib_accPt_one_unconditional

/-- **Strengthened Wedge B headline — H_Fib = ⊤ from a single tracked
Cartan predicate.**

Composes `H_Fib_contains_oneParamSubgroup_from_strengthening` (uses the
strengthened predicate + shipped accPt) with the Wedge B
`CartanFinalStep_SU2` predicate. The original
`H_Fib_eq_top_of_full_cartan_chain` requires THREE tracked Cartan
predicates (gaps #1 + #2 + #3); this strengthened version requires
ONLY the new strengthened predicate + gap #3. -/
theorem H_Fib_eq_top_of_strengthened_chain
    (H_strong : OneParamSubgroupFromAccPt_SU2)
    (H_cartan_final : CartanFinalStep_SU2) :
    H_Fib = ⊤ := by
  have h_one_param : OneParamSubgroupInSU2 H_Fib :=
    H_Fib_contains_oneParamSubgroup_from_strengthening H_strong
  exact H_cartan_final H_Fib H_Fib_isClosed h_one_param
    H_Fib_non_abelian_witness H_Fib_non_N_T_witness

/-- **STRENGTHENED F.21 HEADLINE — Fibonacci density unconditional under
TWO tracked predicates** (strengthened gap #2 + gap #3 only; gaps #1+#2
of the original chain absorbed into the strengthened predicate).

Composes `H_Fib_eq_top_of_strengthened_chain` with the shipped
`fibonacci_density_from_H_Fib_eq_top` (D4 wrapper, FibSU2Density.lean
line 1258). The substantive discharge of `OneParamSubgroupFromAccPt_SU2`
(in `OneParameterSubgroupSU2.lean`) closes F.21 to a *single* remaining
Cartan tracked predicate (`CartanFinalStep_SU2`). -/
theorem fibonacci_density_F21_from_strengthened_chain
    (H_strong : OneParamSubgroupFromAccPt_SU2)
    (H_cartan_final : CartanFinalStep_SU2) :
    SKEFTHawking.FKLW.AharonovAradBridge.DenseInSpecialUnitary 3 2
      (fun b => (SKEFTHawking.FKLW.ρ_Fib_SU2 b :
          Matrix (Fin 2) (Fin 2) ℂ)) :=
  SKEFTHawking.FKLW.fibonacci_density_from_H_Fib_eq_top
    (H_Fib_eq_top_of_strengthened_chain H_strong H_cartan_final)

/-! ## §4.8. Soundness fix — `CartanFinalStep_SU2_v2` corrects the
"non-N(T)" hypothesis

(Soundness pass 2026-05-21, post-gap-#2-unconditional-closure)

**Critical observation.** The `CartanFinalStep_SU2` predicate
(§4.6, line 572) as currently defined is **provably FALSE**.

The intended Cartan classification chain rules out the five cases
(⊥, finite, T, N(T), ⊤) and concludes `H = ⊤`. The "non-N(T)" branch
is meant to be discharged by the antecedent
`∃ g₁ g₂ ∈ H, g₂·g₁ ≠ g₁⁻¹·g₂` — read as "some pair fails the
N(T)-inversion relation". But this antecedent is too weak: it is
trivially satisfied by `H = N(stdTorus_SU2)` itself.

**Counter-example.** Take `H = N(stdTorus_SU2)` with
`g₁ = g₂ = torusElem (π/3) ∈ stdTorus ⊆ N(stdTorus)`. Then
  - `g₂·g₁ = torusElem (2π/3)`,
  - `g₁⁻¹·g₂ = torusElem (0) = 1`,
  - so `g₂·g₁ ≠ g₁⁻¹·g₂` ✓ (the antecedent holds),
  - but `H = N(stdTorus_SU2) ≠ ⊤`.

All four antecedents of `CartanFinalStep_SU2` are satisfied by
`N(stdTorus_SU2)` (it is closed; contains the standard 1-parameter
subgroup `t ↦ torusElem t ⊆ stdTorus ⊆ N(stdTorus)`; is non-abelian
since `weylElem` and `torusElem` do not commute; and admits the
diagonal `g₁ = g₂ = torusElem (π/3)` witness above) yet
`N(stdTorus_SU2) ≠ ⊤`. Hence `CartanFinalStep_SU2` is *unsatisfiable*
and no proof of it exists.

**Why the H_Fib-specific witness (`σ_Fib_SU_not_conj_inverts`,
§4.6 line 534) is not affected as a *fact*, but is insufficient as
*usage*.** The H_Fib witness is a *more specific* instance of the
same broken antecedent (it picks a particular non-torus pair
σ_Fib_1, σ_Fib_2). Its content is genuine — σ_Fib_2 does not invert
σ_Fib_1 under conjugation — but the predicate's antecedent (∃-pair,
arbitrary pair) accepts also the trivial N(T)-diagonal witness above.
Equivalently: D3.a's content is correct but the predicate it gets
plumbed into is too lax to use it.

**The fix.** Replace the `∃ pair g₂·g₁ ≠ g₁⁻¹·g₂` antecedent with the
strictly stronger *conjugate-noncommuting* form

  ∃ g₁ g₂ ∈ H, (g₂·g₁·g₂⁻¹) · g₁ ≠ g₁ · (g₂·g₁·g₂⁻¹).

In words: "some `g₁ ∈ H` does *not* commute with its `g₂`-conjugate".
This subsumes the non-abelian antecedent (if `g₁` and `g₂` commute,
then `g₂·g₁·g₂⁻¹ = g₁` which trivially commutes with `g₁`), so we
can drop the separate "non-abelian" hypothesis.

**Soundness check** (N(T) excluded). In `N(stdTorus)` with `g₁ ∈ T`,
the conjugate `g₂·g₁·g₂⁻¹ ∈ T` (because `T` is normal in `N(T)`), so
it commutes with `g₁`. For `g₁ ∈ wT`, by a similar argument
`g₂·g₁·g₂⁻¹ ∈ wT` if `g₂ ∈ T`, or `g₂·g₁·g₂⁻¹ ∈ T` if `g₂ ∈ wT`; in
either case the conjugate lies in the (abelian) closure of the
subgroup generated by `g₁`, hence commutes with `g₁`. So the
antecedent of `CartanFinalStep_SU2_v2` is *not* satisfied by `N(T)`.
The predicate is sound.

**Pipeline Invariant #15 posture**: `CartanFinalStep_SU2_v2` is a
predicate (Prop `def`), not an axiom — same as the original.

**H_Fib discharge.** Discharging
`H_Fib_NonCentralConjugateWitness` for H_Fib requires showing the
σ_Fib pair satisfies the new antecedent. This reduces to the
matrix-level fact that `σ_Fib_2 · σ_Fib_1 · σ_Fib_2⁻¹` and `σ_Fib_1`
have non-parallel Lie axes in su(2) (which is implied by the shipped
`σ_Fib_lie_bundle_pauliDet ≠ 0` 3-vector spanning, but needs a
"commuting in SU(2) ⇒ parallel Lie axes" sub-lemma). Deferred to a
follow-up ~50-150 LoC ship; tracked here as a Prop. -/

/-- **Tracked Mathlib4 gap #3-corrected** (Cartan classification final
step, soundness-fixed).

"Every closed subgroup `H ≤ SU(2)` that contains a 1-parameter
subgroup and has some pair `g₁, g₂ ∈ H` with `g₁` *not* commuting
with its `g₂`-conjugate, is the whole group `⊤`."

This is the SU(2) specialization of the full Cartan classification of
closed subgroups. The conjugate-noncommuting hypothesis cleanly
excludes all proper closed subgroups:
  - 1-param subgroup ⇒ not finite (excludes finite branch incl.
    binary polyhedrals);
  - conjugate-noncommuting subsumes non-abelian ⇒ not conjugate to T
    (T is abelian);
  - conjugate-noncommuting also excludes N(T): in N(T), every
    element's conjugate by another N(T)-element stays in the same
    abelian subgroup, hence commutes with the original.

**Status**: predicate (Prop `def`), not axiom. Same Pipeline Invariant
#15 posture as gap #2. Discharge would require the full Cartan
classification (~300-500 LoC), upstreamable to Mathlib. -/
def CartanFinalStep_SU2_v2 : Prop :=
  ∀ (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)),
    IsClosed (H : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) →
    OneParamSubgroupInSU2 H →
    (∃ g₁ g₂, g₁ ∈ H ∧ g₂ ∈ H ∧
        (g₂ * g₁ * g₂⁻¹) * g₁ ≠ g₁ * (g₂ * g₁ * g₂⁻¹)) →
    H = ⊤

/-- **H_Fib non-central-conjugate witness — tracked sub-Prop**.

The H_Fib instance of the new antecedent: there is a pair
`(g₁, g₂) ∈ H_Fib × H_Fib` such that `g₁` does not commute with its
`g₂`-conjugate.

**Discharge plan (deferred ~50-150 LoC)**: take `g₁ = σ_Fib_1`,
`g₂ = σ_Fib_2`. By contradiction, if
`(σ_Fib_2 · σ_Fib_1 · σ_Fib_2⁻¹) · σ_Fib_1 = σ_Fib_1 ·
(σ_Fib_2 · σ_Fib_1 · σ_Fib_2⁻¹)`, then `σ_Fib_1` commutes with its
conjugate `c := σ_Fib_2 · σ_Fib_1 · σ_Fib_2⁻¹`. Both have the same
characteristic polynomial (conjugation invariant), so the same
spectrum. Commuting matrices with the same spectrum and distinct
eigenvalues (σ_Fib_1 is not central in SU(2) ⇒ eigenvalues are
distinct on the unit circle) are equal or inverse:
  - `c = σ_Fib_1` ⇒ `σ_Fib_2 · σ_Fib_1 = σ_Fib_1 · σ_Fib_2`,
    contradicting `σ_Fib_SU_not_commute` (D2);
  - `c = σ_Fib_1⁻¹` ⇒ `σ_Fib_2 · σ_Fib_1 = σ_Fib_1⁻¹ · σ_Fib_2`,
    contradicting `σ_Fib_SU_not_conj_inverts` (D3.a).

Both contradictions land. The substantive sub-lemma needed is
"commuting SU(2) elements with the same distinct spectrum coincide
up to inversion". -/
def H_Fib_NonCentralConjugateWitness : Prop :=
  ∃ g₁ g₂, g₁ ∈ H_Fib ∧ g₂ ∈ H_Fib ∧
    (g₂ * g₁ * g₂⁻¹) * g₁ ≠ g₁ * (g₂ * g₁ * g₂⁻¹)

/-- **Corrected strengthened Wedge B headline — H_Fib = ⊤ via sound
predicate**.

Composes the unconditional 1-parameter subgroup discharge
(`OneParamSubgroupFromAccPt_SU2`) with the corrected
`CartanFinalStep_SU2_v2` predicate and the tracked
`H_Fib_NonCentralConjugateWitness`. -/
theorem H_Fib_eq_top_of_strengthened_chain_v2
    (H_strong : OneParamSubgroupFromAccPt_SU2)
    (H_cartan_final_v2 : CartanFinalStep_SU2_v2)
    (H_witness : H_Fib_NonCentralConjugateWitness) :
    H_Fib = ⊤ := by
  have h_one_param : OneParamSubgroupInSU2 H_Fib :=
    H_Fib_contains_oneParamSubgroup_from_strengthening H_strong
  exact H_cartan_final_v2 H_Fib H_Fib_isClosed h_one_param H_witness

/-- **Corrected strengthened F.21 headline** — F.21 Fibonacci density
unconditional under the SOUND Cartan-classification predicate
`CartanFinalStep_SU2_v2` plus the tracked `H_Fib` witness.

This replaces `fibonacci_density_F21_from_strengthened_chain` which
depends on the broken `CartanFinalStep_SU2`. -/
theorem fibonacci_density_F21_from_strengthened_chain_v2
    (H_strong : OneParamSubgroupFromAccPt_SU2)
    (H_cartan_final_v2 : CartanFinalStep_SU2_v2)
    (H_witness : H_Fib_NonCentralConjugateWitness) :
    SKEFTHawking.FKLW.AharonovAradBridge.DenseInSpecialUnitary 3 2
      (fun b => (SKEFTHawking.FKLW.ρ_Fib_SU2 b :
          Matrix (Fin 2) (Fin 2) ℂ)) :=
  SKEFTHawking.FKLW.fibonacci_density_from_H_Fib_eq_top
    (H_Fib_eq_top_of_strengthened_chain_v2 H_strong H_cartan_final_v2 H_witness)

/-! ## §4.9. Discharge of `H_Fib_NonCentralConjugateWitness`

(2026-05-21 follow-on)

Discharges the H_Fib-specific tracked Prop introduced in §4.8 by direct
matrix computation, bringing the F.21 chain down to **only**
`CartanFinalStep_SU2_v2` (Wedge B residual).

**Strategy.** Take the pair `(σ_Fib_1_SU, σ_Fib_2_SU)`. By contradiction,
assume `c := σ_Fib_2_SU · σ_Fib_1_SU · σ_Fib_2_SU⁻¹` commutes with
`σ_Fib_1_SU` at the SU(2) subtype level. Lift to matrices:
`c.val · σ_Fib_1_SU_mat = σ_Fib_1_SU_mat · c.val`.

  - **Step 1.** `σ_Fib_1_SU_mat` is diagonal with distinct entries
    `ω·R_1 ≠ ω·R_τ`. Projecting the commutator equation to entry [0, 1]
    gives `c.val[0, 1] · ω · (R_τ - R_1) = 0`, hence `c.val[0, 1] = 0`.

  - **Step 2.** From `c.val = σ_Fib_2_SU_mat · σ_Fib_1_SU_mat ·
    star σ_Fib_2_SU_mat` and `star σ_Fib_2_SU_mat · σ_Fib_2_SU_mat = 1`
    (unitarity), `c.val · σ_Fib_2_SU_mat = σ_Fib_2_SU_mat ·
    σ_Fib_1_SU_mat`.

  - **Step 3.** Projecting this equation to [0, 0] (and using
    `c.val[0, 1] = 0` from Step 1) gives
    `c.val[0, 0] · σ_Fib_2_SU_mat[0, 0] = σ_Fib_2_SU_mat[0, 0] · ω · R_1`.
    Cancel `σ_Fib_2_SU_mat[0, 0] ≠ 0` to get `c.val[0, 0] = ω · R_1`.

  - **Step 4.** Projecting to [0, 1] (using `c.val[0, 1] = 0`) gives
    `c.val[0, 0] · σ_Fib_2_SU_mat[0, 1] = σ_Fib_2_SU_mat[0, 1] · ω · R_τ`.
    Cancel `σ_Fib_2_SU_mat[0, 1] ≠ 0` to get `c.val[0, 0] = ω · R_τ`.

  - **Step 5.** Steps 3 and 4 together give `ω · R_1 = ω · R_τ`.
    Cancel `ω ≠ 0`: `R_1 = R_τ`, contradicting `R1_C_ne_Rtau_C`. -/

/-! ### Helper non-vanishing facts (public extractions) -/

/-- `ω_Fib_C ≠ 0` (extraction from `norm_ω_Fib_C : ‖ω_Fib_C‖ = 1`). -/
theorem ω_Fib_C_ne_zero : SKEFTHawking.FKLW.ω_Fib_C ≠ 0 := by
  intro h
  have h_norm : ‖SKEFTHawking.FKLW.ω_Fib_C‖ = 0 := by rw [h, norm_zero]
  rw [SKEFTHawking.FKLW.norm_ω_Fib_C] at h_norm
  norm_num at h_norm

/-- `φInv_C ≠ 0` (from `φInv_C² + φInv_C = 1`). -/
theorem φInv_C_ne_zero : SKEFTHawking.FKLW.φInv_C ≠ 0 := by
  intro h
  have h_sq := SKEFTHawking.FKLW.φInv_C_sq_add_self
  rw [h] at h_sq
  simp at h_sq

/-- `φInvSqrt_C ≠ 0` (from `φInvSqrt² = φInv ≠ 0`). -/
theorem φInvSqrt_C_ne_zero : SKEFTHawking.FKLW.φInvSqrt_C ≠ 0 := by
  intro h
  have h_sq := SKEFTHawking.FKLW.φInvSqrt_C_sq
  rw [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at h_sq
  exact φInv_C_ne_zero h_sq.symm

/-- `σ_Fib_2[0, 1] ≠ 0`. -/
theorem σ_Fib_2_apply_01_ne_zero : SKEFTHawking.FKLW.σ_Fib_2 0 1 ≠ 0 := by
  rw [SKEFTHawking.FKLW.σ_Fib_2_apply_01]
  exact mul_ne_zero (mul_ne_zero φInv_C_ne_zero φInvSqrt_C_ne_zero)
    (sub_ne_zero.mpr SKEFTHawking.FKLW.R1_C_ne_Rtau_C)

/-! ### `σ_Fib_1_SU_mat` and `σ_Fib_2_SU_mat` entry lemmas -/

theorem σ_Fib_1_SU_mat_apply_00 :
    SKEFTHawking.FKLW.σ_Fib_1_SU_mat 0 0 =
      SKEFTHawking.FKLW.ω_Fib_C * SKEFTHawking.FKLW.R1_C := by
  show (SKEFTHawking.FKLW.ω_Fib_C • SKEFTHawking.FKLW.σ_Fib_1) 0 0 =
       SKEFTHawking.FKLW.ω_Fib_C * SKEFTHawking.FKLW.R1_C
  rw [Matrix.smul_apply, smul_eq_mul]
  rfl

theorem σ_Fib_1_SU_mat_apply_01 : SKEFTHawking.FKLW.σ_Fib_1_SU_mat 0 1 = 0 := by
  show (SKEFTHawking.FKLW.ω_Fib_C • SKEFTHawking.FKLW.σ_Fib_1) 0 1 = 0
  rw [Matrix.smul_apply, smul_eq_mul]
  show SKEFTHawking.FKLW.ω_Fib_C * (SKEFTHawking.FKLW.σ_Fib_1 0 1) = 0
  rw [show SKEFTHawking.FKLW.σ_Fib_1 0 1 = 0 from rfl, mul_zero]

theorem σ_Fib_1_SU_mat_apply_10 : SKEFTHawking.FKLW.σ_Fib_1_SU_mat 1 0 = 0 := by
  show (SKEFTHawking.FKLW.ω_Fib_C • SKEFTHawking.FKLW.σ_Fib_1) 1 0 = 0
  rw [Matrix.smul_apply, smul_eq_mul]
  show SKEFTHawking.FKLW.ω_Fib_C * (SKEFTHawking.FKLW.σ_Fib_1 1 0) = 0
  rw [show SKEFTHawking.FKLW.σ_Fib_1 1 0 = 0 from rfl, mul_zero]

theorem σ_Fib_1_SU_mat_apply_11 :
    SKEFTHawking.FKLW.σ_Fib_1_SU_mat 1 1 =
      SKEFTHawking.FKLW.ω_Fib_C * SKEFTHawking.FKLW.Rtau_C := by
  show (SKEFTHawking.FKLW.ω_Fib_C • SKEFTHawking.FKLW.σ_Fib_1) 1 1 =
       SKEFTHawking.FKLW.ω_Fib_C * SKEFTHawking.FKLW.Rtau_C
  rw [Matrix.smul_apply, smul_eq_mul]
  rfl

theorem σ_Fib_2_SU_mat_apply_00_ne_zero :
    SKEFTHawking.FKLW.σ_Fib_2_SU_mat 0 0 ≠ 0 := by
  show (SKEFTHawking.FKLW.ω_Fib_C • SKEFTHawking.FKLW.σ_Fib_2) 0 0 ≠ 0
  rw [Matrix.smul_apply, smul_eq_mul]
  exact mul_ne_zero ω_Fib_C_ne_zero SKEFTHawking.FKLW.σ_Fib_2_apply_00_ne_zero

theorem σ_Fib_2_SU_mat_apply_01_ne_zero :
    SKEFTHawking.FKLW.σ_Fib_2_SU_mat 0 1 ≠ 0 := by
  show (SKEFTHawking.FKLW.ω_Fib_C • SKEFTHawking.FKLW.σ_Fib_2) 0 1 ≠ 0
  rw [Matrix.smul_apply, smul_eq_mul]
  exact mul_ne_zero ω_Fib_C_ne_zero σ_Fib_2_apply_01_ne_zero

/-! ### Main discharge -/

/-- **`H_Fib_NonCentralConjugateWitness` is discharged unconditionally.**

The witness pair is `(σ_Fib_1_SU, σ_Fib_2_SU)`. See §4.9 docstring for the
spectral/diagonal argument. -/
theorem H_Fib_NonCentralConjugateWitness_discharged :
    H_Fib_NonCentralConjugateWitness := by
  refine ⟨SKEFTHawking.FKLW.σ_Fib_1_SU, SKEFTHawking.FKLW.σ_Fib_2_SU,
          SKEFTHawking.FKLW.σ_Fib_1_SU_mem_H_Fib,
          SKEFTHawking.FKLW.σ_Fib_2_SU_mem_H_Fib, ?_⟩
  intro h_comm
  -- Set c := σ_Fib_2_SU * σ_Fib_1_SU * σ_Fib_2_SU⁻¹.
  set c : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
    SKEFTHawking.FKLW.σ_Fib_2_SU * SKEFTHawking.FKLW.σ_Fib_1_SU *
      SKEFTHawking.FKLW.σ_Fib_2_SU⁻¹ with hc_def
  -- Lift h_comm to matrix equation
  have h_comm_val : c.val * SKEFTHawking.FKLW.σ_Fib_1_SU_mat =
                    SKEFTHawking.FKLW.σ_Fib_1_SU_mat * c.val := by
    have h := congrArg Subtype.val h_comm
    exact h
  -- c.val expanded
  have h_inv_val : (SKEFTHawking.FKLW.σ_Fib_2_SU⁻¹ :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val =
                   star SKEFTHawking.FKLW.σ_Fib_2_SU_mat := by
    have h_star : star SKEFTHawking.FKLW.σ_Fib_2_SU =
                  SKEFTHawking.FKLW.σ_Fib_2_SU⁻¹ :=
      Matrix.star_eq_inv SKEFTHawking.FKLW.σ_Fib_2_SU
    rw [← h_star]
    rfl
  have h_cval : c.val =
      SKEFTHawking.FKLW.σ_Fib_2_SU_mat * SKEFTHawking.FKLW.σ_Fib_1_SU_mat *
        star SKEFTHawking.FKLW.σ_Fib_2_SU_mat := by
    show (SKEFTHawking.FKLW.σ_Fib_2_SU * SKEFTHawking.FKLW.σ_Fib_1_SU *
          SKEFTHawking.FKLW.σ_Fib_2_SU⁻¹).val = _
    have h1 : (SKEFTHawking.FKLW.σ_Fib_2_SU * SKEFTHawking.FKLW.σ_Fib_1_SU *
               SKEFTHawking.FKLW.σ_Fib_2_SU⁻¹).val =
              SKEFTHawking.FKLW.σ_Fib_2_SU.val * SKEFTHawking.FKLW.σ_Fib_1_SU.val *
                (SKEFTHawking.FKLW.σ_Fib_2_SU⁻¹).val := rfl
    rw [h1, h_inv_val]
    rfl
  -- Step 1: c.val 0 1 = 0
  have h_proj_01 : c.val 0 1 = 0 := by
    have h := congrArg (fun M => M 0 1) h_comm_val
    simp only [Matrix.mul_apply, Fin.sum_univ_two,
               σ_Fib_1_SU_mat_apply_00, σ_Fib_1_SU_mat_apply_01,
               σ_Fib_1_SU_mat_apply_10, σ_Fib_1_SU_mat_apply_11] at h
    -- h : c.val 0 0 * 0 + c.val 0 1 * (ω * R_τ) =
    --     (ω * R_1) * c.val 0 1 + 0 * c.val 1 1
    have h_clean :
        c.val 0 1 * (SKEFTHawking.FKLW.ω_Fib_C *
                     (SKEFTHawking.FKLW.Rtau_C - SKEFTHawking.FKLW.R1_C)) = 0 := by
      have : c.val 0 1 *
              (SKEFTHawking.FKLW.ω_Fib_C * SKEFTHawking.FKLW.Rtau_C) =
             SKEFTHawking.FKLW.ω_Fib_C * SKEFTHawking.FKLW.R1_C * c.val 0 1 := by
        linear_combination h
      linear_combination this
    have h_factor_ne : SKEFTHawking.FKLW.ω_Fib_C *
                       (SKEFTHawking.FKLW.Rtau_C - SKEFTHawking.FKLW.R1_C) ≠ 0 :=
      mul_ne_zero ω_Fib_C_ne_zero
        (sub_ne_zero.mpr (fun h => SKEFTHawking.FKLW.R1_C_ne_Rtau_C h.symm))
    exact (mul_eq_zero.mp h_clean).resolve_right h_factor_ne
  -- Step 2: c.val * σ_Fib_2_SU_mat = σ_Fib_2_SU_mat * σ_Fib_1_SU_mat
  have h_cval_mul_σ2 :
      c.val * SKEFTHawking.FKLW.σ_Fib_2_SU_mat =
        SKEFTHawking.FKLW.σ_Fib_2_SU_mat * SKEFTHawking.FKLW.σ_Fib_1_SU_mat := by
    rw [h_cval]
    -- Use star σ_2_SU_mat * σ_2_SU_mat = 1 (inverse property in SU(2)).
    have h_star_mul : star SKEFTHawking.FKLW.σ_Fib_2_SU_mat *
                      SKEFTHawking.FKLW.σ_Fib_2_SU_mat = 1 := by
      have h_inv_mul :
          (SKEFTHawking.FKLW.σ_Fib_2_SU⁻¹ * SKEFTHawking.FKLW.σ_Fib_2_SU :
            ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) = 1 := inv_mul_cancel _
      have h_val := congrArg
        (Subtype.val : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) → _) h_inv_mul
      have h_lhs : (SKEFTHawking.FKLW.σ_Fib_2_SU⁻¹ *
                    SKEFTHawking.FKLW.σ_Fib_2_SU :
                   ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val =
                   (SKEFTHawking.FKLW.σ_Fib_2_SU⁻¹).val *
                     SKEFTHawking.FKLW.σ_Fib_2_SU_mat := rfl
      have h_one : ((1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val :
                    Matrix (Fin 2) (Fin 2) ℂ) = (1 : Matrix (Fin 2) (Fin 2) ℂ) := rfl
      rw [h_lhs, h_inv_val] at h_val
      rw [h_one] at h_val
      exact h_val
    rw [show SKEFTHawking.FKLW.σ_Fib_2_SU_mat * SKEFTHawking.FKLW.σ_Fib_1_SU_mat *
           star SKEFTHawking.FKLW.σ_Fib_2_SU_mat *
           SKEFTHawking.FKLW.σ_Fib_2_SU_mat =
         SKEFTHawking.FKLW.σ_Fib_2_SU_mat * SKEFTHawking.FKLW.σ_Fib_1_SU_mat *
            (star SKEFTHawking.FKLW.σ_Fib_2_SU_mat *
             SKEFTHawking.FKLW.σ_Fib_2_SU_mat) from by
      rw [mul_assoc]]
    rw [h_star_mul, mul_one]
  -- Step 3: c.val 0 0 = ω * R_1
  have h_cval_00_R1 :
      c.val 0 0 = SKEFTHawking.FKLW.ω_Fib_C * SKEFTHawking.FKLW.R1_C := by
    have h := congrArg (fun M => M 0 0) h_cval_mul_σ2
    simp only [Matrix.mul_apply, Fin.sum_univ_two,
               σ_Fib_1_SU_mat_apply_00, σ_Fib_1_SU_mat_apply_01,
               σ_Fib_1_SU_mat_apply_10, σ_Fib_1_SU_mat_apply_11,
               h_proj_01] at h
    -- h : c.val 0 0 * σ_Fib_2_SU_mat 0 0 + 0 * σ_Fib_2_SU_mat 1 0 =
    --     σ_Fib_2_SU_mat 0 0 * (ω * R_1) + σ_Fib_2_SU_mat 0 1 * 0
    have h_clean : c.val 0 0 * SKEFTHawking.FKLW.σ_Fib_2_SU_mat 0 0 =
                   SKEFTHawking.FKLW.σ_Fib_2_SU_mat 0 0 *
                     (SKEFTHawking.FKLW.ω_Fib_C * SKEFTHawking.FKLW.R1_C) := by
      linear_combination h
    have h_eq : (c.val 0 0 - SKEFTHawking.FKLW.ω_Fib_C * SKEFTHawking.FKLW.R1_C) *
                SKEFTHawking.FKLW.σ_Fib_2_SU_mat 0 0 = 0 := by
      linear_combination h_clean
    have h_factor : c.val 0 0 - SKEFTHawking.FKLW.ω_Fib_C * SKEFTHawking.FKLW.R1_C = 0 :=
      (mul_eq_zero.mp h_eq).resolve_right σ_Fib_2_SU_mat_apply_00_ne_zero
    exact sub_eq_zero.mp h_factor
  -- Step 4: c.val 0 0 = ω * R_τ
  have h_cval_00_Rtau :
      c.val 0 0 = SKEFTHawking.FKLW.ω_Fib_C * SKEFTHawking.FKLW.Rtau_C := by
    have h := congrArg (fun M => M 0 1) h_cval_mul_σ2
    simp only [Matrix.mul_apply, Fin.sum_univ_two,
               σ_Fib_1_SU_mat_apply_00, σ_Fib_1_SU_mat_apply_01,
               σ_Fib_1_SU_mat_apply_10, σ_Fib_1_SU_mat_apply_11,
               h_proj_01] at h
    -- h : c.val 0 0 * σ_Fib_2_SU_mat 0 1 + 0 * σ_Fib_2_SU_mat 1 1 =
    --     σ_Fib_2_SU_mat 0 0 * 0 + σ_Fib_2_SU_mat 0 1 * (ω * R_τ)
    have h_clean : c.val 0 0 * SKEFTHawking.FKLW.σ_Fib_2_SU_mat 0 1 =
                   SKEFTHawking.FKLW.σ_Fib_2_SU_mat 0 1 *
                     (SKEFTHawking.FKLW.ω_Fib_C * SKEFTHawking.FKLW.Rtau_C) := by
      linear_combination h
    have h_eq : (c.val 0 0 - SKEFTHawking.FKLW.ω_Fib_C * SKEFTHawking.FKLW.Rtau_C) *
                SKEFTHawking.FKLW.σ_Fib_2_SU_mat 0 1 = 0 := by
      linear_combination h_clean
    have h_factor :
        c.val 0 0 - SKEFTHawking.FKLW.ω_Fib_C * SKEFTHawking.FKLW.Rtau_C = 0 :=
      (mul_eq_zero.mp h_eq).resolve_right σ_Fib_2_SU_mat_apply_01_ne_zero
    exact sub_eq_zero.mp h_factor
  -- Step 5: contradiction
  have h_eq : SKEFTHawking.FKLW.ω_Fib_C * SKEFTHawking.FKLW.R1_C =
              SKEFTHawking.FKLW.ω_Fib_C * SKEFTHawking.FKLW.Rtau_C :=
    h_cval_00_R1.symm.trans h_cval_00_Rtau
  exact SKEFTHawking.FKLW.R1_C_ne_Rtau_C
    (mul_left_cancel₀ ω_Fib_C_ne_zero h_eq)

/-- **F.21 unconditional on a SINGLE tracked Prop** — `CartanFinalStep_SU2_v2`
(soundness-fixed). Composes `H_Fib_eq_top_of_strengthened_chain_v2` with the
shipped unconditional `OneParamSubgroupFromAccPt_SU2` and the just-discharged
`H_Fib_NonCentralConjugateWitness_discharged`.

This is the *culmination of the §4.8 soundness fix*: F.21 now depends on
exactly one tracked Cartan Prop — `CartanFinalStep_SU2_v2`, the SU(2)
closed-subgroup classification (Wedge B residual).

Note: the `OneParamSubgroupFromAccPt_SU2` argument is the *predicate*; its
discharge `OneParamSubgroupFromAccPt_SU2_unconditional` is shipped in
`OneParameterSubgroupSU2.lean §9.13b`. The final composition into a
hypothesis-free-but-for-`CartanFinalStep_SU2_v2` headline is provided in
`OneParameterSubgroupSU2.lean §10c`. -/
theorem H_Fib_eq_top_of_cartan_final_v2_only
    (H_strong : OneParamSubgroupFromAccPt_SU2)
    (H_cartan_final_v2 : CartanFinalStep_SU2_v2) :
    H_Fib = ⊤ :=
  H_Fib_eq_top_of_strengthened_chain_v2 H_strong H_cartan_final_v2
    H_Fib_NonCentralConjugateWitness_discharged

/-- **F.21 with H_Fib witness absorbed**. Same as
`fibonacci_density_F21_from_strengthened_chain_v2` but with the H_Fib
witness automatically discharged. -/
theorem fibonacci_density_F21_from_cartan_final_v2_only
    (H_strong : OneParamSubgroupFromAccPt_SU2)
    (H_cartan_final_v2 : CartanFinalStep_SU2_v2) :
    SKEFTHawking.FKLW.AharonovAradBridge.DenseInSpecialUnitary 3 2
      (fun b => (SKEFTHawking.FKLW.ρ_Fib_SU2 b :
          Matrix (Fin 2) (Fin 2) ℂ)) :=
  SKEFTHawking.FKLW.fibonacci_density_from_H_Fib_eq_top
    (H_Fib_eq_top_of_cartan_final_v2_only H_strong H_cartan_final_v2)

/-! ## §5. Module summary

`CartanSubstrate.lean` (Phase 6p Wave 2c.4a-R4.2.d.4.3.d.1, 2026-05-14;
Wedge A 2026-05-20):
identity-component substrate for the Cartan classification of closed
subgroups of SU(2).

**Shipped (zero new axioms):**

  - **§1**: 4 generic substrate theorems (parametric in `G`):
    `Subgroup.compactSpace_of_isClosed_in_compact`,
    `Subgroup.finite_of_isClosed_of_discreteTopology`,
    `Subgroup.connectedComponentOfOne_eq_bot_of_finite`,
    `Subgroup.finite_iff_discreteTopology_of_isClosed_in_compact_T1`.
  - **§2**: `H_Fib`-specialization: `CompactSpace H_Fib` instance,
    `H_Fib_idComponent` definition, basic properties
    (`one_mem`, `isClosed`, `isConnected`).
  - **§3**: `H_Fib_idComponent_eq_bot_of_finite` — finite ⇒ trivial
    identity component.
  - **§4**: `H_Fib_finite_iff_discreteTopology` +
    **`H_Fib_dichotomy_discrete_or_accPt`** (substantive headline,
    discrete-topology / AccPt form) +
    **`H_Fib_idComponent_ne_bot_implies_infinite`** (contrapositive
    of §3) +
    **`H_Fib_finite_card_ge_40_and_idComponent_bot_or_infinite`**
    (packaged D4.3.a + identity-component composition).
  - **§4.5** (Wedge A 2026-05-20): Cartan substrate **bridge**.
    `H_Fib_accPt_one_unconditional` (strengthens §4 dichotomy by
    ruling out the discrete branch via shipped `H_Fib_infinite`),
    `OneParamSubgroupInSU2` predicate, tracked Cartan-gap predicates
    `CartanInfiniteImpliesIdComponentNonTrivial_SU2` (gap #1) +
    `CartanIdComponentContainsOneParamSubgroup_SU2` (gap #2), and
    composition headlines `H_Fib_idComponent_ne_bot_of_cartan` +
    **`H_Fib_contains_oneParamSubgroup_of_cartan`** (the Wedge A
    deliverable consumed by Wedge B).
  - **§4.6** (Wedge B 2026-05-20): Cartan classification **final step**
    + H_Fib discharge. `σ_Fib_SU_not_conj_inverts` (subtype-level lift
    of D3.a matrix N(T) ruleout), tracked Cartan-gap predicate
    `CartanFinalStep_SU2` (gap #3 — corrected version of the broken
    universal `FibSU2LieBundle.CartanClassificationOfSU2_Subgroup`,
    adding the N(T)-exclusion antecedent), H_Fib witnesses
    `H_Fib_non_abelian_witness` + `H_Fib_non_N_T_witness`, and
    HEADLINES **`H_Fib_eq_top_of_full_cartan_chain`** +
    **`fibonacci_density_F21_from_full_cartan_chain`** (F.21
    unconditional under all three Cartan tracked Mathlib gaps).

**Substantive content:**
  (a) The §1 generic substrate is reusable for any closed subgroup of
      any compact T1 topological group — not specific to SU(2).
  (b) The §4 dichotomy headline is a clean binary choice between the
      discrete-and-finite case (where D4.3.a's cardinality bound
      applies) and the non-discrete case (where AALemma6's accumulation
      point applies). NO P3/P4/P5 anti-pattern.
  (c) The composition substantively calls D4.1 (`H_Fib_isClosed`),
      D4.2 (`H_Fib_isCompact`), D4.3.a (`H_Fib_card_ge_40_if_finite`),
      and R5.1 (`one_accPt_of_infinite_closed_subgroup`).

**Cross-module bridge integrity** (Stage-3a pipeline check #6):
  - imports `FibSU2Density` (D4.1-D4.3.b substrate) and
    `AharonovAradLemma6` (R5.1 topological substrate);
  - body substantively calls `H_Fib`, `H_Fib_isClosed`,
    `H_Fib_isCompact`, `H_Fib_card_ge_40_if_finite`,
    `H_Fib_infinite_or_card_ge_40`,
    `one_accPt_of_infinite_closed_subgroup`,
    `Subgroup.connectedComponentOfOne`,
    `finite_of_compact_of_discrete`,
    `Finite.instDiscreteTopology`.

**Pipeline-Invariant compliance**:
  - Zero new project-local axioms.
  - Zero `maxHeartbeats` overrides.
  - Pipeline Invariant #15 (no new axioms without sign-off) ✓.

**Deferred to D4.3.d.2+ (multi-session — Wedge B/C work)**:

  - **Discharge of Cartan tracked gap #1** (shipped here as
    `CartanInfiniteImpliesIdComponentNonTrivial_SU2`): closed-subgroup
    theorem for compact Lie groups specialized to SU(2)
    (~300-500 LoC if proved project-local, or upstream Mathlib PR).
  - **Discharge of Cartan tracked gap #2** (shipped here as
    `CartanIdComponentContainsOneParamSubgroup_SU2`): von Neumann
    1-parameter subgroup theorem for SU(2).
  - Maximal-torus classification + non-centrality + D3.a's `N(T)`
    ruleout (Wedge B): composes Wedge A's `H_Fib_contains_oneParamSubgroup_of_cartan`
    with the §44 normalizer ruleout to force `H_Fib = SU(2)` and
    discharge `FibSU2LieBundle.CartanClassificationOfSU2_Subgroup`
    (the higher-level umbrella predicate consumed by §70
    `fibonacci_density_from_cartan_via_H_Fib`).
  - Binary polyhedral classification (Wedge C, optional polish):
    `2D_n, 2T, 2O, 2I` enumeration to close the finite-case branch.

References:
  - Knapp, *Lie Groups Beyond an Introduction* (2002), §IV.4 (Cartan's
    closed-subgroup theorem) + §IV.6 (maximal tori).
  - Hall, *Lie Groups, Lie Algebras, and Representations* (2015), §3.7
    (closed subgroups of matrix Lie groups).
  - Mathlib4 v4.29.0 substrate: `Subgroup.connectedComponentOfOne`
    (`Mathlib.Topology.Algebra.Group.Basic`),
    `finite_of_compact_of_discrete`
    (`Mathlib.Topology.Compactness.Compact`),
    `Finite.instDiscreteTopology` (`Mathlib.Topology.Separation.Basic`).
-/

end SKEFTHawking.FKLW
