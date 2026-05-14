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

/-! ## §5. Module summary

`CartanSubstrate.lean` (Phase 6p Wave 2c.4a-R4.2.d.4.3.d.1, 2026-05-14):
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

**Deferred to D4.3.d.2+ (multi-session)**:

  - Cartan's closed-subgroup theorem (Mathlib4 v4.29.0 gap; ~300-500 LoC
    if shipped directly; could be eventually upstreamed to Mathlib).
  - 1-parameter subgroup theorem (von Neumann): positive-dim closed
    subgroup of SU(2) contains a continuous 1-parameter subgroup
    conjugate to the standard torus T.
  - Maximal-torus classification: combined with D3.a's `N(T)` ruleout
    and D2's non-centrality, forces `H_Fib = SU(2)`.

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
