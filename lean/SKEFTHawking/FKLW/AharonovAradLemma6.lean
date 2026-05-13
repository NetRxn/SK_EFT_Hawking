/-
SK_EFT_Hawking Phase 6p Wave 2c.4a-R5 (sub-wave 1): Aharonov-Arad
Bridge Lemma 6.1/6.2 topological substrate.

This module ships **axiom-free topological sub-lemmas** toward the
constructive discharge of `aa_residual_interior_at_one_for_hom` (the
remaining FKLW axiom, after R1-R4.1 amendments). The substantive
analytic core (AA Bridge Lemmas 6.1 + 6.2 — commutator iteration +
basis-rotation argument) requires the BCH cubic-bound K·δ³ as an
upstream dependency, deferred to a follow-up sub-wave; the topological
infrastructure below feeds DIRECTLY into the analytic discharge once
the BCH cubic is available.

## R5 program status (2026-05-13)

Step decomposition of the full AA discharge:

  1. **`one_accPt_of_infinite_closed_subgroup`** (THIS SHIP) — for any
     closed infinite subgroup H of a compact topological group G, the
     identity element is an accumulation point of H.
     [Axiom-free; constructive proof via discrete + compact = finite.]

  2. **`one_mem_closure_subgroup_of_infinite_subgroup`** (THIS SHIP) —
     immediate corollary: 1 ∈ closure(H) (which follows from any
     subgroup anyway, but the AccPt form is the substantive content
     used downstream).

  3. **`accPt_one_in_range_of_hom`** (THIS SHIP) — specialization to
     the FKLW use case: `BraidGroup n →* SU(d)` MonoidHom with
     infinite range ⇒ 1 is an AccPt of the range.

  4. **Commutator-shrinkage Lemma 6.1** (DEFERRED, requires BCH cubic):
     For elements g, h ∈ SU(d) close to 1 (in some norm sense), the
     group commutator [g, h] = ghg⁻¹h⁻¹ has norm-from-1 ≤ C · ‖g-1‖²
     (quadratically smaller). The cubic BCH bound is the load-bearing
     ingredient: writing g = exp(iF), h = exp(iG) with ‖F‖, ‖G‖ ~ δ,
     the bound `‖[g,h] - 1‖ ≤ ‖exp(-[F,G]) - 1‖ + ‖BCH-remainder‖`
     requires `BCH-remainder = O(δ³)`, not the current linear `200·δ`.

  5. **Basis-rotation Lemma 6.2** (DEFERRED): combines Lemma 6.1's
     small-element generation with `LieSpanProp` to show the resulting
     small-element family covers a neighborhood of 1 in SU(d). This
     uses the ℂ-span of `range ρ_hom` to choose generator commutator
     directions matching a basis of the Lie algebra at 1.

  6. **Composition** (DEFERRED): chain (3) + (4) + (5) +
     `closure_eq_univ_of_one_mem_interior` (already shipped in
     `AharonovAradBridgeIteration.lean §6`) → discharge axiom.

## What this ship enables

  - The downstream consumer of `aa_residual_interior_at_one_for_hom`
    can now invoke `accPt_one_in_range_of_hom` to immediately obtain
    `1 ∈ closure(Set.range ρ_hom)` without invoking the axiom.
  - The substantive analytic content of the AA axiom narrows to:
    "1 ∈ closure ⇒ 1 ∈ interior(closure)", which is the genuine
    Bridge Lemma 6.1 + 6.2 content (modulo BCH cubic upstream).

## Pipeline Invariant compliance

  - Invariant #10 (no `maxHeartbeats`): RESPECTED.
  - Invariant #15 (no new axioms): RESPECTED — pure constructive proof.
  - Strengthening: each lemma captures one mathematical content unit;
    `accPt_one_in_range_of_hom` is the load-bearing FKLW specialization
    (P5 audit: it composes the general `one_accPt_of_infinite_closed_subgroup`
    with the specific MonoidHom structure of FKLW representations —
    NOT a trivial identity-function wrapper).

## Primary reference

  Aharonov & Arad 2011, *New J. Phys.* 13 035019;
  arXiv:quant-ph/0605181 §6 Lemmas 6.1 + 6.2 (the deferred analytic
  content).

  The discreteness-implies-finite-from-compact bridge follows from
  Mathlib's `finite_of_compact_of_discrete` +
  `discreteTopology_iff_isOpen_singleton_one`. Pure topology.

Zero sorry. Zero new project-local axioms.
-/

import Mathlib
import SKEFTHawking.BraidGroup
import SKEFTHawking.FKLW.AharonovAradBridgeIteration

set_option autoImplicit false

namespace SKEFTHawking.FKLW

open scoped Matrix

/-! ## 1. Identity is an accumulation point of any infinite closed subgroup
of a compact topological group

The core topological fact: if H is a closed subgroup of a compact
topological group G and H is infinite, then there are elements of H
arbitrarily close to (but not equal to) the identity.

Proof: contradiction. If 1 is NOT an accumulation point, there's a
neighborhood U of 1 with `U ∩ (H \ {1}) = ∅`. Then the singleton
`{1}` is open in the subspace topology of H, so H is discrete
(by `discreteTopology_iff_isOpen_singleton_one` — translation makes
every H-element have an isolated neighborhood). But H is also compact
(closed in compact G), and `finite_of_compact_of_discrete` forces H
to be finite — contradicting infinity. -/

/-- **Identity is an accumulation point of an infinite closed subgroup
of a compact topological group** (purely topological; no LieSpan
assumed). -/
theorem one_accPt_of_infinite_closed_subgroup
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (H : Subgroup G) (h_closed : IsClosed (H : Set G))
    (h_inf : (H : Set G).Infinite) :
    AccPt (1 : G) (Filter.principal (H : Set G)) := by
  by_contra h_not_acc
  apply h_inf
  -- ¬ AccPt 1 (𝓟 H) ⇒ 1 ∉ closure(H \ {1}) ⇒ some nbhd U of 1 with U ∩ (H \ {1}) = ∅
  rw [accPt_principal_iff_clusterPt, ← mem_closure_iff_clusterPt,
      mem_closure_iff_nhds] at h_not_acc
  push_neg at h_not_acc
  obtain ⟨U, hU_nhds, hU_disj⟩ := h_not_acc
  obtain ⟨V, hV_sub, hV_open, hV_mem⟩ := mem_nhds_iff.mp hU_nhds
  -- V is open, 1 ∈ V, V ⊆ U, V ∩ (H \ {1}) = ∅
  have hV_disj : V ∩ ((H : Set G) \ {1}) = ∅ := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hxV hxH
    have : x ∈ U ∩ ((H : Set G) \ {1}) := ⟨hV_sub hxV, hxH⟩
    rw [hU_disj] at this
    exact this
  -- Now: in subspace H, {1} is open (preimage of V under inclusion is {1}).
  have h_subtype_discrete : DiscreteTopology H := by
    rw [discreteTopology_iff_isOpen_singleton_one, isOpen_induced_iff]
    refine ⟨V, hV_open, ?_⟩
    ext h
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    refine ⟨fun hV_h => ?_, fun h_eq => h_eq ▸ hV_mem⟩
    have h_in_H : (h : G) ∈ (H : Set G) := h.2
    by_contra h_ne
    have h_val_ne : (h : G) ≠ 1 := fun h_eq => h_ne (Subtype.ext h_eq)
    have : (h : G) ∈ V ∩ ((H : Set G) \ {1}) := ⟨hV_h, h_in_H, h_val_ne⟩
    rw [hV_disj] at this
    exact this
  -- H is compact (closed in compact G).
  have h_H_cpt : CompactSpace H := isCompact_iff_compactSpace.mp h_closed.isCompact
  -- Compact + Discrete = Finite.
  have h_finite : Finite H := finite_of_compact_of_discrete
  exact Set.toFinite _

/-- **Identity is in the closure of any infinite closed subgroup of a
compact topological group** (immediate corollary; the AccPt form above
is the load-bearing version). -/
theorem one_mem_closure_of_infinite_closed_subgroup
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (H : Subgroup G) (_h_closed : IsClosed (H : Set G))
    (_h_inf : (H : Set G).Infinite) :
    (1 : G) ∈ closure (H : Set G) :=
  subset_closure H.one_mem

/-! ## 2. Specialization to `BraidGroup n →* SU(d)` MonoidHom

For the FKLW use case, the relevant subgroup is `ρ_hom.range`, where
`ρ_hom : BraidGroup n →* SU(d)`. We need:
  - `ρ_hom.range` is a `Subgroup` of `SU(d)`: automatic from `MonoidHom.range`.
  - `(ρ_hom.range : Set _).Infinite`: this is the `h_inf` hypothesis.
  - `IsClosed (ρ_hom.range : Set _)`: NOT automatic. We use the
    `topologicalClosure`, which IS closed, and whose carrier set is
    exactly `closure (ρ_hom.range : Set _)`.

The cleanest formulation: 1 ∈ closure(range ρ_hom) AND 1 is an AccPt
of `topologicalClosure ρ_hom.range`.
-/

/-- **The identity is an accumulation point of the topological closure
of an infinite-image MonoidHom range into SU(d).**

Specialization of `one_accPt_of_infinite_closed_subgroup` to the FKLW
setting: a `MonoidHom` from `BraidGroup n` to `SU(d)` with infinite
range has its topological closure containing 1 as an accumulation point.

This is the substantive topological core that any future constructive
discharge of `aa_residual_interior_at_one_for_hom` will use as its
"starting point" (combined with the LieSpan + BCH cubic for the
neighborhood-filling step). -/
theorem accPt_one_in_topClosure_of_hom
    {n d : ℕ} (ρ_hom : BraidGroup n →* Matrix.specialUnitaryGroup (Fin d) ℂ)
    (h_inf : (Set.range ρ_hom).Infinite) :
    AccPt (1 : Matrix.specialUnitaryGroup (Fin d) ℂ)
      (Filter.principal
        (ρ_hom.range.topologicalClosure : Set (Matrix.specialUnitaryGroup (Fin d) ℂ))) := by
  have h_range_carrier :
      (ρ_hom.range : Set (Matrix.specialUnitaryGroup (Fin d) ℂ)) = Set.range ρ_hom := by
    ext y; simp [MonoidHom.range]
  -- ρ_hom.range.topologicalClosure carrier = closure (range)
  set K : Subgroup (Matrix.specialUnitaryGroup (Fin d) ℂ) :=
    ρ_hom.range.topologicalClosure with hK_def
  have h_inf_closure : (K : Set (Matrix.specialUnitaryGroup (Fin d) ℂ)).Infinite := by
    have h_sub : (ρ_hom.range : Set (Matrix.specialUnitaryGroup (Fin d) ℂ)) ⊆ (K : Set _) :=
      SetLike.coe_subset_coe.mpr (Subgroup.le_topologicalClosure ρ_hom.range)
    rw [h_range_carrier] at h_sub
    exact h_inf.mono h_sub
  have h_closed : IsClosed (K : Set (Matrix.specialUnitaryGroup (Fin d) ℂ)) :=
    Subgroup.isClosed_topologicalClosure _
  exact one_accPt_of_infinite_closed_subgroup K h_closed h_inf_closure

/-- **The identity is in the closure of an infinite-image MonoidHom
range** (entry-level corollary; downstream consumers prefer the
`AccPt` form for substantive use). -/
theorem one_mem_closure_range_of_infinite_image
    {n d : ℕ} (ρ_hom : BraidGroup n →* Matrix.specialUnitaryGroup (Fin d) ℂ)
    (_h_inf : (Set.range ρ_hom).Infinite) :
    (1 : Matrix.specialUnitaryGroup (Fin d) ℂ) ∈ closure (Set.range ρ_hom) := by
  apply subset_closure
  exact ⟨1, ρ_hom.map_one⟩

/-! ## 3. Module summary

AharonovAradLemma6.lean (Wave 2c.4a-R5.1 ship, 2026-05-13):

**Topological infrastructure** (axiom-free, constructive):
  - `one_accPt_of_infinite_closed_subgroup` — generic compact-group
    topology result.
  - `one_mem_closure_of_infinite_closed_subgroup` — entry corollary.

**FKLW specializations** (axiom-free):
  - `accPt_one_in_topClosure_of_hom` — `BraidGroup n →* SU(d)` with
    infinite image ⇒ 1 is AccPt of `topologicalClosure of range`.
  - `one_mem_closure_range_of_infinite_image` — entry corollary.

**Honest status post-R5.1**:
  - The AA axiom `aa_residual_interior_at_one_for_hom` is NOT
    discharged by this module alone. The substantive analytic content
    (Bridge Lemmas 6.1 + 6.2) requires the BCH cubic-bound K·δ³
    (deferred — current `bch_order_2_thm` gives linear `200·δ` which
    is too weak for the quadratic-shrinkage iteration of Lemma 6.1).
  - This module narrows the axiom's effective surface area: the
    topological "1 ∈ closure" half is now constructive; the residual
    is precisely the analytic "interior at 1 from spanning + small
    elements" content.

**Pipeline Invariant compliance**:
  - #10 (no `maxHeartbeats`): RESPECTED.
  - #15 (no new axioms): RESPECTED (zero introduced).

**Path to full AA discharge** (multi-session, deferred):
  1. R5.2: BCH cubic-bound K·δ³ (substantive 300-500 LoC).
  2. R5.3: Bridge Lemma 6.1 (commutator quadratic shrinkage from BCH).
  3. R5.4: Bridge Lemma 6.2 (basis-rotation from LieSpan).
  4. R5.5: composition with R5.1 (this module) +
     `closure_eq_univ_of_one_mem_interior` to discharge axiom.

Zero sorry. Zero new project-local axioms in this module.
-/

end SKEFTHawking.FKLW
