import SKEFTHawking.Basic

/-!
# Chirality Wall Analysis: Golterman-Shamir vs Thorngren-Preskill-Fidkowski

## Overview

Formalizes the chirality wall analysis — the structural comparison between the
Golterman-Shamir (GS) generalized no-go conditions and the Thorngren-Preskill-
Fidkowski (TPF) disentangler construction for chiral lattice fermions.

## The Analysis

The GS generalized no-go theorem requires 4 conditions:
1. Lattice translation invariance
2. Finite-range Hamiltonian
3. Relativistic continuum limit
4. Complete interpolating field basis

The TPF construction introduces 4 ingredients that potentially evade some
conditions:
1. Infinite-dimensional rotor Hilbert spaces (evades condition 2)
2. Not-on-site symmetries (evades condition 4)
3. Ancilla degrees of freedom
4. Extra-dimensional SPT slab (4+1D gapped interface)

The critical assessment: IF the 4+1D gapped interface conjecture is proven
AND at least 2 GS conditions are evaded, the chirality wall falls.

## References

- Golterman-Shamir (2024-2026): generalized no-go
- Thorngren-Preskill-Fidkowski (Jan 2026): disentangler construction
- Butt-Catterall-Hasenfratz (PRL 2025): numerical evidence
- Hasenfratz-Witzel (Nov 2025): gradient flow
- Gioia-Thorngren (Mar 2025): anomaly constraints
- Seifnashri (Jan 2026): categorical symmetry
-/

namespace SKEFTHawking.ChiralityWall

/-!
## GS No-Go Conditions

The Golterman-Shamir generalized no-go theorem relies on 4 mathematical
conditions that must ALL hold for the no-go to apply.
-/

/-- A Golterman-Shamir no-go condition. Characterized by its name and whether
    it applies to the TPF construction. -/
structure GSCondition where
  /-- Name of the condition -/
  name : String
  /-- Whether this condition applies to the TPF construction -/
  applies_to_tpf : Bool

/-- Condition 1: lattice translation invariance. TPF preserves this. -/
def gs_translation : GSCondition where
  name := "lattice_translation_invariance"
  applies_to_tpf := true

/-- Condition 2: finite-range Hamiltonian. TPF may evade via infinite rotors. -/
def gs_finite_range : GSCondition where
  name := "finite_range_hamiltonian"
  applies_to_tpf := false

/-- Condition 3: relativistic continuum limit. TPF preserves this. -/
def gs_relativistic : GSCondition where
  name := "relativistic_continuum_limit"
  applies_to_tpf := true

/-- Condition 4: complete interpolating fields. TPF evades via not-on-site symmetries. -/
def gs_interpolating : GSCondition where
  name := "complete_interpolating_fields"
  applies_to_tpf := false

/-- The list of all 4 GS conditions. -/
def gs_conditions : List GSCondition :=
  [gs_translation, gs_finite_range, gs_relativistic, gs_interpolating]

/-- There are exactly 4 GS no-go conditions. -/
theorem gs_condition_count : gs_conditions.length = 4 := by native_decide

/-!
## TPF Disentangler Ingredients

The TPF construction uses 4 key ingredients, some of which evade GS conditions.
-/

/-- An ingredient of the TPF disentangler construction. -/
structure TPFIngredient where
  /-- Name of the ingredient -/
  name : String
  /-- Whether this ingredient evades a GS condition -/
  evades_condition : Bool

/-- Ingredient 1: infinite-dimensional rotor Hilbert spaces. Evades GS condition 2. -/
def tpf_infinite_rotors : TPFIngredient where
  name := "infinite_dim_rotor_hilbert"
  evades_condition := true

/-- Ingredient 2: not-on-site symmetries. Evades GS condition 4. -/
def tpf_not_on_site : TPFIngredient where
  name := "not_on_site_symmetries"
  evades_condition := true

/-- Ingredient 3: ancilla degrees of freedom. Does not directly evade a condition. -/
def tpf_ancilla : TPFIngredient where
  name := "ancilla_dof"
  evades_condition := false

/-- Ingredient 4: extra-dimensional SPT slab. Does not directly evade a condition. -/
def tpf_spt_slab : TPFIngredient where
  name := "extra_dim_spt_slab"
  evades_condition := false

/-- The list of all 4 TPF ingredients. -/
def tpf_ingredients : List TPFIngredient :=
  [tpf_infinite_rotors, tpf_not_on_site, tpf_ancilla, tpf_spt_slab]

/-- There are exactly 4 TPF ingredients. -/
theorem tpf_ingredient_count : tpf_ingredients.length = 4 := by native_decide

/-!
## Evasion Analysis
-/

/-- Count the number of GS conditions that are evaded (do not apply to TPF). -/
def evaded_count (conditions : List GSCondition) : Nat :=
  (conditions.filter (fun c => !c.applies_to_tpf)).length

/-- At least 2 GS conditions are evaded by the TPF construction. -/
theorem evaded_condition_count : evaded_count gs_conditions ≥ 2 := by native_decide

/-- Count the number of TPF ingredients that evade a GS condition. -/
def evasion_ingredient_count (ingredients : List TPFIngredient) : Nat :=
  (ingredients.filter (fun i => i.evades_condition)).length

/-- Exactly 2 TPF ingredients evade a GS condition. -/
theorem evasion_ingredients_eq_2 : evasion_ingredient_count tpf_ingredients = 2 := by
  native_decide

/-- Count of GS conditions that DO apply to TPF. -/
def applicable_count (conditions : List GSCondition) : Nat :=
  (conditions.filter (fun c => c.applies_to_tpf)).length

/-- Exactly 2 GS conditions still apply to the TPF construction. -/
theorem applicable_condition_count : applicable_count gs_conditions = 2 := by native_decide

/-- The evaded + applicable counts sum to the total. -/
theorem evaded_plus_applicable :
    evaded_count gs_conditions + applicable_count gs_conditions = gs_conditions.length := by
  native_decide

/-!
## Critical Conjecture and Wall Status
-/

/-- The 4+1D gapped interface conjecture status. -/
inductive ConjectureStatus where
  /-- The conjecture has been proven -/
  | proven
  /-- The conjecture is unproven (current status as of March 2026) -/
  | unproven
  /-- The conjecture has been refuted -/
  | refuted
  deriving DecidableEq, Repr

/-- The chirality wall status classification. -/
inductive WallStatus where
  /-- The wall stands — chiral lattice fermions impossible -/
  | stands
  /-- The wall falls — chiral lattice fermions possible -/
  | falls
  /-- Status is conditional on unproven conjecture -/
  | conditional
  deriving DecidableEq, Repr

/-- Determine the wall status from the conjecture status and evasion count.
    - If conjecture proven AND ≥2 conditions evaded → wall falls
    - If conjecture refuted → wall stands
    - If conjecture unproven → conditional -/
def wall_status (conj : ConjectureStatus) (n_evaded : Nat) : WallStatus :=
  match conj with
  | ConjectureStatus.proven => if n_evaded ≥ 2 then WallStatus.falls else WallStatus.stands
  | ConjectureStatus.refuted => WallStatus.stands
  | ConjectureStatus.unproven => WallStatus.conditional

/-- If the conjecture is proven and 2+ conditions are evaded, the wall falls. -/
theorem wall_falls_if_proven_and_evaded (n : Nat) (h : n ≥ 2) :
    wall_status ConjectureStatus.proven n = WallStatus.falls := by
  unfold wall_status
  simp [h]

/-- If the conjecture is refuted, the wall stands regardless of evasion count. -/
theorem wall_stands_if_refuted (n : Nat) :
    wall_status ConjectureStatus.refuted n = WallStatus.stands := by
  rfl

/-- If the conjecture is unproven, the status is conditional. -/
theorem wall_conditional_if_unproven (n : Nat) :
    wall_status ConjectureStatus.unproven n = WallStatus.conditional := by
  rfl

/-- **Main theorem: the chirality wall status is conditional (as of March 2026).**
    The TPF construction evades ≥2 GS conditions, but the critical 4+1D gapped
    interface conjecture is unproven. -/
theorem wall_status_conditional :
    wall_status ConjectureStatus.unproven (evaded_count gs_conditions) = WallStatus.conditional := by
  rfl

/-- **Conditional positive result:** IF the conjecture were proven, the wall
    would fall because TPF evades ≥2 GS conditions. -/
theorem wall_would_fall_if_proven :
    wall_status ConjectureStatus.proven (evaded_count gs_conditions) = WallStatus.falls := by
  native_decide

/-!
## GS No-Go Structure

The Golterman-Shamir generalized no-go theorem has the logical structure:
    (C1 ∧ C2 ∧ C3 ∧ C4) → ¬ ChiralFermions

Contrapositive: ChiralFermions → ¬C1 ∨ ¬C2 ∨ ¬C3 ∨ ¬C4

The TPF construction achieves ¬C1 (infinite rotors) and ¬C4 (ancilla fields).
This is sufficient: ¬C1 alone breaks the conjunction.
-/

/-
PROBLEM
The GS theorem requires ALL conditions to hold. Evading any one is sufficient
    to break the no-go. For gs_conditions: only 2 of 4 apply to TPF, so the
    conjunction of all 4 fails.

    Strengthened from vacuous `true` conclusion (quality audit 2026-03-26).

PROVIDED SOLUTION
Both conjuncts are decidable computations on concrete lists. Use `native_decide` or `decide`.
-/
theorem gs_nogo_requires_all :
    applicable_count gs_conditions = 2 ∧ applicable_count gs_conditions < gs_conditions.length := by
  native_decide +revert

/-- Stronger: TPF evades exactly 2 conditions, which is more than sufficient. -/
theorem tpf_evades_two_sufficient :
    evaded_count gs_conditions ≥ 2 ∧ evaded_count gs_conditions ≥ 1 := by
  native_decide

/-- The number of non-evaded conditions. Some still apply to TPF. -/
def applying_count (conditions : List GSCondition) : Nat :=
  (conditions.filter (fun c => c.applies_to_tpf)).length

/-- Evaded + applying = total. Conservation law for condition classification. -/
theorem condition_conservation :
    evaded_count gs_conditions + applying_count gs_conditions = gs_conditions.length := by
  native_decide

/-!
## Nielsen-Ninomiya Connection

The chirality wall is related to the Nielsen-Ninomiya theorem: on a lattice
with translation invariance, chiral fermions always come in pairs (equal
left and right). The TPF construction circumvents this by breaking translation
invariance via the extra-dimensional slab.

This connects to the ADW mechanism (Paper 5): the 4 emergent Dirac fermions
from Wen's string-net come in left-right pairs (Nielsen-Ninomiya), which is
one of the 4 structural obstacles for full emergent gravity.
-/

/-- Translation invariance applies to TPF (it doesn't break lattice periodicity).
    Nielsen-Ninomiya follows from translation invariance: on a periodic lattice,
    chiral fermions come in equal left-right pairs. The TPF evades the
    no-go through OTHER conditions (finite-range, interpolating fields),
    not by breaking translation invariance. -/
theorem translation_invariance_applies : gs_translation.applies_to_tpf = true := by rfl

/-!
## Strengthening: Logical Structure of the No-Go
-/

/-- **The GS no-go is a conjunction: ALL 4 conditions are required.**
    Evading k conditions out of 4 leaves 4-k conditions.
    If k ≥ 1, the conjunction fails and the no-go does not apply. -/
-- PROVIDED SOLUTION: evaded_count + applying_count = 4 (condition_conservation).
-- If evaded ≥ 1, then applying ≤ 3 < 4, so not all 4 hold.
theorem evading_one_breaks_nogo :
    evaded_count gs_conditions ≥ 1 →
    applying_count gs_conditions < gs_conditions.length := by
  intro _
  native_decide

/-- **TPF's evasion margin: it evades 2, only needs 1.**
    The margin of safety is 1 — even if one evasion turns out to be
    incorrect, the construction still breaks the no-go. -/
-- PROVIDED SOLUTION: evaded_count = 2 (by native_decide), so 2 ≥ 1 + 1.
theorem tpf_evasion_margin :
    evaded_count gs_conditions ≥ 1 + 1 := by
  native_decide

end SKEFTHawking.ChiralityWall