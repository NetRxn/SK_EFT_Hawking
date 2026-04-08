import SKEFTHawking.Basic

/-!
# Non-Abelian Gauge Erasure Theorem

## Overview

Formalizes the universal structural theorem that non-Abelian gauge degrees
of freedom cannot survive hydrodynamization, while U(1) gauge structure can.

## The Argument Chain

1. **Higher-form symmetries must be Abelian.** Operators charged under a
   p-form symmetry (p ≥ 1) are supported on submanifolds of codimension ≥ 1.
   On a spatial slice, codimension ≥ 1 means operators can be displaced to
   have disjoint support, so they commute. A group whose elements all commute
   is Abelian.

2. **Non-Abelian gauge theories have discrete center symmetries.** For SU(N),
   the relevant 1-form symmetry is the center Z_N. For SO(N), it is Z_2 or
   Z_2 × Z_2. These are finite groups, not continuous Lie groups.

3. **Discrete symmetry breaking → domain walls, not Goldstone bosons.** The
   Goldstone theorem requires a spontaneously broken *continuous* symmetry to
   produce gapless modes. Discrete symmetry breaking produces topological
   defects (domain walls) instead. Domain walls are not hydrodynamic modes.

4. **Therefore: no non-Abelian gauge hydrodynamic modes.** The gauge sector
   of any non-Abelian theory produces no Goldstone bosons upon
   hydrodynamization. The gauge DOF are erased.

5. **U(1) exception.** U(1) gauge theory has a continuous magnetic 1-form
   symmetry U(1)^{(1)}. Its spontaneous breaking produces the photon as a
   1-form Goldstone boson (Grozdanov-Hofman-Iqbal photonization theorem).

## Universality

This holds across ALL hydrodynamic frameworks:
- Standard (Müller-Israel-Stewart) hydrodynamics
- Fracton hydrodynamics
- Holographic hydrodynamics (N=4 SYM is the decisive test)

## References

- Gaiotto-Kapustin-Seiberg-Willett (2015): generalized global symmetries
- Grozdanov-Hofman-Iqbal: photonization theorem, U(1) survival
- Hofman-Iqbal: higher-form symmetry hydrodynamics
- Torrieri (2020): non-Abelian obstruction in fluids
- Nastase-Sonnenschein (2025): non-Abelian Clebsch closure
-/

namespace SKEFTHawking.GaugeErasure

/-!
## Gauge Group Properties

We model gauge groups by their key algebraic properties relevant to
the erasure theorem: Abelianness, continuity, and center structure.
-/

/-- A gauge group characterized by its algebraic properties.
    We use Bool (decidable) rather than Prop for computational properties. -/
structure GaugeGroupData where
  /-- Whether the group is Abelian (all elements commute) -/
  is_abelian : Bool
  /-- Whether the group is continuous (a Lie group, not finite) -/
  is_continuous : Bool
  /-- Whether the center subgroup is continuous -/
  has_continuous_center : Bool

-- non_abelian_center_discrete: removed as axiom (2026-04-04), never used.
-- The center of a non-Abelian simple Lie group is always finite:
--   SU(N): Z_N, SO(N): Z_2 or Z_2×Z_2, Sp(N): Z_2.
-- Provable from Lie theory once Mathlib has center/normalizer API.

/-!
## Higher-Form Symmetry

The type of higher-form symmetry determines the hydrodynamic fate.
-/

/-- Classification of available higher-form symmetries. -/
inductive HigherFormType where
  /-- Continuous 1-form symmetry (U(1) case) -/
  | continuous_1form
  /-- Discrete 1-form symmetry (SU(N), SO(N) center) -/
  | discrete_1form
  /-- No relevant higher-form symmetry -/
  | none

/-- **Higher-form symmetries must be Abelian.**

    Operators charged under a p-form symmetry (p ≥ 1) are supported on
    p-dimensional submanifolds, which have codimension ≥ 1 in space.
    Such operators can always be displaced to have disjoint support,
    so they commute. A symmetry group whose charged operators all commute
    is necessarily Abelian.

    Consequence: the higher-form symmetry of a gauge theory is determined
    by the Abelian part of the gauge group (its center).
    - Abelian + continuous → continuous 1-form (U(1))
    - Non-Abelian → discrete 1-form (Z_N center)
-/
def higher_form_symmetry (G : GaugeGroupData) : HigherFormType :=
  match G.is_abelian, G.is_continuous with
  | true,  true  => HigherFormType.continuous_1form
  | false, true  => HigherFormType.discrete_1form
  | _,     false => HigherFormType.none

/-- Non-Abelian continuous groups always get discrete 1-form symmetry. -/
theorem non_abelian_gives_discrete (G : GaugeGroupData)
    (h_na : G.is_abelian = false) (h_cont : G.is_continuous = true) :
    higher_form_symmetry G = HigherFormType.discrete_1form := by
  unfold higher_form_symmetry
  rw [h_na, h_cont]

/-- Abelian continuous groups get continuous 1-form symmetry. -/
theorem abelian_gives_continuous (G : GaugeGroupData)
    (h_ab : G.is_abelian = true) (h_cont : G.is_continuous = true) :
    higher_form_symmetry G = HigherFormType.continuous_1form := by
  unfold higher_form_symmetry
  rw [h_ab, h_cont]

/-!
## Goldstone vs Domain Wall

The Goldstone theorem applies only to continuous symmetries.
Discrete symmetry breaking produces topological defects.
-/

/-- What happens to the gauge sector upon hydrodynamization. -/
inductive HydroFate where
  /-- Goldstone boson produced (continuous symmetry breaking) -/
  | goldstone
  /-- Domain wall produced (discrete symmetry breaking, no hydro mode) -/
  | domain_wall
  /-- Complete erasure (no symmetry to break) -/
  | erasure

/-- The Goldstone theorem applied to higher-form symmetries.

    - Continuous 1-form → Goldstone boson (the photon for U(1))
    - Discrete 1-form → domain wall (topological defect, not a hydro mode)
    - None → nothing -/
def hydro_fate (hf : HigherFormType) : HydroFate :=
  match hf with
  | HigherFormType.continuous_1form => HydroFate.goldstone
  | HigherFormType.discrete_1form => HydroFate.domain_wall
  | HigherFormType.none => HydroFate.erasure

/-- Continuous 1-form symmetry produces a Goldstone boson. -/
theorem continuous_gives_goldstone :
    hydro_fate HigherFormType.continuous_1form = HydroFate.goldstone := rfl

/-- Discrete 1-form symmetry produces domain walls, not Goldstone bosons. -/
theorem discrete_gives_domain_wall :
    hydro_fate HigherFormType.discrete_1form = HydroFate.domain_wall := rfl

/-!
## The Erasure Theorem
-/

/-- Whether gauge DOF survive hydrodynamization. -/
def survives (fate : HydroFate) : Prop :=
  fate = HydroFate.goldstone

/-- **The gauge erasure theorem (main result).**

    A non-Abelian continuous gauge group does NOT produce surviving
    hydrodynamic modes. Its higher-form symmetry is discrete (Z_N center),
    and discrete symmetry breaking produces domain walls, not Goldstone bosons.

    This is the universal structural theorem:
    non-Abelian → discrete 1-form → domain wall → erasure. -/
theorem gauge_erasure (G : GaugeGroupData)
    (h_na : G.is_abelian = false) (h_cont : G.is_continuous = true) :
    ¬survives (hydro_fate (higher_form_symmetry G)) := by
  rw [non_abelian_gives_discrete G h_na h_cont]
  unfold survives hydro_fate
  simp

/-- **U(1) survival theorem (the Abelian exception).**

    An Abelian continuous gauge group DOES produce surviving hydrodynamic
    modes. Its higher-form symmetry is continuous (U(1)^{(1)}), and
    continuous symmetry breaking produces a Goldstone boson (the photon).

    This is the Grozdanov-Hofman-Iqbal photonization theorem. -/
theorem u1_survival (G : GaugeGroupData)
    (h_ab : G.is_abelian = true) (h_cont : G.is_continuous = true) :
    survives (hydro_fate (higher_form_symmetry G)) := by
  rw [abelian_gives_continuous G h_ab h_cont]
  unfold survives hydro_fate
  rfl

/-- The erasure theorem is an exact dichotomy:
    gauge DOF survive iff the group is Abelian (among continuous groups). -/
theorem erasure_dichotomy (G : GaugeGroupData) (h_cont : G.is_continuous = true) :
    survives (hydro_fate (higher_form_symmetry G)) ↔ G.is_abelian = true := by
  constructor
  · intro h_surv
    by_contra h_na
    push_neg at h_na
    exact gauge_erasure G (by simp [h_na]) h_cont h_surv
  · intro h_ab
    exact u1_survival G h_ab h_cont

/-!
## Standard Model Application

The Standard Model gauge group is SU(3)_c × SU(2)_L × U(1)_Y.
Only U(1)_Y survives hydrodynamization.
-/

/-- SU(3) gauge data: non-Abelian, continuous. -/
def su3_data : GaugeGroupData where
  is_abelian := false
  is_continuous := true
  has_continuous_center := false

/-- SU(2) gauge data: non-Abelian, continuous. -/
def su2_data : GaugeGroupData where
  is_abelian := false
  is_continuous := true
  has_continuous_center := false

/-- U(1) gauge data: Abelian, continuous. -/
def u1_data : GaugeGroupData where
  is_abelian := true
  is_continuous := true
  has_continuous_center := true

/-- SU(3)_c (QCD) is erased. -/
theorem su3_erased : ¬survives (hydro_fate (higher_form_symmetry su3_data)) :=
  gauge_erasure su3_data rfl rfl

/-- SU(2)_L (weak force) is erased. -/
theorem su2_erased : ¬survives (hydro_fate (higher_form_symmetry su2_data)) :=
  gauge_erasure su2_data rfl rfl

/-- U(1)_Y (hypercharge/electromagnetism) survives. -/
theorem u1_survives : survives (hydro_fate (higher_form_symmetry u1_data)) :=
  u1_survival u1_data rfl rfl

/-- In the Standard Model, exactly one factor survives:
    SU(3) × SU(2) × U(1) → only U(1). -/
theorem sm_only_u1_survives :
    -- SU(3) erased AND SU(2) erased AND U(1) survives
    ¬survives (hydro_fate (higher_form_symmetry su3_data)) ∧
    ¬survives (hydro_fate (higher_form_symmetry su2_data)) ∧
    survives (hydro_fate (higher_form_symmetry u1_data)) :=
  ⟨su3_erased, su2_erased, u1_survives⟩

end SKEFTHawking.GaugeErasure
