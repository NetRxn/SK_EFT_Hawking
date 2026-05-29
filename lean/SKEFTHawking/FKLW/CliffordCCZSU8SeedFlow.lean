/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6z Wave 2a — the seed gives `1` as an accumulation point of `H_of_G`

The faithful literal Clifford+CCZ density (Wave 2) seeds its first continuous one-parameter subgroup from
the **infinite-order** seed `seedSU8 ∈ H_of_G` (Wave 1). The von-Neumann route is: an infinite closed
subgroup of the *compact* group SU(8) has the identity as an accumulation point, and a closed subgroup
with `1` as an accumulation point contains a continuous nontrivial 1-parameter subgroup (the SU(d)
generalization of `OneParameterSubgroupSU2`, Wave 2b).

This module ships **Wave 2a**: `1 ∈ AccPt (H_of_G cliffordCCZLiteralGeneratingSetSU8)`. The argument is
generic (any `d`): the powers `{seedSU8 ^ n}` are infinitely many distinct points of `H_of_G` (infinite
order, `seedSU8_pow_ne_one`), so `H_of_G` is infinite; SU(8) is compact, so an infinite subset has an
accumulation point `x` (`Set.Infinite.exists_accPt_principal`); `x` lies in the closed `H_of_G`, and
left-translation by `x⁻¹` (a homeomorphism preserving `H_of_G`) carries it to `1`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6z provenance

Phase 6z Wave 2a (accumulation-point witness for the seed flow). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8SeedNotFiniteOrder
import SKEFTHawking.FKLW.CliffordCCZSU8LiteralGeneratingSet
import SKEFTHawking.FKLW.GenericSUdOneParameterSubgroup

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix SKEFTHawking.FKLW.GenericSUd

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- The literal closure subgroup is infinite: it contains the distinct powers of the infinite-order
seed `seedSU8`. -/
theorem H_of_G_literal_infinite :
    (H_of_G cliffordCCZLiteralGeneratingSetSU8 :
      Set ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)).Infinite := by
  have hnotfin : ¬ IsOfFinOrder seedSU8 := by
    rw [isOfFinOrder_iff_pow_eq_one]
    rintro ⟨n, hn, hpow⟩
    exact seedSU8_pow_ne_one n hn hpow
  have hinj : Function.Injective (fun n : ℕ => seedSU8 ^ n) :=
    injective_pow_iff_not_isOfFinOrder.mpr hnotfin
  refine (Set.infinite_range_of_injective hinj).mono ?_
  rintro _ ⟨n, rfl⟩
  exact pow_mem seedSU8_mem n

/-- **Wave 2a — accumulation-point witness.** `1` is an accumulation point of the literal closure
subgroup `H_of_G`. (Infinite closed subgroup of compact SU(8) ⟹ has an accumulation point ⟹ by
left-translation, `1` is one.) This is the precondition consumed by the SU(d) von-Neumann
1-parameter-subgroup theorem (Wave 2b). -/
theorem seedSU8_accPt_one :
    AccPt (1 : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ))
      (Filter.principal (H_of_G cliffordCCZLiteralGeneratingSetSU8 :
        Set ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ))) := by
  obtain ⟨x, hx⟩ := H_of_G_literal_infinite.exists_accPt_principal
  -- `x` is in the closed subgroup `H_of_G` (a cluster point of a closed set lies in it).
  have hxmem : x ∈ H_of_G cliffordCCZLiteralGeneratingSetSU8 := by
    have hcl : x ∈ closure (H_of_G cliffordCCZLiteralGeneratingSetSU8 :
        Set ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :=
      mem_closure_iff_clusterPt.mpr hx.clusterPt
    rwa [(H_of_G_isClosed cliffordCCZLiteralGeneratingSetSU8).closure_eq] at hcl
  -- Left-translation by `x⁻¹` (a homeomorphism) carries `x ↦ 1` and `H_of_G ↦ H_of_G` (subgroup coset).
  have hmap := hx.map (Homeomorph.mulLeft x⁻¹).continuous.continuousAt
    (Homeomorph.mulLeft x⁻¹).injective
  have hcoset : (fun y => x⁻¹ * y) '' (H_of_G cliffordCCZLiteralGeneratingSetSU8 :
      Set ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) =
      (H_of_G cliffordCCZLiteralGeneratingSetSU8 :
        Set ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (H_of_G cliffordCCZLiteralGeneratingSetSU8).mul_mem
        ((H_of_G cliffordCCZLiteralGeneratingSetSU8).inv_mem hxmem) hy
    · intro hz
      exact ⟨x * z, (H_of_G cliffordCCZLiteralGeneratingSetSU8).mul_mem hxmem hz, by
        show x⁻¹ * (x * z) = z; group⟩
  simpa [Homeomorph.coe_mulLeft, Filter.map_principal, hcoset] using hmap

/-- **The seed's von-Neumann sequence**: a sequence in `H_of_G \ {1}` converging to `1`, extracted from
`seedSU8_accPt_one`. The seed of the BW-on-the-𝔰𝔲(8)-sphere step of the SU(d) von-Neumann construction. -/
theorem seedSU8_vonNeumann_sequence :
    ∃ seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ),
      (∀ n, seq n ∈ H_of_G cliffordCCZLiteralGeneratingSetSU8) ∧ (∀ n, seq n ≠ 1) ∧
      Filter.Tendsto seq Filter.atTop
        (nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ))) :=
  GenericSUd.vonNeumann_extract_sequence _ seedSU8_accPt_one

end SKEFTHawking.FKLW.CliffordCCZSU8
