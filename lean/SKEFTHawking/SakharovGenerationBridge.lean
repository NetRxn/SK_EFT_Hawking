/-
SK_EFT_Hawking TODO-D16: the two `N_f`s, related rather than identified.

WHY THIS MODULE EXISTS
----------------------
The flagship (bundle F, abstract / §1.4 / §6.1 / §12.1) elevates to a headline
*synthesis claim* that the `N_f` in the Sakharov coefficient
`G_N = 12π/(N_f Λ²)` and the `N_f` that fixes the Standard-Model anomaly
classification are **the same `N_f`** — "the substrate is one object; its faces
are the sibling bundles' worth of predictive register."

MEASURED 2026-08-09, AND THE LITERAL CLAIM IS FALSE:

* `HeatKernelExpansion.a0_dirac (N_f : ℝ)` counts **Dirac fermion species** in a
  heat-kernel expansion. It is real-valued and its fiducial anchor is `N_f = 15`.
* `GenerationConstraint`'s `N_f : ℕ` counts **generations**: its own docstring
  says "each generation contributes 16 real fermions in 4D, which reduce to
  `c₋ = 8` per generation", so `c₋ = 8 N_f` is eight-per-generation, and the
  central theorem is `3 ∣ N_f` with minimal nontrivial value `3`.

Different types, different physical objects, different values. The two are not
awaiting a proof of identity; identity is refuted below (`sm_counts_differ`).

WHAT IS TRUE, AND IS THE CLAIM F SHOULD MAKE
--------------------------------------------
Both counts are **determined by one underlying fermion content**, and their
relationship is a fixed proportionality whose constant is the per-generation
Weyl count. That is a real synthesis statement — one object, two faces — and it
is proved here rather than asserted. `generation_constraint_transfers` then
carries the anomaly-side constraint `3 ∣ generations` onto the Sakharov-side
species count, which is the load-bearing direction: an anomaly condition
constrains a gravitational coefficient.

⚠️ NOT CLAIMED: that the SM fermion content *is* the substrate's content. The
content is a parameter here. Fixing it is a physics input, not a theorem.
-/

import Mathlib

set_option autoImplicit false

namespace SKEFTHawking.SakharovGenerationBridge

/-! ## 1. One content, two counts -/

/-- The substrate's fermion content: how many generations, and how many Weyl
fields each carries. Both `N_f`s below are functions of this single object,
which is the precise sense in which "the substrate is one object". -/
structure FermionContent where
  /-- Number of generations. This is `GenerationConstraint`'s `N_f`. -/
  generations : ℕ
  /-- Weyl fields per generation. `16` for the Standard Model with `ν_R`. -/
  weylPerGeneration : ℕ

namespace FermionContent

/-- The anomaly-side count: generations. Enters `c₋ = 8 N_f`. -/
def generationNf (c : FermionContent) : ℕ := c.generations

/-- The Sakharov-side count: Dirac species, two Weyl fields per Dirac field.
Enters `a₀ = 4 N_f/(4π)²` and `G_N = 12π/(N_f Λ²)`. -/
def diracFlavourNf (c : FermionContent) : ℚ :=
  (c.generations * c.weylPerGeneration : ℚ) / 2

/-- The Standard-Model content: three generations, sixteen Weyl fields each
(fifteen chiral plus `ν_R`). -/
def standardModel : FermionContent := ⟨3, 16⟩

end FermionContent

open FermionContent

/-! ## 2. The bridge

The two counts are proportional, with the per-generation Weyl count as the
constant of proportionality. This is the whole content of "one object, two
faces": neither count is prior, both are read off the same structure.
-/

/-- **The bridge identity.** The Sakharov-side species count is the anomaly-side
generation count scaled by half the per-generation Weyl content. -/
theorem diracFlavourNf_eq_scaled_generationNf (c : FermionContent) :
    c.diracFlavourNf = (c.weylPerGeneration : ℚ) / 2 * (c.generationNf : ℚ) := by
  unfold FermionContent.diracFlavourNf FermionContent.generationNf
  ring

/-- **The literal identity is FALSE.** At Standard-Model content the two counts
are `3` and `24`. Stated numerically so it is falsifiable rather than a remark:
if a future content made them agree, this fails. -/
theorem sm_counts_differ :
    (standardModel.generationNf : ℚ) = 3 ∧
    standardModel.diracFlavourNf = 24 ∧
    (standardModel.generationNf : ℚ) ≠ standardModel.diracFlavourNf := by
  refine ⟨by norm_num [FermionContent.generationNf, standardModel], ?_, ?_⟩
  · norm_num [FermionContent.diracFlavourNf, standardModel]
  · norm_num [FermionContent.generationNf, FermionContent.diracFlavourNf, standardModel]

/-- The counts coincide only in the degenerate case of two Weyl fields per
generation — one Dirac field each. The Standard Model has sixteen, so the
coincidence never occurs for it. This is the *exact* condition under which the
flagship's literal claim would have been true. -/
theorem counts_agree_iff_two_weyl_per_generation
    (c : FermionContent) (hg : c.generations ≠ 0) :
    (c.generationNf : ℚ) = c.diracFlavourNf ↔ c.weylPerGeneration = 2 := by
  unfold FermionContent.generationNf FermionContent.diracFlavourNf
  have hg' : (c.generations : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hg
  constructor
  · intro h
    -- `field_simp` clears the `/2` and cancels the nonzero `generations` factor,
    -- leaving the conclusion itself as the hypothesis.
    field_simp at h
    exact_mod_cast h.symm
  · intro h
    rw [h]
    push_cast
    field_simp

/-! ## 3. The load-bearing direction

The anomaly-side constraint is `3 ∣ generations` (`GenerationConstraint`'s
central theorem). It transfers to the Sakharov-side count, so a condition
derived from modular invariance constrains the coefficient of an emergent
Newton constant. That transfer is the synthesis claim's actual predictive
content.
-/

/-- **The anomaly constraint transfers to the Sakharov coefficient.** If the
generation count satisfies the modular-invariance constraint `3 ∣ generations`,
then at Standard-Model per-generation content the Dirac species count is a
multiple of `24`. -/
theorem generation_constraint_transfers
    (c : FermionContent) (hw : c.weylPerGeneration = 16)
    (h3 : 3 ∣ c.generations) :
    ∃ k : ℕ, c.diracFlavourNf = (24 * k : ℚ) := by
  obtain ⟨k, hk⟩ := h3
  refine ⟨k, ?_⟩
  unfold FermionContent.diracFlavourNf
  rw [hw, hk]
  push_cast
  ring

/-- Non-vacuity of the transfer: the Standard-Model content satisfies its
hypotheses, so `generation_constraint_transfers` is not conditionally empty. -/
theorem standardModel_satisfies_transfer_hypotheses :
    standardModel.weylPerGeneration = 16 ∧ 3 ∣ standardModel.generations :=
  ⟨rfl, ⟨1, rfl⟩⟩

end SKEFTHawking.SakharovGenerationBridge
