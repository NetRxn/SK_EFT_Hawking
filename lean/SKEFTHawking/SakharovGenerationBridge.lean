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

  ⚠️ **15 AND 24 ARE TWO CONVENTIONS, AND THE MODULE MUST SAY SO RATHER THAN
  CARRY BOTH SILENTLY.** `15` is the *chiral*-multiplet count per the Standard
  Model without `ν_R` (15 Weyl fields per generation, counted as species).
  `standardModel.diracFlavourNf = 24` is the *Dirac*-pair count over three
  generations WITH `ν_R`: `3 × 16 / 2`. They are not the same quantity, and this
  module's business is the second. `sm_chiral_convention_differs` below states
  the disagreement numerically so a reader cannot absorb one as the other.
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
-- ⚠️ BOTH endpoints are imported, and both are CALLED below. This module exists
-- because a claim was made without a witness; importing only `Mathlib` and
-- re-declaring both sides locally would have reproduced that defect one level
-- down (CLAUDE.md preemptive-strengthening rule 3, and
-- `feedback_python_lean_refs_drift`): a rename on either endpoint would leave
-- this file compiling and wrong.
import SKEFTHawking.GenerationConstraint
import SKEFTHawking.HeatKernelExpansion

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
    (standardModel.generationNf : ℚ) = 3 ∧ standardModel.diracFlavourNf = 24 := by
  refine ⟨by norm_num [FermionContent.generationNf, standardModel], ?_⟩
  norm_num [FermionContent.diracFlavourNf, standardModel]

/-- The disequality, extracted. ⚠️ It was the THIRD CONJUNCT of `sm_counts_differ`
and is implied by the first two — `3 ≠ 24` follows from the two values by
`norm_num`, so bundling it made two substantive numbers look like three claims
(CLAUDE.md preemptive-strengthening rule 1, P2). The two witnesses are the
falsifiable content; this is the reading downstream wants. -/
theorem sm_counts_differ_ne :
    (standardModel.generationNf : ℚ) ≠ standardModel.diracFlavourNf := by
  obtain ⟨h3, h24⟩ := sm_counts_differ
  rw [h3, h24]
  norm_num

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

/-- **The anomaly-side divisibility and the Sakharov-side one are the SAME
CONDITION**, at Standard-Model per-generation content.

⚠️ **STATED AS A BICONDITIONAL BECAUSE THE IMPLICATION WAS A TAUTOLOGY, and
saying so is the only honest form.** This was `generation_constraint_transfers`,
an implication, and it went through two wrong hypothesis choices:

1. It first took `3 ∣ c.generations` — assuming the very constraint it advertised
   as transferring (CLAUDE.md anti-pattern P4).
2. It was then "strengthened" to `24 ∣ 8·generations` on the argument that this
   is the anomaly-side condition on the chiral central charge rather than a
   restatement. **That argument is false, and the refutation is one line:**
   `24 ∣ 8n ↔ 3 ∣ n` over ℤ, kernel-checked. The two hypotheses are logically
   equivalent, so nothing was strengthened.

   Worse, with `hw : weylPerGeneration = 16` we have `diracFlavourNf = 8·g`, so
   the conclusion `∃ k, diracFlavourNf = 24k` unfolds to `24 ∣ 8g` — the
   hypothesis itself. The implication was `P → P` modulo one definition.

The biconditional is the true and non-trivial statement: it says the two
divisibility conditions coincide under SM content, which is a fact about the
factor of 8 (`diracFlavourNf_eq_scaled_generationNf`) and not a transfer of
independent physics. **`24 ∣ c₋` remains a physics INPUT at this boundary** —
`GenerationConstraint.lean:47` records that the modular-invariance axiom which
would have supplied it was REMOVED AS FALSE (it quantified over all `N_f`, and
`N_f = 1` gives `24 ∤ 8`). Nothing here derives it. -/
theorem generation_constraint_transfers_iff
    (c : FermionContent) (hw : c.weylPerGeneration = 16) (hpos : 0 < c.generations) :
    24 ∣ (8 * (c.generations : ℤ)) ↔ ∃ k : ℕ, c.diracFlavourNf = (24 * k : ℚ) := by
  constructor
  · intro hanom
    obtain ⟨k, hk⟩ := SKEFTHawking.generation_mod3_constraint c.generations hpos hanom
    refine ⟨k, ?_⟩
    unfold FermionContent.diracFlavourNf
    rw [hw, hk]
    push_cast
    ring
  · rintro ⟨k, hk⟩
    unfold FermionContent.diracFlavourNf at hk
    rw [hw] at hk
    have hg : (c.generations : ℚ) * 16 / 2 = 24 * k := hk
    have : (c.generations : ℚ) = 3 * k := by linarith
    have hnat : c.generations = 3 * k := by exact_mod_cast this
    exact ⟨(k : ℤ), by rw [hnat]; push_cast; ring⟩

/-- The forward direction alone, for callers that only need it. Named so the old
implication has a home; the biconditional above is the statement with content. -/
theorem generation_constraint_transfers
    (c : FermionContent) (hw : c.weylPerGeneration = 16)
    (hpos : 0 < c.generations) (hanom : 24 ∣ (8 * (c.generations : ℤ))) :
    ∃ k : ℕ, c.diracFlavourNf = (24 * k : ℚ) :=
  (generation_constraint_transfers_iff c hw hpos).mp hanom

/-- Non-vacuity of the transfer: the Standard-Model content satisfies its
hypotheses, so `generation_constraint_transfers` is not conditionally empty. -/
theorem standardModel_satisfies_transfer_hypotheses :
    standardModel.weylPerGeneration = 16 ∧ 0 < standardModel.generations ∧
      24 ∣ (8 * (standardModel.generations : ℤ)) :=
  ⟨rfl, by norm_num [standardModel], by decide⟩

/-! ## 4. The Sakharov side, reached rather than described

The header names `a0_dirac` as the coefficient the species count feeds. These two
theorems make that a CALL: the first evaluates it at the module's own count, the
second states the 15-vs-24 convention gap numerically so neither number can be
quoted as the other.
-/

/-- **The species count is the argument `a0_dirac` takes.** Evaluated at
Standard-Model content: `a₀ = 4 · 24 / (4π)²`. -/
theorem a0_dirac_at_standardModel :
    HeatKernelExpansion.a0_dirac ((standardModel.diracFlavourNf : ℚ) : ℝ)
      = 4 * 24 * HeatKernelExpansion.fourPiSqInv := by
  norm_num [HeatKernelExpansion.a0_dirac, FermionContent.diracFlavourNf, standardModel]

/-- **The two conventions differ, and by how much.** `15` is the chiral-multiplet
count without `ν_R`; `24` is the Dirac-pair count over three generations with it.
Stated as a numeric inequality with the ratio pinned, so a future edit that
silently swaps one for the other fails here. -/
theorem sm_chiral_convention_differs :
    HeatKernelExpansion.a0_dirac 15 ≠
      HeatKernelExpansion.a0_dirac ((standardModel.diracFlavourNf : ℚ) : ℝ) ∧
    HeatKernelExpansion.a0_dirac ((standardModel.diracFlavourNf : ℚ) : ℝ)
      = (8 / 5 : ℝ) * HeatKernelExpansion.a0_dirac 15 := by
  constructor
  · simp only [HeatKernelExpansion.a0_dirac, FermionContent.diracFlavourNf, standardModel]
    norm_num
    exact HeatKernelExpansion.fourPiSqInv_pos.ne'
  · simp only [HeatKernelExpansion.a0_dirac, FermionContent.diracFlavourNf, standardModel]
    push_cast
    ring

end SKEFTHawking.SakharovGenerationBridge
