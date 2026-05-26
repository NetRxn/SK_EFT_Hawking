/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Track T-B.5.2 — Read-Rezayi SU(2)_7 closure-density witness (conditional framework)

Ships the closure-density witness for `readRezayiK7GeneratingSet`
(Track T-B.5.1) conditional on a single tracked Prop
`rr7_v4_witness_tracked`, capturing the v4-witness Lie-theoretic
content already used by Phase 5 Step 13 and Phase 6u Track T-S.2.

## Headline definitions

  * `rr7_v4_witness_tracked : Prop` — the tracked closure-density
    hypothesis at `H_of_G readRezayiK7GeneratingSet`. Same shape as
    `cliffordT_v4_witness_tracked` (Phase 6u Track T-S.2 substrate).

  * `rr7ClosureDenseWitness_of_tracked` — given the tracked Prop,
    builds `ClosureDenseWitness readRezayiK7GeneratingSet` (via
    Classical.choice extraction).

  * `rr7_density_of_tracked` — conditional density at SU(2)_7.

  * `rr7_H_of_G_eq_top_of_tracked` — `H_of_G readRezayiK7GeneratingSet = ⊤`.

## Substantive discharge plan

The tracked Prop is discharged in
`ReadRezayiK7V4WitnessUnconditional.lean` by composing:
  1. **Accumulation at 1** (`rr7_accPt_one_unconditional` from
     `ReadRezayiK7InfiniteOrder.lean`) → produces the X₁ direction via
     Phase 5 Step 13's `vonNeumann_assemble_explicit_X_unconditional`.
  2. **Second ℝ-LI direction via Ad-conjugation**: at least one of
     `H_SU`, `T_RR7` neither commutes nor anti-commutes with X₁
     (`exists_readRezayiK7_generator_not_commute_not_anticommute` from
     `ReadRezayiK7GeneratorCaseAnalysis.lean`); apply Phase 5 Step 13's
     `ts_Ad_LI_of_not_commute_anticommute` to get the ℝ-LI tangent.

The Niven-style accumulation-at-1 for Read-Rezayi level 7 is discharged
DIRECTLY on the SU(2) generators via the cos(π/9) Chebyshev cubic
obstruction (see `ReadRezayiK7InfiniteOrder.lean::cos_pi_div_seven_cubic`
+ `α_RR7_ne_cos_rat_mul_pi`), avoiding any dependence on PU(2) literature.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new axioms): respected (the tracked Prop is a `def`, not
  an `axiom`; it is substantively discharged in
  `ReadRezayiK7V4WitnessUnconditional.lean`).

-/

import SKEFTHawking.FKLW.ReadRezayiK7GeneratingSet
import SKEFTHawking.FKLW.GenericClosureDenseWitness
import SKEFTHawking.FKLW.OneParameterSubgroupSU2

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

open Matrix
open SKEFTHawking.FKLW
open SKEFTHawking.FKLW.SU2LieAlgebra
open SKEFTHawking.FKLW.SU2MatrixExp

/-! ## 1. The tracked closure-density hypothesis -/

/-- **Tracked closure-density hypothesis for Read-Rezayi `SU(2)_7`**.

The v4 witness predicate at `H_of_G readRezayiK7GeneratingSet`: two
ℝ-LI traceless skew-Hermitian flow-line tangents in 𝔰𝔲(2) with
1-parameter-subgroup flow lines `exp(ℝ • X_i) ⊆ H_of_G readRezayiK7GeneratingSet`.

Discharged unconditionally in `ReadRezayiK7V4WitnessUnconditional.lean`
by composing `rr7_accPt_one_unconditional` (from `ReadRezayiK7InfiniteOrder.lean`)
with the second-tangent case analysis (from
`ReadRezayiK7GeneratorCaseAnalysis.lean`). -/
def rr7_v4_witness_tracked : Prop :=
  ∃ X₁ X₂ : Matrix (Fin 2) (Fin 2) ℂ,
    X₁ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2) ∧
    X₂ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2) ∧
    (∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
        M ∈ H_of_G readRezayiK7GeneratingSet ∧
        M.val = expAmbient (((t : ℝ) : ℂ) • X₁)) ∧
    (∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
        M ∈ H_of_G readRezayiK7GeneratingSet ∧
        M.val = expAmbient (((t : ℝ) : ℂ) • X₂)) ∧
    (∀ a b : ℝ, (a : ℂ) • X₁ + (b : ℂ) • X₂ = 0 → a = 0 ∧ b = 0)

/-! ## 2. Conditional ClosureDenseWitness construction -/

/-- **Conditional SU(2)_7 closure-density witness**. -/
noncomputable def rr7ClosureDenseWitness_of_tracked
    (h_tracked : rr7_v4_witness_tracked) :
    ClosureDenseWitness readRezayiK7GeneratingSet := by
  have h_ne : Nonempty (ClosureDenseWitness readRezayiK7GeneratingSet) := by
    obtain ⟨X₁, X₂, hX₁_ts, hX₂_ts, h_flow_X₁, h_flow_X₂, h_LI⟩ := h_tracked
    exact ⟨{ X₁ := X₁, X₂ := X₂
           , hX₁_ts := hX₁_ts, hX₂_ts := hX₂_ts
           , flow_X₁ := h_flow_X₁
           , flow_X₂ := h_flow_X₂
           , hLI := h_LI }⟩
  exact h_ne.some

/-! ## 3. Conditional density and `H_of_G = ⊤` for SU(2)_7 -/

/-- **Conditional SU(2)_7 density (via tracked Prop)**. -/
theorem rr7_density_of_tracked
    (h_tracked : rr7_v4_witness_tracked) :
    IsDenseInSU2_gs readRezayiK7GeneratingSet :=
  densityFromWitness (rr7ClosureDenseWitness_of_tracked h_tracked)

/-- **Conditional `H_of_G readRezayiK7GeneratingSet = ⊤`**. -/
theorem rr7_H_of_G_eq_top_of_tracked
    (h_tracked : rr7_v4_witness_tracked) :
    H_of_G readRezayiK7GeneratingSet = ⊤ :=
  H_of_G_eq_top_of_witness (rr7ClosureDenseWitness_of_tracked h_tracked)

end SKEFTHawking.FKLW.GenericSU2
