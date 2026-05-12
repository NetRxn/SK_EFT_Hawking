/-
SK_EFT_Hawking Phase 6p Wave 1b.3: AGP Concatenated-Steane Threshold Theorem

Lean derivation of the AGP 2006 quantum threshold theorem for the
concatenated Steane [[7,1,3]] code under abstract local stochastic noise.

Headline result:

  agp_threshold_steane :
    For the concatenated Steane [[7,1,3]] code under abstract local stochastic
    noise with rate ε ≤ ε₀ := 1 / A_CNOT, the level-L logical error rate
    satisfies
       εL L ≤ ε₀ · (ε / ε₀)^(2^L)
    so the logical-error rate decays double-exponentially in L when ε < ε₀.

Numerical threshold (DR-locked-in):
       ε₀ > 2.73 × 10⁻⁵
    via A_CNOT ≤ 36,000 (Wave 1b.2 Counting.lean, conservative AGP-rigorous
    value; PDF-pinned at Wave 1b.1 implementor close).

Relation to existing libraries:
  - Coq SQIR / QWIRE / CoqQ / Coq-QECC, Chen-Liu-Fang CAV 2025,
    Huang-Zhou-Fang-Zhao-Ying PLDI 2025: stabilizer / Hoare-logic /
    single-level FT content; no threshold theorem.
  - Isabelle/HOL AFP 2023 concentration; QHLProver; CHSH/Tsirelson 2024:
    concentration-inequality substrate present; no connected threshold.
  - Lean-QuantumInfo (Oct 2025, arXiv:2510.08672): capacity-side primitives;
    no ε-thresholding.

Primary source: Aliferis-Gottesman-Preskill 2006, arXiv:quant-ph/0504218
                (Quantum Inf. Comput. 6, 97–165).
Error model:    abstract local stochastic only (topological deferred to
                Wave 1c+; not equivalent up to constants — see Wave 1a.1 DR).
-/

import Mathlib
import SKEFTHawking.FaultTolerance.Basic
import SKEFTHawking.FaultTolerance.NoiseModel
import SKEFTHawking.FaultTolerance.StabilizerCode
import SKEFTHawking.FaultTolerance.SteaneCode
import SKEFTHawking.FaultTolerance.ExRec
import SKEFTHawking.FaultTolerance.Malignant
import SKEFTHawking.FaultTolerance.Counting
import SKEFTHawking.FaultTolerance.Chernoff
import SKEFTHawking.FaultTolerance.DoubleExp
import SKEFTHawking.FaultTolerance.Concatenation

set_option autoImplicit false

namespace SKEFTHawking.FaultTolerance.AGP

open SKEFTHawking.FaultTolerance

/-! ## 1. The AGP threshold

The AGP threshold is the inverse of the malignant-pair count `A_CNOT`:
    ε₀ := 1 / A_CNOT.
For Steane [[7,1,3]] with `A_CNOT ≤ 36,000`, the threshold satisfies
`ε₀ > 2.73 × 10⁻⁵`, the DR-locked-in commitment.
-/

/-- The AGP threshold for a malignant-pair count `A`. -/
noncomputable def agpThreshold (A : ℕ) : ℝ := 1 / (A : ℝ)

/-- The Steane [[7,1,3]] AGP threshold. -/
noncomputable def steaneAGPThreshold : ℝ :=
  agpThreshold steaneMalignancyCounts.A_CNOT

/-- The Steane AGP threshold exceeds `2.73 × 10⁻⁵`. -/
theorem steaneAGPThreshold_gt :
    steaneAGPThreshold > 2.73e-5 := by
  unfold steaneAGPThreshold agpThreshold
  show (1 : ℝ) / (steaneMalignancyCounts.A_CNOT : ℝ) > 2.73e-5
  exact agp_threshold_steane_bound

/-- The Steane AGP threshold is positive. -/
theorem steaneAGPThreshold_pos : 0 < steaneAGPThreshold := by
  have : (0 : ℝ) < 2.73e-5 := by norm_num
  linarith [steaneAGPThreshold_gt]

/-- The Steane AGP threshold is at most 1 (in fact much less). -/
theorem steaneAGPThreshold_le_one : steaneAGPThreshold ≤ 1 := by
  unfold steaneAGPThreshold agpThreshold
  have h_A_pos : (0 : ℝ) < (steaneMalignancyCounts.A_CNOT : ℝ) := by
    have := steaneMalignancyCounts_A_CNOT_pos
    exact_mod_cast this
  have h_A_ge_one : (1 : ℝ) ≤ (steaneMalignancyCounts.A_CNOT : ℝ) := by
    show (1 : ℝ) ≤ (35235 : ℝ)
    norm_num
  rw [div_le_one h_A_pos]
  exact h_A_ge_one

/-! ## 2. The headline AGP threshold theorem for Steane [[7,1,3]]

For per-location failure rate ε satisfying `A_CNOT · ε < 1` (equivalently
`ε < ε₀ = 1 / A_CNOT`), the concatenated-Steane level-L logical error rate
satisfies the closed-form double-exponential bound from `Concatenation.lean` ∘
`DoubleExp.lean`.
-/

/-- **AGP concatenated-Steane threshold theorem.**

For per-location failure rate ε with `0 ≤ ε` and `A_CNOT · ε < 1`, the
level-L logical error rate `εL L` of the concatenated Steane [[7,1,3]] code
under abstract local stochastic noise satisfies
    `A_CNOT · εL L ≤ (A_CNOT · ε)^(2^L)`
(closed-form double-exponential bound).

The DR-locked-in threshold for this regime is `ε₀ > 2.73 × 10⁻⁵`,
verified separately as `steaneAGPThreshold_gt`. -/
theorem agp_threshold_steane (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ L, (steaneMalignancyCounts.A_CNOT : ℝ) * agpLevelSequence
        (steaneMalignancyCounts.A_CNOT : ℝ) ε L ≤
      ((steaneMalignancyCounts.A_CNOT : ℝ) * ε) ^ (2 ^ L) := by
  apply agpLevelSequence_double_exp_bound
  · exact Nat.cast_nonneg _
  · exact hε

/-- **Below-threshold strict bound.** If the per-location rate is strictly
    below the AGP threshold `ε₀ = 1 / A_CNOT`, then for every level `L ≥ 1`,
    the rescaled logical-error rate is strictly less than 1, i.e., the
    logical error rate stays below the threshold inverse-A.

    This is the AGP threshold theorem in the "useful" form: under-threshold
    physical rates suppress logical errors arbitrarily by concatenation. -/
theorem agp_threshold_steane_strict (ε : ℝ) (hε : 0 ≤ ε)
    (h_below : ε < steaneAGPThreshold) :
    ∀ L, 1 ≤ L →
      (steaneMalignancyCounts.A_CNOT : ℝ) * agpLevelSequence
        (steaneMalignancyCounts.A_CNOT : ℝ) ε L < 1 := by
  apply agpLevelSequence_below_threshold
  · exact Nat.cast_nonneg _
  · exact hε
  -- A · ε < 1 from ε < 1/A
  · have h_A_pos : (0 : ℝ) < (steaneMalignancyCounts.A_CNOT : ℝ) := by
      have := steaneMalignancyCounts_A_CNOT_pos
      exact_mod_cast this
    have h_below' : ε < 1 / (steaneMalignancyCounts.A_CNOT : ℝ) := h_below
    rw [lt_div_iff₀ h_A_pos] at h_below'
    linarith

/-! ## 3. Numerical certificate

Final DR-locked-in numerical certificate: the Steane [[7,1,3]] AGP threshold
exceeds `2.73 × 10⁻⁵`, the rigorous commitment from Wave 1a.1 DR §1. -/

/-- **DR-locked-in numerical certificate.** The Steane [[7,1,3]] AGP threshold,
    derived from the conservative AGP-rigorous count `A_CNOT ≤ 36,000` pinned
    in Wave 1b.2 Counting.lean, is strictly greater than the commonly-quoted
    rigorous lower bound `2.73 × 10⁻⁵` (NOT the heuristic `10⁻⁴`). -/
theorem agp_threshold_steane_numerical :
    steaneAGPThreshold > 2.73e-5 ∧ steaneAGPThreshold ≤ 1 :=
  ⟨steaneAGPThreshold_gt, steaneAGPThreshold_le_one⟩

/-! ## 4. Module summary

AGP/Threshold.lean: the AGP concatenated-Steane threshold theorem.

  - `agpThreshold A := 1 / A` — the threshold for malignant-pair count `A`.
  - `steaneAGPThreshold` — the Steane [[7,1,3]] AGP threshold.
  - `steaneAGPThreshold_gt` — `> 2.73 × 10⁻⁵` (DR-locked-in).
  - `steaneAGPThreshold_pos`, `steaneAGPThreshold_le_one`.
  - **`agp_threshold_steane`** — the headline theorem (closed-form bound).
  - **`agp_threshold_steane_strict`** — the strict below-threshold form.
  - **`agp_threshold_steane_numerical`** — numerical certificate.

Threshold-theorem closure on Steane [[7,1,3]] under abstract local stochastic
noise. Topological-substrate specialization deferred to Wave 1c+ per Wave 1a.1
DR §2 (gate G2): the topological error model is STRICTLY DIFFERENT from the
abstract local-stochastic model — not equivalent up to constants, not additive.

Zero sorry. Zero axioms.
-/

end SKEFTHawking.FaultTolerance.AGP
