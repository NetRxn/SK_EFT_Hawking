/-
SK_EFT_Hawking Phase 6p Wave 1b.2: Extended Rectangle (ex-Rec) Substrate

The AGP threshold theorem builds a recursive structure where each level-L gate
is implemented as an "extended rectangle" (ex-Rec) at level L-1:

    1-EC ∘ 1-Ga ∘ 1-EC

where 1-EC is the level-1 error-correction circuit (encode-and-recover) and
1-Ga is the level-1 implementation of the gate Ga (e.g., transversal CNOT on
the Steane [[7,1,3]] block). An ex-Rec is "good" if its locations have at most
one failure (no two simultaneous failures); otherwise it's "bad" and may exit
the recovery condition.

This module formalizes the ex-Rec data, the "good/bad" classification, and the
malignant-pair definition: a pair of locations whose simultaneous failure exits
the recovery condition (i.e., produces an uncorrectable logical error).

Per Wave 1a.1 DR §1 + gates G4/G5: the exact location-count `M` per ex-Rec and
the exact malignant-pair count `A_CNOT` are pinned in `Counting.lean` (this
file) for Steane [[7,1,3]] from the AGP 2006 PDF, with Reichardt 2006 LNCS
4051 as alternative source if it yields a smaller `A`.

Primary sources:
  - AGP 2006 (arXiv:quant-ph/0504218) §§3–5.
  - Reichardt, LNCS 4051 (2006), pp. 50–61 (alternative `A` derivation).
-/

import Mathlib
import SKEFTHawking.FaultTolerance.Basic
import SKEFTHawking.FaultTolerance.NoiseModel
import SKEFTHawking.FaultTolerance.StabilizerCode

set_option autoImplicit false

namespace SKEFTHawking.FaultTolerance

/-! ## 1. Extended rectangle (ex-Rec) location data

An ex-Rec is characterized by the number of locations its circuit contains.
For Steane [[7,1,3]] CNOT ex-Rec (encode + transversal CNOT + decode), this is
in the low hundreds (AGP 2006 Table V / Reichardt 2006).
-/

/-- An extended rectangle's location count: the total number of locations
    (each subject to independent failure with rate ε in the local-stochastic
    model). -/
structure ExRec where
  /-- Total location count. -/
  M : ℕ
  /-- Location count is positive (well-formed ex-Rec). -/
  M_pos : 0 < M

namespace ExRec

/-- The location count of any ex-Rec is positive. -/
theorem M_one_le (R : ExRec) : 1 ≤ R.M := R.M_pos

end ExRec

/-! ## 2. Malignant-pair specification

A "malignant pair" in an ex-Rec is an *unordered* pair of locations
{loc_i, loc_j} (with i ≠ j) such that the simultaneous failure of both
locations exits the recovery condition (i.e., produces an uncorrectable
logical error).

Different gate ex-Recs have different malignant-pair sets and thus different
`A` constants. For Steane [[7,1,3]] CNOT, the count of malignant pairs is
denoted `A_CNOT`.
-/

/-- A malignant-pair-count attestation: for a given ex-Rec, the number `A` of
    malignant pairs. The attestation does NOT require `A ≤ M.choose 2`
    explicitly — that's a derived fact — but a well-formed attestation
    necessarily has `A ≤ M.choose 2`. -/
structure MalignantPairAttestation (R : ExRec) where
  /-- The number of malignant pairs in this ex-Rec. -/
  A : ℕ
  /-- A is at most the total number of pairs (well-formedness). -/
  A_le_choose_two : A ≤ R.M.choose 2

namespace MalignantPairAttestation

variable {R : ExRec}

/-- A malignant-pair attestation gives `A` as a non-negative natural. -/
theorem A_nonneg (att : MalignantPairAttestation R) : 0 ≤ att.A := Nat.zero_le _

/-- Cast `A` to `ℝ`, non-negative. -/
theorem A_real_nonneg (att : MalignantPairAttestation R) : (0 : ℝ) ≤ (att.A : ℝ) := by
  exact_mod_cast att.A_nonneg

end MalignantPairAttestation

/-! ## 3. The level-recursion bound

For an ex-Rec with `M` locations and `A` malignant pairs, the probability of
ex-Rec failure under abstract local-stochastic noise at rate `ε` satisfies:

    P[ex-Rec fails] ≤ A · ε²   +   (higher-order terms in ε)

The dominant `A · ε²` term comes from the pair-failure union bound:
P[∃ malignant pair (i,j) with both i and j failing] ≤ A · ε². The
higher-order terms are O(ε³) and absorbed for ε ≤ 1/A.

This is the AGP recursion at the abstract real-valued level; the formal
probability-theoretic justification routes through `NoiseModel.jointFailureBound`.
-/

/-- The AGP level-recursion bound: an ex-Rec with malignant-pair count `A` and
    per-location failure rate `ε` has ex-Rec-level failure rate at most
    `A · ε²` (the leading-order Chernoff-like bound from union bound on
    malignant pairs). -/
def exRecFailureBound (A : ℕ) (ε : ℝ) : ℝ := (A : ℝ) * ε ^ 2

/-- The ex-Rec failure bound is non-negative for non-negative `A`. -/
theorem exRecFailureBound_nonneg (A : ℕ) (ε : ℝ) :
    0 ≤ exRecFailureBound A ε := by
  unfold exRecFailureBound
  positivity

/-- The ex-Rec failure bound is monotone in `A`. -/
theorem exRecFailureBound_mono_A (A B : ℕ) (ε : ℝ) (hAB : A ≤ B) :
    exRecFailureBound A ε ≤ exRecFailureBound B ε := by
  unfold exRecFailureBound
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact_mod_cast hAB

/-- The ex-Rec failure bound is monotone in `ε` (for non-negative `ε`). -/
theorem exRecFailureBound_mono_ε (A : ℕ) (ε ε' : ℝ) (hε : 0 ≤ ε) (h : ε ≤ ε') :
    exRecFailureBound A ε ≤ exRecFailureBound A ε' := by
  unfold exRecFailureBound
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg A)
  exact sq_le_sq' (by linarith) h

/-! ## 4. Module summary

ExRec.lean: extended rectangle substrate + malignant-pair attestations.

  - `ExRec` (structure: M, M_pos).
  - `MalignantPairAttestation R` (structure: A, A_le_choose_two).
  - `exRecFailureBound A ε := A · ε²` — the AGP recursion-step bound.
  - `exRecFailureBound_nonneg`, `exRecFailureBound_mono_A`, `exRecFailureBound_mono_ε`.

Consumed by Wave 1b.2 Counting (pins Steane CNOT A_CNOT via decide)
and Wave 1b.3 AGP/Threshold (the main recursion).

Zero sorry. Zero axioms.
-/

end SKEFTHawking.FaultTolerance
