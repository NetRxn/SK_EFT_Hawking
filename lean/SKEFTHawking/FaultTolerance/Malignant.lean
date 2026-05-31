/-
SK_EFT_Hawking Phase 6p Wave 1b.2: Malignant Pair Structure

Bridge between the abstract `MalignantPairAttestation` (ExRec.lean) and the
concrete `MalignancyCounts` for a specific stabilizer code (StabilizerCode.lean).

Given a stabilizer code `C` and a `MalignancyCounts C` assignment, this module
manufactures `MalignantPairAttestation` instances for each gate ex-Rec. The
concrete malignant-pair counts for Steane [[7,1,3]] are pinned in `Counting.lean`.

Primary source: AGP 2006 (arXiv:quant-ph/0504218) §3.
-/

import Mathlib
import SKEFTHawking.FaultTolerance.Basic
import SKEFTHawking.FaultTolerance.NoiseModel
import SKEFTHawking.FaultTolerance.StabilizerCode
import SKEFTHawking.FaultTolerance.ExRec

set_option autoImplicit false

namespace SKEFTHawking.FaultTolerance

/-! ## 1. Gate-specific ex-Recs

For a stabilizer code `C`, each Clifford gate (CNOT, single-qubit Cliffords,
prep, measurement) has its own ex-Rec with a specific location count and
malignant-pair count.
-/

/-- The ex-Rec data for each of the four AGP gate categories on a given code.

This is a *placeholder* schema; concrete location counts for Steane [[7,1,3]]
are pinned in `Counting.lean` from the AGP 2006 PDF / Reichardt 2006. -/
structure GateExRecs (C : StabilizerCode) where
  /-- The level-1 CNOT extended rectangle. -/
  cnot : ExRec
  /-- The level-1 single-qubit Clifford gate extended rectangle. -/
  gate1 : ExRec
  /-- The level-1 measurement extended rectangle. -/
  meas : ExRec
  /-- The level-1 preparation extended rectangle. -/
  prep : ExRec

namespace GateExRecs

variable {C : StabilizerCode}

/-- The maximum location count across all four ex-Recs. -/
def M_max (E : GateExRecs C) : ℕ :=
  max (max E.cnot.M E.gate1.M) (max E.meas.M E.prep.M)

/-- The maximum is positive (every ex-Rec is well-formed). -/
theorem M_max_pos (E : GateExRecs C) : 0 < E.M_max := by
  unfold M_max
  have h := E.cnot.M_pos
  exact lt_of_lt_of_le h (by
    apply le_max_of_le_left
    exact le_max_left _ _)

end GateExRecs

/-! ## 2. Malignant-pair attestations from MalignancyCounts

Given a `MalignancyCounts C` (StabilizerCode.lean) and a `GateExRecs C`, we
build a `MalignantPairAttestation` for each gate.
-/

/-- Build a CNOT malignant-pair attestation from a MalignancyCounts assignment.
    Requires `A_CNOT ≤ R.M.choose 2`, i.e., the count is bounded by the total
    number of location pairs. -/
def cnotAttestation {C : StabilizerCode} (E : GateExRecs C) (M : MalignancyCounts C)
    (hbound : M.A_CNOT ≤ E.cnot.M.choose 2) :
    MalignantPairAttestation E.cnot :=
  { A := M.A_CNOT, A_le_choose_two := hbound }

/-- Build a measurement malignant-pair attestation. -/
def measAttestation {C : StabilizerCode} (E : GateExRecs C) (M : MalignancyCounts C)
    (hbound : M.A_meas ≤ E.meas.M.choose 2) :
    MalignantPairAttestation E.meas :=
  { A := M.A_meas, A_le_choose_two := hbound }

/-- Build a preparation malignant-pair attestation. -/
def prepAttestation {C : StabilizerCode} (E : GateExRecs C) (M : MalignancyCounts C)
    (hbound : M.A_prep ≤ E.prep.M.choose 2) :
    MalignantPairAttestation E.prep :=
  { A := M.A_prep, A_le_choose_two := hbound }

/-- Build a single-qubit-gate malignant-pair attestation. -/
def gate1Attestation {C : StabilizerCode} (E : GateExRecs C) (M : MalignancyCounts C)
    (hbound : M.A_gate1 ≤ E.gate1.M.choose 2) :
    MalignantPairAttestation E.gate1 :=
  { A := M.A_gate1, A_le_choose_two := hbound }

/-! ## 3. The per-gate AGP recursion contributions

Each attestation gives a contribution `A · ε²` to the AGP recursion. The
overall recursion uses `A_max` to bound any gate at once.
-/

/-- The per-CNOT recursion contribution. -/
def cnotRecursionContribution {C : StabilizerCode} {E : GateExRecs C}
    (att : MalignantPairAttestation E.cnot) (ε : ℝ) : ℝ :=
  exRecFailureBound att.A ε

/-- Per-CNOT recursion contribution is non-negative. -/
theorem cnotRecursionContribution_nonneg {C : StabilizerCode} {E : GateExRecs C}
    (att : MalignantPairAttestation E.cnot) (ε : ℝ) :
    0 ≤ cnotRecursionContribution att ε :=
  exRecFailureBound_nonneg att.A ε

/-! ## 4. Module summary

Malignant.lean: malignant-pair attestation manufacture from MalignancyCounts.

  - `GateExRecs C` (structure with cnot, gate1, meas, prep : ExRec).
  - `GateExRecs.M_max`, `M_max_pos`.
  - `cnotAttestation`, `measAttestation`, `prepAttestation`, `gate1Attestation`.
  - `cnotRecursionContribution`, `cnotRecursionContribution_nonneg`.

Consumed by Wave 1b.2 Counting (provides the concrete A_CNOT/etc. via
decide for Steane [[7,1,3]]) and Wave 1b.3 AGP/Threshold.

Zero sorry. Zero axioms.
-/

end SKEFTHawking.FaultTolerance
