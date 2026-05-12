/-
SK_EFT_Hawking Phase 6p Wave 1b.1: Stabilizer Code Substrate

The `StabilizerCode` structure: a quantum error-correcting code defined by a
set of pairwise-commuting Pauli stabilizer generators, with specified logical
operators X̄ and Z̄, and a distance.

Substrate-only: the data structures here are consumed by `SteaneCode.lean` (a
concrete [[7,1,3]] instance) and by Wave 1b.3 `AGP/Threshold.lean`. The
semantic content (codespace = simultaneous +1 eigenspace of stabilizers) is
not formalized here — only the *combinatorial* data needed for fault-tolerance
counting (number of physical qubits, number of stabilizer generators, distance,
malignant-pair count A).

Primary source: Nielsen-Chuang §10.5; Gottesman, PhD thesis (Caltech 1997,
                arXiv:quant-ph/9705052); AGP 2006 §2.
-/

import Mathlib
import SKEFTHawking.FaultTolerance.Basic

set_option autoImplicit false

namespace SKEFTHawking.FaultTolerance

/-! ## 1. The StabilizerCode structure

A `StabilizerCode` packages:
  - `n` = number of physical qubits
  - `k` = number of logical qubits
  - `d` = distance (minimum weight of any nontrivial logical operator)
  - generators: a list of stabilizer Pauli strings of length n, pairwise commuting
  - logical X̄: list of logical-X Pauli strings (k of them)
  - logical Z̄: list of logical-Z Pauli strings (k of them)

We do NOT formalize the codespace semantics here; only the combinatorial data
that AGP threshold counting consumes.
-/

/-- A stabilizer code with parameters [[n, k, d]]. -/
structure StabilizerCode where
  /-- Number of physical qubits. -/
  n : ℕ
  /-- Number of logical qubits encoded. -/
  k : ℕ
  /-- Code distance: minimum weight of any nontrivial logical operator. -/
  d : ℕ
  /-- Stabilizer generators (Pauli strings of length n). The list has length
      `n - k` for a non-degenerate code. -/
  generators : List (PauliString n)
  /-- Logical X operators (one per logical qubit). -/
  logical_x : List (PauliString n)
  /-- Logical Z operators (one per logical qubit). -/
  logical_z : List (PauliString n)
  /-- The number of generators equals `n - k` (rate constraint). -/
  generators_count : generators.length = n - k
  /-- The number of logical-X operators equals `k`. -/
  logical_x_count : logical_x.length = k
  /-- The number of logical-Z operators equals `k`. -/
  logical_z_count : logical_z.length = k
  /-- Distance is at least 1 (every nontrivial logical operator has weight ≥ 1). -/
  distance_pos : 1 ≤ d

namespace StabilizerCode

/-- A code is *distance-3* if any single-qubit error is uniquely identifiable
    by the syndrome, i.e., d ≥ 3. -/
def isDistanceThree (C : StabilizerCode) : Prop := 3 ≤ C.d

/-- A code *protects k=1 logical qubit*. -/
def isSingleLogical (C : StabilizerCode) : Prop := C.k = 1

/-- A `[[7,1,3]]` code: 7 physical qubits, 1 logical, distance 3. -/
def is_7_1_3 (C : StabilizerCode) : Prop := C.n = 7 ∧ C.k = 1 ∧ C.d = 3

/-- A code-parameter triple `[[n, k, d]]`. -/
def parameters (C : StabilizerCode) : ℕ × ℕ × ℕ := (C.n, C.k, C.d)

end StabilizerCode

/-! ## 2. Malignant-pair counts per code

The AGP recursion `ε_{L+1} ≤ A · ε_L²` has `A` as the *malignant-pair count*
for the extended rectangle (ex-Rec) executing a single logical CNOT (or other
gate) at the next level. The malignancy structure depends on the code; for
Steane [[7,1,3]] under abstract local stochastic noise, AGP §5 gives the value.

This is wrapper data — the concrete value for Steane is set in `SteaneCode.lean`
and used by `Counting.lean`.
-/

/-- A *malignant-pair-count assignment* for a stabilizer code, providing
    `A` constants for various gate ex-Recs (the AGP recursion coefficient). -/
structure MalignancyCounts (C : StabilizerCode) where
  /-- Malignant-pair count for the level-1 CNOT ex-Rec. -/
  A_CNOT : ℕ
  /-- Malignant-pair count for the level-1 preparation ex-Rec. -/
  A_prep : ℕ
  /-- Malignant-pair count for the level-1 measurement ex-Rec. -/
  A_meas : ℕ
  /-- Malignant-pair count for the level-1 single-qubit gate ex-Rec. -/
  A_gate1 : ℕ

namespace MalignancyCounts

variable {C : StabilizerCode}

/-- The maximum of the four malignant-pair counts — used as the conservative
    AGP recursion coefficient when bounding any gate at once. -/
def A_max (M : MalignancyCounts C) : ℕ :=
  max (max M.A_CNOT M.A_prep) (max M.A_meas M.A_gate1)

theorem A_max_ge_CNOT (M : MalignancyCounts C) : M.A_CNOT ≤ M.A_max := by
  unfold A_max
  exact le_max_of_le_left (le_max_left _ _)

theorem A_max_ge_prep (M : MalignancyCounts C) : M.A_prep ≤ M.A_max := by
  unfold A_max
  exact le_max_of_le_left (le_max_right _ _)

theorem A_max_ge_meas (M : MalignancyCounts C) : M.A_meas ≤ M.A_max := by
  unfold A_max
  exact le_max_of_le_right (le_max_left _ _)

theorem A_max_ge_gate1 (M : MalignancyCounts C) : M.A_gate1 ≤ M.A_max := by
  unfold A_max
  exact le_max_of_le_right (le_max_right _ _)

end MalignancyCounts

/-! ## 3. Module summary

StabilizerCode.lean: substrate data for AGP threshold theorem.

  - `StabilizerCode` (structure with n, k, d, generators, logical_x, logical_z,
    + length-constraint and distance-pos field).
  - `StabilizerCode.isDistanceThree`, `isSingleLogical`, `is_7_1_3`, `parameters`.
  - `MalignancyCounts C` (structure with A_CNOT, A_prep, A_meas, A_gate1).
  - `MalignancyCounts.A_max` + 4 ge-bound lemmas.

Consumed by Wave 1b.1 SteaneCode (concrete [[7,1,3]] instance), Wave 1b.2
Counting (computes the A constants from ex-Rec structure), Wave 1b.3 AGP/Threshold.

Zero sorry. Zero axioms.
-/

end SKEFTHawking.FaultTolerance
