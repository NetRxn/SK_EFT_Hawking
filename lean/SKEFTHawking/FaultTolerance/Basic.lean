/-
SK_EFT_Hawking Phase 6p Wave 1b.1: FaultTolerance Basic Primitives

Basic data types for the AGP threshold theorem (Wave 1b.3):
  - `Pauli`: the four single-qubit Pauli operators {I, X, Y, Z}
  - `PauliN n`: tensor product of n Pauli operators (a Pauli string of length n)
  - `Location`: a (qubit-index, time-index) pair locating a circuit position
  - `CircuitOp`: a single Clifford-class operation (Pauli prep, measurement, gate)

Substrate-only — no Mathlib MeasureTheory dependency. Theorems consumed by
Wave 1b.2 (NoiseModel + ExRec) and Wave 1b.3 (AGP/Threshold).

Relation to existing libraries:
  - inQWIRE / LeanQuantum (Lean 4): v0.x; vendor minimal substrate here per DR R2.
  - Coq-QECC: stabilizer formalism; no threshold connection.
  - QWIRE / SQIR: linear-type circuits; no threshold.

Primary source: Nielsen-Chuang (Quantum Computation and Quantum Information,
                Cambridge 2010) §10.5 + AGP 2006 (arXiv:quant-ph/0504218) §2.
-/

import Mathlib

namespace SKEFTHawking.FaultTolerance

/-! ## 1. Single-qubit Pauli operators

The Pauli group on one qubit (modulo phase) has four elements: I, X, Y, Z.
We model only the operator labels; phases are tracked separately when needed.
-/

/-- Single-qubit Pauli operator label. -/
inductive Pauli : Type
  | I  -- Identity
  | X  -- Pauli X (bit flip)
  | Y  -- Pauli Y
  | Z  -- Pauli Z (phase flip)
  deriving DecidableEq, Repr, Inhabited

namespace Pauli

/-- The four Pauli labels. -/
def all : List Pauli := [I, X, Y, Z]

theorem mem_all (p : Pauli) : p ∈ all := by
  cases p <;> decide

/-- Pauli is finite (has 4 elements). -/
instance : Fintype Pauli where
  elems := {I, X, Y, Z}
  complete := by intro p; cases p <;> decide

/-- Multiplication on Pauli labels (modulo phase).
    Phase is dropped; this is the projection P_n → P_n/{±1, ±i}. -/
def mul : Pauli → Pauli → Pauli
  | I, p => p
  | p, I => p
  | X, X => I
  | Y, Y => I
  | Z, Z => I
  | X, Y => Z
  | Y, X => Z
  | Y, Z => X
  | Z, Y => X
  | X, Z => Y
  | Z, X => Y

instance : Mul Pauli := ⟨mul⟩

/-- Identity is multiplicative identity. -/
theorem I_mul (p : Pauli) : I * p = p := by cases p <;> rfl
theorem mul_I (p : Pauli) : p * I = p := by cases p <;> rfl

/-- Squaring any Pauli returns I. -/
theorem mul_self (p : Pauli) : p * p = I := by cases p <;> rfl

/-- Whether two Pauli labels commute (modulo phase).
    P_1 P_2 = P_2 P_1 in the projective Pauli group iff they're equal or one is I. -/
def commutes (p q : Pauli) : Bool :=
  match p, q with
  | I, _ => true
  | _, I => true
  | X, X => true
  | Y, Y => true
  | Z, Z => true
  | _, _ => false

end Pauli

/-! ## 2. Pauli strings of length n

A `PauliString n` is a length-n list of Pauli labels; tensor-product structure.
Sufficient substrate for stabilizer generators on `n` qubits.
-/

/-- A Pauli string of length `n` on `n` qubits. -/
abbrev PauliString (n : ℕ) : Type := Fin n → Pauli

namespace PauliString

variable {n : ℕ}

/-- The all-identity Pauli string. -/
def id : PauliString n := fun _ => Pauli.I

/-- Componentwise multiplication of Pauli strings. -/
def mul (p q : PauliString n) : PauliString n := fun i => p i * q i

instance : Mul (PauliString n) := ⟨mul⟩

/-- Whether two Pauli strings commute (modulo phase).
    They commute iff the number of anticommuting positions is even. -/
def commutes (p q : PauliString n) : Bool :=
  decide ((Finset.univ.filter (fun i => ¬ (p i).commutes (q i))).card % 2 = 0)

/-- Weight (number of non-identity positions) of a Pauli string. -/
def weight [DecidableEq Pauli] (p : PauliString n) : ℕ :=
  (Finset.univ.filter (fun i => p i ≠ Pauli.I)).card

end PauliString

/-! ## 3. Circuit locations

A `Location` is a (qubit-index, time-step) pair identifying a position in a
quantum circuit. Used by `NoiseModel` (each location may fail independently)
and `Malignant` (which counts pairs of locations whose joint failure is fatal).
-/

/-- A location in a quantum circuit: which qubit at which time step. -/
structure Location (n_qubits : ℕ) (n_time : ℕ) where
  qubit : Fin n_qubits
  time  : Fin n_time
  deriving DecidableEq, Repr

namespace Location

variable {n_qubits n_time : ℕ}

/-- The total number of locations in an `n_qubits × n_time` circuit. -/
def card_locations (n_qubits n_time : ℕ) : ℕ := n_qubits * n_time

end Location

/-! ## 4. Circuit operations

We model the AGP-relevant Clifford operations at the *label* level. Phase
tracking and gate semantics are deferred — the AGP threshold theorem only
needs the location-count and the (qubit, time)-failure-event structure.
-/

/-- A single Clifford-class circuit operation label. -/
inductive CircuitOp : Type
  | prep_zero  : CircuitOp        -- prepare |0⟩
  | prep_plus  : CircuitOp        -- prepare |+⟩
  | meas_z     : CircuitOp        -- measure Z
  | meas_x     : CircuitOp        -- measure X
  | gate_h     : CircuitOp        -- Hadamard
  | gate_s     : CircuitOp        -- phase gate S = diag(1, i)
  | gate_cnot  : CircuitOp        -- 2-qubit CNOT
  | wait       : CircuitOp        -- idle (subject to memory error)
  deriving DecidableEq, Repr, Inhabited

namespace CircuitOp

/-- How many qubits the operation acts on. -/
def arity : CircuitOp → ℕ
  | prep_zero | prep_plus | meas_z | meas_x | gate_h | gate_s | wait => 1
  | gate_cnot => 2

end CircuitOp

/-! ## 5. Module summary

Basic.lean: substrate data for AGP threshold theorem.

  - `Pauli` (inductive {I, X, Y, Z}), `Fintype`, `Mul`, `commutes`, `mul_self : p*p = I`.
  - `PauliString n` (= `Fin n → Pauli`), `id`, `mul`, `commutes`, `weight`.
  - `Location n_qubits n_time` (structure with `qubit`, `time` fields).
  - `CircuitOp` (inductive: prep_zero/prep_plus/meas_z/meas_x/gate_h/gate_s/gate_cnot/wait), `arity`.

Consumed by Wave 1b.1 SteaneCode, Wave 1b.2 NoiseModel + ExRec, Wave 1b.3
Concatenation + AGP/Threshold.

Zero sorry. Zero axioms.
-/

end SKEFTHawking.FaultTolerance
