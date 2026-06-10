/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 (increment 34) — three-qubit Clifford+T gate semantics (system + 2 ancillas)

The KMM ≤2-ancilla z-rotation (arXiv:1212.0822 §2.2–2.3) realizes `Λ(e^{iφ})` as **controlled-`C`**:
the column-lemma word `C` (inc 32–33) prepares `|v⟩` on the two ancillas, and its system-controlled
version sends `(α|0⟩+β|1⟩)⊗|00⟩ ↦ α|0⟩⊗D₀|00⟩ + β|1⟩⊗C|00⟩` — the ancilla-initialized error is
exactly the inc-8/9 amplitude + leakage budget. This file builds the three-qubit register the
controlled lift lives on, mirroring `CliffordTGate2.lean`.

Index convention: `Fin 2 × Fin 2 × Fin 2` (right-associated) = `system × (ancilla₁ × ancilla₂)`,
so the ancilla pair carries the `Mat4` index type natively and the Kronecker embeddings land
without reindexing.

## Headline definitions

  * `Gate3` — generator ADT: a single-qubit gate on any of the three lines plus the six directed
    cnots (all pairs; Toffoli is NOT a generator — it is Clifford+T-composite and will be realized
    as a word).
  * `gateMatrix3` / `interp3` / `IsRealizable3` / `IsRealizable3Within` — semantics + length-tracked
    realizability, with the additive composition law.
  * `embedAnc : Mat4 → Mat8` — the ancilla-pair embedding `M ↦ I₂ ⊗ M` (where circuit `C` lives);
    `liftAnc : Gate2 → Gate3` — the generator-level lift, with the faithful length-preserving
    transport `embedAnc_interp2`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide` — the cnot involutions are kernel `decide`.
-/

import SKEFTHawking.FKLW.RossSelinger.CliffordTGate2

set_option autoImplicit false

open scoped Kronecker

namespace SKEFTHawking.RossSelinger

/-- Three-qubit operators over `ℤ[ω][1/√2]`: index `system × (ancilla₁ × ancilla₂)`. -/
abbrev Mat8 : Type := Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ZOmegaSqrt2

/-- **Three-qubit Clifford+T generator ADT**: single-qubit gates on each line + the six directed
cnots (`cxIJ` = control `I`, target `J`; `s` = system, `a` = ancilla₁, `b` = ancilla₂). -/
inductive Gate3 : Type
  | onSys (g : CliffordTGate) : Gate3
  | onA1 (g : CliffordTGate) : Gate3
  | onA2 (g : CliffordTGate) : Gate3
  | cxsa : Gate3
  | cxsb : Gate3
  | cxab : Gate3
  | cxba : Gate3
  | cxas : Gate3
  | cxbs : Gate3
  deriving DecidableEq, Repr

namespace Gate3

/-- The ancilla-pair embedding: `M ↦ I₂ ⊗ M` — where the column-lemma circuit `C` lives. -/
def embedAnc (M : Mat4) : Mat8 := (1 : Matrix (Fin 2) (Fin 2) ZOmegaSqrt2) ⊗ₖ M

/-- The system-line embedding: `A ↦ A ⊗ I₄`. -/
def embedSys (A : Matrix (Fin 2) (Fin 2) ZOmegaSqrt2) : Mat8 := A ⊗ₖ (1 : Mat4)

@[simp] theorem embedAnc_one : embedAnc (1 : Mat4) = 1 := by
  rw [embedAnc, Matrix.one_kronecker_one]

@[simp] theorem embedSys_one : embedSys (1 : Matrix (Fin 2) (Fin 2) ZOmegaSqrt2) = 1 := by
  rw [embedSys, Matrix.one_kronecker_one]

/-- The ancilla-pair embedding is multiplicative. -/
theorem embedAnc_mul (M N : Mat4) : embedAnc (M * N) = embedAnc M * embedAnc N := by
  show (1 : Matrix (Fin 2) (Fin 2) ZOmegaSqrt2) ⊗ₖ (M * N) = _
  have h := Matrix.mul_kronecker_mul (1 : Matrix (Fin 2) (Fin 2) ZOmegaSqrt2)
    (1 : Matrix (Fin 2) (Fin 2) ZOmegaSqrt2) M N
  rw [one_mul] at h
  exact h

/-- The system-line embedding is multiplicative. -/
theorem embedSys_mul (A B : Matrix (Fin 2) (Fin 2) ZOmegaSqrt2) :
    embedSys (A * B) = embedSys A * embedSys B := by
  show (A * B) ⊗ₖ (1 : Mat4) = _
  have h := Matrix.mul_kronecker_mul A B (1 : Mat4) (1 : Mat4)
  rw [one_mul] at h
  exact h

/-- cnot, control = system, target = ancilla₁: `|s,a,b⟩ ↦ |s, a⊕s, b⟩`. -/
def cnotSA : Mat8 := Matrix.of fun o i => if o = (i.1, i.2.1 + i.1, i.2.2) then 1 else 0

/-- cnot, control = system, target = ancilla₂: `|s,a,b⟩ ↦ |s, a, b⊕s⟩`. -/
def cnotSB : Mat8 := Matrix.of fun o i => if o = (i.1, i.2.1, i.2.2 + i.1) then 1 else 0

/-- cnot, control = ancilla₁, target = system: `|s,a,b⟩ ↦ |s⊕a, a, b⟩`. -/
def cnotAS : Mat8 := Matrix.of fun o i => if o = (i.1 + i.2.1, i.2.1, i.2.2) then 1 else 0

/-- cnot, control = ancilla₂, target = system: `|s,a,b⟩ ↦ |s⊕b, a, b⟩`. -/
def cnotBS : Mat8 := Matrix.of fun o i => if o = (i.1 + i.2.2, i.2.1, i.2.2) then 1 else 0

/-- **Matrix interpretation of a three-qubit generator.** The intra-ancilla gates and cnots embed
the two-qubit semantics; the system-involving cnots are explicit permutation matrices. -/
def gateMatrix3 : Gate3 → Mat8
  | .onSys g => embedSys (CliffordTGate.gateMatrix g)
  | .onA1 g => embedAnc (Gate2.gateMatrix2 (.onFst g))
  | .onA2 g => embedAnc (Gate2.gateMatrix2 (.onSnd g))
  | .cxab => embedAnc cnot01
  | .cxba => embedAnc cnot10
  | .cxsa => cnotSA
  | .cxsb => cnotSB
  | .cxas => cnotAS
  | .cxbs => cnotBS

/-- Interpretation of a three-qubit gate word (first gate leftmost). -/
def interp3 : List Gate3 → Mat8
  | [] => 1
  | g :: gs => gateMatrix3 g * interp3 gs

@[simp] theorem interp3_nil : interp3 [] = 1 := rfl

theorem interp3_cons (g : Gate3) (gs : List Gate3) :
    interp3 (g :: gs) = gateMatrix3 g * interp3 gs := rfl

theorem interp3_append (gs hs : List Gate3) :
    interp3 (gs ++ hs) = interp3 gs * interp3 hs := by
  induction gs with
  | nil => exact (Matrix.one_mul (interp3 hs)).symm
  | cons g gs ih =>
    rw [List.cons_append, interp3_cons, interp3_cons, ih]
    exact (mul_assoc _ _ _).symm

/-- The generator-level lift of a two-qubit gate onto the ancilla pair. -/
def liftAnc : Gate2 → Gate3
  | .onFst g => .onA1 g
  | .onSnd g => .onA2 g
  | .cx01 => .cxab
  | .cx10 => .cxba

/-- **The faithful ancilla transport**: a two-qubit word lifts to a three-qubit word of the same
length acting on the ancilla pair — `embedAnc (interp2 w) = interp3 (w.map liftAnc)`. The
column-lemma circuit `C` rides this onto the enlarged register at no length cost. -/
theorem embedAnc_interp2 (w : List Gate2) :
    embedAnc (Gate2.interp2 w) = interp3 (w.map liftAnc) := by
  induction w with
  | nil => rw [Gate2.interp2_nil, List.map_nil, interp3_nil, embedAnc_one]
  | cons g gs ih =>
    rw [Gate2.interp2_cons, List.map_cons, interp3_cons, embedAnc_mul, ih]
    congr 1
    cases g <;> rfl

@[simp] theorem length_map_liftAnc (w : List Gate2) : (w.map liftAnc).length = w.length := by simp

/-! ### Realizability with length tracking -/

/-- A three-qubit operator is realizable if it is `interp3` of some word. -/
def IsRealizable3 (M : Mat8) : Prop := ∃ w : List Gate3, interp3 w = M

/-- Length-tracked three-qubit realizability. -/
def IsRealizable3Within (M : Mat8) (L : ℕ) : Prop :=
  ∃ w : List Gate3, interp3 w = M ∧ w.length ≤ L

theorem IsRealizable3Within.mono {M : Mat8} {L L' : ℕ} (h : IsRealizable3Within M L)
    (hL : L ≤ L') : IsRealizable3Within M L' :=
  let ⟨w, hw, hlw⟩ := h
  ⟨w, hw, hlw.trans hL⟩

theorem gateMatrix3_realizableWithin_one (g : Gate3) : IsRealizable3Within (gateMatrix3 g) 1 :=
  ⟨[g], by rw [interp3_cons, interp3_nil]; exact Matrix.mul_one _, by simp⟩

/-- **Budgets add under product** — the three-qubit length-composition law. -/
theorem IsRealizable3Within.mul {A B : Mat8} {La Lb : ℕ}
    (hA : IsRealizable3Within A La) (hB : IsRealizable3Within B Lb) :
    IsRealizable3Within (A * B) (La + Lb) := by
  obtain ⟨wa, ha, hla⟩ := hA
  obtain ⟨wb, hb, hlb⟩ := hB
  refine ⟨wa ++ wb, by rw [interp3_append, ha, hb], ?_⟩
  rw [List.length_append]
  omega

/-- An embedded two-qubit `Gate2` word is realizable within its length. -/
theorem embedAnc_realizableWithin (w : List Gate2) {M : Mat4} (hM : Gate2.interp2 w = M) :
    IsRealizable3Within (embedAnc M) w.length :=
  ⟨w.map liftAnc, by rw [← embedAnc_interp2, hM], by simp⟩

/-- An embedded single-qubit word on the system line is realizable within its length. -/
theorem embedSys_realizableWithin (gs : List CliffordTGate) :
    IsRealizable3Within (embedSys (CliffordTGate.interp gs)) gs.length := by
  refine ⟨gs.map .onSys, ?_, by simp⟩
  induction gs with
  | nil => rw [CliffordTGate.interp_nil, List.map_nil, interp3_nil, embedSys_one]
  | cons g gs ih =>
    rw [CliffordTGate.interp_cons, List.map_cons, interp3_cons, embedSys_mul, ih]
    rfl

end Gate3
end SKEFTHawking.RossSelinger
