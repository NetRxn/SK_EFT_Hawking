/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 — two-qubit Clifford+T gate semantics (system + ancilla)

The KMM ancilla mechanism (arXiv:1212.0822) realizes a single-qubit unitary as the system block of
a unitary on the system PLUS up to two ancilla qubits. Where the relative-norm completion is
unconditional (`AncillaCompletion.lean`'s `exists_two_relativeNorms_of_nat`), the resulting amplitude
column lives on the enlarged register; turning it into an actual Clifford+T *circuit* needs two-qubit
gate semantics — which the single-qubit RS substrate (`CliffordTGate.lean`, `Matrix (Fin 2) (Fin 2)`)
does not provide. This file builds that foundation.

Two-qubit operators are `Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ZOmegaSqrt2` so that the Kronecker
product `A ⊗ₖ B` (single-qubit gate on each line) lands natively, with no `Fin 4` reindexing.

## Headline definitions

  * `Gate2` — two-qubit Clifford+T generator ADT: a single-qubit gate on the first (`onFst`) or
    second (`onSnd`) qubit, plus the two entangling `cnot`s (`cx01`, `cx10`).
  * `gateMatrix2` / `interp2` — `4×4` matrix interpretation + gate-list product.
  * `embedFst` / `embedSnd` — `A ↦ A ⊗ I` / `A ↦ I ⊗ A`, the single-qubit→two-qubit embeddings.

## Headline theorems

  * `embedFst_mul` / `embedSnd_mul` (+ `_one`) — the embeddings are **monoid homomorphisms**
    (`mul_kronecker_mul`), so a single-qubit circuit lifts to a two-qubit circuit faithfully.
  * `embedFst_interp` / `embedSnd_interp` — **realizability transport (the load-bearing bridge):** a
    single-qubit Clifford+T word `gs` lifts to the two-qubit word `gs.map onFst` of the **same length**
    with `embedFst (interp gs) = interp2 (gs.map onFst)`. So the shipped single-qubit `kmmReduce`
    synthesis transports onto the ancilla register at no length cost — exactly what the eventual
    O(log 1/ε)-with-≤2-ancillas headline consumes.
  * `cnot01_mul_cnot01` / `cnot10_mul_cnot10` — the cnots are involutions (Clifford primitives).
  * `interp2_append` — `interp2 (gs ++ hs) = interp2 gs * interp2 hs`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide` — the cnot-involution facts are kernel `decide` on the runtime ring.

## References

  * Kliuchnikov–Maslov–Mosca, PRL 110:190502 (2013), arXiv:1212.0822 (the ≤2-ancilla construction).
  * `CliffordTGate.lean` (single-qubit generators) — the template this mirrors.
  * `Mathlib.LinearAlgebra.Matrix.Kronecker` (`mul_kronecker_mul`, `one_kronecker_one`).
-/

import SKEFTHawking.FKLW.RossSelinger.CliffordTGate
import Mathlib.LinearAlgebra.Matrix.Kronecker

set_option autoImplicit false

open scoped Kronecker

namespace SKEFTHawking.RossSelinger

/-- Two-qubit operators over `ZOmegaSqrt2 = ℤ[ω][1/√2]`, indexed by `Fin 2 × Fin 2` (qubit ⊗ qubit)
so the Kronecker product lands without reindexing. -/
abbrev Mat4 : Type := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ZOmegaSqrt2

/-- A single-qubit operator. -/
abbrev Mat2' : Type := Matrix (Fin 2) (Fin 2) ZOmegaSqrt2

/-- **CNOT, control = first qubit, target = second**: `|a,b⟩ ↦ |a, b ⊕ a⟩` (`⊕ = +` in `Fin 2`). -/
def cnot01 : Mat4 := Matrix.of fun out inp => if out = (inp.1, inp.2 + inp.1) then 1 else 0

/-- **CNOT, control = second qubit, target = first**: `|a,b⟩ ↦ |a ⊕ b, b⟩`. -/
def cnot10 : Mat4 := Matrix.of fun out inp => if out = (inp.1 + inp.2, inp.2) then 1 else 0

/-- **Two-qubit Clifford+T generator ADT.** A single-qubit gate on the first or second qubit, plus
the two entangling cnots. (`onFst`/`onSnd` of the single-qubit generators + cnot generate the
two-qubit Clifford+T group.) -/
inductive Gate2 : Type
  | onFst (g : CliffordTGate) : Gate2
  | onSnd (g : CliffordTGate) : Gate2
  | cx01 : Gate2
  | cx10 : Gate2
  deriving DecidableEq, Repr

namespace Gate2

/-- **Single-qubit → two-qubit embedding on the first line**: `A ↦ A ⊗ I`. -/
def embedFst (A : Mat2') : Mat4 := A ⊗ₖ (1 : Mat2')

/-- **Single-qubit → two-qubit embedding on the second line**: `A ↦ I ⊗ A`. -/
def embedSnd (A : Mat2') : Mat4 := (1 : Mat2') ⊗ₖ A

@[simp] theorem embedFst_one : embedFst (1 : Mat2') = 1 := by
  rw [embedFst, Matrix.one_kronecker_one]

@[simp] theorem embedSnd_one : embedSnd (1 : Mat2') = 1 := by
  rw [embedSnd, Matrix.one_kronecker_one]

/-- The first-line embedding is multiplicative (`mul_kronecker_mul`). -/
theorem embedFst_mul (A B : Mat2') : embedFst (A * B) = embedFst A * embedFst B := by
  show (A * B) ⊗ₖ (1 : Mat2') = (A ⊗ₖ (1 : Mat2')) * (B ⊗ₖ (1 : Mat2'))
  have h := Matrix.mul_kronecker_mul A B (1 : Mat2') (1 : Mat2')
  rw [one_mul] at h
  exact h

/-- The second-line embedding is multiplicative. -/
theorem embedSnd_mul (A B : Mat2') : embedSnd (A * B) = embedSnd A * embedSnd B := by
  show (1 : Mat2') ⊗ₖ (A * B) = ((1 : Mat2') ⊗ₖ A) * ((1 : Mat2') ⊗ₖ B)
  have h := Matrix.mul_kronecker_mul (1 : Mat2') (1 : Mat2') A B
  rw [one_mul] at h
  exact h

/-- **Matrix interpretation of a two-qubit Clifford+T generator.** -/
def gateMatrix2 : Gate2 → Mat4
  | .onFst g => embedFst (CliffordTGate.gateMatrix g)
  | .onSnd g => embedSnd (CliffordTGate.gateMatrix g)
  | .cx01 => cnot01
  | .cx10 => cnot10

/-- **Interpretation of a two-qubit gate sequence** as a matrix product (first gate leftmost). -/
def interp2 : List Gate2 → Mat4
  | [] => 1
  | g :: gs => gateMatrix2 g * interp2 gs

@[simp] theorem interp2_nil : interp2 [] = 1 := rfl

theorem interp2_cons (g : Gate2) (gs : List Gate2) :
    interp2 (g :: gs) = gateMatrix2 g * interp2 gs := rfl

/-- `interp2 (gs ++ hs) = interp2 gs * interp2 hs`. -/
theorem interp2_append (gs hs : List Gate2) :
    interp2 (gs ++ hs) = interp2 gs * interp2 hs := by
  induction gs with
  | nil => exact (Matrix.one_mul (interp2 hs)).symm
  | cons g gs ih =>
    rw [List.cons_append, interp2_cons, interp2_cons, ih]
    exact (mul_assoc _ _ _).symm

/-- **Realizability transport (first line).** A single-qubit Clifford+T word `gs` lifts to the
two-qubit word `gs.map onFst` of the **same length**, with `embedFst (interp gs) = interp2 (gs.map
onFst)`. The shipped single-qubit `kmmReduce` synthesis therefore transports onto the system line at
no length cost — the bridge the KMM ancilla headline consumes. -/
theorem embedFst_interp (gs : List CliffordTGate) :
    embedFst (CliffordTGate.interp gs) = interp2 (gs.map .onFst) := by
  induction gs with
  | nil => rw [CliffordTGate.interp_nil, List.map_nil, interp2_nil, embedFst_one]
  | cons g gs ih =>
    rw [CliffordTGate.interp_cons, List.map_cons, interp2_cons, embedFst_mul, ih]
    rfl

/-- **Realizability transport (second line).** -/
theorem embedSnd_interp (gs : List CliffordTGate) :
    embedSnd (CliffordTGate.interp gs) = interp2 (gs.map .onSnd) := by
  induction gs with
  | nil => rw [CliffordTGate.interp_nil, List.map_nil, interp2_nil, embedSnd_one]
  | cons g gs ih =>
    rw [CliffordTGate.interp_cons, List.map_cons, interp2_cons, embedSnd_mul, ih]
    rfl

/-- The map-length is preserved: a single-qubit word and its first-line lift have equal length. -/
@[simp] theorem length_map_onFst (gs : List CliffordTGate) :
    (gs.map Gate2.onFst).length = gs.length := by simp

/-- **CNOT (control-first) is an involution.** `|a,b⟩ ↦ |a,b⊕a⟩` is self-inverse. -/
theorem cnot01_mul_cnot01 : cnot01 * cnot01 = 1 := by decide

/-- **CNOT (control-second) is an involution.** -/
theorem cnot10_mul_cnot10 : cnot10 * cnot10 = 1 := by decide

/-! ## Two-qubit Clifford+T realizable class

The two-qubit analog of the single-qubit `KMM.IsCliffordTRealizable`: the class of operators
expressible as a `Gate2` word. This is the codomain that two-qubit exact synthesis (the remaining
circuit brick) targets; the algebraic closure here is its monoid structure. -/

/-- A two-qubit operator is **Clifford+T-realizable** if it is `interp2` of some `Gate2` word. -/
def IsRealizable (M : Mat4) : Prop := ∃ w : List Gate2, interp2 w = M

/-- The identity is realizable (the empty word). -/
theorem IsRealizable.one : IsRealizable (1 : Mat4) := ⟨[], interp2_nil⟩

/-- Every generator is realizable (the singleton word). -/
theorem gateMatrix2_isRealizable (g : Gate2) : IsRealizable (gateMatrix2 g) :=
  ⟨[g], by rw [interp2_cons, interp2_nil]; exact Matrix.mul_one _⟩

/-- Realizable operators are **closed under product** (word concatenation, `interp2_append`). -/
theorem IsRealizable.mul {A B : Mat4} (hA : IsRealizable A) (hB : IsRealizable B) :
    IsRealizable (A * B) := by
  obtain ⟨wa, ha⟩ := hA
  obtain ⟨wb, hb⟩ := hB
  exact ⟨wa ++ wb, by rw [interp2_append, ha, hb]⟩

/-- The two cnots and every embedded single-qubit generator are realizable (specializations of
`gateMatrix2_isRealizable`). -/
theorem cnot01_isRealizable : IsRealizable cnot01 := gateMatrix2_isRealizable .cx01

theorem cnot10_isRealizable : IsRealizable cnot10 := gateMatrix2_isRealizable .cx10

/-! ## Length-tracked realizability

The O(log 1/ε) headline is a statement about word **length**, so the realizable class is refined to
carry a length budget. The budget is **additive under composition** (`interp2_append` +
`List.length_append`), so a circuit assembled from pieces of length `L₁, …, Lₙ` has length `≤ ΣLᵢ` —
the structure that turns "each piece is O(log 1/ε)" into "the whole circuit is O(log 1/ε)". -/

/-- `M` is **realizable within length `L`** if some `Gate2` word of length `≤ L` interprets to `M`. -/
def IsRealizableWithin (M : Mat4) (L : ℕ) : Prop :=
  ∃ w : List Gate2, interp2 w = M ∧ w.length ≤ L

/-- Weaken the length budget. -/
theorem IsRealizableWithin.mono {M : Mat4} {L L' : ℕ} (h : IsRealizableWithin M L) (hL : L ≤ L') :
    IsRealizableWithin M L' :=
  let ⟨w, hw, hlw⟩ := h; ⟨w, hw, hlw.trans hL⟩

/-- Forget the budget. -/
theorem IsRealizableWithin.isRealizable {M : Mat4} {L : ℕ} (h : IsRealizableWithin M L) :
    IsRealizable M :=
  let ⟨w, hw, _⟩ := h; ⟨w, hw⟩

/-- Each generator is realizable within length `1`. -/
theorem gateMatrix2_realizableWithin_one (g : Gate2) : IsRealizableWithin (gateMatrix2 g) 1 :=
  ⟨[g], by rw [interp2_cons, interp2_nil]; exact Matrix.mul_one _, by simp⟩

/-- **Budgets add under product** (the load-bearing length-composition law): word concatenation gives
`interp2 (wa ++ wb) = A * B` with `length (wa ++ wb) = La' + Lb' ≤ La + Lb`. -/
theorem IsRealizableWithin.mul {A B : Mat4} {La Lb : ℕ}
    (hA : IsRealizableWithin A La) (hB : IsRealizableWithin B Lb) :
    IsRealizableWithin (A * B) (La + Lb) := by
  obtain ⟨wa, ha, hla⟩ := hA
  obtain ⟨wb, hb, hlb⟩ := hB
  refine ⟨wa ++ wb, by rw [interp2_append, ha, hb], ?_⟩
  rw [List.length_append]
  omega

end Gate2
end SKEFTHawking.RossSelinger
