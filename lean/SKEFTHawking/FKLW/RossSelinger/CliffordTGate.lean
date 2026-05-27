/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — Clifford+T gate ADT + matrix interpretation

Ships the **Clifford+T gate algebraic data type** and its `2×2`-matrix
interpretation over `ZOmegaSqrt2 := ℤ[ω][1/√2]`. This is the substrate
that the Kliuchnikov-Maslov-Mosca exact synthesis algorithm (Item F,
`KMM.lean` companion) consumes.

Per Kliuchnikov-Maslov-Mosca 2013 (arXiv:1206.5236) Theorem 1, the set
of `2×2` unitaries over `ZOmegaSqrt2` is **equivalent** to the set
implementable as single-qubit circuits over Clifford+T. The eight gates
covered here (H, S, T, X, Y, Z, id, ω-phase) generate the full
Clifford+T group, with the canonical relations `T⁸ = 1`, `T·T = S`,
`S·S = Z`, `H·H = 1`, `H·X·H = Z`, etc.

## Headline definitions

  * `CliffordTGate` — inductive ADT covering 8 generators.
  * `CliffordTGate.gateMatrix` — `2×2` matrix interpretation over
    `ZOmegaSqrt2`.
  * `CliffordTGate.interp` — interpretation of a `List CliffordTGate`
    as a matrix product.

## Computability note (Phase 6x F substrate ship)

The gate matrices use `noncomputable` arithmetic over `ZOmegaSqrt2`
(`Localization.Away` from Item E's theory-layer ship). Per
Pre-Implementation DR §1.7, a parallel runtime pair-representation
of `ZOmegaSqrt2` (z, k) for `native_decide`-driven test queries is
**deferred** as a follow-on (substantial multi-session work; ~300+ LoC
extension of Item E's ship).

The substantive content shipped here — the gate ADT + matrix
interpretation + the `interp_append` algebraic identity — does not
depend on the runtime representation. Concrete `#eval` testing of small
examples (e.g., `H·H = I`) requires the deferred runtime layer.

## References

  * Pre-Implementation Research Dossier §3.1, §3.3.
  * Kliuchnikov-Maslov-Mosca 2013 (arXiv:1206.5236), Theorem 1.
  * Giles-Selinger 2013 (arXiv:1312.6584), MA normal form.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.ZOmegaSqrt2
import Mathlib.LinearAlgebra.Matrix.Notation

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

/-- **Single-qubit Clifford+T gate ADT**.

Covers the standard generating set:
  * `H` — Hadamard `(1/√2)·⟨⟨1,1⟩,⟨1,-1⟩⟩`.
  * `S` — phase gate `diag(1, i)` (`= T·T`).
  * `T` — π/8 gate `diag(1, ω)` where `ω = e^(iπ/4)`.
  * `X` — bit flip `⟨⟨0,1⟩,⟨1,0⟩⟩`.
  * `Y`, `Z` — Pauli `Y`, `Z`.
  * `id` — identity.
  * `omega` — global phase `ω·I` (needed for ω-determinant tracking
    in KMM exact synthesis).

`DecidableEq` is auto-derived. -/
inductive CliffordTGate : Type
  | H : CliffordTGate
  | S : CliffordTGate
  | T : CliffordTGate
  | X : CliffordTGate
  | Y : CliffordTGate
  | Z : CliffordTGate
  | id : CliffordTGate
  | omega : CliffordTGate
  deriving DecidableEq, Repr

namespace CliffordTGate

/-- `ω = ζ_8` as a `ZOmegaSqrt2` element via the canonical algebra map. -/
noncomputable def ωS : ZOmegaSqrt2 :=
  algebraMap ZOmega ZOmegaSqrt2 ZOmega.ω

/-- `i = ω²` as a `ZOmegaSqrt2` element. -/
noncomputable def iS : ZOmegaSqrt2 := ωS * ωS

/-- **Matrix interpretation of a Clifford+T gate**.

Each gate maps to its standard `2×2` unitary over `ZOmegaSqrt2`:

  * `H ↦ (1/√2)·⟨⟨1,1⟩,⟨1,-1⟩⟩`
  * `S ↦ diag(1, i)` where `i = ω²`
  * `T ↦ diag(1, ω)` where `ω = ζ_8`
  * `X ↦ ⟨⟨0,1⟩,⟨1,0⟩⟩`
  * `Y ↦ ⟨⟨0,-i⟩,⟨i,0⟩⟩`
  * `Z ↦ diag(1, -1)`
  * `id ↦ I` (identity matrix)
  * `omega ↦ ω·I` (global phase)

Per KMM Theorem 1, every `2×2` unitary over `ZOmegaSqrt2` is implementable
as a product of these gates. -/
noncomputable def gateMatrix : CliffordTGate → Matrix (Fin 2) (Fin 2) ZOmegaSqrt2
  | .H => !![ZOmegaSqrt2.invSqrt2, ZOmegaSqrt2.invSqrt2;
              ZOmegaSqrt2.invSqrt2, -ZOmegaSqrt2.invSqrt2]
  | .S => !![1, 0; 0, iS]
  | .T => !![1, 0; 0, ωS]
  | .X => !![0, 1; 1, 0]
  | .Y => !![0, -iS; iS, 0]
  | .Z => !![1, 0; 0, -1]
  | .id => 1
  | .omega => ωS • (1 : Matrix (Fin 2) (Fin 2) ZOmegaSqrt2)

/-- **Interpretation of a gate sequence** as a matrix product.

Convention: `interp [g₁, g₂, ..., gₙ] = gateMatrix g₁ · gateMatrix g₂ · ... · gateMatrix gₙ`.

This is the left-to-right reading: the first gate in the list is the
leftmost (most-significant) factor. Composition follows the matrix-
multiplication convention `gateMatrix g₁ · gateMatrix g₂` meaning "apply
g₂ first, then g₁". -/
noncomputable def interp : List CliffordTGate → Matrix (Fin 2) (Fin 2) ZOmegaSqrt2
  | [] => 1
  | g :: gs => gateMatrix g * interp gs

@[simp] theorem interp_nil : interp [] = 1 := rfl

theorem interp_cons (g : CliffordTGate) (gs : List CliffordTGate) :
    interp (g :: gs) = gateMatrix g * interp gs := rfl

@[simp] theorem interp_singleton (g : CliffordTGate) :
    interp [g] = gateMatrix g := by
  show gateMatrix g * interp [] = gateMatrix g
  simp

/-- **Concatenation of gate sequences is matrix product**:
`interp (gs ++ hs) = interp gs * interp hs`. -/
theorem interp_append (gs hs : List CliffordTGate) :
    interp (gs ++ hs) = interp gs * interp hs := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    show gateMatrix g * interp (gs ++ hs) = (gateMatrix g * interp gs) * interp hs
    rw [ih, mul_assoc]

end CliffordTGate
end SKEFTHawking.RossSelinger
