/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6z Wave 4 increment 4f.1 — Clifford transitivity on the 63 Pauli labels

The combinatorial heart of the Clifford-adjoint irreducibility: the 3-qubit Clifford group acts
**transitively** on the 63 nonzero Pauli labels `Fin 4 × Fin 4 × Fin 4 \ {0}` (the labels of the 63
tensor-Pauli lines `ℝ·kronK8 v`). The Clifford generators act on a Pauli label by the standard
stabilizer tableau (in the `F₂²` symplectic `(x,z)` encoding `I=(0,0)`, `X=(1,0)`, `Y=(1,1)`, `Z=(0,1)`):

  * **H** on qubit `q`: swaps `X ↔ Z` (swaps the `(x,z)` bits), fixes `I, Y`.
  * **S** on qubit `q`: `X ↦ Y`, `Y ↦ X` (`z ↦ z + x`), fixes `I, Z`.
  * **CNOT** control `c`, target `t`: `xc ↦ xc`, `zc ↦ zc + zt`, `xt ↦ xt + xc`, `zt ↦ zt`.

Each generator is a label **involution**, so the generated group is the closure under the generator set.
Transitivity is the finite fact that the orbit of `X ⊗ I ⊗ I` under the 9 generators
(`H_q, S_q` for `q = 0,1,2` and `CNOT` for the pairs `(0,1), (0,2), (1,2)`) is **all 63 nonzero labels**;
it is discharged by **kernel** `decide` (no `native_decide`) on a `List`-based orbit closure, with
`maxRecDepth` raised so the kernel can reduce the finite closure (this is the finite-decision-procedure
exemption, *not* a `maxHeartbeats` compute-budget shortcut — Pipeline Invariant #10 bans only the latter).

The matrix tableau lifts `gen · kronK8 v · gen⁻¹ = ± kronK8 (φ_gen v)` (connecting these label maps to the
actual SU(8) conjugations) and the W-membership transport are the companion increments.

## Pipeline invariants

  * **#10** (no `maxHeartbeats` in proofs): respected (`maxRecDepth` ≠ `maxHeartbeats`).
  * **#15** (no new project-local axioms): respected. Kernel-pure (no `native_decide`/`Lean.ofReduceBool`).

## Phase 6z provenance

Phase 6z Wave 4 increment 4f.1 (Clifford label transitivity). 2026-05-28.
-/

import Mathlib

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

/-- A Pauli label: a tensor-Pauli `σ_a ⊗ σ_b ⊗ σ_c` is indexed by `(a, b, c) : Fin 4 × Fin 4 × Fin 4`
(`0 = I, 1 = X, 2 = Y, 3 = Z` on each qubit). -/
abbrev PauliLabel : Type := Fin 4 × Fin 4 × Fin 4

/-- The `x`-bit of the `F₂²` symplectic encoding (`I,Y ↦ 0`; `X,Z`… `I↦0,X↦1,Y↦1,Z↦0`). -/
def labelXBit : Fin 4 → ZMod 2 := ![0, 1, 1, 0]

/-- The `z`-bit of the `F₂²` symplectic encoding (`I↦0, X↦0, Y↦1, Z↦1`). -/
def labelZBit : Fin 4 → ZMod 2 := ![0, 0, 1, 1]

/-- Rebuild a Pauli label from its `(x, z)` symplectic bits. -/
def labelOfBits (x z : ZMod 2) : Fin 4 :=
  if x = 0 then (if z = 0 then 0 else 3) else (if z = 0 then 1 else 2)

/-- The H-conjugation label map (`X ↔ Z`, `I, Y` fixed). -/
def hLabel : Fin 4 → Fin 4 := ![0, 3, 2, 1]

/-- The S-conjugation label map (`X ↔ Y`, `I, Z` fixed). -/
def sLabel : Fin 4 → Fin 4 := ![0, 2, 1, 3]

/-- The CNOT-conjugation label map on a (control, target) pair. -/
def cnotLabelPair (c t : Fin 4) : Fin 4 × Fin 4 :=
  (labelOfBits (labelXBit c) (labelZBit c + labelZBit t),
   labelOfBits (labelXBit t + labelXBit c) (labelZBit t))

/-- Apply a single-qubit label map on qubit `q ∈ {0,1,2}`. -/
def onQubit (f : Fin 4 → Fin 4) (q : Fin 3) (v : PauliLabel) : PauliLabel :=
  match q with
  | 0 => (f v.1, v.2.1, v.2.2)
  | 1 => (v.1, f v.2.1, v.2.2)
  | 2 => (v.1, v.2.1, f v.2.2)

/-- Apply the CNOT label map on one of the pairs `(0,1), (0,2), (1,2)`. -/
def cnotLabel (c t : Fin 3) (v : PauliLabel) : PauliLabel :=
  if c = 0 ∧ t = 1 then (let p := cnotLabelPair v.1 v.2.1; (p.1, p.2, v.2.2))
  else if c = 0 ∧ t = 2 then (let p := cnotLabelPair v.1 v.2.2; (p.1, v.2.1, p.2))
  else (let p := cnotLabelPair v.2.1 v.2.2; (v.1, p.1, p.2))

/-- The 9 Clifford label generators: `H_q, S_q` for `q = 0,1,2` and `CNOT` for `(0,1), (0,2), (1,2)`. -/
def cliffordLabelGens : List (PauliLabel → PauliLabel) :=
  [onQubit hLabel 0, onQubit hLabel 1, onQubit hLabel 2,
   onQubit sLabel 0, onQubit sLabel 1, onQubit sLabel 2,
   cnotLabel 0 1, cnotLabel 0 2, cnotLabel 1 2]

/-- One orbit-expansion step: add all single-generator images of the current label list (deduped). -/
def cliffordLabelStep (S : List PauliLabel) : List PauliLabel :=
  (S ++ (cliffordLabelGens.flatMap (fun g => S.map g))).dedup

/-- The orbit of `X ⊗ I ⊗ I` after 6 expansion steps (saturates the full 63-label orbit). -/
def cliffordLabelOrbit : List PauliLabel := cliffordLabelStep^[6] [((1, 0, 0) : PauliLabel)]

set_option maxRecDepth 100000 in
/-- **Clifford transitivity on the Pauli labels** (kernel `decide`): every nonzero Pauli label lies in
the Clifford orbit of `X ⊗ I ⊗ I`. Hence the 3-qubit Clifford group acts transitively on the 63
tensor-Pauli lines — the combinatorial core of the Clifford-adjoint irreducibility on `𝔰𝔲(8)`. -/
theorem clifford_label_transitive (v : PauliLabel) (hv : v ≠ 0) : v ∈ cliffordLabelOrbit := by
  revert hv; revert v; decide

end SKEFTHawking.FKLW.CliffordCCZSU8
