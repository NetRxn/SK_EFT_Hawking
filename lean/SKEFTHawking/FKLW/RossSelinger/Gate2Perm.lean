/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 (increment 30) — basis-permutation words + the pair-alignment table

The `rowOpGadget` (inc 29) performs the Giles–Selinger Lemma-4 row operation at the **canonical**
column pair `{(1,0), (1,1)}` (the `fst = 1` block). The reduction must apply it to an **arbitrary**
matched-active pair, so this file supplies the alignment layer: Clifford permutation words (built
from the two cnots and embedded `X` gates) that relabel the 4 basis indices, pulling any ordered
pair of distinct indices into the canonical slots.

## Headline definitions

  * `permMat f` — the permutation matrix with row `o` carrying its `1` at column `f o`; its column
    action is the **pullback** `(permMat f).mulVec v = v ∘ f`. (A local 0/1-matrix layer is used
    instead of Mathlib's `PEquiv.toMatrix` because the 12-case alignment table below is discharged
    by kernel `decide`, and the `Option`-valued `PEquiv` plumbing obstructs that reduction.)

## Headline theorems

  * `permMat_mulVec` / `permMat_mul` / `permMat_id` — the pullback action and the (anti)composition
    law `permMat f * permMat g = permMat (g ∘ f)`.
  * `cnot01_eq_permMat` / `cnot10_eq_permMat` / `embedFst_X_eq_permMat` / `embedSnd_X_eq_permMat` —
    the four `Gate2` permutation generators identified as `permMat`s of explicit involutions.
  * `exists_pair_alignment` — **the alignment table**: for every ordered pair `p ≠ q` of column
    indices there are mutually-inverse `Gate2` words `w`, `winv` of length `≤ 5`, realizing
    `permMat e` / `permMat e.symm` for an equivalence `e` with `e (1,0) = p`, `e (1,1) = q`.
    Conjugating the inc-29 gadget by these words performs the row operation at `(p, q)`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide` — the table is kernel `decide` (`+kernel` where the word product is deep).
-/

import SKEFTHawking.FKLW.RossSelinger.Gate2Control

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger
namespace Gate2

open ZOmegaSqrt2

/-! ### Permutation matrices over the 4-dimensional register -/

/-- **Permutation matrix (pullback convention)**: row `o` has its `1` at column `f o`, so that
`(permMat f).mulVec v = v ∘ f` — the gate relabels the column entries by `f`. -/
def permMat (f : Fin 2 × Fin 2 → Fin 2 × Fin 2) : Mat4 :=
  Matrix.of fun o i => if i = f o then 1 else 0

/-- **The pullback action**: `permMat f` relabels a column by `f`. -/
theorem permMat_mulVec (f : Fin 2 × Fin 2 → Fin 2 × Fin 2) (v : Fin 2 × Fin 2 → ZOmegaSqrt2) :
    (permMat f).mulVec v = v ∘ f := by
  funext o
  rw [Matrix.mulVec, dotProduct,
    Finset.sum_eq_single_of_mem (f o) (Finset.mem_univ _) (fun i _ hi => by
      show (if i = f o then (1 : ZOmegaSqrt2) else 0) * v i = 0
      rw [if_neg hi, zero_mul])]
  show (if f o = f o then (1 : ZOmegaSqrt2) else 0) * v (f o) = v (f o)
  rw [if_pos rfl, one_mul]

/-- **Anti-composition law**: `permMat f * permMat g = permMat (g ∘ f)` (matrix product applies
`g` first as an action, i.e. the pullbacks compose covariantly). -/
theorem permMat_mul (f g : Fin 2 × Fin 2 → Fin 2 × Fin 2) :
    permMat f * permMat g = permMat (g ∘ f) := by
  ext o i
  rw [Matrix.mul_apply,
    Finset.sum_eq_single_of_mem (f o) (Finset.mem_univ _) (fun k _ hk => by
      show (if k = f o then (1 : ZOmegaSqrt2) else 0) * permMat g k i = 0
      rw [if_neg hk, zero_mul])]
  show (if f o = f o then (1 : ZOmegaSqrt2) else 0) * (if i = g (f o) then 1 else 0) =
    permMat (g ∘ f) o i
  rw [if_pos rfl, one_mul]
  rfl

/-- `permMat id = 1`. -/
theorem permMat_id : permMat id = 1 := by decide

/-! ### The four `Gate2` permutation generators as `permMat`s -/

/-- `cnot01` relabels by `(a, b) ↦ (a, b + a)` (an involution, so the indicator conventions
agree). -/
theorem cnot01_eq_permMat : cnot01 = permMat fun p => (p.1, p.2 + p.1) := by decide

/-- `cnot10` relabels by `(a, b) ↦ (a + b, b)`. -/
theorem cnot10_eq_permMat : cnot10 = permMat fun p => (p.1 + p.2, p.2) := by decide

/-- `X ⊗ I` relabels by `(a, b) ↦ (a + 1, b)`. -/
theorem embedFst_X_eq_permMat :
    embedFst (CliffordTGate.gateMatrix .X) = permMat fun p => (p.1 + 1, p.2) := by decide

/-- `I ⊗ X` relabels by `(a, b) ↦ (a, b + 1)`. -/
theorem embedSnd_X_eq_permMat :
    embedSnd (CliffordTGate.gateMatrix .X) = permMat fun p => (p.1, p.2 + 1) := by decide

/-! ### The pair-alignment table

For the reduction step, an arbitrary matched-active pair `(p, q)` must be pulled into the gadget's
canonical slots `(1,0)`, `(1,1)`. The 12 ordered pairs are each handled by an explicit word of the
four permutation generators (worked out so every word has length `≤ 5`); `fin_cases` enumerates and
kernel `decide` discharges each concrete identification. -/

/-- **The alignment table**: every ordered pair `p ≠ q` of column indices is reachable from the
canonical pair — there are mutually-inverse permutation words `w`, `winv` (length `≤ 5`) realizing
`permMat e` and `permMat e.symm` for an equivalence `e` with `e (1,0) = p` and `e (1,1) = q`.
The aligned column is `(interp2 w).mulVec v = v ∘ e`, placing `v p`, `v q` in the gadget slots. -/
theorem exists_pair_alignment (p q : Fin 2 × Fin 2) (hpq : p ≠ q) :
    ∃ (w winv : List Gate2) (e : (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2)),
      interp2 w = permMat e ∧ interp2 winv = permMat e.symm ∧
      e (1, 0) = p ∧ e (1, 1) = q ∧ w.length ≤ 5 ∧ winv.length ≤ 5 := by
  obtain ⟨p₁, p₂⟩ := p
  obtain ⟨q₁, q₂⟩ := q
  fin_cases p₁ <;> fin_cases p₂ <;> fin_cases q₁ <;> fin_cases q₂
  -- (0,0) → …
  case _ => exact absurd rfl hpq
  case _ => -- p = (0,0), q = (0,1): X⊗I
    exact ⟨[.onFst .X], [.onFst .X],
      ⟨fun r => (r.1 + 1, r.2), fun r => (r.1 + 1, r.2), by decide, by decide⟩,
      by decide +kernel, by decide +kernel, by decide, by decide, by decide, by decide⟩
  case _ => -- p = (0,0), q = (1,0): X⊗I then swap, word [onFst X, cx01, cx10, cx01]
    exact ⟨[.onFst .X, .cx01, .cx10, .cx01], [.cx01, .cx10, .cx01, .onFst .X],
      ⟨fun r => (r.2, r.1 + 1), fun r => (r.2 + 1, r.1), by decide, by decide⟩,
      by decide +kernel, by decide +kernel, by decide, by decide, by decide, by decide⟩
  case _ => -- p = (0,0), q = (1,1): word [cx10, onFst X]
    exact ⟨[.cx10, .onFst .X], [.onFst .X, .cx10],
      ⟨fun r => (r.1 + r.2 + 1, r.2), fun r => (r.1 + r.2 + 1, r.2), by decide, by decide⟩,
      by decide +kernel, by decide +kernel, by decide, by decide, by decide, by decide⟩
  case _ => -- p = (0,1), q = (0,0): word [cx01, onFst X]
    exact ⟨[.cx01, .onFst .X], [.onFst .X, .cx01],
      ⟨fun r => (r.1 + 1, r.2 + r.1), fun r => (r.1 + 1, r.2 + r.1 + 1), by decide, by decide⟩,
      by decide +kernel, by decide +kernel, by decide, by decide, by decide, by decide⟩
  case _ => exact absurd rfl hpq
  case _ => -- p = (0,1), q = (1,0): word [cx01, cx10]
    exact ⟨[.cx01, .cx10], [.cx10, .cx01],
      ⟨fun r => (r.2, r.1 + r.2), fun r => (r.1 + r.2, r.1), by decide, by decide⟩,
      by decide +kernel, by decide +kernel, by decide, by decide, by decide, by decide⟩
  case _ => -- p = (0,1), q = (1,1): swap, word [cx01, cx10, cx01]
    exact ⟨[.cx01, .cx10, .cx01], [.cx01, .cx10, .cx01],
      ⟨fun r => (r.2, r.1), fun r => (r.2, r.1), by decide, by decide⟩,
      by decide +kernel, by decide +kernel, by decide, by decide, by decide, by decide⟩
  case _ => -- p = (1,0), q = (0,0): word [cx01, onFst X, cx01, cx10, cx01]
    exact ⟨[.cx01, .onFst .X, .cx01, .cx10, .cx01], [.cx01, .cx10, .cx01, .onFst .X, .cx01],
      ⟨fun r => (r.2 + r.1, r.1 + 1), fun r => (r.2 + 1, r.1 + r.2 + 1), by decide, by decide⟩,
      by decide +kernel, by decide +kernel, by decide, by decide, by decide, by decide⟩
  case _ => -- p = (1,0), q = (0,1): word [cx10]
    exact ⟨[.cx10], [.cx10],
      ⟨fun r => (r.1 + r.2, r.2), fun r => (r.1 + r.2, r.2), by decide, by decide⟩,
      by decide +kernel, by decide +kernel, by decide, by decide, by decide, by decide⟩
  case _ => exact absurd rfl hpq
  case _ => -- p = (1,0), q = (1,1): identity
    exact ⟨[], [], Equiv.refl _,
      by rw [interp2_nil, ← permMat_id]; rfl, by rw [interp2_nil, ← permMat_id]; rfl,
      rfl, rfl, by decide, by decide⟩
  case _ => -- p = (1,1), q = (0,0): word [cx01, cx10, onFst X]
    exact ⟨[.cx01, .cx10, .onFst .X], [.onFst .X, .cx10, .cx01],
      ⟨fun r => (r.2 + 1, r.1 + r.2), fun r => (r.1 + r.2 + 1, r.1 + 1), by decide, by decide⟩,
      by decide +kernel, by decide +kernel, by decide, by decide, by decide, by decide⟩
  case _ => -- p = (1,1), q = (0,1): word [cx10, cx01]
    exact ⟨[.cx10, .cx01], [.cx01, .cx10],
      ⟨fun r => (r.1 + r.2, r.1), fun r => (r.2, r.1 + r.2), by decide, by decide⟩,
      by decide +kernel, by decide +kernel, by decide, by decide, by decide, by decide⟩
  case _ => -- p = (1,1), q = (1,0): word [cx01]
    exact ⟨[.cx01], [.cx01],
      ⟨fun r => (r.1, r.2 + r.1), fun r => (r.1, r.2 + r.1), by decide, by decide⟩,
      by decide +kernel, by decide +kernel, by decide, by decide, by decide, by decide⟩
  case _ => exact absurd rfl hpq

end Gate2
end SKEFTHawking.RossSelinger
