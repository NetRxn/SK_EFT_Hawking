/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 (increment 10) — the column-synthesis backbone (state preparation, dim 4)

The remaining headline brick is circuit `C`: an `O(k)` Clifford+T word preparing the KMM ancilla state
`|v⟩` (inc 7–9). Faithfully (KMM §2.2 invokes the Giles–Selinger/KMM-1206.5236 exact-synthesis Column
Lemma — there is no guessable explicit circuit), this is the **dim-4 column lemma**: any unit column over
`ℤ[ω][1/√2]` is the first column of a `Gate2` Clifford+T word, with length `O(denominator exponent)`.

This file ships the **structural backbone** of that synthesis, before the (hard) residue-reduction core:

  * `IsColRealizableWithin v L` — `v` is the first column (`M·e₀`) of a `Gate2` word of length `≤ L`.
  * `IsColRealizableWithin.smul_left` — **the induction backbone**: if `G` is realizable within `L'`
    and `v` is column-realizable within `L`, then `G·v` (matrix–vector) is column-realizable within
    `L' + L`. Each reduction step left-multiplies by a generator, so the column-lemma induction is
    exactly iterated `smul_left`; budgets add (`IsRealizableWithin.mul`), giving the `O(k)` length.
  * `isColRealizableWithin_e0` — the base anchor: the computational basis state `e₀ = |00⟩` is
    column-realizable within `0` (the empty word; `M = 1`).

Once the residue-reduction step (`denExp = k+1 ⟹ ∃ O(1)-word g, denExp (g·v) ≤ k`) and the inverse-
closure of the realizable class are in place, `smul_left` + `isColRealizableWithin_e0` assemble the
full `O(k)` column lemma by induction on the denominator exponent.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide`. Kernel-pure `{propext, Classical.choice, Quot.sound}`.
-/

import SKEFTHawking.FKLW.RossSelinger.CliffordTGate2

set_option autoImplicit false

open scoped Matrix

namespace SKEFTHawking.RossSelinger
namespace Gate2

/-- **Column (state-preparation) realizability within a length budget.** A column
`v : Fin 2 × Fin 2 → ZOmegaSqrt2` is **column-realizable within `L`** if it is the first column
(`M · e₀`, i.e. `fun i => M i (0,0)`) of some `Gate2` word of length `≤ L`. This is the target of the
dim-4 exact synthesis: preparing `|v⟩` from `|00⟩`. -/
def IsColRealizableWithin (v : Fin 2 × Fin 2 → ZOmegaSqrt2) (L : ℕ) : Prop :=
  ∃ M : Mat4, IsRealizableWithin M L ∧ (fun i => M i (0, 0)) = v

/-- Weaken the length budget. -/
theorem IsColRealizableWithin.mono {v : Fin 2 × Fin 2 → ZOmegaSqrt2} {L L' : ℕ}
    (h : IsColRealizableWithin v L) (hL : L ≤ L') : IsColRealizableWithin v L' :=
  let ⟨M, hM, hcol⟩ := h; ⟨M, hM.mono hL, hcol⟩

/-- **The induction backbone.** If `G` is realizable within `L'` and `v` is column-realizable within
`L`, then `G · v` (the matrix–vector product) is column-realizable within `L' + L`. The witness is
`G * M` (where `M` prepares `v`): its first column is `G · (M·e₀) = G · v`, and budgets add. The
column lemma is iterated `smul_left` — each residue-reduction step left-multiplies by a generator. -/
theorem IsColRealizableWithin.smul_left {v : Fin 2 × Fin 2 → ZOmegaSqrt2} {G : Mat4} {L L' : ℕ}
    (hG : IsRealizableWithin G L') (hv : IsColRealizableWithin v L) :
    IsColRealizableWithin (G.mulVec v) (L' + L) := by
  obtain ⟨M, hM, hMcol⟩ := hv
  refine ⟨G * M, hG.mul hM, ?_⟩
  funext i
  show (G * M) i (0, 0) = G.mulVec v i
  rw [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun j _ => by rw [← congrFun hMcol j]

/-- **Base anchor**: the computational basis state `e₀ = |00⟩` (`fun i => if i = (0,0) then 1 else 0`)
is column-realizable within `0` — it is the first column of the identity (the empty word). -/
theorem isColRealizableWithin_e0 :
    IsColRealizableWithin (fun i => if i = ((0 : Fin 2), (0 : Fin 2)) then 1 else 0) 0 := by
  refine ⟨1, ⟨[], interp2_nil, le_refl 0⟩, ?_⟩
  funext i
  rw [Matrix.one_apply]

/-- **Every computational basis state is column-realizable within `2`.** The basis state `|a,b⟩`
(`fun i => if i = (a,b) then 1 else 0`) is prepared from `|00⟩` by `X^a ⊗ X^b` — a Clifford word of
`≤ 2` `Gate2` gates (an `onFst X` iff `a = 1`, an `onSnd X` iff `b = 1`). The base-case permutation
piece of the dim-4 column lemma. -/
theorem isColRealizableWithin_basis (a b : Fin 2) :
    IsColRealizableWithin (fun i => if i = (a, b) then 1 else 0) 2 := by
  refine ⟨interp2 ((if a = 1 then [Gate2.onFst .X] else []) ++ (if b = 1 then [Gate2.onSnd .X] else [])),
    ⟨_, rfl, ?_⟩, ?_⟩
  · fin_cases a <;> fin_cases b <;> decide
  · fin_cases a <;> fin_cases b <;> decide

end Gate2
end SKEFTHawking.RossSelinger
