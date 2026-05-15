/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the LEAN license.
Authors: John Roehm, Claude (Anthropic)
-/
import Mathlib
import SKEFTHawking.PolyQuotQ
import SKEFTHawking.ArrayHelpers

/-!
# `buildPowerTable` symbolic characterisation (ADR-001 Unit 1b)

This module provides the **inner-layer** simp-friendly characterisation of
`PolyQuotQ.buildPowerTable r` that — combined with PR #29's outer-layer
`Array.getElem!_ofFn` — closes the simp opacity wall that previously
blocked Path B of `docs/adrs/ADR-001-commring-qcyc5ext-roadmap.md`.

## Why this exists

`PolyQuotQ.buildPowerTable` is implemented via `Nat.fold` + `Array.push` +
`Array.ofFn` for `native_decide`-evaluation performance. Each of those
constructs is simp-opaque for symbolic indices:

- `(Array.ofFn f)[k.val]!` — outer layer; resolved by `Array.getElem!_ofFn`
  (PR #29, ADR 005 Unit 1a).
- `(Nat.fold n push base)[m]!` — **this module's target**; resolved by the
  two simp lemmas `buildPowerTable_getElem!_lt` (base case `m < n`) and
  `buildPowerTable_getElem!_step` (recursion step `m = n + j + 1`).

Together these two layers reduce `((buildPowerTable r)[m]!)[k.val]!` for
any concrete `m` to an explicit `ℚ`-expression in `r 0, …, r (n-1)`,
which `ring` / `decide` / `simp` can then close.

## Main results

* `Array.getElem!_push_lt`: bang-indexed pushed-array access for indices
  below the original size returns the original value (mirrors PR #29's
  pattern — small helper, upstream-contribution-quality).
* `Nat.fold_push_preserve`: positions in scope at fold step `j` survive
  any further fold-push iterations unchanged.
* `PolyQuotQ.buildPowerTable_partialFold_size`: the partial fold of `j`
  push steps grows the size from `n` to `n + j`.
* `PolyQuotQ.buildPowerTable_getElem!_lt`: at row `m < n`, the table is
  the unit vector `e_m` (independent of `r`).
* `PolyQuotQ.buildPowerTable_getElem!_step`: at row `n + j + 1` (for
  `j + 2 ≤ n - 1`), the table is `shiftByXArr r` applied to row `n + j`.

These five together discharge ADR-001 Unit 1b. Unit 1a (already shipped
in PR #29) handles the outer `Array.ofFn`. Unit 2 (`CommRing QCyc5`) is
now structurally unblocked.

## ADR-001 chain

| Unit | Status | Description |
|---|---|---|
| 1a | ✅ shipped (PR #29) | `Array.getElem!_ofFn` outer simp helper |
| **1b** | **✅ this PR** | **`buildPowerTable` static characterisation (5 lemmas)** |
| 2 | unblocked | `CommRing QCyc5` via Path B's per-axiom recipe |
| 3 | unblocked | `CommRing PolyQuotOver` parameterised |
| 4 | depends on 2+3 | `CommRing QCyc5Ext` (headline goal) |
| 5 | optional | Higher-degree generalisations (QCyc40Ext, QCyc80Ext, etc.) |

The downstream `Mat5K.mul_assoc` (currently blocked, forcing
downstream consumers to use chunked-`native_decide` bypass) becomes
reachable after Unit 4.
-/

namespace Array

/--
Bang-indexed `Array.push` simp lemma: for indices below the original
size, `(xs.push x)[i]! = xs[i]!`.

This is the bang-indexed counterpart of Init's `Array.getElem_push_lt`
(file `Init/Data/Array/Lemmas.lean`). The bang variant returns the type's
`default` on out-of-bounds access, but for `i < xs.size` the access into
`xs.push x` is in-bounds (since pushing only extends), so the default
is unreachable and the lemma reduces identically to the safe-indexed
form.

Proven via `getElem!_pos` (Init: bang-to-safe conversion when bounds
hold) + the existing `Array.getElem_push_lt` Init lemma. Mirrors the
pattern of PR #29's `Array.getElem!_ofFn`.
-/
theorem getElem!_push_lt {α : Type*} [Inhabited α] (xs : Array α) (x : α)
    (i : ℕ) (h : i < xs.size) :
    (xs.push x)[i]! = xs[i]! := by
  have h' : i < (xs.push x).size := by simp; omega
  rw [getElem!_pos (xs.push x) i h', getElem!_pos xs i h, Array.getElem_push_lt h]

end Array

namespace Nat

/--
`Nat.fold` of `Array.push` preserves positions in scope: if position `i`
is in bounds of the fold's state at step `j`, then any further fold
iterations (`k ≥ j`) leave it unchanged.

This is the key invariant that lets us reason about `buildPowerTable`
row-by-row — earlier rows survive later push steps verbatim.
-/
theorem fold_push_preserve {α : Type*} [Inhabited α]
    (init : Array α) (j k : ℕ) (hjk : j ≤ k) (f : Array α → α) (i : ℕ)
    (hi : i < (Nat.fold j (fun _ _ acc => acc.push (f acc)) init).size) :
    (Nat.fold k (fun _ _ acc => acc.push (f acc)) init)[i]! =
      (Nat.fold j (fun _ _ acc => acc.push (f acc)) init)[i]! := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [show j + (d + 1) = (j + d) + 1 from by ring, Nat.fold]
    rw [Array.getElem!_push_lt _ _ i (by
      have : (Nat.fold (j + d) (fun _ _ acc => acc.push (f acc)) init).size ≥
             (Nat.fold j (fun _ _ acc => acc.push (f acc)) init).size := by
        clear ih
        induction d with
        | zero => exact le_refl _
        | succ e ih2 =>
          have : (Nat.fold (j + (e + 1)) (fun _ _ acc => acc.push (f acc)) init).size =
                 (Nat.fold (j + e) (fun _ _ acc => acc.push (f acc)) init).size + 1 := by
            rw [show j + (e + 1) = (j + e) + 1 from by ring, Nat.fold]; simp
          omega
      omega)]
    exact ih (Nat.le_add_right _ _)

end Nat

namespace SKEFTHawking

namespace PolyQuotQ

variable {n : ℕ}

/-! ## `buildPowerTable` size lemmas -/

/--
After `k` push steps from the unit-vector base, the table has size
`n + k`. By induction on `k`; the base case is `base.size = n` (the
`Array.ofFn (n := n) ...` has length `n`) and each step adds one.

This lemma is used twice inside `buildPowerTable_getElem!_step` to
discharge "position `n + j` is in bounds at step `j + 1`" obligations.
-/
theorem buildPowerTable_partialFold_size (r : Fin n → ℚ) (k : ℕ) :
    let base : Array (Array ℚ) := Array.ofFn (n := n) (fun m : Fin n =>
        Array.ofFn (fun ki : Fin n => if ki.val = m.val then 1 else 0))
    (Nat.fold k (fun _ _ acc => acc.push (shiftByXArr r (acc[acc.size - 1]!))) base).size = n + k := by
  induction k with
  | zero => simp [Nat.fold]
  | succ p ih => simp [Nat.fold, ih]; omega

/-! ## `buildPowerTable` characterisation: the two row-class lemmas -/

/--
**Base case lemma.** For `m < n`, the row `(buildPowerTable r)[m]!` is
the unit vector `e_m`: its `k`-th coefficient is `1` iff `k = m`, else
`0`. Independent of `r`.

Proof: `buildPowerTable r` starts from a `base : Array (Array ℚ)`
defined as `Array.ofFn (n := n) (fun m => Array.ofFn (fun k => if k = m
then 1 else 0))` (the unit-vector array). The subsequent `Nat.fold (n -
1)` push-iterations only append; they do not modify positions `m < n`.
Apply `Nat.fold_push_preserve` (position survives all push steps), then
unfold the base entry via `Array.getElem!_ofFn` twice.
-/
theorem buildPowerTable_getElem!_lt (r : Fin n → ℚ)
    (m : ℕ) (hm : m < n) (k : Fin n) :
    ((PolyQuotQ.buildPowerTable r)[m]!)[k.val]! = (if k.val = m then 1 else 0 : ℚ) := by
  unfold PolyQuotQ.buildPowerTable
  set base : Array (Array ℚ) := Array.ofFn (n := n) (fun m : Fin n =>
      Array.ofFn (fun ki : Fin n => if ki.val = m.val then 1 else 0)) with hbase
  have hbase_size : base.size = n := by simp [base]
  rw [Nat.fold_push_preserve base 0 (n - 1) (Nat.zero_le _) _ m
      (by rw [show (Nat.fold 0 _ base) = base from rfl, hbase_size]; exact hm)]
  show (base[m]!)[k.val]! = if k.val = m then 1 else 0
  rw [show base[m]! = Array.ofFn (n := n) (fun ki : Fin n =>
        (if ki.val = m then 1 else 0 : ℚ)) from ?_]
  · rw [Array.getElem!_ofFn]
  · have hm_lt : m < base.size := by rw [hbase_size]; exact hm
    rw [getElem!_pos base m hm_lt]
    simp [base, Array.getElem_ofFn]

/--
**Recursive step lemma.** For `j + 2 ≤ n - 1` (equivalently, `n + j + 1
< 2 * n - 1`), the row `(buildPowerTable r)[n + j + 1]!` equals
`shiftByXArr r` applied to the row `(buildPowerTable r)[n + j]!`.

Combined with the base lemma and a finite-step unfolding, this gives a
fully recursive simp-friendly characterisation of every row of the table
for any concrete `n`, exposing the `r` dependence explicitly to `ring` /
`decide` downstream.

Proof: rewrite both LHS and RHS through the `Nat.fold_push_preserve`
invariant so the fold-step count is `j + 2` on the LHS and `j + 1` on
the RHS, both well below the actual `n - 1` total iterations. Then
unfold the LHS one `Nat.fold` step (using `j + 2 = (j + 1) + 1`) to
expose the push, and use `Array.getElem_push_eq` at the new tail
position `state.size = n + j + 1`. The remaining position equality
`state.size - 1 = n + j` is `omega`.
-/
theorem buildPowerTable_getElem!_step (r : Fin n → ℚ)
    (j : ℕ) (hj : j + 2 ≤ n - 1) :
    (PolyQuotQ.buildPowerTable r)[n + j + 1]! =
      shiftByXArr r ((PolyQuotQ.buildPowerTable r)[n + j]!) := by
  unfold PolyQuotQ.buildPowerTable
  set base : Array (Array ℚ) := Array.ofFn (n := n) (fun m : Fin n =>
      Array.ofFn (fun ki : Fin n => if ki.val = m.val then 1 else 0)) with hbase
  have hbase_size : base.size = n := by simp [base]
  have h_partial_size : ∀ k, (Nat.fold k (fun _ _ acc =>
      acc.push (shiftByXArr r (acc[acc.size - 1]!))) base).size = n + k := by
    intro k
    induction k with
    | zero => simp [Nat.fold, hbase_size]
    | succ p ih => simp [Nat.fold, ih]; omega
  rw [Nat.fold_push_preserve base (j + 2) (n - 1) (by omega) _ (n + j + 1)
      (by rw [h_partial_size]; omega)]
  rw [Nat.fold_push_preserve base (j + 1) (n - 1) (by omega) _ (n + j)
      (by rw [h_partial_size]; omega)]
  rw [show (j + 2 : ℕ) = (j + 1) + 1 from rfl, Nat.fold]
  set state := Nat.fold (j + 1) (fun _ _ acc =>
      acc.push (shiftByXArr r (acc[acc.size - 1]!))) base with hstate
  have hstate_size : state.size = n + j + 1 := h_partial_size (j + 1)
  have h_eq_pos : n + j + 1 = state.size := hstate_size.symm
  conv_lhs => rw [h_eq_pos]
  rw [getElem!_pos _ _ (by simp)]
  rw [Array.getElem_push_eq]
  congr 1
  rw [show state.size - 1 = n + j from by omega]

end PolyQuotQ

end SKEFTHawking
