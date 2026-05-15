/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the LEAN license.
Authors: John Roehm
-/
import Mathlib

/-!
# `Array` helper lemmas for cyclotomic-substrate symbolic reasoning

This module ships small `Array`-related `@[simp]` lemmas that fill gaps
in Lean Init / Mathlib for symbolic reasoning over `Array.ofFn`-based
data structures (`PolyQuotQ`, `PolyQuotOver`, derived cyclotomic types).

## Why this exists

`Init.Data.Array.Lemmas` ships `@[simp] theorem getElem_ofFn` (line 4265)
for safe indexing `(Array.ofFn f)[i] = f ⟨i, h⟩`, but **not** the
bang-indexed counterpart `(Array.ofFn f)[i.val]! = f i`. The
performance-oriented `mulReduce` machinery in `SKEFTHawking.PolyQuotQ` /
`PolyQuotOver` materializes intermediate computations into `Array` via
`Array.ofFn` and then reads them back via `[i.val]!` for native-code
efficiency. Without a bang-indexed simp lemma, downstream `simp`-based
reasoning about `mulReduce` outputs hits a definitional opacity wall —
specifically the 200k-heartbeat timeout observed when attempting to
register `CommRing QCyc5Ext` (see `docs/adrs/ADR-001-commring-qcyc5ext-roadmap.md`).

This file adds the missing simp-friendly bang-indexed lemma. With it,
the **outer** layer of `mulReduce`'s simp opacity dissolves; the inner
`buildPowerTable` recursion remains as the ADR's "Unit 1" multi-PR
bottleneck (the recursion has its own simp-blowup characteristics that
require a separate static characterization lemma).

## Scope

This module is intentionally small (one helper lemma). Future
`Array`-related infrastructure can be added here. The lemma is upstream-
contribution-quality (it could be PR'd to Lean Init's
`Array.Lemmas` directly); we ship it locally for immediate use.
-/

namespace Array

/--
Bang-indexed `Array.ofFn` simp lemma: `(Array.ofFn f)[k.val]! = f k`
when `k : Fin n` (so the bounds check is automatic).

This is the bang-indexed counterpart of Init's `Array.getElem_ofFn`
(file `Init/Data/Array/Lemmas.lean`, line 4265). The bang variant
returns the type's `default` value on out-of-bounds access, but for
`k : Fin n` indexing into `Array.ofFn (f : Fin n → α)` the bounds
always hold, so the default is unreachable and the lemma reduces
identically to the safe-indexed variant.

**Why this matters:** the `SKEFTHawking.PolyQuotQ.mulReduce` machinery
uses `(Array.ofFn ... )[k.val]!` for performance (`native_decide`
compatibility — `getD`-based access would inhibit decidable evaluation).
Without this lemma, `simp` can't unfold past the bang access, blocking
abstract ring-axiom proofs.

Proven via `getElem!_pos` (Init: converts bang-to-safe access when
bounds hold) + the existing `@[simp] Array.getElem_ofFn` Init lemma.
-/
@[simp]
theorem getElem!_ofFn {α : Type*} [Inhabited α] {n : ℕ}
    (f : Fin n → α) (k : Fin n) :
    (Array.ofFn f)[k.val]! = f k := by
  rw [getElem!_pos _ _ (by simp [k.isLt])]
  simp

end Array
