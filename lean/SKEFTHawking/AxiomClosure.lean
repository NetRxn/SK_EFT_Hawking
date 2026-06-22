/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# AxiomClosure — memoized transitive axiom-dependency closure (shared utility)

A single-pass, cycle-safe, **memoized** replacement for calling `Lean.collectAxioms` independently on
every declaration. The per-decl re-walk in `ExtractDeps.lean` recomputes overlapping closures and
profiles at ~0.1s/decl × ~16k decls ≈ 27 min (hitting the extraction timeout). This computes every
declaration's axiom closure in ONE traversal of the shared constant-dependency graph.

**Faithfulness.** The edge relation + axiom-leaf set mirror `Lean/Util/CollectAxioms.lean` exactly
(axiom→type; defn/thm/opaque→type∪value; ctor/rec→type; induct→type∪ctors; quot/none→∅; an
`axiomInfo` constant is a leaf that contributes itself). The result per declaration is therefore the
identical SET that `collectAxioms` returns — validated by a parity check (`AxiomClosureParity`).

**Cycle-safety.** Mutual recursion / recursors create cycles in the constant graph. A naive memoized
DFS under-reports axioms for cycle-internal nodes (all SCC members must share the union of the SCC's
reachable axioms). We use Tarjan's algorithm and compute each SCC's closure at pop time — Tarjan
finalizes SCCs in reverse-topological order, so an SCC's out-of-component successors are already
finalized when it is popped.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): N/A (this is `meta`/`IO` infrastructure, not a proof).
  * **#15** (no new project-local axioms): respected (no `axiom` declarations here).
-/

import Lean

open Lean

namespace SKEFTHawking.AxiomClosure

/-- Direct dependencies (the constants `collectAxioms` recurses into) and whether `c` is itself an
axiom, mirroring `Lean/Util/CollectAxioms.lean`'s per-`ConstantInfo` cases. -/
def constDeps (env : Environment) (c : Name) : Array Name × Bool :=
  match env.find? c with
  | some (.axiomInfo v)  => (v.type.getUsedConstantsAsSet.toArray, true)
  | some (.defnInfo v)   => ((v.type.getUsedConstantsAsSet.union v.value.getUsedConstantsAsSet).toArray, false)
  | some (.thmInfo v)    => ((v.type.getUsedConstantsAsSet.union v.value.getUsedConstantsAsSet).toArray, false)
  | some (.opaqueInfo v) => ((v.type.getUsedConstantsAsSet.union v.value.getUsedConstantsAsSet).toArray, false)
  | some (.quotInfo _)   => (#[], false)
  | some (.ctorInfo v)   => (v.type.getUsedConstantsAsSet.toArray, false)
  | some (.recInfo v)    => (v.type.getUsedConstantsAsSet.toArray, false)
  | some (.inductInfo v) => (v.type.getUsedConstantsAsSet.toArray ++ v.ctors.toArray, false)
  | none                 => (#[], false)

/-- Tarjan state for the single-pass closure computation. -/
structure S where
  time       : Nat := 0
  index      : Std.HashMap Name Nat := {}
  lowlink    : Std.HashMap Name Nat := {}
  onStack    : Std.HashSet Name := {}
  stack      : Array Name := #[]
  depCache   : Std.HashMap Name (Array Name) := {}
  isAxiom    : Std.HashSet Name := {}
  sccId      : Std.HashMap Name Nat := {}
  sccClosure : Std.HashMap Nat (Array Name) := {}
  nextScc    : Nat := 0

abbrev M := StateT S CoreM

/-- Memoized direct-deps lookup; records the axiom flag. -/
def getDeps (c : Name) : M (Array Name) := do
  let s ← get
  if let some es := s.depCache[c]? then return es
  let env ← getEnv
  let (es, ax) := constDeps env c
  modify fun s => { s with
    depCache := s.depCache.insert c es
    isAxiom := if ax then s.isAxiom.insert c else s.isAxiom }
  return es

/-- Tarjan `strongconnect`, computing each SCC's axiom closure at pop time. -/
partial def strongconnect (v : Name) : M Unit := do
  modify fun s => { s with
    index := s.index.insert v s.time
    lowlink := s.lowlink.insert v s.time
    onStack := s.onStack.insert v
    stack := s.stack.push v
    time := s.time + 1 }
  let deps ← getDeps v
  for w in deps do
    let s ← get
    if !s.index.contains w then
      strongconnect w
      modify fun s => { s with lowlink := s.lowlink.insert v (min s.lowlink[v]! s.lowlink[w]!) }
    else if s.onStack.contains w then
      modify fun s => { s with lowlink := s.lowlink.insert v (min s.lowlink[v]! s.index[w]!) }
  let s ← get
  if s.lowlink[v]! == s.index[v]! then
    -- Finalize the SCC rooted at `v`: pop members down to `v`.
    let scc := s.nextScc
    let mut members : Array Name := #[]
    let mut stk := s.stack
    let mut onStk := s.onStack
    let mut idMap := s.sccId
    let mut w := v  -- placeholder
    repeat
      w := stk.back!
      stk := stk.pop
      onStk := onStk.erase w
      idMap := idMap.insert w scc
      members := members.push w
      if w == v then break
    -- closure = members' own axioms ∪ closures of successor SCCs (already finalized).
    let mut acc : Std.HashSet Name := {}
    for m in members do
      if s.isAxiom.contains m then acc := acc.insert m
      for d in (s.depCache[m]?.getD #[]) do
        if let some dScc := idMap[d]? then
          if dScc != scc then
            for a in (s.sccClosure[dScc]?.getD #[]) do acc := acc.insert a
    modify fun s => { s with
      stack := stk, onStack := onStk, sccId := idMap
      sccClosure := s.sccClosure.insert scc acc.toArray
      nextScc := scc + 1 }

/-- **Compute the transitive axiom closure AND the immediate constant-dependency graph for each
root**, in ONE Tarjan pass over the shared constant-dependency graph. Returns
`(root ↦ sorted axiom-name array, const ↦ immediate union deps)`.

The first map is identical to `collectAxioms` (validated by the parity check). The second is
`depCache` — every visited const's immediate `type ∪ value` references — which `ExtractDeps` filters
to project-local names to emit the proof-dependency edges (`name_deps_project`) **without a second
`getUsedConstantsAsSet` walk** (ADR-005 D-G: the O(total-expr-size) traversal is already paid here). -/
def axiomClosuresWithDeps (roots : Array Name) :
    CoreM (Std.HashMap Name (Array Name) × Std.HashMap Name (Array Name)) := do
  let go : M Unit := roots.forM fun r => do
    unless (← get).index.contains r do strongconnect r
  let (_, s) ← go.run {}
  let mut res : Std.HashMap Name (Array Name) := {}
  for r in roots do
    if let some scc := s.sccId[r]? then
      let cl := (s.sccClosure[scc]?.getD #[]).qsort (·.toString < ·.toString)
      res := res.insert r cl
  return (res, s.depCache)

/-- **Transitive axiom closure for each root** — back-compat wrapper over `axiomClosuresWithDeps`
(drops the immediate-dependency map). One Tarjan pass; `root ↦ sorted axiom-name array`, identical
set to `collectAxioms` (validated by the parity check). -/
def axiomClosures (roots : Array Name) : CoreM (Std.HashMap Name (Array Name)) := do
  let (closures, _) ← axiomClosuresWithDeps roots
  return closures

end SKEFTHawking.AxiomClosure
