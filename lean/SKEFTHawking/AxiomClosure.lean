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
  -- ADR-005 D-G.2 incremental immediate-ref cache (PROJECT roots only):
  rootSet    : Std.HashSet Name := {}                        -- consts eligible for caching (the roots)
  valCache   : Std.HashMap Name (UInt64 × Array Name) := {}  -- loaded cache: name ↦ (declHash, immediate refs)
  newCache   : Std.HashMap Name (UInt64 × Array Name) := {}  -- cache to persist after this run
  -- ADR-005 D-G.2 Mathlib boundary axiom-closure cache (NON-project LEAVES; pin-keyed). A const in
  -- this map is treated as a Tarjan leaf: its precomputed transitive axiom closure is injected at
  -- SCC-finalize time and the walk does NOT recurse into its (Mathlib) proof terms — eliminating the
  -- dominant transitive-Mathlib traversal. Stable because Mathlib is pinned (ExtractDeps tags the
  -- on-disk cache with a pin key and discards it on any toolchain/dependency bump).
  leafClosure : Std.HashMap Name (Array Name) := {}          -- name ↦ precomputed transitive axiom closure
  -- Boundary-harvest support. `isProject` distinguishes project consts (walked, may change between
  -- runs) from non-project leaves. `missedBoundary` accumulates the boundary cache-MISSES detected
  -- DURING the walk: a non-project const that is a DIRECT dep of a PROJECT node and is not already a
  -- cached leaf. Detecting it inline (gated by the leaf-check that already runs) means a warm run
  -- never classifies the bulk project→Mathlib-LEAF edges — only project→project + the few new misses
  -- — so the boundary harvest costs ~nothing on warm (vs. the O(project→all edges) post-walk scan it
  -- replaces). Post-walk the persisted cache = loaded leaves ∪ these misses' freshly-computed closures.
  isProject      : Name → Bool := fun _ => false
  missedBoundary : Std.HashSet Name := {}

abbrev M := StateT S CoreM

/-- Cheap content hash of a declaration: `mixHash` of its type-hash and value-hash (both O(1),
cached inside the `Expr`). Two runs see the same hash iff the elaborated type+value are identical,
so it changes exactly when the decl's elaboration changes (including via transitive effects). The
incremental immediate-ref cache (D-G.2) is keyed on this. -/
def declHash (env : Environment) (c : Name) : UInt64 :=
  match env.find? c with
  | some ci =>
    let vh := match ci with
      | .thmInfo v    => v.value.hash
      | .defnInfo v   => v.value.hash
      | .opaqueInfo v => v.value.hash
      | _             => 0
    mixHash ci.type.hash vh
  | none => 0

/-- Memoized direct-deps lookup; records the axiom flag. For PROJECT roots (`rootSet`) this also
consults / populates the persistent immediate-ref cache (`valCache`/`newCache`) keyed by `declHash`:
a cache hit reuses the cached refs and SKIPS the expensive `getUsedConstantsAsSet` walk (ADR-005
D-G.2). Mathlib/core consts are never cached (they recompute each run; the pinned library makes that
deterministic). -/
def getDeps (c : Name) : M (Array Name) := do
  let s ← get
  if let some es := s.depCache[c]? then return es
  let env ← getEnv
  if s.rootSet.contains c then
    let h := declHash env c
    let cachedRefs : Option (Array Name) := match s.valCache[c]? with
      | some (ch, refs) => if ch == h then some refs else none
      | none => none
    let (es, ax) := match cachedRefs with
      | some refs => (refs, (match env.find? c with | some (.axiomInfo _) => true | _ => false))
      | none      => constDeps env c
    modify fun s => { s with
      depCache := s.depCache.insert c es
      newCache := s.newCache.insert c (h, es)
      isAxiom := if ax then s.isAxiom.insert c else s.isAxiom }
    return es
  else
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
  let isPV := (← get).isProject v
  let deps ← getDeps v
  for w in deps do
    let s ← get
    if s.leafClosure.contains w then
      pure ()  -- Mathlib leaf (ADR-005 D-G.2): closure injected at finalize; no recursion / back-edge
    else
      -- Boundary cache-MISS detection (ADR-005 D-G.2): only a PROJECT node's (`isPV`) non-project dep
      -- that wasn't a cached leaf (we're past the leaf-skip). `isProject w` is therefore evaluated
      -- only on non-leaf edges — i.e. never on the bulk project→Mathlib-leaf edges on a warm run.
      if isPV && !s.isProject w then
        modify fun s => { s with missedBoundary := s.missedBoundary.insert w }
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
        if let some cl := s.leafClosure[d]? then
          -- Mathlib leaf: inject its precomputed transitive axiom closure (ADR-005 D-G.2).
          for a in cl do acc := acc.insert a
        else if let some dScc := idMap[d]? then
          if dScc != scc then
            for a in (s.sccClosure[dScc]?.getD #[]) do acc := acc.insert a
    modify fun s => { s with
      stack := stk, onStack := onStk, sccId := idMap
      sccClosure := s.sccClosure.insert scc acc.toArray
      nextScc := scc + 1 }

/-- **Cache-aware** transitive-axiom-closure + immediate-dependency pass (ADR-005 D-G.2), backed by
TWO independent, composable caches:

  * `valCache` — the persisted per-decl immediate-ref cache (`name ↦ (declHash, refs)`). A PROJECT
    root whose `declHash` still matches reuses its cached immediate refs and skips its
    `getUsedConstantsAsSet` walk.
  * `mathlibCache` — the persisted **Mathlib boundary axiom-closure** cache (`name ↦ closure`). Every
    const in it is a Tarjan **leaf**: its closure is injected directly and the walk never recurses
    into its (Mathlib) proof terms. This eliminates the dominant transitive-Mathlib traversal — the
    benched ~5 min cost — leaving only the project subgraph to walk. `isProject` (= `inSKPackage`)
    distinguishes project consts (walked, may change between runs) from non-project leaves.

Returns `(root ↦ sorted axiom-names, const ↦ immediate union deps, updated valCache to persist,
updated mathlibCache to persist)`. The fourth value = the loaded leaves carried forward ∪ this run's
boundary MISSES (non-project direct deps of a project node not already cached, detected inline during
the walk), so it stays boundary-sized — it grows by the few newly-referenced Mathlib consts each run
and is reset wholesale on a pin bump. **Both caches only change WALL-TIME, never RESULTS:** the
axiom-closure map is identical to `collectAxioms` regardless of cache state — `valCache` reuses the
same immediate refs, and a `mathlibCache` leaf's closure was computed by THIS SAME cold algorithm
under the SAME library pin (ExtractDeps pin-keys the on-disk cache and discards it on any bump). -/
def axiomClosuresWithDepsCached (roots : Array Name) (isProject : Name → Bool)
    (valCache : Std.HashMap Name (UInt64 × Array Name))
    (mathlibCache : Std.HashMap Name (Array Name)) :
    CoreM (Std.HashMap Name (Array Name) × Std.HashMap Name (Array Name)
           × Std.HashMap Name (UInt64 × Array Name)
           × Std.HashMap Name (Array Name)) := do
  let rootSet : Std.HashSet Name := roots.foldl (·.insert ·) ({} : Std.HashSet Name)
  let init : S := { rootSet := rootSet, valCache := valCache, leafClosure := mathlibCache,
                    isProject := isProject }
  let go : M Unit := roots.forM fun r => do
    unless (← get).index.contains r do strongconnect r
  let (_, s) ← go.run init
  let mut res : Std.HashMap Name (Array Name) := {}
  for r in roots do
    if let some scc := s.sccId[r]? then
      let cl := (s.sccClosure[scc]?.getD #[]).qsort (·.toString < ·.toString)
      res := res.insert r cl
  -- Persisted Mathlib leaf cache for next run = the loaded leaves carried forward ∪ this run's
  -- boundary MISSES' freshly-computed closures (a miss was strongconnected, so its SCC closure IS its
  -- transitive axiom closure). The boundary was detected inline during the walk (`missedBoundary`),
  -- so this is O(misses) — NOT a post-walk O(project→all edges) scan. Carrying loaded leaves forward
  -- (rather than recomputing the whole boundary) means the cache is not actively pruned, but it stays
  -- boundary-sized in practice: it only ever holds project→Mathlib boundary consts, grows by the few
  -- newly-referenced ones each run, and every entry's closure is pin-stable so a stale (no-longer-
  -- referenced) leaf is harmless. A pin bump discards the whole file (ExtractDeps), resetting it.
  let mut newMathlib : Std.HashMap Name (Array Name) := mathlibCache
  for d in s.missedBoundary do
    let cl := match s.sccId[d]? with
      | some dScc => s.sccClosure[dScc]?.getD #[]
      | none      => #[]
    newMathlib := newMathlib.insert d cl
  return (res, s.depCache, s.newCache, newMathlib)

/-- **Compute the transitive axiom closure AND the immediate constant-dependency graph for each
root**, in ONE Tarjan pass. Delegates to `axiomClosuresWithDepsCached` with EMPTY caches (no reuse,
no persistence) — a fully cold walk (every Mathlib const recursed, none treated as a leaf), so the
closures are ground-truth identical to `collectAxioms`. Returns `(root ↦ sorted axiom-name array,
const ↦ immediate union deps)`; the second map is `depCache`, which `ExtractDeps` filters to
project-local names to emit `name_deps_project` without a second `getUsedConstantsAsSet` walk
(ADR-005 D-G). -/
def axiomClosuresWithDeps (roots : Array Name) :
    CoreM (Std.HashMap Name (Array Name) × Std.HashMap Name (Array Name)) := do
  let (closures, depCache, _, _) ← axiomClosuresWithDepsCached roots (fun _ => true) {} {}
  return (closures, depCache)

/-- **Transitive axiom closure for each root** — back-compat wrapper (drops the immediate-dependency
map). `root ↦ sorted axiom-name array`, identical set to `collectAxioms` (validated by the parity
check). -/
def axiomClosures (roots : Array Name) : CoreM (Std.HashMap Name (Array Name)) := do
  let (closures, _) ← axiomClosuresWithDeps roots
  return closures

end SKEFTHawking.AxiomClosure
