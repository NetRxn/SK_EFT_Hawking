-- Import the full Lean meta-programming API
import Lean
import Lean.Util.CollectAxioms
import Lean.Data.Json
import Lean.Structure
import Lean.Meta.Instances
import Lean.PrettyPrinter

-- Import the root module which transitively imports ALL project modules.
-- This ensures ExtractDeps always sees every declaration without maintaining
-- a separate import list that drifts out of sync.
import SKEFTHawking

/-!
# ExtractDeps — Lean 4 meta-programming script for dependency extraction

Extracts all declarations from the SKEFTHawking namespace with:
- kind (axiom, theorem, def, structure, class, instance, inductive, opaque)
- type signature (pretty-printed)
- module of origin
- transitive axiom dependencies (via `collectAxioms`), split into project vs core
- structure field names and types

Output: JSON array to stdout, consumed by `extract_lean_deps.py` (Task 3).
-/

open Lean
open Lean.Meta

/-- The SKEFTHawking namespace prefix. -/
private def skPrefix : Name := `SKEFTHawking

/-- Check if a Name is in the SKEFTHawking namespace. -/
private def inSKNamespace (n : Name) : Bool :=
  skPrefix.isPrefixOf n

/-- Check if a Name lives in a module belonging to the SKEFTHawking package
    (i.e., the module path starts with `SKEFTHawking`). This is the architectural
    successor to `inSKNamespace`: it includes declarations defined at root namespace
    (or sub-namespaces like `FermionBag4D`) as long as they live in our package. -/
private def inSKPackage (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
    let moduleNames := env.header.moduleNames
    if h : idx.toNat < moduleNames.size then
      skPrefix.isPrefixOf moduleNames[idx.toNat]
    else false
  | none => false

/-- Check if a Name is an auxiliary/internal name (contains `._` component). -/
private def isAuxName (n : Name) : Bool :=
  n.isInternal

/-- Check if a Name's last string component starts with "inst".
    This is Lean's naming convention for auto-generated instances. -/
private def nameHasInstPrefix (n : Name) : Bool :=
  match n with
  | .str _ s => s.startsWith "inst"
  | _ => false

/-- Classify a ConstantInfo into a kind string.
    Priority: structure/class > instance > base ConstantInfo kind.
    Uses CoreM for instance check, with name heuristic fallback. -/
private def classifyDecl (env : Environment) (name : Name) (ci : ConstantInfo) : MetaM String := do
  -- Check structure/class before falling through to generic classification
  if isStructure env name then
    return if isClass env name then "class" else "structure"
  -- Check instance via extension, then fallback to name heuristic
  else if (← isInstance name) || nameHasInstPrefix name then
    return "instance"
  else
    return match ci with
    | .axiomInfo _  => "axiom"
    | .thmInfo _    => "theorem"
    | .defnInfo _   => "def"
    | .opaqueInfo _ => "opaque"
    | .inductInfo _ => "inductive"
    | .ctorInfo _   => "constructor"
    | .recInfo _    => "recursor"
    | .quotInfo _   => "quot"

/-- Get the module name for a declaration from the environment. -/
private def getModuleName (env : Environment) (name : Name) : String :=
  match env.getModuleIdxFor? name with
  | some idx =>
    let moduleNames := env.header.moduleNames
    if h : idx.toNat < moduleNames.size then
      toString moduleNames[idx.toNat]
    else
      "<unknown>"
  | none => "<current>"

/-- Pretty-print an expression to a string in MetaM.
    Falls back to a simple string representation on timeout or error. -/
private def ppExprStr (e : Expr) : MetaM String := do
  try
    let fmt ← Lean.PrettyPrinter.ppExpr e
    return toString fmt
  catch _ =>
    -- Fallback: use a basic string representation
    return s!"<expr:{e.hash}>"

/-- Extract structure field information as JSON. -/
private def extractStructureFields (env : Environment) (name : Name) : MetaM (Array Json) := do
  match getStructureInfo? env name with
  | some info =>
    let mut fields : Array Json := #[]
    for fieldName in info.fieldNames do
      let projFnName := name ++ fieldName
      let typeStr ← match env.find? projFnName with
        | some projInfo => ppExprStr projInfo.type
        | none => pure "<unknown>"
      fields := fields.push (Json.mkObj [
        ("name", Json.str (toString fieldName)),
        ("type", Json.str typeStr)
      ])
    return fields
  | none => return #[]

/-- Direct-reference extractor (Phase 5v Wave 9c, Wave 9e perf fix).

Collect the set of Names used in a declaration's *value* (proof body for a
theorem, body for a def). This is what a proof-dependency DAG actually cares
about — who does this proof invoke? — distinct from the transitive axiom
closure which is too coarse to visualize.

We restrict to project-local names (`inSKPackage`) so the graph doesn't
explode with Mathlib edges. Autogen helpers (`noConfusion`, `casesOn`,
`recOn`, etc.) are filtered out on the Python side during node extraction
so referring edges to them naturally drop.

Axioms and opaques have no value — we return an empty set for them.

**Wave 9e perf note (2026-04-24).** The fundamental cost is the
`Expr` traversal itself — every elaborated proof term in a tactic-heavy
module (RingQuot/Hopf-algebra Lean files) has hundreds of thousands of
sub-expressions, and `getUsedConstantsAsSet` must visit every one. No
per-decl budget can reduce the aggregate cost below O(total-expr-size).

Solution: gate the whole feature behind an environment variable. Default
`ExtractDeps.lean` returns to its pre-9c ~60s extraction. Setting
`EXTRACT_NAME_DEPS=1` opts into the slow path (~5–10 min) when the user
actually wants the proof-dep graph.

The dashboard:
- ALWAYS renders the baseline graph (USES edges empty / hidden);
- SHOWS a hint when the user flips the "Proof Deps" toggle without
  `name_deps_project` being populated — with the exact command to run.

Per-decl behaviour when opted in:
- folds directly over the returned set (no `.toList` materialisation);
- runs in `IO` so we can time-budget each decl with `IO.monoMsNow`.
  A decl exceeding `budgetMs` returns `(#[], true)` + logs.

Slow-decl list is written to `lean_name_deps_slow.json` for
regression-signal stability run-over-run.
-/
private def collectProjectNameDeps (env : Environment) (ci : ConstantInfo)
    (budgetMs : Nat := 250) : IO (Array Name × Bool) := do
  let val := match ci with
    | .thmInfo info    => some info.value
    | .defnInfo info   => some info.value
    | _                => none
  match val with
  | none => return (#[], false)
  | some e =>
    let t0 ← IO.monoMsNow
    -- `getUsedConstantsAsSet` returns `Std.TreeSet Name Name.quickCmp`;
    -- it handles Expr-level sharing internally via `hasMData` caching,
    -- so we can't do better than its built-in traversal.
    let used := e.getUsedConstantsAsSet
    let t1 ← IO.monoMsNow
    if t1 - t0 > budgetMs then
      return (#[], true)
    -- Iterate directly via ForIn (no `.toList` materialisation).
    let mut out : Array Name := #[]
    for n in used do
      if inSKPackage env n then
        out := out.push n
    return (out, false)

/-- Is name_deps extraction enabled? Gated by the `EXTRACT_NAME_DEPS`
environment variable (Phase 5v Wave 9e). Default: OFF so the standard
extraction stays at its pre-9c ~60s runtime. Users opt in when they
want the proof-dep graph populated. -/
private def extractNameDepsEnabled : IO Bool := do
  let val ← IO.getEnv "EXTRACT_NAME_DEPS"
  match val with
  | some s =>
    -- `trimAscii` replaces the deprecated `String.trim` in Lean 4.29
    let s := s.trimAscii.toLower
    return s == "1" || s == "true" || s == "yes" || s == "on"
  | none => return false

/-- Process a single declaration: extract all metadata as JSON.

Returns `(Json, timedOut : Bool)` — `timedOut=true` means
`collectProjectNameDeps` hit its per-decl budget. Callers use this to
accumulate a slow-decl log for regression signalling. When the
`EXTRACT_NAME_DEPS` env var is unset, name_deps extraction is skipped
entirely; output includes an empty `name_deps_project` with
`name_deps_extracted=false` so consumers can distinguish from "we
extracted and found nothing". -/
private def processDecl (env : Environment) (name : Name) (ci : ConstantInfo)
    (nameDepsEnabled : Bool)
    : MetaM (Json × Bool) := do
  let kind ← classifyDecl env name ci
  let moduleName := getModuleName env name
  let typeStr ← ppExprStr ci.type

  -- Collect transitive axiom dependencies (project = our package's modules)
  let axioms ← collectAxioms name
  let projectAxioms := axioms.filter (fun a => inSKPackage env a)
  let coreAxioms := axioms.filter (fun a => !inSKPackage env a)

  -- Extract structure fields if applicable
  let structFields ← if kind == "structure" || kind == "class" then
    extractStructureFields env name
  else
    pure #[]

  -- Direct-reference deps — only when opted in via EXTRACT_NAME_DEPS=1.
  -- Default skips to keep extraction at its pre-9c ~60s runtime; opt-in
  -- costs 5–10 min for the full proof-term walk across all decls.
  let (nameDeps, timedOut) ← if nameDepsEnabled then
    liftM (m := IO) (collectProjectNameDeps env ci)
  else
    pure (#[], false)

  let json := Json.mkObj [
    ("name", Json.str (toString name)),
    ("kind", Json.str kind),
    ("module", Json.str moduleName),
    ("type", Json.str typeStr),
    ("axiom_deps_project", Json.arr (projectAxioms.map (fun a => Json.str (toString a)))),
    ("axiom_deps_core", Json.arr (coreAxioms.map (fun a => Json.str (toString a)))),
    ("name_deps_project", Json.arr (nameDeps.map (fun a => Json.str (toString a)))),
    ("name_deps_extracted", Json.bool nameDepsEnabled),
    ("name_deps_timed_out", Json.bool timedOut),
    ("structure_fields", Json.arr structFields)
  ]
  return (json, timedOut)

/-- Check if a ConstantInfo should be skipped (constructors, recursors, quot). -/
private def shouldSkip (ci : ConstantInfo) : Bool :=
  match ci with
  | .ctorInfo _ => true
  | .recInfo _  => true
  | .quotInfo _ => true
  | _ => false

/-- Main extraction: iterate over all constants, filter, process.
    Filters by module membership in the SKEFTHawking package, not by namespace.
    This catches Phase-4 modules (FermionBag4D, SO4Weingarten, etc.) whose
    declarations live at root/sub-namespace but in a SKEFTHawking.* module.

    Returns `(results, slowDecls, nameDepsEnabled)` — slowDecls lists decls whose
    name_deps extraction exceeded the per-decl budget (only populated when
    EXTRACT_NAME_DEPS=1 was set). Logged to stderr + written to
    `lean_name_deps_slow.json` by the main entry point. -/
private def extractAll (env : Environment)
    : MetaM (Array Json × Array Name × Bool) := do
  let nameDepsEnabled ← liftM (m := IO) extractNameDepsEnabled
  -- Collect all declaration names from modules in the SKEFTHawking package
  let declNames : Array (Name × ConstantInfo) :=
    env.constants.fold (init := #[]) fun acc name ci =>
      if inSKPackage env name && !shouldSkip ci && !isAuxName name then
        acc.push (name, ci)
      else
        acc
  -- Sort by name for deterministic output
  let declNames := declNames.qsort (fun a b => toString a.1 < toString b.1)
  let mut results : Array Json := #[]
  let mut slowDecls : Array Name := #[]
  for (name, ci) in declNames do
    let (json, timedOut) ← processDecl env name ci nameDepsEnabled
    results := results.push json
    if timedOut then
      slowDecls := slowDecls.push name
  return (results, slowDecls, nameDepsEnabled)

/-- Entry point: load environment, run extraction, print JSON. -/
unsafe def main : IO Unit := do
  -- Initialize Lean search path
  Lean.initSearchPath (← Lean.findSysroot)
  -- Import all project modules
  let imports : Array Import := #[{ module := `SKEFTHawking.ExtractDeps }]
  let env ← importModules imports {} 0
  -- Set up Core/Meta context for ppExpr and collectAxioms
  -- Disable heartbeat limit (0 = unlimited) for bulk extraction
  let opts := ({} : Options).insert `maxHeartbeats (0 : Nat)
  let coreCtx : Lean.Core.Context := {
    fileName := "<ExtractDeps>"
    fileMap := { source := "", positions := #[0] }
    options := opts
    maxHeartbeats := 0  -- unlimited
  }
  let coreState : Lean.Core.State := { env := env }
  let (results, slowDecls, nameDepsEnabled) ← Lean.Core.CoreM.toIO'
    (MetaM.run' (extractAll env)) coreCtx coreState
  -- Output JSON array (stdout consumed by scripts/extract_lean_deps.py)
  let jsonArray := Json.arr results
  IO.println (toString jsonArray)
  -- Announce opt-in status on stderr (stdout is captured by the Python
  -- wrapper; stderr passes through to the user's terminal).
  if nameDepsEnabled then
    IO.eprintln s!"[name_deps] EXTRACT_NAME_DEPS=1 — name_deps_project populated for {results.size} decls."
  else
    IO.eprintln "[name_deps] EXTRACT_NAME_DEPS not set — name_deps_project left empty (~60s fast path)."
    IO.eprintln "[name_deps]   Set EXTRACT_NAME_DEPS=1 to populate proof-dep edges (~5-10 min slow path)."
  -- Side-file: slow-decls report. Written to stderr (not captured by the
  -- Python wrapper's stdout pipe) AND to a JSON side file so downstream
  -- can diff slow-decl set run-over-run for regression signal.
  if slowDecls.size > 0 then
    IO.eprintln s!"[name_deps] {slowDecls.size} decls exceeded per-decl budget (empty name_deps emitted for them):"
    for n in slowDecls.take 20 do
      IO.eprintln s!"  - {n}"
    if slowDecls.size > 20 then
      IO.eprintln s!"  ... and {slowDecls.size - 20} more (full list in lean_name_deps_slow.json)"
    let slowJson := Json.arr (slowDecls.map (fun n => Json.str (toString n)))
    IO.FS.writeFile "lean_name_deps_slow.json" (toString slowJson)
