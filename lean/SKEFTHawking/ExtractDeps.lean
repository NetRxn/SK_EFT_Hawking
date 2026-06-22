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
-- Memoized transitive axiom-closure + the immediate constant-dependency graph (one Tarjan pass).
-- `axiomClosuresWithDeps` returns both the per-decl axiom closure AND `depCache` (every const's
-- immediate `type ∪ value` references), so proof-dependency edges come for free — see below.
import SKEFTHawking.AxiomClosure

/-!
# ExtractDeps — Lean 4 meta-programming script for dependency extraction

Extracts all declarations from the SKEFTHawking namespace with:
- kind (axiom, theorem, def, structure, class, instance, inductive, opaque)
- type signature (pretty-printed)
- module of origin
- transitive axiom dependencies (via the memoized `AxiomClosure`), split into project vs core
- structure field names and types
- **proof-dependency edges** (`name_deps_project`): the project-local constants this declaration's
  `type ∪ value` immediately references — the who-invokes-whom DAG the proof-dependency graph /
  derived atlas frontier needs.

**ADR-005 D-G (proof-dep edges are a free byproduct).** `name_deps_project` is derived from the
immediate-dependency map (`depCache`) that the axiom-closure Tarjan pass (`AxiomClosure`) ALREADY
builds and would otherwise discard — there is NO second `getUsedConstantsAsSet` traversal, no
`EXTRACT_NAME_DEPS` opt-in, and no per-decl time budget. The O(total-expr-size) walk is paid once,
in `axiomClosuresWithDeps`, for every extraction.

Output: JSON array to stdout, consumed by `extract_lean_deps.py`.
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

/-- Check if a ConstantInfo should be skipped (constructors, recursors, quot). -/
private def shouldSkip (ci : ConstantInfo) : Bool :=
  match ci with
  | .ctorInfo _ => true
  | .recInfo _  => true
  | .quotInfo _ => true
  | _ => false

/-- Process a single declaration: extract all metadata as JSON.

`immDeps` is `AxiomClosure`'s `depCache` — every const's immediate `type ∪ value` constant
references, already computed by the axiom-closure Tarjan pass. We filter THIS decl's entry to
project-local names (and drop self-references) to emit `name_deps_project`, the proof-dependency
edges — at ZERO extra cost, with no second `getUsedConstantsAsSet` walk (ADR-005 D-G). -/
private def processDecl (env : Environment) (name : Name) (ci : ConstantInfo)
    (closures : Std.HashMap Name (Array Name)) (immDeps : Std.HashMap Name (Array Name))
    : MetaM Json := do
  let kind ← classifyDecl env name ci
  let moduleName := getModuleName env name
  let typeStr ← ppExprStr ci.type

  -- Transitive axiom dependencies via the batched memoized closure (`AxiomClosure.axiomClosuresWithDeps`,
  -- computed once in `extractAll`): set-identical to per-decl `collectAxioms` (parity-validated)
  -- but ~40× faster. Arrays are canonically sorted by the utility.
  let axioms := (closures[name]?).getD #[]
  let projectAxioms := axioms.filter (fun a => inSKPackage env a)
  let coreAxioms := axioms.filter (fun a => !inSKPackage env a)

  -- Extract structure fields if applicable
  let structFields ← if kind == "structure" || kind == "class" then
    extractStructureFields env name
  else
    pure #[]

  -- Proof-dependency edges: the project-local immediate references in this decl's `type ∪ value`,
  -- taken straight from the axiom-closure pass's `depCache` (ADR-005 D-G byproduct). Excludes
  -- self-references and non-project (Mathlib/core) names so the edge set is the project DAG.
  let nameDeps := ((immDeps[name]?).getD #[]).filter (fun n => inSKPackage env n && n != name)

  let json := Json.mkObj [
    ("name", Json.str (toString name)),
    ("kind", Json.str kind),
    ("module", Json.str moduleName),
    ("type", Json.str typeStr),
    ("axiom_deps_project", Json.arr (projectAxioms.map (fun a => Json.str (toString a)))),
    ("axiom_deps_core", Json.arr (coreAxioms.map (fun a => Json.str (toString a)))),
    ("name_deps_project", Json.arr (nameDeps.map (fun a => Json.str (toString a)))),
    -- Retained for consumer back-compat: edges are ALWAYS populated now (no opt-in, no budget),
    -- so name_deps_extracted is always true and name_deps_timed_out always false.
    ("name_deps_extracted", Json.bool true),
    ("name_deps_timed_out", Json.bool false),
    ("structure_fields", Json.arr structFields)
  ]
  return json

/-- Main extraction: iterate over all constants, filter, process.
    Filters by module membership in the SKEFTHawking package, not by namespace.
    This catches Phase-4 modules (FermionBag4D, SO4Weingarten, etc.) whose
    declarations live at root/sub-namespace but in a SKEFTHawking.* module. -/
private def extractAll (env : Environment) : MetaM (Array Json) := do
  -- Collect all declaration names from modules in the SKEFTHawking package
  let declNames : Array (Name × ConstantInfo) :=
    env.constants.fold (init := #[]) fun acc name ci =>
      if inSKPackage env name && !shouldSkip ci && !isAuxName name
          && !(`SKEFTHawking.AxiomClosure).isPrefixOf name then
        acc.push (name, ci)
      else
        acc
  -- Sort by name for deterministic output
  let declNames := declNames.qsort (fun a b => toString a.1 < toString b.1)
  -- ONE Tarjan pass over the shared constant graph yields BOTH the batched memoized axiom closures
  -- AND the immediate-dependency map (`depCache`). `name_deps_project` is derived from the latter in
  -- `processDecl` — no separate proof-term walk (ADR-005 D-G).
  let (closures, immDeps) ← SKEFTHawking.AxiomClosure.axiomClosuresWithDeps (declNames.map (·.1))
  let mut results : Array Json := #[]
  for (name, ci) in declNames do
    let json ← processDecl env name ci closures immDeps
    results := results.push json
  return results

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
  let results ← Lean.Core.CoreM.toIO'
    (MetaM.run' (extractAll env)) coreCtx coreState
  -- Output JSON array (stdout consumed by scripts/extract_lean_deps.py)
  let jsonArray := Json.arr results
  IO.println (toString jsonArray)
  -- Status on stderr (stdout is captured by the Python wrapper).
  IO.eprintln s!"[name_deps] proof-dep edges derived from the axiom-closure pass (ADR-005 D-G) — populated for {results.size} decls."
