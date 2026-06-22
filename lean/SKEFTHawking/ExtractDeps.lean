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
private def buildDeclJsonStr (env : Environment) (name : Name) (immDeps : Std.HashMap Name (Array Name))
    (typeStr : String) (kind : String) (moduleName : String) (axioms : Array Name)
    : MetaM String := do
  -- `kind`, `moduleName`, and `axioms` are precomputed by the caller (they also form the JSON cache
  -- key, ADR-005 D-G.2 Phase 1c). This runs ONLY on a JSON-cache miss; the dominant cost is the
  -- `Json.mkObj` build + ~10 `toString`-of-`Name` per decl, which the cache skips on a hit.
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
  -- Return the COMPACT (`Json.compress`) rendering — canonical, deterministic, ~25 % smaller than the
  -- pretty form, and version-stable (no Format line-width layout to drift). The loop caches it verbatim
  -- and `main` streams the array as `[s₀,s₁,…]`; the result is well-formed compact JSON parsed
  -- identically by every downstream `json.load` consumer (ADR-005 D-G.2 Phase 1c).
  return Json.compress json

/-- Persistent immediate-ref cache file (ADR-005 D-G.2), relative to the `lean/` cwd. Gitignored. -/
private def immRefCachePath : System.FilePath := ".lean_immref_cache.json"

/-- Load the incremental immediate-ref cache (`name ↦ (declHash, immediate refs)`). Fail-soft: a
missing/corrupt cache yields an empty map → a full cold walk (still correct). -/
private def loadImmRefCache : IO (Std.HashMap Name (UInt64 × Array Name)) := do
  if !(← immRefCachePath.pathExists) then return {}
  try
    let content ← IO.FS.readFile immRefCachePath
    match Json.parse content with
    | .error _ => return {}
    | .ok j =>
      match j.getArr? with
      | .error _ => return {}
      | .ok arr =>
        let mut m : Std.HashMap Name (UInt64 × Array Name) := {}
        for entry in arr do
          match entry.getArr? with
          | .ok #[jn, jh, jr] =>
            match jn.getStr?, jh.getStr?, jr.getArr? with
            | .ok ns, .ok hs, .ok refsJ =>
              let refs := refsJ.filterMap (fun x => (x.getStr?.toOption).map String.toName)
              m := m.insert ns.toName ((hs.toNat?.getD 0).toUInt64, refs)
            | _, _, _ => pure ()
          | _ => pure ()
        return m
  catch _ => return {}

/-- Persist the updated immediate-ref cache (one JSON array of `[name, declHash, [refs…]]`). -/
private def saveImmRefCache (cache : Std.HashMap Name (UInt64 × Array Name)) : IO Unit := do
  let arr : Array Json := cache.toArray.map (fun (n, (h, refs)) =>
    Json.arr #[Json.str n.toString, Json.str (toString h),
               Json.arr (refs.map (fun r => Json.str r.toString))])
  IO.FS.writeFile immRefCachePath (toString (Json.arr arr))

/-- Persistent **Mathlib boundary axiom-closure** cache (ADR-005 D-G.2), relative to `lean/` cwd.
Gitignored. Stores the transitive axiom closures of the project→Mathlib boundary consts so the
extraction Tarjan treats them as leaves (no recursion into Mathlib proof terms — the dominant cost).
Tagged with a pin key; discarded wholesale on any toolchain/dependency bump. -/
private def mathlibCachePath : System.FilePath := ".lean_mathlib_closure_cache.json"

/-- Pin key: a content hash of `lake-manifest.json` (the resolved dep revs — Mathlib, Physlib, …) +
`lean-toolchain` + **this extractor's own source** (`SKEFTHawking/ExtractDeps.lean`). All three
pin-keyed caches (Mathlib leaf, `typeStr`, per-decl JSON) are tagged with this key and discarded
wholesale when it changes (fail-safe: a stale/missing key ⇒ a cold rebuild, never a wrong value).

**Folding the extractor source into the pin is the drift-proofing for the JSON cache** (ADR-005
D-G.2 Phase 1c): a cached per-decl JSON string is only valid for the rendering logic that produced
it, so ANY edit to `ExtractDeps.lean` (new field, changed `ppExpr`/partition/`inSKPackage` logic, …)
must invalidate the whole cache — and does, automatically, with no hand-maintained key to forget. It
also hardens the Mathlib/`typeStr` caches against the same class of logic drift. -/
private def computePinKey : IO String := do
  let readIf (p : System.FilePath) : IO String := do
    if ← p.pathExists then IO.FS.readFile p else pure ""
  let manifest ← readIf "lake-manifest.json"
  let toolchain ← readIf "lean-toolchain"
  let extractorSrc ← readIf "SKEFTHawking/ExtractDeps.lean"
  return toString (mixHash (mixHash manifest.hash toolchain.hash) extractorSrc.hash)

/-- Load the Mathlib boundary closure cache IFF its stored pin key matches `pin`; otherwise
(missing/corrupt/stale-pin) return empty → a full cold walk that repopulates it. Fail-soft. -/
private def loadMathlibCache (pin : String) : IO (Std.HashMap Name (Array Name)) := do
  if !(← mathlibCachePath.pathExists) then return {}
  try
    let content ← IO.FS.readFile mathlibCachePath
    match Json.parse content with
    | .error _ => return {}
    | .ok j =>
      match j.getObjVal? "pin" with
      | .ok (.str p) => if p != pin then return {}
      | _ => return {}
      match j.getObjVal? "closures" with
      | .error _ => return {}
      | .ok cj =>
        match cj.getArr? with
        | .error _ => return {}
        | .ok arr =>
          let mut m : Std.HashMap Name (Array Name) := {}
          for entry in arr do
            match entry.getArr? with
            | .ok #[jn, jax] =>
              match jn.getStr?, jax.getArr? with
              | .ok ns, .ok axJ =>
                let axs := axJ.filterMap (fun x => (x.getStr?.toOption).map String.toName)
                m := m.insert ns.toName axs
              | _, _ => pure ()
            | _ => pure ()
          return m
  catch _ => return {}

/-- Persist the Mathlib boundary closure cache, tagged with the current pin key. One JSON object
`{"pin": "...", "closures": [[name, [axiom-names…]], …]}`. -/
private def saveMathlibCache (pin : String) (cache : Std.HashMap Name (Array Name)) : IO Unit := do
  let arr : Array Json := cache.toArray.map (fun (n, axs) =>
    Json.arr #[Json.str n.toString, Json.arr (axs.map (fun a => Json.str a.toString))])
  let j := Json.mkObj [("pin", Json.str pin), ("closures", Json.arr arr)]
  IO.FS.writeFile mathlibCachePath (toString j)

/-- Persistent pretty-printed-type cache (ADR-005 D-G.2), relative to `lean/` cwd. Gitignored.
`ppExpr` of ~23k type signatures is a CO-DOMINANT extraction cost (~150 s, benched) recomputed every
run; this caches `name ↦ (declHash, typeStr)` so an unchanged decl reuses its rendered type. Gated by
BOTH the per-decl `declHash` (catches a changed type) AND the library pin (catches a delaborator /
notation change that would re-render the SAME type `Expr` differently). -/
private def typeStrCachePath : System.FilePath := ".lean_typestr_cache.json"

/-- Load the type-string cache IFF its stored pin matches `pin`; else (missing/corrupt/stale) empty
→ a cold ppExpr of every type that repopulates it. Fail-soft. -/
private def loadTypeStrCache (pin : String) : IO (Std.HashMap Name (UInt64 × String)) := do
  if !(← typeStrCachePath.pathExists) then return {}
  try
    let content ← IO.FS.readFile typeStrCachePath
    match Json.parse content with
    | .error _ => return {}
    | .ok j =>
      match j.getObjVal? "pin" with
      | .ok (.str p) => if p != pin then return {}
      | _ => return {}
      match j.getObjVal? "types" with
      | .error _ => return {}
      | .ok tj =>
        match tj.getArr? with
        | .error _ => return {}
        | .ok arr =>
          let mut m : Std.HashMap Name (UInt64 × String) := {}
          for entry in arr do
            match entry.getArr? with
            | .ok #[jn, jh, jt] =>
              match jn.getStr?, jh.getStr?, jt.getStr? with
              | .ok ns, .ok hs, .ok ts => m := m.insert ns.toName ((hs.toNat?.getD 0).toUInt64, ts)
              | _, _, _ => pure ()
            | _ => pure ()
          return m
  catch _ => return {}

/-- Persist the type-string cache, tagged with the current pin. JSON object
`{"pin": "...", "types": [[name, declHash, typeStr], …]}`. -/
private def saveTypeStrCache (pin : String) (cache : Std.HashMap Name (UInt64 × String)) : IO Unit := do
  let arr : Array Json := cache.toArray.map (fun (n, (h, ts)) =>
    Json.arr #[Json.str n.toString, Json.str (toString h), Json.str ts])
  let j := Json.mkObj [("pin", Json.str pin), ("types", Json.arr arr)]
  IO.FS.writeFile typeStrCachePath (toString j)

/-- Persistent **per-decl rendered-JSON** cache (ADR-005 D-G.2 Phase 1c), relative to `lean/` cwd.
Gitignored. The JSON build (`Json.mkObj` + ~244k `toString`-of-`Name`) is the dominant warm cost
(~124 s benched); this caches `name ↦ (key, jsonString)` so an unchanged decl reuses its compressed
JSON verbatim, skipping the entire build. **Drift-proofing:** the per-decl `key` covers every
per-decl input (`declHash`, `kind`, `module`, `hash(axiom closure)`); the rendering LOGIC is covered
by the pin (which hashes this file's source) — so any change to a decl OR to how JSON is rendered
invalidates the relevant entries automatically. Correctness is the standing cold↔warm byte-identity
gate. -/
private def jsonCachePath : System.FilePath := ".lean_json_cache.json"

/-- Per-decl JSON-cache key: `mixHash` over the per-decl inputs that determine the rendered string —
`declHash` (type+value ⇒ also fixes `typeStr` and `name_deps`), `kind` (catches an `@[instance]`/
structure status flip that leaves `declHash` unchanged), `module` (catches a file move), and a hash
of the decl's transitive axiom closure (the only NON-`declHash`-stable input — `axiom_deps`). The
rendering logic itself is pinned separately (the pin hashes `ExtractDeps.lean`). -/
private def jsonCacheKey (declH : UInt64) (kind : String) (moduleName : String)
    (axioms : Array Name) : UInt64 :=
  let axH := axioms.foldl (fun h a => mixHash h (hash a)) (5381 : UInt64)
  mixHash (mixHash declH kind.hash) (mixHash moduleName.hash axH)

/-- Load the per-decl JSON cache IFF its stored pin matches `pin`; else empty → a cold rebuild that
repopulates it. Fail-soft. -/
private def loadJsonCache (pin : String) : IO (Std.HashMap Name (UInt64 × String)) := do
  if !(← jsonCachePath.pathExists) then return {}
  try
    let content ← IO.FS.readFile jsonCachePath
    match Json.parse content with
    | .error _ => return {}
    | .ok j =>
      match j.getObjVal? "pin" with
      | .ok (.str p) => if p != pin then return {}
      | _ => return {}
      match j.getObjVal? "decls" with
      | .error _ => return {}
      | .ok dj =>
        match dj.getArr? with
        | .error _ => return {}
        | .ok arr =>
          let mut m : Std.HashMap Name (UInt64 × String) := {}
          for entry in arr do
            match entry.getArr? with
            | .ok #[jn, jk, js] =>
              match jn.getStr?, jk.getStr?, js.getStr? with
              | .ok ns, .ok ks, .ok ss => m := m.insert ns.toName ((ks.toNat?.getD 0).toUInt64, ss)
              | _, _, _ => pure ()
            | _ => pure ()
          return m
  catch _ => return {}

/-- Persist the per-decl JSON cache, tagged with the current pin. JSON object
`{"pin": "...", "decls": [[name, key, jsonString], …]}`. -/
private def saveJsonCache (pin : String) (cache : Std.HashMap Name (UInt64 × String)) : IO Unit := do
  let arr : Array Json := cache.toArray.map (fun (n, (k, s)) =>
    Json.arr #[Json.str n.toString, Json.str (toString k), Json.str s])
  let j := Json.mkObj [("pin", Json.str pin), ("decls", Json.arr arr)]
  IO.FS.writeFile jsonCachePath (toString j)

/-- Main extraction: iterate over all constants, filter, process.
    Filters by module membership in the SKEFTHawking package, not by namespace.
    This catches Phase-4 modules (FermionBag4D, SO4Weingarten, etc.) whose
    declarations live at root/sub-namespace but in a SKEFTHawking.* module. -/
private def extractAll (env : Environment) (valCache : Std.HashMap Name (UInt64 × Array Name))
    (mathlibCache : Std.HashMap Name (Array Name))
    (typeCache : Std.HashMap Name (UInt64 × String))
    (jsonCache : Std.HashMap Name (UInt64 × String))
    : MetaM (Array String × Std.HashMap Name (UInt64 × Array Name)
             × Std.HashMap Name (Array Name)
             × Std.HashMap Name (UInt64 × String)
             × Std.HashMap Name (UInt64 × String)) := do
  -- Collect all declaration names from modules in the SKEFTHawking package
  let declNames : Array (Name × ConstantInfo) :=
    env.constants.fold (init := #[]) fun acc name ci =>
      if inSKPackage env name && !shouldSkip ci && !isAuxName name
          && !(`SKEFTHawking.AxiomClosure).isPrefixOf name then
        acc.push (name, ci)
      else
        acc
  -- Sort by name for deterministic output. Precompute each decl's `toString` key ONCE (not O(n log n)
  -- times inside the comparator — the comparator-side `toString` was a measurable slice of env-scan).
  let declNames := ((declNames.map (fun p => (toString p.1, p))).qsort (fun a b => a.1 < b.1)).map (·.2)
  -- ONE Tarjan pass yields the batched axiom closures + the immediate-dependency map (`depCache`)
  -- + the updated incremental immref cache (`newCache`) + the updated Mathlib boundary leaf cache
  -- (`newMathlib`), all ADR-005 D-G.2. `name_deps_project` derives from `depCache` in `processDecl`
  -- — no separate proof-term walk (ADR-005 D-G). Mathlib consts in `mathlibCache` are walk leaves.
  let (closures, immDeps, newCache, newMathlib) ←
    SKEFTHawking.AxiomClosure.axiomClosuresWithDepsCached (declNames.map (·.1))
      (fun n => inSKPackage env n) valCache mathlibCache
  let mut results : Array String := #[]
  let mut newTypeCache : Std.HashMap Name (UInt64 × String) := {}
  let mut newJsonCache : Std.HashMap Name (UInt64 × String) := {}
  for (name, ci) in declNames do
    -- Reuse the rendered type for an unchanged decl (declHash hit, ADR-005 D-G.2); ppExpr only on a
    -- miss. `declHash` is shared with AxiomClosure so the type/immref/closure caches age in lockstep.
    let h := SKEFTHawking.AxiomClosure.declHash env name
    let typeStr ← match typeCache[name]? with
      | some (ch, ts) => if ch == h then pure ts else ppExprStr ci.type
      | none          => ppExprStr ci.type
    newTypeCache := newTypeCache.insert name (h, typeStr)
    -- Phase 1c per-decl JSON cache: the key covers every per-decl JSON input (`kind`/`module` computed
    -- cheaply here; `axioms` from the closure pass; `declHash` fixes type+name_deps). The render LOGIC
    -- is pinned via the extractor source-hash. On a hit, reuse the verbatim compressed string and SKIP
    -- the whole `buildDeclJsonStr` build (the ~124 s warm hot spot).
    let kind ← classifyDecl env name ci
    let moduleName := getModuleName env name
    let axioms := (closures[name]?).getD #[]
    let key := jsonCacheKey h kind moduleName axioms
    let jstr ← match jsonCache[name]? with
      | some (k, s) => if k == key then pure s
                       else buildDeclJsonStr env name immDeps typeStr kind moduleName axioms
      | none        => buildDeclJsonStr env name immDeps typeStr kind moduleName axioms
    newJsonCache := newJsonCache.insert name (key, jstr)
    results := results.push jstr
  return (results, newCache, newMathlib, newTypeCache, newJsonCache)

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
  -- Load the four ADR-005 D-G.2 caches (per-decl immref + pin-keyed Mathlib leaf + pin-keyed
  -- type-string + pin-keyed per-decl JSON); run; persist all four.
  let pin ← computePinKey
  let valCache ← loadImmRefCache
  let mathlibCache ← loadMathlibCache pin
  let typeCache ← loadTypeStrCache pin
  let jsonCache ← loadJsonCache pin
  let (results, newCache, newMathlib, newTypeCache, newJsonCache) ← Lean.Core.CoreM.toIO'
    (MetaM.run' (extractAll env valCache mathlibCache typeCache jsonCache)) coreCtx coreState
  saveImmRefCache newCache
  saveMathlibCache pin newMathlib
  saveTypeStrCache pin newTypeCache
  saveJsonCache pin newJsonCache
  -- Stream the JSON array to stdout as `[s₀,s₁,…]` from the per-decl COMPACT strings (consumed by
  -- scripts/extract_lean_deps.py). Streaming avoids an O(n²) multi-MB string rebuild and lets the
  -- Phase-1c JSON cache feed verbatim strings straight through. NOTE: this emits COMPACT JSON, vs the
  -- pre-1c pretty-printed `toString (Json.arr …)` — same data, parsed identically by every
  -- `json.load` consumer, ~25 % smaller; the one-time reformat is expected on the 1c regen.
  let out ← IO.getStdout
  out.putStr "["
  let mut first := true
  for s in results do
    if first then first := false else out.putStr ","
    out.putStr s
  out.putStr "]\n"
  -- Status on stderr (stdout is captured by the Python wrapper).
  IO.eprintln s!"[name_deps] proof-dep edges from the axiom-closure pass (ADR-005 D-G) — {results.size} decls; immref cache {valCache.size}->{newCache.size}; mathlib leaf cache {mathlibCache.size}->{newMathlib.size}; typestr cache {typeCache.size}->{newTypeCache.size}; json cache {jsonCache.size}->{newJsonCache.size} (D-G.2)."
