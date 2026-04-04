-- Import the full Lean meta-programming API
import Lean
import Lean.Util.CollectAxioms
import Lean.Data.Json
import Lean.Structure
import Lean.Meta.Instances
import Lean.PrettyPrinter

-- Import ALL 60 project modules so their declarations are in the environment
import SKEFTHawking.AcousticMetric
import SKEFTHawking.ADWMechanism
import SKEFTHawking.Basic
import SKEFTHawking.BdGHamiltonian
import SKEFTHawking.CenterEquivalenceZ2
import SKEFTHawking.CGLTransform
import SKEFTHawking.ChiralityWall
import SKEFTHawking.ChiralityWallMaster
import SKEFTHawking.DrinfeldCenterBridge
import SKEFTHawking.DrinfeldDouble
import SKEFTHawking.DrinfeldDoubleAlgebra
import SKEFTHawking.DrinfeldDoubleRing
import SKEFTHawking.DrinfeldEquivalence
import SKEFTHawking.FermionBag4D
import SKEFTHawking.FractonFormulas
import SKEFTHawking.FractonGravity
import SKEFTHawking.FractonHydro
import SKEFTHawking.FractonNonAbelian
import SKEFTHawking.FusionCategory
import SKEFTHawking.FusionExamples
import SKEFTHawking.GaugeEmergence
import SKEFTHawking.GaugeErasure
import SKEFTHawking.GaugeFermionBag
import SKEFTHawking.GenerationConstraint
import SKEFTHawking.GoltermanShamir
import SKEFTHawking.GTCommutation
import SKEFTHawking.GTWeylDoublet
import SKEFTHawking.HawkingUniversality
import SKEFTHawking.HubbardStratonovichRHMC
import SKEFTHawking.KappaScaling
import SKEFTHawking.KLinearCategory
import SKEFTHawking.LatticeHamiltonian
import SKEFTHawking.MajoranaKramers
import SKEFTHawking.OnsagerAlgebra
import SKEFTHawking.OnsagerContraction
import SKEFTHawking.PauliMatrices
import SKEFTHawking.PolaritonTier1
import SKEFTHawking.QuaternionGauge
import SKEFTHawking.S3CenterAnyons
import SKEFTHawking.SecondOrderSK
import SKEFTHawking.SKDoubling
import SKEFTHawking.SMFermionData
import SKEFTHawking.SMGClassification
import SKEFTHawking.SO4Weingarten
import SKEFTHawking.SphericalCategory
import SKEFTHawking.SteenrodA1
import SKEFTHawking.SU2PseudoReality
import SKEFTHawking.ThirdOrderSK
import SKEFTHawking.ToricCodeCenter
import SKEFTHawking.TPFEvasion
import SKEFTHawking.VecG
import SKEFTHawking.VecGMonoidal
import SKEFTHawking.VestigialGravity
import SKEFTHawking.VestigialSusceptibility
import SKEFTHawking.WetterichNJL
import SKEFTHawking.WilsonMass
import SKEFTHawking.WKBAnalysis
import SKEFTHawking.WKBConnection
import SKEFTHawking.Z16AnomalyComputation
import SKEFTHawking.Z16Classification

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

/-- Check if a Name is an auxiliary/internal name (contains `._` component). -/
private def isAuxName (n : Name) : Bool :=
  n.isInternal

/-- Classify a ConstantInfo into a kind string. -/
private def classifyDecl (env : Environment) (name : Name) (ci : ConstantInfo) : String :=
  -- Check structure/class/instance before falling through to generic classification
  if isStructure env name then
    if isClass env name then "class" else "structure"
  else if Meta.instanceExtension.getState env |>.instanceNames.contains name then
    "instance"
  else
    match ci with
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

/-- Process a single declaration: extract all metadata as JSON. -/
private def processDecl (env : Environment) (name : Name) (ci : ConstantInfo)
    : MetaM Json := do
  let kind := classifyDecl env name ci
  let moduleName := getModuleName env name
  let typeStr ← ppExprStr ci.type

  -- Collect transitive axiom dependencies
  let axioms ← collectAxioms name
  let projectAxioms := axioms.filter (fun a => inSKNamespace a)
  let coreAxioms := axioms.filter (fun a => !inSKNamespace a)

  -- Extract structure fields if applicable
  let structFields ← if kind == "structure" || kind == "class" then
    extractStructureFields env name
  else
    pure #[]

  return Json.mkObj [
    ("name", Json.str (toString name)),
    ("kind", Json.str kind),
    ("module", Json.str moduleName),
    ("type", Json.str typeStr),
    ("axiom_deps_project", Json.arr (projectAxioms.map (fun a => Json.str (toString a)))),
    ("axiom_deps_core", Json.arr (coreAxioms.map (fun a => Json.str (toString a)))),
    ("structure_fields", Json.arr structFields)
  ]

/-- Check if a ConstantInfo should be skipped (constructors, recursors, quot). -/
private def shouldSkip (ci : ConstantInfo) : Bool :=
  match ci with
  | .ctorInfo _ => true
  | .recInfo _  => true
  | .quotInfo _ => true
  | _ => false

/-- Main extraction: iterate over all constants, filter, process. -/
private def extractAll (env : Environment) : MetaM (Array Json) := do
  -- Collect all SKEFTHawking declaration names from the SMap using pure fold
  let declNames : Array (Name × ConstantInfo) :=
    env.constants.fold (init := #[]) fun acc name ci =>
      if inSKNamespace name && !shouldSkip ci && !isAuxName name then
        acc.push (name, ci)
      else
        acc
  -- Sort by name for deterministic output
  let declNames := declNames.qsort (fun a b => toString a.1 < toString b.1)
  let mut results : Array Json := #[]
  for (name, ci) in declNames do
    let json ← processDecl env name ci
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
  let results ← Lean.Core.CoreM.toIO' (MetaM.run' (extractAll env)) coreCtx coreState
  -- Output JSON array
  let jsonArray := Json.arr results
  IO.println (toString jsonArray)
