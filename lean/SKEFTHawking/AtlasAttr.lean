import Lean

/-!
# `@[atlas_node]` — Derived Proof Atlas landmark metadata attribute (ADR-005 D-E)

A **non-load-bearing** attribute carrying the irreducible curatorial bits the dependency graph cannot
derive, co-located on a landmark declaration:

* `track` — the atlas track / workstream the node belongs to,
* `kind`  — an OPTIONAL kind override (`"OBSTRUCTION"` / `"EDGE"`) for the cases the no-go naming
            convention cannot classify,
* `apex`  — an OPTIONAL flag marking a headline target.

Usage: `@[atlas_node track := "..." kind := "OBSTRUCTION" apex]`.

It is read by the dependency extractor (`ExtractDeps`, via `getAtlasNode?`) and emitted into the
per-decl JSON, then consumed by the atlas classifier (`atlas_view`) and the `atlas_integrity`
validation check — supplying the bits that naming/registries cannot express (ADR-005 D-E). Absent
attribute ⇒ pure derivation. It is the strippable, co-located escape hatch: non-load-bearing (no proof
obligation, no statement change), and dropped on any upstream PR.

Implementation note: the keyword atoms are NON-reserved (`&"..."`), so `track`/`kind`/`apex` remain
ordinary identifiers everywhere else. `getAtlasNode?` reads BOTH the imported and the current-module
extension state (`PersistentEnvExtension.getState` `.2`/`.1`) — `SimplePersistentEnvExtension.getState`
returns only the latter, so cross-module reads (the extractor) would otherwise see nothing.
-/

open Lean

namespace SKEFTHawking.AtlasAttr

/-- The `@[atlas_node]` payload stored per tagged declaration. -/
structure AtlasNodeData where
  /-- The atlas track / workstream. -/
  track : String
  /-- Optional kind override (`"OBSTRUCTION"` / `"EDGE"`) where naming cannot classify. -/
  kind : Option String := none
  /-- Headline-target flag. -/
  apex : Bool := false
  deriving Inhabited, Repr, BEq

/-- Persistent environment extension storing `(declName, payload)` for every `@[atlas_node]` decl
(across imports). Queried post-elaboration by the extractor; no proof obligation. -/
initialize atlasNodeExt :
    SimplePersistentEnvExtension (Name × AtlasNodeData) (Array (Name × AtlasNodeData)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s e => s.push e
    addImportedFn := fun ess => ess.foldl (· ++ ·) #[]
  }

/-- `@[atlas_node track := "..." [kind := "..."] [apex]]`. -/
syntax (name := atlasNodeAttr) "atlas_node" &"track" ":=" str (&"kind" ":=" str)? (&"apex")? : attr

initialize registerBuiltinAttribute {
  name := `atlasNodeAttr
  descr := "Derived Proof Atlas landmark metadata: track, optional kind override, optional apex flag."
  add := fun decl stx _kind => do
    match stx with
    | `(attr| atlas_node track := $t:str $[kind := $k:str]? $[apex%$ax]?) =>
        modifyEnv (atlasNodeExt.addEntry · (decl,
          ⟨t.getString, k.map (·.getString), ax.isSome⟩))
    | _ => throwError
        "invalid `atlas_node` syntax (expected: atlas_node track := \"...\" [kind := \"...\"] [apex])"
}

/-- The `@[atlas_node]` payload for declaration `n`, if tagged. Searches BOTH the imported state
(`.2`) and the current module's local entries (`.1`). -/
def getAtlasNode? (env : Environment) (n : Name) : Option AtlasNodeData :=
  let st := PersistentEnvExtension.getState atlasNodeExt env
  (st.2 ++ st.1.toArray).findSome? fun (m, d) => if m == n then some d else none

end SKEFTHawking.AtlasAttr
