/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# AxiomAudit — non-interactive axiom-closure gate (AI-Defect-Defense-Layer P4)

Walks every declaration in the `SKEFTHawking` namespace and, via the memoized transitive axiom closure
(`SKEFTHawking.AxiomClosure.axiomClosures` — the same machinery `ExtractDeps` uses), emits a JSON object

  `{ "<decl name>": ["<non-core axiom>", ...], ... }`

containing **only** declarations whose closure contains an axiom outside the standard kernel set
`{propext, Classical.choice, Quot.sound}`. A clean project emits `{}`.

The Python wrapper `scripts/validate.py --check axiom_closure_allowlist` compares each emitted axiom
against `{propext, Classical.choice, Quot.sound} ∪ AXIOM_METADATA.keys()` and reports any axiom outside
that allow-list. This backstops **Pipeline Invariant #15** (no undocumented project-local axioms) and
mirrors the lean4 plugin's `/check-axioms` so an interactive `/lean4:checkpoint` satisfies the same gate
at commit time. "Discipline defined once" — both consume `AxiomClosure`.

Run interpreted (native link exceeds macOS arg-length limits with Mathlib, as for `ExtractDeps`):
  `lake env lean --run SKEFTHawking/AxiomAudit.lean`

## Pipeline invariants

  * **#10** exception: this is an `IO`/environment-walking metaprogram (like `ExtractDeps`), not a proof
    body — it may use unlimited heartbeats in its local `CoreM` options.
  * **#15** (no new project-local axioms): respected (this module declares none).
-/

import Lean
import Lean.Data.Json
import SKEFTHawking
import SKEFTHawking.AxiomClosure

open Lean

/-- The standard kernel axioms, always permitted. -/
private def coreAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- Walk all `SKEFTHawking.*` declarations (excluding the `AxiomClosure`/`AxiomAudit` support modules),
compute their transitive axiom closures via the memoized `axiomClosures`, and emit a JSON object of the
declarations carrying a **non-core** axiom (empty `{}` when the project is clean). -/
unsafe def main : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← importModules
    #[{ module := `SKEFTHawking }, { module := `SKEFTHawking.AxiomClosure }] {} 0
  let names := env.constants.fold (init := #[]) fun acc n _ =>
    if (`SKEFTHawking).isPrefixOf n
        && !(`SKEFTHawking.AxiomClosure).isPrefixOf n
        && !(`SKEFTHawking.AxiomAudit).isPrefixOf n then acc.push n else acc
  let ctx : Core.Context := { fileName := "<axiom-audit>", fileMap := default, maxHeartbeats := 0 }
  let st : Core.State := { env := env }
  let act : CoreM (Array (Name × Array Name)) := do
    let closures ← SKEFTHawking.AxiomClosure.axiomClosures names
    let mut out : Array (Name × Array Name) := #[]
    for n in names do
      let cl := (closures[n]?).getD #[]
      let projAxioms := cl.filter (fun a => !(coreAxioms.contains a))
      if !projAxioms.isEmpty then
        out := out.push (n, projAxioms)
    return out
  let (out, _) ← act.toIO ctx st
  let json := Json.mkObj (out.toList.map fun (n, ax) =>
    (toString n, Json.arr (ax.map fun a => Json.str (toString a))))
  IO.println json.compress
