# Existing canonical storage mechanisms: read-only investigation

Date: 2026-11-06. Repository inspected: `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking`. Source snapshot: HEAD `25b5f229ce3f518ac08a9279f1680f2068cd4a4c` (canonical refresh), parent `4672e9fec` (Eq10 aggregate). No source, cache, Git configuration, hooks, controller, or process mutation performed. This report is the sole written artifact. Commands were source reads, rg, and read-only Git log/tree/status. No extraction, build, tests, network, or trial migration was run.

## Result

Existing machinery provides canonical generation, deterministic local serialization, source-hash freshness, synchronized derivative generation, slot build-cache transfer, and explicit assignment recovery. I found **no established canonical large-artifact transport/storage or hydration mechanism** in the inspected repository authority, code, tracked history paths, or workspace governing documents. The only LFS policy reference found concerns the *primary-source literature cache*, not `lean/lean_deps.json`. Installing LFS locally therefore does not establish an accepted declaration-registry storage mechanism.

The immediate gap is transport of a registry blob that exceeds the remote Git limit while preserving the existing invariant that ordinary local JSON is available at `lean/lean_deps.json` to all direct consumers, plus reproducible recovery of the accepted source/artifact pair. This report makes no settled storage design recommendation.

## Existing owners and mechanisms to reuse

1. **Canonical source and writer.** `docs/architecture/END_TO_END_MAP.md:54-57` identifies declaration extraction as the quantitative chokepoint for counts, atlas, graph, frontier. `docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md:272-296` is the per-artifact writer and freshness owner; specifically line 280 gives `extract_lean_deps.py` sole registry ownership and hashes all recursive project `.lean` files plus the aggregate. It does not specify a storage backend, release assets, download, compression, or LFS.

2. **Deterministic ordinary JSON, already compact.** `scripts/extract_lean_deps.py:32-59` already sorts keys and uses `separators=(",", ":")`, one record per line inside a normal JSON array. Introduction: commit `3dcbdccbf`, subject `lean_deps.json: write ONE RECORD PER LINE — kill the 25 s pre-commit diff` (verified with `git log -S 'def serialize_deps'`). Current implementation keeps Python's default ASCII escaping. Its docstring distinguishes source hash from artifact bytes (`:52-54`). A smaller serialization changes byte transport, not declaration semantics or the source hash. Existing implementation is a serialization owner to extend if a serialization policy is chosen, not grounds for a second writer.

3. **Generation and serialization lock.** `scripts/extract_lean_deps.py:98-105` considers the registry stale only if the file/hash is missing or the stored hash differs from current Lean source hash. `:108-138` serializes extraction with existing `harness_lock.regen_lock("lean_deps")`; a contending caller is warned that it uses the previous extraction. `:141-182` runs Lean, parses the output as a list, then writes through `serialize_deps()` and writes the source hash. `:193-196` can use a cached registry when Lake is unavailable, but cannot create one absent Lake. `:202-216` loads through ordinary JSON.

4. **Derivative orchestration is already registered.** `scripts/sync_manifest.py:126-142` registers extraction as the heavy upstream edge, then counts, paper tables, census, atlas and heatmap through their existing writers. `docs/WAVE_EXECUTION_PIPELINE.md:518-536` requires document sync through validation/counts/tables and forbids deleting `.hash` to force a refresh. Any transport/hydration step must preserve this graph rather than creating another routing ledger or canonical declaration producer.

5. **Full-run freshness differs from single-check readers.** `scripts/validate.py:883-900` refreshes once only for a full run; `--check` must avoid heavy extraction. `scripts/validate_helpers.py:98-111` parses the file directly without freshness guard; `:162-180` checks freshness through the existing source-hash predicate, not an artifact checksum.

6. **Assignment recovery is not artifact transport.** `docs/dev-loops/CODEX_CONTINUITY.md:5-29` provides planner reuse, assignment packets and live reconciliation. Its line 9 explicitly says a matching packet does not prove tests, lease validity, or completion. This is dispatch/recovery provenance; it is not registry backup/hydration. ROOT is separately preserving exact Git history; no bundle was duplicated here.

7. **Slot cache distribution is distinct.** `scripts/lean_slots/controller.py:458-477` transfers the primary `.lake` directory to a slot (macOS copy-on-write copy, falling back to `shutil.copytree`). `:495-536` prepares existing slot worktrees by checking authority and resetting to the selected base before replacing Lake state. No LFS fetch/hydration is present in these paths. Whether future checkout filters would hydrate successfully is unverified; slot cache transfer itself does not solve declaration artifact distribution.

## Concrete reader compatibility constraints

| Reader/path | Current contract | Consequence for storage changes (inference from code) |
|---|---|---|
| `scripts/validate_helpers.py:98-111` | `json.loads(LEAN_DEPS_PATH.read_text())` | Pointer text, compressed bytes, or manifest-only substitution is incompatible unless materialized as ordinary JSON before use. |
| `scripts/atlas_view.py:354-375` | Raises `FileNotFoundError` if missing, otherwise `json.load` | Removing the tracked registry without hydration breaks atlas consumers. |
| `scripts/export_web_atlas.py:53-62` | Missing registry yields warning + empty family edges; present file is `json.load` | Absence can degrade published graph data rather than simply block; a pointer is present but invalid JSON. |
| `scripts/provenance_dashboard.py:154-180` | Deliberately suppresses automatic Lake extraction, serves cached data | Relying on automatic regeneration to recover unavailable storage does not cover dashboard operation. |
| `scripts/extract_lean_deps.py:98-105` and `scripts/validate_helpers.py:162-180` | Existence + matching Lean-source hash is called fresh | An unhydrated LFS pointer with matching `.hash` is not detected by freshness; it reaches downstream JSON parsing. Source hash is not transport integrity. |
| Direct readers e.g. `scripts/build_graph.py:495`, `scripts/update_counts.py:656`, `scripts/validation/checks/bundles_readiness.py:1028` | Additional file-level reads, outside one universal loader | Updating only `extract_lean_deps.load_lean_deps()` would not establish universal hydration. Locations identified through rg; this is examples, not a complete consumer census. |

All claims here concern inspected source behavior. No LFS checkout, remote fetch, clone, release restore, or consumer execution was tested.

## CI / cloud / clone boundaries

- `git ls-tree -r --name-only HEAD .github` returns only `.github/dependabot.yml`. `git ls-tree` over tracked paths finds no `.gitattributes`. `git log --all -- .gitattributes .github/workflows` returns no history in the locally available refs. This is bounded local-ref evidence, not a claim about deleted unreachable commits or remote service configuration.
- `docs/architecture/VALIDATION_GATE_TOPOLOGY.md:21-29` explicitly declares no scheduled CI runner. `:130-133` says hooks are local-only/uncommitted and a fresh clone has no mechanical commit gate. Historical assessment `docs/audits/2026-08-04-qa-qi-infrastructure/CI_DEFAULTS_ASSESSMENT.md:250-265,301-304` says no per-push/nightly suite and retains `--ci` for an on-demand release/fresh-clone check, without adding a workflow.
- `scripts/validation/_config.py:73-106` implements `--ci` to skip workstation-specific mtime regenerators and notebook execution. `:108-123` enforces a measured-coverage floor because missing Lean/toolchain inputs used to look greener. `scripts/validate.py:894-900` still performs its up-front full-run source-hash refresh before CI-mode skips. CI mode is **not** a registry download, toolchain provisioning, or hydration mechanism.
- `README.md:402-420` quick start covers uv and Lake and contains no LFS installation/download instruction. This investigation found no supported cloud bootstrap describing LFS credentials, object availability, skip-smudge policy, source-archive hydration, or release-asset fallback. Those compatibility properties remain **UNKNOWN**, not implicitly supported.

## Existing LFS statement and historical scope

`docs/roadmaps/Phase6i_Roadmap.md:92` identifies a >1GB storage migration risk; `:462-464` says: primary-source cache exceeding ~1GB should switch to git-lfs, decision before bulk fetch. This applies to the literature primary-source cache (see owner `QA_QI_INFRASTRUCTURE_MAP.md:296`), not the declaration registry. Latest commit touching this roadmap in available history is `1a09e8d06` (`checkpoint 6b2 (wip)`); that does not establish implementation. Scoped text search across docs/scripts/plugin/workspace governing files found no other Git-LFS storage mechanism. History search of `.gitattributes`, `.github`, ADRs and extraction code for `filter=lfs|git-lfs|git lfs` found none.

Literature acquisition is already an additive cache/fidelity mechanism (ADR-014 and its acquisition register), but it holds papers and stubs and does not supply declaration-registry artifact transport. Publication “bundles” and submission logs throughout the repo mean grouped manuscripts/reviews, not recovery Git bundles or binary-object storage.

## Residue for the lead's canonical finding

Existing machinery covers **generate → serialize → freshness → derive → review/reconcile**, but not **store/fetch a canonical registry beyond Git's blob limit → materialize local JSON → establish transport integrity and offline/release recovery**. Any settled proposal that changes the extractor/writer or infrastructure needs the existing `architecture-change` workflow; `CLAUDE.md:93-122` and `.claude/plugins/skeft-qa/skills/architecture-change/SKILL.md` require existing-owner orientation and specification before implementation. This report performs only that bounded orientation/measurement step. It does not specify or implement a new mechanism.

The parent-supplied 105,862,394-byte rejected blob, 104,780,871-byte UTF-8 pilot, and 54,298 declaration equality were not remeasured here. They remain parent evidence, not independent findings of this report. No fresh-clone or target acceptance is claimed.
