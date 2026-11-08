# Canonical corpus storage proposal R1

Date: 2026-11-06. **Proposal for ROOT and independent architecture review; no selected design, operator agreement, implementation authorization, or finding closure.** Existing finding: `2026-11-07-canonical-artifact-github-size:infra:1.1`, ROOT-owned and OPEN. This document proposes delivery choices only. It changes no scientific acceptance boundary.

## Problem and bounded recommendation

The canonical declaration registry has outgrown GitHub's ordinary Git blob limit. Keep the existing extractor, declaration schema, source-hash freshness, synchronization graph, ordinary local JSON path, and reader semantics. Correct storage/delivery at that boundary rather than creating another extraction, registry, download service, or validation pipeline.

**Proposed ROOT choice P1:** treat lossless UTF-8 serialization as an optional immediate bridge, never a durable resolution. **Proposed ROOT choice P2:** qualify standard Git LFS for this exact path as the first durable candidate, conditional on preserving every required delivery mode below. Do not adopt LFS merely because it is installed. If required cloud, archive, or connector access cannot be made compatible using standard facilities, return the choice to ROOT; neither silently drop those consumers nor invent a fallback service in this increment.

The alternative of source-only regeneration already exists, but cannot currently replace delivery: the cached dashboard intentionally avoids extraction, direct readers need the artifact, and regeneration requires Lean/Lake. No existing mechanism inspected supplies transparent compressed/release-asset hydration. Thus there is no demonstrated durable, zero-bootstrap-change option among current mechanisms.

## Evidence, provenance, and scope

Continuity packet: primary `.codex/continuity/publication-canonical-storage-design-r1.json`; initial check from the assigned CUM checkout returned `fresh: true`, with no changed inputs. CUM HEAD: `70f11e549ae6f849e109f907b387058609ea6104`. Referenced primary notebook is ROOT-written; it was read, not edited. The primary scientific run remains outside this assignment. No build, extraction, slot, backend, hook/configuration change, network write, or Git mutation was run here.

Read-only measurement of the primary canonical file, independently repeated for this proposal:

| Observation | Result |
|---|---|
| Ordinary registry bytes | 105,862,394 |
| Ordinary registry SHA-256 | `3f07674e5885cb1dde3dd8d12004cd0f87f8f245402e11818abffbabee67523a` |
| Pure `ensure_ascii=False` candidate bytes | 104,780,871 |
| UTF-8 candidate SHA-256 | `a2b3c410d4cc423903d5d8b4388601cab842ac23c52f9c4d55cd3ffab6a8f029` |
| Full parsed-list equality | true, all 54,298 records; no field projection |
| GitHub rejection threshold supplied in the assignment | 104,857,600 bytes |
| UTF-8 remaining headroom | 76,729 bytes, approximately 0.073% of the limit |
| Recorded and recomputed Lean-source hash | both `a7162b223f58dbd8` |

These are a dated artifact measurement, not a projected growth rate or a ceiling for future declarations. The serializer is already compact, sorted, and one-record-per-line; minification is not an untried durable fix. The measurement changed no artifact bytes. Its Python import of the extractor may have refreshed ignored Python bytecode incidentally; ROOT was notified. Subsequent Python commands use bytecode suppression. No source mutation is claimed or intended.

The supplied preservation state is source/native checkpoint `4672e9fec` already pushed; the exact unpublished derivative `25b5f229c` is remotely preserved in the recovery bundle carried by `70f11e549`. This proposal did not fetch or restore that bundle. Its recovery availability is parent evidence, not a new independent restore result.

## Existing ownership and actual residue

Read the architecture-change skill and its ADR-012 worked example before designing. Its failure modes apply directly: an installed tool is not a delivery mechanism, matching source hashes are not hydration, and a local pilot is not clone acceptance. The bounded task covers orientation/measurement and a proposal toward specification; independent review, selection, qualification, settled ADR/spec/plan, implementation, and termination are still ahead.

| Existing owner | Existing coverage | Residue relevant here |
|---|---|---|
| `scripts/extract_lean_deps.py:32-59,98-105,108-182` | Sole deterministic JSON serializer/writer, source freshness, regeneration lock | No large-artifact transport or hydration; existence plus matching source hash accepts pointer text as fresh |
| `docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md:272-296` | Artifact writer and staleness ownership | Needs the chosen delivery/materialization contract if a choice is adopted |
| `docs/architecture/END_TO_END_MAP.md:54-57`; `scripts/sync_manifest.py:126-142` | Extraction is upstream of counts/atlas/graph/frontier and mechanical sync | Reuse this graph; do not create a second canonical producer |
| `scripts/validate.py:883-900`; `scripts/validate_helpers.py:98-111,162-180` | Full-run source freshness and direct JSON reading | `--check` is not extraction; CI mode is not provisioning/hydration; source freshness is not object integrity |
| `scripts/provenance_dashboard.py:154-180` | Cached dashboard without automatic Lake extraction | Must work with local ordinary JSON while offline and without Lake |
| `scripts/lean_slots/controller.py:458-536` | Existing slot checkout preparation and `.lake` cache transfer | Cache transfer does not deliver LFS objects or establish checkout-filter behavior |
| `docs/dev-loops/CODEX_CONTINUITY.md` and existing remediation planner | Assignment reconciliation, sole-writer finding routing/closure | Neither is storage transport or a parallel artifact registry |

Mechanical validation already measures declaration structure and freshness; reviewer agents already consume the registry for claims/backing, and adversarial review checks overclaims and production evidence. Neither layer establishes remote LFS availability. The existing investigation `CANONICAL_STORAGE_EXISTING_MECHANISMS_R1.md` found no canonical LFS attributes, hydration, or tracked workflow; gate topology explicitly says no scheduled CI. This proposal adds no check roster, monitoring cadence, registry, or second finding.

## Alternatives and their consequences

| Choice | What changes | Benefits | Compatibility/cost and decision |
|---|---|---|---|
| A. Ordinary Git plus UTF-8 bridge | Extend existing serializer to `ensure_ascii=False`, explicitly persist UTF-8, regenerate only its bytes | Full parsed equality measured; all local JSON readers and file-based access keep their interface | Only 76,729 bytes remain; another ordinary refresh can fail. Locale-dependent readers still need UTF-8 qualification. Suitable only for a bounded delivery checkpoint; finding remains open for durable storage |
| B. Standard Git LFS, exact `lean/lean_deps.json` tracking | Track the path through standard attributes/filters; arrange standard upload and hydration before consumption | Git stores the pointer; hydrated working tree remains ordinary JSON, preserving direct readers and sole extractor | New bootstrap/object-retention dependency, upload/download credentials and quota, archive setting, worktree qualification, connector/raw-path uncertainty. First durable candidate to qualify, not accepted today |
| C. Existing source regeneration, artifact omitted from ordinary Git | Reuse current extractor and source hash, with Lean/Lake available | Avoids a new storage backend | Fails current cached/offline/no-Lake and direct-reader contracts without wider changes; not a compatible delivery correction today |

Compressed tracked files, release assets, or multipart JSON could create size headroom, but no existing transparent hydration facility was found. They would require reader/bootstrap/download changes and artifact-source binding beyond standard checkout. A recovery Git bundle preserves the rejected historical object; it is not a normal clone distribution mechanism. None is a smaller demonstrated compatible correction than qualifying B. No compression ratio or hypothetical fallback service is asserted.

GitHub documents LFS as pointers in Git with file contents stored separately, with the pointer recording object SHA-256 and size. This makes the current JSON-to-pointer mismatch a real contract boundary, not an extension rename. See [GitHub LFS documentation](https://docs.github.com/en/repositories/working-with-files/managing-large-files/about-git-large-file-storage). Local LFS 3.8.0 and absence of a configured pre-push hook were supplied by ROOT; this proposal did not install or configure anything.

## Conditional LFS contract and compatibility qualification

**Proposed ROOT choice P3:** local `lean/lean_deps.json` must contain complete ordinary JSON before any existing consumer runs. Keep `lean_deps.json.hash` as the Lean-source freshness key; it must not be repurposed into an object checksum. Use standard LFS object identity/size and normal JSON parsing for transport/materialization qualification, without another canonical sidecar registry. A pointer plus a matching source hash is never acceptance evidence. Failures must remain visible; never substitute an empty declaration list or an older artifact to make a delivery appear successful.

Standard `git lfs pull` downloads current-ref objects and updates working-copy contents; it is not Lean regeneration. See [upstream pull documentation](https://github.com/git-lfs/git-lfs/blob/main/docs/man/git-lfs-pull.adoc). Exact filtering/configuration behavior must be tested at the installed version. Install configures clean/smudge filters and a pre-push hook, potentially through `core.hooksPath`; inspect existing hooks first and preserve their behavior rather than overwriting them. See [upstream installation documentation](https://github.com/git-lfs/git-lfs/blob/main/docs/man/git-lfs-install.adoc).

| Required mode | What source establishes now | Smallest bounded qualification if B is selected |
|---|---|---|
| Normal clone and checkout | No existing LFS bootstrap instructions; README covers uv/Lake only | Disposable clean clone of exact candidate with LFS installed/configured: prove ordinary JSON, pointer object SHA/size match, source-hash match, complete parsed equality, and a representative direct reader before extraction. Also exercise checkout to a second accepted artifact revision and back |
| Missing LFS, skip-smudge, fetch failure | Pointer passes current existence/source-hash predicate, then direct JSON parsing fails | Exercise these negative cases without running Lean: document standard installation/pull remedy and verify unavailable JSON cannot be called qualified. Automatic support for clients without LFS is UNKNOWN; a requirement for zero-bootstrap compatibility would disqualify B |
| Codex and Claude local sessions | Both use the checkout and ordinary file readers; session identity supplies no object fetch | Run each normal session/bootstrap path against the same hydrated candidate and a resumed checkout. Keep instructions in existing onboarding owners, not a new plugin lifecycle or session hook. Agent names alone establish no support |
| Linked checkouts and ADR-008 slots | Controller transfers Lake cache and performs checkout operations, no LFS preparation | In a disposable worktree first, test actual Git config/filter scope, shared object-store behavior, matching JSON and revision switches. Only ROOT may later use a separately admitted real slot and normal `slotctl` lifecycle; do not borrow an active slot. If a standard pre-hydration action is needed, keep it at existing preparation/bootstrap, not every reader |
| On-demand CI mode | No scheduled CI runner; `--ci` skips some workstation work but can refresh first | In an isolated environment, hydrate before validation and prove no-Lake cached reads; then ROOT runs actual required gates separately. No new workflow or CI runner is proposed. Coverage skips are not hydration acceptance |
| Cloud clones / managed workspaces | No supported cloud provisioning for LFS found | UNKNOWN. Identify actual required provider bootstrap and credential/network policy, qualify exact-ref hydration there. Do not claim a cloud product installs LFS, fetches objects, or shares workstation config |
| GitHub ZIP/tar source archives | GitHub defaults to pointers in archives | If source archives must be self-contained, ROOT must select and verify GitHub's existing include-LFS-objects archive setting, then download and parse exact-ref ZIP and tar archives without Git/Lake. This is an external repository setting, not implemented here. Without that setting or an explicitly accepted materialized release, required self-contained archive support blocks B |
| Offline and no-Lake cached operation | Existing dashboard deliberately reads cached data | Fully hydrated checkout must run cached registry readers with no network/Lake. Separately test offline restore from the chosen preserved object copy. A pointer-only clone without its object cannot satisfy offline availability |
| GitHub connector / raw readers | No connector hydration policy was inspected; Git objects under B contain pointers | UNKNOWN for each actual tool/endpoint. Read exact candidate path with the actual connector and raw access routes; test full content and completeness, not just HTTP success. If a required reader receives pointer/truncated text and cannot use a standard materialized route, B is incompatible until ROOT chooses a supported access contract; do not silently redirect it to a new service |
| Recovery | Existing exact rejected history is preserved by ROOT; no LFS recovery established | Preserve both Git refs/pointers and the corresponding object bytes. Prove restore into an empty disposable repository/object cache without network, compare pointer SHA/size, source hash, parsed data and representative readers. Do not assume a Git bundle alone holds external objects |

GitHub's archive documentation explicitly states the pointer default and the optional inclusion setting, with archive bandwidth charged to the account. Repository setting, account quota/budget, object upload entitlement and actual downloads are UNKNOWN here. See [GitHub archive documentation](https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/managing-repository-settings/managing-git-lfs-objects-in-archives-of-your-repository). The Git bundle manual describes transfer of Git objects/refs; combined with LFS's separate storage model, the need to preserve LFS content separately is an inference, not a tested restore result. See [Git bundle manual](https://git-scm.com/docs/git-bundle).

## Smallest possible changes after selection, not an implementation plan

The minimum file scope depends on the choice. ROOT should finalize it only after independent architecture review and the bounded pilot; this proposal does not create an ADR/spec/plan or assign implementation work.

For A alone: existing `scripts/extract_lean_deps.py` serializer/write encoding, canonical `lean/lean_deps.json` bytes, and tests of Unicode round-trip/encoding/determinism at the existing extractor test surface. Preserve source hash, schema and record ordering. No new extraction is necessary to prove the pure byte transformation. Existing extractor tests are marked slow; pure serializer coverage should be independently runnable without accidentally invoking Lean. Document that the bridge is temporary in the existing finding, not a new operational rule that declares the size problem solved.

For B: exact-path `.gitattributes` entry and the pointer representation of the existing `lean/lean_deps.json`; existing README quick start and applicable Codex/Claude/slot operator bootstrap instructions; existing artifact-owner architecture documentation; extraction/storage tests and any existing architecture-claim tests whose assertions change. `lean_deps.json.hash` stays unchanged for unchanged Lean source. The extractor need not change its schema or ASCII policy to use LFS. Do not combine optional UTF-8 serialization with LFS unless ROOT selects that independent policy for a stated reason.

Installation/filter/pre-push configuration and the GitHub archive inclusion setting are operational prerequisites, not files made correct by committing attributes. Qualify them through standard facilities, preserve existing hook behavior and document exact required setup. No custom uploader, manifest, universal reader rewrite, downloader, fallback daemon, periodic measurement, or extra gate is proposed. If the pilot proves existing bootstrap cannot enforce materialization before readers, return the seam to architecture review; do not hide an unimplemented prerequisite inside this minimum scope.

Prospective tests should prove the selected seam: full real-corpus value equality; deterministic serialization if touched; LFS pointer identity vs materialized JSON; missing/corrupt object and matching-source-hash pointer failure; representative direct readers and cached dashboard data loading without extraction; exact-ref checkout/archive/offline recovery. Fixtures alone cannot establish real transport. Extend existing tests rather than registering a new check by default. If review selects a new production guard, architecture-change's production-seeded mutation, registration derivation and same-commit documentation requirements apply before shipping; no such guard is authorized by this proposal.

## Publication history constraint

**Proposed ROOT choice P4:** preserve the exact rejected historical derivative and all science; publish a separately reviewed transport-correct candidate composed from the already remote source base, after ROOT reconciles the current full-run context. Merely committing smaller bytes or an LFS pointer on top of a reachable unpublished oversized blob leaves that blob in the push ancestry. Therefore qualification must inspect the entire newly reachable object closure, not only the final file. Do not rewrite published history, run broad `lfs migrate --everything`, reset the active primary, or rewrite/delete the preservation bundle as a shortcut.

The exact composition is ROOT-owned and deferred until the live scientific run is reconciled. Evidence for `25b5f229c` remains evidence for that historical scientific source/artifact pair; it must not be relabelled as evidence for a new Git commit. A byte/value equivalence review may transfer only the claims it actually establishes. Changed transport/config/bootstrap still needs its own qualification.

## Review, acceptance, and termination boundaries

ROOT's next decision is whether A is needed as a bridge and whether B merits a standard-facility pilot, with the required connector/cloud/archive routes named. These are proposed author calls, not agreed operator choices. A different architecture reviewer must challenge: duplication with existing owners, the matching-source-hash pointer defect, missing-client behavior, bootstrap coverage, archive/connector access, object retention/recovery, unpublished oversized ancestry, and drift from the requested smallest durable correction. Self-review does not settle the design.

After review and real-corpus pilot, ROOT can write the selected architecture specification before implementation and use the existing planner/finding. Qualify the exact composed candidate through remote upload/readback and fresh clone/materialization before calling the delivery repaired. Run scoped extractor/architecture/bootstrap tests appropriate to changed files; ADR-008 tests if slot machinery changes; broader fast suite and the project's actual full gates before publishing or closing. A proposal diff check cannot substitute for those gates, and this assignment runs none of the live/full scientific work.

Termination remains with ROOT through the existing closure writer and merged-wave requirements: reviewed implementation and corrected owner docs, required verification, exact remote artifact availability, independent acceptance and recorded scoped finding disposition. UTF-8 success alone is not durable storage acceptance. No scientific, source, physical, publication, or waiver closure follows from this proposal.
