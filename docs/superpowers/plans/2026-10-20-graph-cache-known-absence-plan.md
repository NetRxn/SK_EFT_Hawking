# Plan: repair known absence in the existing graph cache

Status: the bounded implementation, runtime/production controls and declared-Verify infrastructure closure have independent whole review. Complete default qualification still fails; the remaining whole-delivery and protected-main requirements below stay active. Governing design: [known absence and unavailable I/O](../specs/2026-10-20-graph-cache-known-absence-design.md), decisions D1–D4.

## Global constraints

- Preserve the whole original `tests/test_dashboard_graph_cache.py` module, real recorded graph fixture, same-object positive control, review/ledger/ancestor controls and once-through real served-node seam. Extend it in place.
- Preserve actual attempted-read data population, imported repository source population and every current ancestor rule. No hand-list, new cache, new gate/framework/ADR, `__pycache__` skip or directory-creation/bytecode workaround.
- Only reported errno.ENOENT is stable known absence. Every other stat/list OSError remains fresh/nonmatching, including unknown→known-absent. File missing remains distinct from empty file; directory missing remains distinct from successful empty listing.
- Preserve first/empty/unrecordable/raced-read fail-safe, existing cache locks/identity/PG behavior and original invalidation call sites. Do not claim atomic filesystem snapshots, content hashing or broader symlink/race coverage.
- Keep the existing planner, architecture owners and canonical finding/closure writers. This repair does not discharge any scientific construction or publication obligation, alter a floor/ceiling/timeout/oracle, or waive a failed gate.
- Work on the exact current candidate; reconcile overlapping D11 dashboard and portability branches by their accepted source hunks and existing file-conflict ownership. Do not reset or replace whole modules or change others' work.

## Phase 1: independent whole design and intent review

1. Give a fresh genuinely nonauthor reviewer both complete documents, the complete original cache test module, actual owner functions/consumers, historical cache finding and Git changes `d82f237b`/`2f5ede79`, actual Q failure payloads, source-backed pilot and original human-intent provenance.
2. Require explicit analysis of both error branches and both transition tables. Ask whether unknown file stat errors can ever alias known absence, whether directory absence can alias empty success, and whether dynamic input/ancestor/consumer coverage is preserved. Review the actual constructor for errno2 and synthetic exception boundary without expanding scope from message text.
3. Separately assess literal intent: this is lead-inferred necessary machinery repair, not a human request for a new cache design. The human's relayed Git/base/history/substantive-review requirements and governing roadmap remain full strength. State the transcript provenance limit; do not assert the author saw the original transcript.
4. Resolve every design finding with a coherent correction and new independent whole assessment. Only after genuine acceptance may ROOT grant the bounded source assignment. Before implementation, a design-author assignment writes only these design documents.

## Phase 2: coherent implementation in the existing owner

One author owns the source/tests/architecture unit below. Do not split error branches or tests from their consumer. No implementation is performed by this plan.

| File | Responsibility | Conservation requirement |
|---|---|---|
| `scripts/provenance_dashboard.py` | D1/D2: narrow existing file absence handling to ENOENT; make other stat errors fresh/nonmatching; add stable distinct ENOENT directory entry while retaining other listing errors fresh/nonmatching; precise warning/docstring/comments | Keep signature, successful metadata/listing shapes, existing file-missing sentinel, read-set/ancestor/code helpers, cache consumers, locks, invalidation and async PG path. A standard `errno` import is the only new dependency needed. |
| `tests/test_dashboard_graph_cache.py` | D3/D4: extend actual owner's error/transition/identity controls | Every original test/fixture/assertion remains; meaningful new cases must fail under the corresponding actual old-source branch. Keep real new-finding served-graph seam. |
| `docs/architecture/DASHBOARD.md` | Describe graph cache derivation and precise absence/unavailable semantics, relevant consumer behavior and actual limits before source shipping | Add/update the existing owner; no duplicate incident history, roster counts, private paths or premature acceptance claims. Correct every statement this repair makes wrong in the implementation commit. |
| this spec and plan | Record accepted specification and exact task/verification boundary | Keep design-before-code ordering; revise current status only with actual evidence and independent acceptance. |

Both file and directory legs implement the same error distinction: only reported ENOENT has a stable known-absence entry; every other error remains fresh/nonmatching. Preserve the existing file absence tuple for real ENOENT and the directory absence token distinct from successful sorted name tuples. A directory-only repair does not satisfy this unit. No serialized fingerprint schema/version or external API is introduced.

## Phase 3: meaningful controls in the current test module

Write the property each assertion establishes before implementing it; compare the immediate pre-mutation baseline, never the already-moved module fixture snapshot.

| Control | Decider and expected failure of old source |
|---|---|
| Original unchanged real warmed graph | Consecutive actual `_graph_fingerprint()` equal; two `get_cached_graph(sync_pg=False)` calls return the identical object. Bytecode-disabled real missing directory remains in captured ancestry. Old directory branch fails the original positive cases. |
| Known-absent directory stability | Path-specific real missing directory watched by actual owner yields stable distinct absence entry; never prune it from dirs. |
| Missing→empty directory→nonempty→empty→missing→recreated | Real temporary filesystem transitions each have an immediate baseline; key changes across each observed state. Missing must differ from legal empty listing. |
| Missing→empty file→nonempty→missing→recreated | Actual file stat path yields stable absence, distinguishable size0; observed presence/metadata/absence transitions change key. |
| Same-size file, changed mtime_ns | Actual key changes. Document same-size and exactly unchanged mtime as a limit rather than claiming content hashing. |
| Unknown directory states | Path-specific injected EACCES/EPERM/ENFILE/EMFILE/EIO/ENOTDIR/ELOOP and opaque OSError: each repeated and unknown→present/missing comparison cannot match. Injection labels remain distinct from native faults. |
| Unknown file states | Same injected errno/opaque matrix at stat boundary: repeated unknown and unknown→ENOENT cannot match. Old broad file except branch fails these controls. |
| Exception classification | Canonical FileNotFoundError with errno2 is stable; synthetic no-errno/contradictory FileNotFoundError remains unknown. Do not inspect message text or a suppressing exists() probe. |
| Dangling target lookup / intermediate file | Actual dangling-link ENOENT follows defined lookup semantics; direct watched target creation changes state. ENOTDIR from intermediate file remains unknown. Do not claim universal alias/retarget coverage. |
| Empty/unavailable/capture failure/existing detected race | Existing never-matching sentinel remains; add targeted checks of actual recorder error cleanup and current mtime poison if not already exercised. Do not replace the real graph with a fake all-green builder. |
| Data/code/ancestor conservation | Original review/ledger/corpus-root assertions remain, add actual loaded graph-builder source check if missing; nested ancestor population follows current helper. |
| Actual served finding and restoration | Keep original `test_a_newly_filed_finding_reaches_the_dashboard_graph`, actual production seeded finding, new node in graph served and absent after restore. No fingerprint-only substitute. |

Use temporary filesystem data for cheap state transitions and carefully scoped syscall injection for hard-to-reproduce errors, passing through unrelated paths. Restore injected boundaries through the test framework. All production seeds use `scripts/seed_journal.py` and appropriate markers; no bare finally-only restoration. The module's original production touches must run only in ROOT's authorized qualification context, not in this design assignment.

## Phase 4: ROOT production-source regression and qualification

ROOT performs this phase after the complete implementation is independently source-reviewed and the actual candidate is bound. The design author does not execute it.

1. Establish corrected baseline with original cache tests plus new semantic controls under the original bytecode-disabled environment and PG sync off. Preserve full argv/cwd/env/raw stdout/stderr/JUnit and exact source hash. A positive baseline is mandatory; unrelated red baseline is not a passed mutation.
2. Through existing `seed_journal`, reintroduce the actual old directory OSError branch into `scripts/provenance_dashboard.py`, run the unchanged real stable-key/same-object deciders, observe rc1, restore exact production source, rerun rc0. Keep the missing directory genuinely missing. No directory creation, fixture replacement or filtered-out original assertion.
3. Separately reintroduce the actual old broad file OSError→missing branch in the production script, run unchanged new real-owner file-error deciders, observe rc1, restore and rerun rc0. The syscall error injection is still a semantic fixture; the poisoned artifact is the actual script read by those deciders. Do not report a native ENFILE experiment.
4. Retain green0/red1/green0 receipts separately for each poison. Require exact original bytes/full mode/nsmtime of every mutated production input and empty final journal. Check unowned source/index/HEAD and generated artifact deltas explicitly. No reset/clean or silent residue deletion.
5. Run the entire containing cache module, original graph/dashboard related tests and the unchanged default repo-plus-plugin profile. The default command remains `uv run python -m pytest -q` with both configured testpaths; no new marker/filter/skip. Prior Q40 and earlier K40 remain their original dated receipts, not a blanket attribution or expected new failure count.
6. Use current existing `verify_scope.py` for changed-source qualification, then ROOT's complete current delivery/merge gate, including full marker mode, CI coverage and checks CI skips, canonical generation as needed and dashboard template/real browser requirements. [Topology](../../architecture/VALIDATION_GATE_TOPOLOGY.md) distinguishes scoped evidence from tree certification. No narrow pass may be called full CI, native activation, main or publication acceptance.

## Phase 5: registration, whole review, canonical closure and delivery

This change does not add or rename a validation check, gate, graph node/edge, writer, CLI, route, template or plugin component. The registration helper accepts registered **check names**, so `_graph_fingerprint` must not be invented as a new check just to make a checklist green. ROOT should probe actual applicable existing owners with `registration_sites.py <existing_check_name> --repo <candidate>` and retain its output/conditional applicability; report unchanged preexisting debt rather than manufacturing registrations or changing floors. Confirm actual existing `verify_scope` mapping of scripts/tests/architecture and existing testpaths. If implementation unexpectedly introduces a new registration surface, return to design rather than silently expanding it.

A genuinely nonauthor whole review reads source, original and new tests, full production-control evidence, complete qualifications, source conservation and the updated DASHBOARD contract. It assesses the original failure and file-leg counterexamples, no new false greens, and literal intent against both complete documents. Design review is not implementation review; author reports do not certify themselves.

Route any required new finding through the existing planner/finding convention and supported Verify, then existing `close_finding.py` after whole review/current gates. Reconcile existing related cache lineage rather than inventing a closure ID. Preserve the already fixed Q machinery findings and original open scientific duties. ROOT owns ordinary Git checkpoints, exact reviewable diff/inverse, protected-main merge and the existing wave close-out; no force/reset, no source-only delivery claim. Completion requires actual canonical closure/current gates and merged delivery under the existing process. Publication acceptance remains a separate boundary.
