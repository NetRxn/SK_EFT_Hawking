# Graph cache: known absence and unavailable I/O

Status: the D1–D4 implementation, bounded runtime and production controls, and declared-Verify infrastructure closure have independent whole review. Complete default qualification still fails; full marker, merge, CI, browser, protected-main and publication acceptance remain pending. The original scientific BUILD obligations are unchanged.

## Purpose and authority

Repair the existing dashboard graph fingerprint so that a confirmed missing input can remain stable, while unavailable I/O cannot make an old graph appear current. Keep the real cache useful and keep newly filed or closed findings visible through its actual consumer.

This is a repair of `scripts/provenance_dashboard.py::_graph_fingerprint`, inferred by the publication lead from actual default-profile failures. The human did not prescribe a cache implementation. The lead relayed these exact human instructions: “Either way, follow git discipline and our publication review/fix process.” “Make sure you’re using the correct base and read the git history on the architecture side before making changes”. Earlier direction, also relayed by the lead: “Carry viable work through substantive repair and independent review. Where construction appears infeasible, provide the decomposition and evidence for my decision. If deferral or reduced scope is requested, ask me explicitly for that specific disposition.” These are relayed quotations; this design author did not independently read their originating transcript.

The directly read [governing remediation plan](../../audits/2026-08-01-publication-readiness/REMEDIATION_PLAN.md) makes substance the default and permits publication to wait for construction. This machinery repair supplies no missing physics, mathematical theorem or numerical-model validation. Its bounded infrastructure closure does not establish a green publication bundle. No scientific duty, guard, floor, ceiling, timeout, oracle, stage or delivery requirement is relaxed.

Follow [the architecture sequence](../../../.claude/plugins/skeft-qa/skills/architecture-change/SKILL.md), [dashboard ownership](../../architecture/DASHBOARD.md), [check-authoring obligations](../../architecture/CHECK_AUTHORING_GUIDE.md), [wave process](../../WAVE_EXECUTION_PIPELINE.md) and [Codex continuity](../../dev-loops/CODEX_CONTINUITY.md). Existing finding routing and closure owners remain authoritative. This document creates no new gate, ADR, framework, ledger or cache owner.

## Current owner and measured problem

Design base: `dcb9a2c5abe80bf64ab387e649975b4d9359b538`. The checkout was clean before these two design documents. Current owner SHA-256 is `1e6b308bb501ab22f65cec552083865a40c7427aef963067cae590248a9340d7`; original test module SHA-256 is `9d6b311fbd8aa624cb7ed69538157e7c252ef077148c69d8d0fa93a59a2beaf4`.

The actual 2026-10-20 default repo-plus-plugin run returned rc1: 40 failed, 7027 passed, 9 skipped, 92 deselected. Its two cache failures are:

- `TestTheCacheStillCaches::test_an_unchanged_tree_keeps_the_key_stable`;
- `TestTheCacheStillCaches::test_an_unchanged_tree_serves_the_cached_object`.

Captured output identifies `[Errno 2] No such file or directory` for `scripts/__pycache__`. At fingerprint index3391 the missing directory is represented by `<unlistable>` and distinct fresh objects on consecutive calls. These warnings are pytest-captured logs in the original stdout; the separate OS stderr file is empty. The original output already abbreviates the full fingerprint; no complete dynamic read-set census or attempted bytecode filename can be recovered from that abbreviation. No new graph build was run to invent one. The existing r21 lineage analysis compares actual node-ID sets: 38 failures shared with accessible earlier K40, and these cache cases new; equal total failure counts do not imply equal failure identities.

The local ignored handback binds original Q stdout/JUnit, source full bytes, source states, read-only Git, and the source-backed pilot. Those machine-local receipts are evidence, not public dependencies of this design.

### Existing coverage, including the review layer

The original [cache finding](../../../papers/AutomatedReviews/2026-08-14-suite-runtime/infra.md) and Git changes `d82f237b` and `2f5ede79` establish why the key must remain derived from real reads, imported code and ancestors. The latter specifically repaired successful-empty versus unreadable directory aliasing and recorder-finalization failure. Reinstating that alias would recreate the original correctness defect through an error branch.

The existing implementation already provides:

- attempted `open` capture before the syscall, preserving interest in missing inputs;
- `_finalise_read_set` and `_repo_ancestors`, retaining data paths and every repository ancestor, with immediate parents for external inputs;
- `_loaded_repo_module_sources`, adding imported repository `.py` sources that the open hook cannot see again;
- fresh nonmatching keys for absent/empty read sets or capture failures, and the existing mtime-based mid-build-write poison;
- comparison and actual cached-object return in `get_cached_graph`, plus reuse by `_get_uses_edges`;
- original real review/ledger/ancestor invalidation controls and a served-graph finding seam in `tests/test_dashboard_graph_cache.py`.

The review-agent layer covers source, publication and mechanism claims through independent reviews; the architecture workflow requires a genuinely nonauthor whole-design review and a separate literal-intent assessment. It does not replace executable cache controls. Extend the current test module and consumer; do not build a parallel detector or substitute a fixture-only fingerprint for that consumer.

### Source-backed pilot, 2026-10-20

| Production input | Observation and owner binding | Ancestors examined |
|---|---|---|
| `scripts/__pycache__` | Actual Q failing fingerprint names this directory; current read-only `listdir` also returns FileNotFoundError/ENOENT. Failed attempted opens can add its ancestry through the current recorder. | missing directory, `scripts`, repository root |
| `papers/AutomatedReviews/2026-08-14-suite-runtime/infra.md` | Present nonempty review; actual `extract_review_finding_nodes` opens every matching dated review. Original warmed test asserts review paths are captured. | dated directory, `papers/AutomatedReviews`, `papers`, root |
| `docs/review_finding_supersessions.json` | Present nonempty ledger; `_load_supersession_ledger` reads it; original warmed test asserts it is watched. | `docs`, root |
| `scripts/build_graph.py` | Present nonempty production builder; imported by the actual graph consumer. Its `.py` belongs to the code leg even when already imported before recording. | `scripts`, root |
| `scripts/provenance_dashboard.py` | Present nonempty cache owner, with the source hash above. | `scripts`, root |

Every listed ancestor was actually listed or returned the recorded ENOENT. Complete names, stat/hash/mode/mtime observations and row dispositions are retained locally. This is a bounded source-backed sample and the actual Q failure, not a newly captured whole dynamic read set. Successful lists show that the population is not empty; their sizes are not new fixed thresholds or claims about the entire graph input population.

## Decisions

### D1. Change the existing error classification in both legs

Keep the function signature, successful file tuple `(path, st_mtime_ns, st_size)`, sorted successful directory listing, sorted dynamic file union, directory population, cache comparisons and cache consumers.

Classify a caught `OSError` as known absence only when its reported `errno == errno.ENOENT`. Preserve the existing file absence tuple `(path, 0, -1)` for that condition. Use a stable directory absence entry such as `(directory, '<missing>')`, distinct from `(directory, ())`, every successful listing and every unknown entry. No external serialized fingerprint format exists to migrate. The small internal error entries need no versioned schema or API.

For every other file stat error, append a fresh nonmatching entry such as `(path, '<unstatable>', object())` and report the failure. Retain the current fresh nonmatching unlistable directory entry and warning for every other listing error. Only the known ENOENT branch changes directory warning behavior: normal absence need not emit an error warning claiming measurement was impossible. Preserve useful warnings for genuinely unavailable observations.

Class identity or message text alone is insufficient: synthetic `FileNotFoundError` with no errno or a contradictory errno stays unknown. ENOTDIR remains conservatively unknown even where an OS could describe it as a missing descendant; expanding absence semantics is unnecessary for the observed defect. Do not use `exists()` or a second probe to relabel an error, since that can suppress an I/O error or observe a different instant.

The file leg belongs in this repair. Its current broad `except OSError` maps permission, descriptor-pressure and opaque failures to the same stable missing tuple. Repeated unknown errors can therefore match; unknown→ENOENT also matches. Repairing only directories would leave that directly observed source-level false-green counterexample intact.

### D2. Exact error-state contract

Assume an otherwise unchanged, valid recorded population; comparisons below concern the affected entry.

| Syscall observation | File entry | Directory entry | Consecutive equal observation can match? |
|---|---|---|---|
| Successful `stat` / successful sorted `listdir` | existing mtime_ns/size tuple | existing sorted names tuple, including empty `()` | yes |
| `OSError` with reported ENOENT (ordinary FileNotFoundError/errno2) | existing `(path,0,-1)` | stable distinct `<missing>` entry | yes |
| EACCES / EPERM / PermissionError | fresh unknown | fresh unknown | no |
| ENFILE / EMFILE | fresh unknown | fresh unknown | no |
| EIO / ELOOP / ESTALE where supported | fresh unknown | fresh unknown | no |
| ENOTDIR, including an intermediate file | fresh unknown | fresh unknown | no |
| generic opaque OSError, errno absent/unrecognized, synthetic contradictory FileNotFoundError | fresh unknown | fresh unknown | no |
| read set unavailable or empty | whole fresh nonmatching key | whole fresh nonmatching key | no |
| existing recorder detects a mid-build write or finalization fails | whole fresh nonmatching key | whole fresh nonmatching key | no |

A successfully statted path that changes kind keeps the existing metadata semantics. A watched directory replaced by a file produces ENOTDIR and refuses stable reuse. These conservative cases may rebuild more often; they may not manufacture a known-absent state.

### D3. Transition contract

| Before → after | Required result |
|---|---|
| known missing → same known missing | stable entry; unchanged real graph hits the same cached object |
| known missing directory → existing empty directory | different key, even though both have no child names |
| empty directory → nonempty directory / reverse | different sorted listing and key |
| existing directory → missing / recreation after observed missing | different key at each observed boundary |
| known missing file → empty file | different key; successful size0 cannot equal absence size-1 |
| existing file → missing / recreation after observed missing | different key at each observed boundary |
| successful file stat → changed size or changed mtime_ns | different key |
| present or missing → unknown / unknown → present or missing | never matches the preceding unknown key |
| unknown → same unknown, same errno or different unknown | fresh key every call; rebuild remains required |
| new dated finding or ledger update | original invalidation behavior retained; new finding appears in the graph actually served |
| no captured reads / capture-finalization failure / existing detected race | original nonmatching fail-safe retained |

A dangling symlink followed by `stat` or `listdir` can report ENOENT; the key records absence of the resolved lookup at that instant. Creation of that target must change a directly watched missing entry. The recorder's existing path resolution and ancestor selection are unchanged: this design does not claim complete tracking of every symlink alias/retarget outside those watched paths. Test the classified observation and the existing resolved-target transition without pretending a new universal alias guarantee.

### D4. Preserve the original freshness boundaries

Preserve the entire original test module and its real warmed graph fixture and served-node seam. Preserve the dynamic data/code population and all ancestors, PG sync opt-in/async behavior, graph identity behavior, lock protocol, read-set capture, and original invalidation calls. No hard-coded input whitelist, `__pycache__` exclusion, directory creation, bytecode enablement, empty-listing error fallback or cache-disable workaround is allowed.

The fingerprint remains an mtime_ns/size and directory-name observation, not content hashing or an atomic filesystem snapshot. Same-size content changes with exactly unchanged nanosecond mtime remain outside the key. A remove-and-recreate event entirely between observations with identical final names/stat metadata need not be observable. Existing mid-build write detection retains its actual mtime predicate, rather than a stronger all-races claim. Pure metadata reads outside the open audit hook remain the documented limit. No new concurrency or arbitrary filesystem-I/O guarantee is introduced.

## Verification and acceptance

The [implementation plan](../plans/2026-10-20-graph-cache-known-absence-plan.md) carries the file/task map and sequence. Before source implementation, a fresh genuinely nonauthor reviewer must assess this entire design and plan against the actual owner, original cache finding/tests/history and relayed human wording. Internal consistency and literal intent are separate questions; neither self-review nor a green fixture run satisfies them.

After that review and an explicit lead source assignment, extend the existing test module with targeted controls for both tables. Use real temporary filesystem transitions where possible; use path-specific injected syscall errors for permission/descriptor/opaque states. Those injections test error semantics and must be labelled as such, not reported as native ENFILE or permission incidents. Each negative control takes its immediate own baseline, avoiding the historical already-moved-baseline vacuity.

Retain the once-through actual new-finding→served-node seam and original live ledger/review controls. Add a positive assertion involving the actual owner and recorded missing input under bytecode-disabled conditions, equal consecutive keys and cached-object identity. Add file-error tests that fail against the old broad file OSError branch, including repeated unknown and unknown→known-absent. Do not make tests pass by deleting the missing directory from `_READ_SET`.

ROOT then owns journalled production-source regressions of each repaired branch, unchanged meaningful deciders green0→old-source red1→exact restoration green0, retaining original bytes/full mode/nanosecond mtime, raw channels/argv/return codes and empty final journal. A fixture-only fault control complements, rather than substitutes for, the production-source regression. ROOT also owns full containing-module and unchanged default-profile qualification, appropriate scope/merge/full current gates, independent whole source/evidence review, canonical finding/Verify/closure routing and protected-main delivery. Existing dashboard template and real-browser obligations remain part of applicable qualification; no UI rendering conclusion follows from Flask/cache tests.

The actual prior failures remain evidence until repaired and independently verified. The D1–D4 contract remains the implemented specification. Bounded repair and infrastructure closure are accepted at their declared scope; complete delivery and publication remain unaccepted.
