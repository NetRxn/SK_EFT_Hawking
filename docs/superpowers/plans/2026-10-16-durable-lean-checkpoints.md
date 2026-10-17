# Durable Lean checkpoint implementation plan

Status: source candidate exists; revised crash-recovery specification independently
reviewed and selected for implementation. No live-slot operation is authorized
by this file alone. Follow ADR-008 CP and the
[design](../specs/2026-10-16-durable-lean-checkpoints-design.md).

## Global constraints

ROOT owns lifecycle, Git, notebook/roadmap, gate/closure writers and acceptance.
Workers share a codebase, preserve other edits and own only assigned paths. Use
ordinary non-Lean source worktrees for implementation/tests. Preserve active
canonical primaries, current dependency windows and actual occupied slots. Keep
public artifacts product-neutral. No new pool, reservation ledger, supervisor
start/stop/status family, generic loader or reduced mathematical completion target.

## Coherent packages and order

1. ROOT documents the owner-first ADR/spec/plan and files the enabling gap through
   the existing finding/remediation planner. Fresh independent reviewer assesses
   adversarial safety, implementability, canonical bootstrap and user-intent drift.
   Source-measure actual code seams and classification costs; correct proposal
   before treating it as settled. No population-wide claims from a source slice.
2. One implementation owner extends `scripts/lean_slots/controller.py`, `state.py`
   and `cli.py` with the checkpoint journal/preservation transaction and guarded
   resume. Use the existing supervisor owned-stop/native observation primitives;
   any necessary narrow `supervisor.py` seam belongs to this same coherent package.
   The independently reviewed CP-7 readiness amendment additionally assigns
   `scripts/lean_slots/proxy.py` and the existing proxy/lifecycle/checkpoint tests
   to this same owner; no code authority exists before that review and fresh packet.
   A focused internal `scripts/lean_slots/checkpoints.py` helper and
   `tests/test_lean_slot_checkpoints.py` may organize this same transaction and
   production-reader tests; they do not add a separate control plane or journal.
   ROOT extends the existing `.codex/hooks/pre_tool_use_policy.py` slotctl command
   denial to include `checkpoint`; the implementation owner adds preserve/recover/
   resume/bootstrap spellings to the existing worker-policy tests. This is the
   existing defense-in-depth shell guard, not a new runtime authority.
   ROOT also updates the existing runtime-fingerprint test MEMBERS roster for
   the new `checkpoints.py` module, retaining exact complete source membership
   and ordinary SF behavior.
   Keep release/acquire containment unchanged. New code remains inactive for real
   leases during source tests. ROOT corrects ADR/operator/continuity documentation
   before code assumptions change and binds the exact candidate implementation.
3. Same package supplies production-seam tests in `tests/test_lean_slots.py` and
   relevant existing supervisor/policy suites; add a focused checkpoint test module
   only if existing suite organization warrants it. Independently seed each sole
   mutant into actual production readers/guards. Capture crash/recovery and
   preservation manifests, restore bytes and rerun required suites.
4. Fresh independent implementation review and ROOT intake bind full source,
   manifests, original acceptance boundaries, unchanged lifecycle tests and all
   mutation results. Isolated native pilot proves candidate stop-only import route,
   actual drain/owned-family absence, durability/ref protection, reset/release,
   counterpart resource accounting and interruption recovery. No production author
   is stopped to make this pilot possible.
5. ROOT separately admits the exact narrow bootstrap with complete current
   canonical/source/lease/native bindings. At each author's source-safe boundary,
   ordinary WIP commit, complete durable checkpoint and canonical release occur
   one number at a time. On uncertainty preserve/quarantine and continue unrelated
   work; no primary advance while an affected dependency owner remains active.
6. Integrate already completed upstream work through normal absorption/current
   gates. Integrate reviewed controller source normally; follow LO/SF coordinated
   loaded-code admission only on actually drained/quiescent eligible resources.
   Fresh current builds/epochs, acquire/prepare and guarded resume revalidate each
   original full proof contract. Old evidence never certifies changed dependencies.
7. ROOT performs supported finding Verify/closure, wave closeout, current-head
   gates and normal reviewed main merge. Do not close at green unit tests, a source
   WIP commit, a successful checkpoint or a free lease.

## Required minimum checks

Run the repository-required `tests/test_lean_slots.py` and
`tests/test_codex_lean_slot_policy.py`, relevant supervisor/overlay/pairing tests,
`git diff --check`, broader fast suite and actual current-head gates. The complete
production-mutant and native pilot matrix is in the design. Record source-only,
isolated native and live admission as distinct states through existing evidence
writers and continuity packets. No manually rewritten journal/lease/pin/cache.

## Crash-recovery completion within the same package

Before further code, ROOT amends CP-3/CP-6/CP-8 and the design from actual abrupt
holder-death and native primitive evidence; obtain independent whole-specification
review with all CP-1 through CP-8 unchanged. Prior source review is historical for
this amendment. Extend the existing lock, Git/evidence runner and journal owners;
do not add a pool, service, ledger or generic process manager.

The implementation owner then delivers the stable advisory inode, complete atomic
NO-REPLACE legacy facade publication/intact retirement, strict recognized-generation
recovery and full mutator launch/completion barrier as one coherent change. Include
the selected nonblocking `fcntl.flock` API and explicit reentry/thread/fork/exec rules.
Thread a typed validated CP context through existing CheckpointTransaction→numbered
controller lock→supervisor lifecycle seams only; default ordinary numbered commands,
prepare/reset/cache/copy, authoritative build, integration/rebase/abort/merge/nested
build and ordinary supervisor callers retain legacy behavior and current nesting.
Never auto-retire their records or claim their descendant families covered. Future
caller upgrades need independent operation-specific admission. Test omitted CP
context and accidental ordinary activation as actual production mutants. Include
parent-death/timeout/exception, descendant fd lifetime, legacy-caller races and
unknown-legacy refusal. Backend/proxy fd policy stays separate. Complete the independently reviewed CP-7
pending/completed context in the existing lease/journal and actual LeaseGate/probe
consumers. Publish pending context with ACTIVE atomically, permit only the internal
live matching smoke, durably complete the journal before completed lease admission,
and preserve context through ordinary lifecycle/heartbeat. Preserve reactivation
then smoke ordering, all normal SF/session/authentication guards, and no secret
forwarding. Exercise the full death, positive completion and sole-mutant controls
in the design. Historical Host-modeled/actual HTTP red controls are source evidence;
they do not replace isolated native A, independent A acceptance, B or live admission.

Run the full production crash/mutation matrix and staged native pilots: candidate
as ordinary canonical in an isolated OS domain first, independent acceptance, then
old-canonical/candidate CP-8 bridge in a separate isolated domain, then separately
gated live admission. Bind honest phase/domain/source/receipt authority before any
constructor or state effect; no fabricated prior-pilot boolean or host-census filter.
Show successful whole recovery and later-owner no-replay, not only refusals.

At final source freeze, use existing generated-artifact writers for module census,
architecture inventory and test-file counts. Run required/broader/current-head gates,
independent implementation review, supported finding Verify/closure and normal
reviewed main delivery. Classify unrelated observed failures with evidence; do not
waive a red broad gate or hand-edit derived counts to obtain green.


## R4 observation and fixture readiness within the same package

1. ROOT applies the independently confirmed R4-S1/S2/S3/S4 and R4-F1/F2
   specification to ADR, design, operator guide and this plan before source edits,
   then binds the exact docs/source and terminal old gates in a fresh owner packet.
2. One owner changes `scripts/lean_slots/state.py` and the existing lifecycle/slot
   tests for narrow whole-pass scheduler resampling, one helper absolute budget,
   strict usable final coherence and original coherent absence. No supervisor
   signal/new-descendant guard or generic-reader relaxation is allocated.
3. The same owner updates `tests/fixtures/lean_checkpoint_native_peer.py` and
   existing native controls for actual owned generation/identity/parent startup
   acknowledgment before listener readiness and a separate deliberately late-child
   refusal. Keep original source/evidence and raw failed case receipts immutable.
4. First run meaningful focused production-seam positives/negatives, including
   actual no-budget CP/orphan paths and earlier nested deadlines, exact rc1 absence,
   persistent flapping and simultaneous nondrift failures. Verify root listener
   absence during slow child initialization and strict late-child refusal.
5. Freeze exact source; fresh full five named suites, all original native case
   dictionaries once plus new controls, max one isolated container, complete raw
   observations and actual owned OS absence. Preserve every failure; no retries
   or source changes during gates. Complete exact-source journalled sole omissions,
   restore/immediate greens and independent whole source/native review.
6. ROOT then evaluates whole A; only accepted A permits separately admitted B,
   then explicit live C. Existing broader gates, generated writers, Verify/closure
   and normal reviewed main delivery remain. A source WIP or test pass is not closure.

## R4-F1-A publication correction in the existing fixture

Global constraints: retain the whole existing CP/R4 package and every prior raw
failure/control. Current source stays frozen until both current validation jobs
are terminal and actual owned OS absence is verified. File the canonical finding
and apply reviewed ADR/spec/guide/plan prose before changing code. ROOT owns
controller/build/integration/closure/main; this plan grants no live activation.

1. Measure exact final current campaign outcomes without retrying cases or
   stitching historical passes. Bind unchanged source/fixture and all raw evidence.
2. Independently review this entire amendment and its user-intent fit. Pilot the
   selected NO-REPLACE primitive on the actual ACK bind mount/image and host-unit
   filesystem, including exclusive competing publishers and preexisting objects.
   Do not presume CP primitives on another filesystem establish ACK support.
3. One owner repairs only `tests/fixtures/lean_checkpoint_native_peer.py` and
   existing fixture tests in `tests/test_lean_slots.py`. Preserve helper API
   compatibility where existing callers need it; an optional cancellation callback
   may carry the existing stopped predicate. No production controller/observer/
   supervisor policy change, new service, alternate ledger or global test skip.
4. Deterministic actual-helper old-red/new-green: barrier around first write,
   in the uncontended initially-absent case observe old final-visible incomplete
   bytes, corrected final absent while staged, then complete same-inode/single-link
   valid read. Separate collision/concurrent-winner controls preserve an existing
   complete final; they assert unchanged winner identity/bytes, not global absence.
   No sleep-based race assertion.
5. At the actual helper seam cover no-overwrite collisions; unsupported API/flags,
   EXDEV, permission, short write/file-fsync/parent-fsync failures; strict mode/UID/
   link/type/UTF-8/JSON/object/size trust; fd and entry/directory substitution,
   after-acquisition ENOENT, interrupted reads, parse/return deadline and stopped
   child. Controlled owned-publisher deaths before/during/after publication retain
   exact evidence: absent final before rename, complete preserved final afterward.
6. Cover every normal and deliberate late-child caller, root token/port/listener
   failure, exact owned cleanup and finite-wait uncertainty. Preserve malformed/
   trust failures as fatal. Recheck recursive identities and no listener until the
   planned family is ready; independently retain actual late-child refusal with
   zero new-family signals and unchanged reservation/quarantine.
7. Freeze corrected source for independent whole source review, focused controls,
   current full five named suites, all original native cases once plus retained
   focused controls, exact-source sole omissions/immediate restores and fresh
   independent whole source/native intake. Maximum one disposable native OS;
   no automatic failed-case retry, source mutation during gates or green stitching.
8. Only whole A acceptance permits separately admitted B then explicit live C.
   Existing current gates, supported closure writer, document sync, full science
   separation and normal reviewed main delivery remain required. A fixture-only
   focused green does not close the enabling package or scientific streams.
