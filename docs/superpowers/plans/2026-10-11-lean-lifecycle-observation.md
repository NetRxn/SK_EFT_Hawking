# Lean lifecycle observation implementation plan

**Status: SOURCE IMPLEMENTED / BOUNDED SOURCE REVIEW ACCEPTED.**
ROOT canonical evidence records documentation/source integration and current project
gates. Bounded source review does not certify those outcomes; live activation remains
unverified and requires its separate measured admission.
Original doc-first design date: 2026-10-11; status reconciliation: 2026-10-12.
Depends on [ADR-008 LO-1–LO-6](../../adrs/ADR-008-shared-lean-slot-control-plane.md#2026-10-11-lifecycle-observation-amendment)
and the [whole design](../specs/2026-10-11-lean-lifecycle-observation-design.md).
This plan is a reviewable next-work contract, not authorization to operate current PIDs.

## Global constraints and acceptance sequence

Keep the existing three physical slots, root-only builds/lifecycle/integration,
fixed public paths and one-way dependency boundary. Extend existing process records
and locks, no second ledger/control plane, no fabricated ownership, unknown-PID
signals/adoption, automatic SIGKILL, dirty reset or extra backend. Implement observations,
reservation consumers and transitions as one coherent change; do not ship a result
producer whose destructive consumers still read absence booleans.

First root freezes exact ADR/spec/plan and source/evidence bindings; independent
whole adversarial and intent-drift review then root admission. This spans lifecycle,
identity, capacity and API seams, so review must consider buildability, overlap,
non-vacuity and intent together. Existing architecture-change skill and worked example
are the process authority. No population-shape assertion is made; if introduced later,
a dated real-slice pilot/manifest is required before that design is accepted.

Phases A–C and the bounded implementation review in Phase D have completed in the
isolated review candidate, including the coherent ND1/ND2 extension and its controls.
Source/test bytes and immutable evidence are independently bound. ROOT documentation/
source integration, independent review, current verification and existing closure-writer
outcomes require their canonical evidence. Phase E remains unverified. No full-tree or
live success is inferred from candidate checks. Active proof runtime needs a separately
admitted window.

## Phase A — Reconcile source and evidence, then admit specification

Owner: root and independent reviewer. Read current owning AGENTS, ADR/guide, topology,
QA/QI map and source/tests; recompute call graph for observation/ownership/registry and
cache replacement functions. Bind exact public source and full F1–F6 report/receipts.
Record authoritative absence of historical unlink instrumentation; never relabel the
present paired observations as exclusive historical causality. Assess fallback/error
paths, descendant identity, global rollback, borrowing and reclaim explicitly.

Acceptance: whole ADR/spec/plan approved or concrete revised contract, root admission,
no inferred runtime lease from the ordinary doc checkout. Root controls integration
of these docs; this author neither commits nor touches primary authorities.

## Phase B — Coherent production implementation and controls

One responsible implementation package owns the complete state/supervisor/controller/
CLI transition and corresponding tests; do not split into inert partial changes.

| File | Responsibility | Required compatibility |
|---|---|---|
| `scripts/lean_slots/state.py` | Explicit bounded process evidence, existing-record schema/atomic reservation support | Owner signature/reclaim callers, old records fail conservatively, existing sole writer/lock |
| `scripts/lean_slots/supervisor.py` | Socket evidence, admission census, transactional spawn/stop, quiescence gate, global rollback/borrow/health/status | Fixed project, max3 physical slots, no unknown signals, existing proxy sessions |
| `scripts/lean_slots/controller.py` | Process owner handling, pre-mutation gates, quarantine/error retention, post-exit residual reporting/doctor | Clean/contained release, unchanged branch absorb/paired dependencies |
| `scripts/lean_slots/cli.py` | Reject ignored supervisor slot flags before action | Existing verbs, probe slot required, existing error exit conventions |
| `tests/test_lean_slots.py` | Existing lifecycle/session/paired/cache compatibility and fixture controls | Preserve old ordering tests and qualified API surface |
| `tests/test_lean_lifecycle_observation.py` | Original lifecycle, six-repair and native-domain production controls using isolated existing-schema records and external seams | Meaningful sole mutants, byte-exact restoration and consumer assertions; no blanket SKIP_SUPERVISOR |
| `tests/test_codex_lean_slot_policy.py` | Existing root/worker/client policy remains intact | No widened worker build/cache/lifecycle allowances |
| `tests/test_architecture_claims.py` | Existing ADR/control-plane claims and actual-call seam checks | Replace brittle substring-only claims when relevant with production behavior/AST, not comments |
| ADR-008 and operator guide | Update accepted status only after admission; exact source/status/CLI contracts | Preserve historical decisions/validation qualifiers; no stale global restart advice |
| This design and plan | Record review corrections, implementation/evidence state and remaining gates | No “done” from unit tests alone |

No configuration/client/proxy endpoint changes are intended. Read actual config/proxy
consumers and retain fingerprints/compatibility; if code proves additional changes
necessary, revise/adversarially review the design first. `host_limits.py` remains
unchanged. A new doctor leg must register in the existing doctor family/shape test.
No new `validate.py` check is planned; if one is proposed, discover every actual
registration site and shipping/mutation obligations before implementation.

## Phase C — Production controls and sole mutation obligations

Tests invoke actual shipped State/Supervisor/Controller/CLI paths with temporary
existing-schema process/lease/cache artifacts. Substitute **only** external observation,
clock/process handle/atomic failure seams needed for deterministic isolation; do not
patch the guard being proved to succeed/fail. Never signal or drive actual production
PIDs, caches, backends or datastores. Assert independent bytes, operation counters,
exception evidence, exact PID identity and reservation/admission results.

For each row, run its healthy positive baseline, seed the one named defect into the
actual production function/path in an isolated candidate, require that same test to
turn red, restore exact source and require green. Save exact mutation patch, source
hash, command/exit/diagnostic and before/after hashes. A mutant changing the test
oracle or only a fixture helper does not count. Use the existing seed-journal discipline
for production artifact mutation; no unjournalled primary mutations or residue.

| Control | Independent negative and positive oracle | Sole production mutant that must fail |
|---|---|---|
| Process/socket observation denied | ps EPERM, nonzero denied stderr, socket EPERM/timeout keep bytes/reservation; reliable absent PID + refused endpoint positive permits safe cleanup | Collapse unavailable into absent |
| Existing identity mismatch | Reused PID/listener never signaled; matched owned identity positive uses bounded stop | Treat mismatch as owned or free |
| Post-SIGTERM observation fails | Retain registration/error; independently confirmed child/tree exit positive clears only then | Delete record when observation becomes unavailable |
| Quiescence before prepare | Unknown listener or denied/missing descendant census: reset/cache-copy counters zero; confirmed never-started/stopped positive permits body | Move/omit gate before yield |
| Paired activation/restoration and rewarm | Each side's unknown/unavailable state blocks before copy; healthy ordering and failure restoration positive | Gate target only or let finally mask body failure |
| Pre-Popen durable reservation | Atomic pending-write failure: Popen count zero; success has pending record before launch | Launch before pending write |
| Identity/registration failure after Popen | Exact created handle rollback/reap or persistent pending/residual; uncertainty never SIGKILL; healthy durable running positive | Raise without rollback/reservation |
| Interrupted launch or timeout | Persisted pending with no invented identity continues reserving on next reader; confirmed no service positive clears | Free pending on timeout/TTL |
| Capacity including another unknown slot | Exact populated endpoint/record census detects unknown and reserves physical number; safe available third slot positive only with bounded total; conflicting same-number servers block | Count only registered matched running records |
| Unavailable/unmapped global census | Admission refuses rather than exact free count; complete positive reports bounded service/reservation state | Treat incomplete census as zero |
| Temporary tool discovery | Borrow uses real admission/transaction; failed stop retains residual; cached positive performs no borrow | Drop reservation or skip admission for harvest |
| Global start/rollback | Later failure retains first created record until verified stopped; original and rollback errors both available | Append rollback ownership only after full startup |
| Lease owner/reclaim | Process-owned unavailable identity cannot create unverifiable ownership or prove owner dead; verified dead + clean/contained/stale positive reclaims; session confirmation remains | Let false process_matches authorize reclaim |
| Release/FREE versus residual | Real completed lease unlink stays complete despite stop failure, but residual visible and future reuse/cache blocked; confirmed stop positive no residual | Clear capacity merely because lease FREE |
| CLI scope | start/stop/status --slot errors before operation counters; unflagged actions global; probe absent errors/present targets exact slot | Silently ignore --slot |
| Branch absorb contract | Literal SHA mismatch refused, actual matching branch positive; no dirty discard or lease edit | Resolve SHA as branch-equivalent absorb match |
| Status/doctor/health | Unknown/unavailable not “down/healthy”; doctor capacity uncertainty fails; healthy observed positive | Feed old booleans/count into safety result |

Census tests must populate real declared endpoints/records and assert the known-present
instances are read. If an AST/source seam guard is used, assert actual calls and the
owned concrete consumer set, not a helper name in prose or an empty scan. Any population
floor/count introduced needs fresh dated measurement, a precise predicate, known-present
witness and evidence of semantic coverage; current design invents none. Do not quote
fixture counts as full runtime coverage or a host census.

## Phase D — Bounded verification and root source integration

Root uses the owning repository's matching `.venv` and a fresh canonical candidate.
Required targeted gate after implementation:

```bash
.venv/bin/python3 -m pytest tests/test_lean_lifecycle_observation.py tests/test_lean_slots.py tests/test_codex_lean_slot_policy.py tests/test_architecture_claims.py -q
git diff --check
```

Root must additionally run the AGENTS-required appropriate fast suite before publication,
using the current canonical command/markers from owning authorities, and the scoped
validator/precheck surfaces warranted by the changed docs/source. Preserve exact
commands, outputs and failures; compare the exact candidate head to the qualified
baseline. Doctor-family checks are not auto-registered validator checks. No Lean rebuild
is owed merely for Python/docs edits; a proof-cache runtime check belongs to Phase E.
A scoped change result is not a whole-tree certification; full gate/submission policies
remain those in validation topology. Commit hooks or a worktree commit are not full gates.

At the original 2026-10-11 checkpoint, all 20 public test failures and 18 validator
failures remain unwaived. Fresh runs must report their actual results, including new
regressions and unchanged failures. This plan does not create an accepted failing
baseline or permission to call the whole gate green. No source/deployment acceptance
is inferred from a finite test pass.

Independent implementation review checks all decisions/callers/controls and evidence,
then root admits a canonical source integration through existing writers. Document
statuses and every newly wrong operator statement must be corrected in that same
accepted change. Root owns normal commit/integration/closure; no parallel shared writer.

## Phase E — Separately coordinated runtime activation

Begin only after active proof owners reach stable checkpoints and root coordinates a
safe lifecycle window. Existing unknown incident processes remain untouched unless
separate actual management authority/evidence permits a canonical operation; this
plan contains none. Do not all-slot restart around an active owner or use a new
supervisor to retroactively adopt old unknown PIDs. If a safe window cannot be formed,
keep accepted source changes unactivated with explicit status.

After source integration, ROOT first obtains fresh read-only capable native evidence.
Global verbs remain global and require all owners drained and known. A conditional
known-owned number replacement uses existing internal APIs under target-slot then
one lifecycle lock, with reliable FREE, complete capable census and both-role backend/
project/retained-descendant quiescence. Within the held lifecycle lock call existing
unlocked internals rather than reacquiring it through public wrappers. Freeze ROOT
dispatch/probes, reconcile actual completed owned requests, and take exact-PID identity,
all-state TCP/listener and native-thread observations plus state-directory membership
on both sides. Passive witnesses do not serialize outside HTTP requests; daemon
handler threads are not joined by server close. Unaccounted activity blocks replacement.
No seamless active-client proxy replacement is claimed: its in-memory session map is
distinct from S-Q persistent-proxy backend rotation. ROOT verifies exact installed
source/config/fingerprints, matching inventory/epoch and resource census before any
eligible operation. Bounded live controls establish
healthy start/lease/prepare/cache park/restart/release and proxy-owned session continuity
on known owned test resources without a fourth actual backend. Interrupted-start and
observation-failure live exercises, if used, require an isolated controlled process,
never old incident PIDs. Record actual stop/reap/child-quiescence and reservation states;
unit mocks do not replace these facts. Preserve prior code/config and all original
incident evidence; rollback cannot bypass uncertain occupancy. Root supplies separate
runtime admission and canonical integration review, with unresolved qualifications.

## Termination and preservation

The original doc-first specification and bounded implementation have independent
source review; their historical frozen artifacts remain immutable. The remaining
repair ends only at merged source, exact meaningful
controls, corrected authorities, root-owned closure record and explicit activation
admission or stated activation blocker. Existing findings use supported closure writers;
this plan creates no ledger/notebook writer. Original research streams, full theorem
contracts and failed gates are unchanged. Any unknown-process recovery or API expansion
beyond this contract needs a new evidence/decision package rather than silent scope drift.

## Explicit failure presentation increment

**Status:** isolated source candidate; whole independent review, normal integration
and separately measured runtime loading remain required.

Extend LO-1/LO-3 through the existing SlotError, CLI and supervisor files plus
`tests/test_lean_lifecycle_observation.py`. Correct ADR/spec/guide/architecture map
before source. Preserve old messages, persisted fields, direct restoration branches,
release warnings and all observation/lifecycle decisions. No new check is introduced.
The sole implementation author owns the coherent graph/serializer/wrapper/test package;
ROOT retains Git, ordinary finding closure, broad gates and runtime admission.

Required controls cover initial creation loss and successful rollback/unlink, identity
and census refusals, reaped/reused handles, coherent readiness, every wrapper and
cause-only borrow, paused/paired nested spawn plus distinct rollback failure, multiple
global cleanups in actual reverse order, exact nine-field witnesses, shared versus
cyclic graphs, all aggregate budgets, strict JSON/UTF-8 boundaries, omitted oversized
items followed by small ones, all-omitted emission and stderr failure containment.
Use actual production methods and CLI dispatch with isolated external seams; capture
original exceptions, exact file preimages and operation counters. Preserve two separate
production mutants with exact red assertions, bytes and restoration/green reruns.

The ordinary finding declares:
`.venv/bin/python -m pytest -m '' tests/test_lean_lifecycle_observation.py tests/test_lean_slots.py tests/test_codex_lean_slot_policy.py -q -s`.
Run that complete command and `git diff --check`, freeze whole source/outputs/hashes
and clause mapping, then independent whole review. ROOT owns broader fast-suite,
normal commit/integration, declared Verify through the closure writer, and any later
known-owner drained runtime window. Isolated propagation does not explain a live
refusal or certify operational reliability.
