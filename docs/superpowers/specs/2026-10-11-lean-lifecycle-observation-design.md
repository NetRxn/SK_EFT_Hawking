# Lean lifecycle observation and residual-capacity design

**Status: SOURCE IMPLEMENTED / BOUNDED SOURCE REVIEW ACCEPTED.**
ROOT canonical evidence records documentation/source integration and current project
gates. Bounded source review does not certify those outcomes; live activation remains
unverified and requires its separate measured admission.
Original doc-first design date: 2026-10-11; status reconciliation: 2026-10-12.
Normative decisions: [ADR-008 LO-1–LO-6](../../adrs/ADR-008-shared-lean-slot-control-plane.md#2026-10-11-lifecycle-observation-amendment).
Execution: [implementation plan](../plans/2026-10-11-lean-lifecycle-observation.md).
This source-only design authorizes no process, lease, cache or runtime action.

## 1. Problem, authority and evidence limits

The existing controller already owns leases, atomic records, lifecycle locks,
fixed-project HTTP endpoints, cache transitions and the global three physical slots.
The repair belongs there. No new daemon, control-plane sidecar, private overlay,
registry, ledger or scientific theorem is proposed. ADR-008 and the operator guide
own this surface; validation topology and QA/QI maps own their respective gates and
finding/closure writers. Root remains the single lifecycle and integration writer.

At public source `ffef94744b6c115618848c703ceda5ee4c54d2d8`, source reads identify
F1–F6 as described in the amendment. The accepted forensic evidence shows a present
restricted `ps`/socket observation path, not a captured historical unlink event or
exclusive historical cause. The failed first probe stopped at `ps`; it supplies no
socket evidence. The corrected default script and the earlier authorized observation
are different source revisions, explicitly qualified in the immutable root receipts.
This design makes no corpus population, repaired-fraction or host-wide census claim;
therefore no population-shape pilot is claimed or required for this contract. If a
later revision asserts such shape, it owes a dated production-slice manifest before
admission. Existing mathematical reviews and failed validation gates remain separate.

## 2. Existing producers, consumers and uncovered seams

| Surface at the original design source | Existing mechanism | Implemented correction |
|---|---|---|
| `state.py:367-387` | PID start/command signature, `process_matches` | Distinguish identity evidence and observation failure; include owner/reclaim callers |
| `supervisor.py:33-72` | socket and registration liveness helpers | Preserve error evidence; truthful observation state |
| `supervisor.py:115-149,295-320` | shared registered heavy count/owners | Conservative occupancy across all declared physical numbers and role inventories |
| `supervisor.py:161-266` | Popen, signature/atomic registration, SIGTERM stop | Existing-record transaction, residual retention, verified shutdown/reap |
| `supervisor.py:325-444` | lifecycle lock, paused/paired transitions | Actual-quiescence gate before every mutation yield and restoration |
| `supervisor.py:446-501,585-616` | global start/stop, health, temporary tool discovery | Propagate unavailable states, owned-only borrowing/rollback |
| `supervisor.py:744-774` | status serialization | Separate observation, managed identity, residual and capacity from old booleans |
| `controller.py:214-245,696-760` | owner capture and stale reclaim | Unavailable owner observation cannot establish dead owner |
| `controller.py:488-534,762-851` | prepare/absorb/rewarm | Gates before reset/cache mutation; preserve failure causes |
| `controller.py:590-694,1130-1150` | lease exit/reconciliation/doctor | Preserve post-unlink semantics; expose unresolved occupancy |
| `cli.py:191-207` | supervisor action dispatch | Reject ignored slot flags, keep probe slot requirement |
| slot/policy/architecture tests | fixture/mocked ordering and boundary guards | Production functions + external observation/failure seams + independent state oracles |

The whole implementation review dispositions each changed helper's actual callers.
Any later source change requires fresh consumer review. A code-name in a comment is not a consumer.
Preserve `proxy.py` session ownership and transport behavior; no proxy-policy widening
is required. Doctor checks belong to the controller's family, not `validate.py`.
No new validator check/registration family is proposed. If implementation adds one,
that is a design revision with live registration discovery and mutation obligations.

## 3. LO-1 observation contract

Internal result objects carry state, target, operation, UTC observation time, observed
identity (when available), return code/error class/errno and bounded diagnostic text.
They never upgrade an inferred argv/port match into managed process ownership.

| Result | Meaning | Permitted consequence |
|---|---|---|
| Present with matching identity | Captured PID/start/command matches authoritative managed record and observer succeeded | May continue owned operation; still verify descendants/port for shutdown |
| Confirmed absent | Reliable, target-specific absence evidence with observer capability established | May clean stale identity only after target quiescence is independently satisfied |
| Identity mismatch | PID is observable but differs from stored signature | Never signal that PID; retain old evidence and investigate residual occupancy |
| Unavailable | Permission failure, ambiguous/nonzero tool result, timeout, malformed/partial output or unknown identity | Retain record/reservation; block destructive cleanup, reuse and mutation |

Process observation must inspect `ps` exit code, stdout and stderr, not merely
`stdout.strip()`. A nonzero empty result alone is insufficient: distinguish a validated
platform no-such-PID result from denied/failed tooling with independently reliable
absence/capability evidence. A bounded zero-signal existence check of an **already
recorded PID**, where supported, can contribute evidence (`ESRCH` versus `EPERM`);
it is not a signal/adoption mechanism and must itself preserve uncertainty. PID
reuse establishes the original identity is gone only when reliable evidence supports
that conclusion; it grants no authority over the replacement process.

Socket connection success means a listener exists, not that it belongs to this
backend. `ECONNREFUSED` can establish no listener at that endpoint then; permission
errors, timeouts and network/observer failures cannot. A closed endpoint alone does
not show an LSP or its descendants have stopped or released project mappings.

Do not remove existing managed identity fields on observation error. Boolean helpers
may survive only as convenience readers derived from explicit states; destructive
consumers must inspect the evidence and not treat false as permission. Owner capture
for process-owned leases must refuse unavailable signatures; stale process-owner
reclaim must refuse unavailable identity/death evidence. Session-owner confirmation
and heartbeat/dirty/containment gates remain unchanged; a process observation repair
must not silently loosen them.

## 4. LO-2 actual-quiescence gate

Before **any** reset/cache replacement yield, while holding the existing lifecycle
lock, establish the target physical number and fixed project; inspect its existing
registration, endpoint and all known relevant process descendants. Stop a verified
managed backend using the existing bounded SIGTERM path and confirm that the owned
process tree is absent and the endpoint is closed. Wrapper exit is insufficient if
its known child or associated project LSP remains. If the platform cannot reliably
observe relevant descendants/project occupancy, fail as unavailable, not as stopped.

For a legitimately never-started backend, reliable absence of its configured listener,
registration residual and relevant fixed-project process occupancy admits preparation.
Missing JSON is not the absence proof. Unknown listener/identity or incomplete census
refuses before `yield`, Git reset, cache deletion/copy, backend credential exposure
or Popen. Do not adopt a discovered server to create quiescence.

Apply this gate to `paused_backend`, both sides of `activating_from`, counterpart
restoration and absorb rewarm; inspect standalone preparation and every production
cache replacement caller. Proxy health is still required but proves a different
property. On entry failure do not run the body or blindly attempt restart. On body
failure, bounded restoration of a previously owned backend may be attempted only if
safe; retain both original and restoration failure evidence without one masking the
other. `Controller` quarantines failed transitions through its existing writer.
Primary build/cache ownership remains root-only; worker exceptions never bypass gates.

## 5. LO-3 launch/stop transaction and interruption safety

Extend the **existing** `Inventory.process_path(kind, number)` record and atomic writer.
The outer `schema_version` remains 1; new records carry `process_schema_version: 2`
and phase `launch_pending`, `running` or `uncertain_residual`. Legacy omitted process
version/phase reads as version 1/running only with valid configured identity and
complete root PID/signature. Invalid schema, phase, identity or retained descendants
are unavailable, not free; readers preserve the record rather than normalizing away
uncertainty. Runtime fingerprints include the changed source.

The heavy-backend entry checks a complete nonconflicting physical census before
`_spawn`; the proxy entry uses its own configured registration/fingerprint and
proxy-specific quiescence checks, not the heavy-backend admission count. Under the
existing lifecycle lock `_spawn` writes `launch_pending` before Popen, with
`schema_version`, `process_schema_version`, `phase`, `launch_token`, `repo_role`,
`slot`, `kind`, `inventory_source`, `project`, `command`, `runtime_fingerprint`,
`port`, `started_at` and `initiator_pid`. The initiator PID is diagnostic provenance,
not a captured owner identity or lease authority. There is initially no process PID
or trusted signature. Reservation-write failure prevents Popen. An interrupted
pending transaction reserves capacity until reliable quiescence permits cleanup;
expiry alone does not release it.

After Popen, retain the exact live handle. Assign its PID in memory, then require
coherent selected-process and complete-census signature capture while the handle is
unreaped. Only then persist PID and signature together in the pending record, before
port readiness. If that initial capture or write fails, the earlier durable pending
record continues reserving capacity. Initial capture failure cannot use a signature
invented from argv or the handle. There is no serialized `identity-established`
phase. Port readiness and a subsequent present signature plus live handle precede
the durable `running` transition; a process without durable registration is never
reported as successfully started. Failures enter the bounded owned rollback path.

Rollback may SIGTERM only the exact just-created process whose live ownership is
still established by the creation handle and a valid non-reused identity. After
initial coherent capture, a later census failure may use the exact unreaped handle
and a matching capable selected-PID signature for bounded wrapper reap. This narrow
fallback neither grants generic management/dispatch ownership nor clears descendant
uncertainty. Without valid owned identity, retain pending/uncertain occupancy and fail
without signaling.
If wrapper exits/execs or ownership of descendants is uncertain, do not infer ownership
from command strings, listening ports, a process group number or a guessed PID.
Controlled descendant tracking and identity verification must establish any automatic
owned-tree stop, or it remains a residual. Never automatic SIGKILL, including newly
spawned processes; bounded wait/reap or explicit residual is the outcome.

Once reliable shutdown/quiescence is demonstrated, delete the existing record as
normal. If terminate/wait, readiness, signature capture, atomic registration or global
start rollback fails, retain its prior record and attempt the existing atomic residual
write. `error` and `rollback_error` are stringified exceptions, not promised bounded
serialized diagnostics; typed Observation diagnostics have their own bounded contract.
A failed residual write leaves the earlier durable pending reservation. A successful
write can exceed the separate reader size limit; a later reader then reports unavailable
and retains that record/reservation rather than declaring free.
Failure to append is not a reason to delete the prior reservation. Preserve all relevant failures. Stop of an established record
likewise retains identity/reservation on unavailable post-SIGTERM observations.

Existing unregistered listeners cannot receive a fabricated managed record. An
observation-only `uncertain_residual` record at the same established process path may
reserve the physical slot with evidence/endpoint and **no managed PID/signature**.
That is accounting, not adoption: all stop/reuse paths must reject management of it.
Such a write is root-owned under the existing lock; source review supplies no authority
to write such records for current unknown processes. Reliable absence evidence, not a TTL, clears it.

## 6. LO-4 capacity, status and doctor

Under the shared lifecycle lock, reconcile evidence over the fixed physical numbers,
configured role endpoint inventories and all existing process records. Use existing
inventory resolution; do not commit downstream paths/data or build another census
service. Inspect all relevant configured endpoints/records, not only the target or
only files that happen to exist. Unsupported/corrupt records, unavailable observers,
unregistered listeners and launch-pending/residual phases reserve the associated
physical number. A known conflict of multiple services on one physical number blocks
admission regardless of total. Exclude a linked copy only using capable Git identity
and a matching canonical primary's complete physical/server domain; keep primary
conflicts and supported same-primary aliases. Validate relevant ancestry using the
complete capable census through generic intermediates. Only a matching-project
ancestor makes a row part of the same project tree; independent project services
under a nonproject manager stay distinct. Cycles, duplicate PIDs, missing relevant
ancestors or unavailable observations block completeness. Stored generic/reparented
descendant identity remains independent of present ancestry. See the
[ND1/ND2 design](2026-10-12-lean-native-domain-census-design.md).

Admission requires the target physical number confirmed available, no cross-role
owner/residual for it, and a conservative global reservation total within the existing
three-slot limit after adding the new service. Uncertainty on another physical number
reserves that number, rather than creating free capacity. If evidence cannot bound
occupancy (e.g. unresolved multiple services or unsupported mapping), fail admission
instead of declaring an exact total. The census asserts safety in the configured
controller domain; it is not an arbitrary whole-host absence proof. Known external
heavy services/residuals must be accounted for or block admission; root must not use
this limited census to justify a fourth actual backend.

Status supplies separate lease state, process record phase/identity authority,
observation states/errors, confirmed service count, conservative reserved numbers
and census completeness. Keep old JSON fields for compatibility only with explicit
observed-only semantics; never feed those booleans/counts back into safety admission.
`down` is valid only for confirmed absence; unavailable/unknown/mismatch must be
visible. Doctor's existing heavy limit/endpoint checks fail on unavailable/unresolved
capacity, even if a registry-derived numerical bound looks small. Diagnostics must
not recommend unconditional all-slot restart or adoption. Repeated status reads may
observe/report; they may not signal/spawn/unlink reservations as a hidden side effect.

## 7. LO-5 and LO-6 front-door/integration contract

Reject `--slot` for supervisor `start`, `stop`, `status` before constructing an action
that can mutate anything; error text says those verbs are global. `probe` without
`--slot` still fails, and with it targets exactly that slot. Do not add scoped verbs
or reinterpret ignored input as success. Parser/help/operator documentation and tests
must agree. Existing direct root `start_backend`/`stop_backend` internals remain under
lifecycle ownership and the strengthened contract.

Lease exits retain unlink-before-reconcile and completed-exit nonfatal resource
warnings. `FREE` does not clear uncertain occupancy. Status/doctor must expose it;
subsequent preparation or launch cannot bypass it. A release warning must describe
an unresolved resource, not promise `start` repairs unknown processes. Retain clean,
containment, paired-dependency, session-owner and integration gates.

Acquire normal proof work using the actual primary branch name and matching epoch.
`absorb` retains literal branch comparison; document the source distinction between
resolvable ref and supported absorption ref. Do not broaden acquisition/ref behavior,
add retarget commands or silently change no-change release semantics in this repair.
On mismatch preserve exact source/commits through canonical recovery; a new lease or
physical slot requires full fresh runtime validation and independent integration.

## 8. Temporary borrowing, health and global rollback

Tool-list harvesting must use the same admission/registration/stop transaction as
normal starts and retain residual reservations on failure. It may not hide errors and
claim that a borrowed backend is “always stopped” without confirmed stop evidence.
If unresolved occupancy prevents borrowing, expose discovery unavailability without
spawning elsewhere beyond the cap. Cache-hit tool discovery needs no borrow. Preserve
proxy/session semantics and already cached tools; discovery failure cannot mint fake
tools or modify loaded hook/config state.

Global start rollback records every process it created **before** a later operation
can fail; each exact created record remains until verified stopped. A rollback failure
must survive with the original startup failure and reservation. Existing unknown
servers are never placed in the owned rollback list. Global stop likewise refuses
unknown/unavailable targets and retains evidence; its partial-result diagnostics must
not describe all slots as stopped. Health checks distinguish observation failure,
stale fingerprint, verified stopped and unknown ownership.

## 9. Verification and admission

The plan defines production-path negative/positive controls and sole mutants for every
LO decision, external OS seams, independent file/counter/identity oracles, no production
PID actions and no helper-mirroring tests. Source integration and runtime activation
are separate gates. Whole independent adversarial review must inspect the amended ADR,
this design, the plan, actual implementation consumers and original F1–F6 scope.
Whole source review accepts only bounded source/test/evidence. ROOT reconciles these
authorities and obtains independent integration review before selective primary source
integration through existing writers. Current project gates remain unwaived. Known
owned number APIs retain their scope; conditional replacement needs target-slot then
lifecycle locking, complete capable both-role/backend/project/retained-descendant
quiescence and independently accounted completed client requests. Existing unlocked
internals avoid reacquiring the held lifecycle lock. FREE and passive TCP/native-thread
samples do not prove request drain; outside HTTP races and daemon handler nonjoining
remain limitations. See the operator guide for the before/after witnesses and separate
loaded-source/MCP/lease/reconnect/paired-epoch gates. Unknown resources stay untouched.

## Explicit failure diagnostics (LO-1 / LO-3 presentation)

**Status:** isolated source candidate; whole independent review, normal integration
and separately measured runtime loading remain required.

`SlotError.secondary_errors` is an optional tuple of `(role, actual_exception)`
references. Construction is passive. Each exception retains its own observations
and original explicit cause. The CLI collector follows only `__cause__` and these
labelled references, cause first, then stored order. It never follows implicit
context, traceback, locals or native state. Existing first/last shutdown witnesses
remain bounded witnesses rather than a complete observation history.

After the unchanged `slotctl: <message>` stderr emission, a caught failure with any
own observation discovered by traversal emits `slotctl diagnostics: ` followed by
one strict JSON object with `schema: "slotctl-diagnostics/v1"`. Exit status remains
two and the diagnostic path emits no stdout. Formatting/write errors are contained.
No discovered observation means no added line; an unvisited tail may still contain
unknown witnesses. Normal returned observations, parser output, release warnings
and proxy HTTP/JSON-RPC surfaces retain their existing contracts.

The envelope contains `groups`, `edges`, `limits`, `inspection`, `omitted`,
`budget_exhausted`, `unvisited_content_unknown`, `traversal_complete`,
`observations_complete`, and `fallback`. Groups have small integer `id`, bounded
`class` and `message`, separate presentation truncation flags, `observations_total`,
and `observations` entries containing original tuple `index` plus exact `value`.
Edges have `from`, nullable `to`, `relation` (`cause` or `secondary`), bounded `role`,
`role_truncated`, and `disposition` (`new`, `shared`, `cycle`, or `group_budget`).
Only a reference to the current DFS stack is a cycle; repeated objects reuse IDs.

Aggregate limits are eight groups including root, sixteen relationship inspections,
thirty-two observation attempts, and 65536 final encoded UTF-8 JSON bytes. Inspected
repeated relationships and omitted observations consume their budgets. Known direct
relationship and observation tuple lengths give exact local omissions; unreachable
subgraph contents are explicitly unknown. Group/edge omissions imply incomplete
traversal. Cycles/shared references are disclosed independently of completeness.
Class and role presentation are capped at 128 Unicode code points, messages at 1024;
truncation flags are separate from observation completeness. Unencodable presentation
text is replaced with an explicitly marked unavailable presentation.

Discover bounded graph metadata first and reserve its encoded size plus 4096 bytes
for final counters before accepting payloads. Observation encoding is strict JSON,
with finite numbers, string dictionary keys, no coercion and no `default=str`.
Use bounded structural preflight (depth 64, 65536 value/key visits and conservative
string/number size checks) and bounded streaming encoding. The omission precedence
is observation-attempt budget, serialization/structural refusal, then byte budget.
Oversized/invalid items are omitted whole, leaving later small items eligible. Exact
small `Observation.as_dict()` values preserve all nine fields; identities, signatures
and targets are never shortened. A final encoded-size check removes whole admitted
items from the end if required, attributing each removal to byte budget. A bounded
fallback states discovered evidence was omitted and never claims completeness.
These defensive budgets are not census counts, readiness gates or cost guarantees.

Actual multi-failure wrappers attach only already-caught objects:

| Method | Secondary role |
|---|---|
| `_spawn` | `launch_rollback` |
| `paused_backend` | `backend_restoration` |
| `activating_from` | `paired_restoration` |
| `restore_counterpart` | `target_recovery` |
| `start` | `start_cleanup:<kind>:<slot>`, original reverse-started order |
| `_harvest_tool_list_unlocked` | `borrowed_cleanup` |

Existing message and persisted error strings stay unchanged. Cause-only safe-capacity
borrowing, source/environment failure, quiescence, stop and state wrappers retain
their explicit causes. Controller bookkeeping bare rethrows preserve the object;
implicit bookkeeping/lock-cleanup histories remain outside this representation.
Post-unlink warning `observations=` arrays, orphan persisted evidence and proxy error
surfaces are unchanged. No observation, poll, clock, write, signal, reap, retry,
reservation, capacity, readiness, fingerprint or lifecycle decision is added.

Acceptance requires actual production-method/CLI controls through temporary records
and external OS seams, nested restoration/spawn/rollback and multiple cleanup roles,
strict JSON and UTF-8 boundaries, exact witnesses and unchanged lifecycle counters.
Separate production mutations dropping a secondary attachment and suppressing CLI
emission must each fail its specific full-route oracle, then restore exact bytes and
rerun green. Whole independent source/evidence review precedes ROOT commit, existing
finding closure and separately measured runtime admission.
