# Lean lifecycle observation and residual-capacity design

**Status: SOURCE IMPLEMENTED / BOUNDED SOURCE REVIEW ACCEPTED.**
ROOT canonical evidence records documentation/source integration and current project
gates. Bounded source review does not certify those outcomes; live activation remains
unverified and requires its separate measured admission.
Original doc-first design date: 2026-10-11; status reconciliation: 2026-10-12.
Normative decisions: [ADR-008 LO-1–LO-6](../../adrs/ADR-008-shared-lean-slot-control-plane.md#2026-10-11-lifecycle-observation-amendment).
Execution: [implementation plan](../plans/2026-10-11-lean-lifecycle-observation.md).
This source-only design authorizes no process, lease, cache or runtime action.

**Startup extension:** §5.1 / LO-3a–LO-3e has genuine independent whole source,
isolated runtime and production regression/exact-restoration acceptance, recorded by
ROOT. The explicit missing live-client configuration case remains unmeasured.
Broader fast/project gates, canonical source delivery and actual shared native
loading/lease/MCP/paired admission remain pending. The original contract and its
historical receipts retain their own scope; this is no scientific or runtime grant.

## Persisted-fixture mutation custody

Adverse metadata fixtures use the existing durable owner in `scripts/seed_journal.py`.
Capture the actual original process-record bytes and stat before opening an entry.
Use `seeded_mutation` for one replacement image, including a raw invalid-UTF8 payload,
and `journalled` for the existing truncated-then-legacy multiwrite window. Every
mutation and original live-consumer assertion stays inside that owner's window;
normal restoration is the owner's operation, not a hand-written `finally` write.
Backup and durable entry publication precede mutation. A killed run retains recovery
information for the existing next-session orphan repair and residue guard.

Apply this to `_la_bad_record_through_consumers`, each independent-grammar case and
the required-key test's truncated/legacy window. Keep actual Supervisor record readers,
status/capacity/stop calls, original semantic inputs and invalid bytes, error classes,
negative disk/process effects, native witnesses, deadlines and strict guards. Retain
all original assertions; use the journal-yielded original image to bind custody to the
independently captured source. The strict unjournalled-restore allow-list does not grow.

The current journal restores original bytes and nsmtime; it does not snapshot or
reconstruct file mode. These content-only fixtures overwrite the existing file in
place and must assert unchanged full `st_mode` during mutation and after restoration.
They do not chmod, replace or delete the admitted metadata path. A mode-changing
fixture would require a separately reviewed owner capability, not an unjournalled
fallback or a claim the current journal restores modes. Preserve the test-exclusive
multiwrite path; `journalled` itself does not add `seeded_mutation`'s per-path lock.

This fixture-custody source amendment requires fresh whole nonauthor source/intent
review and ROOT actual startup plus seed-residue verification. Previous bounded
startup evidence remains at its original scope; the broader failed profile, remaining
failures, native source loading and scientific/full-gate/main duties remain owed.

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
Every failed diagnostic or residual publication retains a bounded typed Observation
at its actual catch, including class, errno, message and operation phase. Keep these
observations in occurrence order alongside the original startup and distinct rollback
causes, even when persistence fails. Continue independently safe cleanup; a reporting
failure cannot suppress it. If cleanup succeeds after a reporting failure, the existing
SlotError/Observation transport still exposes that failure and chains the original
startup exception. Do not add a reporting retry or overwrite the first cause or the
rollback fault to store another cause. No persisted schema change is required.
Controls for this aggregate assert the exact original exception object and native
class through `__cause__`, and each subsequent typed publication witness in occurrence
order. A first publication failure with successful cleanup and no secondary reporting
failure still propagates that original exception directly. The aggregate selector must
not discard the original native-error oracle or weaken cleanup/record/capacity checks.
An external atomic-write control inspects only its intended process-record destination;
all unrelated replacements, including raw backend-token writes, pass through unchanged.
The deadline control must reach the actual launch and retain its independent configured
bound, watchdog and persisted-evidence oracles; a prelaunch fixture exception cannot
serve as its timeout result.
Record a deferred descendant-census failure when it is detected, with the actual
native observation and its original operation. Independently safe wrapper cleanup
continues, but a later wait, signal or quiescence failure cannot replace that first
rollback fault. Expose each later distinct failure once in occurrence order. Raising
the already-recorded deferred failure after cleanup does not create a second cause.
The persisted rollback fault retains its original phase and, where available, native
type, errno and detail; outward observations retain subsequent failures separately.
Generic identity, descendant-exit and quiescence refusals carry their actual known
observations as well. Preserve every native witness field, including an absent native
exception class; do not replace it with an invented exception type. The unchanged
persisted error slot selects the first actual failed typed native witness, or the real
wrapper exception when no such native exception exists. Bounded outward context keeps
the original wrapper message and native operation separately from its rollback phase.
Benign present/absent facts cannot displace an actual failed native witness.
An exited or reaped creation handle before identity capture remains an identity-
unavailable refusal. Its outward diagnostic preserves that established classification
and the specific creation/rollback phase text. The existing rollback
`identity unavailable/mismatch` family includes unavailability without asserting an
observed mismatch: retain the actual missing-identity/reaped-handle detail and typed
witnesses, including absent native fields. Do not query, adopt or signal a replacement
to fill a diagnostic or relax the early unreaped-handle guard.
Failure to append is not a reason to delete the prior reservation. Preserve all relevant failures. Stop of an established record
likewise retains identity/reservation on unavailable post-SIGTERM observations.

Existing unregistered listeners cannot receive a fabricated managed record. An
observation-only `uncertain_residual` record at the same established process path may
reserve the physical slot with evidence/endpoint and **no managed PID/signature**.
That is accounting, not adoption: all stop/reuse paths must reject management of it.
Such a write is root-owned under the existing lock; source review supplies no authority
to write such records for current unknown processes. Reliable absence evidence, not a TTL, clears it.


<a id="lo3-creation-admission-design"></a>

### 5.1 Creation-admission extension — LO-3a–LO-3e

**WHOLE SOURCE, ISOLATED RUNTIME AND PRODUCTION CONTROLS ACCEPTED;
CANONICAL DELIVERY AND SHARED NATIVE ADMISSION PENDING.** Whole nonauthor design
review preceded the existing state/supervisor implementation. Genuine independent
whole source/runtime review and ROOT intake accept the complete targeted suites and
meaningful sole-production regressions with exact restoration. The missing
live-client configuration case remains unmeasured. Broader fast/project gates,
canonical committed source, loaded processes, client drain and real shared-slot
qualification remain separate required evidence. Original historical LO/SF/RR
receipts are not reinterpreted. The stable decisions remain LO-3a–LO-3e in ADR-008.

#### Exact additive diagnostic wire contract — LO-3a

The contract below is normative for this extension. Candidate source presence does
not establish an installed or admitted runtime schema.
All objects have exactly the listed required keys; unknown keys/versions, missing
required keys, and null where not explicitly allowed are invalid. These fixed-key
rules govern only the new types below; the outer existing process record retains
its original legacy-field/reader semantics. Types are exact JSON
types, not Python coercions: bool never satisfies integer/number, strings are not
numbers, and dict/list subclasses do not bypass validation. Invalid present evidence
makes the existing record unavailable/reserved; no normalization, dropped field or
best-effort repair may turn it into legacy or free state.

**Observation layout.** Keep the original positional fields in their current order:
state, signature, detail, errno, target, operation, observed_at, returncode,
error_class, identity. Append only reason: str-or-null = None and diagnostics:
dict-or-null = None. Existing detail bounding and identity/signature semantics are
unchanged. Both additions None means the original as_dict shape with no new keys.
Otherwise both must be present and nonnull: reason is a Reason below, diagnostics
is PairV1, and the Observation state/observed_at agree with that pair's classification
and ending UTC. as_dict appends exactly reason and diagnostics; it never copies
diagnostics into observed_identity/signature. One missing/null addition is invalid,
not a reason-only retry grant. New additions are for non-present observations;
ordinary present observations and legacy positional callers retain their old shape.

**Primitive vocabulary.** Int is an exact JSON integer in the interoperable signed
range ±(2^53−1), PosInt is Int>0 and Count is Int>=0. Number is an exact int/float,
finite and non-bool; Mono is Number>=0; Positive is Number>0. ErrorClass is a nonempty
ASCII Python class identifier matching [A-Za-z_][A-Za-z0-9_]{0,127}, recording the
actual caught type(exc).__name__, never an invented ToolFailure class. Hash is exactly
64 lowercase hexadecimal characters; Token is exactly 32 lowercase hexadecimal
characters. UTC is an exact valid-calendar YYYY-MM-DDTHH:MM:SSZ string, seconds 00–59.
Text strings contain Unicode scalar values and encode with strict UTF-8; lone
surrogates are invalid. All nullable fields below are required with explicit null
when unavailable, not omitted.

| Object | Exact required keys and value grammar |
|---|---|
| Stamp | utc: UTC; mono: Mono |
| Span | start: Stamp; end: Stamp; utc_regressed: bool |
| TextV1 | prefix: string; utf8_bytes: Count; sha256: Hash; truncated: bool; hash_scope: full_retained or full_unretained |
| ProbeV1 | operation: ps-selected or ps-census; span: Span; state: present, absent or unavailable; capable: bool; returncode: Int-or-null; error_class: ErrorClass-or-null; errno: Int-or-null; diagnostic: TextV1; operand: TextV1-or-null; target_ppid: Count-or-null; observer_witness: PosInt-or-null |
| PairV1 | version: literal integer 1; pid: PosInt-or-null; expected_signature_supplied: bool; span: Span; selected: ProbeV1-or-null; census: ProbeV1-or-null |
| FailureV1 | id: PosInt; stage: creation or final; attempt: PosInt; state: unavailable, absent or mismatch; reason: Reason; observed_at: UTC; diagnostics: PairV1 |
| ErrorV1 | error_class: ErrorClass; errno: Int-or-null; message: TextV1 |
| FaultV1 | phase: FaultPhase; at: Stamp; error: ErrorV1; observation_ref: PosInt-or-null |

Span.end.mono>=start.mono; utc_regressed is exactly whether parsed ending UTC precedes
starting UTC. UTC supplies dated evidence, not a reliable monotonic clock; a wall-clock
step is explicitly flagged, not silently reordered or used to enlarge a budget.
Probe spans lie within the Pair span, and selected.end.mono<=census.start.mono when
both ran. Failure.observed_at equals Pair.span.end.utc. No reconstructed sample/time
may be inserted to make an interval appear coherent.

Probe operation matches its selected/census position. With a caught Python exception,
returncode is null, error_class is actual/non-null, and errno is its actual integer
or null; without one, error_class/errno are null and returncode is the actual result.
An unavailable probe may have returncode0 with parse/capability failure; that is not
success. A capable probe has state present or absent, no Python error and empty
diagnostic text. A non-capable probe has state unavailable. For capable selected,
returncode0/present requires a nonempty valid full operand; absent requires empty
retained operand and returncode0 or1. Selected target_ppid/observer_witness are null.
For capable census, returncode0 and the known-present observer_witness are required:
present has a valid full target operand and nonnull target_ppid; absent has null
operand/target_ppid. Unavailable census has null operand/target_ppid/witness. The
census witness is the actual observing process PID, equal to startup observer_pid
when embedded in a startup record. A selected unavailable probe retains its actual
stripped output operand if available, else null; census failure never reconstructs
a target from a later call. For either probe, diagnostic is its existing bounded detail text (including the
original detail clamp), empty for a capable probe; it is not a claim to retain the
original complete stderr channel. The census diagnostic is not whole-host output. No new census producer or extra ps invocation is added.

Reason is exactly one of this table's codes. These classify actual full inputs at
production time, before prefixes are discarded. Retained full operands permit the
reader checks specified below; truncated operands remain supplied diagnostic claims.
expected_signature_supplied records signature is not None, not string truthiness.
A mismatch against the unretained expected signature, or census completeness/capability
beyond the retained target/witness fields, remains a producer claim; readers enforce
the declared structure without reconstructing missing inputs or granting authority.

| Reason | Observation/Failure state and required combination |
|---|---|
| invalid_target | unavailable; pid null; selected/census null |
| selected_failure | unavailable; pid PosInt; selected non-capable; census null |
| census_failure | unavailable; pid PosInt; selected capable; census non-capable |
| selected_census_presence_drift | unavailable; both probes capable, exactly one present and one absent |
| selected_census_signature_drift | unavailable; both probes capable/present, valid full signatures unequal |
| confirmed_absent | absent; both probes capable/absent |
| signature_mismatch | mismatch; both probes capable/present with equal full signatures and expected_signature_supplied true |

For all but invalid_target, pid is positive. A skipped probe is null, not an invented
not_run result. A census may run only after a capable selected result. Equality,
inequality and full-signature parse checks are enforced directly when the relevant
operands are full_retained. When any required full text is unretained, a reader
validates the declared field/state/type/capability/reference structure only and
labels the text-content/parse/equality claim supplied, not independently verified.
No hash inequality is used as process identity or proof of unequal original text.

Only selected_census_signature_drift from an actual initial call without an expected
signature can be retried. Actual _spawn invokes the strict observer with signature=None
and checks that local fact as well as the returned false expected_signature_supplied.
No serialized record/reason can authorize a retry after restart or in any ordinary
owner/reclaim/proxy/stop/status consumer. Unknown codes and all other combinations
refuse. Final capture retains no stabilization loop.

**Text, serializer and boundedness.** TextV1.prefix is at most 2048 UTF-8 bytes.
utf8_bytes is the length of the full actual decoded/parsed text after the specified
strip operation, sha256 hashes those exact full UTF-8 bytes, and prefix is an actual
leading scalar-aligned prefix of them. Untruncated means prefix byte length equals
utf8_bytes, truncated false and hash_scope full_retained; the reader recomputes the
length/hash and, when applicable, complete signature parse/equality. A fully retained
operand also equals its own strip(); diagnostic/error messages are not stripped. Truncated means
utf8_bytes strictly exceeds retained length, truncated true and hash_scope
full_unretained. The reader enforces prefix Unicode/bound, full-length inequality,
hash syntax and scope/flag consistency, but cannot verify the hash or suffix of
unretained text. It must never report that full hash/content as verified. Production
same-call tests independently know the full text and check the producer's full hash.

The canonical size calculation is the actual record encoding: json.dumps with
sort_keys=True, indent=2, ensure_ascii=True, allow_nan=False, followed by one newline
and ASCII/UTF-8 encoding. Existing atomic_json uses that formatting; reject nonfinite
data before invoking it. Size includes escaping and newline, not merely character
count. PairV1 is at most 65536 encoded bytes and startup_evidence at most 196608.
Compute each full text's hash/length first; initially retain its longest scalar-aligned
prefix within 2048 bytes. If the pair exceeds its bound, remove one final scalar from
the currently longest prefix by UTF-8 byte length, breaking ties by lexicographic JSON
field path, until it fits. Update truncated/hash_scope; never change full hash/length.
Apply the same deterministic reduction over all TextV1 prefixes for the enclosing
envelope bound, without duplicating referenced pairs. If empty prefixes plus fixed
metadata still exceed a bound or cannot encode, diagnostic production fails visibly;
it cannot enable retry or erase the earlier durable reservation. Readers enforce
bounds/grammar and directly verifiable text checks, not unverifiable maximal-prefix
or absent-suffix claims. Console summaries remain bounded, without full operands or
whole-host data; decoded/parsed text is never claimed as original OS bytes.

**Exact StartupV1 / startup_evidence v1.** The optional top-level field is entirely absent for
legacy records. A present null is invalid. Its only eligible parent has outer schema
version1, process_schema_version2, record_origin ABSENT and recovery ABSENT. No
managed-origin tag is introduced. Existing ordinary v1/other records without this
field keep their original semantics and bytes; stop-only recovery cannot carry it.
Require the parent's existing launch_token: Token and initiator_pid: PosInt.

| Required envelope key | Value |
|---|---|
| version | literal integer 1 |
| launch_token | Token, exactly equal to the unchanged parent launch_token |
| observer_pid | PosInt, exactly equal to parent initiator_pid |
| configured_seconds | Positive |
| started | Stamp immediately before this single Popen |
| local_deadline | Mono = started.mono + configured_seconds, finite |
| enclosing_deadline | Mono-or-null, the actual inherited ContextVar value captured before startup push |
| effective_deadline | Mono = min(local_deadline,enclosing_deadline), or local_deadline if enclosing is null |
| stage | creation, readiness, final, complete or failed |
| creation_attempts | Count of actual initial full-observer calls, excluding the final call |
| creation_succeeded | bool; one genuine coherent initial capture, never inferred from diagnostics |
| failure_count | Count of failed full observations during initial capture plus at most one final observation |
| failures | list of exactly the retained FailureV1 entries defined below |
| first_failure_ref | PosInt-or-null |
| last_failure_ref | PosInt-or-null |
| terminal | FaultV1-or-null |
| rollback | FaultV1-or-null |
| updated | Stamp, updated.mono>=started.mono |
| utc_regressed | bool, exactly updated.utc<started.utc after UTC parsing |

All failure/probe spans and fault stamps fall between started.mono and updated.mono.
When both first and last entries are retained, first.diagnostics.span.end.mono<=last.diagnostics.span.start.mono.
Fault.at is the actual retaining catch/refusal point, not an invented kernel-throw
timestamp: terminal.at.mono is no earlier than any retained failure's end, rollback.at
is no earlier than terminal.at, and updated is no earlier than either fault.
All nonnull pair PIDs agree with the exact creation PID in production and with one
another in the reader; when the parent has a PID they also match it. This is structural
consistency, not adoption authority. Creation calls have expected_signature_supplied
false; signature_mismatch cannot represent a legitimate initial capture.

Let a=creation_attempts, c=a−(1 if creation_succeeded else0); require c>=0. Let q be1
exactly when the last retained failure has stage final, otherwise0. Require
failure_count=c+q; q=1 requires creation_succeeded true. A creation Failure has
id=attempt<=c; a final Failure has id=c+1 and attempt 1. Thus there is at most one
failed final capture. For failure_count 0, failures is empty and both refs null.
For count 1, failures contains only id1 and both refs equal1. For count >1, failures
contains exactly ids 1 and failure_count in ascending order, with refs 1 and
failure_count. Middle pairs are intentionally unretained, not fabricated. These
rules deduplicate first=last and make dangling/duplicate/out-of-order refs invalid.
terminal/rollback observation_ref is null or one of those actually retained ids,
never a dropped middle id.

FaultPhase is one of spawn, handle, creation, diagnostic_write, signature_write,
readiness, final_observation, running_write, deadline, rollback_identity,
rollback_census, rollback_signal, rollback_wait, rollback_quiescence, residual_write.
terminal accepts exactly spawn, handle, creation, diagnostic_write, signature_write,
readiness, final_observation, running_write or deadline. rollback accepts exactly
rollback_identity, rollback_census, rollback_signal, rollback_wait,
rollback_quiescence or residual_write. A final failure q=1 requires terminal.phase final_observation
and observation_ref equal to its final failure id. Faults record actual typed exceptions
through ErrorV1; the first retained refusal is never replaced by the terminal/rollback
fault. Error messages use the same TextV1 rules, without unbounded traceback/args dumps.

Stage creation has creation_succeeded false and parent launch_pending; controlled
retry publication has no top-level PID/signature. Readiness/final have succeeded
true, parent launch_pending, and the original coherent top-level PID/signature.
Complete has succeeded true, parent running, no terminal/rollback and updated.mono
no later than effective_deadline. Failed has nonnull terminal, optional rollback,
and original launch_pending/uncertain_residual behavior; an original raw residual
PID without a signature remains unverified. A false creation_succeeded never permits
a top-level signature, and a true value requires the original coherent top-level
PID/signature even in a failed residual. Other stages require both faults null
and no failed final capture. A positive-stage envelope is formed within the effective
bound; a failed envelope may document an expired bound. Readers enforce updated.mono<=effective_deadline
for every non-failed stage; they never compare a stored deadline to current time as
a liveness/release test. Neither a stored future
deadline nor stage complete proves current liveness, loaded code, ACTIVE lease or
permission to clear anything. Deadline data is not a TTL.

Before controlled retry/sleep, publish bounded diagnostic updates through the existing
atomic writer at the same pending path, preserving launch token/context. On write,
encoding or grammar failure stop retrying, retain the first observation plus actual
failure, and enter existing guarded cleanup. Initial authoritative PID/signature is
published together only after genuine coherent capture; terminal raw-PID behavior
remains original. Crash before a new diagnostic write may lose that observation, but
must leave the earlier durable reservation. No impossible all-crash evidence promise.


#### Creation-only loop and shared deadline

Validate configured startup_timeout_seconds as finite positive numeric data
(excluding bool) before reservation/Popen; absence retains default 45. No new timeout
knob, enlarged default or per-stage grace is introduced. Immediately before the one
Popen, capture s=monotonic_now and the actual enclosing ContextVar value E, then
D_local=s+T and **D_effective=min(D_local,E)**, or D_local when E is null. Both
addition and nonnull E must be finite valid Mono values; invalid context fails closed.
Do not start Popen if the effective bound has already expired. Fingerprint, prelaunch
quiescence/cache preparation and durable prelaunch reservation remain outside this
local startup allowance and retain their original enclosing-context guards.

Reuse the existing observation_budget/ContextVar, extending its absolute-deadline
input to return/yield the exact effective value it installed, preserving all existing
relative callers. The caller uses that same value for **every** explicit startup
deadline check, not the larger local deadline. Keep T/D_local separately diagnostic;
they never govern a later success decision while E is tighter. No second timer
framework or recomputation from now+T is permitted.

D_effective governs all post-initialization capture/diagnostic/signature IO, publication,
readiness, sleeps, final observation and running admission. All observations and
sleeps clamp to its remaining allowance; _wait_port receives D_effective without
starting a fresh timer. Check that exact value immediately before and after each
returned observation or IO/durable publication, before accepting positive readiness,
and at the last success decision. A write returning after E but before D_local still
fails admission even if no further subprocess/observation occurs. An uninterruptible
operation may return late or momentarily publish a running-shaped record; it cannot
return accepted startup/ACTIVE, and triggers original guarded failure handling.

The startup context restores exactly the captured real enclosing value E on every
exit, including exceptions. It removes only its own deadline. Cleanup must not set
None, reset now+T, manufacture grace or disregard a tighter/expired genuine outer
context. With no enclosing deadline, original independent rollback opportunities
remain. With E, all applicable original checks see that actual remaining authority;
before a fallback observation or managed effect, respect its expiry rather than
circumventing it via a selected-only helper. If safe identity/quiescence cannot be
established within the restored context, retain the pending/residual reservation
and failure. Conservative failure/reservation accounting is not a new admission or
clearance grant; no timeout is authority to signal, unlink or declare cleanup complete.

The loop stays inside _spawn's original lifecycle lock and exact pending transaction:

1. Preserve one exact returned Popen handle, PID and launch token. Check genuine handle
   viability before and after each attempt; poll/reap or an exited/reaped handle ends
   creation retry authority. Do not rebind the handle, restart Popen or adopt a reused
   PID. A handle is local creation context, never a fabricated process signature.
2. Invoke the unchanged strict full observer without a supplied expected signature.
   A present full coherent signature plus viable exact unreaped handle permits the
   existing PID/signature pending publication. It does not retroactively validate
   earlier failed samples. One genuine coherent pair is the current contract; do not
   substitute a majority vote or invent a repeated-equality requirement.
3. Only the structured eligible signature-drift result above may cause another
   nondestructive observation. Preserve its first/last evidence, publish as bounded
   pending diagnostics, and sleep up to 0.1 seconds clamped to remaining D_effective. There is
   no busy loop, fresh timer or retry in generic process ownership. All other results
   fail immediately into existing guarded rollback.
4. After first capture/publication, wait for the endpoint under remaining D_effective. Perform
   the existing strict final full observation and exact-handle viability check.
   This final check is not given another stabilization loop or weaker signature
   semantics. Preserve existing handling of a genuinely coherent exec/command sample
   from the still-owned handle; unavailable/mismatch/exit is failure.
5. Check D_effective immediately before and after the durable running publication. If an
   observation or write returns late, no startup success/ACTIVE transition may be
   returned: exit the startup budget and perform the original guarded rollback.
   An uninterruptible atomic write can temporarily publish a running-shaped record
   before its late return is detected; that is not accepted startup or an ACTIVE
   lease, and failure/residual handling must retain it until safe cleanup. Do not
   claim an impossible hard kernel/filesystem/Popen wall or silent rollback authority.

Keep first refusal, terminal phase/typed error and rollback witnesses distinct.
Existing SlotError/Observation transport carries them; a timeout, final refusal or
diagnostic IO failure must not replace the original observation with authored prose.
An eventual successful stabilization retains its earlier refusal as diagnostic
history, not as a failed operation or ownership evidence.

#### Independent cleanup and conserved consumers

Exit only the startup budget context on every exception before the original
rollback observations/effects begin. Inherited unrelated stricter authority remains;
do not manufacture a fresh unlimited context. Preserve original wrapper wait(5 seconds) and
separate descendant exit wait(5 seconds) opportunities, per-operation bounds and every existing
root/child identity, durable reservation and final-quiescence guard. They are not the
separate RR whole-stop 10-second budget and cannot be spent during startup stabilization.

A previously coherent signature may use only the existing exact-unreaped-created-handle
selected fallback after later census failure; an initial failed pair or diagnostic
operand can never enable it. Unknown descendants keep reservation even if wrapper
reap succeeds. No SIGKILL/group signal, terminal-child adoption, unknown-PID kill,
expiry unlink, lease edit, base-ref retarget, dirty reset, cache bypass or extra slot.

Review actual ordinary consumers together: process-owned acquire/reclaim and proxy
lease gate; running reuse/fingerprint/health/status; capacity and retained descendants;
normal stop, stop-only RR recovery and all final quiescence readers; normal/paired
prepare, restore/rewarm, temporary discovery and global rollback. Optional diagnostics
must not change any admission verdict or observer state in these consumers. Shared
source/fingerprint changes still require separate actual loaded-code qualification;
an old process record must not be restamped current.

The implementation plan's startup controls and genuine whole nonauthor design,
implementation/evidence and literal-intent reviews are required. ROOT owns source
integration, native request-drain/loading/normal lifecycle acceptance, existing finding
Verify/closure and protected main. No source-only or isolated-green result closes
scientific or publication gates.

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
Whole source/runtime review accepts only its measured bounded source/test/control
scope. ROOT reconciles current authorities, obtains fresh independent integration
review and completes broader fast/change-appropriate gates before protected source
delivery through existing writers. Canonical primary must be clean and committed
before the existing authoritative build publishes its matching epoch. Current project
gates remain unwaived. Known
owned number APIs retain their scope; conditional replacement needs target-slot then
lifecycle locking, complete capable both-role/backend/project/retained-descendant
quiescence and independently accounted completed client requests. Existing unlocked
internals avoid reacquiring the held lifecycle lock. FREE and passive TCP/native-thread
samples do not prove request drain; outside HTTP races and daemon handler nonjoining
remain limitations. See the operator guide for the before/after witnesses and separate
loaded-source/MCP/lease/reconnect/paired-epoch gates. Unknown resources stay untouched.
