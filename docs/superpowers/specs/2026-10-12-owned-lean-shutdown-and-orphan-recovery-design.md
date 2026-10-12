# Owned Lean shutdown and stop-only orphan recovery

Status: **design accepted; candidate source implemented, verification pending.**
Whole independent design review and ROOT intake accepted the contract. Candidate
source and controls exist; tests, whole source review and native recovery acceptance
remain pending. This document alone authorizes no native operation. Owning decisions: [ADR-008 RR-1–RR-4](../../adrs/ADR-008-shared-lean-slot-control-plane.md#owned-shutdown-and-operator-authorized-orphan-recovery).
The operator has explicitly authorized repairing shutdown and restoring affected
slots. This design implements that scope without altering scientific work or gates.

## Existing machinery and exact residue

Source baseline: `33be8dbe04d3477788b2696633970c76fc72365f`, inspected 2026-10-12.
`scripts/lean_slots/state.py:482–600` provides bounded, capable process observation;
`supervisor.py:581–623` validates existing process records; `:834–978` owns capacity
and quiescence; `:1124–1175` owns stop; `:1242–1264` owns lifecycle locking.
`controller.py:216–295` owns session matching and `:592–647` owns preservation at
release. `cli.py` retains global supervisor start/stop/status semantics.

Generic identity combines second-resolution native `lstart` with mutable command
text. `_stop` saves identities, walks reversed numeric PIDs rather than ancestry,
and refuses a descendant mismatch before reaching live parents. A retained exited
child can therefore block progress. Existing missing-registration refusal correctly
blocks automatic stop/adoption but supplies no explicitly authorized orphan-stop
operation. Extend these owners; do not introduce a ledger, watchdog or new normal
lease lifecycle. Native incident particulars belong in [RR1/RR2](../../../papers/AutomatedReviews/2026-10-12-lean-runner-recovery/source.md).
The bound original witness is evidence of that dated slice, not current authorization.
No population-wide assertion or population pilot is claimed.

## RR-1: shutdown-only terminal evidence

Keep `observe_process`, `ProcessSnapshot`'s generic identity semantics and all
lease-owner consumers unchanged. Add a shutdown-specific native observation that
captures selected and complete-census PID, PPID, genuine `lstart`, native process
state and command, with the existing capability witness, output/row bounds,
timeouts, diagnostics and typed unavailable results. Successful parsing of
`<defunct>` does not mean `Z`. Any incomplete, denied, malformed, conflicting or
drifting selected/census evidence is unavailable, not an inferred terminal state.

A terminal exception is eligible only for a non-root PID already retained with a
genuine earlier live full signature, whose native state is `Z`, whose native birth
value matches the birth parsed from that original signature, and whose complete
current PPID chain reaches the exact live root through exact live retained ancestors.
Each ancestor must independently pass the unchanged full-signature observer. Reject
cycles, missing links, changed birth, a reparented child, absent/mismatched root,
unrelated command mismatch, or an unretained already-terminal child. The current
chain is current evidence, not a claim that legacy records saved historical PPIDs.

Legacy records remain usable at the precision they genuinely contain. Native
`lstart` has second-level resolution and observations precede signals, so this is an
observational identity model with TOCTOU exposure, not atomic generation ownership.
Do not invent high-resolution start tokens, prior signal receipts or historical
parent chains. The terminal observation never authorizes signalling that child;
the live parent's unchanged exact-identity authority is separate. If observed
generation ambiguity affects the actual live signal target, refuse. A new sample
may be recorded as a separately timestamped shutdown witness, never overwrite the
original signature or upgrade a historical witness's precision.

## RR-2: bounded ancestry-ordered shutdown

Keep the entry root identity gate and current final quiescence owners. Build a
bounded complete acyclic ancestry graph from a capable snapshot, including generic
intermediates; calculate descendant-before-ancestor order, root last, independent
of numeric PID ordering. Union current owned descendants with all retained identities.
Persist identities before the first signal; retain previously absent identities
through this attempt so final absence covers every retained PID. Do not replace an
original signature with a command observed after exit. A newly seen live descendant
must be coherently exact and durably retained before it becomes a signal target.
An unclassified new descendant or changing graph causes refusal/re-observation
within the fixed budget, not silent omission or an endless retry loop.

Before each SIGTERM, reobserve the exact live target and its rooted ancestry; all
relevant descendants must have actual absence, exact owned live identity or the
RR-1 terminal witness. Reobserve all terminal exceptions used to permit this step.
Skip actually absent processes and eligible zombies. Signal only the independently
exact live owned target. A descendant's `Z` permits progress to its independently
guarded parent without waiting for that child to reap first. It is never marked
absent, removed from retained identities or signalled. Use only SIGTERM with the
existing bounded stop budget (10 seconds, including bounded re-observation/waits);
no group signals and no automatic SIGKILL. Actual owned Popen children may use
their genuine handle; do not introduce `waitpid` for unrelated children.

After a signalled parent exits, a child may disappear or reparent. Reparenting
does not create new signal authority. Wait within the remaining budget for capable
actual absence; while a retained reparented/mismatched child remains, do not use
its earlier terminal witness to authorize further signals. Root absence likewise
does not authorize chasing residual children. Such survivors retain reservation
and produce a visible refusal. A later completely absent family may pass normal
quiescence without signalling. Successful stop requires every retained PID actually
absent in capable observation, closed endpoint, no fixed-project family, complete
registry/domain/capacity evidence and the existing `_assert_quiescent` checks.
Capacity may contain other accounted independent slots; success requires no target
residual/conflict, not a globally empty machine. Never unregister on native `Z`,
closed socket alone, a missing JSON alone, or a partial census.

Record successful this-attempt SIGTERM delivery separately from original identity
evidence; delivery is not proof of termination. A signalled live parent or wrapper
may itself become native `Z` or its surviving descendants may briefly reparent.
Both the signal loop and final wait must permit bounded passive re-observation of
these exit transitions without issuing further signals on weakened identity,
classifying them absent, or dropping reservation. Keep original mismatches visible.
If the whole retained family becomes actually absent, apply final quiescence; if
ambiguity/survivors persist, refuse with the residual intact. Legacy lists provide
no evidence that an earlier invocation delivered any particular signal. These
passive waits do not relax the strict initial root-absent/reparented rules.

## RR-3: explicit stop-only recovery

Proposed internal API, to be implemented only after acceptance:

`Controller.recover_orphan_backend_stop(number, *, expected_root, expected_family,
authorization, expected_residual_sha256=None)`.

`expected_root` and `expected_family` carry exact positive PIDs, full original
signatures and the complete expected PPID graph; bound lengths like existing
records. `authorization` binds explicit operator permission's provenance, configured
backend target, actual lease-owner authority when present, shared physical slot and
the existing driving session identity; it is not a client token or
a new authentication system. Trusted-local process access remains the threat model.
A bare boolean or an arbitrary caller-supplied session string cannot replace the
controller's independently resolved current owner and the recorded approval scope.

The receiving controller is `backend_target`: its canonical inventory owns the
project, backend family/listener and role-qualified process-record path to stop.
Resolve `lease_owner` separately from the actual global lease and the capable
canonical role universe, not from a caller-supplied role override. When a lease
exists, its role must resolve unambiguously to an actual owning controller. For
same-role quarantine that controller is `backend_target`. For a different role,
require the owner's declared directional `paired_inventory()` to identify this
canonical backend target, the same capable shared state-root identity and the same
physical number. Validate the configured paired path and inventory/domain identity;
a role name or common numeric slot alone does not establish a pairing. A FREE slot
has `lease_owner: null`; do not fabricate a lease or owner-gone assertion.

Use `lease_owner._lease_for_command(number, states={"QUARANTINED"})` unchanged,
so role/worktree/client-auth/current owner/state/dependency equality is checked by
the controller that actually owns that lease. Never call the target's role check
on a legitimate different-role lease, weaken role equality, rewrite the lease or
silently treat an arbitrary foreign role as paired. Independently resolve the
current driving session for target authorization and match the owner session through
the owning controller. Keep worktree identity, cleanliness and `_is_absorbed`
containment checks with that owner. Its existing `_assert_paired_dependency` uses
the recorded dependency SHA with `require_primary_match=False`, verifying the
clean target worktree and actual declared dependency path/pin without substituting
a later primary HEAD. Preserve original historical pins. Missing/ambiguous pairing,
wrong state root/number/worktree/pin or competing active resource ownership refuses.

The target controller owns lock order: target `_slot_lock`, then one target
`Supervisor.lifecycle`, both in the verified shared state root. Owning-controller
validation uses unlocked checks inside those locks, not another lifecycle/slot
wrapper. The target invokes a new guarded unlocked recovery helper;
neither layer reacquires the nonreentrant lifecycle lock. No CLI verb is added.
Normal `_stop`, `start`, `prepare`, `reclaim` and `release` must not automatically
enter the orphan-admission route. They preserve residual refusal/reporting.

Admission, repeated under both locks immediately before reservation/signalling:

- Resolve canonical inventory/project/physical number and capable complete role,
  registry, process, endpoint, listener and all-state TCP evidence. Require one
  unique family at the configured project, with exact expected root/family
  signatures and complete ancestry through generic intermediates. Parse actual
  fixed-project/host/port arguments; a substring or mere root PID is insufficient.
  The configured loopback backend listener must be uniquely owned inside that
  family on initial admission, with no competing/foreign listener, second project
  root or opposing active backend/lease ownership conflict. A legitimate same-session
  paired QUARANTINED lease alone is not an opposing resource conflict. Existing
  unrelated accounted slots are
  preserved. Missing required native listener capability is unavailable.
- Require FREE or a matching QUARANTINED lease validated by the actual `lease_owner`
  above; refuse ACTIVE, ACQUIRED, PREPARING, READY_TO_ABSORB, malformed, undeclared
  foreign or mismatched leases. Recheck owner work preservation and declared paired
  target cleanliness/path/pin under the shared locks. For FREE, use the target's
  worktree identity/cleanliness and direct containment in its configured integration
  ref; there is no lease base to fabricate. No dirty or unabsorbed work may be reset,
  released or bypassed.
- Freeze controller dispatch/probes and reconcile completed owned requests under
  ROOT coordination. Passive TCP/thread samples are supplementary; absence of
  established TCP or an idle lease does not prove all handlers completed. Unknown
  external activity blocks admission. These are operator-reviewed drain evidence
  plus fresh observations, not a newly claimed automatic concurrency barrier.
- Initial admission requires a capable absent target process record and no other
  registry ownership of the family. Stale expected identities, observation drift,
  multiple roots, wrong project/port and incomplete evidence refuse before signals.

Reserve only at the existing backend process path. Extend the validated v2 record
with `record_origin: "operator_stop_only"` and a bounded `recovery` object carrying
original expected identities/graph, approval reference and scope, owner session hash,
timestamp and admission evidence. Bind both resolved authorities: target canonical
inventory/domain, role, worktree/project and process path; actual lease-owner
canonical inventory/domain, role, worktree and original dependency pin (or explicit
null for FREE); shared state root and physical number. Approval must cover that
target/owner pair. Keep `phase: "uncertain_residual"`; preserve the
root and descendant signatures as observed before stop. For this origin, reject
`running`, `launch_pending`, `runtime_fingerprint`, launch token or invented launch
command/time fields. No schema-wide reinterpretation of legacy records is needed.
The optional new origin is validated wherever records are read; malformed or unknown
origin is unavailable and reserved. Legacy records without origin retain their
existing meaning, never retroactively become recovery authorizations.

The exclusive publisher must make the complete synced JSON visible atomically and
without replacement, and sync the containing directory before any signal. Existing
`exclusive_json` uses O_EXCL then writes/fsyncs the file; that alone must not be
described as atomically publishing complete content or directory-durable. Minimally
extend shared state publication for this caller (e.g. synced same-directory temporary
file and exclusive hard-link publication with directory fsync), without weakening
lease creation. Denial, unsupported primitives, occupied path or any write/fsync
failure means no signal; any visible incomplete/uncertain record stays reserved.
No fallback overwrite. Recheck file bytes/hash and current gates after publication.

Use RR-1/RR-2 shutdown only after that reservation. Record provenance as stop-only
authority in status; never report `managed`, `running`, `healthy`, a successful
launch or current loaded code from this origin. Its resource state stays residual
or unavailable and capacity remains reserved until actual final quiescence. `_spawn`
and health/prepare/reconciliation readers must not reuse or automatically stop it.
Only the explicit controller API may resume its signals.

A deliberate retry may supply `expected_residual_sha256`. It admits only the exact
existing validated stop-only record, same original target and lease-owner authorities,
driving owner and authorization scope, unchanged original signatures and dependency
pin, and complete fresh applicable admission checks. Re-resolve and validate the
declared pairing, both inventories/worktrees, shared state root and physical number;
target/owner/lease-presence changes are not an authenticated retry. A normal release
occurs after completed recovery, not between retries.
Do not overwrite/restamp an existing managed, foreign, unknown or unmatched record.
On retry, already absent family members or a closed former listener are acceptable
only through capable actual absence and no foreign replacement; remaining live
members/root must match the original identities, and zombie handling remains RR-1.
A missing root with remaining children never grants signal authority. Actual full
absence can discharge the record after normal quiescence. An interruption/failure
retains exact provenance plus bounded error observations and durable reservation;
the expected hash for a later retry must name the actual resulting residual bytes.

## RR-4: completion and controls

Recovery cannot start/reload, alter a lease, reset/cache-copy, commit/build or publish
an epoch. After stopped-resource evidence, ROOT uses the actual lease-owner
controller's normal clean-quarantine release
and the normal current-build/epoch/acquire/prepare/MCP/no-change-release cycle. Each
affected slot needs native diagnostics through its matching attached endpoint,
actual stop/quiescence, reconnect and capacity evidence. Persistent proxy loading
is a separate measured gate; this correction does not imply a proxy restart.

The plan's positive/negative controls and sole-production-mutation/restoration
controls are binding, using production methods over isolated external OS seams and
real disposable record files. In particular, test a genuine native-state transition
to `Z` while command text changes and reaping follows parent SIGTERM; do not mock
the final admission verdict. Preserve generic mismatch, legacy compatibility,
every consumer's reservation and no-signal refusal. Native acceptance is ROOT-only
and separately recorded after source acceptance; no pool restoration or wider gate
acceptance follows from this proposal, its review, or isolated green tests.

Candidate R2 implements the review-required lease-preservation preflight for the
new stop-only origin before acquire/release mutations, with existing slot then
lifecycle locking and relevant same/paired target reads. Original null-owner or
quarantined-owner authorization remains retryable. Legacy managed post-unlink
semantics remain. The combined family budget is 4096 identities, including absent
retained IDs and the root; every persisted record is validated. Rooted ancestry is
reobserved after durable writes, and the final observed target PPID must still agree.
Source execution, whole review and native acceptance remain pending.

R3 selects new-origin provenance before applying recovery-domain and complete record
checks to lease operations. Genuine originless legacy malformed-descendant records
remain for existing strict resource consumers to reject. Explicit origin presence
never means legacy, even for null or false values. Physical-slot recovery protection
uses existing registry observation and role discovery in either pairing direction.
The API shape, ten-second stop budget, original identities and retry pins remain.


### R4: bounded fresh-guard shutdown progress

The accepted R3 source and its bounded controls are distinct from native pool
acceptance. A populated normal release reached the ten-second stop deadline after
one delivered SIGTERM; FREE did not mean backend absence. R4 corrects the source
progress and observation costs; implementation review, ROOT execution and native
normal-release acceptance remain pending.

Keep initial identity/ancestry refusals unchanged. Only after a successful SIGTERM
in this invocation may a temporary exit-related refusal enter bounded passive
re-observation and later resume the pending target. Resumption requires the entire
retained family to satisfy the original classification again, followed by durable
persistence, fresh whole-family state/PPID comparison and the final exact live-target
check. While any required descendant is reparented, mismatched, unqualified terminal
or unavailable, no further signal is authorized. An exact live parent alone does
not bypass its descendants. An eligible native Z remains present and never receives
a signal; actual absence may permit fresh parent progress. Root absence with
survivors never permits chasing them. Delivery receipts contain only this attempt's
successful signals and do not prove termination or historical parent identity.

A shutdown-only family observation may batch bounded generic/native selected and
complete-census commands within one classification. Preserve original full generic
signatures and native PID/PPID/birth/STAT/command. Require capable known-observer
censuses, complete parsing, no extra/duplicate selected rows, selected/census and
cross-format coherence; absence needs all capable views. Generic observe_process
and ordinary readers retain their existing semantics. Never reuse a batch across
a durable write, signal or passive retry. Reject oversized requests/output rather
than truncating; the combined identity bound remains 4096, including absent IDs.

The same absolute ten-second budget includes every observation, persistence and
wait. Retain a bounded first refusal phase/target/typed observations alongside the
last passive observations in timeout diagnostics, without new probes after expiry.
Unregistration still requires actual absence of every retained PID and all existing
endpoint/project/registry/capacity checks. Ownership, exact retry hash, lease/pin/
domain preservation, stop-only provenance and all broader gates are unchanged.

R4 controls use production methods, real isolated JSON and external OS seams:
five/six-PID asynchronous exit chains with a synthetic 0.035-second cost per ps
command (pilot-informed, not a native guarantee), persistent refusal/no-extra-signal
negatives, nested terminal transitions, fresh evidence after persistence/signals,
malformed/denied/partial/duplicate/extra/oversized batches, and first-cause retention.
Preserve all nineteen prior mutation intents and add focused sole-guard controls.
