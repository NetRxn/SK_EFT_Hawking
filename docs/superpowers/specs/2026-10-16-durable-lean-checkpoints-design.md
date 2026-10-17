# Durable nonaccepting Lean checkpoints

Status: source candidate exists; revised crash-recovery specification independently
reviewed and selected for implementation. Whole native pilot and live admission remain open.
Normative proposal: ADR-008 CP-1 through CP-8. Existing accepted behavior remains law
until independent review and the stated activation gates establish a usable route.

## Purpose and unchanged endpoint

Allow a long proof to survive slot reuse and a dependency integration window without
calling an unfinished proof complete. Preserve its entire original contract,
source, failures, evidence and ancestry. Reuse the current controller, its locks,
leases, process registry, owner checks and canonical release/prepare routes.
This feature does not alter mathematical/scientific/build/publication acceptance.

## Measured existing seam

At the design base, `Controller.release` requires clean contained source and does
not accept READY_TO_ABSORB. `_is_absorbed` checks integration/base refs, not arbitrary
preservation refs. `prepare` intentionally resets a safely admitted slot to a
current base. `Inventory.load` chooses explicit configuration and derives roots
from it. `Supervisor` full resource health enforces actual package/launcher SF
coherence; an alternate candidate package cannot use a canonical inventory to
claim healthy launch authority. Existing `_stop_backend_unlocked`, owned-stop
identity guards, `_assert_quiescent` and `capacity_census` are candidate stop-only
implementation seams to verify, not an already usable checkpoint API.

## Transaction data

Extend `scripts/lean_slots/state.py` and the existing controller. A create-only
checkpoint ID owns a versioned journal under the canonical shared state root;
immutable evidence belongs to local storage in its owning repository. Public
records/code contain no downstream-specific paths or identifiers. The journal
refers to the existing lease and registry rather than reserving resources itself.

Bind exact canonical repository and common Git directory, inventory bytes/realpath,
complete physical domain/state root, slot/worktree/branch, owner identity and lease
generation/bytes, base/dependency pins, original and current candidate implementation
source/import manifests, original full contract, sourceReady=false, Git HEAD/tree/
index/content, every evidence reference and original/copied byte hash, request drain
receipts, native process identities/descendants, phases and failures.

Preserve exact HEAD using a create-only `refs/lean-checkpoints/<id>/source` ref in
the owning repository. Ref collision or retargeting refuses. Verify object
reachability and source bytes independently of ref existence. Copy evidence through
exclusive staging, rehash originals and copy, flush files/directories, then publish
an exclusive durable completion receipt. A valid manifest cannot contain missing,
escaped, unsupported nonregular, unreadable or changed inputs. Symlink traversal
must be explicitly bounded to the declared owning evidence roots; uncertainty
refuses. Preserve original evidence and immutable copies after release/resume.

Enumerate nontracked source and ignored material before reset. Every entry needs an
explicit classification: preserved source, preserved evidence, or named regenerable
cache/runtime state that is neither proof evidence nor copied on resume. Unknown
files refuse. A cache exclusion must be demonstrably tied to the existing cache
owner and cannot conceal ignored source or an evidence reference. Measure enumeration
cost and completeness in the isolated pilot; do not substitute a filename guess for
source/evidence preservation. Every preserved source entry must bind actual durable
bytes in the protected WIP tree or a copied source payload, including its path,
type and hash; a nontracked source hash alone refuses. Before checkpoint reset,
same-base restoration or changed-base merge, enumerate/reobserve the destination
and all tracked targets for retained ignored/nontracked file and directory
collisions. Refuse before overwrite, preserving destination-owner bytes and the
checkpoint. Resolve collisions through ordinary source-safe ownership first, never
through automatic removal. No `git clean` or manual lease/ref/pin edits.

## State sequence and failure boundaries

1. ROOT drains the author and creates an ordinary clean source-only WIP commit;
   no task acceptance, ready transition or integration is inferred. Capture the
   complete preservation inputs before granting reset authority.
2. Acquire existing target-slot then lifecycle lock. Validate exact owner, lease
   state/generation, source/manifest, pin and canonical-domain inputs. Persist
   durable intent, ref and evidence completion. Independently completed-client
   receipts must cover the actual owners/endpoints; no request-drain inference
   from locks, process silence, fingerprints or backend absence.
3. Journal and quarantine the existing lease to deny further proxy dispatch.
   Reobserve source and bindings after drain and quarantine. Stop exact known owned
   backend families via RR; keep each signal, birth/signature and descendant receipt.
   Other numbers remain untouched. Unknown occupancy remains reserved.
4. Require actual both-role endpoint/project/retained-child absence and a capable
   complete conflict-free global census. Reverify clean exact source/ref/evidence
   and ordinary containment of the recorded lease base. Only then reset clean
   tracked source to that base, never delete nontracked material.
5. Durably record reset completion and eligibility for canonical release. Drop locks.
   ROOT invokes unchanged canonical release, which independently checks existing
   rules and handles pairing/lease unlink/reconciliation. Persist observed outcome;
   remeasure resources because counterpart restoration can start a backend.

Recovery observes every durable boundary, including partial Git reset/index updates.
Before reset completion, source/ref/evidence are retained and dispatch denied.
After reset before release, exact base cleanliness, preservation integrity and owner
must revalidate. After release, a stale journal cannot change a later lease or owner.
Unknown source/process/durability state remains quarantined/reserved; no optimistic
completion, lease recreation or automatic destructive rollback.

## Crash-safe locking and mutation lifetime (CP-3, CP-6)

Extend `state.directory_lock` and the existing checkpoint Git/evidence mutation
seams through an explicit internal typed CP transaction context, passed only from
validated `CheckpointTransaction` through `Controller._slot_lock` and
`Supervisor.lifecycle`. The context binds the CP operation/generation and admitted
mutation family; purpose strings, ambient globals or a new CLI switch cannot select
the protocol. It is not lifecycle authority and cannot bypass existing ROOT/lease/
domain checks. Ordinary defaults retain the existing legacy directory protocol.
Preserve CP target-slot then lifecycle ordering and the unchanged legacy lock
pathname. A stable permanent sidecar is a mutex, not lease, drain or reset authority.
Open beneath validated held parent dirfds without following links; validate regular
type, owner, mode, single link, device/inode and initialized protocol. Never unlink
or replace the sidecar. Unknown members, substituted parents/inodes and unsupported
filesystem operations refuse. Select Python `fcntl.flock(fd, LOCK_EX | LOCK_NB)`;
contention, unsupported platform/filesystem or uncertain semantics produce a typed
bounded refusal. No blocking acquisition, POSIX record locking or `lockf` substitution.
Reject same-process reentry and exclude concurrent threads at the same guard; never
reuse a held file description as a successful nested acquisition. Fork children
cannot continue the parent's CP transaction, acquire by borrowing its description or
issue LOCK_UN. Default descriptors are noninheritable; only explicitly admitted
mutating exec families retain them. This assumes no shell flock executable and
does not change S-C's existing atomic lease publication.

The current shared primitive's caller boundary is explicit:

| Existing consumer | Protocol in this amendment | Mutation/lifetime boundary |
| --- | --- | --- |
| Numbered controller commands, including ordinary prepare/reset/cache/copy | Existing legacy default | No CP facade or automatic legacy-record retirement. |
| Authoritative build and configured build descendants | Existing legacy default | No inferred Git/lake/helper fd coverage or new recovery claim. |
| Integration/rebase/abort/merge and nested authoritative build | Existing legacy default | Preserve integration→slot→build/lifecycle nesting and ordinary containment. |
| Ordinary supervisor lifecycle, including backend/proxy launch | Existing legacy default | RR/LO identity and quiescence apply; no transaction fd inheritance. |
| CP preserve/recover/observe-release/resume slot and lifecycle scopes | Explicit validated typed CP context | Full prewrite launch, inherited-guard and native completion obligations below, including all nested admitted mutations. |

Every CP lock entry must receive this explicit context; an omitted context is a
production defect, not permission to use legacy locking for a CP phase. Conversely,
ordinary callers must not acquire a recognized CP facade by default. CP treats raw
ordinary/old-canonical records as unknown/reserved, even after holder death. A future
ordinary-caller upgrade requires its own reviewed operation-specific mutator closure
and controls before activation; unproved upgraded families refuse before their first
mutation. No universal lock-order change or generic process manager is introduced.

Prepare a unique same-filesystem holder directory in classified owned staging.
Before publication, write/fsync complete immutable protocol, nonce, holder native
birth/command, sidecar identity, canonical domain/operation, directory/member
identities and applicable lease generation/bytes. Atomically expose it at the old
directory lock pathname with native dirfd-relative NO-REPLACE rename. Darwin
`renameatx_np(RENAME_EXCL)` and Linux `renameat2(RENAME_NOREPLACE)` are the selected
measured primitives. Refuse unsupported symbols/flags/filesystems and EXDEV before
protected effects; no ordinary rename/replace or check-then-rename fallback. An old
caller winning mkdir retains its empty or populated directory unchanged. A new
caller winning publication exposes the complete fsynced holder, never a partial
owner. Preserve unexposed staging after interruption as classified evidence.

Recovery acquires the stable sidecar and checks the exact recognized facade's full
generation/nonce/bytes/device/inodes/domain and the mutator barrier before protected
source inspection or effects. Retire only that facade by atomic NO-REPLACE move to
unique retained history; fsync affected parents. Never owner-unlink followed by
rmdir. Once retired, a new legacy mkdir may win: the retiring operation must never
touch that pathname or perform another protected effect. Preserve retirement intent,
destination identity and generations so a crash after rename cannot replay against
a later owner's facade. Unknown members, changed generations, raw legacy empty or
partial directories and uncertain durability remain reserved. A separately proven
legacy launch fence plus complete native reconciliation is required for attributed
legacy migration; PID absence, sidecar acquisition and manual deletion are insufficient.

The protected interval includes every mutating descendant, even after the Python
holder dies, raises or times out. Bind launch/native identity durably before the
first possible Git/reset/merge/copy/helper write, using a bounded start barrier or
the existing equivalent durable launch pattern. A PID recorded only after Popen
does not close that gap. Explicitly retain guard fds through admitted mutating exec
families, including configured hooks/helpers; parent close must not issue LOCK_UN
on their shared description. Require actual full completion/quiescence before
facade retirement on normal, exception, timeout and recovery paths. A retained
sidecar alone cannot block an unchanged legacy mkdir after premature retirement.
Unbounded or unproved hooks/helpers/daemon configurations refuse before mutation;
the controlled update-ref experiment proves only its exact family. Ordinary backend
and proxy launches use close-on-exec/default descriptor closing and do not keep
transaction guards alive. No new generic process manager is introduced.

After all candidate facades retire and guards drop, ROOT invokes unchanged canonical
release separately. It must still be able to acquire its original mkdir lock.
Neither a permanent directory at that pathname nor a candidate release is permitted.

## Resume

Use fresh canonical acquire/prepare, current exact successful epoch and current
paired dependency pin. No checkpoint transfers lease tokens, sessions, caches or
endpoint authority. Under existing locks, drained clients and owned-stop/quiescence,
first bind the newly acquired lease generation/current bytes and destination
manifest, then durably quarantine it before ANY source mutation. Proxy dispatch
stays denied across restoration, interruption, merge conflicts and recovery. Never
use an unconditional context-manager backend restart on a failed/conflicted tree.
Restore the exact preserved source when the base agrees; otherwise perform an
explicit ancestry-preserving merge into the freshly prepared base. Conflict leaves
both original checkpoint and conflict state intact and blocks proof continuation.
Record exact new tree/HEAD, full old/new manifests and changed review scope.

All old native/MCP/build/scientific observations remain historical on changed
source/dependencies. Revalidate whole required source and original consumers, not
only the most recent helper. Resume never sets sourceReady or drops an obligation.
Use existing canonical lifecycle restoration and supported loaded-runtime admission
before proof dispatch. Verify exact restored source, current epoch/dependency,
known backend and existing pre-dispatch loaded-code/session/tool-policy gates.
No candidate SF bypass or unconditional restart is permitted.

### Pending admission in the existing lease and journal

ACTIVE remains the prerequisite for the matching proof smoke. Publish ACTIVE and
its pending resume-admission context atomically in one existing lease write after
the journal's reactivation intent. A later pending-marker write leaves an unsafe
crash window and is forbidden. The context binds exact checkpoint/journal canonical
identity and domain, current new lease generation and owner, restored source and
matching smoke-file bytes, current epoch/dependency, and this transaction's native
PID/birth/command identity. Reuse existing identity observers and bounded trusted
file readers. Do not add another readiness store, process manager or reservation.

Extend the actual `proxy.py` LeaseGate consumer. For a resume context it validates
the journal/context/generation/owner/domain relationship and completion before
ordinary proof dispatch or leased stream admission. A pending, missing, malformed,
truncated, stale or mismatched context/journal/receipt denies. The original ROOT
lease-owner session remaining alive cannot validate a dead CP attempt. Normal
never-resumed ACTIVE leases keep their ordinary behavior. Existing S-Q discovery,
opaque client session handling and transport cleanup remain compatible; discovery
or DELETE cleanup is not a matching smoke or readiness proof.

Only the internally validated pending transaction may issue its bounded matching
`lean_diagnostic_messages` request through `Supervisor.probe`. Generate a fresh
unguessable per-attempt capability; store only its digest in the same lease/journal
and pass the secret directly through the internal validated transaction/probe
context and an internal proxy header. It is not an operator option or ambient env
variable. Check capability, exact diagnostic name and argument shape/matching file,
current file hash, live attempt identity and all ordinary authentication/role/
owner/pair/source-runtime guards. Refuse batches, other files/tools, arbitrary code,
builds and unexpected/stale capabilities; never fall back to ordinary admission.
The client session ID is transport identity, never this capability. Strip the
internal header before backend forwarding and exclude secrets from logs/errors/
receipts. Do not describe the capability as one-shot unless consumption is actually
enforced. Any needed transport retry or session handshake is bounded to this same
smoke and existing session semantics, with no extra ordinary dispatch authority.

The smoke must retain an actual clean positive proof response, not just a server
or tools/list success: `success=true`, `timed_out=false`, empty diagnostics and
failed dependencies, normal non-error envelope, actual request/response identity
and byte hashes. Missing/error/malformed/timeout responses fail. Bind its receipt
to exact restored file/source, attempt, lease generation, epoch/dependency and
normal loaded-runtime admission. Persist and fsync the completed `resumed` journal
with this receipt FIRST. Then recheck the same live lease/context/source/current
inputs under CP locks and atomically publish completed admission in that lease.
Keep checkpoint/journal/completion-receipt binding rather than removing context.
Ordinary LeaseGate validates that durable completion before dispatch. This attests
to restored source at admission, not perpetual immutability of proof files during
subsequent ordinary authorized editing. Heartbeat and normal lifecycle transitions
preserve the context; they cannot manufacture completion or discard pending state.
If journal state changes for another guarded operation, deny until that operation
establishes its own valid admission or leaves quarantine.

Raised failures quarantine immediately. Actual death before ACTIVE, after ACTIVE,
during smoke, after smoke before journal completion, or after completed journal
before completed lease admission leaves ordinary dispatch denied. Valid completion
allows ordinary calls even if the completed transaction process later exits.
Recovery requires existing recognized CP locks/mutator completion, exact same
new lease generation and current normal source/runtime/epoch/pair gates. Establish
a new attempt/capability and fresh matching proof smoke; never replay the previous
secret, recreate a released lease or alter a later owner's bytes. Unknown state
stays reserved/quarantined. Full source/scientific/build acceptance stays separate.

### Production and native readiness controls

Use actual process death and production HTTP LeaseGate/probe/lease/journal readers,
with the transaction owner distinct from the long-lived ROOT lease owner. Cover
both owner-session states and both configured authentication modes. Test every
boundary above, missing/truncated/replaced journal, mismatched domain/generation/
source or smoke-file hash, stale/dead attempt, wrong capability/file/tool/shape,
batches and attempted capability forwarding/logging. Assert no backend proof
request occurs on denial. Positive controls must demonstrate a live matching
smoke followed by durable completed readiness and ordinary dispatch, unchanged
never-resumed ACTIVE/discovery/session cleanup, recovery success and later-owner
non-replay. Seed each sole production-guard omission and restore exact bytes before
its green control. Include death after completed admission as an allowed control.
Host-modeled transactions plus real HTTP controls are useful source tests, not the
full isolated native A matrix or actual Lean proof acceptance. Complete the original
full native A/B sequence and all original preservation/lock/legacy/SF obligations.

## Shutdown observation and mechanical fixture readiness

ADR-008 R4-S1 through R4-S4 and R4-F1/F2 extend existing observer and fixture
seams without changing CP-1 through CP-8. The shutdown-only single-PID and family
observers enter existing `observation_budget(10.0)` once around the entire invocation,
including all attempts, parsing and usable-result return. Preserve earlier nested
deadlines. At most three total attempts discard only a fully capable R/S-only
same-suffix discrepancy with otherwise exact stable fields and complete graph/
membership coherence. Return usable evidence only from one strict coherent pass;
never combine views, cache across effects, retry another error or adopt a new child.
Typed refusal preserves bounded first/last context without postdeadline probes.
The helper fallback is not a total CP transaction budget.

Selected `ps` rc1 with empty rows remains valid when complete capable censuses
independently witness absence. Selected rc0/nonempty, complete rc0/witness and
mixed present/absent identities retain their original protocol. Empty rc0,
nonempty rc1, census-present target, denied/partial/malformed/extra or other
unexpected result refuses; no inconsistent absence enters scheduler resampling.
Generic readers and exact original final target/identity/graph/absence guards
remain unchanged. Only existing post-first-SIGTERM exit/reaping continuation is
permitted; observation resampling grants no signal authority.

The positive mechanical peer waits for exact owned generation-bound recursive
middle/leaf startup before binding its listener. Validate actual PID/birth/argv/
PPID chain; stale historical rows or port readiness do not establish it. Bound
startup, preserve descriptor policy and fail without product-command retries.
Keep a separate deliberately late real descendant after durable graph reservation,
proving strict refusal and zero signals to that new family with reservation retained.
The ordinary absorb route must cover internal rewarm then immediate counterpart
restoration. Source and fixture changes invalidate affected historical gates.


#### R4-F1-A: exclusive complete startup acknowledgment

The standalone mechanical peer serializes its complete bounded startup object
before publication. Hold the exact trusted control directory through a no-follow,
close-on-exec directory descriptor; require current ownership and no group/other
write, and recheck its pathname identity at readiness boundaries. Create a unique
same-directory private stage with exclusive/no-follow/close-on-exec flags and mode
0600. This invocation exposes no final entry before publishing its complete stage.
An initially absent final remains absent during uncontended staging. A preexisting
final or a concurrently published complete winner remains untouched; this invocation
then collides with FileExistsError, without deleting, replacing, adopting or retrying
invalid data from the existing object. Admit only
complete bounded writes, an fsynced regular single-link private inode with exact
size and stable identity, and an unexpired original deadline without cancellation.

Publish by dirfd-relative native NO-REPLACE rename, preserving collision as
FileExistsError and leaving any existing final object unchanged. Use the existing
platform/ABI pattern without importing controller code: Linux renameat2 flag1,
Darwin host-unit renameatx_np flag4. Actual support must be established on the ACK
bind mount in the selected image and the host-unit filesystem before reliance.
Unsupported APIs/filesystems, cross-device moves, permission or durability errors
fail startup; no overwrite, check-then-rename, hard-link publication or retry of
invalid data is permitted. Stage and final remain on one directory/device. The
completed published inode remains single-link and is never modified afterward.
Fsync the held parent before the publisher continues. Atomic content visibility
alone does not prove parent-fsync completion, publisher survival or power-loss
recovery. Deadline checks do not preempt uninterruptible filesystem operations.

A prepublication error removes only this invocation's exactly identified staged
inode, or retains that private stage as failure evidence. Never remove another
stage or an existing final path. A postpublication failure preserves the complete
final acknowledgment, even when parent fsync or later readiness fails.

Readers use held trusted directory authority and no-follow/close-on-exec/nonblocking
open. Require a regular single-link file, exact private mode/current UID and bounded
stable size. Bound reads to maximum+1, require complete bytes equal to stable size,
and compare inode/device/owner/mode/link count/size/mtime/ctime and directory-entry
identity across acquisition/read. Reject FIFO, symlink, directory, oversized,
short/growing/truncated data or substitution. Missing final name at initial open
alone means not yet published. Missing/substituted entry or parent after acquisition
is fatal consistency failure, including ENOENT; never turn it into another wait.
Strict JSON/UTF-8/object validation and postparse deadline checks remain fatal on
failure. No malformed-data or trust-error retry is added.

Keep one absolute startup deadline through normal root/middle/leaf and every
publication/read/identity/ready boundary. The waiter retries only initial missing
final-name acquisition. After acknowledgment checks, recheck cancellation, the
exact created child's poll/native PID/birth/start ticks/full argv/PPID, and deadline
before return. Revalidate the full required owned recursive family before own
readiness publication and root listener bind. These are fresh boundary checks,
not a guarantee that a process cannot subsequently exit. Keep the existing distinct
late-child negative's separately bounded leaf-start interval; never respawn or
retry a product command to repair startup.

One narrow owned-child finally covers publication/read failure, cancellation,
missing root token/port, listener construction, serving exit and late-child wait
failure. Terminate/wait only the unreaped exact direct-child Popen handle created
by this fixture. Preserve the existing finite cleanup wait and any cleanup timeout
as uncertainty; no guessed PID, nonchild signal, controller cleanup or inherited
transaction descriptor is authorized. Existing server/thread cleanup stays owned.

All original CP-1 through CP-8, R4-S1 through S4/F1/F2, selected-ps absence,
identity/ancestry/graph/new-descendant/final-target/every-PID-absence, quarantine,
lease/pin/owner/provenance/capacity, client auth/session and A-before-B-before-live
contracts remain unchanged. This amendment repairs the mechanical peer only.

## Candidate stop-only bootstrap

CP-8 is needed only to break the source-installation dependency cycle. The ROOT
session stays the non-worktree orchestrator. It invokes exact reviewed candidate
code with an explicit pinned canonical inventory/domain while canonical primaries
remain unchanged. Bind candidate commit plus complete imported bytes and the
unchanged canonical implementation; refuse modified source or ambient overrides.
Validate those bindings BEFORE Controller construction or state-directory creation.
The selected transaction may preserve, journal/quarantine, stop exact known owned
families, observe and reset fully preserved clean source. It cannot invoke candidate
health as authority, suppress SF, rewrite runtime metadata to appear fresh, start or
reload any process, release, prepare, build or absorb. Canonical release runs in its
own command after locks are dropped. Normal integrated code owns later resume.

Establish native pilot evidence in separate phases, before any real lease uses CP:

1. In a new isolated OS/process/network domain, install the exact candidate as
   ordinary canonical code with local temporary Git repositories, paired inventory,
   state, transparent launchers, real controlled MCP peers and native descendants.
   Run the whole preserve/recover/separate canonical release/acquire/prepare/resume
   and crash matrix through production readers. This ordinary route needs no CP-8
   prior-pilot claim. Independent acceptance binds its exact source and domain.
2. In a separate isolated domain, exercise the old canonical code plus the exact
   reviewed candidate's CP-8 bridge. Bind accepted phase-one receipts, exact phase,
   candidate and canonical source, inventories and domain before constructor/state
   effects. Test unchanged old canonical release separately. Candidate
   health/start/release/prepare remain forbidden. No false prior-pilot boolean or
   generic skip-pilot/disposable flag can authorize the live canonical domain.
3. Only after both full pilots and independent review pass may ROOT separately
   admit live preservation one physical number at a time. Ordinary integration,
   LO/SF loaded-code admission, current builds/epochs and fresh proof resumption
   remain later gates. A controlled MCP peer is not Lean or mathematical acceptance.

Both isolated phases must use actual CLI/import/Git/evidence readers and native
owned backend/descendants, client completion, collision refusal,
interruption/recovery and canonical release. Separate host directories/ports alone
do not isolate the host-global capacity census. Do not filter foreign live processes
or weaken observer completeness to make the pilot pass.

Prove the isolated route
using actual CLI/import/Git/evidence readers and native owned backend/descendants,
client completion, collision refusal, interruption/recovery and canonical release.
Review must resolve whether the stop-only seam is complete without hidden calls to
SF-dependent launch/health paths. Specifically forbid process_state, paused_backend,
activating_from and _assert_backend_owned_or_stopped in the candidate transaction:
they reach SF health or automatic starts. Call only the validated low-level owned
stop/quiescence/census route under existing locks. Failure preserves the original
source window.

## Verification and acceptance

Test production Controller transactions against actual temporary Git repositories,
worktrees, canonical inventories and byte manifests. Cover dirty/staged/untracked/
ignored evidence, missing references, symlink/denied reads, ref collision/drift,
owner/pin/domain drift, concurrent changes and source-only no-acceptance behavior.
Inject failure after every durable phase and assert no lost source/evidence, no
reset before protection, no stale replay over later owners and retained reservations.
Include actual child process death (not only raised exceptions) at holder staging,
publication, retirement, journal/ref/copy/fsync/quarantine/stop/reset/index,
release/resume/conflict and smoke boundaries. Demonstrate successful recognized
recovery as well as reserved uncertainty, then a later owner with no stale replay.
Cover legacy mkdir versus publication/retirement, empty/nonempty collisions,
generation/inode/member substitution, native unsupported/permission/EXDEV refusal,
mutators surviving death/timeout/exception, lost inheritance and premature retirement.
Verify explicit CP-context propagation through both lock scopes, ordinary default
legacy behavior, reentry/thread/fork refusal and unchanged ordinary successful
release/acquire/prepare/build/absorb. Sole missing-CP-context and accidental ordinary
protocol-activation mutants must be red; CP cannot reclaim any legacy caller's record.
Seed sole mutants in actual production readers, including a removed native
NO-REPLACE guard, split owner-unlink retirement and omitted mutator barrier. Native
primitive experiments and a safe-reservation-only run do not complete this matrix.
Exercise actual RR native-observer seams and both-role/global capacity refusal.

Bootstrap tests must reach the actual production candidate route: wrong/default/
copied inventory, override, candidate/import drift and wrong owner refuse before
effects; canonical SF start/health mismatch remains a refusal. Check unchanged
ordinary release/acquire/prepare/absorb behavior. Test same-base restoration and
changed-base merge/conflict with fresh epochs and original full obligations. Reach
the actual proxy lease reader during paused resume before/after restoration and
conflicts to prove denial. Real temporary Git cases must contain ignored/untracked
source distinct from evidence, omitted copied source and file/directory collisions
introduced by both recorded/current target trees. Assert immutable checkpoint and
current destination-owner bytes survive every refusal and crash.

Independent sole production mutants must expose omitted file classification,
hash/reobservation/durability/ref barriers, dirty reset, missing drain/quiescence,
rescue-ref containment bypass, SF/source-identity bypass, unknown-process signal,
stale-generation replay, omitted resume quarantine/reactivation guards, source bytes
represented only by a hash, destination-collision omission and carried-forward
acceptance. Restore bytes and verify
green after each. Retain existing required runner tests, broader fast gates,
independent source review, closure and normal reviewed main delivery. Source/unit
success is distinct from isolated pilot, live bootstrap, current builds and resume.
