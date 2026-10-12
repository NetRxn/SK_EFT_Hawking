# Owned Lean shutdown and orphan recovery plan

Status: **design accepted; candidate source implemented, verification pending.**
Whole independent design review and ROOT intake accepted the contract. Source
controls and mutation mappings are present; ROOT execution and whole implementation
review remain pending. Owner: primary controller lead. Findings:
[RR1/RR2](../../../papers/AutomatedReviews/2026-10-12-lean-runner-recovery/source.md).
Contract: [design](../specs/2026-10-12-owned-lean-shutdown-and-orphan-recovery-design.md),
[ADR-008 RR-1–RR-4](../../adrs/ADR-008-shared-lean-slot-control-plane.md#owned-shutdown-and-operator-authorized-orphan-recovery).

## Global constraints and order

Use the existing remediation planner and closure writer; this plan is not another
routing or execution ledger. ROOT owns notebook, integration, native operations,
builds, caches, leases and gates. Keep one writer per assigned candidate. The
author edits only its implementation packet's files and performs static AST checks;
ROOT alone executes tests, native probes, signals and lifecycle commands. No scientific source, proof,
apex, publication or broad project acceptance is in scope.

1. Independently review the complete ADR, guide, design, plan and findings against
   current source and original operator scope. Review the actual dated native slice
   without reclassifying it as a current census. No population-shape pilot is
   required because no population assertion is made. Resolve every design finding
   and record explicit ROOT acceptance before code or test execution.
2. Implement one coherent bounded correction in the existing state/supervisor/
   controller owners and existing test modules. Keep recovery admission and all
   record consumers together; an origin tag without protected readers is incomplete.
   Establish the controls below before native use. Preserve public/private isolation.
3. Independently review complete implementation, negative controls and meaningful
   production mutations, then let ROOT integrate exact reviewed bytes. Existing
   gates and finding closure retain their owners and acceptance scopes.
4. ROOT performs separately admitted native recovery using fresh evidence. Record
   each actual pool cycle and residuals; do not turn an earlier successful build,
   tool response or FREE lease into current stopped-resource evidence.

## File-to-task map

| Owner surface | Work after design acceptance |
|---|---|
| `scripts/lean_slots/state.py` | Bounded shutdown-only native-state observations; preserve generic observer semantics; minimally extend exclusive complete/durable process-record publication without weakening lease writers. |
| `scripts/lean_slots/supervisor.py` | Ancestry-ordered guarded stop; terminal/passive exit handling; strict optional recovery-origin validation across status/capacity/stop/start/health/quiescence; guarded unlocked orphan-stop helper using existing registry. |
| `scripts/lean_slots/controller.py` | Explicit target-controller `recover_orphan_backend_stop` API; resolve actual lease owner through canonical declared pairing, preserving each controller's unchanged role/owner/work/pin checks; target-slot then one shared lifecycle lock; both-authority authorization and exact-residual retry. No automatic callers or lease rewrite. |
| `tests/test_lean_lifecycle_observation.py` | Extend external host seams for native state, listener ownership, graph transitions, publication failures and receipts; exercise production methods and real temporary records. |
| `tests/test_lean_slots.py`, `tests/test_codex_lean_slot_policy.py`, `tests/test_architecture_claims.py` | Existing lifecycle/policy regressions plus binding authority/proposed-to-implemented wording where materially changed. No invented targeted CLI. |
| ADR-008, operator guide, this spec/plan and RR source finding | Keep semantics and actual acceptance status synchronized before implementation ships. ROOT alone writes closure through `scripts/close_finding.py`. |

`scripts/lean_slots/cli.py` needs no new command or action. Verify its unchanged
global start/stop/status rejection of `--slot` and existing scoped probe behavior.
If implementation requires another path or changes this API/contract, return the
complete revised proposal for review before expanding ownership.

## Binding isolated controls

Implement the named test families below in `tests/test_lean_lifecycle_observation.py`.
Each exercises production code with only external OS boundaries simulated and
independently populated native rows, listeners and on-disk records. Assert attempted
signals/launches/writes/unlinks/cache changes, durable original signatures, typed
diagnostics and capacity outcomes; never patch the admission or quiescence verdict.
Tests must have populated positive controls so refusal is not vacuous.

| Future test family | Positive control and required negative controls |
|---|---|
| `test_rr1_generic_identity_unchanged` | Same live identity and capable absence retain existing behavior; changed command on native Z stays generic mismatch. Denied, malformed, selected/census disagreement stay unavailable. |
| `test_rr1_retained_zombie_parent_progress` | Genuine retained live child becomes native Z with same birth under exact live parent/root; only live parent/root receive SIGTERM and records clear only after actual absence. Child command text changes; include a legacy record with no historical PPID/signal receipt. |
| `test_rr1_terminal_evidence_refusal` | Reject non-Z `<defunct>`, missing state, changed birth, unsupported/ambiguous birth, unretained Z, wrong/missing root, unknown ancestor, reparenting, cycle, denied/partial state or selected/census drift. No new signal based on these states. |
| `test_rr1_ancestry_order` | Use a deep generic-intermediate tree with PID numbers deliberately opposite creation/topological order; assert child-before-parent/root-last. New drifting descendant, incomplete graph and unknown command cause refusal before an unsafe next signal. |
| `test_rr1_exit_wait` | Actual signalled parent/root becomes Z or descendants reparent briefly, then all disappear: bounded passive observation succeeds only after absence. Persistent Z/reparenting, mismatch and timeout retain record/capacity. No zombie/nonchild waitpid/SIGKILL or additional signal under weakened identity; delivery receipt never proves exit. |
| `test_rr1_absent_root_and_quiescence` | Every retained PID actually absent plus complete quiescence clears record. Root absent with surviving generic/reparented child, live project descendant, port/listener, unknown registry or incomplete capacity retains it. Preserve existing root-absent refusal behavior. |
| `test_rr2_unique_family_stop_only` | FREE clean-contained and same-role same-session clean-contained QUARANTINED cases each admit one exact family; configured listener belongs to it; no lease/cache/epoch/proxy change. Real record exists durably before first signal and is removed only after complete absence/quiescence. |
| `test_rr2_paired_lease_authority` | Populated generic public target orphan with same-session QUARANTINED declared downstream lease owner, same state root/physical number and valid recorded dependency pin: owning controller's unchanged role/owner/work checks pass, target checks select only the public family/listener/process path. Preserve exact lease and both worktree bytes; leave normal release to actual owner. Reject unpaired/undeclared foreign role, wrong session, ACTIVE/transitional owner, wrong state root/number/worktree, ambiguous pairing, invalid dependency path/pin, dirty/unabsorbed work, opposing active backend and retry changes of target/owner/pair/pin. Assert no signal or competing record write on refusals. |
| `test_rr2_authority_and_work_refusal` | Missing/wrong-scope authorization, mismatched current session/role/worktree, every disallowed lease state, dirty or unabsorbed work, unavailable containment and undeclared active requests refuse before reservation/signals. Existing approved scope needs no repeated human prompt. |
| `test_rr2_family_and_listener_refusal` | Reject stale expected root/child, omitted/extra member, independent second root under generic manager, wrong project/host/port, duplicate or foreign listener, cross-role conflict, incomplete/denied/drifting census or TCP evidence. Unrelated accounted slots remain untouched. |
| `test_rr2_exclusive_durable_reservation` | Inspect actual record bytes at first signal and complete publication behavior; inject occupied path, O_EXCL/publication collision, write/flush/file-fsync/directory-fsync failure and interruption. No signal before successful complete durable publication; preserve any visible residual, never overwrite a competitor. |
| `test_rr2_record_consumers` | Recovery origin always residual/reserved, with explicit stop-only provenance in status. Test `running`/pending/fingerprint/token/unknown-origin corruptions against status, capacity, normal stop/start, health, prepare and reconciliation; none claims healthy reuse or performs automatic recovery. Legacy shapes still work. |
| `test_rr2_exact_residual_retry` | Exact current hash, same original target/lease-owner authorities, approval/session/pair/pin, fresh identities and work/drain gates allow retry; absent former members/listener require actual absence and no replacement. Wrong hash/owner/scope, changed target/lease owner/state root/number/pin, managed/foreign/unmatched record and restamped signature refuse without overwrite. Root absent with surviving children never grants signals. |
| `test_rr2_lock_and_no_lifecycle_expansion` | Production entry takes target lock before lifecycle exactly once and uses unlocked helper; lock contention refuses safely. Assert no launch/reload, lease removal, cache operation or epoch publication; existing global CLI behavior unchanged. |

## Meaningful mutation and restoration

For each guard below ROOT runs a sole production-code mutation against its named
control, retains original and mutant bytes/output, verifies the control fails for
the asserted unsafe effect, restores exact original bytes, and reruns the control
green. A test-only assertion mutation, exception unrelated to the defect or several
simultaneous mutants is not evidence. Required guard mutations: classify `Z` as
absence; trust `<defunct>` without native state; signal a zombie; overwrite retained
signature; restore reversed numeric order; unregister before every-PID/project
quiescence; remove owner/clean/lease gate; skip listener/family uniqueness; signal
before durable reservation; allow recovery-origin healthy reuse; accept wrong retry
hash; allow ordinary stop to resume recovery; and remove the pairing/owner-routing
guard so an undeclared foreign owner reaches target recovery. The dedicated paired
positive must remain admitted and that foreign-owner negative must fail its native
assertion under this sole production mutant, then pass after exact restoration.
Each maps to the corresponding
named row above. Preserve generic observer/regression baselines across the campaign.

## Exact future verification and acceptance

ROOT first runs the candidate controls using the canonical primary interpreter's
absolute path and candidate working directory. After accepted integration, the
following exact commands run from the canonical primary. They are future requirements,
not executed evidence from the proposal author. The named RR controls must actually
exist and be collected; zero selected tests is not a pass.

```text
.venv/bin/python -m pytest tests/test_lean_lifecycle_observation.py -q -k 'rr1 or rr2'
.venv/bin/python -m pytest tests/test_lean_lifecycle_observation.py tests/test_lean_slots.py tests/test_codex_lean_slot_policy.py tests/test_architecture_claims.py -q
git diff --check
```

ROOT also runs the required broader fast suite and validation before publication,
records actual existing failures without waivers, and uses the existing finding
writer after scoped evidence is independently accepted. This plan adds no validation
registry entry or new validation check. If implementation adds a check, run the
architecture-change registration-site procedure and meet every derived registration
obligation plus a production-artifact seeded red/green control.

Native acceptance, separately authorized and ROOT-only: (a) fresh managed residual
stop with retained terminal child, capable every-PID absence and no lost source;
(b) fresh stop-only admission and recovery of each affected orphan family, including
public backend target with its actual same-session declared downstream QUARANTINED
lease owner, exact both-authority/pair/pin reservation/error evidence and preserved
lease and both worktree bytes; (c) actual lease-owner controller's normal release
after clean containment, current authoritative build/epoch, normal
acquire/prepare to ACTIVE, matching attached native Lean diagnostics, normal
no-change release, actual backend/family absence and complete capacity; (d) reconnect
and repeat eligibility through the persistent front door, with current loading
evidence if that front door required a separately admitted replacement. Keep all
original witnesses and refusal evidence. Any residual means that slot is not restored.
Source acceptance, normal operational recovery and full wave completion are distinct.
Do not reclaim a live owner's quarantine or assert owner-gone. The confirmed same
session uses normal no-change release after recovery. Unchanged endpoint URLs and
a new healthy lease do not require configuration render or client restart.

Document verification also binds the whole unchanged accepted SF closing text in
ADR and guide before each RR heading. SF source/native statuses must not
appear under the RR section. Preserve frozen prior author/review reports; each
revision reports original-to-current and prior-to-current complete diffs and pins.

R2 adds production controls for genuine original same-role/paired quarantine lease
preservation and FREE acquisition refusal, followed by original-authority retry;
legacy managed warning behavior; late final PPID drift; at/over combined family
budget with absent retained IDs; publication write/flush/interruption; partial/all-
absent retry; and actual slot/lifecycle lock contention. The original fourteen
control families and thirteen mutations remain binding. Additional sole lifecycle,
final-parent and shared identity-bound mutations require independently asserted
effects and exact restoration. ROOT alone executes these controls.

R3 reconciles all 25 actual four-module failures across six groups without accepting
unsafe effects: narrow legacy preflight selection, post-SIGTERM diagnostic evidence,
real leased-policy JSON/reload, acquisition before deliberate provenance denial, and
real Supervisor subclasses preserving lifecycle/preflight methods. New controls
cover explicit malformed origins and reverse paired FREE reservations. All original
20 families and 17 mutation intents remain, with additional focused provenance and
reverse-reservation mutants. Actual execution and whole review remain ROOT-owned.
