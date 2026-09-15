# ADR-018 — distinct Chat client for shared Lean slots: implementation plan

**Status:** specification accepted at PR #75 head `469e4e47607b7d74da0b9b3c81dc56d04c3dd24f` / COMMENT `5202241729`; author implementation is in progress on PR #76. The implementation review at `42803dfc2baa5e5a26b152557e0c7e0d8c9504aa` returned `ACCEPT_WITH_CHANGES`; current-document reconciliation, applicable mechanical verification, and a fresh exact-head independent implementation re-review are pending before Gate A.

**Design:** [`2026-09-14-adr018-chat-slot-client-design.md`](../specs/2026-09-14-adr018-chat-slot-client-design.md)

**ADR:** [`ADR-018`](../../adrs/ADR-018-chat-client-for-shared-lean-slots.md)

**Measured public base:** `codex/memory-process-clocks` @ `9ea7b61a33e91190ffe99e843247e03a51e8fb3e`.

**Measured private/downstream state:** `NetRxn-RD` `codex/frontier-first-deliverables` @ `47b380f6e233a0fd70662640422b3652e6d3191a`; schema-1 private inventory, no `allowed_clients`, shared public controller.

## Global constraints

- ADR-008 remains the slot lifecycle/build/integration authority.
- The specification gate is closed at `469e4e47607b7d74da0b9b3c81dc56d04c3dd24f`; author implementation may proceed, but do not call the implementation accepted until applicable mechanical evidence and exact-head independent implementation re-review are satisfactory.
- Do not add a second slot/worktree/backend/proxy/integration mechanism.
- `chat` is a distinct client identity; never impersonate `claude` or `codex`.
- Inventory owns lease/dispatch admission; renderer capability is a separate explicit interface.
- Schema-1 missing `allowed_clients` means exactly Codex/Claude, never Chat; any present value must pass the declared roster validation and explicit JSON `null` is invalid.
- Roster removal is quiescent + restart-bound; a file edit is not immediate revocation.
- One opaque `LEAN_SLOT_OWNER_SESSION` remains the lifecycle owner; no implicit ownership transfer at `ready`.
- No worker-side `lean_build`, direct slot push, merge, publication, deployment, or automatic repair/discard.
- Preserve paired public/private dependency invariants.
- Live no-mutation production-bridge acceptance precedes any source-mutating Chat task.
- A real source-mutating task is blocked until heartbeat, disposable mutation-path evidence, and reviewed `ready → absorb` owner continuity exist.

## Phase 0 — independent design review and reconciliation

### Task 0.1 — first fresh-reader adversarial review — COMPLETE

PR #75 received a durable GitHub COMMENT review against head `332f44f5e4ba557ae1d119a55018aa51fd923ce8` with verdict `ACCEPT_WITH_CHANGES`.

Blocking findings:

- B1 removal/revocation + stale proxy/token semantics;
- B2 lifecycle owner/heartbeat/ready→absorb continuity;
- B3 private/downstream migration;
- B4 renderer capability boundary;
- B5 production-bridge acceptance non-vacuity;
- B6 mandatory ADR-008/operator-guide reconciliation.

### Task 0.2 — reconcile first review — COMPLETE IN SPECIFICATION

Reconciled dispositions:

- B1 → ADR D8 / spec S18-9: quiesce + removal preflight, bearer token revocation while still admitted, roster edit, supervisor restart, verify;
- B2 → ADR D5/D11 / spec S18-5/S18-10/S18-12: one durable owner session, heartbeat before mutation, no implicit transfer or bridge integration authority;
- B3 → ADR D9 / spec S18-8: measured private schema-1 overlay; exact missing-field fallback `{codex, claude}` only;
- B4 → ADR D6/D10 / spec S18-4/S18-6/S18-11: admission and renderer capability remain distinct; Chat renderer rejected;
- B5 → ADR D11 / spec S18-12: Gate A uses production bridge end-to-end; disposable mutation path before real source;
- B6 → ADR D12 / spec S18-13: ADR-008 + operator guide reconciliation mandatory in shipping commit.

### Task 0.3 — focused fresh-reader specification re-review — COMPLETE

The review chain continued through focused and residual B1 passes. Final canonical-consistency COMMENT review `5202241729` at exact PR #75 head `469e4e47607b7d74da0b9b3c81dc56d04c3dd24f` returned **`ACCEPT`**, residual B1 `CLOSED`, with no B2–B6 regression.

That result closes the specification gate at its exact head. It does not accept later implementation heads, replace mechanical verification, authorize Gate A, or waive independent implementation review.

## Phase 1 — make admission versioned data

### Task 1.1 — inventory property and schema-1 compatibility

**Files**

- `config/lean-slots.public.json`
- `scripts/lean_slots/state.py`
- `tests/test_lean_slots.py`

**Change**

- add `server.allowed_clients = ["codex", "claude", "chat"]` to public inventory;
- add `Inventory.allowed_clients` validation/projection;
- safe grammar consistent with existing token-file naming;
- validate non-empty + unique;
- for schema 1 only, missing field returns exactly `{codex, claude}`;
- every present value, including JSON `null`, reaches declared roster validation rather than compatibility fallback;
- never infer Chat from a missing field.

**Tests**

- explicit three-client public inventory loads;
- empty/duplicate/malformed fail;
- present non-array values including explicit null fail;
- schema-1 missing field is exactly Codex/Claude;
- active private-style schema-1 paired fixture remains loadable and does not admit Chat.

### Task 1.2 — client removal/restart semantics

**Files**

- `scripts/lean_slots/state.py`
- supervisor/proxy tests in `tests/test_lean_slots.py`
- operator docs in Phase 3

**Change/test**

- no new instant-revocation mechanism;
- test stale running proxy retains its loaded policy after only a file edit;
- stale fingerprint/state is detectable;
- restart loads the new roster;
- post-restart controller/proxy deny the removed identity;
- active lease for the client makes the removal procedure invalid until quiesced;
- bearer token is revoked while the client is still admitted, before the roster edit, and later re-add does not silently reuse the old credential.

## Phase 2 — enforce admission at project boundaries without confusing renderer support

### Task 2.1 — controller admission

**Files**

- `scripts/lean_slots/controller.py`
- `tests/test_lean_slots.py`

**Change**

- validate client in `Controller.acquire()` before lease creation/mutation;
- validate client in `session_environment()` before token/environment behavior;
- keep generic lease record shape;
- if touched, change product-specific `Codex session owner mismatch` diagnostic to neutral `session owner mismatch`.

**Non-vacuity**

Programmatic unadmitted `Controller.acquire(... client="other" ...)` fails and leaves no lease artifact.

### Task 2.2 — proxy admission

**Files**

- `scripts/lean_slots/proxy.py`
- `tests/test_lean_slots.py`

**Change**

- trusted-local identification consumes loaded `Inventory.allowed_clients`;
- bearer mode rejects clients absent from loaded admission even if a token file exists.

**Tests**

- Chat discovery under admitted inventory;
- unknown client reject;
- no-lease dispatch reject;
- Chat lease/Chat hint pass;
- Chat lease/Claude hint reject;
- Claude lease/Chat hint reject;
- bearer hint/token mismatch reject;
- removed-client token alone cannot admit client.

### Task 2.3 — admission CLI delegates; renderer CLI stays exhaustive

**Files**

- `scripts/lean_slots/cli.py`
- `tests/test_lean_slots.py`

**Change**

- remove `codex|claude` parser choices from `acquire --client` and `session env --client` only;
- controller/inventory supplies the authoritative admission failure;
- preserve an explicit renderer capability set for `config render --client`;
- replace any catch-all Codex renderer branch with exhaustive named dispatch.

**Tests**

- `acquire/session --client other` parses then fails through project admission without creating state;
- `config render --client chat` fails and writes nothing;
- unknown renderer fails explicitly;
- Codex/Claude renderers remain positive controls.

## Phase 3 — mandatory documentation reconciliation

### Task 3.1 — reconcile ADR-008 client enumeration

**Files**

- `docs/adrs/ADR-008-shared-lean-slot-control-plane.md`

**Change**

- preserve all ADR-008 lifecycle/build/integration decisions;
- amend S-A/S-C and any other load-bearing client enumeration that becomes false;
- point admitted-client identity to versioned inventory rather than re-listing a hand-maintained runtime roster where avoidable.

### Task 3.2 — operator guide client-neutral/removal/owner procedure

**Files**

- `docs/dev-loops/LEAN_SLOT_OPERATOR_GUIDE.md`

Document:

- admitted clients derive from versioned inventory;
- Chat uses product-neutral `LEAN_SLOT_OWNER_SESSION`;
- bridge connects to the selected proxy with `?client=chat`;
- no Chat-specific workspace renderer exists;
- connection does not grant a lease;
- canonical removal is `quiesce + removal-preflight → bearer revoke-token while still admitted → roster edit → supervisor restart → doctor/controller/proxy denial verification`;
- `ready` does not transfer lease ownership.

### Task 3.3 — architecture claims/registration

Run the repository architecture-change registration/claim checks and update every document the implementation makes wrong in the same shipping commit. Do not add hand-maintained counts.

## Phase 4 — mechanical verification

Run project-native relevant tests/checks, including:

- targeted and applicable full Python tests;
- schema/mixed-version public-private tests;
- trusted-local and bearer admission tests;
- stale-running-proxy/restart removal tests;
- renderer negative/positive tests;
- cross-process owner-session tests;
- existing worktree/epoch/quarantine/paired-dependency/ready/absorb regressions;
- architecture/document checks and registration-site probe;
- `slotctl doctor` read-only checks after required supervisor restart.

No live Chat MCP dispatch yet.

At the current author-document checkpoint these commands are **NOT_MEASURED**; the repository has no `.github/workflows/` runner. Exact feasible commands and environment requirements are recorded in the post-audit document-reconciliation status rather than promoted to PASS by source inspection.

## Phase 5 — independent implementation review

Separate from the specification reviewer and implementer where practical.

Review questions:

- is inventory genuinely the only lease/dispatch roster?
- can any programmatic path create an unadmitted lease?
- are stale-proxy and removal semantics actually enforced as specified?
- can stale bearer credentials restore authority unexpectedly?
- did renderer capability remain distinct from admission?
- did Codex/Claude behavior drift?
- did any path expand worker/build/integration authority?
- do mixed-version private/public tests match the measured private overlay?
- are tests production-shaped rather than helper-only?
- are ADR-008/operator docs now true?
- does explicit JSON null fail closed rather than selecting schema-1 missing-field compatibility, with neighboring malformed and valid positive controls?

Blocking findings are fixed and re-reviewed before live acceptance.

## Phase 6 — bounded no-mutation **production bridge** acceptance

**Only after implementation, applicable mechanical verification, and independent implementation review are satisfactory.**

Use one clean/free slot and the actual WP-010 bridge path:

1. create durable bridge preflight from exact admitted task/ref/SHA;
2. bridge `activate()` performs non-repairing probe + project-native Chat acquire + prepare;
3. independently observe lease/worktree/endpoint state;
4. bridge calls only task-allowlisted diagnostics/`lean_verify`;
5. mismatched client identity fails against that same lease;
6. `lean_build` absent/denied;
7. verify HEAD unchanged and `git status --porcelain` empty, including untracked files;
8. bridge `release_no_change()`;
9. capture exact structured evidence.

Do not substitute manual `slotctl acquire/prepare/release` for bridge calls. Manual commands may independently observe/debug only.

Gate A remains bounded below the 900-second lease timeout with the existing two-minute safety margin; it does not claim to validate heartbeat.

## Phase 6.5 — mutation/continuation prerequisite

Before any real source-mutating Chat task:

### Caller/control-plane work

- implement project-native heartbeat on the WP-010 adapter/service/MCP bridge using the same durable session ID;
- unit-test that the same session identity is supplied across activate/heartbeat/ready/release;
- use a disposable production-shaped repository/slot fixture to exercise scoped write → normal-hook checkpoint commit → ready;
- retain fail-closed owned-path/unowned-dirty-file checks.

### Integration continuation design/evidence

- define the explicitly authorized lead/integration operation that continues `READY_TO_ABSORB → absorb` using the same durable owner session;
- do not grant absorb merely because a worker task can mark ready;
- independently review this continuation before a real mutating canary;
- test owner mismatch denial and positive same-owner continuation across process boundaries.

## Phase 7 — first source-mutating direct Chat canary

Only after Phase 6 and 6.5 pass.

Bound one real Lean task with:

- exact ref/SHA;
- one slot;
- explicit owned files;
- exact Lean MCP tool allowlist;
- no worker build/push;
- fixed resource bounds;
- verification floor;
- independent review requirement.

Flow:

`bridge activate → read/Lean-MCP/edit loop → heartbeat as needed → diagnostics → lean_verify → checkpoint commit → ready → separately authorized same-owner lead/integration continuation → absorb/build/validation → independent review`.

The first real canary is not permitted to serve as the first mutation-API or owner-continuity test.

## File-to-task map

| File | Phase/task |
|---|---|
| `config/lean-slots.public.json` | 1.1 |
| `scripts/lean_slots/state.py` | 1.1, 1.2 |
| `scripts/lean_slots/controller.py` | 2.1 |
| `scripts/lean_slots/proxy.py` | 2.2 |
| `scripts/lean_slots/cli.py` | 2.3 |
| `tests/test_lean_slots.py` | 1–4 |
| `docs/adrs/ADR-008-shared-lean-slot-control-plane.md` | 3.1 mandatory |
| `docs/dev-loops/LEAN_SLOT_OPERATOR_GUIDE.md` | 3.2 mandatory |
| architecture claim/routing docs | 3.3 if affected by measured implementation |
| ADR-018/spec/plan/audit status | review/reconciliation |
| `NetRxn/chat-control-plane` WP-010 heartbeat/bridge tests | Phase 6.5 caller-side dependency |

## Stop conditions

Stop and return to author repair/review rather than working around the issue if:

- exact-head independent implementation re-review reports unresolved blockers;
- an existing admission owner is discovered;
- private/downstream behavior differs materially from the measured active inventory;
- direct Chat would require impersonating another client;
- Chat identity needs different slot privileges from existing workers;
- admission cannot be enforced at controller + proxy boundaries;
- implementation requires changing slot count/lifecycle/build ownership;
- a safe `ready → absorb` owner-continuity path would require silently granting worker integration authority;
- live acceptance would require repairing/quarantined state rather than using a clean admitted slot.
