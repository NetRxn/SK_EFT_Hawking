# ADR-018 — distinct Chat client for shared Lean slots: design specification

**Status:** **SPECIFICATION ACCEPTED** at PR #75 head `469e4e47607b7d74da0b9b3c81dc56d04c3dd24f`, COMMENT review `5202241729`: `ACCEPT`, residual B1 `CLOSED`, no B2–B6 regression. Author implementation is in progress on PR #76; mechanical verification and fresh exact-head independent implementation re-review remain pending before Gate A.

**Normative decision:** [`ADR-018`](../../adrs/ADR-018-chat-client-for-shared-lean-slots.md).

**Measured public base:** `codex/memory-process-clocks` @ `9ea7b61a33e91190ffe99e843247e03a51e8fb3e`.

**Measured private/downstream state:** `NetRxn-RD` `codex/frontier-first-deliverables` @ `47b380f6e233a0fd70662640422b3652e6d3191a`; its `config/lean-slots.private.json` is schema 1, trusted-local, has no `allowed_clients`, and its overlay tests exercise the public controller.

**Existing owner:** ADR-008 remains the authority for the shared slot lifecycle. This specification only extends client admission; it does not introduce a second execution plane.

---

## 1. Problem statement

The existing shared Lean control plane already has the correct execution semantics for direct bounded proof work:

- three persistent worktree slots;
- one writer per slot;
- supervisor-owned loopback MCP front doors;
- lease-gated dispatch;
- successful-build epoch preparation;
- no worker-side `lean_build`;
- primary-orchestrator-owned ready/absorb/build/integration;
- quarantine instead of destructive repair;
- paired public/private dependency pinning where configured.

The missing capability is narrower: a machine-local NetRxn Chat execution bridge needs to participate as a **distinct client identity** rather than impersonating Codex or Claude.

Measured at the public base ref:

- `Controller._owner()` already accepts the product-neutral `LEAN_SLOT_OWNER_SESSION` before client-specific session variables;
- lease records already store an arbitrary string `client`;
- bearer token filenames already accept safe generic client strings;
- `LeaseGate.identify()` in trusted-local mode hard-codes `{codex, claude}`;
- `slotctl acquire --client` and `slotctl session env --client` hard-code `codex|claude` in argparse;
- `slotctl config render --client` is a different capability boundary and supports only concrete Codex/Claude renderers;
- the versioned slot inventory has no declared admitted-client set;
- `Controller.acquire()` itself does not currently enforce an admission roster;
- a running proxy snapshots inventory/code, so a roster file edit is not immediate revocation.

Measured in the private/downstream overlay:

- the active private inventory is schema 1 and lacks `allowed_clients`;
- it uses the same public controller through the private `slotctl` wrapper;
- therefore a required new schema-1 field would be a real cross-repository compatibility break.

The design must make admission a project-owned versioned fact while preserving every existing runtime invariant and making rollout/removal semantics explicit.

---

## 2. Design decisions

Numbering `S18-n` is stable and is cited by the implementation plan and review.

### S18-1 — one versioned lease/dispatch client-admission owner

Add to `config/lean-slots.public.json`:

```json
"server": {
  "allowed_clients": ["codex", "claude", "chat"]
}
```

`Inventory.allowed_clients` is the **only lease/dispatch admission owner**. It validates:

- JSON array shape;
- non-empty;
- unique values;
- safe client-name grammar compatible with existing token-file naming;
- callers receive an immutable/set-like projection rather than mutating raw inventory state.

The renderer capability set is intentionally separate because it answers a different question: which product configuration formats this repository knows how to generate.

### S18-2 — controller validates admission even for programmatic callers

`Controller.acquire(number, client=..., base_ref=...)` rejects a client not present in `Inventory.allowed_clients` **before creating a lease or mutating slot state**.

`Controller.session_environment(client=...)` applies the same validation before token/environment handling.

Rationale: CLI validation alone is not an authority boundary. The local Chat bridge and future callers may invoke controller logic programmatically.

Existing lifecycle commands operating on an already-issued lease do not re-check a newly edited roster mid-flight; removal is a quiescent migration defined in S18-9.

### S18-3 — proxy consumes the same admission data

In trusted-local mode, `LeaseGate.identify()` replaces the hard-coded set with `Inventory.allowed_clients`.

It still requires a non-empty `?client=` hint. A hint not admitted by the proxy's loaded inventory fails closed.

Bearer mode retains its existing token lookup and hint/token-consistency checks. Admission is checked in addition to token ownership: possession of a token file for a client not present in the loaded roster does not admit that client.

Because the proxy snapshots inventory at process start, roster changes become effective only after the restart/verification procedure in S18-9.

### S18-4 — admission CLI paths do not maintain their own roster

Remove argparse `choices=("codex", "claude")` only from client arguments whose true authority is the versioned admission roster:

- `slotctl acquire --client`;
- `slotctl session env --client`.

The CLI accepts a string and the controller/inventory returns the authoritative admission failure.

This decision does **not** remove the explicit capability restriction from `slotctl config render --client`; that is covered by S18-11.

### S18-5 — one durable bridge owner session spans project lifecycle operations

The direct local bridge supplies one stable opaque execution-session identifier via:

```text
LEAN_SLOT_OWNER_SESSION=<opaque bridge session id>
```

for every project-native lifecycle invocation belonging to that execution session.

There is no owner transfer at `ready`. The same durable local orchestration session remains the lease owner until a project-native terminal transition.

This ADR does not authorize the bridge to perform `absorb`. Before any real source-mutating Chat task is admitted, the caller/control-plane side must:

- expose project-native heartbeat under the same owner session;
- demonstrate owner continuity across separate processes;
- define and independently review the explicitly authorized lead/integration operation that continues `ready → absorb` under that same owner session;
- prove that this does not turn ordinary worker authority into implicit merge/integration authority.

Gate A remains no-change and terminates through `release`, so it does not claim to prove heartbeat or absorb.

No product-specific Chat owner variable is introduced.

### S18-6 — no third client configuration renderer

The direct bridge derives the slot endpoint from versioned inventory and calls:

```text
http://127.0.0.1:<proxy_port>/mcp?client=chat
```

The existing Claude and Codex config renderers remain the only renderer capabilities in this change.

`slotctl config render --client chat` must fail before writing any configuration. The CLI handler uses exhaustive named dispatch rather than a catch-all `else` that could silently map an unknown client to Codex.

A future Chat-specific renderer requires a separate architecture change driven by a concrete transport need.

### S18-7 — no privilege difference by client identity

`chat` is an audit/routing identity, not a privilege tier.

The same slot invariants apply regardless of admitted client:

- identical lease state machine;
- identical configured worktree and branch identity;
- identical endpoint identity checks;
- identical disabled worker tools;
- identical epoch preparation;
- identical paired-dependency checks;
- identical readiness/integration rules;
- identical quarantine behavior.

Any future client-specific privilege difference requires a separate architecture change.

### S18-8 — schema-1 migration uses an exact legacy fallback and never implies Chat

Measurement of the active private overlay resolves the earlier migration alternative.

For schema 1 only:

- if `server.allowed_clients` is present, validate and use it;
- if it is absent, interpret the admitted set as exactly `{codex, claude}`;
- the missing-field fallback never contains `chat`.

The public inventory explicitly declares `[codex, claude, chat]` when implementation lands.

The active private inventory is not silently rewritten and remains Codex/Claude-only until its own repository explicitly opts in to Chat.

Mixed-version paired-inventory tests are mandatory. A later schema version may make the field required after all overlays migrate.

### S18-9 — removal is quiescent, bearer-credential-cleaned, and restart-bound

A roster edit does not mutate an already-running proxy's in-memory inventory, and the planned `session_environment(client)` path rejects unadmitted clients before token processing. Therefore credential cleanup cannot depend on a post-removal session command.

Canonical removal procedure:

1. **quiesce + preflight:** prove there is no active lease for the client being removed and evaluate the current/prospective roster-vs-live-lease health predicate;
2. **bearer mode only, while still admitted:** invoke `slotctl session revoke-token --client <client>`;
3. remove the client from the versioned inventory;
4. restart the supervisor/proxies so current code + inventory are loaded;
5. run project-native health/doctor checks;
6. prove the removed identity is denied through both controller and proxy paths.

`slotctl session revoke-token --client <client>` is a narrow operator/admin capability, not a worker capability. Its implementation contract is:

- require `client_auth == "bearer"`;
- require the client is still present in `Inventory.allowed_clients`;
- fail closed if any live lease records that client;
- resolve exactly `Inventory.client_token_path(client)`; no caller-supplied path;
- delete that token file if present, and succeed idempotently if already absent;
- never emit the token value or other secret material;
- return only nonsecret structured evidence such as client name + whether credential state existed/revocation completed.

Trusted-local mode has no credential state to revoke and skips step 2.

The roster/lease mismatch predicate is observational. A current or prospective roster that excludes a client while a live lease still records that client is red migration-health evidence, but the predicate must not mutate/reclaim/quarantine/release the lease and must not be inserted as a hidden `_lease_for_command()` admission re-check. Correct-owner ADR-008 cleanup remains legal until the lease is quiescent.

Bearer re-admission after removal must generate fresh credential state. The pre-removal credential must fail after later re-admission; `Inventory.token()` must not silently reuse a credential that removal declared revoked.

Tests must distinguish stale-process policy before restart from effective removal after restart, and must production-seed the roster/lease mismatch into the actual lease/inventory artifacts consumed by doctor/preflight.

This section incorporates and supersedes the ordering portion of the residual-B1 S18-14..16 supplement. Where the supplement or older reconciliation prose differs, **S18-9 is canonical**.

### S18-10 — owner continuity is a control-plane responsibility, not an implicit worker privilege

The project slot controller already has the primitive required for cross-process ownership: `LEAN_SLOT_OWNER_SESSION`.

The caller/control plane is responsible for retaining that opaque session identity durably and presenting it on every lifecycle command. It may expose `heartbeat` without gaining integration authority.

A `READY_TO_ABSORB` lease cannot be handed to an unrelated actor/session. The production continuation must either use the same authorized owner session or a future explicit project-native ownership-transfer mechanism. This ADR chooses the former for the first implementation and does not introduce ownership transfer.

### S18-11 — renderer capability and lease admission remain deliberately distinct

Lease admission comes from `Inventory.allowed_clients`.

Renderer support remains an exhaustive product capability:

- Codex renderer;
- Claude renderer;
- no Chat renderer in ADR-018.

Negative verification must prove `config render --client chat` fails with no write.

### S18-12 — live acceptance tests the production bridge end-to-end

Gate A must exercise the real NetRxn local execution path, not manually substitute project commands:

1. durable direct-Chat preflight;
2. bridge `activate()`;
3. independently observe active Chat lease/prepared state;
4. bridge domain-MCP diagnostics/`lean_verify` over the adapter-selected endpoint;
5. mismatched-client negative control;
6. prove HEAD and `git status --porcelain` unchanged;
7. bridge `release_no_change()`;
8. capture exact task/ref/SHA/slot/lease/tool evidence.

Manual `slotctl` calls may be used as observation/debug evidence only.

Before Gate B (real source mutation), a production-shaped disposable repository must exercise `write → checkpoint → ready`, and the production bridge must support heartbeat. A real source task is a bounded canary after those conditions, not the first test of the mutation API.

### S18-13 — normative lifecycle documentation is reconciled in the shipping commit

ADR-008 remains lifecycle authority, but its current Codex/Claude-only client enumeration becomes false once Chat is admitted.

Therefore the implementation commit must update the relevant ADR-008 S-A/S-C language and `LEAN_SLOT_OPERATOR_GUIDE.md` to make admitted-client enumeration inventory-owned while preserving the existing lifecycle/build/integration contract.

This is mandatory architecture-rule compliance, not optional documentation cleanup.

---

## 3. Files and ownership

Implementation surfaces for the accepted design and current author implementation wave:

| Surface | Responsibility |
|---|---|
| `config/lean-slots.public.json` | explicitly admits public clients |
| `scripts/lean_slots/state.py` | validates/exports allowed clients; schema-1 exact legacy fallback; exact token-path primitive |
| `scripts/lean_slots/controller.py` | programmatic admission enforcement; doctor/removal-preflight mismatch predicate; bearer token revocation guard/operation; product-neutral diagnostics where touched |
| `scripts/lean_slots/proxy.py` | trusted-local/bearer admission enforcement against loaded inventory |
| `scripts/lean_slots/cli.py` | delegates admission on acquire/session; exposes narrow `session revoke-token`; preserves exhaustive renderer capability boundary |
| `tests/test_lean_slots.py` | production-shaped admission/removal/stale-proxy/token-revocation/owner/renderer/mixed-version tests |
| `docs/adrs/ADR-008-shared-lean-slot-control-plane.md` | mandatory client-enumeration reconciliation |
| `docs/dev-loops/LEAN_SLOT_OPERATOR_GUIDE.md` | mandatory client/removal/owner procedure reconciliation |
| architecture claim/routing docs | update if implementation makes a load-bearing claim or routing row incomplete |

No Chat-control-plane Python is copied into SK_EFT.

The caller-side WP-010 separately owns bridge heartbeat, durable local execution state, scoped mutation, and end-to-end bridge acceptance mechanics.

---

## 4. Invariants / negative requirements

Implementation is incorrect if any of the following becomes true:

1. an unadmitted client can acquire a lease through either CLI or direct Python calls;
2. a stale bearer token alone can admit a removed client;
3. a roster edit is claimed as immediate revocation while a stale proxy continues serving;
4. a client can be removed while its active lease remains and the system calls that migration complete;
5. `chat` can dispatch tools against a `claude`/`codex` lease, or vice versa;
6. adding `chat` creates another worktree, backend, proxy, build lane, cache, or integration route;
7. the bridge must impersonate `claude` to function;
8. the worker gains `lean_build` or primary-checkout build authority;
9. Chat connectivity alone authorizes execution without an active project lease;
10. implementation changes private/downstream inventory contents implicitly;
11. schema-1 missing-field compatibility admits Chat;
12. `config render --client chat` reaches the Codex renderer;
13. failure of a Chat client causes automatic reset/repair/discard of slot state;
14. a different owner session can absorb a Chat-owned ready lease without an explicit transfer mechanism;
15. direct Chat receives merge, publication, or release authority merely from slot admission;
16. bearer token revocation depends on a caller-supplied filesystem path or on an already-unadmitted client reaching `session env`;
17. doctor/removal-preflight changes lease lifecycle state merely because roster health is red.

---

## 5. Mechanical verification design

### 5.1 Inventory admission and migration tests

Production-shaped inventory fixtures demonstrate:

- public inventory with `codex`, `claude`, `chat` loads;
- empty list fails;
- duplicate entries fail;
- malformed client names fail;
- every present non-array roster value, including JSON `null`, fails rather than taking the schema-1 compatibility fallback;
- schema-1 missing field resolves exactly to Codex/Claude;
- mixed public-explicit/private-legacy paired inventories load;
- private legacy inventory does not admit Chat;
- unadmitted client acquire fails before a lease file is created.

### 5.2 Trusted-local proxy tests

For an inventory admitting all three clients:

- discovery handshake for `chat` succeeds according to existing discovery rules;
- lease-required call with no lease fails;
- active `chat` lease + `?client=chat` passes lease-gate identity;
- active `chat` lease + `?client=claude` fails;
- active `claude` lease + `?client=chat` fails;
- unknown `?client=other` fails before dispatch.

Removal tests use a real long-running proxy fixture or equivalent process boundary to demonstrate:

- roster file edit alone leaves the stale process on old policy;
- stale state is detected;
- restart loads the new roster;
- removed identity then fails;
- production-seeded live-lease/roster mismatch is red in doctor/removal-preflight while the lease artifact remains unchanged and correct-owner cleanup stays possible.

### 5.3 Bearer-mode tests

- `chat` gets its own token path under the existing token mechanism;
- correct Chat token + Chat hint maps to Chat;
- Chat token + Claude hint fails;
- a token for a client absent from the loaded roster fails admission;
- `slotctl session revoke-token --client chat` succeeds only while Chat is still admitted, bearer mode is active, and no Chat lease remains;
- token revocation deletes only the exact project-owned client token path and never emits credential material;
- trusted-local mode does not pretend to revoke nonexistent bearer state;
- roster removal follows revocation, then supervisor restart + denial verification;
- later re-add creates fresh credential state and the pre-removal credential cannot authenticate;
- legacy Codex/Claude token behavior remains green.

### 5.4 Session-owner tests

Use multiple controller invocations with the same `LEAN_SLOT_OWNER_SESSION` and verify ownership across acquire/prepare/heartbeat/ready/release-or-absorb as appropriate.

Negative control: a different owner session cannot operate the lease.

No client-specific owner variable is needed for `chat`.

### 5.5 Renderer tests

- Codex renderer remains positive;
- Claude renderer remains positive;
- `config render --client chat` fails before writing;
- an unknown renderer value fails explicitly rather than falling through.

### 5.6 Existing-invariant regression tests

All existing ADR-008 tests remain green, especially:

- worktree identity;
- no-worker-build enforcement;
- build-epoch matching;
- proxy fingerprint/drift behavior;
- paired dependency pinning;
- quarantine/release/ready/absorb semantics;
- global three-slot capacity.

---

## 6. Live acceptance sequence — explicitly after implementation review

### Gate A — no-mutation production-bridge rehearsal

Only after implementation, applicable mechanical verification, and independent implementation review are satisfactory:

1. bridge durable preflight against exact ref/SHA and clean/free slot;
2. bridge `activate()` performs project-native probe/acquire/prepare with one owner session;
3. independent status observation confirms expected Chat lease/worktree/endpoint;
4. bridge calls only task-allowlisted diagnostics/`lean_verify` via `?client=chat`;
5. mismatched-client call is denied;
6. `lean_build` is absent/denied;
7. HEAD and `git status --porcelain` prove no source/untracked mutation;
8. bridge `release_no_change()` succeeds;
9. exact evidence is filed.

This rehearsal remains below the lease timeout with margin and does not substitute for heartbeat validation.

### Gate B prerequisite — mutation API and continuation proof

Before touching real project source:

- bridge heartbeat is implemented and tested with the same owner session;
- a disposable production-shaped repo/slot exercise proves scoped `write → checkpoint → ready`;
- owner continuity through the intended authorized `ready → absorb` continuation is tested/reviewed;
- no bridge operation gains integration authority accidentally.

### Gate B — first source-mutating proof canary

Only after Gate A and the prerequisite above:

1. acquire/prepare an admitted task-owned slot through the bridge;
2. bounded read / Lean MCP / scoped edit loop;
3. heartbeat as needed;
4. diagnostics + `lean_verify` floor;
5. task-owned commit through normal hooks;
6. `ready`;
7. same durable project lifecycle owner continues through the separately authorized lead/integration path to `absorb` and authoritative build/validation;
8. independent implementation/scientific review remains separate from worker success.

---

## 7. Review reconciliation and current implementation gate

Review history on PR #75 is tied to exact target heads:

- first review at `332f44f5e4ba557ae1d119a55018aa51fd923ce8`: `ACCEPT_WITH_CHANGES`, B1–B6;
- focused review at `8407079f935ba3dd758a4f2c288b3cd43ec5239e`: B1 `PARTIALLY_CLOSED`, B2–B6 `CLOSED`;
- cloud-dispatched residual-B1 closure review at `0e71346775028daa09eb90006be6c85c458b5388`: substantive mismatch-preflight design accepted, with one remaining blocker that D14/S18-16's pre-edit credential cleanup contradicted canonical D8/S18-9 and left the concrete credential operation deferred;
- final canonical-consistency review at `469e4e47607b7d74da0b9b3c81dc56d04c3dd24f`: COMMENT `5202241729`, **`ACCEPT`**, residual B1 `CLOSED`, no B2–B6 regression.

That final review closed the specification gate. The current implementation remains a separate evidence target. Implementation review `5203396570` at `42803dfc2baa5e5a26b152557e0c7e0d8c9504aa` returned `ACCEPT_WITH_CHANGES` because current normative/status documents still contradicted the accepted specification; later author repair `fbfeb76e3ed5736ec95268e3ede9acd0dad59d44` also corrected the explicit-null/missing-key parser distinction under S18-8 and added regression tests. Those changes are author work, not independent acceptance.

Before Gate A, obtain actual applicable mechanical evidence on the exact resulting head and a fresh independent implementation re-review that checks both the documentation reconciliation and explicit-null repair. Tests merely authored are not tests run, and a scheduled task identity alone does not establish reviewer independence.

---

## 8. Out of scope

- deployment/tunneling of the NetRxn Chat local bridge;
- ChatGPT Apps SDK UI;
- changing the number of slots;
- worker-side authoritative builds;
- silently enabling Chat in the private paired repository;
- introducing a generic lease ownership-transfer mechanism;
- generalizing all SK_EFT clients into a portfolio-wide identity system;
- merging or publishing from Chat;
- changing the research/publication control planes.
