# ADR-018 — distinct Chat client for shared Lean slots: design specification

**Status:** revised after independent adversarial review (`ACCEPT_WITH_CHANGES`). **Do not implement until a focused fresh-reader re-review accepts the reconciled design.**

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

### S18-9 — removal is quiescent and restart-bound, not instant file-edit revocation

A roster edit does not mutate an already-running proxy's in-memory inventory.

Supported removal procedure:

1. prove there is no active lease for the client being removed;
2. remove the client from the versioned inventory;
3. in bearer mode, delete or rotate the removed client's token state so future re-admission cannot silently reuse an old credential;
4. restart the supervisor/proxies so the current code and inventory are loaded;
5. run project-native health/doctor checks;
6. prove the removed identity is denied through controller and proxy paths.

Attempting to treat an inventory edit with an active removed-client lease as completed revocation is invalid. Existing owner lifecycle commands are not made roster-sensitive mid-flight because that could strand an issued lease; the client must be quiesced before the edit.

Tests must measure stale-proxy behavior before restart and effective removal after restart rather than conflating the two.

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

Expected implementation surfaces if focused re-review accepts the reconciled design:

| Surface | Responsibility |
|---|---|
| `config/lean-slots.public.json` | explicitly admits public clients |
| `scripts/lean_slots/state.py` | validates/exports allowed clients; schema-1 exact legacy fallback |
| `scripts/lean_slots/controller.py` | programmatic admission enforcement on acquire/session environment; product-neutral diagnostics where touched |
| `scripts/lean_slots/proxy.py` | trusted-local/bearer admission enforcement against loaded inventory |
| `scripts/lean_slots/cli.py` | delegates admission on acquire/session; preserves exhaustive renderer capability boundary |
| `tests/test_lean_slots.py` | production-shaped admission/removal/stale-proxy/owner/renderer/mixed-version tests |
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
15. direct Chat receives merge, publication, or release authority merely from slot admission.

---

## 5. Mechanical verification design

### 5.1 Inventory admission and migration tests

Production-shaped inventory fixtures demonstrate:

- public inventory with `codex`, `claude`, `chat` loads;
- empty list fails;
- duplicate entries fail;
- malformed client names fail;
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
- removed identity then fails.

### 5.3 Bearer-mode tests

- `chat` gets its own token path under the existing token mechanism;
- correct Chat token + Chat hint maps to Chat;
- Chat token + Claude hint fails;
- a token for a client absent from the loaded roster fails admission;
- removal procedure deletes/rotates token state;
- later re-add does not silently reuse the pre-removal credential;
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

Only after implementation + independent implementation review are green:

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

## 7. Review reconciliation and focused re-review questions

The first independent review on PR #75 returned `ACCEPT_WITH_CHANGES`. Focused re-review should verify that the revised head adequately resolves:

- B1: removal/revocation, stale proxy, active-lease and bearer-token semantics → S18-9;
- B2: durable owner session, heartbeat, `ready → absorb` actor boundary → S18-5/S18-10/S18-12;
- B3: measured private migration and exact schema-1 fallback → S18-8;
- B4: renderer capability vs admission → S18-4/S18-6/S18-11;
- B5: production bridge Gate A and disposable mutation-path prerequisite → S18-12;
- B6: mandatory ADR-008/operator-guide reconciliation → S18-13.

The reviewer should also challenge whether these dispositions introduce a new blocker or contradict ADR-008.

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
