# ADR-018 — distinct Chat client for shared Lean slots: design specification

**Status:** proposed design, 2026-09-14. **Do not implement until the independent adversarial specification review is complete and blocking findings are resolved.**

**Normative decision:** [`ADR-018`](../../adrs/ADR-018-chat-client-for-shared-lean-slots.md).

**Measured base:** `codex/memory-process-clocks` @ `9ea7b61a33e91190ffe99e843247e03a51e8fb3e`.

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

Measured at the base ref:

- `Controller._owner()` already accepts the product-neutral `LEAN_SLOT_OWNER_SESSION` before client-specific session variables;
- lease records already store an arbitrary string `client`;
- bearer token filenames already accept safe generic client strings;
- `LeaseGate.identify()` in trusted-local mode hard-codes `{codex, claude}`;
- `slotctl acquire --client` and `slotctl session env --client` hard-code `codex|claude` in argparse;
- the versioned slot inventory has no declared admitted-client set;
- `Controller.acquire()` itself does not currently enforce an admission roster.

The design must make admission a project-owned versioned fact while preserving every existing runtime invariant.

---

## 2. Design decisions

Numbering `S18-n` is stable and is cited by the implementation plan and review.

### S18-1 — one versioned client-admission owner

Add to `config/lean-slots.public.json`:

```json
"server": {
  "allowed_clients": ["codex", "claude", "chat"]
}
```

`Inventory.allowed_clients` is the **only** admission owner. It validates:

- JSON array shape;
- non-empty;
- unique values;
- safe client-name grammar compatible with existing token-file naming;
- existing public deployment includes `codex` and `claude` during migration;
- callers receive an immutable/set-like projection rather than mutating raw inventory state.

The exact validation helper belongs beside the existing inventory/auth validation in `scripts/lean_slots/state.py`.

### S18-2 — controller validates admission even for programmatic callers

`Controller.acquire(number, client=..., base_ref=...)` must reject a client not present in `Inventory.allowed_clients` **before creating a lease or mutating slot state**.

Rationale: CLI validation alone is not an authority boundary. The local Chat bridge and future callers may invoke controller logic programmatically.

`Controller.session_environment(client=...)` applies the same validation before token/environment handling.

### S18-3 — proxy consumes the same admission data

In trusted-local mode, `LeaseGate.identify()` replaces the hard-coded set with `Inventory.allowed_clients`.

It still requires a non-empty `?client=` hint. A hint not admitted by the inventory fails closed.

Bearer mode retains its existing token lookup and hint/token-consistency checks. Admission is checked in addition to token ownership: possession of a stale token file for a removed client must not silently re-admit that client.

### S18-4 — CLI does not maintain its own client roster

Remove argparse `choices=("codex", "claude")` from the client arguments whose true authority is the versioned inventory.

The CLI accepts a string, and the controller/inventory returns the authoritative failure.

This applies to at least:

- `slotctl acquire --client`;
- `slotctl session env --client`.

No new `--client chat` special case is added elsewhere.

### S18-5 — Chat uses the existing owner-session mechanism

The direct local bridge supplies a stable opaque execution-session identifier via:

```text
LEAN_SLOT_OWNER_SESSION=<opaque bridge session id>
```

for every lifecycle invocation belonging to one admitted execution session.

No `CHAT_THREAD_ID` or product-specific slot-owner variable is introduced.

### S18-6 — no third client configuration renderer

The direct bridge derives the slot endpoint from versioned inventory and calls:

```text
http://127.0.0.1:<proxy_port>/mcp?client=chat
```

The existing Claude and Codex config renderers remain unchanged.

This change therefore does **not** add Chat entries to workspace `.mcp.json`, a new generated config file, or a new endpoint family.

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

### S18-8 — migration is explicit and downstream-safe

The public inventory declares `allowed_clients` immediately when implementation lands.

For an older/private paired inventory that lacks the field, implementation must choose one of these **before coding** based on actual downstream usage:

1. fail closed and require that inventory to migrate in the same coordinated release; or
2. provide a narrow legacy default of exactly `{"codex", "claude"}` while emitting/recording a migration obligation.

The implementation must not silently default missing inventories to include `chat`.

The adversarial review must explicitly evaluate which migration behavior is safer given the current private overlay contract.

---

## 3. Files and ownership

Expected implementation surfaces if the design is accepted:

| Surface | Responsibility |
|---|---|
| `config/lean-slots.public.json` | declares admitted client identities |
| `scripts/lean_slots/state.py` | validates/exports allowed clients |
| `scripts/lean_slots/controller.py` | programmatic admission enforcement on acquire/session environment |
| `scripts/lean_slots/proxy.py` | trusted-local and bearer admission enforcement |
| `scripts/lean_slots/cli.py` | removes duplicated argparse roster; delegates authority |
| `tests/test_lean_slots.py` | production-shaped positive/negative admission and compatibility tests |
| `docs/adrs/ADR-008-shared-lean-slot-control-plane.md` | only if implementation changes/corrects a current statement there |
| `docs/dev-loops/LEAN_SLOT_OPERATOR_GUIDE.md` | documents the third client only when implementation exists |
| `docs/architecture/*` owning slot surface | update if the implementation makes existing mechanism prose incomplete |

No Chat-control-plane Python is copied into SK_EFT.

---

## 4. Invariants / negative requirements

Implementation is incorrect if any of the following becomes true:

1. an unadmitted client can acquire a lease through either CLI or direct Python calls;
2. a stale bearer token file can re-admit a removed client;
3. `chat` can dispatch tools against a `claude`/`codex` lease, or vice versa;
4. adding `chat` creates another worktree, backend, proxy, build lane, cache, or integration route;
5. the bridge must impersonate `claude` to function;
6. the worker gains `lean_build` or primary-checkout build authority;
7. Chat connectivity alone authorizes execution without an active project lease;
8. implementation changes private/downstream inventory contents implicitly;
9. failure of a Chat client causes automatic reset/repair/discard of slot state;
10. direct Chat receives merge, publication, or release authority merely from slot admission.

---

## 5. Mechanical verification design

### 5.1 Inventory admission tests

Production-shaped inventory fixtures must demonstrate:

- public inventory with `codex`, `claude`, `chat` loads;
- empty list fails;
- duplicate entries fail;
- malformed client names fail;
- unadmitted client acquire fails before a lease file is created;
- removal of a client from the inventory makes later acquisition fail.

### 5.2 Trusted-local proxy tests

For an inventory admitting all three clients:

- discovery handshake for `chat` succeeds according to existing discovery rules;
- lease-required call with no lease fails;
- active `chat` lease + `?client=chat` passes lease-gate identity;
- active `chat` lease + `?client=claude` fails;
- active `claude` lease + `?client=chat` fails;
- unknown `?client=other` fails before dispatch.

### 5.3 Bearer-mode tests

- `chat` gets its own token path under the existing token mechanism;
- correct Chat token + Chat hint maps to Chat;
- Chat token + Claude hint fails;
- token for a client removed from `allowed_clients` fails admission;
- legacy Codex/Claude token behavior remains green.

### 5.4 Session-owner tests

Use multiple controller invocations with the same `LEAN_SLOT_OWNER_SESSION` value and verify ownership survives across the lifecycle exactly as the current cross-process session tests require.

No client-specific owner variable is needed for `chat`.

### 5.5 Existing-invariant regression tests

All existing ADR-008 tests remain green, especially:

- worktree identity;
- no-worker-build enforcement;
- build-epoch matching;
- proxy fingerprint/drift behavior;
- paired dependency pinning;
- quarantine/release/ready/absorb semantics.

---

## 6. Live acceptance sequence — explicitly after implementation review

Live acceptance is ordered so the first Chat interaction cannot mutate project source.

### Gate A — no-mutation direct Chat rehearsal

1. supervisor/current proxy fingerprint healthy;
2. choose a clean/free slot;
3. `acquire --client chat` using one stable `LEAN_SLOT_OWNER_SESSION`;
4. `prepare`;
5. call bounded diagnostics/`lean_verify` via `?client=chat`;
6. assert no source diff/unabsorbed commit;
7. `release`;
8. record exact ref/SHA, slot, lease evidence and tool result.

Failure at any step blocks source-mutating direct Chat work.

### Gate B — source-mutating proof task

Only after Gate A:

1. acquire/prepare an admitted task-owned slot;
2. bounded read / Lean MCP / scoped edit loop;
3. diagnostics + `lean_verify` floor;
4. task-owned commit through normal hooks;
5. `ready`;
6. existing lead/orchestrator performs `absorb` and authoritative build/validation;
7. independent implementation review remains separate from worker success.

---

## 7. Adversarial-review questions

The required independent specification review should actively try to falsify these claims:

- Is inventory actually the correct single owner, or does another existing client registry already exist?
- Does moving argparse validation inward accidentally broaden another call path?
- Is `chat` really privilege-equivalent under trusted-local/bearer, or is there a hidden Claude/Codex assumption elsewhere?
- Is missing-field migration safe for the private paired overlay?
- Can a removed bearer client survive through an existing token file?
- Is `LEAN_SLOT_OWNER_SESSION` sufficient for the local bridge's process model, including heartbeats and recovery?
- Is there any path where a Chat bridge can change source before project-native lease admission?
- Does the proposed no-mutation acceptance genuinely test the transport/identity boundary, or can it pass vacuously?
- Does a third client increase slot concurrency/resource pressure, or only provide another contender for the same leases?
- Which current architecture/operator docs become false or incomplete when the change lands?

The reviewer should report **blocking**, **non-blocking**, and **unknown / needs measurement** findings separately and give an explicit `ACCEPT / ACCEPT_WITH_CHANGES / REJECT` specification verdict.

---

## 8. Out of scope

- deployment/tunneling of the NetRxn Chat local bridge;
- ChatGPT Apps SDK UI;
- changing the number of slots;
- worker-side authoritative builds;
- changing private paired-repository semantics except explicit compatibility testing/migration;
- generalizing all SK_EFT clients into a portfolio-wide identity system;
- merging or publishing from Chat;
- changing the research/publication control planes.
