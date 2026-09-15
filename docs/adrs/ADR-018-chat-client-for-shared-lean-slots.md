# ADR-018 — Distinct Chat client on the shared Lean slot control plane

- **Status:** **SPECIFICATION ACCEPTED — PR #75 head `469e4e47607b7d74da0b9b3c81dc56d04c3dd24f` received COMMENT review `5202241729`: `ACCEPT`, residual B1 `CLOSED`, no B2–B6 regression. Author implementation is in progress on PR #76; mechanical verification and exact-head independent implementation re-review remain pending before Gate A.**
- **Tracks:** issue #74; specification review on PR #75; implementation on PR #76.
- **Measured public base:** `codex/memory-process-clocks` @ `9ea7b61a33e91190ffe99e843247e03a51e8fb3e`.
- **Measured private/downstream state:** `NetRxn-RD` `codex/frontier-first-deliverables` @ `47b380f6e233a0fd70662640422b3652e6d3191a`; `config/lean-slots.private.json` is schema 1, trusted-local, has no `allowed_clients`, and `tests/test_lean_slot_overlay.py` verifies the private wrapper reuses the public controller.
- **Owner:** ADR-008 remains normative for slot lifecycle, builds, integration, leases, endpoint identity, and paired-dependency safety. This ADR is a narrow client-admission extension, not a second control plane.

## Context

ADR-008 already supports Codex and Claude Code over the same supervisor-owned `wt1`/`wt2`/`wt3` Lean slots. The primary orchestrator owns slot lifecycle and authoritative builds; workers use lease-gated loopback MCP endpoints, prove/commit within one slot, and never build or repair shared infrastructure.

A separate NetRxn Chat control-plane project is preparing a machine-local execution bridge so an ordinary Chat session can eventually drive the same bounded proof-development loop directly rather than requiring a Claude/Codex worker for every edit/MCP cycle. The bridge deliberately refuses to impersonate either existing client. The project therefore needs an explicit third client identity if direct Chat is ever admitted.

At the measured specification base, the implementation was partly generic already:

- `Controller._owner()` prefers product-neutral `LEAN_SLOT_OWNER_SESSION`, then product-specific session variables;
- bearer token files accept generic safe client names;
- lease records already carry a string `client` and the proxy compares it to the active lease;
- endpoint/worktree/repository-role/dependency/build-epoch checks do not depend on a specific product.

At that measured base, client admission was duplicated/hard-coded:

- trusted-local `LeaseGate.identify()` accepts only `codex` and `claude`;
- `slotctl acquire --client` accepts only `codex|claude` in argparse;
- `slotctl session env --client` accepts only `codex|claude` in argparse;
- the versioned inventory has no declared client-admission set.

The correct extension is therefore to make **admitted client identity versioned project data** and have every admission surface consume it. It is not to add another slot, another proxy, another worktree family, or a parallel lifecycle.

## Decisions

### D1 — ADR-008 remains the lifecycle authority

A `chat` client uses the existing `acquire → prepare → dispatch → ready → absorb` or clean `release` lifecycle. It receives no alternative reset, build, integration, quarantine, or cache path.

The primary non-worktree orchestration path remains the only owner of authoritative builds and integration. Direct Chat workers inherit the same no-worker-build rule as Claude/Codex workers.

### D2 — Admitted client identities become inventory data

Add one versioned server field to the public inventory:

```json
"allowed_clients": ["codex", "claude", "chat"]
```

`Inventory` validates this as a non-empty unique set of safe client names. `chat` is admitted only by an explicit repository diff to this field.

The inventory is the single source for **lease/dispatch admission**. No other code path maintains a parallel admission set.

### D3 — Every lease/dispatch admission path validates against `Inventory.allowed_clients`

At minimum:

- trusted-local `LeaseGate.identify()` validates its `client_hint` through the inventory;
- bearer-mode identity additionally requires the token's client to remain admitted;
- `Controller.acquire()` validates `client` through the inventory even when called programmatically;
- `Controller.session_environment()` validates `client` before token/session handling;
- CLI parsing for `acquire --client` and `session env --client` stops hard-coding the two legacy choices and lets the controller/inventory issue the authoritative error.

This is defense in depth: a caller cannot bypass the CLI and create an unadmitted lease.

### D4 — `chat` is an identity label, not a new privilege tier

In trusted-local mode the identity remains a nonsecret loopback routing label, exactly like the existing clients. Lease state is still the dispatch authority.

In bearer mode the existing token-file mechanism applies to `chat` without a special path. The supplied token and optional client hint must still agree.

No change expands the trust boundary beyond the single-user/loopback posture already accepted by ADR-008.

### D5 — direct Chat uses one durable project-lifecycle owner session

The local bridge supplies a stable, opaque session identifier via `LEAN_SLOT_OWNER_SESSION` across all project-native lifecycle calls for one admitted execution session.

There is **no owner transfer at `ready`**. The same durable local orchestration session remains the lease owner until a project-native terminal transition (`release` for no change, or later `absorb` when that integration operation is separately admitted).

This ADR does not itself grant the bridge `absorb`/integration authority. A source-mutating live Chat task is not admitted merely because `ready` works. Before the first real mutating task, the caller/control-plane side must demonstrate heartbeat support and a reviewed continuation through `ready → absorb` using the same owner session and an explicitly authorized lead/integration operation. Until then, only the no-change `release` live path is eligible for acceptance.

No Chat-specific owner environment variable is introduced.

### D6 — no client-specific MCP configuration renderer is added to SK_EFT

The local bridge derives the selected slot proxy URL from the versioned inventory and calls the endpoint as:

```text
http://127.0.0.1:<proxy_port>/mcp?client=chat
```

SK_EFT does not render a third workspace client configuration merely to support this bridge.

The **renderer capability set remains explicitly Codex/Claude-specific** and is not an admission roster. `slotctl config render --client chat` must fail without writing Codex configuration. The existing handler must use exhaustive named dispatch rather than a catch-all `else` that could route an unknown client through the Codex renderer.

A future Chat-specific renderer, if a concrete transport requires one, is a separate architecture change.

### D7 — project-native worker and integration invariants are unchanged

The `chat` path must preserve all existing slot invariants, including:

- one writer per slot;
- exact configured worktree/branch identity;
- lease-gated tool calls;
- `lean_build` disabled at worker endpoints;
- successful-build epoch preparation;
- paired dependency pinning where configured;
- clean committed work required by `ready`;
- orchestrator-owned `absorb` and authoritative validation;
- quarantine on unexpected state rather than automatic repair/discard;
- no direct worker push from a shared slot.

A direct Chat control plane may checkpoint a slot commit and mark it ready only under the task contract; that capability does not itself grant merge, publication, or release authority.

### D8 — client removal is a quiescent, restart-bound operation

`allowed_clients` is loaded into the long-running proxy process. Editing the inventory is therefore **not immediate revocation**.

The canonical supported removal procedure is:

1. **quiesce and preflight:** prove there is no active lease owned by the client and evaluate the non-disruptive prospective-roster/lease health predicate;
2. **bearer mode only, while the client is still admitted:** run the project-owned `slotctl session revoke-token --client <client>` operation. It must fail closed unless the client is currently admitted and has no live lease, delete only `Inventory.client_token_path(client)`, be idempotent when the token is already absent, and never print token material. Trusted-local mode skips this step;
3. remove the client from the versioned `allowed_clients` inventory;
4. restart the supervisor/proxies so the new inventory/code fingerprint is actually loaded;
5. run project-native health/doctor checks and prove the removed identity is denied through controller and proxy paths.

A roster edit while an active lease for that client exists is an invalid migration state and must be reported by the health/removal-preflight predicate, not treated as successful revocation. That predicate is observational only: it must not make lifecycle methods roster-sensitive mid-flight or strand an already-issued lease. The legitimate owner retains the existing ADR-008 cleanup path until the lease is quiescent.

Bearer credential revocation is deliberately **pre-edit**. `Controller.session_environment()` is planned to reject an unadmitted client before token processing, so post-removal session-token cleanup is not a valid dependency. Deleting the token while still admitted ensures a later re-admission creates fresh credential state rather than silently reusing the pre-removal credential.

Tests must distinguish a stale still-serving proxy from an effective post-restart removal and must production-seed the roster/lease mismatch into the real artifacts consumed by doctor/preflight.

This canonical sequence incorporates the residual-B1 D13/D14 addendum. If older reconciliation text differs on credential-removal ordering, **this ADR D8 controls**.

### D9 — schema-1 private/downstream compatibility is explicit and does not imply Chat

Measurement found the active private inventory is schema 1, has no `allowed_clients`, uses trusted-local auth, and reuses the public controller implementation.

Therefore schema 1 receives one narrow backward-compatible interpretation:

> if `server.allowed_clients` is absent, the admitted set is exactly `{codex, claude}`.

The public inventory declares `[codex, claude, chat]` explicitly when this change ships. Missing-field fallback **never** includes `chat`.

This lets the public controller upgrade without breaking the private overlay while preserving private opt-in: private Chat execution remains denied until the private inventory is separately changed under its own authority.

Mixed-version paired-inventory tests are mandatory. A future schema revision may make the field required after all overlays have migrated.

### D10 — renderer support and lease admission are deliberately different authorities

Lease/dispatch admission is inventory-owned. Client-specific configuration generation is a capability-specific interface.

Accordingly:

- `acquire --client` and `session env --client` delegate admission to inventory/controller;
- `config render --client` remains exhaustive over the renderers that actually exist (`codex`, `claude`);
- `chat` cannot fall through to a Codex renderer.

This distinction is intentional, not duplicate admission policy.

### D11 — the first live acceptance must exercise the production bridge, not manual substitutes

The no-mutation Gate A must run the actual caller path:

`durable preflight → bridge activate() → project-native lease/prepare → bridge domain MCP diagnostics/verify → mismatched-identity negative control → bridge release_no_change()`.

Manual `slotctl acquire/prepare/release` calls may be used only as independent observation/debug evidence, not as substitutes for the bridge calls whose correctness Gate A is meant to prove.

Gate A is intentionally bounded below the 900-second lease timeout with a two-minute safety margin; it does not claim to validate heartbeat.

Before Gate B (source mutation), the production bridge must have a project-native heartbeat path and a production-shaped disposable-repository exercise of `write → checkpoint → ready`. The first real project source task is a bounded canary, not the first evidence that those APIs work.

### D12 — ADR-008 and the operator guide must be reconciled in the shipping commit

ADR-008 remains lifecycle authority, but its current client enumeration (`codex`/`claude`) becomes false when Chat ships.

The implementation commit must therefore update the relevant ADR-008 S-A/S-C client-enumeration language and the Lean slot operator guide to describe inventory-owned admitted clients while preserving all lifecycle/build/integration decisions. This reconciliation is mandatory, not conditional cleanup.

## Rejected alternatives

### A1 — impersonate `claude`

Rejected. It destroys client-level auditability and makes future policy differences impossible to reason about. The bridge must fail closed until the project explicitly admits its own identity.

### A2 — launch separate Chat-only Lean worktrees/endpoints

Rejected. It recreates the pre-ADR-008 multiplication of execution resources and a second lifecycle beside the existing shared pool.

### A3 — let the local bridge call `lean-lsp-mcp` directly

Rejected. That bypasses slot leases, build/cache isolation, disabled tools, paired dependencies, and the supervisor-owned endpoint contract.

### A4 — keep the hard-coded client set and add `chat` in every caller

Rejected. It makes client admission another duplicated roster. Versioned inventory data is the correct owner.

### A5 — treat the local Chat connector/tunnel as sufficient authorization

Rejected. Transport connectivity does not authorize slot use. The project lease remains the runtime admission boundary.

### A6 — immediate roster-edit revocation

Rejected for this local control plane. The proxy snapshots versioned inventory; pretending a file edit instantly revokes a live process would create a false security property and can strand active leases. Quiesce + credential revocation where applicable + roster edit + restart + verify is the supported removal boundary.

## Compatibility and migration

The active private inventory was measured directly and is a real consumer of the public controller contract. It is schema 1 and does not yet declare `allowed_clients`.

Implementation therefore retains schema 1 compatibility with the exact legacy fallback `{codex, claude}`. The public inventory explicitly declares Chat. The private inventory is not silently rewritten and does not inherit Chat admission.

Rollout order:

1. public controller/tests gain the compatibility reader and explicit public roster;
2. mixed public/private tests prove an older private inventory remains Codex/Claude-only;
3. public proxies restart and Chat admission is accepted only on the public side;
4. private Chat admission, if wanted later, requires an explicit private inventory change and its own review.

Rollback/removal of Chat follows D8 and leaves the legacy private overlay unaffected.

## Acceptance requirements

Implementation is not accepted merely because `chat` can call an endpoint. Required evidence includes:

1. inventory validation rejects empty, duplicate, malformed, and other present non-array client admission values; explicit JSON `null` is invalid and never selects the missing-field compatibility path;
2. missing schema-1 field resolves to exactly `codex`/`claude`, never Chat;
3. existing `codex` and `claude` trusted-local tests remain green;
4. trusted-local proxy accepts `chat` discovery traffic but denies lease-required calls before an active `chat` lease;
5. a lease acquired as `chat` cannot be used by `claude` or `codex`, and vice versa;
6. controller programmatic acquisition rejects an unadmitted client before lease state is created;
7. bearer mode maps `chat` to its own token file and preserves hint/token mismatch denial;
8. removal/re-add tests cover production-seeded roster/lease mismatch reporting, unchanged lease state, correct-owner cleanup, stale running proxy behavior, mandatory restart, canonical pre-edit bearer token revocation, and proof that re-admission cannot reuse the pre-removal credential;
9. same `LEAN_SLOT_OWNER_SESSION` permits cross-process acquire/prepare/release for Gate A; heartbeat/ready/absorb owner continuity is proven before Gate B;
10. worker endpoint still omits/denies `lean_build` for `chat`;
11. mixed-version paired public/private dependency tests preserve private Codex/Claude-only admission;
12. `slotctl config render --client chat` fails without writing Codex/Claude configuration;
13. `slotctl doctor`/supervisor fingerprinting detect stale pre-change proxies after code/inventory changes, and doctor/removal-preflight reports a live lease whose client is outside the current/prospective roster without mutating the lease;
14. one bounded **no-mutation** live rehearsal exercises the real production bridge path from preflight through release;
15. disposable production-shaped mutation tests exercise write/checkpoint/ready before any real source task;
16. ADR-008 and the operator guide are reconciled in the same implementation commit;
17. only after Gate A, heartbeat/integration-continuity evidence, implementation review, and the disposable mutation path pass may a real source-mutating direct Chat proof canary be admitted.

## Review gate

The review chain on PR #75 is historical evidence tied to exact heads:

- first independent review at `332f44f5e4ba557ae1d119a55018aa51fd923ce8`: `ACCEPT_WITH_CHANGES`, B1–B6;
- focused re-review at `8407079f935ba3dd758a4f2c288b3cd43ec5239e`: B1 `PARTIALLY_CLOSED`, B2–B6 `CLOSED`;
- cloud-dispatched residual-B1 closure review at `0e71346775028daa09eb90006be6c85c458b5388`: `ACCEPT_WITH_CHANGES`, substantive D13/S18-14 mismatch-preflight design accepted, with one remaining canonical contradiction in bearer credential-removal ordering;
- final canonical-consistency review at `469e4e47607b7d74da0b9b3c81dc56d04c3dd24f`: COMMENT `5202241729`, **`ACCEPT`**, residual B1 `CLOSED`, no B2–B6 regression.

That final review closes the ADR-018 specification gate at its exact head. PR #76 implementation may proceed under this accepted design, but acceptance does not transfer to implementation heads. Implementation review `5203396570` at `42803dfc2baa5e5a26b152557e0c7e0d8c9504aa` returned `ACCEPT_WITH_CHANGES` and required current-document reconciliation; the later explicit-null author repair also changed the target. Mechanical verification and a fresh exact-head independent implementation re-review remain required before Gate A. Self-review and author reconciliation do not satisfy that implementation-review gate.
