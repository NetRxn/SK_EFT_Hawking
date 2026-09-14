# ADR-018 — Distinct Chat client on the shared Lean slot control plane

- **Status:** **PROPOSED — specification only; independent adversarial review required before implementation.**
- **Tracks:** issue #74.
- **Measured base:** `codex/memory-process-clocks` @ `9ea7b61a33e91190ffe99e843247e03a51e8fb3e`.
- **Owner:** ADR-008 remains normative for slot lifecycle, builds, integration, leases, endpoint identity, and paired-dependency safety. This ADR is a narrow client-admission extension, not a second control plane.

## Context

ADR-008 already supports two clients, Codex and Claude Code, over the same supervisor-owned `wt1`/`wt2`/`wt3` Lean slots. The primary orchestrator owns slot lifecycle and authoritative builds; workers use lease-gated loopback MCP endpoints, prove/commit within one slot, and never build or repair shared infrastructure.

A separate NetRxn Chat control-plane project is preparing a machine-local execution bridge so an ordinary Chat session can eventually drive the same bounded proof-development loop directly rather than requiring a Claude/Codex worker for every edit/MCP cycle. The bridge deliberately refuses to impersonate either existing client. The project therefore needs an explicit third client identity if direct Chat is ever admitted.

The current implementation is partly generic already:

- `Controller._owner()` prefers product-neutral `LEAN_SLOT_OWNER_SESSION`, then product-specific session variables;
- bearer token files accept generic safe client names;
- lease records already carry a string `client` and the proxy compares it to the active lease;
- endpoint/worktree/repository-role/dependency/build-epoch checks do not depend on a specific product.

But client admission is currently duplicated/hard-coded:

- trusted-local `LeaseGate.identify()` accepts only `codex` and `claude`;
- `slotctl acquire --client` accepts only `codex|claude` in argparse;
- `slotctl session env --client` accepts only `codex|claude` in argparse;
- the versioned inventory has no declared client-admission set.

The correct extension is therefore to make **admitted client identity versioned project data** and have every admission surface consume it. It is not to add another slot, another proxy, another worktree family, or a parallel lifecycle.

## Decisions

### D1 — ADR-008 remains the lifecycle authority

A `chat` client uses the existing `acquire → prepare → dispatch → ready → absorb` or clean `release` lifecycle. It receives no alternative reset, build, integration, quarantine, or cache path.

The primary non-worktree orchestrator remains the only owner of authoritative builds and integration. Direct Chat workers inherit the same no-worker-build rule as Claude/Codex workers.

### D2 — Admitted client identities become inventory data

Add one versioned server field:

```json
"allowed_clients": ["codex", "claude", "chat"]
```

`Inventory` validates this as a non-empty unique set of safe client names. `chat` is admitted only by an explicit repository diff to this field.

The inventory is the single source for client admission. No other code path maintains a parallel set.

### D3 — Every client admission path validates against `Inventory.allowed_clients`

At minimum:

- trusted-local `LeaseGate.identify()` validates its `client_hint` through the inventory;
- `Controller.acquire()` validates `client` through the inventory even when called programmatically;
- `Controller.session_environment()` validates `client` before token/session handling;
- CLI parsing stops hard-coding the two legacy choices and lets the controller/inventory issue the authoritative error.

This is defense in depth: a caller cannot bypass the CLI and create an unadmitted lease.

### D4 — `chat` is an identity label, not a new privilege tier

In trusted-local mode the identity remains a nonsecret loopback routing label, exactly like the existing clients. Lease state is still the dispatch authority.

In bearer mode the existing token-file mechanism applies to `chat` without a special path. The supplied token and optional client hint must still agree.

No change expands the trust boundary beyond the single-user/loopback posture already accepted by ADR-008.

### D5 — direct Chat uses product-neutral session ownership

The local bridge supplies a stable, opaque session identifier via `LEAN_SLOT_OWNER_SESSION` across all `slotctl` lifecycle calls. No Chat-specific owner environment variable is required.

That keeps lease ownership independent of transport implementation and reuses the exact mechanism added for later-client compatibility in ADR-008.

### D6 — no client-specific MCP configuration is added to SK_EFT

The local bridge derives the selected slot proxy URL from the versioned inventory and calls the endpoint as:

```text
http://127.0.0.1:<proxy_port>/mcp?client=chat
```

SK_EFT does not need to render a third workspace client configuration merely to support this bridge. Claude and Codex configuration renderers remain unchanged.

A future deployment may add a Chat-specific renderer only if a concrete client requires one; that would be a separate architecture change.

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

A direct Chat control plane may checkpoint a slot commit and later ask the project-native lifecycle to mark it ready; it does not acquire merge/publish authority from that capability.

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

## Compatibility and migration

Existing Codex/Claude behavior must remain unchanged. The implementation should provide a compatibility default for inventories that predate `allowed_clients` only if necessary for downstream/private rollout; the public inventory itself should declare the field explicitly when this change ships.

Downstream/private paired inventories must not be silently rewritten by the public change. If they consume shared slot code, their compatibility behavior must be exercised in tests before migration.

## Acceptance requirements

Implementation is not accepted merely because `chat` can call an endpoint. Required evidence includes:

1. inventory validation rejects empty, duplicate, malformed, and unknown client admission;
2. existing `codex` and `claude` trusted-local tests remain green;
3. trusted-local proxy accepts `chat` discovery traffic but denies lease-required calls before an active `chat` lease;
4. a lease acquired as `chat` cannot be used by `claude` or `codex`, and vice versa;
5. controller programmatic acquisition rejects an unadmitted client;
6. bearer mode maps `chat` to its own token file and preserves hint/token mismatch denial;
7. `LEAN_SLOT_OWNER_SESSION` permits acquire/prepare/heartbeat/ready/release or absorb across separate controller invocations;
8. worker endpoint still omits/denies `lean_build` for `chat`;
9. paired public/private dependency checks remain unchanged;
10. `slotctl doctor`/supervisor fingerprinting detect stale pre-change proxies after code/inventory changes;
11. one bounded **no-mutation** live Chat-bridge rehearsal exercises acquire → prepare → MCP diagnostics/verify → release;
12. only after the no-mutation rehearsal passes may a source-mutating direct Chat proof task be admitted.

## Review gate

Per the repository `architecture-change` process, this ADR/spec package must receive a distinct independent adversarial review before the design is treated as settled. Self-review may identify issues but does not satisfy that gate.
