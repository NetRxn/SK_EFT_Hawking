# ADR-008 — Shared three-slot Lean control plane for Codex and Claude Code

- **Status:** **ACCEPTED (design, 2026-07-22; trusted-local authentication amendment, 2026-07-22). CODEX-FIRST IMPLEMENTATION AUTHORIZED; CLAUDE CODE ACTIVATION DEFERRED.**

  ⚠️ **PARITY STEP TAKEN 2026-08-13, AHEAD OF FULL CLAUDE ACTIVATION.** The Claude side gained
  `PreToolUse(Bash)` → `harness_worker_shell_guard.py`, which denies the same build / cache /
  integration command set as `.codex/hooks/pre_tool_use_policy.py` for SUBAGENTS ONLY (keyed on
  `agent_id`; the lead is never affected). A cross-client test loads the Codex policy module and
  asserts both deny the same commands, so the two cannot drift.

  **Why it could not wait for the activation window:** this ADR's load-bearing rule — *workers
  prove and commit; the orchestrator builds* — was mechanical on one client and prose on the
  other, and on 2026-08-13 three Claude workers correctly declined to build while the lead read
  their compliance as evasion and edited the instruction to require it. Nothing in the system
  could contradict the lead. An invariant enforced in one client and stated in the other is not
  a rule; it is a coin flip on which client picked up the work. The guard is client-local and
  changes no slot lifecycle, so it carries none of the risk the activation window is protecting
  against.

  ⚠️ **`lake build -j4` NO LONGER EXISTS AS A CAP.** Lake 5.0.0 removed `-j` entirely (verified
  against the full `lake --help` and `lake help build`). The narrow single-module exception was
  safe *because* it was job-capped, so it is now a lead-granted, one-slot-at-a-time decision —
  and the guard denies it to workers for that reason, not as a tightening.

  ⚠️ **PHASE 4 WIRED 2026-08-13; ACCEPTANCE GATE NOT YET PASSED.** The Claude activation change set
  is implemented and the control plane is live — see the *2026-08-13 Phase 4 record* below for what is
  measured, what each item cost, and which of the seven deferred-gate tests remain unrun. Claude status
  moves from `DESIGNED_NOT_VALIDATED` to **`WIRED_PENDING_ACCEPTANCE`**, not to verified. The legacy
  stdio path is retained as rollback per item 7 and is restored by
  `slotctl config render --client claude --rollback`.

  **Still deferred:** retirement of the legacy stdio entries and the manual off-repo `pkill` procedure
  (Phase 5), which the deferred gate's test 7 governs. Legacy per-slot `lean-lsp-wtN` remains the rollback path until that validation runs. Codex may be enabled immediately. The local single-user deployment defaults to credential-free loopback access; optional bearer authentication remains banked for a future shared-user deployment. The shared infrastructure MUST be Claude-compatible, but Claude configuration/plugin changes MUST NOT be activated or declared verified until a live Claude Code validation window is available, no earlier than the week of 2026-07-27. Legacy Claude behavior remains the rollback path until that validation passes.
- **Decider:** John Roehm (project owner) — approved the three-slot, orchestrator-owned-build posture and the Codex-first/Claude-later rollout on 2026-07-22.
- **Investigation and draft:** Codex, following an adversarial review of the current workspace, the pinned `lean-lsp-mcp` implementation, and the relevant public Claude-plugin commit history.
- **Scope:** the public `SK_EFT_Hawking` Lean substrate, product-neutral local slot infrastructure, Codex integration, and a privacy-preserving extension point for private downstream repositories. Repository-specific private configuration and paths remain in private overlays and MUST NOT be committed here.

## 2026-08-13 Phase 4 record — Claude activation wired

Design: [`docs/superpowers/specs/2026-08-13-adr008-phase4-claude-activation-design.md`](../superpowers/specs/2026-08-13-adr008-phase4-claude-activation-design.md),
decisions `P4-1`–`P4-6`. Measured against `5e764ec6`.

### Two claims in this ADR were wrong and are corrected here

1. **§ Context asserts the host "has since been raised to `kern.maxvnodes=786432`"** as though it were a
   standing property. It is a manual `sysctl -w`, which writes the running kernel only: the boot default
   on the reference host is **263168**, and the raise is lost on every reboot. Confirmed by inspection —
   no `/etc/sysctl.conf`, no `LaunchDaemon`, no `boot-args` persists it. A capacity claim that silently
   reverts is worse than an absent one, because the swarm fails at a moment nobody chose.

   **Superseded by measurement (2026-08-14).** 786432 is itself too low. On the reference host
   (16-core / 128 GiB), one active slot drives `kern.num_vnodes` to ~753k; two reach 586k mid-run, and a
   third projects past 786432 before any concurrent build. The requirement is now **declared data, not
   prose** — `host_limits` in the versioned inventory, asserted by `slotctl doctor` with a runnable
   remedy, at a floor of **1048576**. Persistence guidance, including why a `LaunchDaemon` and not
   `/etc/sysctl.conf`, lives in the operator guide.

   ⚠️ File descriptors are **not** the binding resource and `ulimit -n` will mislead you: a Lean server
   holds ~9,991 *memory-mapped* `.olean` files, which consume vnode references rather than open-file
   entries — system-wide `kern.num_files` stays under 11k while one server maps ten thousand files.
2. **Change-set item 3 names a "compile-feedback *unbounded build lane*".** No surface by that name
   exists. Its residue was the narrow single-module worker build exception, carried in three plugin
   files, one of which additionally still prescribed `-j4` — a flag Lake has never had — one paragraph
   after stating that Lake has no job cap. Item 3 was therefore a prose-reconciliation task.

### Change-set disposition

| # | Item | Disposition |
|---|---|---|
| 1 | Generate HTTP MCP entries pointing at the running endpoints | **Shipped.** `slotctl config render --client claude` owns a named key block inside the shared workspace `.mcp.json` — adds `skeft_wt{1,2,3}`, removes the legacy stdio slots, leaves every other project's servers and their order intact. Ports derive from the versioned inventory, so they cannot drift from the controller. `doctor` gained `config.claude`. |
| 2 | Lead acquires leases; workers never build | **Shipped.** `agents/lean-worker.md`, `skills/goal-dev/SKILL.md`, `references/parallel-worktrees.md` and `commands/reset-slot.md` now carry the `acquire → prepare → dispatch → ready → absorb` flow. This is a correctness requirement, not documentation: the endpoints are **lease-gated**, so a dispatch without a lease yields a connected server whose every tool call fails closed. |
| 3 | Remove/repurpose the unbounded build lane | **Shipped** as prose reconciliation — see above. The worker reports the module; the lead builds it. |
| 4 | Worker tool allowlists and build/cache/integration denials | Shipped earlier the same day (the parity step recorded above). |
| 5 | Project the protocol into a private Claude plugin | **Out of scope here** — private overlay. |
| 6 | Bump plugin versions, refresh cache, restart | **Restated to match the mechanism.** `skeft-qa` carries no `version` field and the loader keys its cache on a **content hash** (`~/.claude/plugins/cache/skeft-local/skeft-qa/<hash>/`), so there is nothing to bump: the edited tree becomes a new hash directory at the next refresh. Verified that the live cache snapshot still holds the pre-edit `lean-worker.md`, which is exactly why **the restart, not a version string, is the activation step.** |
| 7 | Retain the legacy stdio path | **Shipped** as a one-time pre-activation snapshot restored by `--rollback`, rather than as live coexisting entries — keeping both live would preserve exactly the `clients × configured servers` multiplication item 1 exists to remove (§ *Alternatives* 2). |

### A gap S-K required and the controller did not have

`Controller._owner()` resolved a session identity from `CODEX_THREAD_ID` alone, falling back to
`os.getppid()`. Because each `slotctl` invocation is a separate short-lived process, a Claude lead's
`acquire` and `prepare` ran under different parents and the second failed `process owner mismatch` —
S-C's own owner check rejecting the lease it had just issued. S-K requires the controller to "already
admit a later Claude client"; on this path it did not. Owner resolution is now product-neutral:
`LEAN_SLOT_OWNER_SESSION` first, then the per-client session variables.

### Measured state after activation

`slotctl doctor`: every check green except `wt2.lease`. **Claude activates at 2 of 3 slots** — slot 2 is
held by a **private** `QUARANTINED` lease carrying two unabsorbed commits. The public controller refuses
to reclaim it on repository-role mismatch, which is S-C and S-H behaving correctly; Phase 1's "use only
currently clean/available slots" already pre-decides this. Capacity returns when the private side
resolves its own quarantine.

Published epoch `6fc5d77c…`; endpoints report 21 tools with `lean_build` absent server-side, and
`lean_multi_attempt` / `lean_goal` / `lean_diagnostic_messages` / `lean_verify` all present, so the
worker's binding loop survives the transport change. The endpoints run without `--repl` per S-F.

### Deferred Claude activation gate — status

**Test 2 passes.** The full lead workflow was exercised against the live plane:
`acquire --slot 1 --client claude --base-ref main` → `prepare` (→ `ACTIVE`) → an MCP
`tools/call` of `lean_file_outline` over `http://127.0.0.1:8761/mcp?client=claude`, which returned real
Lean declaration data → `release` (→ `FREE`). Worker denial is separately enforced and tested. The
lease gate is therefore demonstrated in both directions: dispatch is refused unleased and served once
`ACTIVE`.

**Tests 1, 3, 4, 5 and 6 are unrun** — each needs a client restart and a live swarm, which is the
operator's next step. Test 7 is deliberately not attempted. **No Claude compatibility claim advances to
verified beyond test 2 on this record.**

Two operational facts this exercise established, both worth knowing before the first swarm:

- **A controller code change invalidates the running endpoints.** The proxy records a runtime
  fingerprint of the implementation it loaded, so after editing `scripts/lean_slots/*` the endpoints
  report `proxy=False` while still serving, and `prepare` fails with *"proxy for wtN is not healthy"*
  and quarantines the slot. Run `supervisor stop && supervisor start` after any controller edit. This
  is the mechanism working — it is what stops a stale front door being mistaken for a current one.
- **`slotctl` resolves its inventory, state root and lease directory from the current working
  directory.** Invoked from inside a slot it addresses a different control plane and reports every slot
  FREE. Always run it from the primary checkout.

## 2026-07-22 authentication amendment

The original Codex-first implementation required every local MCP client to inherit an environment-backed bearer token. That requirement was not part of the operator's requested feature and adds little protection on this trusted, single-user workstation: any process with the same user account can already read the local runtime state and repositories. It also creates a material reliability cost because an otherwise normal Codex launch fails MCP startup when hidden shell state is absent.

The active deployment therefore uses `server.client_auth = "trusted-local"`. Front doors remain bound to loopback, each client supplies a nonsecret URL identity label for collision/routing checks, tool dispatch remains fail-closed on the active lease and its client/repository/worktree/endpoint/dependency identity, and `lean_build` remains disabled. `server.client_auth = "bearer"` is retained and tested as an explicit deployment feature flag for a future shared-user host; only that mode requires `LEAN_SLOT_CODEX_TOKEN` and client-token hashes. Proxy process metadata fingerprints the loaded implementation and inventory so an authentication-mode or code change cannot be mistaken for an already-current process. This amendment changes authentication, not lifecycle authority or collision safety.
- **Related:** [ADR-004](ADR-004-substrate-integrity-gates.md) (single-writer/generated-artifact integrity posture); [ADR-005](ADR-005-derived-proof-atlas.md) (three-slot proof swarming and lead-owned extraction); [ADR-007](ADR-007-kernel-nogo-ledger-and-negative-frontier.md) (machine-enforced swarm steering); `ef0c3d36`, `f0d1d6eb`, `5639f685`, `abaff71b`, `ff0dcab4`, `62e8da08`, `e3441cc5`, and `43686347` (the public worktree/LSP harness evolution whose lessons this ADR preserves).

---

## Context

The repository already uses three persistent public worktrees (`wt1`, `wt2`, `wt3`) for parallel Lean development. Each historically had its own inherited stdio `lean-lsp-mcp` server because inline per-subagent MCP definitions did not surface through the Claude Agent tool (`ef0c3d36`). That design made parallel proof work possible, but the MCP process lifecycle remained client/session-owned: every Claude session could spawn the entire configured server set. Concurrent shell builds, worker-triggered builds, abandoned headless sessions, and per-session MCP processes then compounded file-descriptor/vnode pressure. The resulting ENFILE incident was pathological, not evidence that three workers are intrinsically unsafe.

The host has since been raised to `kern.maxvnodes=786432`, and three simultaneous build/slot workers are acceptable when lifecycle ownership is deterministic. The load-bearing correction is organizational and mechanical: **the primary, non-worktree orchestrator owns integration, cache publication, and rebuilding; slot workers prove and commit but do not rebuild or repair infrastructure.**

Codex and Claude Code both support streamable-HTTP MCP clients. The pinned `lean-lsp-mcp` release (`135997851a6b219c944cb1a9b46970658f874382`, release 0.26.1) supports streamable HTTP, fixed project roots, bearer authentication, disabled-tool lists, and a process-global shared Lean LSP client. This permits both products to connect to one server process for a given project/worktree instead of spawning one stdio server per client or subagent.

The same implementation also constrains the safe design:

- HTTP deployments are intentionally single-project and reject project switching. A live endpoint must not be rebound from one repository to another.
- The Lean LSP client is shared within one server process, but REPL objects are session-scoped; on first REPL use, separate client sessions can still start separate REPL subprocesses.
- `lean_build` is destructive and performs `lake exe cache get`, an optional `lake clean`, a full `lake build --verbose`, and an LSP restart. It is not a worker tool under the adopted authority model.
- The current slot cache stamp is repository-HEAD-only. That does not prove the copied `.lake` came from a successful build, and it is insufficient for a downstream project whose build also depends on an exact public-substrate revision.
- A workspace-root `.mcp.json` is local launch configuration, not a versioned source of truth. It must be generated from versioned templates and checked for drift.

Claude Code cannot be exercised during the present usage-limit window. Delaying all infrastructure work would unnecessarily block Codex, while activating untested Claude changes would turn assumptions into production configuration. This ADR therefore separates **shared infrastructure compatibility** from **per-client activation**.

### Historical constraints retained from the existing harness

The public Git history records operational requirements that remain binding:

1. **Persistent slots are deliberate.** Per-agent inline MCP did not surface; inherited, pre-existing slot endpoints did (`ef0c3d36`).
2. **Workers do not repair shared Git or build state.** Destructive recovery attempts caused avoidable churn even when confined to a worktree (`f0d1d6eb`).
3. **A worktree commit must not run the primary-checkout build/sync gate.** The shared hook previously crossed trees and produced invalid objects (`5639f685`).
4. **Reset immediately before dispatch.** A batch-reset slot can become stale when the primary branch advances before its worker starts (`ff0dcab4`).
5. **A cache copy needs a freshness predicate.** The existing HEAD stamp was introduced after stale `.lake` state reached workers (`abaff71b`), but this ADR strengthens that predicate to a successful-build epoch.
6. **Integration must preserve ancestry.** Cherry-picking caused the reset guard to treat already-absorbed work as unmerged (`62e8da08`).
7. **Surplus and leaked MCP processes are a real resource class.** Session trimming and the harvest reaper were added after ENFILE failures (`e3441cc5` and descendants).
8. **Ownership must survive compaction and use an explicit base.** The slot-aware marker/reset hardening added ownership transfer, base-ref resolution, and fail-closed Git checks (`43686347`).

---

## Decision

Adopt a **product-neutral, three-slot Lean control plane** shared by Codex and, after live validation, Claude Code. The physical worktrees remain `wt1`–`wt3`; no Codex-only `wt4`–`wt6` set is created. A slot may be used by either client, but never by two writers at once.

The words MUST, MUST NOT, SHOULD, and MAY below are normative.

| # | Decision | Required behavior |
|---|---|---|
| **S-A — Three global physical slots** | Slot identifiers are exactly `1`, `2`, and `3`. They are a workspace-wide capacity pool, not a per-client allowance. Codex and Claude MUST reuse this pool. Private/downstream work MAY have a repository-specific worktree paired with each number, but it remains the same capacity slot: only one heavy backend and one writer may be active for slot `N`. |
| **S-B — The primary orchestrator owns lifecycle and builds** | Only a non-worktree orchestrator may acquire/reclaim slots, reset branches, replace `.lake`, start/stop heavy backends, absorb commits, publish build epochs, run authoritative `lake build`/extraction/validation, or repair infrastructure. Workers may edit, query their leased MCP endpoint, verify proof state, stage their assigned files, and commit. Workers MUST NOT invoke `lake build`, `lake clean`, `lean_build`, dependency/cache repair, raw Git plumbing, or integration operations. |
| **S-C — Cross-client lease is the authority** | Every active slot has one fail-closed lease containing at least: schema version, slot number, repository role, client (`codex` or `claude`), client-auth mode, owner process/session identity, base ref and base SHA, worktree path, endpoint identity, acquired/heartbeat timestamps, lease state, and—when downstream—its exact public dependency SHA. Bearer mode additionally stores the client-token hash. Lease creation/transfer MUST use an atomic filesystem primitive; implementations MUST NOT assume `flock` exists on macOS. Prompt text and Claude goal markers are advisory projections of this lease, not competing authorities. |
| **S-D — Fixed-root HTTP endpoints** | Each repository/worktree has a stable, repository-qualified streamable-HTTP endpoint bound to `127.0.0.1`. The active single-user deployment uses credential-free `trusted-local` client access; an explicit `bearer` feature flag adds environment-backed client authentication for a shared-user deployment. Both products connect to the same endpoint for that project/worktree; no endpoint is duplicated per client. An endpoint MUST NOT be hot-rebound between public and downstream projects. A global gate MUST prevent more than three heavy Lean LSP/REPL backends across the numbered slots, even if more lightweight HTTP front doors are configured. |
| **S-E — Worker endpoint tool policy** | `lean_build` MUST be removed server-side from worker endpoint tool listings, then denied again by each client's worker tool policy. Shell `lake build`/`lake clean` MUST likewise be unavailable to worker roles. Defense is layered because client hooks are guardrails, not the sole enforcement boundary. Main/orchestrator validation uses an explicit orchestrator command path, never the worker endpoint. |
| **S-F — REPL is initially disabled** | Codex-first endpoints launch without `--repl`. Shared REPL is a later optimization, not an activation dependency. It may be enabled only after the pinned fork provides one lazy, project-scoped REPL per daemon (or an equivalently bounded design), serializes stateful access, resets it at lease/build boundaries, and passes two-client concurrency and teardown tests. Per-session REPL subprocess multiplication is not acceptable. |
| **S-G — Successful-build epochs replace HEAD-only stamps** | A slot cache is current only when it matches an orchestrator-published successful-build epoch. A public epoch includes the public commit SHA plus Lean toolchain and Lake manifest/dependency fingerprints. A downstream epoch additionally includes the exact public dependency SHA and the downstream fingerprints. The orchestrator MUST stop/park the slot LSP, clone the authoritative `.lake` to a temporary sibling, atomically install it, then restart service. It MUST NOT delete or replace `.lake` beneath a live LSP, and MUST NOT publish an epoch before the authoritative build succeeds. |
| **S-H — Downstream slots are paired, not assumed nested** | A private overlay is responsible for placing its worktree so its relative public path dependency resolves to the public half of the same numbered slot. During a downstream lease, that public half is pinned at the lease's `public_dependency_sha` and treated read-only. Acquisition MUST refuse a dirty or mismatched public dependency. The public implementation exposes the pairing protocol but contains no private repository name, path, endpoint, or credential. |
| **S-I — Integration is serialized and ancestry-safe** | `slotctl absorb` (or its exact equivalent) is orchestrator-only and protected by an integration lock. It verifies a clean committed slot, rebases the slot branch onto the current authoritative base when necessary, and then fast-forwards the primary checkout. It never cherry-picks, force-pushes, or discards unmerged work. A conflict or unexpected ancestry enters `QUARANTINED` state for explicit orchestrator resolution. After absorption, the orchestrator runs the authoritative gate, publishes a new epoch, rewarms the slot, and releases it. |
| **S-J — Versioned specification, generated local configuration** | Product-neutral controller/supervisor code, schemas, tests, and public endpoint templates live in this repository. Private endpoint mappings live only in a private overlay. Workspace-root Claude/Codex MCP configuration is generated local state with a source digest. `slotctl doctor` MUST report drift rather than silently overwriting operator configuration. Credentials, leases, PIDs, logs, and epochs are gitignored runtime state. |
| **S-K — Codex first; Claude activation gated** | Codex configuration, agents, and worker policies are implemented and tested first. The shared controller, supervisor, lease schema, endpoint naming, and generated-config interface MUST already admit a later Claude client. Claude plugin/config changes are a separate activation phase requiring live tests; until then, the existing Claude plugin and stdio launch path remain unchanged. No Claude compatibility claim may advance from “designed” to “verified” without those tests. |
| **S-L — A heavy backend is a consequence of a lease** *(added 2026-08-14)* | The public inventory sets `server.backend_policy = "leased"`: a backend runs only while this repository holds a lease in an active state. Every lease-exit path — `release`, `reclaim`, `absorb` — MUST reconcile the backend **after** the lease record is removed, because expectation is derived from the lease. Reclamation MUST NOT fail an exit path that has already succeeded; a stray backend is a resource cost, not a correctness one, and is reported for `supervisor start` to resolve. Rationale is measured, not assumed: one active slot holds `lake serve` + `lean --server` + `lean --worker` at ~4.4 GB, and before this rule that memory persisted from first use until the supervisor was stopped by hand. Peak concurrency is unchanged; only the idle-after-a-wave cost is removed. `"default"` remains available and is unaffected. |
| **S-P — An idle endpoint still advertises the real tool surface** *(added 2026-08-14)* | MCP tools are registered at **session start**. A slot whose backend is idle at that moment must therefore still advertise the full tool list, or it contributes **zero tools to that session permanently** — no matter what the lead leases afterwards. The supervisor harvests the list once (`tools/list` needs no Lean server, so this costs ~2s and spawns nothing heavy), caches it keyed on the server command + `disabled_tools` + REPL flag — **not** the per-slot fingerprint, which folds in the project path and would invalidate a good cache per slot — and the proxy serves it whenever the backend is down. Safety is unchanged: `tools/call` still reaches the real backend and still fails closed (`wt1 has no active lease`). ⚠️ Without this, S-L and S-N combine into an undispatchable swarm, which is how it was found: `skeft_wt2` registered empty in a live session because its backend was down at attach, and preparing the slot later never added its tools. **A legible failure at call time beats a silent absence at registration time.** ⚠️ **AMENDED 2026-08-14 — necessary, NOT sufficient.** S-P makes tools *register* on an idle slot; it does not make them *usable* once the slot is leased. A session whose MCP session was established against the idle proxy cannot address the endpoint after a lease starts the backend — every `tools/call` returns `-32602`, permanently, while a fresh session against the same endpoint at the same moment succeeds. **Tool registration and tool usability are different properties, and S-P delivers only the first.** See `papers/AutomatedReviews/2026-08-14-slot-session-ordering/infra.md`. ⛔ **The ordering constraint this amendment originally imposed — "acquire and prepare slots BEFORE starting the session that will use them" — is RETIRED by S-Q (2026-08-15) and must not be reinstated.** It was a workaround for a defect in our own front door, not a property of MCP: the idle proxy answered `initialize` without minting a session. S-Q makes the proxy own the client session, so usability now follows registration and the lifecycle is drivable mid-session. This is the second time this ADR recorded a proxy defect as a rule for operators to obey; when the next one appears, ask whether the front door should be behaving that way before writing the constraint down. |
| **S-O — Absorption means containment in the INTEGRATION ref** *(added 2026-08-14)* | `release` and `reclaim` must decide *"would freeing this slot lose work?"* by testing the slot's `HEAD` against the declared integration ref (`integration_ref`, default `main`) — the branch `absorb` fast-forwards. The lease's recorded `base_ref` is a **hint**, tried second, never the authority: ordinary hygiene (merge a feature branch, delete it) deletes or supersedes it. An unresolvable ref is skipped, not fatal; if nothing resolves the answer is **not absorbed**, so the audit stays fail-closed and dirty work still blocks. ⚠️ Discovered by a slot that no verb could free: its base branch was deleted after its commits reached `main`, so `release` failed on owner identity, `reclaim` failed on `rev-parse`, and the only exit was deleting runtime state by hand — precisely what S-C tells operators not to do. **A state reachable by ordinary hygiene must never be unrecoverable through the controller.** |
| **S-N — The lease gate applies at DISPATCH, not at CONNECT** *(added 2026-08-14)* | A client opens every endpoint in its configuration at startup, long before any slot is leased. An endpoint whose slot is unleased MUST therefore still complete the MCP handshake — `initialize`, `tools/list`, `ping`, and notifications — answering locally when no backend is running, and MUST advertise an **empty tool list**. ⚠️ **The empty list is the UNLEASED state only, and constrains no worker.** A leased, prepared slot exposes its full surface — measured at 21 tools, every one the MCP-first loop needs (`lean_goal`, `lean_multi_attempt`, `lean_diagnostic_messages`, `lean_verify`, `lean_run_code`, the searches, hover, completions). The single removal anywhere is `lean_build` (S-E). A worker never meets the empty list, because a worker is only ever dispatched into a slot the lead has leased and prepared. Refusal belongs on `tools/call`, where `LeaseGate.authorize` already enforces it. This does not weaken S-E: no tool can be named, and dispatch still fails closed. ⚠️ Discovered by regression — S-L made unleased endpoints answer `503` to `initialize`, and codex-cli 0.145.0 (`rmcp`) treats that as a **fatal** transport error that kills the whole session with no answer, `required = false` notwithstanding. Claude Code tolerates it, so client resilience here is **not symmetric** and a single client's success is not evidence the contract holds. |
| **S-Q — The proxy owns the client-facing MCP session** *(added 2026-08-15)* | The front door MUST mint and return its **own** `Mcp-Session-Id` on every `initialize` it answers — idle or not — and MUST translate that client session to a **lazily (re-)established backend session** on each forwarded request, re-establishing and retrying once when the backend does not recognise it. The client session is therefore stable across every backend lifecycle event: lease start, `prepare`'s server restart, `absorb`'s rewarm, and release. ⚠️ **This retires the ordering constraint recorded in S-P's amendment.** Measured at HEAD 2026-08-15: an idle proxy answered `initialize` with HTTP 200 and **no `Mcp-Session-Id` header at all**, while the backend mints one (`supervisor.py:676`). That asymmetry — not any MCP limitation — is why a session established against an idle slot could never address the endpoint after a lease: the client held no session the backend had ever issued, so every `tools/call` returned `-32602`. **Minting only when idle would not be enough**, and the reason generalises the bug: a session that attached while the backend was UP would hold a *backend* session id, which `prepare` invalidates when it restarts the Lean server mid-wave. Uniform minting is what makes the whole lifecycle transparent. Session state is per-proxy and in-memory, so a `supervisor stop`/`start` still ends client sessions — that is a configuration-change cost, not a per-wave one. **The operating consequence is that an agent may now drive `acquire → prepare → dispatch → absorb` entirely inside one session, with no operator restart** — which is the property the swarm needed and never had. |
| **S-M — Host kernel limits are declared, checked, and portable** *(added 2026-08-14)* | Resource requirements a swarm depends on MUST live as data in the versioned inventory (`host_limits`), keyed by `platform.system()`, and be reported by `doctor` with a remedy command derived from the declared minimum so the two cannot drift. Because this repository is public, the check MUST fail **only** for a knob the running kernel exposes whose value is below the declared floor: an undeclared platform passes, an unexposed knob passes, and `LEAN_SLOT_SKIP_HOST_LIMITS` opts a host out without a repository diff. A limit that is right for one workstation MUST NOT fail a clone on another. |

### Slot state machine

The controller owns this state machine:

```text
FREE
  -> ACQUIRED
  -> PREPARING
  -> ACTIVE
  -> READY_TO_ABSORB
  -> INTEGRATING
  -> REBUILDING
  -> REWARMING
  -> FREE

Any invariant failure -> QUARANTINED
```

- `ACQUIRED` records ownership before a worker is spawned.
- `PREPARING` resolves the base, verifies cleanliness/dependency pinning, installs a matching build epoch, and starts the endpoint backend.
- `ACTIVE` permits worker edits and MCP proof operations.
- `READY_TO_ABSORB` requires a clean worktree and at least one committed lease-owned change, unless the worker reports no-change completion.
- `INTEGRATING` through `REWARMING` are orchestrator-only states.
- `QUARANTINED` is fail-closed: no automatic reset, release, or stale reclaim may discard commits or dirty files.

### Lease and stale-reclaim rules

1. Trusted-local mode requires loopback binding and uses a nonsecret client identity label, not a credential. Bearer mode generates a token outside Git, supplies it through an environment-backed header, and stores only its hash in the lease.
2. Every slot-affecting controller command verifies owner process/session identity, client-auth mode, repository role, worktree realpath, branch, and lease state; bearer mode additionally verifies the token hash.
3. Heartbeat expiry alone does not authorize destructive reclaim. Reclaim also requires the recorded owner process/session to be absent and a Git audit to show no dirty files or unabsorbed commits.
4. If work exists, reclaim moves the slot to `QUARANTINED` and reports exact recovery commands; it does not reset automatically.
5. The endpoint gate checks the active lease before resource creation and tool dispatch. A stale client connection therefore cannot reactivate a released slot.

### Controller command contract

The implementation MUST provide non-interactive equivalents of:

```text
slotctl doctor
slotctl status [--json]
slotctl acquire --slot N --repo-role ROLE --client CLIENT --base-ref REF
slotctl prepare --slot N
slotctl ready --slot N
slotctl absorb --slot N
slotctl release --slot N
slotctl reclaim --slot N
```

`doctor` checks, at minimum: configured worktrees and realpaths, dirty/untracked state, branch/base reachability, lease/schema validity, endpoint health, process ownership, active heavy-backend count, successful-build epoch fingerprints, generated-config drift, and public/private boundary violations. Human-readable output and stable JSON are both required so Codex, later Claude, and operators consume the same facts.

---

## Client specifications

### Codex — activate now

Codex connects to the stable HTTP endpoints through repo-local `.codex/config.toml` or a generated included configuration. Worker agents inherit only the slot endpoints and tools needed for proof iteration. At minimum:

- `lean_build` is disabled both at the server and client layers.
- Worker shell policy denies `lake build`, `lake clean`, cache mutation, and integration commands.
- The orchestrator explicitly calls `slotctl acquire` before spawning a slot worker; a subagent-start hook does not acquire the slot.
- Each worker receives the lease identity, slot number, absolute worktree path, repository role, base SHA, allowed paths, and endpoint name in its task context.
- A worker that encounters lease mismatch, endpoint-root mismatch, build/cache failure, or Git failure stops and reports the exact condition.

Codex activation is accepted only after the Codex acceptance tests below pass. Claude absence during this phase removes an immediate collision source but does not waive lease enforcement: the same controller must remain safe when Claude is later added.

### Claude Code — prepare now, activate later

The shared infrastructure is Claude-ready when it provides stable HTTP URLs, optional bearer-header input, the lease API, generated `.mcp.json` data, and product-neutral status/doctor output. During the current usage-limit window:

- Do not alter the active Claude `.mcp.json`, workspace approval state, or installed plugin cache solely to switch transports.
- Do not remove the legacy stdio servers or session-start trimming procedure.
- Product-neutral infrastructure tests may use protocol-level MCP clients, but they do not count as Claude validation.

When live Claude testing becomes available, the Claude activation change set must:

1. Generate repository-qualified HTTP MCP entries that point to the already-running shared endpoints rather than spawning `uvx` stdio servers.
2. Update public `lean-worker`, goal-development, reset-slot, and parallel-worktree guidance so leases are acquired by the lead and workers never build.
3. Remove or repurpose the compile-feedback “unbounded build lane”; only no-build decomposition/research remains unbounded.
4. Add explicit worker tool allowlists and build/cache/integration denials.
5. Project the public protocol into any private Claude plugin via a private-only overlay without copying private identifiers into this repository.
6. Bump plugin versions, refresh the plugin cache, and restart sessions because command/skill prose and MCP attachment are session-snapshotted.
7. Retain the legacy stdio path until Claude-only and mixed-client acceptance tests pass.

---

## Acceptance tests

### Shared controller and supervisor

1. Acquiring an already leased slot fails closed, including cross-client acquisition.
2. Three different slots may be active simultaneously; a fourth heavy backend cannot start.
3. Dirty or untracked slot contents prevent reset/reclaim and produce `QUARANTINED`, not data loss.
4. Owner death with a clean, fully absorbed slot permits audited stale reclaim; owner death with work does not.
5. Endpoint project-root mismatch and repository-role mismatch fail before LSP/REPL creation.
6. A released lease cannot call tools through an existing HTTP session; bearer mode additionally rejects stale or wrong client credentials.
7. A daemon crash does not lose lease state; restart either reattaches to the matching lease or stays inactive.
8. Build/cache refresh cannot overlap another authoritative build, including across public and downstream repositories.
9. `.lake` replacement is atomic and never occurs while the slot LSP is live.
10. Build-epoch invalidation fires on commit, toolchain, manifest/pin, or downstream public-dependency changes.
11. Two workers branched from the same base can be absorbed serially: the second is rebased by the orchestrator and then fast-forwarded without cherry-picking.
12. `doctor --json` is deterministic enough for automated assertions and reports generated-config drift.
13. Public tests and fixtures contain no private repository names, paths, endpoint names, credentials, or proprietary namespace identifiers.

### Codex activation gate

1. Codex can acquire, prepare, use, commit in, and release each clean public slot.
2. Three Codex workers can perform MCP proof iteration concurrently with exactly three heavy slot backends and no worker-triggered `lake build`.
3. A worker is denied `lean_build`, shell builds/cleaning, cache mutation, and integration operations.
4. The orchestrator can absorb multiple worker commits serially, run one authoritative build at a time, publish the epoch, and rewarm/release the slots.
5. Interrupted Codex workers and stale sessions exercise the reclaim/quarantine rules without work loss.
6. Downstream Codex activation, if enabled in the same tranche, additionally passes paired-public-SHA, path-firewall, privacy, and private-hook worktree-safety tests in the private repository.

### Deferred Claude activation gate

Status as of 2026-08-14. A test is **PASSED** only where a real client exercised it end to end;
"the mechanism looks right" is not a pass.

1. **PASSED** — after the restart, a Claude session attached to `skeft_wt{1,3}` over HTTP with no
   per-agent stdio spawn; the legacy `lean-lsp-wt*` servers are gone from the session.
2. **PASSED** — `harness_worker_shell_guard.py` denies builds/cache/integration to subagents only,
   with a cross-client test asserting parity against the Codex policy; the lead is unaffected.
3. **PASSED** — a live session held an ACTIVE lease across a full `supervisor stop`/`start`. The
   lease was **preserved**, not reacquired (same owner-session hash), because it lives on disk and
   the proxy holds no lease state. The backend genuinely restarted (pid 47633 → 47903, fresh
   `lake serve` → `lean --server` → `lean --worker` chain), and the client's next tool call
   succeeded with no intervention — reconnect is transparent to the caller.

   ⚠️ **Project-root stability needed a discriminating test.** Comparing HEADs proves nothing:
   `prepare` resets the slot to the base, so wt1 and `main` sit at the same commit and every read
   looks identical from either root. Verified instead by planting a module that exists **only** in
   the slot's tree and resolving it through the endpoint — plus the backend argv, which stays
   pinned to `…/worktrees/wt1/lean`. A same-content check would have passed against the wrong root.
4. **PARTIAL** — two concurrent slots ran with no ENFILE and no process accumulation; the third was
   unavailable (see capacity). Peak measured at 2/3, not 3/3.
5. **PASSED** — a Claude lease on wt1 and a Codex lease on wt3 dispatched real Lean tool calls
   concurrently (`codex exec` returned `SUCCESS 33`, matching the Claude side). Sharing is denied at
   **both** layers: the controller refuses the second `acquire` (`already leased by claude`), and the
   endpoint refuses dispatch on a client mismatch (`skipped-nonmatching-lease`).
6. **PASSED** — restart behaviour is documented in the operator guide and was exercised twice, once
   for the transport switch and once for the stale-implementation fingerprint.
7. **NOT MET, deliberately.** Tests 3 and 4 are partial, so the legacy stdio entries stay
   recoverable via `config render --client claude --rollback`.

⚠️ **Test 5 is why the gate exists.** Every mechanism read correctly before it ran, and the first
two live attempts failed — see S-N. A single client's success would have been mistaken for the
contract holding.

---

## Rollout

Each phase is independently reversible. A later phase may not weaken an earlier phase's safety gate.

### Phase 0 — protect the current state and close known preconditions

- Inventory slot status before changes; never reset a dirty slot. At adoption time, `wt1` contains untracked work and is unavailable until its owner resolves it, while `wt2` and `wt3` are clean.
- Add tests for worktree hook behavior and ensure any downstream/private mirror skips primary-checkout sync/build work during worktree commits before downstream slots are enabled.
- Introduce the versioned schema, state-machine tests, and `doctor` in product-neutral public code.

### Phase 1 — Codex public activation

- Implement `slotctl`, lease/epoch storage, global build/integration locks, the HTTP supervisor/gate, and generated Codex configuration.
- Launch fixed public `wt1`–`wt3` endpoints on loopback, without REPL and without `lean_build`.
- Add Codex orchestrator/worker configuration and pass the shared-controller plus Codex activation gates.
- Use only currently clean/available slots; capacity increases automatically as protected work is resolved.

### Phase 2 — Codex downstream/private activation

- In the private repository only, add the repository-specific overlay, paired downstream worktrees, public-dependency SHA enforcement, private hook/reset parity, and private epoch fingerprints.
- Reuse the same global three-slot controller and heavy-backend semaphore; do not create additional numbered capacity.
- Run private privacy/firewall and paired-dependency tests before allowing private workers.

### Phase 3 — Claude-ready shared infrastructure, inactive client wiring

- Ensure the supervisor exposes stable Claude-compatible HTTP endpoints in trusted-local mode and can feature-flag environment-backed bearer headers for a shared-user deployment.
- Generate a reviewable Claude configuration preview from the same endpoint inventory without activating it.
- Keep current Claude plugin/config/stdio behavior unchanged and label Claude status `DESIGNED_NOT_VALIDATED`.

### Phase 4 — Claude Code live activation

- Begin only when Claude usage is available for live testing, no earlier than the week of 2026-07-27.
- Apply the Claude plugin/config changes listed above, refresh/restart, and run Claude-only followed by mixed-client acceptance tests.
- On failure, restore the legacy Claude configuration while leaving the Codex/shared controller operational.

### Phase 5 — legacy retirement

- After an observation period with both clients, remove client-spawned stdio slot servers, obsolete manual process trimming, and superseded worker build instructions.
- Retain migration diagnostics capable of identifying an old client still attempting to spawn legacy servers.

---

## Consequences

**Positive.** Codex can use the existing worktree investment immediately without doubling physical slots. Claude can later join the same capacity pool without another infrastructure migration. Build publication, integration, and cache lifecycle become deterministic and observable. Fixed-root endpoints preserve repository boundaries. A successful-build epoch makes cache correctness stronger than the current HEAD-only heuristic. Three workers remain available while the failure-amplifying operation—rebuilding—is serialized under the orchestrator.

**Costs.** The controller, supervisor/gate, generated configuration, epoch schema, and test matrix add real infrastructure. Initial Codex proof iteration may be slower without REPL. Downstream pairing requires repository-specific private work. Claude transport and plugin changes remain a separate change set and cannot be considered complete until live-tested.

**Risks and mitigations.** A controller bug could strand a slot; fail-closed quarantine and non-destructive recovery are mandatory. Trusted-local mode deliberately assumes processes running as the workstation owner are trusted and is rejected on non-loopback bindings. Bearer mode is available when that assumption no longer holds, but bearer identity never replaces filesystem/Git and lease checks. Lightweight endpoint processes may outnumber active slots, but the global heavy-backend semaphore—not process-name counting—is the resource invariant. The host vnode increase provides headroom but is not used as a substitute for lifecycle control.

---

## Alternatives considered

1. **Create Codex-only `wt4`–`wt6`.** Rejected: duplicates large build state, bypasses the proven slots, and permits six heavy workers if both clients run.
2. **Leave Claude stdio infrastructure unchanged and add equivalent Codex stdio servers.** Rejected: preserves the `clients × configured servers` multiplication that caused process/vnode pressure.
3. **Hot-rebind three HTTP daemons between repositories.** Rejected: the server intentionally fixes the HTTP project root; reconnecting clients and stale sessions make rebinding a path-firewall risk.
4. **Allow each worker an isolated build because three workers fit.** Rejected: three workers fit only when rebuild ownership is controlled. Simultaneous rebuilding was the pathological multiplier the new design must remove.
5. **Use prompt instructions or client hooks as the lease.** Rejected: prompts drift, hooks do not cover every path, and Codex subagent-start hooks cannot be the spawn-stopping authority. The lease is checked by the controller and endpoint.
6. **Wait for Claude availability before implementing anything.** Rejected: Codex can be validated independently, and the client-neutral interfaces can be frozen now. What is deferred is Claude activation and the claim of Claude compatibility, not the shared infrastructure.
7. **Enable the current per-session REPL immediately.** Rejected for Phase 1: streamable HTTP shares the LSP but not the session-scoped REPL object/process lifecycle. Bounded shared REPL is an optimization requiring its own concurrency tests.

---

## References

- [Claude Code MCP documentation](https://docs.anthropic.com/en/docs/claude-code/mcp) — HTTP transport, project configuration, environment/header support, and reconnect behavior.
- [Codex MCP documentation](https://learn.chatgpt.com/docs/extend/mcp) — HTTP URLs, bearer-token environment variables, and server/tool allow/deny configuration.
- [Codex hooks documentation](https://learn.chatgpt.com/docs/hooks) — tool-hook coverage and the explicit warning that hooks are guardrails rather than a complete enforcement boundary.
- Pinned `lean-lsp-mcp` source at release 0.26.1 — fixed-root HTTP behavior, shared LSP client, session-scoped REPL, destructive `lean_build`, bearer authentication, and disabled-tool support.
