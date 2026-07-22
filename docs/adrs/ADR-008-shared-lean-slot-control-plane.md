# ADR-008 — Shared three-slot Lean control plane for Codex and Claude Code

- **Status:** **ACCEPTED (design, 2026-07-22). CODEX-FIRST IMPLEMENTATION AUTHORIZED; CLAUDE CODE ACTIVATION DEFERRED.** Codex may be enabled immediately. The shared infrastructure MUST be Claude-compatible, but Claude configuration/plugin changes MUST NOT be activated or declared verified until a live Claude Code validation window is available, no earlier than the week of 2026-07-27. Legacy Claude behavior remains the rollback path until that validation passes.
- **Decider:** John Roehm (project owner) — approved the three-slot, orchestrator-owned-build posture and the Codex-first/Claude-later rollout on 2026-07-22.
- **Investigation and draft:** Codex, following an adversarial review of the current workspace, the pinned `lean-lsp-mcp` implementation, and the relevant public Claude-plugin commit history.
- **Scope:** the public `SK_EFT_Hawking` Lean substrate, product-neutral local slot infrastructure, Codex integration, and a privacy-preserving extension point for private downstream repositories. Repository-specific private configuration and paths remain in private overlays and MUST NOT be committed here.
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
| **S-C — Cross-client lease is the authority** | Every active slot has one fail-closed lease containing at least: schema version, slot number, repository role, client (`codex` or `claude`), owner/session token hash, base ref and base SHA, worktree path, endpoint identity, acquired/heartbeat timestamps, lease state, and—when downstream—its exact public dependency SHA. Lease creation/transfer MUST use an atomic filesystem primitive; implementations MUST NOT assume `flock` exists on macOS. Prompt text and Claude goal markers are advisory projections of this lease, not competing authorities. |
| **S-D — Fixed-root HTTP endpoints** | Each repository/worktree has a stable, repository-qualified streamable-HTTP endpoint bound to `127.0.0.1` and protected by an uncommitted bearer credential. Both products connect to the same endpoint for that project/worktree; no endpoint is duplicated per client. An endpoint MUST NOT be hot-rebound between public and downstream projects. A global gate MUST prevent more than three heavy Lean LSP/REPL backends across the numbered slots, even if more lightweight HTTP front doors are configured. |
| **S-E — Worker endpoint tool policy** | `lean_build` MUST be removed server-side from worker endpoint tool listings, then denied again by each client's worker tool policy. Shell `lake build`/`lake clean` MUST likewise be unavailable to worker roles. Defense is layered because client hooks are guardrails, not the sole enforcement boundary. Main/orchestrator validation uses an explicit orchestrator command path, never the worker endpoint. |
| **S-F — REPL is initially disabled** | Codex-first endpoints launch without `--repl`. Shared REPL is a later optimization, not an activation dependency. It may be enabled only after the pinned fork provides one lazy, project-scoped REPL per daemon (or an equivalently bounded design), serializes stateful access, resets it at lease/build boundaries, and passes two-client concurrency and teardown tests. Per-session REPL subprocess multiplication is not acceptable. |
| **S-G — Successful-build epochs replace HEAD-only stamps** | A slot cache is current only when it matches an orchestrator-published successful-build epoch. A public epoch includes the public commit SHA plus Lean toolchain and Lake manifest/dependency fingerprints. A downstream epoch additionally includes the exact public dependency SHA and the downstream fingerprints. The orchestrator MUST stop/park the slot LSP, clone the authoritative `.lake` to a temporary sibling, atomically install it, then restart service. It MUST NOT delete or replace `.lake` beneath a live LSP, and MUST NOT publish an epoch before the authoritative build succeeds. |
| **S-H — Downstream slots are paired, not assumed nested** | A private overlay is responsible for placing its worktree so its relative public path dependency resolves to the public half of the same numbered slot. During a downstream lease, that public half is pinned at the lease's `public_dependency_sha` and treated read-only. Acquisition MUST refuse a dirty or mismatched public dependency. The public implementation exposes the pairing protocol but contains no private repository name, path, endpoint, or credential. |
| **S-I — Integration is serialized and ancestry-safe** | `slotctl absorb` (or its exact equivalent) is orchestrator-only and protected by an integration lock. It verifies a clean committed slot, rebases the slot branch onto the current authoritative base when necessary, and then fast-forwards the primary checkout. It never cherry-picks, force-pushes, or discards unmerged work. A conflict or unexpected ancestry enters `QUARANTINED` state for explicit orchestrator resolution. After absorption, the orchestrator runs the authoritative gate, publishes a new epoch, rewarms the slot, and releases it. |
| **S-J — Versioned specification, generated local configuration** | Product-neutral controller/supervisor code, schemas, tests, and public endpoint templates live in this repository. Private endpoint mappings live only in a private overlay. Workspace-root Claude/Codex MCP configuration is generated local state with a source digest. `slotctl doctor` MUST report drift rather than silently overwriting operator configuration. Credentials, leases, PIDs, logs, and epochs are gitignored runtime state. |
| **S-K — Codex first; Claude activation gated** | Codex configuration, agents, and worker policies are implemented and tested first. The shared controller, supervisor, lease schema, endpoint naming, and generated-config interface MUST already admit a later Claude client. Claude plugin/config changes are a separate activation phase requiring live tests; until then, the existing Claude plugin and stdio launch path remain unchanged. No Claude compatibility claim may advance from “designed” to “verified” without those tests. |

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

1. A process/session token is generated outside Git and supplied to the MCP client through an environment-backed bearer header. The lease stores only its hash.
2. Every slot-affecting controller command verifies the token, repository role, worktree realpath, branch, and lease state.
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

The shared infrastructure is Claude-ready when it provides stable HTTP URLs, bearer-header input, the lease API, generated `.mcp.json` data, and product-neutral status/doctor output. During the current usage-limit window:

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
6. A released lease token cannot call tools through an existing HTTP session.
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

1. One Claude session and multiple Claude subagents share the configured HTTP endpoints without spawning per-agent stdio servers.
2. Claude worker tool policy denies builds and integration, while the lead can invoke the controller workflow.
3. Claude reconnect after endpoint restart preserves or cleanly reacquires the intended lease and never changes project root.
4. Claude-only three-slot work passes without ENFILE or process accumulation.
5. One Claude worker and one Codex worker can operate on different leased slots concurrently; attempts to share a slot are denied.
6. Session restart/plugin-cache refresh behavior is documented and verified.
7. Only after all tests pass may the legacy stdio entries and manual off-repo `pkill` procedure be retired.

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

- Ensure the supervisor exposes stable Claude-compatible HTTP endpoints and environment-backed bearer headers.
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

**Risks and mitigations.** A controller bug could strand a slot; fail-closed quarantine and non-destructive recovery are mandatory. A bearer token identifies a session but does not replace filesystem/Git checks; the endpoint verifies both. Lightweight endpoint processes may outnumber active slots, but the global heavy-backend semaphore—not process-name counting—is the resource invariant. The host vnode increase provides headroom but is not used as a substitute for lifecycle control.

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
