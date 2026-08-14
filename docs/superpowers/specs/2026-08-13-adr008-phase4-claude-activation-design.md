# ADR-008 Phase 4 — Claude Code live activation

**Status:** design, 2026-08-13. Implements the seven-item *Claude activation change set* in
[ADR-008](../../adrs/ADR-008-shared-lean-slot-control-plane.md) § *Claude Code — prepare now,
activate later*, and is bound by decisions **S-A** through **S-K** there. Numbering below is
`P4-n` and is cited from the plan and from ADR-008's amendment.

---

## 1. Measured state at HEAD (`5e764ec6`, 2026-08-13)

Every figure here is derived from the live artifact, not from ADR-008's 2026-07-22 text.

| Fact | Measurement | Instrument |
|---|---|---|
| Claude HTTP MCP entries | **not built** — `Controller.render_config` writes only `.codex/config.toml`; `source_digest` hashes only `.codex/*`; `doctor` checks only `config.repo` / `config.workspace` | `scripts/lean_slots/controller.py:846-897, 993-1000` |
| Workspace Claude transport | all six servers stdio; `lean-lsp-wt{1,2,3}` spawn `uvx` per session, each with `--repl` | workspace `.mcp.json` |
| Lead acquires a lease | **nowhere** — no plugin agent, command or skill mentions `slotctl`, a lease, or `acquire` | grep over `.claude/plugins/skeft-qa/` |
| Worker single-module build exception | live in three places | `agents/lean-worker.md:60`, `skills/goal-dev/SKILL.md:93`, `skills/goal-dev/references/parallel-worktrees.md:76-83` |
| Worker Bash guard | ships and denies `lake build` to subagents | `scripts/harness_worker_shell_guard.py` |
| Plugin version | `.claude-plugin/plugin.json` has **no `version` key** | `plugin.json` |
| Build epoch | published `6fc5d77c…` for `5e764ec6` | `slotctl build` |
| Endpoints | proxies 1/2/3 up; backends 1 and 3 up, 2 correctly suppressed | `slotctl supervisor start` |
| wt2 slot | held by a **private** `QUARANTINED` lease carrying 2 unabsorbed commits | `.lean-slots/leases/wt2.json` |
| Host vnode ceiling | **`kern.maxvnodes = 263168`** | `sysctl -n kern.maxvnodes` |

Two of these contradict ADR-008's own text and are corrected in its amendment:

- ADR-008 § *Context* asserts the host "has since been raised to `kern.maxvnodes=786432`". It is
  **263168** — the raise did not survive a host reboot. The three-slot posture therefore rests on
  lifecycle control alone, which is what ADR-008 § *Risks* already says it must ("the host vnode
  increase provides headroom but is not used as a substitute for lifecycle control"). Nothing in
  the design depends on the larger value; the ADR's factual claim is what is wrong.
- ADR-008 change-set item 3 names a "compile-feedback *unbounded build lane*". **No surface by
  that name exists.** Its residue is the narrow single-module worker build exception, which the
  guard shipped earlier today already denies — so item 3 is a prose-reconciliation task, not a
  removal task.

### 1.1 The endpoint contract, measured

`slotctl supervisor probe --slot 1` and a direct `tools/list` against `127.0.0.1:8761`:

- **21 tools**, `lean_build` absent — S-E is enforced server-side, not only by client policy.
- `lean_multi_attempt`, `lean_goal`, `lean_diagnostic_messages`, `lean_verify` all present, so the
  worker's binding proof loop survives the transport change. The endpoints run without `--repl`
  (S-F), so REPL-backed behaviour behind `lean_run_code` is the one capability at risk; it is not
  on the worker's binding path and is an acceptance-test item, not a blocker.
- `active_dispatch: false` — **tool dispatch is lease-gated.** In trusted-local mode `proxy.py`
  requires a `?client=` query parameter and rejects the call unless the active lease's `client`
  field equals it (`proxy.py:56-61, 101`).

That last point is the load-bearing one: **the MCP entries are inert until the lead acquires a
lease with `--client claude`.** Item 2 of the change set is therefore a correctness requirement,
not documentation polish — without it every Claude worker gets a connected server whose every tool
call fails closed.

---

## 2. Decisions

### P4-1 — The Claude renderer owns a key block, not the file

The workspace `.mcp.json` is shared: it also defines the primary `lean-lsp`, a downstream project's
server, and `codex`. A whole-file renderer would destroy configuration this repository does not own,
which S-J forbids ("`doctor` MUST report drift rather than silently overwriting operator
configuration").

The renderer therefore owns exactly a **named managed block** inside `mcpServers`:

- **adds** `skeft_wt1`, `skeft_wt2`, `skeft_wt3` — `{"type": "http", "url":
  "http://127.0.0.1:<proxy_port>/mcp?client=claude"}`, ports read from
  `config/lean-slots.public.json`, never hand-listed;
- **removes** `lean-lsp-wt1`, `lean-lsp-wt2`, `lean-lsp-wt3`;
- **preserves every other key byte-for-byte, in its original order.**

Endpoint names mirror the Codex side (`skeft_wtN`) because S-D requires one endpoint per
project/worktree shared by both products, not one per client.

⚠️ The ports are derived from the inventory rather than copied into a template. The Codex template
hard-codes them, which is a second place for a port to drift; the Claude path does not repeat that.

### P4-2 — Rollback is a snapshot, not a second live config

ADR-008 item 7 requires retaining the legacy stdio path until the acceptance gate passes. Keeping
the stdio entries *live alongside* the HTTP ones would preserve exactly the
`clients × configured servers` multiplication that item 1 exists to remove (ADR-008 § *Alternatives*
2), so "retain" is satisfied by recoverability, not by coexistence.

Before its first managed write the renderer captures the pre-activation `mcpServers` block to
`.lean-slots/generated/claude-mcp.rollback.json`. `--rollback` restores it verbatim. The snapshot is
written **once** and never overwritten by a later render, so a second activation cannot destroy the
original legacy definition.

### P4-3 — `doctor` gains `config.claude`

A drift check alongside `config.repo` / `config.workspace`: it compares the live managed block to
the rendered one and reports, never writes. Drift states it distinguishes:

| state | meaning |
|---|---|
| `current` | managed block matches the render |
| `not activated` | no `skeft_wt*` keys and the legacy stdio keys are present — the pre-activation state, reported OK |
| `drifted` | managed keys exist but differ from the render |
| `partial` | some managed keys present, others missing |

`not activated` is OK rather than FAIL because Phase 4 is reversible by design: a rolled-back
workstation must not report a broken control plane.

### P4-4 — Claude activates at 2 of 3 slots

Slot 2 is held by a private `QUARANTINED` lease carrying two unabsorbed commits. The public
controller **cannot** resolve it — `reclaim` fails closed on repository-role mismatch
(`controller.py:621-625`) — and must not: S-C makes quarantine non-destructive and ADR-008 Phase 1
already pre-decides "use only currently clean/available slots; capacity increases automatically as
protected work is resolved."

`skeft_wt2` is still rendered. The endpoint exists and is lease-gated; a Claude `acquire` on slot 2
fails closed on the existing lease, which is the designed behaviour and needs no separate guard.

### P4-5 — The lead acquires; the worker never does

Per-sub-chain lead flow, replacing the current `/reset-slot N` → dispatch pair:

```
slotctl acquire --slot N --client claude --base-ref main
slotctl prepare --slot N          # resets to base, installs the epoch's .lake, backend up, → ACTIVE
  → dispatch lean-worker at mcp__skeft_wtN__*
slotctl ready   --slot N          # worker committed
slotctl absorb  --slot N          # rebase + ff-only + authoritative build + epoch + rewarm + release
```

`prepare` subsumes what `/reset-slot` did — it resets the worktree to the base and installs a
`.lake` matching the published epoch — and adds the epoch check `/reset-slot`'s HEAD-SHA stamp could
not make (S-G). `/reset-slot` remains for slots being driven outside a lease.

`absorb` is orchestrator-only and ancestry-safe by construction: it rebases and fast-forwards, never
cherry-picks (S-I, and the `62e8da08` lesson the current prose already carries).

### P4-6 — The worker single-module build exception is retired

`agents/lean-worker.md:60`, `skills/goal-dev/SKILL.md:93` and `parallel-worktrees.md:76-83` grant a
worker one `lake build SKEFTHawking.<Module>`. The shipped guard denies it unconditionally to
subagents, so the grant is unexecutable prose that instructs a worker to attempt a denied command.

It is replaced by the mechanism that actually exists: **the worker reports the module it needs
built; the lead builds it.** ADR-008 item 3's "only no-build decomposition/research remains
unbounded" is thereby satisfied.

`parallel-worktrees.md:38` — "this plugin ships no Bash guardrail" — is false as of today and is
corrected in the same commit.

---

## 3. Non-vacuity

Each new mechanism ships with a test that seeds the defect into the **production artifact**, per
`CHECK_AUTHORING_GUIDE.md` §2.4:

| mechanism | seeded defect | expected |
|---|---|---|
| `config.claude` drift | rewrite a rendered `skeft_wtN.url` port in a real `.mcp.json` copy | `drifted` |
| `config.claude` partial | delete one `skeft_wtN` key | `partial` |
| managed-block preservation | render over a file carrying unrelated servers | unrelated keys and their order unchanged |
| rollback snapshot | render twice | snapshot still holds the **pre-activation** block |
| client identity | render and assert every URL carries `?client=claude` | matches the lease `client` `proxy.py` compares against |

## 4. Out of scope

- **Resolving wt2's private quarantine.** Private-overlay work; the public side cannot and must not.
- **Change-set item 5** (projecting the protocol into a private Claude plugin) — private overlay.
- **Enabling `--repl` on the endpoints** — S-F defers it behind its own concurrency tests.
- ~~**`backend_policy: "leased"`** for the public inventory.~~ **SHIPPED 2026-08-14 as ADR-008 S-L**,
  after measurement showed the standing cost was ~4.4 GB per used slot rather than the ~114 MB an
  unused one suggested — a Lean server is spawned lazily but never reclaimed, so it persisted from
  first use until `supervisor stop`.

  ⚠️ **Both of this section's earlier claims about the obstacle were wrong, and both were derived by
  reading rather than running.** The first said `prepare` would strand a slot because `paused_backend`
  consults `backend_expected`; it does not. The correction then said `paused_backend` "restarts the
  backend unconditionally", so nothing blocked the policy. What it actually does is call
  `assert_healthy` **at entry**, which requires a running *backend* — a state a freshly-acquired
  leased slot legitimately lacks, making `prepare` unreachable under the policy. The downstream
  fixture never surfaced it because the paired path uses `activating_from`, not `paused_backend`.
  Entry now asserts only proxy health (`Supervisor.assert_proxy_healthy`).

  Measured full cycle after the fix: idle 0 MB → `prepare` 0 MB (Lean server still lazy) → worker
  active 4336 MB → `release` 0 MB, reclaimed automatically. Peak concurrency is unchanged.
- **Retiring the legacy stdio path and the session-start `pkill` procedure** — ADR-008 Phase 5,
  gated on the acceptance tests passing.
