# Parallel Lean development — persistent worktree slots (per-worker LSP)

Loaded on demand when a `/goal` proof program **branches into independent sub-chains** and the `lead`
wants to fan bricks out. (A tightly-coupled single-file chain stays **solo** with one fast MCP — fan out
only when the DAG has genuinely branched.)

Each brick goes to the **`lean-worker` subagent** (`skeft-qa:lean-worker`), one per **persistent worktree
slot**. Each slot has its **own** build-isolated lean-lsp server, so several workers run **fully in parallel
with zero coordination**.

| Slot | Worktree (gitignored) | Its endpoint |
|---|---|---|
| `wt1` | `SK_EFT_Hawking/.claude/worktrees/wt1/lean` | `mcp__skeft_wt1__*` |
| `wt2` | `…/wt2/lean` | `mcp__skeft_wt2__*` |
| `wt3` | `…/wt3/lean` | `mcp__skeft_wt3__*` |

**Why persistent static slots (not inline per-subagent MCP):** inline `mcpServers` in subagent frontmatter
**do not surface** via the Agent tool in this environment (verified empirically). Only **inherited**
`.mcp.json` servers surface to subagents, and those attach at **session start** — so the slot worktrees must
already exist when you launch. Pre-create the slots once, keep them. Disk is cheap — each slot's `.lake` is an
APFS `cp -c` clone (copy-on-write): 3 slots ≈ **~500 MB real** (`du` shows ~43 GB *logical* — COW-blind).

**One-time setup:** `scripts/setup_lean_worktree_slots.sh` creates `wt1/2/3`. The three `skeft_wtN`
endpoints are shared streamable-HTTP front doors on loopback, generated into the workspace `.mcp.json` by
`slotctl config render --client claude` and served by `slotctl supervisor start` — one process per slot for
the whole workstation, not one per client or per subagent. **Restart after first setup** so they attach.

⛔ **The endpoints are lease-gated.** Every tool call is rejected unless slot `N` holds an ACTIVE lease whose
`client` is `claude`. A connected server with no lease is not a working slot — it fails every call. Acquire
first (step 1); this is why a dispatch without a lease fails immediately rather than degrading.

**A leased slot gives a worker the FULL tool surface** — 21 tools, everything the MCP-first loop
needs. The only removal anywhere is `lean_build`. An *unleased* endpoint advertises no tools, which
is the "there is nothing here yet" signal, not a restriction on workers: a worker is only dispatched
into a slot already leased and prepared.

**A slot's Lean server is a consequence of its lease.** `prepare` starts the backend; the Lean server itself
spawns lazily on the first tool call and costs **~4.4 GB** (`lake serve` + `lean --server` + `lean --worker`,
measured). `release` / `absorb` reclaim it automatically. So an idle slot costs nothing, a full swarm costs
~13 GB at peak, and you never need to remember `supervisor stop` to get the memory back.

⚠️ **Before a full swarm, run `slotctl doctor`.** A concurrent swarm memory-maps thousands of `.olean` files
per slot, which consumes kernel **vnodes** — not file descriptors, so `ulimit -n` will tell you everything is
fine while the real ceiling binds. `doctor` asserts the declared floor and prints the exact command to fix a
shortfall. Persistence (it is a runtime setting, lost on reboot) is in the slot operator guide.

## Lead's flow (per independent sub-chain)

1. **Acquire and prepare the slot — IMMEDIATELY before dispatching *this* slot's worker**, per task, **not
   as a batch up front.** A slot prepared early goes stale the moment `main` advances (e.g. you merged an
   earlier worker).
   ```bash
   uv run python scripts/slotctl.py acquire --slot N --client claude --base-ref main
   uv run python scripts/slotctl.py prepare --slot N
   ```
   `prepare` resets the worktree to the base, installs a `.lake` matching the **published successful-build
   epoch**, and brings the slot's backend up — so the slot's LSP always matches its git tree. It refuses on
   a dirty slot or unabsorbed commits, moving the slot to `QUARANTINED` rather than discarding work.
   - ⚠️ **Do NOT reach for `git reset --hard` / `git clean`** on a slot. Those are denied by the auto-mode
     permission classifier on a worktree the agent didn't create this session.
   - **`/reset-slot N`** remains for a slot you are driving **outside** a lease. It does the guardrail-safe
     `checkout -B` and re-clones `.lake` staleness-gated on main's HEAD SHA, but it cannot check the build
     epoch — prefer `prepare` whenever the slot is leased.
2. **Dispatch** `Agent(subagent_type="skeft-qa:lean-worker", prompt="SLOT N=2, path=<abs …/wt2>, use
   mcp__skeft_wt2__*. <the one independent brick + its Lit-Search refs + acceptance>")`.
3. The worker proves MCP-first via **its own `mcp__skeft_wtN__*`** (never write→`lake build`), kernel-pure,
   and **commits on `worktree-wtN`**. **The worker runs no builds — you do** (next section).
4. **Harvest:**
   ```bash
   uv run python scripts/slotctl.py ready  --slot N     # audits: clean, committed, on the lease's base
   uv run python scripts/slotctl.py absorb --slot N     # rebase → ff-only → build → epoch → rewarm → release
   ```
   `absorb` holds an integration lock, so two slots finishing together are serialized rather than racing.
   It **rebases and fast-forwards, never cherry-picks** — a cherry-pick mints a new SHA, leaving the slot's
   original commit content-merged but not a SHA-ancestor of `main`, which makes the next reset's
   ancestry guard refuse the slot. For a worker that finished with no commits, use `release --slot N`.
   The slot stays for the next task — never delete it.

Dispatch up to 3 workers concurrently (one per slot) for genuinely independent bricks.

**Capacity is whatever `slotctl status` says is FREE.** A slot showing `QUARANTINED` — including one held by
another repository against the same slot number — is not available, and acquiring it fails closed. Run
`slotctl doctor` before a fan-out.

## ⛔ Build concurrency: the LEAD owns `lake build`. Workers do not. (binding)

Slot isolation is about **correctness** — each slot has its own `.lake`, so a slot build can't corrupt
main's. It buys you nothing on **contention**: Lake defaults to one job per core, so every slot that
builds tries to take the whole machine.

Measured 2026-07-28 on a 16-core box: three workers building concurrently pushed the lead's pre-commit
hook — ~15 s solo, ~90 % user-CPU — past **10 minutes**, and the lead started backgrounding its commits
to keep moving. Nothing was broken; the machine was oversubscribed, and the cost landed squarely on the
serialized process that gates everyone. It also reads exactly like a broken toolchain, so it burns
diagnosis time before anyone suspects load.

**The contract:**
- **Workers run no builds.** Their gate is `lean_diagnostic_messages` + `lean_goal` + `lean_verify` —
  per-file, near-free, and sufficient for "does this elaborate / close / stay kernel-pure". This is
  written into `agents/lean-worker.md` as a binding rule; **say it again in the dispatch brief** if a
  worker is likely to add a module.
- **The lead runs `lake build` / `lake build SKEFTHawking.ExtractDeps` / `validate.py`** — on `main`,
  after the merge, or through `slotctl absorb`, which serializes it under the integration lock and
  publishes the epoch the next `prepare` installs. That is the run that counts; a slot's green build
  proves nothing about `main`.
- **A worker that needs a NEW module importable reports the module name; the lead builds it.** There is
  no worker-side build, capped or otherwise.

  ⚠️ **Lake has no job cap.** There is no `-j`, `--jobs`, `--threads`, `-K` key or lakefile
  field for parallelism, and Lake has no scheduler of its own: it spawns build jobs onto the
  Lean task-manager pool, sized by `get_lean_num_threads()` — one per logical core by default.
  A single-module build is far cheaper than the bare target but is still unbounded, which is why
  it is not delegable.

  `LEAN_NUM_THREADS` is the only lever, and it is soft, not a `make -j`: a blocked pooled
  worker raises the ceiling, `Task.Priority.dedicated` bypasses the pool, and Lake does not
  override it for child processes, so it bounds Lake's pool and each child `lean`'s pool.
  Measure before relying on it.

  **One build at a time, run by the lead, is the stronger guarantee and the primary control.**

**Layered enforcement, not prose alone:** `lean_build` is absent from the endpoint's tool list
server-side; a `PreToolUse(Bash)` guard denies `lake build|clean|update`, cache mutation and
integration commands to subagents (never to the lead); and `slotctl absorb`/`build` hold locks that
serialize whatever survives. Matching policy applies on the Codex side, and a cross-client test
asserts both deny the same command set.

> **Maintainer caveat (do not regress):** a worker's slot commit depends on `scripts/pre-commit-sync.sh`
> detecting a worktree (`git rev-parse --git-dir` ≠ `--git-common-dir`, env-resolved so it survives the shared
> hook's `cd` to main) and **skipping** the main-oriented sync gate — the pure-bash leak-guard still runs. Do
> **not** make that gate always-run: in a worktree it stitches a cloned dependency's top-level `.github/*`
> blobs (absent from SK's object store) into the slot's commit tree → `invalid object … Error building trees`,
> blocking every slot commit.

> **Launch note:** works from **either** launch point — the workspace root (where `.mcp.json` lives) or inside
> `SK_EFT_Hawking/`. The lead manages slots with plain `git -C <slot>` (no `isolation: worktree`), so there is
> no non-git-cwd problem; the endpoints are loopback URLs and serve regardless of the lead's cwd.
>
> ⚠️ **Run `slotctl` from the primary checkout.** It resolves its inventory, state root and lease directory
> from the current working directory, so invoking it from inside a slot silently addresses a different
> control plane and reports every slot FREE.
