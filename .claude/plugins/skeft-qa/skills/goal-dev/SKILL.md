---
name: goal-dev
description: >
  In-loop development guidance for an autonomous /goal Lean-proof loop in SK_EFT_Hawking. This skill
  should be used when developing Lean 4 proofs inside a goal loop, deciding whether to fan work out to
  parallel worktree slots or stay solo, resetting a worktree slot, hitting a recurring Lean tactic/
  elaboration friction, or sharding the lab notebook. It surfaces the MCP-first proof loop, kernel-purity
  rules, the worktree fan-out flow, and a symptom-indexed friction catalog. Invoke it at the start of a
  development stretch and whenever you hit proof-mechanics friction or need the parallel-dev recipe.
---

# Developing in a `/goal` loop (the in-loop dev skill)

This is the **in-loop** companion to `goal-prompt` (which only *authors* the goal at launch). Invoke this
skill while doing the work; its references load on demand. **Project conventions in
`SK_EFT_Hawking/CLAUDE.md` are canonical and override the generic `lean4` skill** where they differ.

## Posture (the always-on stance)

Scope is **SETTLED** — do the next increment of real work THIS turn. A stop-hook firing is a **GO** signal,
never a cue to stop/hold/re-scope/hand-back. Legitimate stops are **only**: a kernel-checked no-go (build
around it; carry one scoped disclosed Prop + a discharge plan) or a genuine user-only decision (ask once,
keep shipping meanwhile). It is **not your job to manage the context window** — auto-compaction is handled;
quality does not drop across a compaction boundary. Full rationale + worked negative examples:
`references/decision-heuristics.md`.

## The MCP-first proof loop (milliseconds/cycle, not ~15s write→lake-build)

1. `lean_file_outline` → orient. 2. Write the statement with `sorry`; save. 3. `lean_goal` at the `sorry` —
**see the actual goal**. 4. `lean_multi_attempt` 4–6 candidate tactics; pick the winner. 5. Write it; repeat
from 3. 6. `lean_goal` → "no goals" ⟹ drop the `sorry`; `lake build` to finalize. **Search before prove**
(`lean_local_search` first). Hard rules, Aristotle-fallback policy, preemptive-strengthening, and the
substrate-specific gotchas: `references/lean-dev.md`.

**Kernel-purity is the bar (non-negotiable):** target axioms exactly `{propext, Classical.choice,
Quot.sound}`; **no new project `axiom` without explicit user sign-off**, no new `sorry` / `native_decide` /
`maxHeartbeats`. Verify each substantive brick with `lean_verify`. A heartbeat wall ⟹ wrong architecture →
decompose into `have` sub-lemmas (≤ 12-term targets).

## Incremental-commit discipline

**Maximize per-turn throughput.** Land the maximum coherent GREEN progress each turn — as many bricks as you
can finish cleanly, not one; don't artificially atomize (fewer, bigger turns amortize per-turn overhead and
reach auto-compaction slower). The commit cadence below is an **orthogonal safety checkpoint** (rollback +
notebook durability), **not a per-turn cap**.

Commit a **GREEN kernel-pure increment** every ~5–10 bricks (each: zero sorry, `lean_verify` clean, `lake build`
clean) — batches of finished bricks, never one giant commit — updating the lab notebook each brick; the
notebook is the **compaction-durable source-of-truth**.
**Never push** (user action). The notebook is a two-layer system (a bounded always-loaded INDEX +
chronological shards); maintain it with the **`/skeft-qa:notebook`** command — `sync` each brick, `shard`
at the checkpoint to keep the active shard under the ~25k-token Read guard automatically. Each brick is its
own `### ` heading; settled forks / kernel-checked no-gos go in the INDEX's append-only DECISIONS block.
**Encode-on-settle (ADR-007 N-E, Invariant #17):** a *kernel-CHECKABLE* no-go additionally lands a backing
refutation/forcing theorem + a `KERNEL_NOGO_REGISTRY` entry (`src/core/constants.py`) in the settling turn —
NOT a prose line alone (prose-only recording of a kernel-encodable fork is itself a `nogo_substrate_integrity`
finding). Policy / route / preference bans stay prose in `SETTLED_FORKS.md` (not kernel-encodable).
Full model + per-brick discipline: `references/lab-notebook.md` (the lead curates; workers report up).

## Consult the atlas — BOTH fronts (`/skeft-qa:frontier`)

The atlas (`lean/atlas_view.json`, derived — cannot drift) is the machine-truth of the substrate, both signs:
- **Positive frontier** (ADR-005 D-I) — the ranked OPEN assumptions; consult it to **aim fan-out** at the
  highest-impact provable work (the KEYSTONE) instead of roadmap-opaque selection.
- **Negative frontier** (ADR-007 N-D) — the ranked **settled-dead forks** (kernel-checked, with their
  `false_statement`); consult it to **steer AWAY** from provably-false paths. Both are re-injected in the
  SessionStart digest and available on demand via `/skeft-qa:frontier`; the two binding project no-gos are
  `lattice_arf_bridge_refuted` + `dataBordism_two_torsion_of_revStr_trivial`.

## Solo vs. fan-out

Keep a **tightly-coupled single-file chain solo** with one fast MCP — that is faster than coordinating. Fan
out **only when the DAG has genuinely branched** into independent sub-chains. To fan out, as `lead`:

1. **`/reset-slot N`** — resets worktree slot `wtN` to `main`, the **guardrail-safe** way. ⚠️ Never reach for
   `git reset --hard` / `git clean` on a slot — the auto-mode permission classifier denies them (it's a
   Claude Code heuristic, not a dev-harness hook). `/reset-slot` refuses if the slot holds unmerged commits,
   so nothing is lost.
2. `Agent(subagent_type="skeft-qa:lean-worker", prompt="SLOT N=…, use mcp__lean-lsp-wtN__*, <one independent
   sub-chain/BLOCK — as large as is coherently independent — + Lit-Search refs + acceptance + any relevant
   kernel no-go from the NEGATIVE frontier the worker must not re-derive>")` — up to 3 concurrent. Hand
   workers **as-large-as-coherent blocks**, not atomic bricks (bigger blocks = fewer dispatch/merge/reread
   cycles + higher per-worker throughput). A fresh worker is the highest-risk re-deriver — **name the
   dead-forks in its brief.**
3. Merge each `worktree-wtN` into `main`; re-run the full gate; `/reset-slot N` again for the next brick.

**⛔ You own `lake build`; workers do not.** Slot `.lake` isolation buys correctness, not contention
relief — Lake takes one job per core, so 3 building slots is 3× the machine. Measured 2026-07-28: three
concurrent slot builds stretched the lead's ~15 s pre-commit hook past **10 minutes**, which reads
exactly like a broken toolchain and isn't. Workers gate on `lean_diagnostic_messages` / `lean_goal` /
`lean_verify` (per-file, near-free); **you** run `lake build`, `lake build SKEFTHawking.ExtractDeps`, and
`validate.py` on `main` after the merge. Only exception: a worker adding a NEW module another file must
`import` may run `lake build -j4 SKEFTHawking.<ThatOneModule>` — one named module, job-capped, reported.

Full flow, why the slots are persistent, and the maintainer caveat: `references/parallel-worktrees.md`.

## When a proof-mechanics error recurs

**Grep `references/lean-friction-catalog.md` for the symptom** (motive-not-type-correct, `Subsingleton ℝ`,
`ext` over-unfolding, `ring` on `•`, quotient `mk`-coercion, free-variable capture, …) before re-deriving
the fix. Add a new entry the *first* time a pattern recurs.

## References (load on demand)

- `references/lean-dev.md` — the full MCP loop, hard rules, Aristotle policy, substrate gotchas.
- `references/lean-friction-catalog.md` — symptom-indexed tactic/elaboration frictions.
- `references/parallel-worktrees.md` — worktree-slot fan-out flow + `/reset-slot`.
- `references/decision-heuristics.md` — the settled-scope / anti-escape stance, with worked examples.
- `references/lab-notebook.md` — lab-notebook lifecycle (create / maintain / shard / re-orient), the
  two-layer INDEX model, and the `/skeft-qa:notebook` ops.
