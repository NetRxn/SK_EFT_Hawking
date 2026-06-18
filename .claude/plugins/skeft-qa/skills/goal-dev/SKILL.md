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

## Shard-and-commit discipline

Commit a **GREEN kernel-pure shard** every ~5–6 bricks (each: zero sorry, `lean_verify` clean, `lake build`
clean), updating the lab notebook each brick — the notebook is the **compaction-durable source-of-truth**.
**Never push** (user action). When a notebook shard crosses its size budget, follow
`references/notebook-sharding.md` (the lead curates; workers report up).

## Solo vs. fan-out

Keep a **tightly-coupled single-file chain solo** with one fast MCP — that is faster than coordinating. Fan
out **only when the DAG has genuinely branched** into independent sub-chains. To fan out, as `lead`:

1. **`/reset-slot N`** — resets worktree slot `wtN` to `main`, the **guardrail-safe** way. ⚠️ Never reach for
   `git reset --hard` / `git clean` on a slot — the auto-mode permission classifier denies them (it's a
   Claude Code heuristic, not a dev-harness hook). `/reset-slot` refuses if the slot holds unmerged commits,
   so nothing is lost.
2. `Agent(subagent_type="skeft-qa:lean-worker", prompt="SLOT N=…, use mcp__lean-lsp-wtN__*, <one independent
   brick + Lit-Search refs + acceptance>")` — up to 3 concurrent.
3. Merge each `worktree-wtN` into `main`; re-run the full gate; `/reset-slot N` again for the next brick.

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
- `references/notebook-sharding.md` — lab-notebook sharding + index discipline.
