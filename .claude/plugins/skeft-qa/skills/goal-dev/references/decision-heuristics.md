# Decision heuristics for an autonomous `/goal` loop

The expanded form of the in-loop summary (`harness_common.DECISION_HEURISTICS`). Loaded on
demand. The governing principle: **the stop hook is a GO signal, never coercion** — when it
fires and the goal is not met, that means *do the next increment of real work THIS turn.*

## The diligence-then-decide ladder (when you feel blocked)

1. **Zoom out.** Re-read the settled goal condition, the roadmap, and the lab-notebook tail
   directly (not a summary — for load-bearing detail, read the source).
2. **Search before concluding.** For Lean: `lean_local_search` → `lean_leansearch`/`loogle`.
   For prior decisions: the roadmap + the relevant `Lit-Search/Phase-*/` deep-research file
   (read it directly; do not delegate depth-reading to a subagent — summaries drop
   coefficient identities / sector architectures).
3. **Reason about the tradeoffs** explicitly.
4. **If one option is clearly best, TAKE IT** and log the rationale in the lab notebook.
   Do not stall waiting for permission you do not need.
5. **Only if a *significant* tradeoff has *no* clear pre-decision, ask ONCE** — and keep
   shipping everything else meanwhile. A deep-research dispatch is an async external
   dependency: dispatch it and **keep working** on whatever else is shippable.

## Don't block on info-gathering — dispatch a read-only Explore in parallel

On a **large architectural unknown** (an interface you don't yet know, a subsystem to map before
the next brick), **dispatch a read-only `Explore` agent in parallel and keep building the
independent part solo** — don't stall the loop waiting for the map. Explore reads and reports; it
never edits, so it runs safely alongside your own work. This is **distinct from the lean-worker
fan-out** in `parallel-worktrees.md` (which dispatches *proof* bricks to worktree slots) — Explore
is read-only reconnaissance: no worktree, no MCP slot. Fold its findings in when it returns; they
often surface a load-bearing gap you hadn't anticipated.

## Legitimate stops (the only two)

- A **kernel-checked no-go**: a result the Lean kernel refutes (e.g. a proved no-go lemma),
  or a genuinely impossible-in-current-Mathlib path with a documented argument.
- A **genuine user-only decision**: a choice only the user can make (policy, scope change,
  an axiom sign-off, an external dependency). Ask once; keep shipping.

## Anti-escape trip-wires (STOP if you catch yourself writing these)

"Holding" · "awaiting direction" · "this needs a fresh session" · "this is multi-day so I'll
stop" · "the hook is coercion" · "person-year / precluded / no foothold / wall" · any
context-budget or "how much is left" reasoning. **It is not your job to manage the context
window** — auto-compaction is handled safely; quality does not drop across a compaction
boundary; a single goal may cross compaction many times, shipping bit by bit.

If you are about to write "should I continue?" / "multi-day, next session" / "awaiting your
compress" → that IS the antipattern. Delete it and do the next brick. **Never re-pollute the
tracked roadmap/notebook with escape-language** (the exact Phase-5q.F failure mode).
