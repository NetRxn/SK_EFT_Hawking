# Pre-Decisions — the standing decisions the loop applies WITHOUT asking

Decisions already made, so an autonomous `/goal` loop — and the in-time coach — apply them
instead of stalling or escalating. **Canonical, tracked, human-curated.**

> **Home.** Lives in `docs/` (not the plugin) so `/debrief` graduates a new pre-decision by editing
> THIS file alone — no plugin cache refresh. Grown by `/debrief`: generalize a human-reviewed
> System-2 finding → a crisp *"when X → do Y"* → merge/supersede, never a near-dup.

Two layers — robust to an **unbounded and growing** number of pre-decisions (the whole point of the
`/debrief` graduation pipeline), because the pre-decisions are **NO LONGER injected** into the
post-compaction payload. They are a **MANDATORY READ**: the SessionStart re-inject's `FIRST_ACTION`
directive makes "read this file" step 1 of every post-compaction turn. So they grow without any
payload-budget pressure (`CORE_MAX_CHARS` retired).

- **Core** = the always-on keystones — what the mandatory read targets first. Terse on purpose (it's
  the fast-read set), but **no longer byte-bounded**: it's read, not injected, so it can't starve the
  payload.
- **Full** = the deep reference — situational rules + the graduated long tail; read on-demand (the
  coach reads it; the loop reads it when a situation matches). This is where growth mainly goes.
- The **tier-2 coaching block** (harvest-authored, per-goal) is the relevance layer: it surfaces the
  pre-decisions *relevant to this goal's current state* (e.g. PD-1 on a stall) so the loop needn't
  re-read Full every turn. It is an OPTIONAL enhancement (absent for a new goal until the first
  harvest, and it ages between runs), so the mandatory read of this file is the baseline.

Keep Core terse anyway (it's the fast-read essentials). Rungs, rationale, and worked examples live in
Full / the System-2 register.

## Core (the mandatory-read essentials — keep terse; no longer byte-bounded)

### PD-0 — Scale/difficulty are pre-accepted *(keystone)*

The budget/scope/acceptance call was made when `/goal` was invoked. **"Bigger/harder/longer than I
thought" is NEVER grounds to stop, ask for a continuation, or re-scope** — climb the ladder (PD-1)
instead. A prohibition without a constructive path just becomes a grind.

### PD-1 — When a step resists: zoom out, then climb the ladder *(don't grind, don't stop)*

Zoom out first (goal + roadmap + notebook INDEX FRONTIER + DECISIONS/DEAD-ENDS), then climb the lowest
rung that fits — **A** load context · **B** toehold-sweep the whole substrate *(≠ re-altitude)* · **C**
research a known gap (`research-scout`) · **D** decompose + bank · **E** forensic arc-trace
(`/skeft-qa:trace`). **Escalate, two classes only:** *process-gap* → make the best call now (`/debrief`
graduates it); *genuine external-value call* → `AskUserQuestion` (logged though denied; never self-veto).
*(Rung detail → Full.)*

### PD-2 — Bank a tracked hypothesis only with a *mechanical* discharge

Bankable **iff** it gates ≥1 real downstream theorem in the atlas (non-empty `dependent_theorems`),
one scoped Prop per **wave/objective boundary**. A mid-stall unbacked discharge plan isn't trustworthy
— arc-trace (E) first. Never ship a project-local axiom without sign-off. *(Detail → Full.)*

### PD-3 — Legitimate stops (only two) + anti-escape

**Stops, ONLY two:** a kernel-checked no-go, or a genuine user-only decision (ask once, keep shipping).
**STOP if you write:** "Holding" · "awaiting direction" · "fresh session" · "multi-day" · "no
foothold/wall" · any context-budget reasoning. Not your job to manage the context window; never
re-pollute the roadmap/notebook with escape-language.

### PD-4 — At a compaction/session boundary, re-anchor before resuming

The compaction summary optimizes *tactical continuity over strategic anchoring* — it freezes the
mid-air rewrite and drops the close-path, **re-seeding the thrash**. On resume, FIRST re-anchor
(notebook FRONTIER + critical-path / close-path), THEN act; the summary's mid-flight line is **not
authoritative** (resume it only if it still matches the close-path).

## Full (coach-readable / on-demand — folded from the former decision-heuristics.md; grown by `/debrief`)

### Why PD-0 (the failure it prevents)

The dominant failure mode: realize a step is bigger than expected → want a human call → the question
is dropped → thrash. 5q.F *had* the "disregard scale / don't stop" posture and still thrashed for
days — because a prohibition alone relocates the failure into a grind. PD-0 pairs the prohibition with
PD-1's construction. (Full RCA: the System-2 register meta-finding.)

### Why PD-4 (the compaction-summary bias)

Two independent L2 post-mortems — a fresh forensic trace AND a separate parallel re-run — found the
*same* re-seed: the session resumed at a compaction boundary, the summary surfaced a mid-flight
tactical line (`boundaryExtract`; earlier `CrossReal`) as the "active" work and dropped the trace's
strategic close-path, so the loop pushed the divergent route and burned ~6 turns rediscovering the
settled strategy before correcting. The failure mode is **robust to both a fresh trace and a
compaction** — which is exactly why the guard must be a STANDING boundary procedure, not a one-time
insight. Operationalized two ways: the **tier-2 re-orientation brief** leads every pass with this
goal's current close-path (the specific, per-goal form); PD-4 is the general always-on backstop. The
summary is optimized to resume mid-edit (tactical continuity); *which node closes the goal* (strategic
anchoring) is what it drops — and for a residual whose difficulty is route-choice, that is the exact
bias that re-seeds the thrash.

### The diligence-then-decide frame (expanded PD-1)

1. **Zoom out.** Re-read the goal condition, roadmap, and lab-notebook **INDEX** (FRONTIER +
   DECISIONS & DEAD-ENDS — settled forks / kernel-checked no-gos live there); open a shard only for
   load-bearing detail, and read the source then, not a summary.
2. **Search before concluding.** Lean: `lean_local_search` → `lean_leansearch` / `loogle`. Prior
   decisions: the roadmap + the relevant `Lit-Search/Phase-*/` deep-research file — **read it
   directly; do not delegate depth-reading to a subagent** (summaries drop coefficient identities /
   sector architectures).
3. **Reason about the tradeoffs** explicitly.
4. **If one option is clearly best, TAKE IT** and log the rationale in the lab notebook.
5. **Only if a *significant* tradeoff has *no* clear pre-decision, ask ONCE** (the external-value
   class) — and keep shipping everything else meanwhile.

### The PD-1 ladder rungs (expanded)

- **A — Load context:** `goal-dev` + `lean4` + the residual's references (friction catalog, DR file,
  notebook arc).
- **B — Toehold-sweep *(≠ re-altitude)*:** query the atlas / read-only Explore over the **whole**
  substrate (incl. archives + seemingly-unrelated areas) for a committed node that closes/implies the
  residual. Re-altitude = the *same* residual at a different level — try both.
- **C — Research early:** a *known* result local search lacks → `research-scout` / `/deep-research`;
  stage state and keep shipping meanwhile.
- **D — Decompose + track:** large step → provable sub-steps; bank what works **and** what fails.
- **E — Forensic arc-trace (`/skeft-qa:trace`):** lost in the arc → full read-only trace to disk +
  synthesis (also what makes a later bank-or-grind escalation trustworthy).
- **Escalation, two classes only:** *process-gap* = a graduation trigger, not a stall (make the best
  call now; `/debrief` graduates it). *Genuine external-value call* (risk budget / change the goal /
  right target) = `AskUserQuestion` (logged even though denied — don't self-veto; rare).

### The research path — Tier 1 (don't reinvent a known result)

When step-2 local search is dry **and** the gap is a *known* result: dispatch **`research-scout`** (or
`/deep-research`) — the only web-tool holder, read-only / sandboxed, returns a **structured cited
report**, never raw page content. **You (lead) vet** it, then **file** it into `Lit-Search/…` with a
provenance header and keep building (web facts stay `tier: PROJECTED` until a primary source is
checked; the Lean kernel is the terminal verifier). **Sanitize the question** to its public
math/physics core first. The slow `Lit-Search/Tasks/submitted/` human dispatch is the **last** resort.

### Scope to the consumer (anti over-build)

Before building a component, check what its **downstream consumer actually needs** and build exactly
that minimal deliverable — not a more general abstraction. The consumer's interface defines the scope.

### Don't block on info-gathering — dispatch a read-only Explore in parallel

On a **large architectural unknown**, dispatch a read-only `Explore` agent in parallel and **keep
building the independent part solo**. Explore reads and reports, never edits; it runs a lighter model
and can echo the loop's anti-patterns — **treat its output as leads to vet, not conclusions.**

### Graduated pre-decisions (appended by `/debrief`)

_(empty — the long tail of `when X → do Y` rules graduated from human-reviewed System-2 findings)_
