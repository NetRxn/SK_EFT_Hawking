# Lab-notebook lifecycle (create → maintain → shard → re-orient)

The lab notebook is the **one source-of-truth brick log** for a `/goal` loop (live brick-state;
the marker is captured-once at launch). It is **progressively disclosed** and the plugin maintains
it for you via the `/skeft-qa:notebook` command (`scripts/notebook_lib.py`). You should rarely touch
its structure by hand — author the *content*, let the tool keep the *scaffold* correct and the active
shard **under the ~25k-token Read guard automatically**.

> **Why a two-layer model (read this once).** Sharding fixes *size*, not *retrieval*. The expensive
> recurring failures are retrieval failures — **re-exploring a dead-end, re-deriving a settled
> decision, frontier drift** — because writes are chronological but reads are topical. So the
> high-value topical content lives in a small **always-loaded INDEX that is never sharded away**;
> the chronological shards are the audit trail, read on demand.

## Layout

```
<per-loop home>/                   # DEFAULT docs/dev-loops/<roadmap>/ (in-repo; notebook git-ignored → leak-safe).
                                   # OVERRIDABLE (goal-prompt `notebook=<dir>`) e.g. workspace Lit-Search/<phase>/.
├── goal_prompt_<goal_id>.md       # the durable /goal condition (TRACKED; one per goal; never overwrite)
├── LAB_NOTEBOOK_INDEX.md          # ← THE ENTRY POINT (injection + /orient read this FIRST). DURABLE layer.
├── LAB_NOTEBOOK.md                # the ACTIVE shard (most-recent bricks; oldest first). AUDIT layer.
└── LAB_NOTEBOOK_W1.md … _W<n>.md  # frozen historical shards (older waves). AUDIT layer.
```

## 1. Create — at inception, not when it's already a mess

A new loop's notebook is scaffolded **at arm time** by `goal-prompt` (which calls `notebook new`), so
progressive disclosure exists from turn 1. If you ever find a loop without an INDEX, create one:

```
/skeft-qa:notebook new          # bootstrap-if-missing; resolves the home from the marker
```

`new` is idempotent — it creates a correct active `LAB_NOTEBOOK.md` **and** `LAB_NOTEBOOK_INDEX.md`
when either is absent and **never clobbers** existing files. The marker's `notebook_path` points at the
**INDEX** (the entry point), not the active shard.

**Home + leak-safety.** The home **defaults to `docs/dev-loops/<roadmap>/`** (in-repo: stable paths, and the
pre-commit `notebook check` applies). It is **overridable** at arm time (`goal-prompt notebook=<dir>`) for a
loop whose notebook already lives elsewhere — e.g. `Lit-Search/<phase>/` — which is used **as-is, never
moved**. Either way the notebook files (`LAB_NOTEBOOK*.md`) are **git-ignored and NEVER committed**: they are
auto-written in full-`/goal` mode, so committing them risks leaking private content into public git. The
tracked, durable, reviewable artifact is `goal_prompt_<goal_id>.md`; the notebook is regenerable live state.

## 2. The INDEX — the durable, always-loaded layer (keep it ≤ ~150 lines / ~6 KB)

Four live blocks. The SessionStart re-injection and `/orient` land on this file FIRST; it must never
go stale.

1. **FRONTIER** (≤15 lines, edited **every brick**) — last-committed SHA + uncommitted/untracked state;
   the single next brick as a numbered item; any open error/wall; any blocked decision. Record the SHA as
   `HEAD=<sha>` so `notebook check` can flag drift.
2. **DELIVERABLES CHECKLIST** — GFM checkboxes (`- [x]`/`- [ ]`) synced to present state. Flip a row the
   moment its deliverable lands. (`new` seeds these from the roadmap's acceptance criteria.)
3. **DECISIONS & DEAD-ENDS** — **append-only; never sharded.** One line per settled fork or kernel-checked
   no-go: `DATE — claim → CHOSEN/REJECTED/NO-GO: why [lemma|commit]`. **This is the antidote to
   re-attempting a known-wrong path.** When you settle a fork or prove a no-go, **promote it out of the
   transient FRONTIER into here** — the FRONTIER gets overwritten next brick, so a decision left only in
   FRONTIER evaporates (exactly how the "re-explored a dead-end" failure happens).
4. **SHARD INDEX** — one line per shard, **newest first**, each **topic-tagged** (which deliverable / wave
   it covers) so deliverable→shard retrieval works when you do need the deep trail.

## 3. Maintain — per brick (cheap; do not skip)

After each brick, in the SAME turn it is committed (so the frontier never drifts from git):
- **Edit the INDEX FRONTIER** + flip any completed CHECKLIST row.
- **Append the long detail bullet** to the active `LAB_NOTEBOOK.md` under **its own heading**
  (`### <date> — <brick>`), **terse** — one tight paragraph, *not* a 1 KB single line. Heading-per-brick
  is what keeps the shard splittable; a single un-headed mega-section can't be sharded (only `roll`-ed).
- **If you settled a fork / hit a no-go**, append one line to **DECISIONS & DEAD-ENDS**.
- Run `notebook sync` to refresh the mechanical scaffold (shard rows; ensures the DECISIONS block exists)
  and surface any staleness.

`sync` maintains the *scaffold*, never your judgement prose (FRONTIER / CHECKLIST / DECISIONS are yours).

## 4. Shard — automatic, under the budget

At your incremental-commit checkpoint (every ~5–6 bricks), keep the active shard small:

```
/skeft-qa:notebook shard        # rolls the OLDEST headed sections into LAB_NOTEBOOK_W<n> until < budget
/skeft-qa:notebook roll         # freeze the WHOLE active shard (clean wave boundary / un-headed blob escape)
```

`shard` keeps the most-recent bricks in the active shard and self-levels it under the token budget
(`BUDGET_BYTES` ≈ 72 KB ≈ 18k tokens — margin under the 25k Read guard). It needs per-brick headings; if
the active shard is one un-headed blob it will tell you to head the entry or `roll`. `roll` freezes the
entire active shard into a new `W<n>` and starts a fresh active — the INDEX FRONTIER carries current
state, so a fresh active is fine.

A read-only `notebook check` also runs in the **SessionStart re-injection** and the **pre-commit gate**, so
an oversized active shard or a stale FRONTIER can't go silent. **No hook ever mutates the notebook** —
`sync`/`shard`/`roll` self-level only when you invoke them (self-improving, never self-mutating).

## 5. Re-orient — INDEX first

On every session start / post-compaction, read `LAB_NOTEBOOK_INDEX.md` FIRST — its FRONTIER + CHECKLIST +
DECISIONS give the live state and the settled forks in one read. Open the active shard only if the
FRONTIER is insufficient; open a frozen `W<n>` only for deep audit (use the topic-tagged SHARD INDEX to
pick the right one). `/skeft-qa:orient` does exactly this.

## Discipline (the non-negotiables)

- **One source-of-truth log.** In a team loop the lead curates (workers report up); in a solo loop the
  loop is its own lead.
- **Heading-per-brick.** Each brick is its own `### ` (or `## ` wave) heading so the active shard stays
  shardable. Terse entries — verbose 1 KB lines re-bloat the shard.
- **Promote decisions out of FRONTIER.** A settled fork / no-go belongs in DECISIONS & DEAD-ENDS
  (append-only), not only in the FRONTIER that gets overwritten.
- **Never re-pollute.** The notebook records *what happened*, not escape-bait. Do **not** write
  "person-year / precluded / wall / multi-day, next session" into it. Record kernel-checked no-gos
  factually (with the lemma that proves them) in DECISIONS, not as morale commentary.
- **Never commit the notebook.** `LAB_NOTEBOOK*.md` is git-ignored on purpose (leak-safe); do **not**
  `git add -f` it. Commit your Lean/autogen paths as usual — the notebook persists on local disk across
  compactions; git is not its backup (the tracked `goal_prompt_<goal_id>.md` is the durable source).

## Why in-repo (git-ignored) + sharded + two-layer

In-repo default home → **stable paths** (a goal prompt's self-describing paths don't rot, and the
pre-commit `notebook check` applies). **Git-ignored** → the auto-written notebook is **never committed**, so
it can't leak private content into public git in full-`/goal` mode (the tracked durable artifact is the
small, reviewable `goal_prompt_<goal_id>.md`). Sharded → the active log stays small enough that a fresh
post-compaction turn re-reads it cheaply. Two-layer → the content that prevents re-work (FRONTIER /
CHECKLIST / DECISIONS) is always loaded and never buried in time-ordered history.
