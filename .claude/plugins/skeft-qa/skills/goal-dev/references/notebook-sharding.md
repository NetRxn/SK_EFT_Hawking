# Lab-notebook + sharding discipline

Loaded on demand when the lab notebook for a `/goal` loop grows large. The notebook is the
**one source-of-truth brick log** for the loop (live brick-state; the marker is captured-once
at launch). It lives in the tracked per-loop home:

```
<repo>/docs/dev-loops/<roadmap>/
├── goal_prompt_<goal_id>.md     # the durable /goal condition (one per goal; never overwrite)
├── LAB_NOTEBOOK.md              # the active brick log (+ shards below)
├── LAB_NOTEBOOK_W4.md           # a shard (older waves)
└── LAB_NOTEBOOK_INDEX.md        # the shard index
```

## Discipline

- **One source-of-truth log.** Record each brick: what shipped, the commit, the key
  decision + rationale, and any open thread. This is what `/skeft-qa:orient` and the
  SessionStart re-injection point at — keep it current and honest.
- **Each checkpoint must survive compaction.** Write enough that a *fresh* post-compaction turn
  re-grounds with zero re-derivation: **(a)** the exact last-committed SHA + any **uncommitted
  file state**, **(b)** known **errors/warnings** still open, **(c)** the **next brick as a
  numbered item**, **(d)** any **blocked decision with its arguments**. A checkpoint missing these
  costs a 4–5-turn re-orientation; one that has them is a seamless resume.
- **The lead curates.** In a team loop, workers report up; the lead writes the canonical
  notebook. In a solo loop, the loop is its own lead.
- **Shard as it grows.** When the active `LAB_NOTEBOOK.md` crosses its size budget (keep the
  *active* shard readable in one glance — roughly a few hundred lines), roll the older
  content into `LAB_NOTEBOOK_W<n>.md` and start a fresh active shard. Keep the most recent
  bricks in the active shard so a post-compaction re-read lands on current state.
- **Index-sync (do not skip).** After sharding, update `LAB_NOTEBOOK_INDEX.md` with a
  one-line pointer per shard (wave range + dates) so the history stays navigable. A shard
  with no index entry is lost history.
- **Never re-pollute.** The notebook records *what happened*, not escape-bait. Do not write
  "person-year / precluded / wall / multi-day, next session" into it — that is the exact
  5q.F re-pollution failure. Record kernel-checked no-gos factually (with the lemma that
  proves them), not as morale commentary.

## Why tracked + sharded

Tracked → **stable paths** (a goal prompt's self-describing paths don't rot). Sharded →
the active log stays small enough that a fresh post-compaction turn can re-read it cheaply
and re-ground on current state rather than wading through the whole history.
