# Tracked follow-on: System-1 orphan → System-2 adoption triage

> **Status: TRACKED FOLLOW-ON (demoted from the harness build's critical path — spec Plan 3
> Task 7 Step 3).** Not yet executed. No System-1 schema change is involved or permitted.

## What

System-1 (the paper-correctness QI graph) has **~500 / 918 `ReviewFinding` nodes with no
`FLAGS` edge** (invisible to the readiness gates + `qi_register` clustering). Of these, the
genuinely **dev-loop / harness-flavored** subset is **System-2-shaped** and should migrate
into the System-2 register at `human-reviewed`. Per the firsthand trace (snapshot §9a/§9c):

- **~70 `unclassified`** orphans + items like **`qi-vizdiscipline`** (the plotly-hrect-on-log-axes
  tooling gotcha) are the **dev-loop/harness-flavored** adoptable slice → migrate to System-2.
- The **~70 `NarrativeGrounding`** orphans are **paper-narrative correctness** = System-1's
  domain → they **stay** System-1's to fix (a better `_infer_paper_key_from_text`, or an explicit
  `paper:` frontmatter key). NOT adopted.
- The other ~350 correctness orphans are System-1 inference misses → not System-2.

## Why it's a follow-on, not inline

Each candidate orphan needs a **human judgment** call (is this really a dev-process lesson, or a
paper-correctness finding that merely failed paper-inference?). That judgment lands at the
`human-reviewed` tier by definition, so the migration is naturally a `/skeft-qa:debrief`-style
human pass — not an automated build step.

## Acceptance (when executed)

- A documented count: how many of the ~70 `unclassified` orphans were judged dev-loop/harness
  and migrated to `docs/dev-loops/SYSTEM2_REGISTER.md` at `human-reviewed`.
- **No System-1 schema change** (read the orphans; do not mutate `ReviewFinding`/the graph/AGE).
- The `NarrativeGrounding` orphans remain System-1's (record that they were excluded by design).

## How (when picked up)

1. Query the orphaned `ReviewFinding` nodes lacking a `FLAGS` edge (read-only) and filter to
   `unclassified` + `qi-vizdiscipline`-like process/tooling findings.
2. For each, decide dev-process vs paper-correctness; migrate the dev-process ones via
   `echo '<finding-json>' | uv run python scripts/system2_register.py --upsert` at
   `"tier": "human-reviewed"`.
3. Record the triaged count here; leave System-1 untouched.
