# Wave 2 brief — verify the escalated clusters

Wave 1 read the transcript and produced 89 raw findings across eight slices. Its agents saw only a
*process spine* — user messages, assistant prose, tool-call signatures, tool errors. They did not
read the repository. Their findings are therefore **claims about what was said**, not established
facts about the machine.

Your job is to convert claims into verified facts, and to kill the ones that do not survive.

**Window:** t0 = 2026-08-15 09:46 CDT to HEAD (`4c81c2ec`). The plugin actually running in that
window is cache `f33dc0a1b2e5` = commit `f33dc0a1`. Four plugin commits post-date it and were never
loaded: `fd6cac3d`, `e9e5e314`, `c4b1a1ca`, `f58a3fe4`. **A defect that one of those four already
fixes is ALREADY ADDRESSED — say so and kill it.** That distinction is the whole point of the audit.

## Inputs

- Wave-1 reports: `docs/audits/2026-08-17-process-review/wave1/{A..H}.md` — read the ones for your
  cluster's cited IDs, in full.
- Process spine: `/private/tmp/claude-501/-Users-johnroehm-Programming-PythonEnvironments-Physics-Fluid-Based-Physics-Research/6cf37aa2-f1c7-4e33-a712-f17c2d75d99b/scratchpad/audit/spine/`
  (`main-2026-08-15.md` lines 8378+, `main-2026-08-17.md`) and `.../audit/sub/` (redraft-lead spines).
- **The repository itself** — this is what wave 1 could not use. `scripts/validation/checks/`,
  `scripts/`, `docs/architecture/`, `docs/adrs/`, `papers/*/`, `.claude/plugins/skeft-qa/`, git log.

## The test each claim must pass

For every finding in your cluster, answer all four. A claim failing any of 1–3 is **KILLED**.

1. **Real?** Does the defect exist in the tree at HEAD right now? Show the code, the line, the
   command output. Not the transcript — the tree.
2. **Unaddressed?** Was it fixed after it was observed — by a later commit in the window, or by one
   of the four unloaded plugin commits? Check `git log` on the touching path.
3. **Correctly diagnosed?** Wave 1 named a cause. Is that cause the actual one? A wrong diagnosis
   with a real symptom stays alive but gets **re-diagnosed** by you, with evidence.
4. **How big?** Measure the population the defect actually touches — how many bundles, checks,
   briefs, records. Run the command. A number quoted from wave 1 is a claim; re-derive it.

## Output

Write to the path in your assignment, one section per cluster finding:

```
### <CLUSTER>-NN — <defect stated as a mechanism, not a story>

- **Wave-1 source IDs:** e.g. G-02, C-06, E-6
- **Verdict:** CONFIRMED | RE-DIAGNOSED | ALREADY-ADDRESSED | KILLED
- **Evidence at HEAD:** file:line + the command you ran + its output. Required.
- **Population:** the measured blast radius, with the command that measured it.
- **Already-addressed by:** commit SHA, or "no"
- **Mechanism:** what in the machine produces this, in two or three sentences
- **Recurs on the next bundle?** YES | NO, and why
```

Then return **only** a compact table: ID, verdict, population, recurs.

## Rules

- Every number you state must come from a command you ran in this session. Quote the command.
- Read-only. Do not edit anything except your own report. Do not commit. Do not run `lake build`.
- If a claim is about physics correctness rather than process, say so and drop it — this audit is
  about the machine, not the manuscripts.
- Prefer killing to keeping. A finding that survives your pass will be acted on; a false one costs
  more than a missed one at this stage.
