# The six reviewer reports, recovered verbatim

**These files are the primary record.** [`../README.md`](../README.md) and
[`../PR_REVIEW_2026-08-05.md`](../PR_REVIEW_2026-08-05.md) are summaries *of* them, and the
summaries lost most of their content.

## Why this directory exists

Six `general-purpose` reviewer subagents ran on 2026-08-05 against
`infra/adr-009-validation-modularization`. Their four Criticals were transcribed to disk
(they became QI-31…QI-34, now fixed). **Their non-Critical findings were not.** The handoff
recorded the phrase *"~17 Important findings … See the review record"* — and no review record
existed. The reports lived only in the session transcript.

Recovered 2026-08-05 by reading
`~/.claude/projects/…/6cf37aa2-f1c7-4e33-a712-f17c2d75d99b/subagents/agent-*.jsonl` and
extracting each agent's final assistant message unedited.

## The count was wrong by about 3×

| reviewer | focus | verdict | Important |
|---|---|---|---|
| [R1](R1-architecture-and-correctness.md) | architecture and correctness | with fixes | 6 |
| [R2](R2-test-quality.md) | test quality | with fixes | 5 |
| [R3](R3-deferred-scope.md) | deferred scope | **No** — with fixes | 9 |
| [R4](R4-enforcement-efficacy.md) | enforcement efficacy | **No** | **11** |
| [R5](R5-coverage-adequacy.md) | coverage adequacy | partially adequate | 6 |
| [R6](R6-test-appropriateness.md) | test appropriateness (holistic) | partially | 16 † |
| | | **total actionable non-Critical** | **53** |

† **R6 uses no severity labels at all** — its findings are grouped as *Mismatches* (M1–M9)
and *Untested seams* (S1–S7). That is why they contributed **zero** to a count obtained by
grepping for the word "Important", and it is most of the gap between 17 and 53.

A further **48 Minor** findings (R1 #8–15, R2 #8–12, R3 M1–M6, R4 M1–M10, R5 M0–M4) are in
these reports and are not in the consolidated register.

## What the summaries lost outright

Three artifacts, each the most reusable output of its review, existed nowhere else:

- **R4's "checks that CANNOT fail (or cannot fail in production)" table — 17 rows.** Four
  became QI-31…QI-34. **The other 13 rows were gone.**
- **R5's invariant → mechanism → verdict table — 17 rows** (4 enforced, 10 partial, 2
  prose-only, 1 prose-only-and-violated).
- **R6's bad-wave walkthrough** — a stage-by-stage trace of a wrong number, a mis-stated
  theorem and a figure contradicting its caption each surviving all fourteen pipeline stages.

## The lesson, which is the same one this audit is about

A finding that lives only in a summary is a finding that has been deleted at an unknown
future date. The summary said *"See the review record"*; the review record was a sentence
naming five of fifty-three. **Persist the reviewer's own words at dispatch time, not a
paraphrase at close time** — and never write a count you have not derived from the artifact.
