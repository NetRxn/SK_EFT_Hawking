# pr-review-toolkit round — 2026-08-10

**Why this directory exists.** A closure reviewer, correctly barred from accepting this
loop's own prose as evidence, reported condition 7 **UNVERIFIABLE**: the only record that
this round ran lived in the handoff and two ledgers, all inadmissible, and the newest
on-disk reviewer artifact was four days and ~100 commits older than HEAD. **A review with
no artifact is indistinguishable from a claim that one happened.** That was a fair call and
this directory is the remedy.

## What ran

Two passes, in this order.

### Pass 1 — the CHUNKED exhaustive review (21 chunks)

The first six-agent pass dispatched every agent over the **whole** 451-file diff, so each
necessarily sampled; the union of six samples is not a complete review. It read as 100%
because six agents ran.

The replacement partitions the reviewable surface into **21 disjoint chunks** — no overlap,
no gap, verified at generation — sized so an agent can read all of its chunk. The partition
is machine-recorded in [`review_chunks.json`](../../architecture/.working-docs/review_chunks.json)
and its status in
[`REVIEW_COVERAGE_LEDGER.md`](../../architecture/.working-docs/REVIEW_COVERAGE_LEDGER.md).

| | files | lines | outcome |
|---|---:|---:|---|
| total diff | 451 | 177,921 | — |
| generated/binary (excluded, each generator reviewed) | 72 | 84,733 | — |
| **reviewable, partitioned** | **379** | **93,188** | 21/21 chunks closed |

Yield: **~250 findings, 11 BLOCKERs**, in code the whole-diff pass had nominally covered.

### Pass 2 — the six NAMED toolkit agents over the branch diff

`code-reviewer`, `silent-failure-hunter`, `pr-test-analyzer`, `type-design-analyzer`,
`comment-analyzer`, `code-simplifier`. Each was briefed with what pass 1 had already fixed
so it hunted the NEXT defects rather than re-reporting closed ones.

Yield: **72 findings** — 2 BLOCKER, 23 MAJOR, 19 IMPORTANT, 28 MINOR.

## What it found that mattered

The recurring shape across both passes was **a guard that could not fail**:

| defect | why it mattered |
|---|---|
| a compile-gate verdict written for a run that compiled nothing (`pdflatex` absent → `compile_gate_ok: true` for all 21 bundles) | BLOCKER; and it was covered by no test — reverting the fix left 85 tests green |
| a CRASHED paper-side check let `--scope substrate` exit 0 printing "SUBSTRATE: clean" | `gate_precheck s13-lean` runs exactly that command |
| the `--ci` coverage floor counted registry entries, not MEASURED checks | the floor exists to catch a suite that silently shrank |
| `Detail.measured` silently reset to `True` on every memo replay | positional round-trip over 4 of 5 fields |
| the production-graph guard was bypassable, aimed at prod, AND deselected from the default run | three independent failures in one test, any one re-arming a 49,003-vertex wipe |
| `proxy_body_audit`'s scanner anchored at column 0 | blind to 8.1% of the corpus; `@[simp]`, `private`, indented all invisible |
| `\totaltheorems` published 3,729 compiler-generated declarations as authored | reached readers in I1's abstract |

## Reading the evidence

Findings are recorded where they can be checked, not narrated here:

* **fixes** — the commit series on this branch, each carrying its reproduction
* **measurements that refuted a filed finding** —
  [`ACCURACY_LEDGER.md`](../../architecture/.working-docs/ACCURACY_LEDGER.md) V81 (E2 over-ceiling,
  REFUTED), V82 (`@[simp]` projections)
* **coverage** — `REVIEW_COVERAGE_LEDGER.md`, per chunk
* **what remains** — `ARCHITECTURE_TODOs.MD`, incl. TODO-D39 (a scheduled circle-back)

⚠️ **This README is prose and therefore not evidence for itself.** Every number in it is
re-derivable from the repo; a reader who needs to trust it should re-derive rather than read.
The counts above come from the agent transcripts of this session, which are not committed —
so treat the *findings* as verified (each fix carries a reproduction) and the *totals* as
this document's own claim.
