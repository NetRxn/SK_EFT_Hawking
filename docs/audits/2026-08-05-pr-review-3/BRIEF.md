# PR review pass 3 — `infra/adr-009-validation-modularization`

**Date:** 2026-08-05 · **Head:** `db430c65` · **Base:** `main` · **117 commits, 136 files,
+36 631 / −8 102.**

## Why a third pass

Passes [1](../2026-08-04-qa-qi-infrastructure/) (53 findings) and
[2](../2026-08-05-pr-review-2/) (6 reviewers, 5 YES-WITH-FIXES + 1 NO) both closed with every
Critical/Major addressed. **Then, within one working session, three further defects of the
branch's own signature class were found** — not by auditing the checks, but by measuring the
corpus independently for ADR-010 and noticing the numbers disagreed:

| commit | defect | scale |
|---|---|---|
| `c7148779` | `prose_theorem_reference_coverage` matched only `\texttt{}`; D8/D9 write every Lean reference through `\newcommand{\lean}[1]{\texttt{#1}}` | **288** references never scanned |
| `c5f384b4` | same check could not see `\verb`; D6 writes **235** of those against 25 `\texttt` | **276** more |
| `9f62deaa` | `check_bundle_source_freshness` scored an **absent** source directory as fresh | **9** bundles, fully vacuous PASS |

**Verified before commissioning this pass: none of these appears anywhere in the pass-1 or pass-2
corpora.** They are genuine misses, not re-derivations of something already known.

The check reported `21 bundle drafts scanned / 671 candidate Lean references` throughout. It was
671 of 1 051. **A count of what was scanned is not evidence that the population was reached** —
and two review passes, including one built specifically to find "absence of measurement rendered
as success", did not catch it.

## The question this pass exists to answer

> **Where else is an instrument on this branch pointed at a population it does not actually
> reach — and would we know?**

Secondary: are the three repairs themselves correct, and are the ADR-010 measurements published on
their strength trustworthy?

## Rules

1. **You have your own worktree** (`.claude/worktrees/rvN`, detached at `db430c65`). Work only
   there. Pass 2 ran six reviewers on a shared tree and left a stubbed check body and a zero-byte
   `paper_draft.tex` mid-run; two reviewers had to defend findings by reading `git show HEAD:`.
2. **Write your report to disk** at
   `docs/audits/2026-08-05-pr-review-3/reviewer-reports/RN-<slug>.md`, in the MAIN checkout, not
   your worktree. Pass 1 lost 53 findings to a transcript.
3. **Severity:** CRITICAL / MAJOR / IMPORTANT / MINOR. For each: file:line, what breaks, the
   concrete failing input, and how you verified it. **An unverified claim must say so.**
4. **Verify by execution, not by reading.** The house standard (QI-30) is: seed the defect in the
   **production artifact**, run the thing, watch it fail, restore. A mutation caught against a
   fixture proves the test works, not that the check can fail in production.
5. **A count is meaningless without its predicate.** State the predicate for every number.
6. **A failed reproduction is itself a measurement that can be wrong.** This branch's history has
   three cases where the *checker* was broken, not the claim. Before filing "X is wrong", confirm
   your own instrument reaches the population.
7. Do not fix anything. Report only.

## Orientation

- `docs/architecture/VALIDATION_ARCHITECTURE.md`, `VALIDATION_GATE_TOPOLOGY.md`,
  `CHECK_AUTHORING_GUIDE.md`, `QA_QI_INFRASTRUCTURE_MAP.md` — the branch's own account of itself.
  **Treat these as claims to be checked, not as ground truth.**
- `docs/adrs/ADR-009-validation-suite-modularization.md` — decision record + §Deferred 0–7.
- `docs/adrs/ADR-010-publication-portfolio-reassessment.md` +
  `docs/audits/2026-08-05-adr010-measurement/MEASUREMENTS.md` — the new measurement claims.
- `uv run python scripts/validate.py --list` — the live check roster.

Current state: suite **5 575 passed / 5 skipped / 0 failed**; `validate.py` **58/60**, substrate
clean, both reds attributed to the paper corpus.
