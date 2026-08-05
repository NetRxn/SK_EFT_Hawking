# PR review, pass 2 — shared reviewer brief

**Branch:** `infra/adr-009-validation-modularization`
**Base:** `main` @ `c2b597e1` — **99 commits, 114 files, +28,374 / −7,797**
**Repo root:** `SK_EFT_Hawking/` (run everything from there)

You are one of six independent reviewers. Do not coordinate; another reviewer covering the
same ground differently is the point.

---

## 1. Write your report TO DISK. This is not optional.

Write it yourself, with the `Write` tool, to:

```
docs/audits/2026-08-05-pr-review-2/reviewer-reports/<YOUR-ID>.md
```

**Why this is rule #1.** Pass 1 (2026-08-05, same branch) ran six reviewers whose reports were
returned only as chat messages. Four Criticals got transcribed; **53 non-Critical findings did
not**, and the handoff recorded the phrase *"~17 Important findings"* — wrong by 3× — pointing
at a "review record" that did not exist. They were recovered days later only by mining
`~/.claude/projects/**/subagents/agent-*.jsonl`. Your returned message is a **summary**; the
file is the artifact. If you run out of room, the file wins.

## 2. Severity vocabulary — use these exact words

`CRITICAL` · `MAJOR` · `IMPORTANT` · `MINOR`

Label **every** finding with exactly one. Pass 1's sixth reviewer used its own scheme
(*"Mismatches M1–M9 / Untested seams S1–S7"*) and contributed **zero** to a count obtained by
grepping for "Important" — that alone was most of the 17-vs-53 gap. Give each finding a stable
id: `<YOUR-ID>-C1`, `-MAJ1`, `-I1`, `-MIN1`.

## 3. Every finding must carry a measurement, not an impression

For each: **file:line · what it claims · what it actually does · how you verified · blast
radius.** "How you verified" means a command you ran and its output — `rg`, a `python -c`, a
`pytest -k`, a seeded mutation. A finding you could not verify is still worth filing: mark it
`UNVERIFIED` and say what would settle it.

This repo's standing rule: **a filed finding's count, consumer and effort are CLAIMS.** If you
assert "N call sites" or "this has no test", produce the count. Reviewers in pass 1 filed
counts that were wrong in both directions.

## 4. The defect class this branch exists to fight

**"Absence of measurement rendered as success."** A check, test or guard that reports PASS
while measuring nothing. Its many faces, all found in this repo already:

- a check whose verdict is computed then discarded (`passed=True` unconditionally);
- an early return on a missing artifact / absent toolchain that yields PASS;
- a test asserting against a patched fixture, where the production artifact would not fire it
  (**QI-30's criterion: seed the defect in the PRODUCTION artifact**);
- a glob / filter / regex that silently narrows the population being checked;
- a hand-maintained list parallel to a registry, which drifts;
- a cache or skip that hits across the very change it should have caught;
- a *document* describing a repaired guard as broken, or a broken guard as fine.

## 5. New surface landed 2026-08-05 — in scope, attack it

`scripts/validation/_memo.py` (input-fingerprint memoization) and the `paper_latex_compiles`
per-draft cache make checks **report PASS without running**. That is deliberately the defect
class above, made load-bearing. Assume it is wrong and try to prove it:

- Can you construct a change that moves a check's verdict but **not** its key?
- `axiom_closure_allowlist` key = Lean sources + toolchain/Mathlib pin set + `AXIOM_METADATA`
  + `update_counts.is_native_decide_axiom` + the body's own source. What input is missing?
- `_draft_input_closure` — what can change a LaTeX compile outcome that it does not hash?
- Do the tests in `tests/test_validation_memo.py` seed *production* or a fixture?

## 6. Read before you review

- `docs/audits/2026-08-04-qa-qi-infrastructure/FINDINGS_REGISTER.md` — pass 1's 53 findings,
  ~40 still OPEN. **Re-filing an open one is useful** (it confirms it survived); say so
  explicitly with its id so reconciliation is not guesswork.
- `docs/audits/2026-08-04-qa-qi-infrastructure/reviewer-reports/` — pass 1 verbatim.
- `docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md`, `docs/WAVE_EXECUTION_PIPELINE.md`
  (invariants), `docs/adrs/ADR-009-*`.

## 7. Verdict

End your file with: **is this branch safe to merge to `main`?** — `YES` / `YES WITH FIXES` /
`NO`, and name the findings that decide it. Distinguish **merge blockers** (this branch makes
something worse, or ships a guard that cannot fire) from **submission blockers** (the paper
corpus is not ready) — the latter route to ADR-010 and are explicitly *not* merge blockers.

## 8. Do not

- Do not `git commit`, `git add`, push, or modify any file outside your own report.
- Do not run `lake build` or `cd lean && lake ...` (minutes, and another reviewer may be mid-run).
- `uv run --no-sync python scripts/validate.py --check <name>` is fine and encouraged.
