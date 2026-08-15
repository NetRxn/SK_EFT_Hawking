---
paper: infra
bundle: infra
bundle_target: infra
tier: 2
reviewer: lead
model: claude-opus-5
review_date: 2026-08-15T14:10:00Z
readiness_gates_version: 1
kind: targeted-infra
---

# `count_literals` cannot see a single-digit count, or any count joined by a LaTeX tie

## Summary

**1 MAJOR.** `count_literals` is the guard that stops a hand-typed census figure from
drifting. Its theorem pattern requires **two to five digits** followed by **whitespace**, so
it is blind to two shapes that are common in this corpus and one of which is the house
style:

- **single-digit counts** — `9~theorems` never matches `\d{2,5}`;
- **any count joined by a LaTeX tie** — `12~theorems` never matches `\s+`, and `~` is what
  this project writes between a number and its noun throughout.

⚠️ **This is not hypothetical and the check reported the opposite.**
`papers/paper10_modular_generation/paper_draft.tex` carried two hand-typed per-module
counts, `WangBridge.lean (9~theorems)` and `ModularInvarianceConstraint.lean
(12~theorems)`, **and both were wrong** — they counted compiler-generated equation lemmas,
so under the canonical non-autogen convention the project-wide figure beside them uses,
they are 8 and 11. `count_literals` reported paper10 as *"no count literals found (macros
in use)"*. The paper was clean by the guard and wrong by measurement, which is this
project's own defect class — absence rendered as success — inside the instrument built to
catch exactly this.

Both were caught by a human-directed read during D12/paper10 remediation, not by the check.

---

### 1.1 — 🔴 MAJOR — the pattern excludes the two shapes most likely to occur

- **Severity:** major
- **Lane:** `infra`
- **Verify:** `cd "$REPO" && uv run python -m pytest tests/test_d5_prose_checks.py -q -k "tie or single_digit"`
  *What it asserts:* that a count written `9~theorems` or `12~theorems` is detected. Exits 1 at HEAD (no such test, and the check does not detect them).
- **Gate:** CountFreshness
- **Location:** `scripts/validation/checks/papers_prose.py` — the theorem/module literal pattern in `check_count_literals`
- **Observed:** The pattern is of the shape `\d{2,5}\s+(?:Lean\s+)?theorems?`. Two exclusions
  follow directly: a one-digit count, and a tie-joined count. Neither exclusion is stated
  anywhere as intentional.
- **Evidence:** Measured 2026-08-15 during paper10 remediation.
  - `paper10_modular_generation` carried `(9~theorems)` and `(12~theorems)`; the canonical
    non-autogen counts are **8** and **11**. `count_literals` reported paper10 clean.
  - The tie is house style: it is used between a number and its noun throughout the corpus,
    so this is not an edge case the check happens to miss — it is the common case.
  - The two literals are now bound to macros (`\paperTenWangBridgeThms` /
    `\paperTenModularInvarianceThms`) emitted by `scripts/update_counts.py`, so paper10 is
    repaired. The CHECK is not.
- **Expected:** A hand-typed census count is detected regardless of digit count or of whether
  the number is joined to its noun by a space or a tie.
- **Fix:** Widen the pattern to `\d{1,5}[\s~]+` for both the theorem and module legs, and
  ship the two shapes as test cases.
  ⚠️ **This is a ratchet re-baseline, not a one-line regex edit, and it must be sequenced as
  one.** Widening the pattern will surface literals across the corpus that were never counted,
  taking the population above the frozen `COUNT_LITERAL_CEILING` (95 at the time of writing).
  The honest order is: widen the pattern → **measure** the new population → sweep the newly
  visible literals or freeze the ceiling at the measured value with the jump stated in the
  same commit. Do **not** widen and immediately raise the ceiling to whatever comes out; that
  reproduces the "constant set just under the live maximum" defect this repository has
  recorded three times.
- **Related:** the same shape as `review_severity_declared` counting per-document totals, and
  as the `\bibitem`-as-proxy defect retired in `d39d2ffb` — a guard whose predicate is
  narrower than its purpose, so its silence is not evidence.
- **Cache:** N/A.
