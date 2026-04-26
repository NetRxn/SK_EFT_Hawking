---
paper: process
reviewer: wave10h-fixer-pipeline-audit
model: claude-opus-4-7
review_date: 2026-04-25T15:34:00Z
readiness_gates_version: 1
---

# Wave 10h process audit — claims-reviewer-v2 + fixer pipeline

## Summary

During Wave 10h's retrofit batch (claims-reviewer-v2 across all 18 papers + parallel fixer queue), two distinct process gaps were observed across multiple papers. Both are **process-level** issues (Stage 14 / QI category), not paper-content issues. severity: critical.

**Issue 1 (FixPropagation):** v2 review writes `claims_review.json` containing a `blocking_issues` snapshot. When a fixer agent then modifies the paper's `paper_draft.tex` to address those issues, the `blocking_issues` array in `claims_review.json` is NOT refreshed. Subsequent passes that consume `blocking_issues` see stale findings whose underlying state has already been fixed. Confirmed across 3 papers (paper3, paper4, paper6).

**Issue 2 (LeanProofSubstance — false-positive class):** v2 reviewer's `lean_deps.json` oracle is unreliable — at least one Class TN finding (paper2 block:1) reports a theorem as "not found in lean_deps.json" when the theorem IS present (paper2: `firstOrder_correction_zero_iff_no_dissipation` at line 65238 of `lean_deps.json`). This class of false positive corrupts the fixer queue (a deterministic fixer applying the prescribed remediation would have collapsed two distinct theorems with different hypothesis structures, introducing a regression). The "Closest match" heuristic in the reviewer's TN finding is not safe ground for prescription.

## QI Candidate

Both issues are systemic. Recommend remediation in a follow-on wave.

## Findings

### 1.1 — 🔴 BLOCKER — Stale blocking_issues snapshot after parallel fixer pass (FixPropagation)

- **Gate:** FixPropagation
- **Location:** `scripts/sentence_state.py` (sole writer to `claims_review.json` is the v2 reviewer agent only — fixers don't update it); `papers/<paper>/claims_review.json` schema has no per-issue `status` field.
- **Observed:** During Wave 10h retrofit, claims-reviewer-v2 wrote `papers/paper3_gauge_erasure/claims_review.json` at 02:38:31, with `blocking_issues[0]` flagging "12 theorems" in GaugeErasure abstract. A parallel fixer agent then patched `paper_draft.tex` at 02:44:43 (6m13s later) to "11 theorems". The fix did not propagate back to `claims_review.json`'s `blocking_issues` array — the snapshot is still present in the JSON, untouched, even though the underlying paper state is now correct. Same pattern: paper4 (review 02:40:18, tex 02:45:38, +5m20s) and paper6 (review 02:40:42, tex 02:46:38, +5m56s). The fix did not propagate to the review's source-of-truth view, so consumers downstream see findings still present despite resolution.
- **Evidence:**
  ```
  $ stat -f "%Sm" papers/paper3_gauge_erasure/{paper_draft.tex,claims_review.json}
  paper_draft.tex     2026-04-25 02:44:43
  claims_review.json  2026-04-25 02:38:31
  ```
  Repeat for paper4, paper6 — same direction.
- **Expected:** When a fixer modifies a paper to resolve a blocking_issue, the corresponding entry in `blocking_issues[].status` flips to `'fixed'` (or the entry is removed). Subsequent passes can distinguish "needs work" from "already done."
- **Fix (one of):**
  1. **Sole-writer extension:** add a `sentence_state.py mark-issue-fixed --paper <p> --issue-id <id>` subcommand. Fixers call it after a successful edit; the JSON is updated atomically. Symmetric with the existing `cmd_mark` for sentence verdicts.
  2. **Re-review post-fixer:** at the end of each Wave 10h fixer batch, re-run claims-reviewer-v2 on the touched papers to refresh the blocking_issues snapshot. Doubles the agent budget per wave.
  3. **Status-aware consumption:** consumers of `blocking_issues` (the fixer dispatcher, the dashboard, the readiness gate) re-validate each finding against the current paper state before treating it as actionable. Pushes the cost to consumers.
  Option 1 is cheapest and matches the Wave 10b sole-writer architecture.
- **Cache:** N/A
- **Affected papers:** paper3_gauge_erasure, paper4_wkb_connection, paper6_vestigial (Wave 10h fixers reported "no edits needed; already in target state" on 3 of 7 sweeps).

### 1.2 — 🔴 BLOCKER — claims-reviewer-v2 trivial-proof / placeholder oracle false-positive on Lean theorem names in paper2_second_order (LeanProofSubstance)

- **Gate:** LeanProofSubstance — the reviewer's Class TN finding is structurally analogous to a placeholder / trivial-proof misclassification: it asserts a theorem is "absent" (i.e. a placeholder gap that needs filling) when the theorem in fact exists with full proof substance. False-positive trivial-proof flags corrupt the fixer queue the same way they would for a real placeholder finding.
- **Location:** `.claude/plugins/physics-qa/agents/claims-reviewer.md` (Class TN — Theorem-Name-not-in-Lean-deps prescription); paper2_second_order's `claims_review.json` `blocking_issues[0]`.
- **Observed:** paper2's Class TN finding states: "paper references `firstOrder_correction_zero_iff_no_dissipation` (Sec 5.3.2, line 388); not found in lean_deps.json. Closest match is firstOrder_correction_zero_iff (without _no_dissipation suffix). Likely renamed/consolidated post-draft." This is wrong — both theorem names ARE in `lean/lean_deps.json`:
  ```
  $ grep -n "firstOrder_correction_zero_iff" lean/lean_deps.json
  65226:  "name": "SKEFTHawking.WKBAnalysis.firstOrder_correction_zero_iff",
  65238:  "SKEFTHawking.WKBAnalysis.firstOrder_correction_zero_iff_no_dissipation",
  ```
  The two theorems live in `lean/SKEFTHawking/WKBAnalysis.lean` lines 383 and 437; the paper at line 388 cites the `_no_dissipation` form correctly (forward-only theorem, `γᵢ = 0 → δ = 0`), and at line 377 cites the `_iff` form correctly (biconditional with `κ > 0`). Paper is right; reviewer is wrong.
- **Evidence:**
  Paper-side: lines 377 + 388 both PASS a manual cross-check against the Lean file. Lean-side: both theorem names exist with full type signatures. Reviewer-side: the Class TN finding has `sentences: []` (empty — no source sentence cited), which is itself a structural red flag.
- **Expected:** Class TN findings against `lean_deps.json` must (a) cite a source sentence ID, (b) verify the absence claim with a deterministic grep on the actual `lean_deps.json` file (not a partial / cached snapshot), (c) NOT prescribe "rename to closest match" when two distinct theorems with different hypothesis structures exist — that prescription is unsafe by construction.
- **Fix:**
  1. Tighten claims-reviewer-v2's TN prompt to (a) require `sentences` non-empty for any finding that cites a code-level identifier (mirrors the existing IA / SD / HD discipline), (b) state the deterministic grep that was run, (c) reject the "Closest match" heuristic for prescriptions; the heuristic may surface a candidate, but the fixer is told to verify via grep and not auto-rename.
  2. Add a self-check pass at end of v2 review: for every Class TN finding, run `grep -nE "name.*\\.<name>\b" lean/lean_deps.json`. If the grep returns ≥1 match, flip the finding to advisory + `status: false-positive` and emit a non-blocking followup instead.
  3. Pipeline gate: post-v2-review, before the fixer queue dispatches, run a quick deterministic verifier over each `blocking_issues` entry of class TN. Drop entries whose absence claim doesn't reproduce.
- **Cache:** N/A — deterministic file scan.
- **Affected papers:** paper2_second_order (1 confirmed false positive); class is likely systemic (not measured because most reviewers aren't Lean-name-resolving). Recommend re-scan of papers with `by_finding_class.TN > 0` to estimate FP rate.

## QI Candidate (cont.)

Both findings recommend remediation in a follow-on wave (Wave 10i candidate). Severity: critical because (a) Issue 1 corrupts the dashboard's Process Health surfacing of papers as "needs fixer work" when work is done, and (b) Issue 2 would have introduced a Lean-paper regression had the fixer agent not declined the prescription on its own initiative (a fortunate rather than systemic guard).

Both relate to the architectural rule "the v2 review/fixer pipeline must converge to a fixed point." Right now it doesn't — fixers can't refresh review state, and reviewer findings can be wrong-but-actionable.
