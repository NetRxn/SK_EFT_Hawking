# ADR-009 close-out — what is complete, what remains, and where it is scoped

**Status 2026-08-05.** Branch `infra/adr-009-validation-modularization`, ~110 commits ahead of
`main`, suite **5,554 passed / 5 skipped / 0 failed**.

---

## 1. ADR-009's own scope is COMPLETE

**§Deferred items 0–7: 8 of 8 dispositioned.** Verified against code by PR-review pass 2
(reviewer R3), not against the tracker. Two carry prose-only residue, both now corrected:

| item | residue | state |
|---|---|---|
| 0 | second half (shared graph handle) declined on measurement; sub-clause (d) never done | ✅ recorded in the ADR |
| 6 | sub-clause *"`--strict` reaches no automated caller"* falsified by `gate_precheck submission` | ✅ superseded in the ADR 2026-08-05 |

⚠️ The figure **"4 of 8"** appeared in the operator memory note and was **stale** — corrected.

## 2. Documentation is now current

| artifact | state |
|---|---|
| `ADR-009` §Deferred 0–7 | ✅ all dispositioned; item 6 sub-clause superseded |
| `ADR-009` **Post-delivery addendum II** | ✅ **added 2026-08-05** — documents `_memo.py`, `CheckResult.measured`, `--ci`, the LaTeX slow-gate deletion, pass-2 verdicts, and why `measured` is additive rather than a third `passed` state (item 4's objection does not apply) |
| `QA_QI_INFRASTRUCTURE_MAP.md` | ✅ retracted-then-re-asserted "59 of 59 mutation-verified" corrected to **4 of 59 production-seeded** |
| `validation-module-migration-notes.md` | ✅ `_memo.py` added to the module map; "eight domain modules" → **twelve, 8,969 lines** |
| `RESUME_STATE.md` | ✅ QI-29's own correction (falsified by the slow-gate deletion) superseded; `--strict`-no-caller claim corrected; 57-of-59 annotated |
| pass-1 register | ✅ reconciled with pass-2 outcomes (R4-I6, R4-I8, R5-I1, R6-M1) |
| pass-2 register + 6 reviewer reports | ✅ on disk, written by the reviewers themselves |
| operator memory note | ✅ corrected (8 of 8; the rules this branch earned) |

## 3. What remains — NOT ADR-009 scoped

### 3a. Needs an operator decision (1)

- **Namespace-vs-leaf obstruction policy.** 223 declarations are classified `OBSTRUCTION` because
  their *namespace* matches, split **134 `theorem` / 89 apparatus** (`def` 82, `structure` 4,
  `instance` 2, `inductive` 1). Recommendation on file: exclude apparatus, keep theorems
  (507 → 418). One-line predicate. The unambiguous half — 68 auto-generated declarations — is
  already fixed.

### 3b. ADR-010 / Phase 7 corpus work

- **R5-C2…C5** — figure content, number recomputation, theorem-statement correspondence, citation
  content. Absent *checks*, not broken ones. C2 re-measured worse than filed: **124 bundle PNGs
  across 49 dirs, 29 with no `FIGURE_REGISTRY` spec at all**.
- **8 bundles carry inline unit-bearing numbers with no provenance link** — D1, D3, D4, D5, E1,
  E2, F, L1. Root cause is §7 of the frozen `BUNDLE_LIFT_PROCEDURE`: numbers should arrive via
  `\input{tables/<spec_id>.tex}`, and **zero of 21 bundles have a `tables.py`**. Giving those 8
  bundles table specs makes their provenance structural — no registry, no inheritance heuristic.
  ⚠️ Bundles must NOT inherit parameters as a union over source papers: §3 makes them
  *synthesis-driven new compositions*, so a union would attribute dependencies they never used.
- **D3's two fatal LaTeX errors** — now a visible default red rather than a silent skip.
- Legacy `papers/paperN_*/` drafts are **substrate, not publication targets** (`BUNDLE_LIFT` §188),
  so their gate coverage is out of scope by design.

### 3c. Infra residue — real, measured, none blocking merge

| item | measurement |
|---|---|
| R3-C2 fixture-only ratchet | **55 of 59** checks never production-seeded (`FIXTURE_ONLY_CEILING = 55`) — ratcheted, not swept |
| R2 seam guard | asserts `>= 30` against an actual **54** — **44 % headroom**, a ratchet that cannot fire |
| R3 | **5 of 10** ratchets have no zero-headroom test |
| R3-I5 / R1 | BinOp path-alias gap — **5 sites**, two under a docstring denying they exist |
| R4-I1 | `cross_path_consistency`'s two legs produce **bit-identical** `rel_diff`; both skip to `passed=True, details=[]` |
| R6-M2 | `NarrativeGrounding` is a change-detector for five historical overclaims |
| R1/R2/R3 tail | ~15 further IMPORTANT/MINOR items, each with a measurement in the pass-1 register |

## 4. Merge assessment

**The branch is safe to merge.** Every pass-2 CRITICAL and MAJOR is closed; the residue above is
pre-existing or additive, and none of it makes anything worse than `main` — which had no guard in
these positions at all.

The distinction that matters and was not being drawn: **the branch is safe to merge; the corpus is
not safe to submit.** Those are different gates with different owners.

⚠️ One behavioural change to expect: a default `validate.py` now exits **1** with three reds —
`bundle_metadata_matches_graph`, `readiness_submission_gate`, and `paper_latex_compiles` (D3).
All three were red in reality before; only the third is newly *visible*.
