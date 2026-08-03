# Resume state — infrastructure + publication remediation

**Last updated:** 2026-08-03. Written so any session (or a post-compaction continuation) can pick this up
without re-deriving it. Read this first, then the linked documents.

---

## Git layout (as of 2026-08-03)

**`main`** — `c2b597e1 docs(audit): publication-readiness assessment of all 21 bundles`.
The completed assessment only. No infra code.

**`infra/adr-009-validation-modularization`** — all infrastructure work, off main until every phase is
done and ready to merge (operator ruling 2026-08-03):

```
a41f8573  feat(egress): whitelist isa-afp.org + path-scoped prover repos
50ac26d5  docs(adr): ADR-009 + QA/QI infrastructure map
cdb81f7e  feat(validate): ADR-009 Phases 0-1
<review docs commit>  docs(reviews): Stage-13 bundle reviews, 2026-08-01
```

**`stash@{0}`** — paper-remediation WIP from the 07-31/08-01 sessions (132 regenerated figures,
`counts.json`/`.tex`, `provenance.py`, `citation_cache.py`, `lean_deps.json.hash`). Separated by mtime;
boundary verified. **Restoring it changes `counts.json`, which several checks read — take a fresh
characterization baseline after any unstash.**

⚠️ **Two git gotchas learned here.**
1. The pre-commit hook runs `sync.py --fast` and **restages** `SK_EFT_Hawking_Inventory_Index.md`,
   `lean/atlas_view.json`, `docs/ATLAS_HEATMAP.md` and `papers/*/tables/*.tex` into whatever you commit.
   Stage explicit paths only; check `git show --stat HEAD` afterwards.
2. **mtime is not provenance.** `harness_web_egress_guard.py` reported an 08-01 mtime for a change made
   on 08-03. Verify authorship by diff content, not timestamp.

---

## Where we are

Two workstreams, sequenced by operator ruling (2026-08-03): **infrastructure remediation first, paper-prose
remediation second, ADR-008 Claude-Code onboarding third.**

### Workstream 1 — infrastructure (ACTIVE)

Governed by **[ADR-009](../../adrs/ADR-009-validation-suite-modularization.md)** (status: PROPOSED;
direction authorized, contingent on architecture review + operator visibility).

| Phase | State |
|---|---|
| **0 — characterization harness** | ✅ **COMPLETE.** 3 guards + the harness, all mutation-verified |
| **1 — anchors + helpers, file stays put** | ✅ **COMPLETE.** `CHARACTERIZATION HELD — 49 checks identical` |
| 2 — package split | **IN PROGRESS.** Ordering mechanism landed + mutation-verified |
| 3 — semantic fixes | not started; list in ADR-009 §Deferred |

**Phase 1 delivered** (all verified behaviour-preserving against a pre-change baseline):
- `scripts/validate_helpers.py` — the single path anchor + artifact loaders.
- **8 `lean_deps.json` loaders** → one helper; each call site KEEPS its own missing-file verdict,
  marked `TODO(semantic-review)`. Five PASS / two FAIL / one PASS-with-warning / one unguarded — the
  divergence is now visible in one place instead of scattered, and deliberately not unified.
- **7 draft-scoping sites** → `all_paper_drafts()`. Equivalence proven empirically first (all three
  idioms return the identical 64 files).
- **7 path anchors** → aliases of `validate_helpers` (H1). This is what makes the Phase-2 move
  path-neutral rather than silently retargeting `PROJECT_ROOT` into `scripts/`.
- **14 redundant `sys.path.insert`** + 3 dead `import sys as _sys` + 2 orphaned guards removed.

**Deliberately NOT converted** (pattern-matched but semantically different):
- the `iterdir` scanning for `claims_review.json` — different artifact, and its `name.startswith('paper')`
  filter excludes every bundle;
- the three `for code in BUNDLE_CODES` loops — each carries per-site missing-draft reporting that
  `bundle_drafts()` would silently drop.

**Verification method for Phase 2 — use the same loop:**
```
uv run python tests/validate_characterization.py --record /tmp/before.json   # ~6 min, 49 checks
...make the change...
uv run python tests/validate_characterization.py --record /tmp/after.json
uv run python tests/validate_characterization.py --compare /tmp/before.json /tmp/after.json
```
⚠️ Run these **from the repo root** — a background shell reverts to the workspace parent, and a
piped `tail` will report exit 0 for a command that never ran. (Caught once already.)

**Phase 0 progress:**
- ✅ **Guard 1 — registry contract.** `tests/test_validate_registry_contract.py`, 6 tests. Freezes the
  check COUNT and registration ORDER, plus a property test that regenerators precede their consumers.
  Mutation-tested three ways (drop a check / swap two / move `counts_fresh` behind its consumer) — all
  caught; clean negative control.
- ✅ **Guard 2 — flag propagation.** `tests/test_validate_flag_propagation.py`, 14 tests. Behavioural leg
  (`parameter_provenance` flips `True→False` under `--strict`) + end-to-end CLI leg (rc 0 → 1) + structural
  `co_names` leg over all 8 flag-consuming checks. Mutation-tested: an import-time copy of `STRICT_MODE`
  (the literal H5 hazard) and a flag rebound as a default argument are both caught; clean negative control.
  Stated coverage limit: no behavioural leg for `FORCE_NOTEBOOK_REEXEC` or the `True` direction of
  `FORCE_LATEX` (too slow) — structural only.
- ✅ **Guard 3 — de-nested the recurrence matcher.** `_RECURRENCE_MIN_TITLE`,
  `_RECURRENCE_MIN_OVERLAP`, `_recurrence_norm` now live at module scope in `validate.py`; the in-function
  `_MIN_TITLE` / `_MIN_OVERLAP` / `_norm` are aliases, so the calibration comments stay with the decision and
  the two can never diverge. `tests/test_bundle_formulas_d11_d12.py` now imports the real matcher and the
  real threshold instead of re-implementing them.
  **Verified:** check output byte-identical to the pre-change baseline (213 closures compared, 924 open,
  0 contradicted). **Mutation-tested:** breaking the production normalizer, or retuning the production
  threshold, now fails the frozen-pairs test — and the counterfactual (restoring the old local copy) is
  MISSED, which is the defect this guard removes.
- ⬜ **Golden per-check `--json` snapshots.** Normalize `elapsed_seconds`, sort details, `PYTHONHASHSEED=0`.
  **Quarantine nine non-snapshottable checks:** `lean_build`, `notebook_exec`,
  `notebook_stored_outputs_current`, `paper_latex_compiles`, `counts_fresh`, `tables_fresh`,
  `claim_clusters_fresh`, `tracked_hypotheses_fresh`, `bundle_figure_integrity`.

### Workstream 2 — paper prose (SPECIFIED, NOT STARTED)

Fully documented; runnable by any session from the documents alone.
`docs/audits/2026-08-01-publication-readiness/` — `SYNTHESIS.md` (verdict, 80 P0s, the systemic finding),
`REMEDIATION_PLAN.md` (BUILD / CORRECT-TO-SUBSTRATE / FACTUAL triage), `bundles/*.md` (13 reports).

**Governing posture:** [[feedback-remediation-build-dont-walkback]] — fix with substance, not prose.
Publication schedule is the flexible variable; claim strength is not.

**Roster decision:** 21 → 14 (author's call, operator delegated). Proposed merges recorded in the
session that produced `SYNTHESIS.md`; not yet written into `PAPER_STRATEGY.md`.

### Workstream 3 — ADR-008 (DEFERRED BY DECISION)

See `tangential-items.md` T2. Behind schedule, deliberately, until 1 and 2 complete.

---

## What is NOT on disk

**The full read of `scripts/validate.py`.** All 7,778 lines were read directly on 2026-08-03; its
*findings* are captured (ADR-009 hazards H1–H5, the always-pass list, the line citations) but the read
itself is not reproducible from the documents.

**Operator rule:** core infra may only be modified by an agent that has read the file directly. So a fresh
session must re-read `validate.py` in full before touching it. Budget for that. This is why Phases 0–1
should be finished in a session that already has the read.

---

## Live state / gotchas

- **`validate.py` is RED on `main`.** The `stage13_status` guard (2026-08-03,
  `check_bundle_metadata_matches_graph`) fires on 14 of 21 bundles. Intended — the dial working. Operator
  has confirmed they expect gates and bundles to go red as remediation applies.
- **Line-number offset.** ADR-009's citations are anchored to the 7,778-line read; the guard added 35 lines
  at `:4355`, so citations after that point are **+35** from the live file (7,813). Phase 1 re-anchors
  mechanically and deletes the note.
- **Egress guard was extended** 2026-08-03 with `isa-afp.org` (host) and a path-scoped `_PATH_WHITELIST`
  for named prover repos. Verified 12/12 on an allow/deny matrix incl. traversal and suffix-confusable
  hosts. This unblocks D12's two prior-art gates, which were wrongly recorded as "structurally
  undischargeable".
- **Do not re-derive the Codex question.** Verified zero coupling to the validation suite; parked in
  `tangential-items.md` T1.

---

## Reading order for a cold start

1. This file.
2. `docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md` — the whole quality layer, §6 (enforcement reality) first.
3. `docs/adrs/ADR-009-validation-suite-modularization.md` — the decision and its five hazards.
4. `docs/audits/2026-08-01-publication-readiness/SYNTHESIS.md` — if picking up workstream 2.
5. `.working-docs/qa-qi-map-verification-log.md` — only if you need to know how a claim was established.
