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
cdb81f7e  feat(validate): ADR-009 Phases 0-1 — characterization harness + shared helpers
cc943091  docs(reviews): Stage-13 bundle review documents, 2026-08-01
8cde34a0  feat(validate): decouple execution order from import order (H3)  ← mechanism was DEFECTIVE
436bc3a2  feat(validate): Phase 2 — one flag owner (_config), and FIX the ordering mechanism
2fd89d59  fix(tests): repair the strict-mode prose test; freeze validate's external surface
9886ecf4  refactor(validate): extract result types + registry to validation/_registry
```

Untracked and deliberately NOT committed: `docs/dev-loops/proposals/prose-bridged-claims-gate.md` — an
operator-filed DRAFT awaiting the operator's own go/no-go. Not this workstream's to land.

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
| **2 — package split** | ✅ **COMPLETE 2026-08-03.** 11 modules, 0 checks left in validate.py (7900 → 720). 48/49 checks byte-identical vs the pre-Phase-2 baseline |
| 3 — semantic fixes | **IN PROGRESS.** 3 of 8 done + the graph node-id half of item 7 |

### Phase 2 — COMPLETE

Eleven modules under `scripts/validation/checks/`; `validate.py` is 720 lines of framework with **zero**
registered checks. Shared layers: `_registry` (result types + registry), `_config` (flags), `_tex` (LaTeX),
`validate_helpers` (paths). Every phase boundary verified; end-to-end, **48 of 49 characterized checks are
byte-identical to the pre-Phase-2 baseline**, the one difference being `graph_integrity`'s node count moving
by exactly the 13 guard tests added.

**Three modules were split beyond the §4 plan**, each measured before the fact and each on a seam where the
halves share no helpers: `lean_substrate`/`lean_toolchain` (~1,580 combined), `papers_prose`/`prose_lean_refs`
(~1,507), `bundles_readiness`/`reviews` (~1,250). §4's table is a plan; D1's *readable in one pass* is the
requirement. The two checks the table never assigned — `theorems` and `paper_toolchain_pin_drift` — are in
`lean_toolchain` and `papers_prose`.

**The guards that made it safe**, all mutation-verified in both directions, all in
`tests/test_validate_{registry_contract,public_surface,flag_propagation}.py`:
registry count + order · every check has a declared execution position · the sort runs after the last
registration (counting `from validation.checks import …` as a registration) · flags reach their checks and
no module shadows one · no module derives a path from `__file__` · no module aliases a path by value ·
**no module references a name left behind in validate.py** · one module identity for `validate.py` ·
the frozen 54-name external surface.

⚠️ **The last two were each written because the failure had already happened.** Stranded module-level
constants (`_COUNT_LITERAL_PATTERNS`, `_NUMERICAL_LITERAL_RE`, `_LATEX_FATAL_RE`) passed the entire
4,986-test suite and were caught only by the characterization harness, because only it invokes every check.
And a module-level `PAPERS_DIR = _H.PAPERS_DIR` silently defeated two tests that monkeypatch a temp tree to
seed a defect.

### Phase 3 — semantic fixes (ADR-009 §Deferred, 8 items)

Each is a **separate reviewed change** that ships with a mutation test proving both directions — fires on
a seeded defect, silent on correct data (D5). Never batch them with a mechanical move.

Ordered by how much a wrong answer costs today:
1. ✅ **DONE** (`fd470314`) — `readiness_submission_gate` was **inverted**: it failed only when zero gate
   nodes existed and passed when it measured RED. 61 of 64 papers were RED with verdict `True`. Four
   defects fixed (verdict, per-paper details, summary, fail-open ImportError); two pure cores extracted;
   11 tests, 5 mutations, clean negative control. **`validate.py` is now RED on this check by design.**
   ⚠️ Harness lesson from it: scope every mutation to the target function's AST span. Two mutations read
   as MISSED because `str.replace(…, 1)` hit the FIRST match in the file — inside a *different* function.
2. ✅ **DONE** (`c3456a23`) — all 8 dispositioned individually. 4 were defects (fixed:
   `readiness_submission_gate`, `paper_latex_compiles`, and ratchets for `count_literals` /
   `numerical_literals`); 4 are honestly advisory with recorded reasons. **`paper_latex_compiles` now fails
   on D3 — 2 fatal LaTeX errors, a real publication blocker for that bundle.**
3. ✅ **DONE** (`<this commit>`) — `native_decide_regression` now measures `lean_deps.json` directly.
   Reordering could not have fixed it: the commit gate invokes the check in ISOLATION, so `counts_fresh`
   never runs there at all.
4. **Fabricated VERIFIES edges** (§Deferred item 7) — `np.kron` → `Curvature.kron`, `v` →
   `EWMassMatrixInputs.v`. 10 of 534. One-line alias guard; changes what a gate measures.
5. No `UNEVALUATED` state — ~20 sites encode "could not measure" as PASS.
6. `count_literals` ⊂ `axiom_count_prose_consistency` — same predicate, one hard-fails, one cannot fail.
7. `--strict` reaches no automated caller, so two gates are unreachable in practice.
8. Memoizing `load_lean_deps()` + a shared graph handle — **reviewed together**, because both change what
   a check observes once the `*_fresh` checks regenerate artifacts mid-run (≈8 extractions / ≈20 parses of
   a 70 MB file per run today).

**Phase 2 so far** — three pieces of scaffolding, each of which had to be repaired after being built:

1. **`_CANONICAL_ORDER` + `_apply_canonical_order()`** (H3) — execution order declared as data, so module
   organisation stops determining it. ⚠️ **Shipped broken and was caught by the mandatory full re-read, not
   by any test.** The call sat mid-file: 14 of 59 checks registered below it were never sorted, and its
   `raise` for an undeclared check could not fire for anything after that line — including the end of the
   file, where a new check naturally goes. Invisible because the tail was coincidentally already in
   canonical order. Fixed by moving the call below the last registration; ADR-009 H3 carries the full
   account. **Phase 2 must move it after the check-module import block**, which makes it structural.
2. **`scripts/validation/_config.py`** (H5) — the three runtime flags now have exactly one owner, reached by
   attribute access (`_cfg.STRICT_MODE`) so the value resolves at call time. `validate.STRICT_MODE` and
   siblings no longer exist.
3. **`scripts/validation/__init__.py`** — the package. Named `validation`, **not** `validate`: a package
   shadows a same-named module on the same `sys.path` entry (verified empirically), so ADR-009 D1's original
   `scripts/validate/` + shim pairing was unbuildable and is corrected in the ADR.

⚠️ **Guard 2 had a hole, found by attempting the work it protects.** `co_names` records names used for
`LOAD_ATTR` as well as `LOAD_GLOBAL`, so `from validate import STRICT_MODE` still shows `STRICT_MODE` in
`co_names` — a global lookup resolving against the wrong namespace. The flag freezes at import time,
`--strict` becomes a no-op, and the guard written for exactly that hazard stays green. Closed structurally:
every consuming check must show `_cfg` in `co_names`, and `TestNoCheckModuleShadowsAFlag` asserts that **no
suite module binds a flag in its own namespace at all** — which catches it however the body reads it.
Mutation-verified: the old leg MISSES the cross-module copy, the new one catches it.

4. **`validation/_registry.py`** — `Detail` / `CheckResult` / `CheckSpec` / `_CHECKS` / `register_check`.
   Kills the import cycle that blocked check-module extraction (a check module needs `register_check`;
   `validate` imports check modules for their side-effect). Re-exported from `validate` **by binding** —
   `_CHECKS` must stay the SAME list, since registration appends and the canonical sort mutates in place.
   ⚠️ Extracting it **surfaced a pre-existing defect**: `test_substrate_integrity_gates.py` imported
   `from scripts.validate import …` while everything else uses `import validate`, so `validate.py` was
   loaded TWICE under two module identities. Invisible while all shared state was per-module (two
   registries of 59 look like one); fatal once `_CHECKS` became a singleton (118 checks, duplicate names).
   Never harmless: `isinstance` across the two `CheckResult` classes was silently False. Fixed at source;
   `test_validate_is_loaded_exactly_once` guards it via `sys.modules`.

**Standing lesson for the rest of this refactor.** Four for four, the scaffolding was defective on first
write and the defect was of the *same class the scaffolding exists to prevent* — an inert guard, a
partially-applied mechanism, a name that resolves to the wrong thing, a module with two identities.
Three of the four were found by re-reading or by attempting the next step, **not by any test**. Assume the
next piece is defective too, and attack it before trusting it.

**And run the WHOLE fast suite, not the tests you just wrote.** Removing `validate.STRICT_MODE` broke the
one pre-existing test of strict mode; targeted runs stayed green and the 2.5-minute full suite caught it
immediately.

**A failing test is NOT evidence that a guard fired.** Twice in one session a mutation run reported
"caught" when the test had actually failed to *collect* — once a stray docstring quote (SyntaxError),
once a mutation using a name the target module does not import (NameError). Both produced false
confidence in a guard that had not been exercised at all. Every mutation harness must distinguish
**"the guard's assertion fired"** from **"the mutation broke the import"**, and the mutation itself must
be something a person would plausibly write — importable, and realistic. The `notebooks` extraction's
harness does both; copy it.

**Guard scope must grow with the code it guards.** The H1 test scanned only `validate.py`; it would have
gone blind the moment the first check module landed. It now walks `validation/**/*.py`. When you add a
module directory, check every structural guard's scope before trusting a green run.

**Phase 1 delivered** (all verified behaviour-preserving against a pre-change baseline):
- `scripts/validate_helpers.py` — the single path anchor + artifact loaders.
- **8 `lean_deps.json` loaders** → one helper; each call site KEEPS its own missing-file verdict,
  marked `TODO(semantic-review)`. Five PASS / two FAIL / one PASS-with-warning / one unguarded — the
  divergence is now visible in one place instead of scattered, and deliberately not unified.
- **7 draft-scoping sites** → `all_paper_drafts()`. Equivalence proven empirically first (all three
  idioms return the identical 64 files).
- **7 path anchors** → aliases of `validate_helpers` (H1). This is what makes the Phase-2 move
  path-neutral rather than silently retargeting `PROJECT_ROOT` into `scripts/`.
  ⚠️ **This was INCOMPLETE and the claim above overstated it — corrected 2026-08-03.** Phase 1 converted
  the seven MODULE-LEVEL anchors; **five `Path(__file__)` derivations remained inside check bodies**,
  which is precisely where a module move relocates them: `formulas` (:159), `graph_integrity` (:3347),
  `accepted_findings_carry_rationale` (:4228), `citation_primary_sources_present` (:5172),
  `quantum_network` (:6114). Measured before fixing — three would have failed loudly, but **two would
  have passed SILENTLY**: `accepted_findings_carry_rationale` returns `passed=True` on a missing ledger,
  and `citation_primary_sources_present` downgrades its duplicate-bibkey guard to an advisory warning
  inside an `except`. All five now derive from `validate_helpers`; each replacement was proven to resolve
  to the identical existing path before substitution.
  `test_no_check_derives_a_path_from___file__` makes "H1 is closed" checkable instead of asserted, and
  is the guard to run before EACH module move — not once.
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
