# Resume state — infrastructure + publication remediation

**Last updated:** 2026-08-04. Written so any session (or a post-compaction continuation) can pick this up
without re-deriving it. Read this first, then the linked documents.

---

## Git layout (verified 2026-08-04)

**`main`** — `c2b597e1 docs(audit): publication-readiness assessment of all 21 bundles`.
The completed assessment only. No infra code.

**`infra/adr-009-validation-modularization`** — all infrastructure work, off main until every phase is
done and ready to merge (operator ruling 2026-08-03). **31 commits ahead of main, 0 behind.** HEAD:

```
cc797605  fix(graph): stop fabricating 144 Lean VERIFIES edges — §Deferred item 7 (complete)
9532ba76  fix(validate): native_decide ratchet measures live substrate — §Deferred item 1
01117b08  docs(architecture): record the sixth silent-drop point in the map's §3
cb9e1dcd  fix(graph): stop silently dropping 66 test nodes — §Deferred item 7 (half)
c3456a23  fix(validate): disposition the always-pass checks — §Deferred item 3
fd470314  fix(validate): readiness_submission_gate can finally fail — §Deferred item 2
2ced308d  refactor(validate): extract citations, reviews, bundles_readiness — Phase 2 complete
```

Working tree carries two pre-existing, deliberately untouched entries: `M lean/lean_deps.json.hash`
and `?? docs/dev-loops/proposals/prose-bridged-claims-gate.md`.

**Live measurements, all re-verified 2026-08-04:** `validate.py --list` = **59**; `validate.py` = **720**
lines with **zero** registered checks (its 5 `@register_check` hits are all comments/docstrings);
`_apply_canonical_order()` at `:618`, below the check-module import block (`:484-494`) ✅;
frozen external surface = **54**; full fast suite **5039 passed, 5 skipped, 0 failed** in 166 s.

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
| 3 — semantic fixes | **IN PROGRESS.** 4 of 8 done (item 7 now complete, both halves) |

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

⚠️ **The list below is ordered by COST, which is a different permutation from ADR-009 §Deferred's own
0–7 numbering — and §Deferred's numbering is the canonical one for cross-references.** Two documents
already mis-cited across the two schemes. Mapping (this list → §Deferred): 1→**2**, 2→**3**, 3→**1**,
4→**7**, 5→**4**, 6→**5**, 7→**6**, 8→**0**.

⚠️ **Re-measure every open item's scope before fixing it.** Item 4's filing was wrong in four independent
ways; item 7's "two gates" is measured at **six**. A partition inherited from prose is not a partition.

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
4. ✅ **DONE** (`<this commit>`) — fabricated VERIFIES edges. **144 of 536** Lean-targeted edges were
   phantom, not the 10 the ADR recorded. Two independent rules, each mutation-verified as load-bearing:
   a ref rooted at a **module alias** (`import X`) is a Python module, never a Lean declaration (kills
   bare `v`, `m`, `time` *and* every `np.*`); a **dotted** ref may resolve only as a full Lean name,
   never by its tail (kills `PARAMETER_PROVENANCE.get` and five `CANDIDATE_*.basic_viability` refs
   collapsing onto one field). Formula/param edges bit-identical (1,390 → 1,390), so no
   `ComputationCorrectness` verdict can move. 16 tests, 6 mutations, clean negative control.
   ⚠️ **The filed finding was wrong in four ways** — count, consumer, function name, effort. See the new
   standing lesson in the map's §9: *re-measure a finding's scope before fixing it, even your own.*
5. No `UNEVALUATED` state. ⚠️ **Re-shaped 2026-08-04 by a full read of all 11 check modules.** The
   "~20 sites" estimate is in the right ballpark (~11 return `passed=True` from an `except`; the
   missing-artifact class adds roughly as many again), **but the framing was wrong**: the fix is
   almost certainly NOT a new `CheckResult` state. `passed` is consumed by `print_results`,
   `archive_results`, the `--json` payload (a D2 CONTRACT item), `gate_precheck.py` and
   `pre-commit-sync.sh` — a third state is a contract break. And the project has **already converted
   ~60% of the population by hand**, each with a written reason: `bundle_metadata_matches_graph`,
   `readiness_verdicts_agree`, `readiness_submission_gate`, `review_docs_mint_findings`,
   `recurrence_reopens_closures`, `native_decide_regression`, `notebook_stored_outputs_current`
   (empty glob → FAIL) and both of `graph_integrity`'s inner guards all FAIL on cannot-measure.
   **Treat item 5 as finishing that per-site sweep, with the readiness/graph family as the template**
   — or decline the type change with this measurement. The remaining PASS-on-cannot-measure sites
   are concentrated in `axiom_closure_allowlist` (5 separate PASS returns — no lake, no source,
   timeout, non-zero rc, unparseable JSON), `paper_latex_compiles` (2), `paper_toolchain_pin_drift`
   (2), `inventory_index_autogen_fresh` (2), and the import guards in `notebooks`,
   `bundle_figure_integrity`, `tracked_hypotheses_fresh`, `bibitem_title_primary_source`.
   Two are annotated in-body as the H1-SILENT sites: `accepted_findings_carry_rationale` (missing
   ledger → PASS) and `citation_primary_sources_present`'s duplicate-key guard (exception → advisory).
6. ⛔ **`count_literals` ⊂ `axiom_count_prose_consistency` — THE PREMISE IS FALSE. Read both
   2026-08-04.** Neither half of the filing survives. (a) `count_literals` is no longer "incapable of
   failing" — §Deferred item 3 made it a ratchet against `COUNT_LITERAL_CEILING` (`c3456a23`).
   (b) They are **not the same predicate**: `count_literals` ratchets the *density* of literal
   counts ("N theorems", "N modules", "N sorry") and never compares them to anything;
   `axiom_count_prose_consistency` performs a **value comparison against computed truth**
   (`docs/counts.json` → `lean.axioms`) with a ±120-char historical-attribution window and a
   negation guard, hard-failing only when prose asserts a live axiom while the count is 0. Merging
   them would DESTROY the comparison-to-truth. The real finding is the inverse and is worth
   shipping: **`axiom_count_prose_consistency` is the model `count_literals` should be raised to** —
   compare each literal against its `counts.tex` macro value, rather than only counting literals.
   Disposition: DECLINE the merge with this measurement; consider the strengthening separately.
7. `--strict` reaches no automated caller, so every strict-only leg is dead code. ⚠️ **Filed as "two
   gates" (`axiom_closure_allowlist`, `bundle_source_freshness`); re-measured 2026-08-04 by AST at
   SIX** — those two plus `parameter_provenance`, `provenance_doi_in_registry`,
   `bibitem_title_primary_source`, `theorem_name_embedded_citations`. First step is partitioning
   "unreachable without `--strict`" from "merely promotes an advisory under `--strict`"; the filed
   figure conflated them.
8. Memoizing `load_lean_deps()` + a shared graph handle — **reviewed together**, because both change what
   a check observes once the `*_fresh` checks regenerate artifacts mid-run (≈8 extractions / ≈20 parses of
   a 70 MB file per run today).

**Live finding from item 7, for the record:** 135 PythonTest nodes lost their last edge and are now
orphans — their *only* graph coverage was fabricated. That is the honest picture arriving, not a
regression. 16 Lean declarations likewise became orphans (they had no other edges at all).

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
  **Quarantine TEN non-snapshottable checks** (planned as nine; `bundle_source_freshness` was added when
  the harness was built): `lean_build`, `notebook_exec`, `notebook_stored_outputs_current`,
  `paper_latex_compiles`, `counts_fresh`, `tables_fresh`, `claim_clusters_fresh`,
  `tracked_hypotheses_fresh`, `bundle_figure_integrity`, `bundle_source_freshness`.
  **59 − 10 = 49** — which is what every `CHARACTERIZATION HELD — 49 checks identical` line means.
  Authoritative set: `QUARANTINE` in `tests/validate_characterization.py` (verified 2026-08-04).

### Workstream 2 — paper prose (SPECIFIED, NOT STARTED)

Fully documented; runnable by any session from the documents alone.
`docs/audits/2026-08-01-publication-readiness/` — `SYNTHESIS.md` (verdict, **80 P0s**, the systemic
finding), `REMEDIATION_PLAN.md` (BUILD / CORRECT-TO-SUBSTRATE / FACTUAL triage), plus **10 bundle
reports** in `bundles/` and **3 `CROSS-*.md`** cross-cutting reports — 13 auditors, 13 documents, but
only ten of them per-bundle. (Filed here as "13 reports"; corrected 2026-08-04.)

⚠️ **The two documents use DIFFERENT vocabularies and are not interchangeable.** "P0" is a severity
label used in `SYNTHESIS.md` §1 and in the per-finding tables of `CROSS-*.md` / `bundles/*.md`
(`X-11`, `X-14`, …). **`REMEDIATION_PLAN.md` contains the string "P0" zero times** — it re-triages the
Class-1 findings into **BUILD (B1–B8) / CORRECT-TO-SUBSTRATE (5 items) / FACTUAL (4 items)**, and its §0
explains why: `SYNTHESIS.md` §6 Phase 1 was *mis-posed*, pricing the walk-back as the fix. So a task
phrased "remediate every P0 in REMEDIATION_PLAN.md" names a set that document does not define. Track
**B1–B8 + the CORRECT/FACTUAL queues** against `REMEDIATION_PLAN.md`, and the **80 P0s** against
`SYNTHESIS.md` + the finding tables.

**Governing posture:** [[feedback-remediation-build-dont-walkback]] — fix with substance, not prose.
Publication schedule is the flexible variable; claim strength is not.

**Roster decision — ⛔ OPEN, and the "21 → 14" recorded here was UNSUPPORTED (corrected 2026-08-04).**
Nothing on disk backs 14. The audit's own recommendation is **21 → 16**, stated twice and in detail:
`SYNTHESIS.md` §5 **D-1** ("Roster consolidation, 21 → 16") and `CROSS-portfolio-coherence.md` §6.4
("**Recommended roster — 16 targets**", with a full per-target table). The merges are
**D6+D9+D12 → D6★**, **D10+D11 → D10★**, **E1+E2 → E★**, **D7 folded into D1**, **D4 §9 → D8** —
21 − 5 = 16.

Worse, **`14` is one of the stale roster counts the audit itself files as a defect**: finding **X-11**
(P0) records that manuscripts state the roster as *14, 15 and 17*, and `PAPER_STRATEGY.md:341` still
carries "All 14 bundles have shipped…" from 2026-05-07. Writing 21 → 14 into `PAPER_STRATEGY.md` would
encode the very drift the audit found. Live registry (`scripts/bundle_registry.py` → `BUNDLE_CODES`) is
**21**, verified 2026-08-04.

`SYNTHESIS.md` §5 lists D-1 among the **decisions required from the operator** — *"These gate the
remediation plan; everything else I can execute."* **Do not assume a number.** Default to the audit's
**16** if forced to proceed, and say so explicitly wherever it is written down.

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
