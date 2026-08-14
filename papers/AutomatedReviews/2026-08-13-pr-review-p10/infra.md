# pr-review toolkit over today's surface — the findings not fixed in-session — 2026-08-13

**Found by** four toolkit agents (`code-reviewer`, `silent-failure-hunter` + `pr-test-analyzer`,
`comment-analyzer`, `type-design-analyzer` + `code-simplifier`) over `0bf91714~1..HEAD`, 30
files, ~2,100 lines — all of it authored the same day.

**Fixed in-session and NOT filed here** (`f6e9d08f`): the three file-collision routes in
`target_files`, the two vacuous orchestrator tests, deferred-groups-inside-`dispatch[]`, the
cross-lane fan-out cap, `lean_slots()` accepting a bare directory, the tautological partition
assert, `--slots -1`, the hand-copied severity rank, the `.flow-missing`/`absent` stylesheet
inversion, and the `orchestrate.py` row wrongly added to the operator-surfaces table.

⚠️ **The reason this filing exists is the calibration, not the count.** Four of the six
sync-audit defects earlier the same day were introduced or missed by the author; the two tests
written specifically for the file-collision regression could not fail; and three separate
drafts of the same fix each put one file in two workers' hands. **Reading did not find these.
Running and adversarial review did.**

---

## Findings

### 1 — 🟠 The Attention pane renders a fabricated decision-package verdict

- **Severity:** major
- **Lane:** infra
- **Gate:** `bundle_readiness`
- **Location:** `scripts/templates/partials/attention_tab.html:55`
- **Observed:** the template reads `item.decision_package.complete` and `.missing`.
  `dashboard_attention._decision_package()` emits only `orientation_available`,
  `orientation_command`, `not_machine_checkable`. Jinja's default `Undefined` is falsy and
  `Undefined|join` yields `''`, so the `else` branch always wins: **every finding row renders
  `missing ⟨nothing⟩`.**
- **Evidence:** measured live — all 5 `review_finding` rows render the short badge; `complete`
  is unreachable; the one machine-checkable component the module *does* compute is displayed
  nowhere.
- **Expected:** render `orientation_available` and `not_machine_checkable` as they are.
  ⚠️ **The fix belongs in the TEMPLATE.** Making the producer emit `complete`/`missing` would
  convert D11's deliberate "four of five components are not machine-checkable" into a claim
  that they were checked — the exact conversion the module's docstring forbids.
- **Verify:** `uv run python -m pytest tests/e2e -m e2e -k attention -q`

### 2 — 🟠 44 of 49 Attention rows render a raw Python dict

- **Severity:** major
- **Lane:** infra
- **Gate:** `bundle_readiness`
- **Location:** `scripts/templates/partials/attention_tab.html:48`
- **Observed:** `{{ item.label if item.label is defined else item }}`. Only `review_finding`
  items carry `label` (5 of 38 publication rows). `process` items carry `title`, `decisions`
  carry `question`/`header`, `qi_derived` carry `pattern_summary`, `qi_register_open` carry
  `heading`. Measured: publication 5/38, process 0/8, decisions 0/3.
- **Evidence:** the operator control surface prints `{'source': 'qi_derived', 'id': …}` for 44
  rows. The `is defined` fallback is what makes it silent; `StrictUndefined` would not catch it.
- **Expected:** a per-source label resolution, or one label field the producers agree on.
- **Verify:** `uv run python -m pytest tests/e2e -m e2e -k attention -q`

### 3 — 🟠 `pytest_cases` can be published as 0 and nothing guards the value

- **Severity:** major
- **Lane:** infra
- **Gate:** `counts_fresh`
- **Location:** `scripts/update_counts.py:367`
- **Observed:** `count_python` sets `pytest_cases = 0` on ANY exception, and its regex
  `(\d+)\s+tests?\s+collected` also matches a partially-collected run. The mtime legs are
  satisfied because counts.json was just written; the new count leg does not compare this key
  by design. So `counts_fresh` reports green having just published `\totaltests{0}` into every
  paper.
- **Evidence:** `grep pytest_cases` — no floor, no non-zero assertion anywhere.
- **Expected:** `count_python` refuses to write 0 rather than degrading gracefully, or the key
  joins the value compare (it costs one collection, and the check already shells out to a far
  more expensive regeneration when stale).
- **Verify:** `uv run python -m pytest tests/test_d5_freshness.py -q`

### 4 — 🟠 `_republish` voided three pre-existing freshness tests

- **Severity:** major
- **Lane:** infra
- **Gate:** `counts_fresh`
- **Location:** `tests/test_d5_freshness.py:118`
- **Observed:** the fixture republishes counts *before* each test seeds its file, so seeding
  now moves the live count too and the new value leg fires regardless of mtime.
  `test_every_tree_counts_json_publishes_is_a_staleness_input[SRC_DIR|TESTS_DIR|NOTEBOOKS_DIR]`
  therefore stays green **even if the four-tree mtime loop is deleted outright** — they no
  longer test their named subject. (`PAPERS_DIR` survives only by accident: the glob
  `paper*/paper_draft.tex` does not match the fixture's `D1/paper_draft.tex`.)
- **Evidence:** reviewer disarmed the mtime signal (seeded file stamped older than counts) and
  all three still reported stale, via the count leg.
- **Expected:** republish *after* seeding, or assert on the reason string so each leg is
  attributed to the mechanism it names.
- **Verify:** `uv run python -m pytest tests/test_d5_freshness.py -q`

### 5 — 🔵 `test_production_seeded_…`'s negative control asserts on the developer's tree

- **Severity:** minor
- **Lane:** infra
- **Gate:** `counts_fresh`
- **Location:** `tests/test_d5_freshness.py:224`
- **Observed:** the post-`finally` `assert fr._counts_is_stale()[0] is False` fails whenever
  any source has been edited since the last regeneration — reproduced by touching
  `src/wkb/spectrum.py`. The test guards its *seeded* half against exactly this (stamping
  counts.json into the future) and then reintroduces the hazard in its tail.
- **Expected:** re-stamp for the control too, or assert only `published == live`.
- **Verify:** `uv run python -m pytest tests/test_d5_freshness.py -q`

### 6 — 🔵 Three of the four claim pins assert a name, not a call

- **Severity:** minor
- **Lane:** infra
- **Gate:** `architecture_inventory_fresh`
- **Location:** `tests/test_architecture_claims.py`
- **Observed:** the census pin asserts `_shell_header` / `_notebook_first_markdown` **exist**;
  rewriting both call sites to a generic extractor keeps it green while the pinned sentence is
  false. The counts pin asserts a `count_python_cheap` call exists module-wide; neutering
  `if published.get(leg) != value:` to `if False:` leaves the leg dead and the pin green. The
  merge-gate pin counts argv literals module-wide, so an unrelated helper carrying `-m ""`
  satisfies it while the gate runs no unmarked suite.
- **Expected:** assert the CALL inside the function under test — the guide's §2.5 rule, which
  this file's own header cites.
- **Verify:** `uv run python -m pytest tests/test_architecture_claims.py -q`

### 7 — 🔵 The e2e reachability test passes on a fully errored pane

- **Severity:** minor
- **Lane:** infra
- **Gate:** `bundle_readiness`
- **Location:** `tests/e2e/test_operator_panes.py:98`
- **Observed:** `data-partial` sits on the outer `<div>`, outside the `{% if %}`, and the error
  branch renders inside that same div — so the assertion holds when the pane is 100% error. It
  does still catch the unwired regression (no include → no element).
- **Expected:** assert one content selector per tab, or `.flow-error` count == 0.
- **Verify:** `uv run python -m pytest tests/e2e/test_operator_panes.py -m e2e -q`

### 8 — 🔵 `count_python_cheap`'s `viz_file` is a derived root offered as an independent one

- **Severity:** minor
- **Lane:** infra
- **Gate:** `counts_fresh`
- **Location:** `scripts/update_counts.py:302`
- **Observed:** `VIZ_FILE = SRC_DIR / "core" / "visualizations.py"` — derived from `src_dir` —
  but the signature makes them independent and each defaults to a module global. A caller
  retargeting `src_dir` and omitting `viz_file` silently counts figures from the real repo.
  Demonstrated: a tmp-tree call returns `figures: 170`.
- **Evidence:** both non-default callers already hand-reconstruct the derivation
  (`freshness.py:220`, `test_d5_freshness.py:85`) inside a block whose comment reads *"The
  derivation is IMPORTED, never re-implemented"*.
- **Expected:** resolve `src_dir` first, then default `viz_file` from it; delete both
  reconstructions. Production behaviour is byte-identical.
- **Verify:** `uv run python -m pytest tests/test_d5_freshness.py -q`

### 9 — 🔵 The `2,360 lines` figure is wrong in three places; the true count is 1,760

- **Severity:** minor
- **Lane:** infra
- **Gate:** `architecture_inventory_fresh`
- **Location:** `docs/architecture/DASHBOARD.md:190`, `docs/adrs/ADR-012-…md:1175`,
  `papers/AutomatedReviews/2026-08-13-p9-panes-unwired/infra.md`
- **Observed:** 804 + 788 + 168 = **1,760**, and the finding that states 2,360 tabulates the
  three components two paragraphs below its own prose. No combination yields 2,360.
- **Expected:** 1,760, or "~1,800". The finding's own table is the source.
- **Verify:** `wc -l scripts/dashboard_flow.py scripts/dashboard_attention.py scripts/dashboard_loops.py`

### 10 — 🔵 The wrong commit hash anchors the `counts_fresh` repair narrative, in three places

- **Severity:** minor
- **Lane:** infra
- **Gate:** `architecture_inventory_fresh`
- **Location:** `docs/architecture/VALIDATION_ARCHITECTURE.md:295`, `scripts/update_counts.py:314`,
  `scripts/validation/checks/freshness.py:198`
- **Observed:** all three say the Index's autogen test was deleted "with the Index itself in
  `bee7608c` (ADR-013 D7)". `git log --diff-filter=D` shows **`596c941d`** deleted both the
  Index and that test; `bee7608c` deleted a *different* file (the Inventory, **D8**) and
  touched no test. Wrong hash, wrong decision id.
- **Expected:** `596c941d`, ADR-013 D7. The surrounding measurement (194 vs 193, green across
  `596c941d`→`8ef09c17`) is correct.
- **Verify:** `git log --oneline --diff-filter=D -- tests/test_inventory_index_autogen.py`

### 11 — 🔵 "mtime is kept for `pytest_cases` alone" is false in three documents

- **Severity:** minor
- **Lane:** infra
- **Gate:** `architecture_inventory_fresh`
- **Location:** `docs/architecture/VALIDATION_ARCHITECTURE.md:305`,
  `QA_QI_INFRASTRUCTURE_MAP.md:139`, `CHECK_AUTHORING_GUIDE.md:214`
- **Observed:** `_counts_is_stale` leaves **every** pre-existing mtime leg intact —
  `_COUNTS_SOURCES`, `lean/**/*.lean`, and the four-tree loop. The value leg covers only the
  five python glob figures. `counts.json` publishes ~20 `lean.*` and 2 `aristotle.*` figures
  whose ONLY protection is those mtime legs.
- **Expected:** say the value leg was ADDED beside the mtime legs, not that it replaced them.
  A reader acting on the QA_QI row could narrow the mtime legs to `tests/` and silently
  unguard every Lean count.
- **Verify:** `uv run python -m pytest tests/test_d5_freshness.py -q`

### 12 — 🔵 A comment claims all three panes refuse an empty read; only one does

- **Severity:** minor
- **Lane:** infra
- **Gate:** `bundle_readiness`
- **Location:** `scripts/provenance_dashboard.py:1163`
- **Observed:** the comment says "ON FAILURE THESE RENDER AN ERROR, NEVER AN EMPTY PANE",
  citing `flow_board()`'s refusal. Only `dashboard_flow` has it. Verified against the live app
  with the extractor returning `[]`: **Attention returns 200 and renders as a clean pane** —
  "0 open findings declare `needs_operator`" — so an unreadable `papers/AutomatedReviews/`
  reads as "nothing wants a decision".
- **Expected:** give the other two the refusal, or scope the comment to the one that has it.
- **Verify:** `uv run python -m pytest tests/test_template_contract.py -q`

### 13 — 🔵 `_counts_is_stale`'s comparison sits outside its own try, so it can raise

- **Severity:** minor
- **Lane:** infra
- **Gate:** `counts_fresh`
- **Location:** `scripts/validation/checks/freshness.py:211`
- **Observed:** with `"python": null` in counts.json, `.get("python", {})` returns `None` (the
  key is present) and `published.get(leg)` raises `AttributeError` out of the function. The
  documented contract for this leg is fail-**stale**.
- **Expected:** `(… .get("python") or {})`, or move the loop inside the `try`.
- **Verify:** `uv run python -m pytest tests/test_d5_freshness.py -q`

### 14 — 🔵 One connected component now holds 107 findings across 33 files

- **Severity:** minor
- **Lane:** infra
- **Gate:** `bundle_readiness`
- **Location:** `scripts/orchestrate.py::target_groups`
- **Observed:** connected components are correct for collision-safety but transitive: findings
  chaining through a common file (`README.md`) merge unrelated work into one unit. The live
  plan's largest group is 107 findings / 33 files, spanning four lanes.
- **Evidence:** `uv run python scripts/orchestrate.py` — the first dispatched row.
- **Expected:** a decision, not a silent fix. Either the group is genuinely one worker's block
  (defensible — they do share files), or high-degree "hub" files need excluding from the
  union so they do not chain unrelated components. ⚠️ **Excluding hubs re-admits the
  collision** for those files, so it is a tradeoff to state, not to bury.
- **Verify:** `uv run python scripts/orchestrate.py --json`
