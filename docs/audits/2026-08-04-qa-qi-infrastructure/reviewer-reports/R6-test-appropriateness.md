<!-- Recovered verbatim 2026-08-05 from the subagent transcript
     agent-a79b51ffc3e863d3e.jsonl. This is the reviewer's own final report,
     unedited. See ../FINDINGS_REGISTER.md for the consolidated list. -->

I have enough to report. Writing it up now.

## What the test strategy gets RIGHT (specific)

**1. The mutation obligation is mechanized, and honest about its own limits.** `tests/test_d5_mutation_obligation.py` converts ADR-009's D5 prose ("a check must ship with a test that fails on a seeded defect and stays silent on correct data") into an enforced registry: every name in `validate._CHECKS` must appear in exactly one of two lists, and the backlog is ratcheted at 0. Its docstring (`:41-44`) explicitly says "THIS FILE DOES NOT PROVE A TEST IS GOOD… Do not read a green run here as coverage." That self-awareness is rare and correct.

**2. Baselines are frozen, not computed from the thing under test.** `tests/test_cannot_measure_baseline.py:44-47` states the principle outright and applies it — the 22 (check, kind) cannot-measure pairs are hand-listed, so a new silent `passed=True` fails on arrival. Same idiom in `test_validate_registry_contract.py` (`EXPECTED_CHECKS`) and `test_validate_public_surface.py` (`EXPECTED_SURFACE`).

**3. Tests are written against the *defect*, not the code.** `tests/test_readiness_submission_gate.py:26-33` reasons about which test would actually have caught the original inversion and rejects the one that wouldn't: "the defect lived in the last line of the function, not in the logic — which is exactly why a test asserting only the classification would have passed while the gate was inert." That is the right analysis, done before writing the test.

**4. The graph→gates→heatmap seam is genuinely cross-checked.** `readiness_verdicts_agree` (`scripts/validation/checks/bundles_readiness.py:27-31`) exists precisely because two subsystems compute a per-bundle verdict from different inputs and "nothing compared them, so the reassuring one could be quoted." Both directions asserted.

**5. The d5 suite is overwhelmingly genuine fault injection.** Across 13 files / 326 tests, ~294 fabricate a bad *input* and assert the real check logic fails on it. `tests/test_d5_reviews.py` and `test_d5_physics.py` are clean. Where a mock replaces the system it's usually the correct boundary — e.g. `test_d5_graph_atlas.py:219` patching `build_atlas` is right, because `check_atlas_integrity` *consumes* an atlas and feeding it a bad one is the fault to inject.

**6. Closure-guard bypasses are tested against the real corpus.** `tests/test_closure_guard_bypasses.py:84-152` replays six historically-successful bypass shapes against the real ledger and includes an anti-vacuity leg proving a well-formed record still closes.

---

## Mismatches

### Testing the wrong thing — tests that pass while the property they name is unprotected

**M1. The atlas's "cannot drift" property is a *staleness* claim; nothing tests that the derivation is *right*, and on real data it is not.**
`test_atlas_view.py` drives `build_atlas` with **two synthetic declarations** (`:16-21`). Freshness is covered by `sync_manifest._atlas_view_stale` (`:75-90`). But `_is_obstruction` (`scripts/atlas_view.py:81-85`) matches `_NOGO_RE` against the **module** name as well as the decl name. Measured on the live atlas: **454 obstruction entries, 409 unregistered**, of which **29 are module-name-only matches**. The top-ranked entry on the negative frontier is `SKEFTHawking.VestigialInflationNoGo.InflationParams.MPlRed_pos` — a positivity lemma about the reduced Planck mass, classified as a settled-dead fork because it lives in a `*NoGo*` module. Also present: `single_mem_stdSimplex`, `sqNorm_smul`, `circD5_mem_sphere5`. `scripts/atlas_view.py:319-321` prints these unfiltered as "NEGATIVE frontier — settled-dead paths". The SessionStart digest is safe (`harness_common.py:369` filters to `registered`) — but nothing tests *that filter either*, and the CLI/`export_web_atlas` paths are unfiltered. A derivation error here mis-steers agents; a staleness check cannot see it.

**M2. `NarrativeGrounding` (a P1 submission gate) is a change-detector for five historical overclaims.** `scripts/build_graph.py:1213-1219` — `_INTERESTING_PATTERNS` is five regexes reverse-engineered from specific past defects (`Ramanujan`, `all the same 16`, `first … in any proof assistant`). `_eval_narrative_grounding` (`readiness_gates.py:497-499`) then has `elif not interesting: r.state = 'passed'`. A *new* overclaim matches nothing, `interesting=False`, gate passes with note "no interesting prose claims flagged". Extraction is abstract-only (`build_graph.py:1236-1237`). The gate's name promises narrative grounding; what it protects is five sentences that were already fixed.

**M3. Numeric-claim protection is anchored regressions on numbers that were once wrong.** `tests/test_f_hierarchy_claims.py:5-8` — "targets the specific Heidelberg sentences by anchored regex." Its FAIL leg is F's *historical* stale magnitudes. Meanwhile `numerical_literals` is a **count** ratchet (`papers_prose.py:209`, `:285`) — changing `2.4\%` to `24\%` leaves the count unchanged and passes — and `\caption{}` regions are **stripped before scanning** (`papers_prose.py:240-245`). So a wrong number in a caption is invisible by construction.

**M4. Eleven tests assert data the test itself declared.** The clearest: `tests/test_d5_mutation_obligation.py:536` (`set(MUTATION_VERIFIED) & frozenset()`), `:547` (`0 <= 0`), `:556` (`0 == 0`, comparing two literals declared 8 lines apart at `:495` and `:503`), `:631` (asserts the file's own prose strings are ≥30 chars). Four of that file's six tests are currently unfalsifiable; its value rests entirely on the two that cross-reference the live registry. Also `test_d5_bundles_readiness.py:355`/`:359`, `test_d5_freshness.py:538`/`:542`, `test_d5_notebooks.py:294` — all `assert <constant> in <module constant>`.

**M5. A decoy fixture.** `tests/test_d5_prose_lean_refs.py:44-52` `_index()` returns keys `{full, short, modules, registry}`. The real `_load_lean_name_index` returns `{names, shorts, dotted_suffixes, short_to_modules, modules, registry_keys, count}` (`prose_lean_refs.py:243-251`) and `_resolve_prose_ref` reads `index["names"]` (`:355`). The fixture would `KeyError` if the resolver ran — which is why every test in the class also stubs `_resolve_prose_ref` (`:61`). `test_a_resolving_reference_passes` patches the resolver to `lambda t, i: "OK"` and then asserts the check passed. The faults here were injectable as *data*; instead the decision-maker was replaced.

**M6. A test whose docstring denies what it is.** `tests/test_d5_lean_substrate.py:302-323` says "Ships as a scan rather than a fixture list… a scan protects the next word someone adds." It is a fixture list hardcoding the 8 alternatives currently in `_LEDGER_HEDGE_RE`. A 9th with the same `\b`-closed-stem bug (the QI-28 defect) is not caught.

### Right thing, wrong level

**M7. Invariant #8 is tested at the DOM, and the behaviour it names does not exist.** This is the most serious finding. `scripts/provenance_dashboard.py:1273` sets `entry['human_verified_date'] = now` on the **in-process dict**. Persistence is a stub: `:5449-5452` `if args.write: … # TODO: implement file rewriting; return`. The route's audit event (`verification_state.record_event`) never writes `human_verified_date` — I grepped every writer: the only persistent one is the one-off `scripts/wave2_flip_provenance.py:106-118`. Both gate readers key on that field: `readiness_gates.py:248` → `state='blocked'` at `:260`, and `validation/checks/citations.py:124-137` (hard-fails under `--strict`, "paper-submission blocker"). The e2e tests assert only the badge text — `tests/e2e/test_parameters_tab.py:67` `expect(card).to_contain_text("HUMAN VERIFIED")` — and the fixture (`:16-28`) even backs up and restores the log it never reads. Net: a human clicks Confirm, sees HUMAN VERIFIED, the state dies on restart, and `validate.py --strict` in a fresh process never saw it. **A unit test on `verify_param` asserting persistence would have caught this; no browser test ever could.**

**M8. The 11 readiness gate evaluators have zero direct tests.** `grep` for all eleven `_eval_*` names plus `BLOCKING_SEVERITIES` across `tests/` returns **1 hit** — a docstring mention. `tests/test_readiness_cannot_measure.py:46` monkeypatches `rg.GATES` to a single toy evaluator and `rg.GraphIndex` to a stub. What's tested is the try/except wrapper and the aggregation. The decision logic that determines submission-readiness — including `_eval_lean_proof_substance`'s vacuous pass when a paper cites no theorems (`readiness_gates.py:359-412`) — is untested. `_eval_fix_propagation` (`:673-746`), the function that turns a Stage-13 BLOCKER into `state='blocked', priority=1`, has no test.

**M9. The graph extractor suite is unit-shaped, empty-tolerant, and deselected.** `tests/test_build_graph.py:19` `pytestmark = pytest.mark.slow`; `pyproject.toml:99` `addopts = "-m 'not slow and not e2e'"`. 115 of 5528 tests are deselected — and they are exactly the seam-verifying population. Inside it, assertions are shape-only (`_assert_valid_node`, `:576-585`) with `pytest.skip` on empty (14 sites) — **an extractor that silently returns `[]` passes**, which is the "absence of measurement rendered as success" pattern this branch's own ADR indicts, sitting in the graph layer. Most tests inspect `nodes[:10]`.

**Consequence, verified by running it:** `tests/test_build_graph.py::TestExtractReviewFindingNodes::test_node_shape` is **currently RED** and has been hidden. `:647` declares `valid_severity = {'blocker','major','minor','info','advisory','unknown'}`; the producer's vocabulary is `{critical, major, minor, advisory}` (`build_graph.py:1782-1785`). `'critical'` — the only submission-blocking value — is not in the accepted set. `AssertionError: assert 'critical' in {...}`. Pre-existing at merge-base `c2b597e1`, not introduced here.

### Untested seams

**S1. Stage-13 finding → gate: no end-to-end test.** Four files each cover one hop, none the chain: `test_closure_guard_bypasses.py` stops at `meta.status`; `test_d5_graph_atlas.py:200-205` monkeypatches `build_graph_json` so no review `.md` is ever parsed; `test_readiness_submission_gate.py:47-51` hand-builds gate dicts; `test_graph_integrity.py:205` asserts a *statistical floor* (`attach_rate >= 0.70`) — 30% of the 1561 live findings may be orphaned and it passes, and it's `slow`. Nothing walks `review .md → ReviewFinding node → FLAGS edge → Gate 11 blocked → paper RED`.

**S2. Severity vocabulary has no shared contract, and the mismatch is exploitable.** `build_graph.py:1786` `_MAP.get(_v)` returns `None` on a typo (`blockr`, `high`, `BLOCKING`) → `severity='advisory'`. Crucially the file-level BLOCKER escalation at `:1818` is gated on `if _decl is None:` — and `_decl` *is* non-None (the line matched; only the value failed). So a typo'd severity silently downgrades past `BLOCKING_SEVERITIES` (`readiness_gates.py:670`) into `needs-recheck`/P2 → paper YELLOW, gate passes. `check_review_severity_declared` (`reviews.py:269`) counts `**Severity:**` *lines*, never validates the value; its tests (`test_d5_reviews.py:211-252`) cover present/absent only.

**S3. No headings-minted reconciliation.** `check_review_docs_mint_findings` (`reviews.py:403`) fires only on `n == 0`. A doc with 12 findings where 3 headings drift format mints 9 nodes and is green everywhere. `_REVIEW_SECTION_RE` has been widened repeatedly against real reviews that minted zero — which is the evidence that partial loss happens.

**S4. `find_stage13_review_evidence` decides whether Stage 13 happened, and has no test.** `bundle_readiness.py:148-210` infers a review from a *filename* in a dated directory; the only content check is "does not contain `AGGREGATION_MARKER`". It then **writes back** into `bundle_metadata.json` (`:266-268`). Currently 3 of 21 bundles' Stage-13 dates are backfilled this way. `write_bundle_review_doc` and the heatmap writer are likewise untested.

**S5. `scripts/gate_precheck.py` — the stage gate runner — has zero tests**, and `validate_review_doc` in `scripts/review_runner.py` (also zero tests) prints "covers all sources and anchors" while checking only substring presence of source keys; `ANCHOR_DOC` is never read. `review_runner.py:115` indexes `profile_per_tier[tier]` raw where the sibling lookups deliberately use `.get(b, 1)`.

**S6. Display↔gate agreement is untested in both directions.** Nothing asserts the dashboard's rendered verification state matches what CHECK 15 / Gate 3 read. `tests/e2e/test_readiness_tab.py:13` asserts only `td count > 50` — the tab could render every cell green and pass. That is the same failure shape `test_readiness_submission_gate.py` was written to prevent, still open one layer up.

**S7. Real-data baselines are absent for ~9 of 13 d5 files.** Only `test_d5_physics.py` systematically asserts its checks pass on the live tree. Thresholds tuned only against fixtures chosen to straddle them: `_MIN_OVERLAP` 0.40, the 66-dangling baseline, `_ROSTER_LITERAL_THRESHOLD` 6. `tests/validate_characterization.py` would cover more but is **not collected** (no `test_` prefix).

---

## The bad-wave walkthrough

An AI-authored wave ships (a) a wrong number, (b) a mis-stated theorem, (c) a figure contradicting its caption.

**(a) Wrong number — `2.4%` → `24%` in bundle D7 prose.**
Stages 1–2 don't see prose. Stage 7 `numerical_literals` is a **count** ratchet — count unchanged, passes (`papers_prose.py:285`). The anchored numeric cross-checks exist only for D1 (`d1_hierarchy_table`) and F (`f_hierarchy_claims`), and F's is anchored to *specific Heidelberg sentences*. Stage 10 claims-reviewer is an LLM that may catch it; its Class-IA pass is the only real defense. Stage 13 adversarial review likewise. **Survives every programmatic stage; reaches a human only if an LLM reviewer happens to read that sentence.** If the number is in a `\caption{}`, it is stripped before the only scanner that could see it.

**(b) Mis-stated theorem — statement weakened, proof still closes.**
Stage 3a's preemptive-strengthening checklist is agent-following-instructions; `proxy_body_audit` / `vacuous_statement_audit` are the backstops and catch only the known tautology shapes. Stage 5 `lake build` is green by construction. Gate 5 `LeanProofSubstance` only checks `PlaceholderMarker` overlap — and passes vacuously when a paper cites no theorems (`readiness_gates.py:405-411`). **Survives to Stage 13.**

**(c) Figure contradicting its caption.**
Stage 8 generates the PNG. Stage 9's figure-reviewer writes `figures/figure_review_report.json` — I grepped `scripts/` and `tests/`: **zero consumers**. The "all figures PASS" gate is enforced by the agent asserting it. `bundle_figure_integrity` covers legibility for 7 of 42 PNGs. `viz_consistency` compares figure code to formulas, not caption to plot. The paper's `\caption{}` is stripped by the literal scan. **Survives to submission with no gate having looked.**

**Then the compounding failure:** suppose Stage 13 *does* catch (a). The reviewer writes `- **Severity:** blockr`. `_MAP.get` → `None`, `_decl` non-None so the escalation at `build_graph.py:1818` is skipped, severity becomes `advisory`, Gate 11 emits `needs-recheck`/P2, `paper_aggregate_state` returns **yellow**, `readiness_submission_gate` **passes**. And if the operator instead verifies the underlying parameter by hand on the dashboard, the confirmation never reaches disk (`provenance_dashboard.py:5451`), so `validate.py --strict` still blocks — the human's work is discarded in the *other* direction. Both ends of the human loop are lossy, and no test observes either.

---

## The 3 highest-value test additions, in order

**1. A unit test on `provenance_dashboard.verify_param` asserting `human_verified_date` survives a process restart — i.e. that the write reaches `src/core/provenance.py`.** Paired with an agreement test: after Confirm, `validation.checks.citations.check_parameter_provenance` (fresh import) must agree with what the Parameters tab renders. *Reasoning:* Invariant #8 is one of eight named invariants and the **only** point where human judgment enters the pipeline. It is currently a no-op with respect to its own gate, and the existing e2e test passes because it asserts the DOM. This is the single largest gap between what the infrastructure claims and what it does, and the test that closes it is ~20 lines at the right level. It will fail on landing — that is the point.

**2. One end-to-end Stage-13 lifecycle test: write a synthetic review `.md` to a temp `AutomatedReviews/` dir, run the real `extract_review_finding_nodes` → `extract_flags_edges` → `_eval_fix_propagation` → `paper_aggregate_state`, assert RED; plus a shared-vocabulary contract test pinning `build_graph._MAP`'s value set against `readiness_gates.BLOCKING_SEVERITIES`; plus a headings-vs-nodes-minted reconciliation.** *Reasoning:* Stage 13 is the last line of defense and the only stage that reads for meaning. Four tests each cover one hop and the seams between them are where two shipped defects lived (`build_graph.py:3736-3745` records ten bundles vacuously passing while six BLOCKERs sat unclosed). The severity contract is three lines and closes a live silent-downgrade I verified by code reading. The reconciliation closes partial parse loss, which the repeated widening of `_REVIEW_SECTION_RE` shows is recurrent.

**3. Extend the D5 mutation-obligation registry beyond `validate._CHECKS` to the 11 `readiness_gates._eval_*` evaluators, and give each a both-directions test.** *Reasoning:* the D5 machinery already exists and is at 100% for the check layer — but that layer asserts *consistency between derived artifacts*, while the evaluators decide *submission readiness* and have zero tests. Two of them (`NarrativeGrounding`, `LeanProofSubstance`) contain vacuous-pass branches of exactly the shape the ADR was written to eliminate. Extending an existing, respected registry is cheaper than inventing a mechanism, and it puts the obligation where the decisions are made rather than where they are reported.

*(Runner-up, cheap: fix `test_build_graph.py:647`'s severity set, drop the `nodes[:10]` slice, and split the non-Lean extractor classes out of the `slow` marker so they run by default. It is currently a red test nobody sees.)*

---

## Assessment

**Is the test strategy appropriate to what this infrastructure is for? — Partially.**

The strategy is *exemplary within one layer and absent outside it*. For the 59 `validate.py` checks the discipline is close to best-in-class: mechanized mutation obligation, frozen baselines, tests reasoned from the defect rather than the code, honest docstrings about what a green run does and does not prove. That layer is not the problem.

The problem is that this infrastructure exists to make a claim about *reality* — that a number in a paper matches a computation, that a theorem says what the prose says it says, that a human looked at a parameter — and the tested layer only checks **consistency between derived artifacts**. Everything *upstream* of the checks (the ~20 graph extractors, the atlas classifiers, the 11 gate evaluators, the Stage-13 evidence resolver) and everything *downstream* (the dashboard write path, `gate_precheck`, `review_runner`, the QI register) is under no equivalent obligation. Two-thirds of the d5 suite never runs its check against the real tree, so thresholds are tuned only against fixtures built to straddle them.

The deepest structural issue is that the correctness properties are enforced where they are *cheapest to test* rather than where they are *load-bearing*. The result is a suite that would go green on the bad wave described above at every one of the fourteen stages, while the branch's own documents name "absence of measurement rendered as success" as the systemic defect being fixed. The fix has been applied thoroughly to the check registry and not yet to the layers on either side of it.
