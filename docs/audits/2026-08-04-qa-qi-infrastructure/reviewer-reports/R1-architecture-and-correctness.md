<!-- Recovered verbatim 2026-08-05 from the subagent transcript
     agent-ab40f58d67ec7aa5b.jsonl. This is the reviewer's own final report,
     unedited. See ../FINDINGS_REGISTER.md for the consolidated list. -->

## Strengths (specific, file:line)

- **H1 is genuinely closed and mechanically enforced.** `scripts/validate_helpers.py:71-81` is the single anchor; `tests/test_validate_public_surface.py:186-229` AST-scans `validate.py` **plus every** `scripts/validation/**/*.py` for `__file__` outside the one bootstrap, and the scope-grows-with-the-package reasoning is written down. Grep confirms zero in-body `Path(__file__)` derivations across the 12 check modules.
- **H5 is correct.** `scripts/validation/_config.py` is a leaf module; every one of the 20 flag reads I found is `_cfg.STRICT_MODE` / `_cfg.FORCE_LATEX` / `_cfg.FORCE_NOTEBOOK_REEXEC` by attribute (`citations.py:130,667,904`; `freshness.py:617,634`; `papers_prose.py:431`; `notebooks.py:266,289`; `prose_lean_refs.py:757,767`; `lean_toolchain.py:521`). The docstring at `_config.py:22-25` correctly notes that a `co_names` structural test does *not* catch import-by-value — a real trap, correctly identified.
- **The cycle is genuinely broken.** `validation/_registry.py`, `_config.py`, `_tex.py` import nothing from the suite; `validate.py:133` re-exports `_CHECKS` **by binding** and `tests/test_validate_public_surface.py` asserts `validate._CHECKS is validation._registry._CHECKS`. The "two registries + `all([])` is True" failure mode is closed.
- **H3's mechanism is right and its own failure was caught.** `_CANONICAL_ORDER` at `validate.py:162-186`, sort at `:515` after the import block, and `tests/test_validate_registry_contract.py:154-210` asserts the call's position **from the AST including `from validation.checks import …` lines** — the only test shape that can see an early sort while the tail is coincidentally ordered.
- **`test_validate_public_surface.py:298-342`** (no module-level `_H.X` alias) is a real find: it documents the concrete `test_f_hierarchy_claims` monkeypatch that silently stopped reaching the check. Grep confirms zero bare aliases remain.
- **`--json` schema and CLI are preserved.** Verified live: `--list` prints 59, unknown `--check` → rc 2, `--check formulas --json` emits the unchanged `{elapsed_seconds, checks{passed,error,details[]}, summary}` payload. `sync_manifest.py:48-61` and `pre-commit-sync.sh:84-85` still resolve `validate._counts_is_stale` / `_tables_is_stale`.
- **`build_graph.py:3806-3850`** (VERIFIES alias guard) is well-reasoned and the two rules are the right ones; `bundle_readiness.py:274-314` (`None` vs `{}`) and `readiness_gates.py:768-788` (`blocked` not `open`) are correct fail-closed repairs with the pre-change measurement recorded.
- **`tests/test_d5_mutation_obligation.py:14-45`** — the argument for a curated registry over a scanner is correct, and the seam guard (a `MUTATION_VERIFIED` entry must name a test that mentions the check) is exactly the right third leg.
- Verified green: 153 + 313 tests across the 21 new/changed guard files.

---

## Issues

### Critical (Must Fix)

**1. The refactor silently emptied a published paper table, and it was committed that way.**
`scripts/paper_tables/sources.py:440-468` — `validation_checks()` AST-parses **`scripts/validate.py` only** for `@register_check` decorators. Phase 2 moved all 59 out, so it now returns `[]`. Verified empirically:

```
$ python -c "from paper_tables.sources import validation_checks; print(len(validation_checks()))"
0
```

`papers/paper15_methodology/tables/table2_checks.tex` went from 59 rows to a bare `\begin{tabular}…\hline\hline\end{tabular}` in commit `c3456a23` (`-59/+0` in the branch diffstat), and `papers/paper15_methodology/paper_draft.tex:136` still `\input{tables/table2_checks.tex}`. `tables_fresh` regenerated it and passed — it only compares mtimes, never content. This is precisely the ADR's own thesis (a measurement scoped by a predicate, voided when the thing the predicate keyed on moves) reproduced by the refactor, and `tests/test_inventory_index_autogen.py:138-168` even documents widening the *identical* scan two commits earlier without sweeping this one.
**Fix:** widen `validation_checks()` to `sources = [scripts/validate.py] + sorted((scripts/validation).rglob("*.py"))` (copy the loop from `test_inventory_index_autogen.py:150-153`), regenerate `render_paper_tables.py`, and add an assertion that the row count equals `len(validate._CHECKS)` so it cannot silently empty again.

---

### Important (Should Fix)

**2. `bundle_registry_consistency` Leg C lost a third of its scope.**
`scripts/validation/checks/bundles_readiness.py:887` — `for py in sorted(_H.SCRIPT_DIR.glob("*.py"))`, non-recursive. The 12 check modules now live in `scripts/validation/checks/`, which Leg C no longer reaches, so a re-hardcoded bundle roster written inside a check module is invisible to the gate whose entire purpose (docstring `:769-798`) is to stop the roster being hardcoded in seven places again. Same class as finding 1. **Fix:** `rglob("*.py")` with the allowlist keyed on the relative path, and report `n_scanned` so a scope collapse shows in the summary line.

**3. A behaviour change shipped inside the phase the ADR requires to be behaviour-preserving.**
Commit `cdb81f7e` ("ADR-009 Phases 0-1 … **all verified behaviour-preserving**") added a new suppression branch to `recurrence_reopens_closures` — now `scripts/validation/checks/reviews.py:214-215`:

```python
if (len(_a & _b) / len(_a | _b) < _MIN_OVERLAP + 0.10
        and cid.rsplit(':', 1)[-1] != oid.rsplit(':', 1)[-1]):
    continue
```

The base had a single `>= _MIN_OVERLAP` test. This is a real verdict-moving change to a guard whose threshold this project has already had to re-calibrate three times, it landed in the same commit as the mechanical helper extraction, and the commit message mentions only "de-nested the recurrence matcher". D4 says "Phases 1–2 must be provably behaviour-preserving" and Alternative 2 rejects mixing outright. The `CHARACTERIZATION HELD — 49 checks identical` claim for that boundary is therefore load-bearing on the fact that no live pair happened to sit in the 0.40–0.50 band. **Fix:** at minimum, correct the ADR §D4 status line and the commit record to state that Phase 0-1 carried one deliberate semantic change plus the `stage13_status` guard; ideally the tie-breaker should have been its own commit with its own mutation test (`test_d5_reviews.py` does now cover it — but it landed 40 commits later).

**4. `_iter_test_functions` double-yields on nested classes.**
`scripts/build_graph.py:1418-1440` — the first loop is `for node in walk(tree) if ClassDef: for sub in walk(node) if FunctionDef`. For `class Outer: class Inner: def test_x`, both `Outer` and `Inner` match the outer filter and both `walk`s reach `test_x`, so it yields twice with different qualifiers → **two PythonTest nodes for one test function**, i.e. fabricated coverage in the same edge population the commit was fixing. There are zero nested test classes today (I checked), and `tests/test_validate_public_surface.py:420-440` would fail loudly if one appeared — so this is latent, not live. **Fix:** compute the innermost enclosing class once (walk with a parent stack, or `for sub in node.body` + recurse) instead of two independent `walk`s.

**5. Documentation contradicts the code at the one place it matters for the new coupling.**
`scripts/build_graph.py:2713-2714`: *"Import here to avoid circular imports; readiness_gates imports only stdlib + logging"*. As of `scripts/readiness_gates.py:44-51` it now imports `validation._tex`, i.e. a *production* script depends on the *validation-suite* package. The dependency is fail-closed (an ImportError degrades to zero ReadinessGate nodes → `readiness_submission_gate` fails, `_blocked_p1_gates_by_paper` returns `None` → GREEN withheld), so it is safe, but the layering is inverted and the comment asserting otherwise is exactly the kind of stale claim the ADR exists to end. **Fix:** update the comment, and consider moving `find_inline_numerical_literals` to `scripts/validate_helpers.py` (already outside the package, already the shared-helper home) so the arrow points the conventional way.

**6. `test_regenerators_precede_their_consumers` was never widened, and the ADR says it should have been.**
`tests/test_validate_registry_contract.py:102-112` still asserts only `counts_fresh` against `_COUNTS_CONSUMERS`. `_REGENERATORS` names `tables_fresh` and `claim_clusters_fresh` but they appear only in an error string (`:96-99`), and the eight `lean_deps.json` consumers are not represented at all. ADR §Deferred item 0(d) explicitly says widening this property "is part of item 0's fix" — item 0's first half shipped (`ensure_lean_deps_fresh`, `validate.py:589-592`, correctly scoped to full runs so the commit gate never triggers ExtractDeps) but the guard did not. I checked the actual ordering and found **no live violation** (the physics table checks read paper drafts, not the regenerated `tables/*.tex`), so this is missing coverage rather than a live defect. **Fix:** add `_LEAN_DEPS_CONSUMERS` and `_TABLES_CONSUMERS` tuples and assert them, or delete `_REGENERATORS`' unasserted members so the tuple stops implying coverage it does not have.

**7. Merge to `main` turns the full suite red.** A full run on this branch is **57/59** — `bundle_metadata_matches_graph` and `readiness_submission_gate` both fail, by design (14 bundles at `stage13_status: green` with open blockers; 61 of 64 papers RED). ADR §Consequences documents this and it is the dial working, but `scripts/gate_precheck.py:49` runs `scripts/validate.py --no-archive` for the `s13` gate and will fail for every wave close after merge. The commit gate is unaffected (3 checks in isolation). **Decide before merging:** remediate the bundles first, or accept a red `main` gate and say so where wave operators will see it (README / WAVE_EXECUTION_PIPELINE), not only inside ADR-009.

---

### Minor

8. **Dead imports remain in `scripts/validate.py:60-73`** despite `6f4721f5` ("remove dead code and duplicate imports from the enforcement path"): `ast`, `hashlib`, `importlib`, `re`, `shutil`, `subprocess`, `tempfile`, `List` are all unreferenced (`re` appears only in a comment and a help string). `Detail`/`CheckSpec`/`register_check`/`_strip_tex_comments` are deliberate re-exports and should stay.

9. **Three module-level *derived* paths still freeze against a monkeypatched base** — `notebooks.py:51` `NOTEBOOK_EXEC_CACHE`, `freshness.py:242` `CLAIM_CLUSTERS_PATH`, `prose_lean_refs.py:290` `_PHYSLIB_DIR`. `test_no_check_module_aliases_a_path` explicitly permits these and its own message admits "it freezes the same way if the base is patched". Make them zero-arg functions, or the next test patching `_H.PROJECT_ROOT` gets a silently vacuous positive control.

10. **`validate.py:42`** still says "Checks are run in registration order" — `_CANONICAL_ORDER` replaced that. **ADR-009:33** says `validate.py` is "now **720 lines**"; it is 635. `QA_QI_INFRASTRUCTURE_MAP.md:16` and `ADR-009:522` say `build_graph.py` is 4,207 lines; it is 4,292 after this branch's own edits.

11. **Draft-scoping conversions changed two edge behaviours.** `check_disclosure_consistency`, `check_placeholder_not_cited` and `check_paper_provenance` moved from `sorted(PAPERS_DIR.iterdir())` to `_H.all_paper_drafts()`. If `papers/` is absent, the base raised (loud); the helper returns `[]` (silent skip). Detail ordering can also differ for hyphenated directory names (`A-b/` sorts before `A/` by full path, after by dir name). Both immaterial today; worth a line in the migration notes.

12. **`_iter_test_functions` reorders nodes within a file** (all class methods, then module-level tests) — irrelevant to ids, but it perturbs graph node ordering for any snapshot diff.

13. **`build_graph.py:1494`** — the loop body is indented 16 spaces under an 8-space `for`, a leftover from deleting the `if isinstance(...)`. Valid Python, ugly diff.

14. **Egress guard `_path_allowed`** (`.claude/plugins/skeft-qa/scripts/harness_web_egress_guard.py`) normalizes with `posixpath.normpath` but does not percent-decode, so `%2e%2e%2f` survives normalization. Practically harmless (the server 404s), but the docstring claims traversal is handled.

15. **Unrelated work rides on this branch:** `a41f8573` (web-egress whitelist, security-adjacent, 70 lines), `cc943091` (20 Stage-13 bundle review documents, ~1,600 lines), `9ccba366` (ADR-010 portfolio charter, 335 lines). None is an ADR-009 deliverable. Also `4c51409b` mixes a production regex fix (`_LEDGER_HEDGE_RE`, a real defect — 6 of 9 alternatives could never match) into a commit titled `test(qa-qi)`.

---

## Recommendations

- Fix #1 and #2 together — they are one bug class ("a scan scoped to `scripts/*.py` or to `validate.py`"), and a single sweep for `glob("*.py")` / hardcoded `validate.py` source reads across the repo will find any third instance.
- Add a `paper_tables` regression assertion tying `table2_checks` row count to `len(validate._CHECKS)`; the D5 registry proves every *check* is mutation-tested, but nothing proves the *generators that read the suite* still see it.
- Split the branch before merge if history matters: `a41f8573`, `cc943091` and `9ccba366` are cleanly separable and none touches the validation package.
- Correct the ADR §D4 / `cdb81f7e` record on the recurrence tie-breaker rather than leaving "all verified behaviour-preserving" standing — the ADR's credibility is its main asset here.
- **Environment note:** a concurrent session is editing this working tree (`tests/test_d5_bundles_readiness.py`, `tests/test_d5_mutation_obligation.py` and `docs/counts.json` changed under me mid-review, from another agent's `validate.py --json` run). Nothing I ran mutated the repo, but re-verify `git status` before merging.

---

## Assessment

**Ready to merge?** With fixes

**Reasoning:** The refactor itself is unusually well executed — H1/H2/H3/H5 are closed with mechanical guards rather than prose, the `--json`/CLI/private-surface contracts hold live, and 466 new tests pass — but it silently emptied a real paper table (`table2_checks.tex`) and narrowed the roster gate's scan scope, both because a source-reading consumer wasn't swept when the checks moved; those two must be fixed, and the red-on-`main` full-suite verdict needs an explicit decision rather than an ADR footnote.
