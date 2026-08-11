<!-- Recovered verbatim 2026-08-05 from the subagent transcript
     agent-a6f571a5361fc42c2.jsonl. This is the reviewer's own final report,
     unedited. See ../FINDINGS_REGISTER.md for the consolidated list. -->

All green. Writing up the review.

---

## Strengths (specific, with file:line)

The owner's critique does **not** describe the bulk of this work. I read all 13 `test_d5_*.py` files, 10 other new test files, and the 7 modified pre-existing ones. The dominant pattern is *synthetic-fixture, real-check, property-based* — the opposite of a change-detector.

- **Fixtures drive the real check over a synthetic corpus, never the live tree.** `test_d5_reviews.py:7-19` states the reasoning explicitly: these checks read a *self-remediating* corpus, so `assert check_x().passed` on the live tree "passes whether the check works or not, and it breaks when the corpus is legitimately remediated." Every test in that file builds `papers/AutomatedReviews/` under `tmp_path`. Same in `test_d5_lean_substrate.py`, `test_d5_lean_statements.py`, `test_d5_citations.py`.
- **Reference tables are read from the production AST, not copied.** `test_d5_physics.py:62-76` (`_literal_in_check`) and `test_d5_lean_substrate.py:95-113` pull the check's own `expected`/`mapping`/`spot_checks` literal via `ast.literal_eval`. This is exactly the fix for "two copies of a literal agreeing with each other" — the duplication is removed rather than asserted.
- **Isolated-defect legs added precisely because bundled fixtures were measured non-load-bearing.** `test_d1_hierarchy_table.py:142-172` and `test_f_hierarchy_claims.py:105-141` were added after `all_pass = all_pass and ok → all_pass` came back **MISSED**: the historical stale draft fails four ways at once, so no single ground carried the verdict. `_corrupt_cell` corrupts exactly one cell and asserts `failed == {"Steinhauer.delta_disp"}`. This is real mutation discipline, not box-ticking.
- **Structural guards that protect the *next* offender, not today's.** `test_lean_scan_coverage.py:190-206` scans the enforcement surface for `.glob("*.lean")` — and `:208-215` guards the seam (the regex actually matches the forbidden form and *not* `rglob`), so the assertion can't go vacuous. `test_d5_lean_substrate.py:302-330` does the same for hedge-regex inflections.
- **The discipline found a real latent defect.** `test_d5_lean_substrate.py:38-52` documents QI-28: strengthening the hedge test exposed that six of nine `_LEDGER_HEDGE_RE` alternatives were `\b`-closed stems that could never match an inflected form — a sixth of the check's logic was unexecutable while both check and test were green.
- **The one case the owner named by hand is fixed, and honestly.** `test_d5_lean_toolchain.py:61-76` opens with a warning that the previous `TestTheoremCount` was vacuous — two legs unreachable behind `constants.py`'s import-time assert, one a tautology — and that *"a mutation caught against a patched fixture does not establish that the check can fail in production."* The replacement resolves every registry key against real Lean declarations. `test_cross_validation.py:62` was updated in the same pass.
- **Genuinely-vacuous baselines are guarded.** `test_cannot_measure_baseline.py:167-179` asserts the AST scan found ≥30 sites *and* at least one FAIL site, "if the scanner silently matched nothing, both assertions below would pass vacuously."
- **False-positive direction is tested as deliberately as the failure direction.** `test_d5_freshness.py:377-392` measures its own jitter fixture (`assert jittered != base, "the jitter fixture is bit-identical — it tests nothing"`) after finding 1e-16 was below float64 eps.

Runtime: 317 d5 tests in **2.35 s**; the other 201 in **22 s**. All pass.

## Issues

### Critical (Must Fix)

**1. `tests/test_d5_bundles_readiness.py:375-385` — `test_an_illegible_figure_fails` is vacuous; it passes for a reason unrelated to its name.**

The test monkeypatches `bundle_figure_typeset_pt → 3.0`, then points `_H.PAPERS_DIR` at an empty `tmp_path`. Every PNG is absent, so the check takes the `missing_png` branch and `continue`s — `fn()` is never called and the patched function is never invoked. I confirmed this empirically:

```
passed: False   typeset_pt calls: 0   detail names: ['missing_png', 'summary']
```

The test's own comment admits it (`"Every PNG is absent under tmp_path, so the check fails on missing artefacts"`) — but it is still named `test_an_illegible_figure_fails` and is registered as covering the legibility guarantee. It is a duplicate of `test_a_missing_shipped_png_fails` (:387-394) with a no-op monkeypatch bolted on.

**Consequence:** `if pt < FLOOR_PT:` (`scripts/validation/checks/bundles_readiness.py:160`) has **zero** behavioural coverage. Mutating it to `if False:` would be MISSED by the whole suite. Yet `bundle_figure_integrity` sits in `MUTATION_VERIFIED` (`test_d5_mutation_obligation.py:479-484`) — which is precisely the "check a box rather than do a function" failure the owner named.

**Fix:** write a real fixture — create the shipped PNGs under `tmp_path/papers/<bundle>/figures/`, stub the `fig_*` functions, and assert `3.0 → illegible:` detail present + `passed False`, and `9.0 → legible:` + no illegible detail. Then delete `test_the_legibility_floor_is_8pt` (see Important #2), because the two-sided behavioural test subsumes it.

**2. `tests/test_d5_bundles_readiness.py:405-418` — `test_the_legibility_floor_is_8pt` is the textbook change-detector.**

```python
assert floors and floors[0].value == 8.0, (
    f"the legibility floor moved to {floors[0].value if floors else '?'} — "
    f"8.0 pt against 10 pt body text is the standard Stage-9 round 3 set")
```

It AST-scrapes `FLOOR_PT` and asserts it equals its current value. Raising the floor to 9 pt — a legitimate tightening — breaks the test while catching no defect. Worse, it is currently the *only* thing "covering" the legibility rule (see Critical #1), so it is a change-detector standing in for a behavioural test. Verbatim the owner's complaint.

**Fix:** delete it once #1 lands. The two-sided behavioural test pins the floor's *effect*, which is what matters and what survives a deliberate change.

### Important (Should Fix)

**3. `tests/test_validate_flag_propagation.py:154-163` — asserts an exact source substring.**

```python
assert 'args.force_latex or args.check == "paper_latex_compiles"' in src
```

Any reformat (operand swap, black wrapping the line, single→double quotes, adding a second auto-enabled check) fails this while the behaviour is intact. Detects no defect it doesn't share with a one-line AST test.

**Fix:** parse `main()` and assert the `FORCE_LATEX` assignment's RHS references both `force_latex` and the string `"paper_latex_compiles"`, or invoke `main(["--check","paper_latex_compiles","--dry-run"])`-style and assert `_cfg.FORCE_LATEX is True`.

**4. `tests/test_d5_lean_toolchain.py:240-258` — pins message *text*, and asserts two strings merely differ.**

```python
assert bm != am, "the two SKIP messages were unified — H4 violation"
assert "github.com/leanprover/elan" in bm
assert "github.com/leanprover/elan" not in am
```

The negative assertion is the problem: adding the elan install URL to the axiom-check skip message is a legitimate UX improvement that would fail this test with the message "H4 violation", which it is not. `bm != am` is also a weak proxy — one changed character satisfies it.

**Fix:** keep the substantive half (both callers early-return `passed=True` and each emits its own detail with its own `name`), drop the URL-presence/absence pair. If the intent is "the helper returns the resolution, not a `CheckResult`", assert that structurally on `lt._resolve_lake`'s return annotation/type instead.

**5. `tests/test_d5_mutation_obligation.py:574-589` — the seam guard is far weaker than the file claims.**

The docstring calls this "the seam guard; without it, moving a name from the backlog to the verified list would be free." It matches `\b<check_name>\b` against the raw file text. Measured: **40 of the 45 `MUTATION_VERIFIED` entries are satisfied only by a mention in the module docstring** — the tests call `check_<name>`, which `\b<name>\b` does not match. Promoting a fictional entry today costs one line of prose.

The good news: I also measured that **all 45** entries *do* reference `check_<name>` in executable code. So tightening the guard is free.

**Fix:** require the code reference, not the prose one:
```python
code = "\n".join(ast.unparse(n) for n in ast.parse(path.read_text()).body)
assert f"check_{check}" in code or re.search(rf"\b{re.escape(check)}\b", code)
```

**6. `tests/test_d5_mutation_obligation.py:547-567` — two constants in the same file asserted to agree.**

`AWAITING_MUTATION_TEST = frozenset()` (:495) and `AWAITING_CEILING = 0` (:503) are declared eight lines apart. `test_backlog_only_shrinks` asserts `0 <= 0`; `test_the_ceiling_tracks_the_backlog` asserts `0 == 0`. Neither reads anything outside this file, and the first is strictly implied by the second. With the backlog empty they are inert.

This is a defensible ratchet idiom and the file argues for it, so I'd rate it Important-not-Critical — but note the *binding* leg is `test_every_check_is_accounted_for` (:514), which reads the live `validate._CHECKS`. Consider collapsing 547-567 into one test and saying so.

**7. `tests/test_validate_registry_contract.py:48-100` — a legitimate check addition trips three tests.**

`EXPECTED_CHECKS` (59 names, frozen) is asserted by `test_check_count_is_frozen`, `test_registration_order_is_frozen`, and `test_list_names_match_registry_in_order` (:217-230). The *property* that actually matters is already tested independently by `test_regenerators_precede_their_consumers` (:102-112) and `test_every_registered_check_has_a_declared_position` (:139-152).

The count freeze is justified (`all([]) is True` — a dropped check makes the suite quieter). The full **ordering** freeze is the change-detector half: it duplicates `_CANONICAL_ORDER`, which is already the declared source of truth, and any reorder must now be edited in two places. I'd keep `test_check_count_is_frozen` + the property tests and reduce `test_registration_order_is_frozen` to `[s.name for s in v._CHECKS] == list(v._CANONICAL_ORDER)`.

### Minor

**8. `tests/test_d5_bundles_readiness.py:355-357, 359-367`** — `test_the_registry_itself_is_allowlisted` and `test_validate_is_a_declared_roster_consumer` assert membership in a constant and exercise no code path. The second has a stated policy rationale (ADR-009 H2 prohibits removal), so it earns its place as a policy pin; the first (`"bundle_registry.py" in bru._ROSTER_LITERAL_ALLOWLIST`) is redundant with `test_a_rehardcoded_roster_literal_is_detected` (:322-339), which exercises the allowlist behaviourally.

**9. `tests/test_d5_freshness.py:538-544` and `tests/test_d5_notebooks.py:294-306`** — `TestPathAliasCoupling` / `test_the_cache_path_is_derived_from_the_notebooks_dir` assert a path equals its current derivation. Both carry a genuine rationale (a test patching only `_H.NOTEBOOKS_DIR` would otherwise write the cache into the real repo), so they're not decoration — but they will fail on a legitimate relocation and the failure message won't say "you moved the file, update this."

**10. `tests/test_d5_lean_toolchain.py:145-169`** — `test_the_count_invariant_is_owned_by_constants_not_duplicated_here` bans integer-literal comparisons `> 1` in the check body via AST. Adding e.g. `if len(unresolved) > 5: <truncate the message>` — display logic, not an assertion — would trip it. The escape hatch is documented in the message ("A threshold belongs in a named constant"), which is reasonable, but the guard is broader than the invariant.

**11. `tests/test_d5_lean_toolchain.py:397-406`** — `test_maxHeartbeats_is_deliberately_not_watched_here` pins the current watchlist contents. Adding `maxHeartbeats` to the advisory watchlist would fail with a message asserting it's wrong; the rationale is stated, but it is a preference pin, not a defect guard.

**12. `tests/test_validate_public_surface.py:381-402`** — `test_surface_has_no_unexpected_public_additions` fails on any new public callable on `validate`. The remediation is stated in the message ("If this is deliberate, add it here"), which is the right way to write a change-detector you've decided to keep.

## Recommendations

1. **Fix Critical #1 first, then delete #2.** It's the single place where a change-detector is standing in for absent behavioural coverage, and it's the finding that most directly validates the owner's critique.
2. **Add a "does the mutation reach the code under test?" step to the D5 protocol.** The suite already caught six such cases and documented them honestly (`test_d5_lean_statements.py:93-102`, `test_d5_prose_lean_refs.py:90-108`, `test_d5_citations.py:295-304`, `test_d5_bundles_readiness.py:123-128`, `:224-235`). The figure test is the one that slipped through — because the check `continue`s past the mutated line rather than executing it and ignoring the result. A cheap mechanical check: assert the monkeypatched stub was *called*.
3. **Split `MUTATION_VERIFIED` into `verdict-verified` vs `warning-verified`.** Five entries are advisory-by-design checks whose "both directions" are on the warning (`viz_consistency`, `inventory_index_autogen_fresh`, `elaboration_knob_watchlist`, `atlas_hypothesis_discipline`, `paper_toolchain_pin_drift`). The registry notes say so per-entry, but "59/59 mutation-verified" reads stronger than it is. A second field would make the summary honest without weakening the ratchet.
4. **Codify the discipline you've already demonstrated.** The strongest anti-change-detector pattern here is *read the constant from the production AST rather than restating it* (`test_d5_physics.py:62`, `test_d5_lean_substrate.py:95`, `test_d5_lean_toolchain.py:176`). Applying it to `EXPECTED_CHECKS` (from `_CANONICAL_ORDER`) and `FLOOR_PT` (delete, cover behaviourally) would eliminate three of the findings above.
5. **Prefer `ast.unparse`-based structural guards over raw-text substring guards.** `test_lean_ref_normalizer.py:143-150` already gets this right and explains why ("`ast.unparse` yields CODE only, so prose can never fail the guard"). `test_validate_flag_propagation.py:160` is the outlier.

## Assessment

**Ready to merge?** With fixes

**Reasoning:** The owner's "rookie level" characterisation does not survive contact with the code — roughly **11 of 317** d5 tests (~3.5%) are change-detectors and one is outright vacuous, while the overwhelming majority drive real checks over synthetic fixtures, read production constants from the AST rather than copying them, and were demonstrably strengthened after measured MISSED mutations. Fix Critical #1 and #2 before merge (`bundle_figure_integrity`'s legibility rule currently has zero behavioural coverage while being registered as mutation-verified — the exact "box-ticking" pattern, and the one place the critique lands squarely); Important #3–#7 can follow in a cleanup pass.
