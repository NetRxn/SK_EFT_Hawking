<!-- Recovered verbatim 2026-08-05 from the subagent transcript
     agent-a803f73a5af86fc98.jsonl. This is the reviewer's own final report,
     unedited. See ../FINDINGS_REGISTER.md for the consolidated list. -->

Review complete. All 59 checks assessed; every finding below verified by running the live suite, not read off docstrings.

---

### Strengths (specific, file:line)

- **`scripts/validation/_config.py:1-60`** — the flags-by-attribute rule is genuinely load-bearing and correctly reasoned. The docstring's note that a `co_names` structural test would *not* catch an import-time flag copy is correct and is the kind of insight that prevents a whole defect class. `tests/test_validate_flag_propagation.py` enforces it.
- **`scripts/validate.py:204-220`** — `_apply_canonical_order()` is deliberately called at the file bottom, with the reasoning for why placing it at the definition site silently sorted only 45 of 59 checks recorded inline. The registry test asserts the call's *position* structurally because no behavioural test can see it.
- **`scripts/validate.py:573-576`** — an unknown `--check` name hard-errors with rc2 rather than yielding an empty result set (`all([]) is True` → silent green). Exactly the right instinct.
- **`scripts/validation/checks/graph_atlas.py:228-231`** and **`:148-150`** — two exception handlers converted from `passed=True` to fail-closed, with the account of the three dangling records filed while the guard was inert. This is the correct remediation shape.
- **`scripts/validation/checks/lean_statements.py:525-611`** (`nogo_substrate_integrity`) — the strongest gate in the suite: 126 backing theorems checked for existence, kernel purity, *and* non-vacuity against `lean_deps.json`.
- **`tests/test_cannot_measure_baseline.py:184-202`** — an exact-set ratchet that fails in **both** directions (new sites *and* stale entries). This is a better ratchet than any of the count-based ceilings.
- **`scripts/validation/checks/physics.py:{d1_hierarchy_table,f_hierarchy_claims}`** — both genuinely `read_text()` the draft and `_parse_latex_number()` the cells. Real cross-source comparisons, and the model `paper_table` should have followed.

---

### Issues

#### Critical (Must Fix)

**C1. `paper_table` never reads the paper — `scripts/validation/checks/physics.py:155-197`**

Registered as *"Paper 1 Table 1 values match solver output"*. It resolves `papers/paper1_first_order/paper_draft.tex` at :155 and uses it **only for `.exists()`**. The `.tex` is never read. The "paper" side of the comparison is a hardcoded dict at :164-168 inside the check body.

Two consequences:
- Editing Paper 1's Table 1 to any wrong value **cannot fail this check**. The one guard against published-table drift is structurally blind to the published table.
- 11 of its 12 assertions are **byte-identical** to `numerical`'s `expected` dict (`physics.py:61-65`), compared against the same `get_all_experiments()` source. Only `Steinhauer.T_H` differs (5.78e-12 vs 6.0e-12, inside the 5% tolerance). This is the QI-30 *"same comparison written twice"* shape verbatim.

The D5 test confirms the blindness while asserting the opposite: `tests/test_d5_physics.py:208` writes `(d / "paper_draft.tex").write_text("draft")` — a fixture containing no table at all — and the check passes. The seeded defect at :221 is applied to the **solver** side (`scale={"Heidelberg.T_H": 1.5}`), so the "mutation caught" proves only that the arithmetic responds to inputs. The test docstring says *"the published table and the code disagree, which is the entire purpose of the check"*; no published table is ever present.

*Fix:* parse the Table 1 cells from the `.tex` as `d1_hierarchy_table` already does (`physics.py`, `read_text` + `_parse_latex_number`), and delete the duplicated dict — `numerical` already owns that comparison.

**C2. `paper_provenance`'s theorem-reference leg examines 0 of 1,963 candidates — `scripts/validation/checks/papers_prose.py:126-127`**

```python
texttt_refs = re.findall(r'\\texttt\{([a-z_][a-zA-Z0-9_]*)\}', tex)
theorem_refs = [r for r in texttt_refs if '_' in r]
```
LaTeX writes underscores in `\texttt{}` as `\_`, and the character class cannot cross a backslash. Measured across all 64 drafts: **480 raw matches, 0 containing an underscore, against 1,963 `\texttt{}` blocks that do contain an escaped underscore** (i.e. every real Lean theorem name). The named purpose of the check runs against an empty population, and the 2,039-file `rglob` at :115 building a 19,108-name set is consumed by nothing.

Note this leg is the one QI-01 just "fixed" (`glob`→`rglob`, :107-113) — the fix was applied to a leg that cannot fire. `paper_provenance` is one of only four checks `gate_precheck.py s10` runs.

*Fix:* `r'\\texttt\{([a-zA-Z0-9_\\]+)\}'` then strip `\`; or reuse `_extract_prose_lean_candidates` from `prose_lean_refs.py`, which handles the escaping correctly.

**C3. `bibitem_title_primary_source` cannot fail in any production run, and is currently suppressing 9 live drift flags — `scripts/validation/checks/citations.py:904`**

```python
summary_passed = not _cfg.STRICT_MODE or (n_drop_word == 0 and n_not_found == 0)
```
With `STRICT_MODE=False` this reduces to the literal `True`. Every per-finding Detail also carries `passed=_cfg.STRICT_MODE is False` (:924) — constant `True`. No automated caller passes `--strict`: `gate_precheck.py:49` runs `validate.py --no-archive`, `pre-commit-sync.sh:39` runs `--check "$1"`, and there is no `.github/workflows/`.

I ran it: **PASS**, with 9 DROP-WORD flags — the exact BLOCKER class it exists to detect. Most look like PDF-extraction truncation, but `Turyshev2026DESI` has registry title `"DESI DR2 reanalysis"` against page-1 text `"…rgy after desi dr2 observational status reconstr…"`, which reads as a citation pointing at a different paper. A wrong citation shipping in a bundle is a genuinely wrong artifact.

This check is **not** in ADR-009 §Deferred item 3's eight-always-pass disposition table, so it has never been consciously ruled advisory.

**C4. `recurrence_reopens_closures`'s threshold sits above its live population — `scripts/validation/checks/reviews.py:44`**

`_RECURRENCE_MIN_OVERLAP = 0.40` (Jaccard). Measured max over the live corpus: **0.375**, across 7,489 candidate pairs (213 blocking closures × 924 later open findings). Zero pairs can clear the gate; the `_MIN_OVERLAP + 0.10` section-number tie-breaker at :214 tightens it further. Live output: `213 compared / 0 contradicted` — structurally the only reachable result.

This is the **fourth** mis-calibration of this threshold; the in-body comment at :121 cites a justifying 0.429 pair that no longer exists in the corpus. The check's own header (`:200-206`) records that its previous test re-implemented `norm()` locally and *"asserted nothing about this code"* — the replacement test (`test_d5_reviews.py:103`) instead uses synthetic fixtures scoring **Jaccard 1.0**, which is equally disconnected from the live distribution.

*Fix:* calibrate against the measured distribution (p99 = 0.200, max = 0.375) and add a test asserting the live corpus max stays below the threshold by a stated margin — otherwise the next corpus shift silently re-deadens it.

#### Important (Should Fix)

**I1. `cross_path_consistency`'s two legs are one assertion — `scripts/validation/checks/physics.py:579-601`**

Registered as *"Different code paths agree"* / *"Catches duplicate implementations that drift apart."* Leg 2 computes `dk_formulas = decoherence_parameter(Gamma_H, kappa)` and compares it to `summ['delta_k_at_T_H']`, which is `src/wkb/spectrum.py:551: dk = decoherence_parameter(Gamma_H, p.kappa)` — the **same function**. So leg 2 is leg 1 composed with a common monotone function and adds no independent constraint; the two cannot fail independently, contrary to the D5 entry's claim that they "move the verdict independently." Leg 1 measures `rel_diff = 0.0000` exactly, so the 0.5% tolerance has never been exercised (the higher-order γ terms vanish on the Steinhauer platform). Also note the check *introduces a third* inline re-implementation of the formula it is policing.

**I2. `paper_latex_compiles` is unreachable from every automated caller while D3 is genuinely broken — `scripts/validation/checks/papers_prose.py:431-435`**

`if not _cfg.FORCE_LATEX: return CheckResult(passed=True, ...)`. The default full run reports it **PASS** with detail `"SKIPPED (slow)"`. Forced, it **FAILS**: `D3: 2 fatal — ! Undefined control sequence`. So `gate_precheck.py s13`'s "full green over Stages 1–12" is achievable with a non-compiling bundle draft. The slow-gate justification is also stale — I timed the forced run at **18.0s**, not "minutes."

Partial credit: `docs/audits/.../README.md:242-243` **does** disclose this (QI-29). But ADR-009 §Deferred item 3 still claims *"Live consequence: `paper_latex_compiles` now fails on D3"*, which is false for every automated run. Either drop the slow gate (18s) or have `gate_precheck.py s13` pass `--force-latex`.

**I3. The QI-30 ratchet reports the laundering hole but leaves it open — `scripts/validation/checks/lean_substrate.py:73`**

`check_formulas_to_theorems` does `all_lean_names = set(ARISTOTLE_THEOREMS.keys())`. All 322 keys — including the 14 the new `theorems` check just proved resolve to no Lean declaration — remain in the valid-name set. The commit message correctly identifies this as the reason the fix is load-bearing, but `ARISTOTLE_REGISTRY_UNRESOLVED_CEILING = 14` against a live population of exactly 14 means the 14 fake names still launder. The generator is closed; the existing hole is not.

*Fix:* subtract the unresolved set at :73, or make `theorems` fail rather than warn once the registry is repaired.

**I4. Fail-open handler in `tracked_hypotheses_fresh` — `scripts/validation/checks/lean_substrate.py:540-541`**

A bare `except Exception` around the renderer import returns `passed=True`. Any breakage inside `render_tracked_hypotheses` at import time — including a tripped `constants.py:1372` assert, which is an `AssertionError`, not an `ImportError` — converts a real drift gate to a silent green.

**I5. `nogo_substrate_integrity` grants a free pass on empty backing — `scripts/validation/checks/lean_statements.py:561-565`**

A `KERNEL_NOGO_REGISTRY` entry with empty `backing_theorems` yields `Detail(passed=True, warning=True)` and `continue`. Population is 0 today, but this is the escape hatch on Invariant #17: adding an unbacked no-go entry buys a pass. Also `:555`'s `sorryAx` conjunct is dead (`:554`'s `issubset` already excludes it), and `:544/:553` strip `native_decide` axioms before the purity test, so a `native_decide`-backed no-go scores kernel-pure against CLAUDE.md's stated bar.

**I6. Two advertised `formula_grounding` legs are dead — `scripts/validation/checks/lean_statements.py:394-401`**

The `kind == "derivation" and is_defl` leg (the R-05 evidence-laundering gate the docstring foregrounds) and the invalid-kind leg both require entries that do not exist: `FORMULA_GROUNDING_KIND` has **2 entries, both `definitional-record`**. `:336-337` is also unreachable.

**I7. The three freshness regenerators cannot fail on staleness — `freshness.py:125, 235, 335`**

`counts_fresh` measures staleness, shells out to regenerate, then asserts only that the output files *exist* — it never re-tests staleness. `tables_fresh:235` returns `passed=True` unconditionally and does not even assert existence. Live proof from my run: `counts_fresh` detail 1 = `"stale: constants.py newer than counts.json"`, detail 2 = `"update_counts.py succeeded"`, verdict **PASS**. These are self-healing, not gates. Subprocess failure does fail closed, which is correct — but a generator exiting 0 having written nothing passes silently. Additional silent-empty holes at `:188` (`"no tables.py specs"` → not stale) and `:254/:270`.

**I8. `readiness_verdicts_agree`'s reverse leg is unreachable — `scripts/bundle_readiness.py:392-394`**

`aggregate_by_bundle` now calls `_blocked_p1_gates_by_paper()` and downgrades GREEN→YELLOW for exactly the condition the reverse leg (`bundles_readiness.py:422-434`) tests. The heatmap already consumes the gate verdict, so the two sides are no longer independent in that direction. The forward leg is genuinely independent and does work.

**I9. `atlas_integrity` on a missing `lean_deps.json` aborts the entire suite — `scripts/atlas_view.py:281`**

`raise SystemExit(...)` is a `BaseException`, so it is caught by neither `graph_atlas.py:358`'s `except Exception` nor `run_checks`'s handler at `validate.py:237`. The process exits rc=1 (so not a false green), but the ~24 checks ordered after `atlas_integrity` never run and produce no JSON — indistinguishable from a truncated run.

**I10. `notebook_exec`'s skip-cache is unsigned and gitignored — `scripts/validation/checks/notebooks.py:266-289`**

The only integrity control is a plain SHA-256 of `src/core/*.py`. A hand-written cache with the current fingerprint skips all 91 notebooks and returns unconditional PASS with zero kernels started. Currently 0 skipped / 91 executed only because `constants.py` was touched after the last cache write; the cache is rewritten unconditionally at :328, so every subsequent run skips 91/91 until `src/core` changes again. Also `:254` `except ImportError` → `passed=True` greens the most expensive check in the suite on env drift.

**I11. Six `--strict` legs have no automated caller.** `bundle_source_freshness` (`freshness.py:617`), `parameter_provenance` (`citations.py:130`, 78 params lack human verification), `provenance_doi_in_registry` (`citations.py:667`, 120 DOIs), `bibitem_title_primary_source` (C3), `axiom_closure_allowlist` (`lean_toolchain.py:521`), `theorem_name_embedded_citations` (`prose_lean_refs.py:767`). ADR-009 item 6 records this as a declined complaint with a noted residue; with C3 now demonstrating live suppressed findings, the residue is realized. Two bundles carry `stage13_redo_required: true` that `--strict` would catch.

#### Minor

- **M1.** `numerical` / `paper_table` silently `continue` on any experiment not in their 3-entry literal tables (`physics.py:78, 181`) — new platforms are unchecked with no signal.
- **M2.** `check_formulas_to_theorems` uses substring containment (`lean_substrate.py:97`), so `'secondOrder_count' in doc` is implied by `secondOrder_count_with_parity` — 2 of 11 doc assertions are degenerate.
- **M3.** `disclosure_consistency` (`lean_substrate.py:269/283`) uses a 60-char **after-only** window, detecting only theorem-as-subject phrasing; it has never had a non-zero candidate population (5 name matches, 0 verb windows corpus-wide).
- **M4.** `parameter_provenance` leg 4 is 82% blind — `_lookup_provenance_value` returns `None` for 169 of 206 entries and the skip is silent, then prints `"All provenance values match code"` (`citations.py:166`).
- **M5.** `citation_primary_sources_present`'s content half covers 69 of 652 registry entries; 420 skipped as non-parseable, 163 uncached (`citations.py:493, 498`).
- **M6.** `review_severity_declared`'s `_CUTOFF = "2026-08-01"` admits 5 of 273 review docs, and `if n_head == 0: continue` (`reviews.py:281`) drops 21 of the 26 in scope.
- **M7.** `bundle_registry_consistency`'s `_ROSTER_LITERAL_THRESHOLD = 6` (`bundles_readiness.py:759`) lets a hand-rolled roster of ≤5 codes through.
- **M8.** `bundle_consistency` records `normalized` cluster matches as advisory (`bundles_readiness.py:707`), so a fuzzy cross-bundle numerical mismatch cannot fail it; live population is 3 clusters, all `exact` — i.e. only the consistent-by-construction branch is exercised.
- **M9.** `notebooks` (isolation): exactly **1** code cell across all 91 notebooks contains any `def`. Predicate is genuine, population is ~nil.
- **M10.** `lean_build` skips-as-pass when `lake` is absent (`lean_toolchain.py:~18`) — a box without elan silently greens the zero-sorry gate. Documented as deliberate optional-toolchain policy; flagging for visibility.

---

### Does `tests/test_d5_mutation_obligation.py`'s "all 59 mutation-verified" claim hold up?

**No — it holds at the entry level and overstates at the headline.** The file is unusually honest internally (`:42-44` "THIS FILE DOES NOT PROVE A TEST IS GOOD"; `:56-60` "claims decay"), and its seam guard correctly strips docstrings after finding 3 of 59 entries satisfied by prose alone. But `:46-47` — *"All 59 registered checks are mutation-verified"* — is what a reader carries away, and it is doing work the evidence does not support.

Three structural gaps:

1. **The seam guard proves reference, not direction.** `test_verified_entries_name_a_test_that_calls_the_check` (`:597-629`) only requires the named test to mention the check function in code. Nothing asserts the test contains a `passed is False` assertion, and nothing asserts the seeded defect was applied to the operand that is actually blind.
2. **5 of the 59 entries self-declare that their "both directions" are on the *warning*, not the verdict** (`:262, 305, 339, 369, 392` — `viz_consistency`, `inventory_index_autogen_fresh`, `elaboration_knob_watchlist`, `atlas_hypothesis_discipline`, `paper_toolchain_pin_drift`). These checks cannot fail by construction and are counted toward "100%."
3. **QI-30's own residue was not applied as a sweep.** The commit that fixed `theorems` states the lesson exactly: *"A mutation caught against a patched fixture does not establish that the check can fail in production."* That lesson was recorded and then not run against the other 58.

Spot-checks (8 required; 9 performed):

| Check | Named test | Could the test pass while the check is broken? |
|---|---|---|
| `paper_table` | `test_d5_physics.py:200-235` | **Yes — proven.** Fixture `.tex` contains the literal `"draft"`; defect seeded on the solver side. The blindness to the paper is invisible to the test. |
| `paper_provenance` | `test_d5_papers_prose.py:63,70,83` | **Yes — proven.** Fixtures use raw `\texttt{real_theorem}` (unescaped `_`) — the one input shape the check can parse, and the shape no real draft uses (all 1,963 use `\_`). |
| `bibitem_title_primary_source` | `test_d5_citations.py:263` | **Yes.** `monkeypatch.setattr(_cfg, "STRICT_MODE", strict)` exercises a branch no production run reaches. |
| `recurrence_reopens_closures` | `test_d5_reviews.py:103` | **Yes.** Synthetic fixtures score Jaccard **1.0**; live corpus max is **0.375** against a 0.40 gate. |
| `cross_path_consistency` | `test_d5_physics.py` | **Yes.** Entry claims the two paths "move the verdict independently"; both route through `decoherence_parameter`. |
| `viz_consistency` | `test_d5_notebooks.py` | Entry itself discloses the directions are on the warning. Honest, but counted as verified. |
| `inventory_index_autogen_fresh` | `test_d5_freshness.py` | Same — entry discloses; all four return sites are `passed=True`. |
| `atlas_hypothesis_discipline` | `test_d5_graph_atlas.py` | Same — INFO-only by design, disclosed. |
| `notebook_exec` | `test_d5_notebooks.py:243-278` | **Mostly no** — genuinely good. Covers failure-not-cached, `--force-notebooks` bypass, code-hash and `src/core` invalidation. Does not cover a **forged** cache (I10). |

The registry mechanism (accounted-for + ratchet + seam guard) is sound and worth keeping. What it currently certifies is *"a decision was recorded for every check,"* which is what `:42-44` says — the `:46-47` headline should be brought into line with it.

---

### Table: checks that CANNOT fail (or cannot fail in production)

| Check | Module | Reason |
|---|---|---|
| `paper_table` | physics.py:155-197 | The `.tex` is opened but never read; the "paper" side is a hardcoded dict, 11/12 identical to `numerical` |
| `cross_path_consistency` | physics.py:579-601 | Both legs route through `decoherence_parameter`; one assertion written twice; measured `rel_diff = 0.0000` |
| `paper_provenance` (theorem-ref leg) | papers_prose.py:126 | Escaped-underscore regex ⇒ population 0 of 1,963 |
| `bibitem_title_primary_source` | citations.py:904 | `not STRICT_MODE or (...)` ≡ `True`; no caller passes `--strict`; 9 live flags suppressed |
| `recurrence_reopens_closures` | reviews.py:44 | Threshold 0.40 above live max 0.375 |
| `paper_latex_compiles` | papers_prose.py:431 | Early `return passed=True` unless `FORCE_LATEX`; no automated caller sets it (D3 fails when forced) |
| `viz_consistency` | notebooks.py:199 | Unconditional `passed=True`; 61 untagged `.show()` live |
| `inventory_index_autogen_fresh` | freshness.py:669,677,682 | Every return site is `passed=True` |
| `atlas_hypothesis_discipline` | graph_atlas.py:512 | Unconditional `passed=True` (INFO-only) |
| `paper_toolchain_pin_drift` | papers_prose.py:831,836,844,882 | All four return sites `passed=True`; 34 live hits |
| `elaboration_knob_watchlist` | lean_toolchain.py | Advisory by design; 46 live sites, warning-only |
| `counts_fresh` / `tables_fresh` / `claim_clusters_fresh` (staleness legs) | freshness.py:125,235,335 | Regenerate-then-pass; staleness self-heals and can never fail |
| `bundle_source_freshness` | freshness.py:617 | Only FAIL leg is `STRICT_MODE`-gated; ordinary findings hardcode `passed=True` |
| `theorem_name_embedded_citations` | prose_lean_refs.py:767 | Only real verdict is strict-only; live population = 1 |
| `readiness_verdicts_agree` (reverse leg) | bundle_readiness.py:392 | Heatmap now consumes the gate verdict it is cross-checked against |
| `formula_grounding` (R-05 legs) | lean_statements.py:394-401 | Require `kind='derivation'`; zero such entries exist |
| `nogo_substrate_integrity` (empty-backing path) | lean_statements.py:561 | Empty `backing_theorems` ⇒ passing warning + `continue` |

Zero-headroom ratchets (these **can** fail, on growth only, and are the correct idiom): `NUMERICAL_LITERAL_CEILING` 116/116, `COUNT_LITERAL_CEILING` 107/107, `NATIVE_DECIDE_DECL_CLOSURE_CEILING` 546/546, `_LEDGER_DANGLING_BASELINE` 66/66, `ARISTOTLE_REGISTRY_UNRESOLVED_CEILING` 14/14, `AWAITING_CEILING` 0/0.

---

### Assessment

**Ready to merge?** No.

**Reasoning:** The branch is already RED on its own suite (57/59 — `bundle_metadata_matches_graph` and `readiness_submission_gate`, both correctly), so it cannot merge green regardless; and the audit that motivated it did not catch four checks in the same vacuity class as QI-30 — `paper_table` (compares a hardcoded dict to itself, never reads the paper), `paper_provenance` (0 of 1,963 references examined), `bibitem_title_primary_source` (currently suppressing 9 live citation-drift flags, one of which looks like a genuinely wrong citation), and `recurrence_reopens_closures` (fourth mis-calibration, threshold above the live maximum). C1–C4 plus I3 are the merge blockers; the rest can be filed. The ADR, the migration notes and the D5 registry are excellent work and should be kept — the single change worth making to the process itself is applying QI-30's own residue as a sweep rather than a footnote: for each check, seed the defect in the **production artifact**, not in a monkeypatched fixture.
