# R4 — the test suite: can it fail?

**Branch** `infra/adr-009-validation-modularization` · **head** `db430c65` · **worktree**
`.claude/worktrees/rv4` (detached at head) · **date** 2026-08-05

**Verdict: NO — do not merge as-is.**
Two tests fail on the head commit, caused by the last two commits on the branch. Separately,
one production check cannot detect a 10× drift in the fundamental constant it exists to
guard, and one check mutates nine tracked production files every time it — or the test suite
— runs.

| severity | count |
|---|---|
| CRITICAL | 2 |
| MAJOR | 3 |
| IMPORTANT | 5 |
| MINOR | 3 |

Method note: every mutation below was seeded in the **production artifact**, with
`find . -name __pycache__ -type d -exec rm -rf {} +` between seed, run, and restore, and a
post-restore re-run confirming the check returns to its baseline verdict. `git status` was
checked clean for the mutated path after every restore. Commands were
`uv run --no-sync python scripts/validate.py --check <name> --no-archive --no-memo`.

---

## Environment caveat, stated up front

The worktree's `.venv` was empty on arrival; I ran `uv sync` (default extras only). That
environment lacks `torch` and `mlx`, so my suite run is **5550 passed / 3 failed / 6 skipped**
against the brief's claimed 5575/0/5. Of the three failures, **one is a worktree artifact**
(finding I4) and **two are real and reproduce in the main checkout's tree state** — they read
tracked files (`papers/`, `lean/lean_deps.json`, both byte-identical between main and the
worktree; `lean_deps.json` is 70 612 219 bytes in both) and assert against a check verdict I
reproduced directly with `validate.py`.

---

## CRITICAL

### C1 — `parameter_provenance` reaches 37 of 206 entries, and cannot see a 10× drift in ℏ

`scripts/validation/checks/citations.py:~500` (leg 4, "Consistency: provenance value matches
actual constant"), helper `_lookup_provenance_value` in the same module.

**What breaks.** Two independent narrowings compose:

1. The comparison is guarded by `if actual is not None:`. Measured against the live registry:
   `_lookup_provenance_value` returns `None` for **169 of 206** `PARAMETER_PROVENANCE`
   entries — every key that is not `HBAR/K_B/A_BOHR/POLARITON_MASS`, not `<ATOM>.<key>`, not
   `<EXPERIMENT>.<key>`, not `<POLARITON_PLATFORM>.<key>`. Those 169 (`V_FERMI_GRAPHENE`,
   `ALPHA_GRAPHENE_HBN`, `Steinhauer.T_H_measured`, all `Dean_bilayer_nozzle.*`,
   `Majumdar.*`, `MATHER_1982_GRADIENT_REDUCTION`, …) have their `value` compared to nothing.
   The check nevertheless emits `Detail("value_consistency", True, "All provenance values
   match code")` — a claim over the whole population, from a measurement over 18 % of it.
2. Of the 37 that *are* compared, the denominator is
   `max(abs(float(actual)), 1e-30)`. For any SI-scale constant below 1e-30 the "relative"
   test silently becomes an absolute test with tolerance `1e-33`. Measured tolerated drift:
   **HBAR 9.48×, POLARITON_MASS 14.3×.**

**Concrete failing input, verified by execution.** In the production file
`src/core/provenance.py`, `PARAMETER_PROVENANCE['HBAR']['value']` changed
`1.054571817e-34 → 1.054571817e-33` (tier `MEASURED`, source "CODATA 2018 / SI 2019"):

```
registry HBAR value: 1.054571817e-33
constants HBAR     : 1.054571817e-34
  ✓ PASS  parameter_provenance: Every experimental parameter has verified provenance
  ✓ value_consistency  —  All provenance values match code
```

`__pycache__` cleared before the run; the divergence is printed from the same interpreter
session that then ran the check, so this is not a stale-bytecode artifact.

**Why the tests did not catch it.** `parameter_provenance` carries a `MUTATION_VERIFIED`
entry naming "6 mutations across coverage, LLM verification, **value consistency**, …". The
value-consistency mutation was necessarily seeded on a key the lookup resolves *and* whose
magnitude is above 1e-30 — i.e. on 18 % of the registry, in the non-degenerate regime. This
is precisely the QI-30 shape one level in: the mutation proves the branch exists, not that
the corpus reaches it. `parameter_provenance` is correctly absent from `PRODUCTION_SEEDED`.

Pipeline Invariant #8 ("every experimental parameter has verified provenance … enforced by
CHECK 15") is therefore enforced for coverage and LLM-verification, and **not** for value
agreement outside a 37-entry subset.

---

### C2 — two tests fail at HEAD; the last two commits shipped a ratchet regression

`src/core/constants.py:1422` (`LEGACY_DRAFT_UNRESOLVED_REF_CEILING = 79`);
`tests/test_d5_prose_lean_refs.py:202`; `tests/test_validate_prose_checks.py:337`.

The brief records current state as "suite 5 575 passed / 5 skipped / **0 failed**". That is
not the state of `db430c65`.

```
FAILED tests/test_d5_prose_lean_refs.py::TestProseTheoremReferenceCoverage::test_the_live_legacy_ceiling_has_ZERO_headroom
  AssertionError: the live corpus carries 83 unresolved legacy references but the ceiling is 79.
FAILED tests/test_validate_prose_checks.py::TestLiveRepoSmoke::test_prose_theorem_reference_coverage_passes
  AssertionError: [('summary', '21 bundle drafts scanned / 1051 candidate Lean references — 1 unresolved FAIL(s) …')]
```

and directly:

```
$ uv run --no-sync python scripts/validate.py --check prose_theorem_reference_coverage --no-archive
  Overall: 0/1 checks passed (1 warning)
  ● PAPER CORPUS (1): prose_theorem_reference_coverage
```

**What happened.** `c7148779` (`\texttt` aliases, +288 refs) and `c5f384b4` (`\verb`,
+276 refs) widened the scanned population from 671 to 1 051. Both are correct repairs. But
they moved the measured legacy-unresolved population from 79 to 83 and surfaced one new
bundle-side unresolved reference, and neither commit updated the ceiling or resolved the
reference. The branch's own zero-headroom ratchet — the exact instrument that exists to catch
a ceiling drifting away from its population — fired, and the commits shipped anyway.

This is a *good* outcome for the instrument and a bad one for the branch: the repairs to the
three defects the brief commissions this pass over were merged with their own guard red.
Merging as-is ships a red suite and a red `validate.py` check whose redness is *not* a
pre-existing paper-corpus condition — it was introduced by these two commits.

**Not filed as "the repair is wrong."** I checked: the widened extractor is doing the right
thing. The defect is that the ratchet and the one dangling reference were not carried with it.

---

## MAJOR

### M1 — `bundle_source_freshness` writes to nine tracked production files, on every run

`scripts/check_bundle_source_freshness.py:221-224` and `:241-245`;
`scripts/validation/checks/freshness.py:675`.

```
$ git checkout -- papers/ && git status --porcelain | wc -l
0
$ uv run --no-sync python -m pytest tests/test_d5_freshness.py -q
41 passed in 0.76s
$ git status --porcelain
 M papers/D1/bundle_metadata.json
 M papers/D2/bundle_metadata.json
 M papers/D3/bundle_metadata.json
 M papers/D4/bundle_metadata.json
 M papers/D5/bundle_metadata.json
 M papers/E1/bundle_metadata.json
 M papers/F/bundle_metadata.json
 M papers/I1/bundle_metadata.json
 M papers/L2/bundle_metadata.json
```

Every diff is `- "freshness_stale": true` → `+ "freshness_stale": false`. The same nine
files are dirtied by `validate.py --check bundle_source_freshness` alone, and therefore by
any full `validate.py` run and by the commit gate.

Three distinct problems, in ascending order of importance:

1. **Running the audit dirties the tree it audits.** The brief's rule 1 exists because pass 2
   left artifacts in a shared tree; this check *guarantees* that outcome for anyone who runs
   the suite. `tests/validate_characterization.py:133` already knows this
   (`"bundle_source_freshness": "WRITES freshness_stale into tracked bundle_metadata.json"`)
   and quarantines the check from capture — so the behaviour is known to the harness and
   still not to `pre-commit-sync.sh` or to the reviewer.
2. **It is the anti-pattern the branch pins against one check over.** The
   `tracked_hypotheses_fresh` `MUTATION_VERIFIED` note reads: *"a leg asserting the check does
   NOT write the generated doc (ADR-004 W7 M1 — a check that repairs the tree makes the drift
   invisible in review)."* `bundle_source_freshness` writes not a generated doc but **its own
   verdict**, into the artifact the dashboard and `LATE_PHASE6_ABSORPTION_PROTOCOL` read as
   the absorption trigger.
3. **HEAD's committed metadata disagrees with what the check computes.** Nine bundles carry
   `freshness_stale: true` in git and compute `false`. Whichever value is right, the
   repository ships a stale copy of a machine-written field, and the only thing that
   reconciles them is an unrelated side effect.

The `MUTATION_VERIFIED` note for this check claims the `--strict` WARN→FAIL promotion is
*"the only behaviour a bug could silently disable"*. It is not: the metadata write and the
new `UNMEASURABLE` branch from `9f62deaa` are both live behaviours with live consumers, and
neither is asserted against regression by the strict-promotion leg.

### M2 — `CheckResult.measured` reaches 14 of 21 cannot-measure-PASS sites; its guard cannot see the other 7

`tests/test_cannot_measure_baseline.py:228` (`_SKIP_WORDS`) and
`::TestSelfDeclaredSkipsDeclareMeasuredFalse`.

The guard scans `passed=True` returns whose source segment matches
`SKIPPED|not found|absent|not installed|missing|unreadable|could not`. Measured live: it
finds **24 sites, 0 non-compliant** — and passes. But the frozen
`CANNOT_MEASURE_PASS_BASELINE` holds 21 (check, kind) pairs, and an AST walk over the same
population finds **7 cannot-measure `passed=True` returns that do not set `measured=False`**,
all of them invisible to the keyword list:

| file:line | check | detail text | why the regex misses it |
|---|---|---|---|
| `freshness.py:476` | `notebook_stored_outputs_current` | `nbclient/nbformat unavailable (…); skipping` | "unavailable" / "skipping" not in the list ("SKIPPED" ≠ "skipping") |
| `lean_substrate.py:185` | `placeholder_not_cited` | `no papers/ directory` | "no X" phrasing |
| `lean_substrate.py:283` | `disclosure_consistency` | `no papers/ directory` | same |
| `lean_substrate.py:397` | `proxy_body_audit` | `no lean dir` | same |
| `lean_substrate.py:515` | `tracked_hypothesis_ledger` | `no lean_deps.json` | same |
| `reviews.py:350` | `review_severity_declared` | `no review directory` | same |
| `reviews.py:581` | `accepted_findings_carry_rationale` | `no supersession ledger; skipping` | same |

Consequence, exactly as the field's own docstring predicts for the sites it *does* cover:
`--ci`'s coverage floor (`validate.py:736-738`) counts these seven as measured, so a runner
missing `papers/`, `lean/`, `lean_deps.json` or `nbclient` can lose up to seven checks
without the floor moving. `notebook_stored_outputs_current`'s handler is the sharpest case —
it is the optional-toolchain class the field was created for.

Three of the four modules with **zero** `measured=False` sites (`lean_substrate.py`,
`reviews.py`, plus `graph_atlas.py`, `prose_lean_refs.py`, `physics.py`) are in this table,
which is the tell: the annotation pass followed the keyword scan, and the keyword scan is the
population it reached.

### M3 — `bundle_figure_integrity` passes over a corrupt shipped PNG

`scripts/validation/checks/bundles_readiness.py:67-219`.

Seeded: `papers/D11/figures/d11_fig1_phononic_band_gap.png` truncated to half its bytes
(unopenable file, still present).

```
✓ PASS  bundle_figure_integrity: Bundle figures match a fresh render and are legible at typeset size
✓ summary  —  7 bundle figures checked — 7 legible / 0 below the 8.0pt floor
⚠ drift:D11:d11_fig1_phononic_band_gap  —  shipped PNG differs from a fresh render (8c6e2949… vs 8ddf6d11…) — re-render before review
```

The drift detector fired — as `warning=True`, which does not move the verdict — and the
legibility leg measured `fn()`, the **freshly rendered figure object**, never the shipped
file. So the only property of a shipped artifact that can fail this check is its *existence*.
The registered description in `--list` reads "Bundle figures match a fresh render and are
legible at typeset size", and the docstring opens with "**Two guarantees the printed paper
actually depends on**". One of the two cannot fail. (The advisory disposition *is* stated
further down in the body — this is an overclaim in the roster line and the docstring
headline, not an undocumented behaviour.)

---

## IMPORTANT

### I1 — `physical_bounds`: `T_H > 0` and `kappa > 0` are constant-true

`scripts/validation/checks/physics.py:677`; `src/wkb/spectrum.py:60-125`.

`PlatformParams` declares `kappa: float = 1.0` and `c_s: float = 1.0`, and
`_platform_from_solver` constructs it with only `name/D/gamma_dim/description`. `T_H` is the
property `kappa / (2π)`. Measured on all three platforms:

```
Steinhauer_Rb87 kappa= 1.0 T_H= 0.15915494309189535
Heidelberg_K39  kappa= 1.0 T_H= 0.15915494309189535
Trento_Na23     kappa= 1.0 T_H= 0.15915494309189535
```

So 6 of the 15 unconditional details (`T_H > 0` and `kappa > 0` × 3 platforms) cannot fail on
any production input. Verified by seeding `src/core/formulas.py`'s
`hawking_temperature` → `return -HBAR * kappa / (2 * np.pi * K_B)` (a negative Hawking
temperature in the canonical formula module): **`physical_bounds` stayed GREEN.** The
docstring's *"Catches absurdities like negative temperatures"* describes a quantity the check
does not read; the SI-unit `T_H` is only covered by `numerical`'s 5 %-tolerance table.

The check is not wholly vacuous — seeding `gamma_dim = coeffs['Gamma_Bel'] * 1e9 / kappa` in
`src/wkb/spectrum.py` turns it red on the `0 < delta_diss < 1` leg — so this is a
partial-vacuity finding, in the natural-unit legs.

### I2 — 157 test functions never execute, and the summary reports them as 5 lines

`tests/test_hs_rhmc.py` (32), `test_hs_rhmc_mlx.py` (51), `test_hs_rhmc_stencil.py` (33),
`test_run_rhmc_mlx_driver.py` (22), `test_stencil_dirac.py` (19) are module-level
`importorskip`'d on `torch` / `mlx`, which are optional extras (`gpu`, `mlx`, `mc-all` in
`pyproject.toml`) and are **not** installed by a plain `uv sync`. pytest reports one SKIPPED
line per module, so the "5 skipped" in the headline understates the unexecuted population by
two orders of magnitude. A reader of `5575 passed / 5 skipped` has no way to learn that the
whole RHMC/stencil surface is dark. (The sixth skip, `test_bdg_self_energy.py:372`, is a
deliberate no-literature-anchor skip and is fine.)

### I3 — a `MUTATION_VERIFIED` note has decayed into a false claim, on the one check that ratchets an Invariant

`tests/test_d5_mutation_obligation.py:358-364` records for `elaboration_knob_watchlist`:
*"A leg pins that maxHeartbeats is deliberately NOT watched here — Invariant #10 bans it
outright elsewhere, and listing it would read as 'allowed with a warning'."*

Live behaviour contradicts every clause:

```
⚠ invariant_10  —  22 `maxHeartbeats` site(s) in a proof body (ceiling 22)
```

`lean_toolchain.py:694-715` builds `violations` for proof-body `maxHeartbeats`, ratchets them
at `MAXHEARTBEATS_PROOF_BODY_CEILING`, and returns `passed=not over` — i.e. this
"advisory by design" check **hard-fails** when the population grows. The test file was
already updated (`test_maxHeartbeats_in_a_proof_body_is_now_ENFORCED`,
`tests/test_d5_lean_toolchain.py:397`) and its docstring records that the previous
`test_maxHeartbeats_is_deliberately_not_watched_here` asserted a ban enforced nowhere. The
D5 registry note was not updated with it. The registry's own warning — *"a `MUTATION_VERIFIED`
entry is a claim, and claims decay"* — has a live instance.

Secondary, outside my dimension but worth surfacing: **22 proof-body `maxHeartbeats` sites
are live**, held at a ceiling, while `CLAUDE.md` states the ban is outright.

### I4 — `tests/test_phase6i_wave1.py` hardcodes a parent-walk and fails in any worktree

`tests/test_phase6i_wave1.py:20`:
`PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent`

In the main checkout that is the workspace root; in a `git worktree` under
`.claude/worktrees/rvN` it resolves to `.claude/worktrees`, so every `Lit-Search/...`
primary-source path misses and the test reports 398 "sync drift" + 10 "genuine registry bugs"
over files that exist. The file **imports `find_workspace` at line 30** and does not use it
for `PROJECT_ROOT`; `src.core.workspace.find_workspace()` resolves correctly from the
worktree (verified). This is the documented convention in `CLAUDE.md` ("Workspace-level
paths … never hardcode parent-walks"). It is the third of my three suite failures and the
only one that is a worktree artifact.

### I5 — the D5 registry's own counts are stale

`tests/test_d5_mutation_obligation.py` docstring says "the suite grew to 59 checks",
"all 59 registered checks are mutation-verified", "4 of 59 checks have been seen to fail",
"55 of 59". Live registry is **60** checks; `PRODUCTION_SEEDED` holds **5**;
`FIXTURE_ONLY_CEILING = 55` is correct arithmetic against 60. The mechanisms are all
consistent — only the prose is behind. I verified the two seam properties hold:

* All 60 registered checks are declared, `AWAITING_MUTATION_TEST` is empty, ceiling 0.
* **All 60 `MUTATION_VERIFIED` entries name a test file that actually *calls* the check
  function**, by AST (not by the file's own regex, which would accept a bare mention). Zero
  fictional entries. This part of the registry is honest.

---

## MINOR

* **m1** — `scripts/validation/checks/notebooks.py`, `check_notebook_isolation` uses
  `_H.NOTEBOOKS_DIR.glob("*.ipynb")`, not `rglob`. Latent (91 notebooks, 0 subdirectories
  today), but it is the QI-01 class at a site the QI-01 sweep did not convert, and the same
  module's `notebook_exec` and the `bundle_registry_consistency` leg-C scan were both
  converted for exactly this reason.
* **m2** — 11 test functions repo-wide contain no `assert`, `raise`, `pytest.raises` or
  `self.assert*`. Most are import smoke tests (`test_module_imports`, `test_package_imports`)
  or assert inside a called helper (`test_associativity` → `verify_a1_associativity`, which
  asserts). `tests/test_build_graph.py:557::test_write_survives_pg_unavailable` is the
  "no exception was raised" shape. Low value, low risk.
* **m3** — **UNVERIFIED BY EXECUTION.** `tests/test_ci_mode.py:157::test_the_LIVE_floor_has_ZERO_headroom` computes
  `expected = len(validate._CHECKS) - len(_cfg.CI_SKIP)` and compares it to
  `CI_MIN_CHECKS_RUN`. Post-fix the floor compares **measurements** (`r.measured`), not
  invocations, so the test pins the constant against a different quantity than the guard
  uses. It is no longer self-sealing in the pass-2 sense (the constant can now drift out of
  step and be caught), but nothing asserts that a fully-provisioned run actually *measures*
  56 — which is what M2 makes non-obvious. I attempted the live measurement
  (`validate.py --ci --no-archive`) and **abandoned it after 5+ minutes with no output**:
  `lean_build` is not in `CI_SKIP`, and a fresh worktree has no `lean/.lake/build`, so `--ci`
  shells into a cold full `lake build`. That is itself worth noting — `--ci` on a fresh clone,
  which is the mode's stated target, pays a cold Lean build before it can report anything.
  I have not measured how long, so I file the claim as unverified rather than as a finding.

---

## Things I checked that are FINE — recorded so the next pass does not re-derive them

* **The memo's cache-hit path is exercised.** `tests/conftest.py` sets
  `SKEFT_VALIDATION_NO_MEMO=1` suite-wide, but `tests/test_validation_memo.py`'s `live_memo`
  fixture (`:56-64`) `monkeypatch.delenv`s it, clears `_cfg.NO_MEMO`/`STRICT_MODE`, and
  redirects `_cache_path` to `tmp_path`. `TestMemoSemantics` covers hit-skips-body, warning
  replay, failure-never-cached, failure-evicts, legacy-shape-ignored, both bypasses, corrupt
  cache, schema bump; `TestNonMeasurementIsNeverCached` covers the `measured` interaction;
  `TestCheckKeysSpanTheirInputs` seeds real edits through `__memo_full_key__` (the R2 fix).
  The only untested configuration is the real `docs/validation/.check_memo.json` path, and
  redirecting that in tests is correct, not a gap. **Not a finding.**
* **The ratchet zero-headroom guard reaches its population.** `tests/test_ratchets_have_zero_headroom.py`
  covers six ratcheted checks; I confirmed by execution that `_population_and_ceiling`
  matches a real Detail for **all six** (`native_decide_regression` 546/546, `count_literals`
  107/107, `numerical_literals` 116/116, `theorems` 14/14, `elaboration_knob_watchlist`
  22/22, `bundle_tables_use_pipeline` 4/4). The regex `ceiling\s+(\d+)` does not match the
  *failing* message form ("above the frozen ceiling of 14"), but the test only reads the
  passing form, so this is not live.
* **`CANNOT_MEASURE_PASS_BASELINE` is exact** — live scan finds 54 (check, kind) sites, 21
  PASS, baseline 21, zero new and zero stale. The `>= 54` seam floor is at zero headroom.
* **`_verified_entries_name_a_test_that_calls_the_check`** resolves through `spec.func.__name__`
  and strips docstrings; I re-verified by AST that all 60 named tests contain a real call.

---

## Mutation-test log

All seeded in the production artifact named. "red" = `validate.py --check <name>` returned
`rc=1`. Every row was restored and re-run green afterwards.

| # | check | module | what I seeded (production artifact) | red? | notes |
|---|---|---|---|---|---|
| 1 | `numerical` | physics | `src/core/constants.py` — Steinhauer `density_upstream` `5e7 → 8e7` | **YES** | 4 Steinhauer legs fail, other platforms unaffected |
| 2 | `identities` | physics | `src/core/formulas.py` — `count_coefficients` `return (N+1)//2 + 1 → + 2` | **YES** | 3 count legs fail |
| 3 | `cross_path_consistency` | physics | `src/core/formulas.py` — `decoherence_parameter` `2.0 → 2.3` | **YES** | ratio 2.300 vs expected 2.0; the leg R4-I1 rewrote in pass 2 is live |
| 4a | `physical_bounds` | physics | `src/core/formulas.py` — `hawking_temperature` negated | **NO** | **I1** — the check reads natural-unit `T_H = kappa/2π` with `kappa` a dataclass default |
| 4b | `physical_bounds` | physics | `src/wkb/spectrum.py` — `gamma_dim = Gamma_Bel * 1e9 / kappa` | **YES** | `0 < delta_diss < 1` fails on heidelberg + trento |
| 5 | `cgl_fdr` | physics | `src/second_order/cgl_derivation.py` — `expected = 2*gamma/beta → 3*gamma/beta` | **YES** | einstein_relation leg |
| 6 | `quantum_network` | physics | `src/core/formulas.py` — `werner_param` `/3.0 → /3.1` | **YES** | |
| 7 | `formulas` | lean_substrate | `src/core/formulas.py` — docstring `thirdOrder_count → thirdOrderCount` | **YES** | `Missing from docstring: ['thirdOrder_count']` |
| 8 | `formula_grounding` | lean_statements | `src/core/formulas.py` — `Lean: dampingRate_eq_zero_iff → …ZZZ` | **YES** | 522 refs / 521 resolve / 1 dangling |
| 9 | `theorems` | lean_toolchain | `src/core/constants.py` — `ARISTOTLE_THEOREMS` key `soundSpeed_from_eos → …ZZZ` | **YES** | 15 unresolved vs frozen ceiling 14 — zero headroom confirmed |
| 10 | `lean_source` | lean_toolchain | `lean/SKEFTHawking/AcousticMetric.lean` — `theorem acousticMetric_det → …ZZZ` | **YES** | |
| 11 | `native_decide_regression` | lean_toolchain | (attempted constant rename — invalid seed, not a result) | — | population 546 == ceiling 546 confirmed separately |
| 12 | `notebooks` | notebooks | `notebooks/D11_TopologicalBandTheory_Technical.ipynb` — injected `def damping_rate(x): pass` in a code cell | **YES** | |
| 13 | `notebook_stored_outputs_current` | freshness | same notebook — stored output `certified gap edges : (1, 2) → (1, 3)` | **YES** | names the exact first divergence |
| 14 | `atlas_integrity` | graph_atlas | `src/core/constants.py` — `HYPOTHESIS_REGISTRY` `dependent_theorems` → phantom FQN | **YES** | `1 phantom target(s)` |
| 15 | `axiom_count_prose_consistency` | papers_prose | `papers/D2/paper_draft.tex` — inserted "The construction rests on one axiom." | **YES** | names file:line, non-historical context |
| 16 | `review_severity_declared` | reviews | `papers/AutomatedReviews/2026-08-01-0009-internal-adversarial/D11.md` — `Severity: blocker → blockr` | **YES** | the pass-2 reviewer-6 vocabulary leg is live in production |
| 17 | `citation_primary_sources_present` | citations | `papers/D2/paper_draft.tex` — added `\cite{GhostReferenceZZZ2099}` | **YES** | |
| 18 | `parameter_provenance` | citations | `src/core/provenance.py` — `HBAR` value ×10 | **NO** | **C1** — reports "All provenance values match code" |
| 19 | `bundle_registry_consistency` | bundles_readiness | `scripts/repo_state_probe.py` — added a 7-code literal roster | **YES** | leg C AST scan, names file:line |
| 20 | `bundle_figure_integrity` | bundles_readiness | `papers/D11/figures/d11_fig1_phononic_band_gap.png` truncated to 50 % | **NO** | **M3** — drift detected but `warning=True` |
| 21 | `theorem_name_embedded_citations` | prose_lean_refs | `papers/D5/paper_draft.tex` — bibitem author `E.~P.~Verlinde → E.~P.~Anonymous` | **NO (inconclusive)** | passes under `--strict` too; the `CITATION_REGISTRY`+`used_in` OR-fallback absorbs a bibitem-only mutation. Population is 3 declarations / 1 prose-mention check — small enough that I do not file it as a defect without a two-sided seed |
| 22 | `prose_theorem_reference_coverage` | prose_lean_refs | none needed | **already red at HEAD** | **C2** |
| 23 | `bundle_source_freshness` | freshness | none needed | — | **M1** — running it writes to 9 tracked files |

**Coverage:** 21 checks across **all 12** check modules. 17 of the 21 seeded mutations turned
the check red. Two are hard misses (C1, M3), one is a partial-vacuity miss (I1/4a), one is
inconclusive (21).

Read against `FIXTURE_ONLY_CEILING = 55`: the fixture-only population is **mostly sound** —
these were all fixture-only checks and 17 of them do fail in production. The ratchet is
honestly conservative, as its comment claims. The value of lowering it one check at a time is
that it finds the C1/M3 shape, which nothing else does.

---

## What I would require before merge

1. **C2** — resolve the one unresolved bundle reference and re-seat
   `LEGACY_DRAFT_UNRESOLVED_REF_CEILING` at the measured 83 (or fix the 4 that grew), in one
   commit, and re-run the suite to 0 failed. The branch cannot merge with two red tests.
2. **C1** — make `parameter_provenance`'s value leg report the population it reached
   (`"N of 206 values compared"`), turn a non-resolving key into a finding rather than a
   silent skip, and replace `max(abs(actual), 1e-30)` with a scale-free comparison.
3. **M1** — move the `freshness_stale` write out of the check into a regenerator, or gate it
   behind an explicit flag; then add the "does not write the tree" leg
   `tracked_hypotheses_fresh` already has.
4. **M2** — replace `_SKIP_WORDS` with a scan over `CANNOT_MEASURE_PASS_BASELINE` itself
   (the population is already frozen and exact), and annotate the seven sites.
5. **M3** — either promote the drift comparison to a failure or change the registered
   description and docstring headline to say it is advisory.

I did not fix anything. The worktree is at `db430c65` with `git status` clean.
