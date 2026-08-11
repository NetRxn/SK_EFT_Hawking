# R6 — holistic appropriateness (PR review pass 2)

**Reviewer id:** `R6` · **Branch:** `infra/adr-009-validation-modularization` @ `19ddba6d`
· **Base:** `main` @ `c2b597e1` (99 commits)
**Lens:** not line-level correctness — *are the right things tested and guarded at all?*

Every finding below carries a `CRITICAL` / `MAJOR` / `IMPORTANT` / `MINOR` label and a
stable id. Pass 1's R6 used its own `M#`/`S#` scheme and counted zero; the mapping from
those ids to these is given per finding so the register can reconcile.

**Summary:** 1 CRITICAL, 6 MAJOR, 8 IMPORTANT, 4 MINOR. Two of the CRITICAL/MAJOR set are
**new defects introduced by this branch** (`R6-C1`, `R6-MAJ1`); the rest are pass-1 findings
that survived, two of them with counts I had to correct — including one that *I* got wrong
in pass 1 by a factor of 5, in the conservative direction.

---

## 0. What the strategy gets right (unchanged from pass 1, re-verified)

The mutation obligation (`tests/test_d5_mutation_obligation.py`, 783 LOC), the frozen
cannot-measure baseline, the zero-headroom ratchet idiom, and the "reason from the defect,
not the code" docstrings are all still there and still exemplary **within the
`validate.py` check registry**. `tests/conftest.py` disabling the memo suite-wide is
exactly the right instinct, applied at the right altitude. I am not repeating pass 1's
six strengths; they hold.

The thesis of pass 1 also holds, and this pass sharpens it: *the discipline is applied
where it is cheapest to apply, not where the decisions are made.* This branch added
**526 validation-infrastructure tests** (measured, see R6-I7) and **zero** tests for the
eleven functions that decide whether a paper may be submitted.

---

## CRITICAL

### `R6-C1` — the `--ci` coverage floor cannot fire on the scenario its own docstring says it exists for. NEW ON THIS BRANCH.

**File:** `scripts/validate.py:659-680`, `scripts/validation/_config.py:108-121`,
`tests/test_ci_mode.py:128-142`

**What it claims.** `_config.py:108-119`:

> *"Dropping the Lean toolchain from a runner makes the suite ~200 s faster and stops 7
> checks that read `lean_deps.json` plus 3 that shell to `lake` from measuring anything —
> while the run still reports green. That is 'absence of measurement rendered as success'
> reintroduced at the CI layer… So `--ci` FAILS when fewer checks execute than this. A
> missing toolchain becomes a red build reading '48 of 55 ran'."*

**What it actually does.** `validate.py:660` computes `n_ran = len(results)`, and
`run_checks` (`validate.py:231-238`) inserts an entry for **every** registered spec —
`results[spec.name] = spec.func()` on success, `CheckResult(passed=False, error=...)` on
exception. A check whose toolchain is missing does not vanish from `results`; it
*early-returns `passed=True`*. So `len(results)` is always `len(_CHECKS) - len(CI_SKIP)` =
`59 - 4` = `55` = the floor, **regardless of whether anything measured**. There is no
state in which a missing Lean toolchain produces "48 of 55".

**How I verified.** Ran the most expensive Lean check with `lake` pointed at nothing:

```
$ SKEFT_VALIDATION_NO_MEMO=1 LAKE_PATH=/nonexistent/lake PATH=/usr/bin:/bin \
    uv run --no-sync python scripts/validate.py --check axiom_closure_allowlist --no-archive
  ✓ PASS  axiom_closure_allowlist: … (Invariant #15 backstop)
  ⚠ axiom_audit_run — SKIPPED — [Errno 2] No such file or directory: '/nonexistent/lake'
  Overall: 1/1 checks passed (1 warning)
  ALL CHECKS PASSED
```

PASS, and counted. Registry size confirmed independently:
`len(validate._CHECKS)=59`, `len(_cfg.CI_SKIP)=4`, `CI_MIN_CHECKS_RUN=55`.

**Why the test does not catch it — and this is the point.** The seeded-defect test
`test_a_shrunken_suite_FAILS_even_though_every_check_passed` (`tests/test_ci_mode.py:128`)
uses the `tiny_registry` fixture: it replaces `_CHECKS` with 6 toy specs and lowers the
floor to 9. It seeds *registry shrinkage*, which is the one failure mode that (a) cannot
occur on a runner without a source edit and (b) is already frozen twice over by
`EXPECTED_CHECKS` (`test_validate_registry_contract.py`) and `test_validate_public_surface.py`.
The production failure — 55 checks dispatched, ten of them measuring nothing — is
unreachable from the fixture. This is **QI-30's criterion violated in code written to
close QI-30**: the mutation was seeded in a fixture that the production artifact cannot
produce. `test_the_LIVE_floor_has_ZERO_headroom` likewise asserts
`CI_MIN_CHECKS_RUN == len(_CHECKS) - len(CI_SKIP)` — an identity between two constants,
true by construction, and blind to the same thing.

**Blast radius.** The mode is the branch's answer to R5-C1 ("no CI"). It has no caller
today (`R6-I7`), so nothing is *currently* mis-gated — but the moment a runner is wired
up, `--ci` is the guard, and its one substantive property is inert. A green
`--ci` run over a toolchain-less runner is precisely the manufactured confidence the
docstring says it prevents.

**What would settle it / fix.** The floor must count checks that **measured**, not checks
that were dispatched. The repo already has the vocabulary: `tests/test_cannot_measure_baseline.py`
enumerates the 22 (check, kind) cannot-measure return sites. Have those sites emit a
machine-readable marker on the `Detail` (e.g. `Detail(name, True, "SKIPPED — …")` already
prefixes `SKIPPED`), and make `n_ran` count `results` whose details contain no
`SKIPPED`-shaped early return. Then seed the defect in production: run `--ci` with
`LAKE_PATH` unset and assert rc==1.

---

## MAJOR

### `R6-MAJ1` — the memo caches a **fail-open SKIP** as a genuine PASS and replays it indefinitely. NEW ON THIS BRANCH.

**File:** `scripts/validation/_memo.py:memoized` (guard 3, "Only PASS is cached");
`scripts/validation/checks/lean_toolchain.py:474-517` and `:690-694`

**What it claims.** `_memo.py` guard 3: *"Only PASS is cached. A failing check re-runs
every time, so a red check can never be memoized away, and a fix is never masked by a
stale failure."*

**What it actually does.** `check_axiom_closure_allowlist` has **five** early returns that
yield `CheckResult(passed=True, …)` without running the audit — lake absent
(`:475`), `AxiomAudit.lean` missing (`:481`), `subprocess` timeout (`:498`), non-zero exit
(`:505`), unparseable JSON (`:512`). `check_lean_docstring_refs_resolve` has one
(`lean_deps.json` absent, `:692`). Every one of these is `passed=True`, so `memoized`
stores it as the last passing state, keyed on the current Lean sources + pins. The next
run — with the toolchain repaired and **no `.lean` source edit** — hits the cache and
replays the skip as a PASS. Guard 3 discriminates PASS from FAIL; it does not
discriminate *measured* PASS from *fail-open* PASS.

**How I verified.** Probe against the real `_memo.memoized`, cache redirected to a temp
path, with a single body (so `source_fingerprint` is identical between calls, exactly as
in production — my first probe used two functions and produced a false negative):

```
run 1 (build broken) -> passed=True  body-invocations=1
   detail: SKIPPED - AxiomAudit exited 1
run 2 (build FIXED)  -> passed=True  body-invocations=1
   detail: SKIPPED (cached) — Lean sources unchanged since the last PASS; …
   detail: SKIPPED - AxiomAudit exited 1
HAZARD CONFIRMED
```

The real body ran **once across two runs**; the second run's verdict is a replayed skip.

**Blast radius.** `axiom_closure_allowlist` is the Invariant #15 backstop — the only
programmatic guard against an undocumented project-local axiom. `gate_precheck.py:84`
runs the wave-close gate as `validate.py --force-latex --no-archive`: **no `--no-memo`**.
So a wave can close on a replayed skip. Only `gate_precheck submission` (`:86`,
`--strict`) bypasses. Reachable states: a `.lake` nuke mid-cycle, a transient Lean compile
error, an `elan` shim not on `PATH` in one shell, the 600 s timeout on a cold environment.

**Mitigations that exist.** The replayed detail still reads `SKIPPED — AxiomAudit
exited 1`, so a human reading details can see it; and the verdict is correct-by-policy
(the pre-memo behaviour was also a fail-open PASS). What is *new* is persistence: before
the memo the next run re-measured; now the skip is sticky until a source edit.

**Fix (small).** In `memoized`, refuse to cache a result whose details contain a
`SKIPPED`/`warning=True` early-return marker — the same predicate `test_cannot_measure_baseline.py`
already enumerates. Add the test at the production level: seed the skip through the real
check with `LAKE_PATH` bogus, then assert the cache has no entry.

### `R6-MAJ2` — `lean/SKEFTHawking.lean` — the 5,226-line root aggregate `AxiomAudit` imports — is **not** in the memo key.

**File:** `scripts/validation/_memo.py:lean_source_fingerprint`

**What it claims.** `check_axiom_closure_allowlist`'s docstring: *"The key names every
input that can move the verdict: the Lean sources (`AxiomAudit` reads the built
environment, which derives from them)…"*

**What it actually does.** `lean_source_fingerprint()` returns
`tree_fingerprint(PROJECT_ROOT/"lean"/"SKEFTHawking", "**/*.lean")`. `lean/SKEFTHawking.lean`
is a **sibling** of that directory, not a member of it.

**How I verified.**

```
files hashed by lean_source_fingerprint: 2039
any path == lean/SKEFTHawking.lean :     False
```

and `lean/SKEFTHawking/AxiomAudit.lean:32-35`:

```
import Lean
import Lean.Data.Json
import SKEFTHawking          ← the 5,226-line root aggregate at lean/SKEFTHawking.lean
import SKEFTHawking.AxiomClosure
```

`AxiomAudit.lean:49-52` folds `env.constants` filtered on the `SKEFTHawking` prefix — i.e.
the audited population **is** whatever `lean/SKEFTHawking.lean` imports.

**Blast radius.** Commenting out or deleting one `import SKEFTHawking.Foo` line removes
every declaration in `Foo` from the axiom audit. The verdict moves (a non-allow-listed
axiom in `Foo` disappears); the key does not (no file under `lean/SKEFTHawking/` changed).
Quarantining a module during a refactor is a routine operation, and it is exactly the
shape that produces this. Direction of failure: **greener**.

**Fix (one line).** Add `lean/SKEFTHawking.lean` to the `files_fingerprint` list, or glob
`lean/**/*.lean` excluding `.lake`.

### `R6-MAJ3` — `lean_deps.json` and the Mathlib package tree are read by `lean_docstring_refs_resolve` and are not in its key.

**File:** `scripts/validation/checks/lean_toolchain.py:652-712`

`check_lean_docstring_refs_resolve`'s key is `lean_source_fingerprint() + toolchain_pin_fingerprint()`.
The body reads two inputs neither of those covers:

1. **`lean/lean_deps.json`** — `_H.load_lean_deps()` at `:694`, supplying the 29,725-name
   project universe against which every docstring reference resolves. Absent → early
   return `passed=True` with warning (`:692`) — which, per `R6-MAJ1`, is then cached.
   The file *is* tracked (`git ls-files` confirms), so absence is rare; the compound with
   MAJ1 is the live risk.
2. **`lean/.lake/packages/mathlib/Mathlib`** — grepped at `:702-714` for the 138,726-name
   Mathlib exemption set. The key proxies this with `lake-manifest.json`. The proxy is
   sound for a *pin change* and unsound for **presence**: on a checkout without
   `lake exe cache get`, `mathlib_dir.exists()` is False, `mathlib_names = set()`, and the
   exemption set collapses — same manifest, different verdict. `except Exception:
   mathlib_names = set()` (`:715`) makes a `grep` timeout (180 s) do the same silently.

**How I verified.** Read the body; confirmed live cache contents
(`docs/validation/.check_memo.json` holds one entry per check; the
`lean_docstring_refs_resolve` entry replays *"scanned … against 29725 project + 138726
Mathlib names — 0 FAIL(s) in the strict families, 843 advisory elsewhere"*, i.e. both
un-keyed inputs are load-bearing in the cached verdict).

**Blast radius.** The Mathlib-absent direction produces *more* unresolvable tokens →
FAIL → not cached (safe). The `lean_deps.json`-absent direction produces PASS → cached
(unsafe). Rated MAJOR jointly with MAJ1/MAJ2 as the same class: **the key is a
hand-maintained list parallel to what the body reads** — the drift shape this repo keeps
re-finding (`EXPECTED_CHECKS`, `_REGENERATORS`, `validation_checks()`).

### `R6-MAJ4` — the 11 readiness-gate evaluators still have **zero** direct tests. *(Re-file of open finding `R6-M8`; it survived.)*

**File:** `scripts/readiness_gates.py:142-746` (804 LOC)

**How I verified.** `rg '^def _eval_' scripts/readiness_gates.py` → 11 definitions.
Programmatic scan of every `.py` under `tests/` for each name:

```
_eval_fix_propagation       tests/ occurrences: NONE
_eval_lean_proof_substance  tests/ occurrences: NONE
_eval_narrative_grounding   tests/ occurrences: NONE
```

and `rg '_eval_' tests/` returns **one** hit repo-wide — a docstring mention at
`tests/test_d5_citations.py:111`. `tests/test_readiness_cannot_measure.py:47` still
monkeypatches `rg.GATES` to `[("Exploding", 1, _boom)]` (a toy that raises) and
`rg.GraphIndex` to a 4-line stub, so what is tested is the try/except wrapper and
`paper_aggregate_state`'s mapping — not one line of any real evaluator.

**Blast radius.** These eleven functions *are* the submission decision.
`_eval_fix_propagation` (`:673-746`) is the one that turns a Stage-13 BLOCKER into
`state='blocked', priority=1`. `_eval_lean_proof_substance` (`:359-412`) still passes
vacuously when a paper cites no theorems. `_eval_narrative_grounding` (`:468-505`) still
reads `elif not interesting: r.state='passed'` over five reverse-engineered regexes
(`R6-MAJ6`'s sibling, pass-1 `R6-M2`, still open). Contrast with `R6-I7`'s count: 526
tests for the layer that *reports*, 0 for the layer that *decides*.

### `R6-MAJ5` — the human-verification write path is still a stub; Invariant #8 has no persistence and no unit test. *(Re-file; pass 1 ranked this its highest-value gap. It survived unchanged.)*

**File:** `scripts/provenance_dashboard.py:1273` (in-process write) and `:5449-5452`
(`if args.write: … # TODO: implement file rewriting; return`)

**How I verified.** `rg 'human_verified_date' scripts/ src/ tests/` → the only writers are
`provenance_dashboard.py:1273/:1278` (mutating the imported `PARAMETER_PROVENANCE` dict
in memory) and the one-off `scripts/wave2_flip_provenance.py:69`. `--write` is still
`TODO: implement file rewriting; return` (read at `:5449-5452`). Test coverage of the
route handler: `verify_param` → **0 occurrences under `tests/`**.

**Blast radius.** Both gate readers key on the field —
`readiness_gates.py:248` → `state='blocked'` at `:262`, and
`validation/checks/citations.py:124-137` (`--strict` hard fail, "paper-submission
blocker"). An operator clicks Confirm, the badge reads HUMAN VERIFIED, the state dies at
process exit, and a fresh `validate.py --strict` never saw it. The e2e test
(`tests/e2e/test_parameters_tab.py`) asserts the badge text; no browser test can catch
this and a ~20-line unit test would. **This remains the single largest gap between what
the infrastructure claims and what it does**, and it is the one place human judgement
enters the pipeline.

### `R6-MAJ6` — the atlas obstruction classifier: **144 of 409** unregistered obstructions are classified by namespace/module name alone, from **14** modules. *(Corrects pass-1 `R6-M1` — which I filed as 29 from 3 modules — and the register's re-count of the same number.)*

**File:** `scripts/atlas_view.py:81-85` (`_is_obstruction`), `:242-254` (leg b)

**Measured on the live `lean/atlas_view.json` + `lean/lean_deps.json`:**

```
total obstruction entries: 454
  registered=True :  45
  registered=False: 409
      ¬ / Not-typed (substantive)      :  85
      BASE declaration name matches    : 180
      NAMESPACE / MODULE-ONLY match    : 144   ← from 14 distinct modules
```

Top contributors: `PinPlusTraceSeamCollarBridgeNoGo` 23, `QTheoryNoGoTheorem` 21,
`VestigialInflationNoGo` 20, `SoftTheorems.DissipativeNoGo` 11,
`DarkEnergyObstructionPrinciple` 11, `DoubleCopy.BCJNoGo` 9,
`PinPlusTraceSeamTransferNoGo` 9, `FKLW.RossSelinger.RelNormEvenPowerObstruction` 9,
`KummerK7SeamCoverNoGo` 8, `RokhlinArfNoGo` 7, `FractonDarkMatter` 5,
`PinPlusTaylorConventionNoGo` 4 (+2 more).

**Why pass 1 and the register both undercounted.** Both computed "module-name-only" as
"`_NOGO_RE` misses `rec['name']` **and** misses the type head **and** hits `rec['module']`"
— which yields 29 from 3 modules, and I reproduce that number exactly. But `rec['name']`
in `lean_deps.json` is **fully qualified**, so it embeds the namespace: `_NOGO_RE.search`
on `SKEFTHawking.VestigialInflationNoGo.InflationParams.MPlRed_pos` matches *"NoGo" in the
namespace*, not in the declaration. Splitting on the last dot and testing the **base**
name gives the real population: 144. My pass-1 number was a 5× undercount in the
conservative direction; the lead's re-count inherited the same predicate.

**Concretely wrong entries.** The **highest-impact unregistered obstruction in the whole
atlas** is `SKEFTHawking.VestigialInflationNoGo.InflationParams.MPlRed_pos`
(`frontier_impact` 7) — a positivity lemma about the reduced Planck mass, ranked as a
settled-dead fork. Also present: `InflationParams.Mphi_pos`, `nSAtHilltop_eq`,
`PinPlusTraceSeamCollarBridgeNoGo.single_mem_stdSimplex`,
`DoubleCopy.adwGravityScale.eq_1`, `RossSelinger.daggerDecomposable_sq`.

**What is safe, measured.** The SessionStart digest **is** filtered:
`harness_common.antifrontier_from_atlas` takes `[o for o in obs if o.get("registered")]`
and reports the rest only as a count. The CLI (`atlas_view.py:342-348`) prints `obs[:8]`
against a registered-first sort with **45 registered entries**, so today it never reaches
an unregistered row, and rows it does print are tagged `[naming-only, unregistered]`. So
the *mis-steer* is latent, not live — I am correcting pass 1's "prints these unfiltered"
on that point. `export_web_atlas.py:166-187` is the one surface that emits the
unregistered set wholesale.

**What is untested — and this is the finding.** `antifrontier_from_atlas`,
`format_atlas_antifrontier`, `frontier_from_atlas`, `_is_obstruction` and
`classify_theorem` return **0 occurrences under `tests/`**. `tests/test_atlas_view.py`
drives `build_atlas` with two synthetic declarations. The freshness guard
(`sync_manifest._atlas_view_stale`) proves the artifact is not *stale*; nothing proves the
derivation is *right*, and on real data 35 % of the unregistered negative frontier is
derived wrong. A staleness check cannot see a derivation error.

---

## IMPORTANT

### `R6-I1` — the memo key is a hand-maintained list parallel to what the body reads, and no test asserts the two agree.

`tests/test_validation_memo.py::TestKeyCoversItsInputs` is genuinely production-seeded
(4 tests, each mutating a real file and asserting the key moves — this satisfies QI-30
and is the right idiom). But it tests only the inputs *already declared*. `R6-MAJ2` and
`R6-MAJ3` name three inputs the bodies read that no key covers, and no test in the file
could have found any of them, because the test set is derived from the key rather than
from the body. **Verified:** 24 tests in the file; zero of them inspect the check body's
read sites. A structural test — parse the memoized bodies' `open`/`read_text`/`rglob`/
`subprocess` targets and assert the set is covered by the key's contributors — is the
guard that scales. Same shape as the `_REGENERATORS` and `EXPECTED_CHECKS` drift this
audit already found twice.

### `R6-I2` — `bundle_readiness.py` (807 LOC) has no test module; the function that decides *whether Stage 13 happened* has none, and writes back. *(Re-file of open `R6-S4`.)*

**Verified:** `find_stage13_review_evidence` and `write_bundle_review_doc` → **0
occurrences under `tests/`**. `tests/test_d5_bundles_readiness.py` (30 tests) targets
`scripts/validation/checks/bundles_readiness.py` — the validate.py check — not the
807-line script. The evidence resolver infers a Stage-13 review from a **filename** in a
dated directory, content-checks only "does not contain `AGGREGATION_MARKER`", and then
persists its inference into `bundle_metadata.json`. An untested inference that writes to
the artifact the gates read is the highest-leverage untested seam in the bundle layer.

### `R6-I3` — `scripts/review_runner.py` (241 LOC) has no tests. *(Re-file; the `gate_precheck` half of `R6-S5` is now ✅ fixed — `tests/test_gate_precheck.py`, 9 tests — the `review_runner` half survived.)*

**Verified:** `validate_review_doc` → **0 occurrences under `tests/`**; no
`tests/*review_runner*` file exists.

### `R6-I4` — the Stage-9 figure-review verdict has no programmatic consumer and no gate. *(Refines pass-1's "zero consumers", which was wrong as stated.)*

**Verified:** `rg -l 'figure_review_report' scripts/ tests/ src/ .claude/` →
`scripts/provenance_dashboard.py` (three sites: load + render) and
`.claude/plugins/skeft-qa/agents/figure-reviewer.md` (the writer). So there **is** one
consumer — a *display* consumer. There are **0** in `tests/` and **0** validate.py checks.
The "all figures PASS" gate is enforced by the agent asserting it in prose. Corrects pass
1; the substance (a figure contradicting its caption reaches submission with no gate
having looked) is unchanged, and is R5-C2's territory.

### `R6-I5` — the d5 suite is still overwhelmingly fixture-driven; **4 of 13 files never touch the live tree**. *(Refines open `R6-S7`, which said "~9 of 13".)*

AST-measured (a "live-tree leg" = a test function that calls a `check_*` and takes no
fixture parameter and does no patching):

| file | tests | live-tree legs |
|---|---|---|
| `test_d5_freshness.py` | 39 | **0** |
| `test_d5_lean_statements.py` | 24 | **0** |
| `test_d5_papers_prose.py` | 25 | **0** |
| `test_d5_reviews.py` | 27 | **0** |
| `test_d5_bundles_readiness.py` | 30 | 1 |
| `test_d5_citations.py` | 27 | 1 |
| `test_d5_graph_atlas.py` | 28 | 1 |
| `test_d5_lean_substrate.py` | 37 | 1 |
| `test_d5_lean_toolchain.py` | 37 | 1 |
| `test_d5_notebooks.py` | 20 | 1 |
| `test_d5_prose_lean_refs.py` | 16 | 1 |
| `test_d5_mutation_obligation.py` | 11 | 3 |
| `test_d5_physics.py` | 32 | **5** |

Median: 1 live-tree leg against 27 fixture legs. Thresholds (`_MIN_OVERLAP` 0.40, the
66-dangling baseline, `_ROSTER_LITERAL_THRESHOLD` 6) are tuned only against fixtures
chosen to straddle them. Better than "9 of 13 absent" — but 4 files with *zero* is the
number that should be zero.

### `R6-I6` — display↔gate agreement is still untested in both directions. *(Re-file of open `R6-S6`.)*

**Verified:** `tests/e2e/test_readiness_tab.py:13` is still
`assert page.locator("#readiness-heatmap td").count() > 50`. The tab could render every
cell green and pass. This is the same failure shape `test_readiness_submission_gate.py`
was written to prevent, still open one layer up — and `R6-MAJ5` is the concrete
consequence in the other tab.

### `R6-I7` — proportionality: 2,446 LOC of tests for 537 LOC of validation plumbing, against 0 for the submission decision.

Measured:

| test file | LOC | guards |
|---|---|---|
| `test_d5_mutation_obligation.py` | 783 | the obligation registry (meta) |
| `test_validate_public_surface.py` | 452 | a frozen public-symbol list |
| `test_validation_memo.py` | 410 | `_memo.py` (317 LOC, a perf optimisation) |
| `test_validate_registry_contract.py` | 230 | check count + order |
| `test_cannot_measure_baseline.py` | 210 | the 22 frozen cannot-measure pairs |
| `test_ci_mode.py` | 196 | `--ci` (**no caller**, see below) |
| `test_always_pass_dispositions.py` | 165 | dispositions |
| **total** | **2,446** | `_memo.py` + `_config.py` + `_registry.py` = **537 LOC** |

Total validation-infrastructure tests on this branch: **526** (13 d5 files + the
`test_validate_*` / memo / ci / cannot-measure / readiness / gate_precheck set).
Against: `readiness_gates.py` 804 LOC / 11 decision functions / **0 tests**;
`bundle_readiness.py` 807 LOC / **0 test module**; `provenance_dashboard.py` 5,528 LOC /
**0 unit tests** (14 e2e DOM files only); `review_runner.py` 241 LOC / **0 tests**.

Several of the 2,446 are *right* — the mutation obligation and the cannot-measure baseline
are load-bearing meta-guards and I would keep both. But `--ci` has **no caller**:
`rg -- '--ci'` outside `tests/test_ci_mode.py` and `_config.py` docstrings returns nothing,
and `.github/workflows` does not exist. 196 LOC of tests and a 4-entry skip registry
protect a mode nothing invokes, while the eleven functions that gate arXiv submission
have none. That is the mismatch, stated as a ratio.

### `R6-I8` — the Stage-13 chain still has no end-to-end test; four tests each cover one hop. *(Re-file of open `R6-S1`, partially improved.)*

**Verified:** `extract_review_finding_nodes` appears in `test_closure_guard_bypasses.py`
(stops at `meta.status`), `test_build_graph.py` (shape-only, and `slow`-marked), and
`test_d5_reviews.py` (monkeypatched away, 4 sites). `paper_aggregate_state` appears only
in `test_readiness_cannot_measure.py`, driven from hand-built gate dicts. Nothing walks
`review .md → ReviewFinding node → FLAGS edge → Gate 11 blocked → paper RED`. The
severity-vocabulary half of pass-1's `R6-S2` **is** fixed (`4a16826e`); the chain is not.

---

## MINOR

### `R6-MIN1` — `_memo.py`'s own docstring says "the 55-check suite"; the registry holds 59.
`len(validate._CHECKS) == 59`; 55 is the post-`CI_SKIP` number. A count in a docstring
that reads as the registry size, one number off from `CI_MIN_CHECKS_RUN`, in the module
whose correctness argument is "the key names every input" — worth the one-word fix.

### `R6-MIN2` — pass-1's `R6-S7` tail is **NOT REPRODUCED**: `tests/validate_characterization.py` is not an uncollected test file.
It contains **0 `def test_`** functions. It is a deliberate before/after CLI harness
(`--record` / `--compare`) with its own docstring explaining why it is not a committed
golden. Pass 1's "would cover more but is not collected (no `test_` prefix)" mis-read it.
No action.

### `R6-MIN3` — pass-1's `R6-M4` ("eleven tests assert data the test itself declared") is **largely not reproduced** after the branch's rework.
The specific sites cited (`set(MUTATION_VERIFIED) & frozenset()`, `0 <= 0`, `0 == 0`) are
gone. What remains in `test_d5_mutation_obligation.py` is the zero-headroom ratchet idiom
(`AWAITING_CEILING == n` at `:643`, `FIXTURE_ONLY_CEILING == n` at `:698`) which is the
house pattern and defensible, plus one survivor: `:778`, `thin = … if len(why.strip()) < 30`
— a test asserting the file's own prose strings are ≥30 characters. That one still asserts
nothing about the system. My own broader AST sweep for self-referential tests flagged 77
functions repo-wide, but the heuristic is too loose to file a number against (most are
legitimate mathematical-fact assertions in `test_e8_rokhlin.py`, `test_steenrod.py` etc.);
I am not filing that count.

### `R6-MIN4` — the LaTeX closure's extension-less-`\includegraphics` hazard is real in the code and **absent in practice**.
`_draft_input_closure` (`papers_prose.py:412-447`) applies LaTeX's `.tex` default only to
`\input`/`\include` (`m.group(1)`), never to `\includegraphics` (`group(2)`), so an
extension-less graphics reference would be recorded as a non-existent path and hash as
`\0MISSING` forever — a regenerated figure would not move the draft's key. **Measured:
64 drafts, 306 closure entries, 1 non-existent** (`papers/paper15_methodology/counts.tex`,
extension-*ful*), 0 extension-less. So the hazard is latent. Noting it because the
closure's own docstring claims "deliberately a SUPERSET where it is uncertain," and this
is the one place it silently is not. Also unhashed: the pdflatex/TeX-distribution version,
and any local `.cls`/`.sty` — of which there are **0** under `papers/`, so also moot today.

---

## Was reverting the per-notebook `src/` scoping right? — **Yes, and for the right reason.**

`CI_DEFAULTS_ASSESSMENT.md` §3 records it being built (AST module-level dependency graph,
transitively closed per notebook) and then reverted after measuring blast radius by
actually editing each file: `src/core/formulas.py` → **91/91** notebooks re-execute;
`src/vestigial/hs_rhmc_mlx.py`, `src/wkb/spectrum.py`, `src/second_order/coefficients.py`
→ 82/91 each. Exact closure buys ~10 % on the common case and adds a dependency-graph
maintenance surface — one more derived artifact that can drift from what it models, which
is the class this whole audit is about.

What makes the revert *correct* rather than merely convenient is the discipline shown:
the first justification was measured on the wrong window ("of the last 400 commits, 42
touch `src/` and all 42 touch `src/core/`" — true of this infra branch, false on `main`,
where **62 of 340** `src/` commits miss `src/core/`), and it was **re-measured
structurally rather than defended**. That is `feedback-remeasure-filed-findings-before-fixing`
applied to the reviewer's own work. The same discipline appears in the memo timing (a
360.6 s first reading discarded because the seeded-invalidation probe had left the cache
keyed to an edited tree). Building it, measuring it, and deleting it is the right
outcome — and the fact that a *reverted* feature is documented with its measurement is
worth more than the feature would have been.

**Is the rest of the 2026-08-05 work proportionate?**
- `_memo.py` — **proportionate in intent, under-verified in the key.** 171.6 s → 0.1 s is
  a real win and the four structural guards are the right four. But three inputs are
  un-keyed (`R6-MAJ2`, `R6-MAJ3`) and fail-open skips are cached as passes (`R6-MAJ1`),
  so the module currently does the thing its own docstring calls "strictly worse than no
  cache." Fixable in ~15 lines. Do not merge it as-is into a wave-close path.
- The LaTeX cache — **proportionate and clearly net-positive.** It funded deleting the
  slow gate, which is why `paper_latex_compiles` now actually compiles (D3's two fatal
  errors were invisible before). The closure is a superset by construction. This is the
  best piece of work on the branch.
- `tests/conftest.py` — **exactly right, and the right altitude.** Environment variable
  rather than module patch so it survives the subprocess shell-outs. One caveat worth
  stating: because it disables the memo suite-wide, **no test in the repo ever exercises a
  memo hit against a real check** — `test_validation_memo.py` re-enables it only against
  its own `live_memo` fixture. That is the correct trade (poisoning the developer's cache
  is worse), but it means the memo↔check seam is verified only by the four
  production-seeded key probes, which is how `R6-MAJ2`/`MAJ3` got through.
- `--ci` + coverage floor — **disproportionate.** 196 LOC of tests and a config registry
  for a mode with no caller, whose one substantive guard cannot fire (`R6-C1`).

---

## What I would delete

1. **`--ci`, `CI_SKIP`, `CI_MIN_CHECKS_RUN` and `tests/test_ci_mode.py` — or fix the floor
   and wire a caller. Not both-and-neither.** As shipped it is 196 test LOC + a 4-entry
   parallel registry guarding a flag nothing invokes, whose floor is an identity between
   two constants. The register itself says "No workflow file, no schedule; that remains
   the operator's call" *and* that the fresh-clone mtime blocker must be fixed first — so
   the mode cannot be used yet even if someone wanted to. Either close `R6-C1` and add the
   caller, or delete it and re-add it with the runner.
2. **`tests/test_d5_mutation_obligation.py:778`** — the ≥30-character prose-length
   assertion on the registry's own `why` strings. It asserts the file's own text.
3. **`provenance_dashboard.py:5449-5452`'s `--write` stub** — either implement it
   (`R6-MAJ5`) or remove the flag. A CLI flag that prints *"Write mode: updating
   provenance.py with verification state…"* and then returns without writing is a
   *document describing a broken guard as fine*, in executable form. Of the two, implement:
   this is the highest-value ~20 lines on the whole branch.
4. **`_NOGO_RE` matching against `rec["name"]`** (`atlas_view.py:82`) — match the **base**
   declaration name (`name.rsplit(".",1)[-1]`) and `rec["module"]` separately, and treat a
   module-only match as advisory-at-lower-rank rather than as an OBSTRUCTION node. That
   single change removes 144 false entries from the negative frontier (`R6-MAJ6`).

---

## The three highest-value additions, in order

1. **Fix `R6-C1` and re-seed its test in production.** Count checks that *measured*, not
   checks that were *dispatched*; then assert `--ci` exits 1 with the Lean toolchain
   absent. Rationale: it is the only guard on the branch that is inert against its own
   stated purpose, it was written to close a Critical, and the fix reuses the
   cannot-measure vocabulary that already exists.
2. **Fix the three memo-key gaps and refuse to cache a fail-open skip** (`R6-MAJ1/2/3`),
   then add the *structural* key-coverage test from `R6-I1` so the fourth gap cannot land
   silently. Rationale: `gate_precheck s13` trusts the memo, `axiom_closure_allowlist` is
   the Invariant #15 backstop, and the failure direction is greener. ~15 lines of
   production, ~30 of test.
3. **Extend the D5 mutation-obligation registry to the 11 `readiness_gates._eval_*`
   evaluators** (`R6-MAJ4`), starting with `_eval_fix_propagation` and
   `_eval_lean_proof_substance`. Rationale: unchanged from pass 1 and now measured
   against the branch's own output — 526 new tests for the reporting layer, 0 for the
   deciding layer. Extending a respected mechanism is cheaper than inventing one, and it
   puts the obligation where the decisions are made.

*(Runner-up, cheap: `R6-MAJ6`'s one-line base-name fix, plus the first test for
`antifrontier_from_atlas` — the filter every agent's SessionStart digest depends on and
that nothing verifies.)*

---

## Verdict

# YES WITH FIXES

**Merge blockers — 2, both new on this branch, both small:**

- **`R6-C1`** — `--ci`'s coverage floor cannot fire on a toolchain-less runner. It is a
  guard that cannot fire, shipped as the answer to a Critical, with a fixture-seeded test
  that certifies it. That is the exact defect class named in BRIEF §4 and it did not exist
  before this branch. Fix the floor, or land `--ci` behind a documented "not yet usable"
  and delete its test file's claim to be the answer to R5-C1.
- **`R6-MAJ1`+`R6-MAJ2`** — the memo caches a fail-open skip as a PASS, and its key omits
  the root aggregate `AxiomAudit` actually imports. `gate_precheck s13` reads through the
  memo. Before this branch the second run re-measured; after it, a skip is sticky. This
  makes something worse, which is the merge-blocker test. ~15 lines.

Neither is architectural. Both are cheap. Everything else on the branch is a clear
improvement over `main` — the LaTeX gate now actually compiles, `gate_precheck submission`
gives `--strict` its first caller, and the d5 mutation obligation is real work honestly
done.

**Submission blockers (route to ADR-010, explicitly NOT merge blockers):**
`R6-MAJ4` (the submission decision is untested), `R6-MAJ5` (Invariant #8 does not
persist), `R6-MAJ6` (35 % of the unregistered negative frontier is derived wrong),
`R6-I2`, `R6-I3`, `R6-I4`, `R6-I6`, `R6-I8`. Every one of these is a pre-existing absence
that this branch did not introduce and did not worsen. They are why the *corpus* is not
ready; they are not why the *branch* is not ready. Pass 1 drew this distinction correctly
and I am re-affirming it.
