# R2 — test quality

**Reviewer:** R2 · **Lens:** do the tests actually test anything?
**Branch:** `infra/adr-009-validation-modularization` · **Base:** `main` @ `c2b597e1`
**Date:** 2026-08-05

---

## 0. Suite baseline — measured, not assumed

```
$ uv run --no-sync python -m pytest tests/ -q
5482 passed, 5 skipped, 118 deselected, 7 warnings in 280.85s (0:04:40)
```

Green. `--collect-only` reports `5483/5601 tests collected (118 deselected)`. No
`pytest-xdist`, no `pytest-randomly` installed, so the suite is single-process and
file-ordered.

Static census of the 39 changed/added test files: **775 test functions, exactly 1 with no
assertion** (`tests/test_build_graph.py:557::test_write_survives_pg_unavailable` — and that
one is pre-existing on `main`, verified by `git show c2b597e1:tests/test_build_graph.py`).
So the crude form of theatre is essentially absent. Everything below is the subtle form.

I also ran a **whole-population mutation sweep** — neutering each of the 59 registered checks
in turn, in production source (§6). **0 of 59 went undetected.** Every check has at least one
test that can tell it apart from a no-op. On the crude axis this suite is genuinely not
theatre, and that result should be weighed against everything below.

**Headline.** The suite is unusually self-aware — it hunts its own theatre in docstrings and
it repaired several real vacuities during this branch. But three of the branch's *flagship*
new guards cannot fire for the failure mode they were built for, and I proved three of my
findings by seeding the defect into the **production** source and watching the suite stay
green — including the exact historical regex regression that corrupted D12's blocker count
(§R2-MAJ3), which all 5,482 tests tolerate.

---

## 0.1 Finding index (29 findings — grep-safe, one severity word per row)

| id | severity | one line |
|---|---|---|
| R2-C1 | CRITICAL | `--ci` coverage floor counts registered checks, not measuring ones — dead code against the failure mode it names; `test_ci_mode.py:157` pins the tautology |
| R2-C2 | CRITICAL | memo "production-seeded key tests" test the hash helpers, not any check's key — proved by deleting `lean_source_fingerprint` from production; 24/24 still green |
| R2-C3 | CRITICAL | a `SKIPPED — lake not found` PASS is cached by the memo and replayed forever; demonstrated; no test covers it |
| R2-MAJ1 | MAJOR | cannot-measure baseline scanner is blind to 12 of 36 silent-PASS sites; `(check,kind)` keying hides 3 more; seam guard has 44 % headroom |
| R2-MAJ2 | MAJOR | `test_it_stays_advisory` asserts `True is True` — the check has only `passed=True` returns |
| R2-MAJ3 | MAJOR | `_infer_bundle_from_text` has zero real coverage; the D12 regex regression is invisible to all 5,482 tests (proved) |
| R2-MAJ4 | MAJOR | severity-vocabulary test is `for tok in M: assert tok in M` |
| R2-MAJ5 | MAJOR | `assert self._bundle(...) is not None` on a function that returns a list — always true; test is a duplicate |
| R2-MAJ6 | MAJOR | numerical-literal ratchet (ceiling 99 / 0 on a 2-match fixture) pins only "count ≥ 1" |
| R2-MAJ7 | MAJOR | `gate_precheck` flag assertions union across 4 dispatches — per-call flag loss invisible |
| R2-MAJ8 | MAJOR | the only live-corpus leg of the verifies-alias guard is `@slow`, deselected by the documented default command |
| R2-I1 | IMPORTANT | conftest's env var means the memo is never exercised end-to-end (no assertion weakened, but nothing binds it either) |
| R2-I2 | IMPORTANT | `_memo` docstring mis-describes which guards need `unwrap`; `unwrap` is enforced by convention only |
| R2-I3 | IMPORTANT | dangling-closure ratchet fabricates its population from its own baseline; headroom undetectable |
| R2-I4 | IMPORTANT | public-surface guard silently lost half its population (4 of 8); assertion is one-directional |
| R2-I5 | IMPORTANT | `--strict` does not bypass the `paper_latex_compiles` cache; no test covers the interaction |
| R2-I6 | IMPORTANT | `TestGraphTestNodeCoverage` re-implements the extractor it tests; already went vacuous once |
| R2-I7 | IMPORTANT | `test_a_drifted_title_warns_by_default` reaches the NOT-FOUND branch, not the drift branch |
| R2-I8 | IMPORTANT | re-file of pass-1 **R3-C2**: 55 of 59 checks never production-seeded; `PRODUCTION_SEEDED` unverifiable by construction |
| R2-I9 | IMPORTANT | cannot-measure baseline's own stated measurement (22 pairs / 60 sites / 25 PASS) ≠ shipped state (21 / 54 / 21) |
| R2-I10 | IMPORTANT | memo tests restore content correctly but not mtimes — running the suite makes `counts_fresh` stale (measured) |
| R2-MIN1 | MINOR | transposed commit ids in the QI-31…34 production-probe provenance note |
| R2-MIN2 | MINOR | class-level `skipif(pdflatex is None)` deletes the whole ADR-009 item-3 regression suite on a TeX-less runner |
| R2-MIN3 | MINOR | three registry-contract legs are strictly implied by a fourth and can never fail independently |
| R2-MIN4 | MINOR | four assertions that measure prose length / message wording / a module default |
| R2-MIN5 | MINOR | six change-detectors on production constants rather than behaviour |
| R2-MIN6 | MINOR | `_StoredFakeClient` compares stored outputs to themselves when `produce is None` |
| R2-MIN7 | MINOR | "ONE owner" guard matches one exact spelling and uses a `[:6000]` window that overruns both targets |
| R2-MIN8 | MINOR | the one no-assert test in 775 (pre-existing on `main`) |

Plus one **NOT REPRODUCED** claim, §5.

---

## 1. CRITICAL

### R2-C1 — the `--ci` coverage floor cannot fire for the failure mode it names; a test pins the tautology that makes it dead code

**Files:** `scripts/validate.py:231-239, 671-677` · `scripts/validation/_config.py:92-119` ·
`tests/test_ci_mode.py:163-164`

**What it claims.** `_config.py:108-119`, verbatim: *"Dropping the Lean toolchain from a
runner … stops 7 checks that read `lean_deps.json` plus 3 that shell to `lake` from measuring
anything — while the run still reports green. … So `--ci` FAILS when fewer checks execute
than this. A missing toolchain becomes a red build reading '48 of 55 ran', not a green tick."*
This is the branch's answer to pass-1 finding **R5-C1**.

**What it actually does.** `n_ran = len(results)` where `results` comes from `run_checks`:

```python
# scripts/validate.py:231-239
    results = {}
    for spec in _CHECKS:
        if check_filter and spec.name != check_filter:
            continue
        try:
            results[spec.name] = spec.func()
        except Exception as e:
            results[spec.name] = CheckResult(passed=False, error=str(e))
    return results
```

Every spec produces an entry unconditionally — a check that cannot find `lake` still runs,
still returns a `CheckResult`, still occupies a slot. `len(results)` is therefore invariant at
`len(_CHECKS)` (59), minus the four `CI_SKIP` names under `--ci`, i.e. **55, in every
environment**. `CI_MIN_CHECKS_RUN = 55`. The `return 1` at `validate.py:677` is unreachable
except by a *registration* change, which `test_validate_registry_contract.py` already covers.

**How I verified.** Two legs.

1. Code reading above — `n_ran` is a count of *registered* checks, never of *measuring* ones.
2. Empirically, that a toolchain-less check still lands in `results` with `passed=True`
   (scratch probe, in-process, throwaway cache):

```
RUN1 (lake missing) passed= True | details: ['SKIPPED — lake not found. Set LAKE_PATH or install elan']
```

`axiom_closure_allowlist` — one of the "3 that shell to `lake`" the docstring names — returns
a **PASS**, so it is counted. Same shape at `papers_prose.py:497` (`pdflatex` missing → PASS)
and at eleven other sites (see R2-MAJ1).

**The test pins it.** `tests/test_ci_mode.py:157-168`,
`test_the_LIVE_floor_has_ZERO_headroom`:

```python
expected = len(validate._CHECKS) - len(_cfg.CI_SKIP)
assert _cfg.CI_MIN_CHECKS_RUN == expected
```

That is the *definition* of `n_ran`, asserted against the floor. A test that asserts
`floor == the quantity being compared to the floor` guarantees the comparison can never fire.
Its docstring reads *"the floor must equal what a correctly-provisioned runner actually
executes"* — the gap is that a **badly**-provisioned runner executes the same number, because
`run_checks` never drops a spec.

The "fires on the seeded defect" leg —
`test_a_shrunken_suite_FAILS_even_though_every_check_passed` (`:128-142`), whose docstring
says *"on a runner without `lake`, the suite gets ~200 s faster and 10 checks quieter, and
without this it exits 0"* — only fires because `tiny_registry` (`:64-78`) fabricates a
10-spec registry and the test lowers the floor to 9 by hand. That is fixture-only coverage of
a **registry shrink**, presented as coverage of a **toolchain loss**. The two are not the same
event, and only the first is detectable.

**Blast radius.** The mode advertised as the remedy for R5-C1 reports GREEN on precisely the
runner it was built to fail. `test_ci_mode.py`'s own opening line — *"A green tick over 48 of
59 is worse than no CI"* — describes the state this mode ships.

**Fix direction (not required for merge, but the honest one):** count checks that *measured*.
The cheapest form: have `run_checks` mark a result as non-measuring when its sole detail
message starts with `SKIPPED`, and floor on that count. That reuses the existing convention
rather than adding the `UNEVALUATED` state ADR-009 §Deferred 4 declined.

---

### R2-C2 — `test_validation_memo.py`'s "production-seeded" key tests do not test any memoized check's key. **Proved with a production-seeded mutation.**

**Files:** `tests/test_validation_memo.py:93-139` · `scripts/validation/checks/lean_toolchain.py:426-436, 652-655`

**What it claims.** `_memo.py:41-44`: *"**`tests/test_validation_memo.py` seeds a real change
into each declared input, in the production tree, and asserts the key moves.** Per QI-30: a
mutation caught against a patched fixture proves nothing about production."* And
`test_validation_memo.py:98-106`: a Lean edit that did not move the key would be *"the single
worst outcome this cache can produce."*

**What it actually does.** Every test in `TestKeyCoversItsInputs` calls a **fingerprint
helper** directly:

```python
_seeded(victim, b"...", _memo.lean_source_fingerprint)      # :100
_seeded(lakefile, b"...", _memo.toolchain_pin_fingerprint)  # :109
_seeded(constants, b"...", lambda: _memo.files_fingerprint([constants]))  # :128
```

None of them resolves the registered check, and none of them calls the check's `key_fn`. What
is asserted is that `sha256(x + delta) != sha256(x)` — true of any hash function. The binding
between *the input* and *the key of the check that must not skip across it* is nowhere
asserted.

**How I verified — seeded into PRODUCTION source, twice.**

Mutation A. Deleted `_memo.toolchain_pin_fingerprint(),` from `axiom_closure_allowlist`'s
`key_fn` (`scripts/validation/checks/lean_toolchain.py:430`). A Mathlib/toolchain bump now
leaves the 145 s axiom audit frozen at the old Mathlib's verdict.

```
$ uv run --no-sync python -m pytest tests/test_validation_memo.py -q
........................                                                 [100%]
24 passed in 0.27s
$ uv run --no-sync python -m pytest tests/test_validate_flag_propagation.py \
      tests/test_d5_lean_toolchain.py tests/test_d5_prose_lean_refs.py -q
77 passed in 25.38s
```

Mutation B — the one the test file calls the worst possible outcome. Replaced
`_memo.lean_source_fingerprint(),` with `"",` in the same `key_fn`, so **editing a `.lean`
file no longer moves `axiom_closure_allowlist`'s key at all**:

```
$ uv run --no-sync python -m pytest tests/test_validation_memo.py -q
........................                                                 [100%]
24 passed in 0.29s
```

Both mutations restored; `git diff scripts/validation/checks/lean_toolchain.py` is empty.

**Blast radius.** The memo is the branch's single most dangerous new mechanism — it makes a
check report PASS *without running* — and the guard offered as its justification is decoupled
from it. Any future edit, refactor or copy-paste of a `key_fn` that drops an input is
undetected by the suite. `TestMemoizedSetIsFrozen` freezes *which* checks are memoized but
says nothing about *what their keys cover*, so the frozen-set ratchet does not compensate.

**Fix (small).** Add, per memoized check, a test that resolves the *registered* spec, captures
`key_fn()` from the decorator (it is closed over in the wrapper; expose it as
`wrapper.__memo_key_fn__` alongside `__memo_body__`), seeds each declared input in production,
and asserts *that* key moves. Roughly four assertions per check; it is the test the module's
own docstring already claims to have.

---

### R2-C3 — a "cannot measure ⇒ PASS" verdict is **cached** by the memo and replayed indefinitely. Demonstrated. No test covers it.

**Files:** `scripts/validation/_memo.py:265-279` · `scripts/validation/checks/lean_toolchain.py:474, 484, 496, 505, 511` ·
`tests/test_cannot_measure_baseline.py:96-98` · `tests/test_validation_memo.py` (absent)

**What it claims.** `_memo.py:43-45`: *"**Only PASS is cached.** A failing check re-runs every
time, so a red check can never be memoized away."* `_memo.py:54-58`: *"Every error path here
computes rather than skips. … The cache can only ever make a run *slower* when it is broken,
never greener."*

**What it actually does.** `check_axiom_closure_allowlist` has **five** early
`return CheckResult(passed=True, …)` paths — `lake` not found, `AxiomAudit.lean` absent,
`subprocess` timeout (600 s), `AxiomAudit` exited non-zero, unparseable JSON. Two of those
are already frozen as legitimate "cannot measure ⇒ PASS" in
`tests/test_cannot_measure_baseline.py`'s baseline. The memo does not distinguish them from a
measured PASS: `if result.passed: entries[name] = {...}`. So a transient environment failure
writes a green key fingerprinted on the **real** tree, and every later run with a working
toolchain reads it back.

**How I verified.** In-process, throwaway cache file (never touched
`docs/validation/.check_memo.json`):

```
RUN1 (lake missing) passed= True | details: ['SKIPPED — lake not found. Set LAKE_PATH or install elan']
CACHE after run1: {"axiom_closure_allowlist": {"details": [["lake", true,
  "SKIPPED — lake not found. Set LAKE_PATH or install elan", false]],
  "key": "667d2fcea758a94b4a42079a"}}
RUN2 (lake present) passed= True | details: ['SKIPPED (cached) — Lean sources, toolchain pins,
  AXIOM_METADATA unchanged since the last PASS; --no-memo (or --strict) re-measures',
  'SKIPPED — lake not found. Set LAKE_PATH or install elan']
```

Run 2 completed instantly with a working `lake`. The 145 s audit never runs again until a
`.lean` file, a pin file, `constants.py` or `update_counts.py` changes. Realistic triggers:
`elan` not on `PATH` in a subshell; the 600 s timeout under three concurrent worktree `lake`
builds (this repo runs `wt1/wt2/wt3`); an `ENFILE` storm, which this repo's own CLAUDE.md
documents as a live hazard.

**Test coverage of this:** none. `test_a_failure_is_never_cached` and
`test_a_failure_evicts_an_earlier_pass` cover `passed=False`. The whole point of
`tests/test_cannot_measure_baseline.py` is that `passed=True` **is not the same as** a
measured pass — and the memo treats them identically. Two branch-new mechanisms compose into
exactly the defect class the branch exists to fight, and nothing in 5,482 tests sees the seam.

**Fix (one line, plus a test).** Do not cache a result whose details are all
`SKIPPED`-prefixed — or, better, thread the existing cannot-measure notion into
`CheckResult` as a private flag the memo refuses to store. `--strict` bypassing the memo does
**not** mitigate this: the poisoned key persists for every non-strict run in between, which is
every `/goal` loop and every `gate_precheck s13`.

---

## 2. MAJOR

### R2-MAJ1 — the cannot-measure baseline scanner is blind to 12 of the 36 silent-PASS sites, including the two that poison the memo

**File:** `tests/test_cannot_measure_baseline.py:126-163`

The scanner recognises exactly two syntactic kinds: a `return` inside an `except` handler, and
a `return` inside an `if` whose test *calls* one of six presence predicates
(`exists`/`is_file`/`is_dir`/`lean_deps_present`/`counts_present`/`which`). Anything else —
`if not lake_bin:`, `if result.returncode != 0:` — is invisible.

**Measured** (AST over `git show HEAD:scripts/validation/checks/*.py`, so the count is immune
to my own in-flight mutations):

```
early passed=True return sites (excl. final): 36
distinct (check,kind) pairs the scanner can see: 21
UNCLASSIFIED silent-PASS sites (invisible to the baseline scanner):
  axiom_closure_allowlist: lines [474, 505]
  bundle_consistency: [681]        bundle_figure_integrity: [99]
  bundle_source_freshness: [644]   inventory_index_autogen_fresh: [727]
  lean_build: [364, 379]           paper_latex_compiles: [497]
  paper_toolchain_pin_drift: [934, 942]   tracked_hypotheses_fresh: [589]
total unclassified: 12
```

`axiom_closure_allowlist:474` is *`lake` not found → PASS* and `:505` is *`AxiomAudit` exited
non-zero → PASS* — the two that produce the cached green in R2-C3, and neither is on the
record. `paper_latex_compiles:497` is *pdflatex missing → PASS*, the survivor of the
slow-gate removal.

**Second slack:** the ratchet is keyed on `(check, kind)` **pairs**, not sites. 24 classified
sites collapse to 21 pairs, so **3** additional silent-PASS returns already exist inside
baselined pairs, and adding a fourth `except: return PASS` to a check that already carries an
`exception` entry fails nothing.

**Third slack:** the seam guard is `assert len(sites) >= 30` (`:177`) against a live count of
**54**. 24 of 54 sites (44 %) can vanish from the scan and the guard still passes. This file
is where the repo states its own rule — *"a ceiling far above the population is headroom in
which the ratchet does nothing"* (`test_d5_mutation_obligation.py:693-696`) — and violates it.
The companion `assert any(v is False …)` (`:181`) is satisfied by 1 of 33 FAIL sites.

**Verified:** `len(CANNOT_MEASURE_PASS_BASELINE) == 21`, `len(scan_cannot_measure_sites()) == 54`,
`len(_pass_sites()) == 21`.

---

### R2-MAJ2 — `test_it_stays_advisory` asserts `True is True`

**Files:** `tests/test_d5_lean_toolchain.py:371-377` · `scripts/validation/checks/lean_toolchain.py:601, 621`

```python
assert lt.check_elaboration_knob_watchlist().passed is True, (
    "elaboration_knob_watchlist started failing — ADR-009 item 3 keeps it advisory …")
```

`check_elaboration_knob_watchlist` has exactly two `return` statements and both are literal
`CheckResult(passed=True, …)` (verified: `rg "def check_elaboration_knob_watchlist" -A60 |
rg "return CheckResult"` → lines 601 and 621, both `passed=True`). There is no reachable
`passed=False`. The fixture and the two monkeypatches cannot influence the outcome. The loud
failure message describes a state the function cannot enter without a source edit that would
also delete the `return` this test reads.

Same family, lower confidence: `tests/test_d5_graph_atlas.py:404-411`
(`test_it_never_gates_however_bad_the_distribution`) — that one is not a pure tautology,
because `check_atlas_hypothesis_discipline` does have a `passed=False` exception handler.

---

### R2-MAJ3 — `build_graph._infer_bundle_from_text` has **zero** real test coverage; the atlas round-trip leg is tested only against an identity stub

**Files:** `tests/test_d5_graph_atlas.py:59-60, 77-93, 130` · `scripts/validation/checks/graph_atlas.py:62` ·
`scripts/build_graph.py:1655-1657, 1678-1697`

Production predicate:

```python
unresolved = sorted(c for c in _roster if _infer_bundle_from_text(c) != c)
```

The fixture monkeypatches `_infer_bundle_from_text` to the **identity**, so the predicate
reduces to `c != c` — false for every roster code by construction. The failing leg
hand-writes the bug as `lambda t: t if len(t) <= 2 else None`.

**Measured:** the symbol appears in the whole `tests/` tree exactly three times, all in
`tests/test_d5_graph_atlas.py`, all as a monkeypatch target or a docstring:

```
$ rg -n "_infer_bundle_from_text|_BUNDLE_CODE_RE|_valid_bundle_codes" tests/
tests/test_d5_graph_atlas.py:14   (docstring)
tests/test_d5_graph_atlas.py:59   monkeypatch.setattr(build_graph, "_infer_bundle_from_text", ...)
tests/test_d5_graph_atlas.py:130  monkeypatch.setattr(build_graph, "_infer_bundle_from_text", lambda t: t)
```

**Proved, not argued.** I re-introduced the historical defect into production
(`scripts/build_graph.py:1656`, `D\d{1,2}` → `D[1-9]`) and ran the whole suite:

```
5482 passed, 5 skipped, 118 deselected, 7 warnings in 284.53s (0:04:44)
```

Byte-identical to the clean baseline (§0). Restored; `git diff scripts/build_graph.py` empty.
So the named defect — which `build_graph.py:1640-1654` records as having produced *"D12
rendered 'Blockers 0' while carrying 36 open ReviewFindings"* and **false FLAGS edges** —
is invisible to all 5,482 tests. The same `_run` also stubs `build_graph_json` and
`run_integrity_checks`, so `test_a_verification_conflict_is_a_hard_failure`,
`test_an_orphan_claim_is_a_hard_failure` and
`test_generic_orphans_and_broken_chains_stay_advisory` only threshold a fabricated `summary`
dict. This is the fixture-only class named in the brief, in the check that gates the graph.

---

### R2-MAJ4 — the severity-vocabulary test is `for tok in M: assert tok in M`

**Files:** `tests/test_d5_reviews.py:339-355` · `scripts/validation/checks/reviews.py:367-369, 394-395`

Test builds its fixture from `build_graph._SEVERITY_DECL_MAP`; the check rejects a token
`if v.strip().lower() not in vocabulary` where `vocabulary = set(_SEVERITY_DECL_MAP)` — the
same object, same import. No edit to the vocabulary (adding, removing, misspelling, or
emptying it — an empty map yields an empty document, zero findings and a trivial pass) can
make this fail. The docstring's stated purpose (*"otherwise this check and the extractor
disagree"*) is unachievable by construction.

---

### R2-MAJ5 — `test_the_floor_sits_between_those_two_values`: `assert <list> is not None`, and the test is a verbatim duplicate

**File:** `tests/test_d5_bundles_readiness.py:445-459`

```python
assert self._bundle(tmp_path, monkeypatch, pt=3.0) is not None
```

`_bundle` ends `return calls` where `calls = []` (`:379`) — a list, **always** non-`None`.
Its two siblings do this correctly with `assert calls, "…the check short-circuited before the
legibility branch, so this test is not testing the floor"` (`:428`, `:440`). Those guards
exist *because* the class previously passed for a reason unrelated to its name (pass-1
**R2-C1**, fixed). This test re-weakened the same guard, and with it stripped, the test is a
verbatim re-run of `test_an_illegible_figure_fails` + `test_a_legible_figure_passes`.

---

### R2-MAJ6 — the numerical-literal ratchet pair pins only "count ≥ 1"

**File:** `tests/test_always_pass_dispositions.py:81-99`

Measured fixture: `find_inline_numerical_literals(DIRTY)` → **2** matches
(`'5.78 nK'`, `'1.334 \mu m'`). Production predicate is `over = total_findings > CEILING`.
The pair uses ceiling **99** for the pass leg (`2 > 99` false for any count 0–99, including
0 — i.e. the regex matching nothing) and ceiling **0** for the fail leg (true for any count
≥ 1). A regression from 2 matches to 1 — the `\mu m` alternative dropping out of the regex —
is invisible to both legs, and there is no `test_a_clean_corpus_passes` for this check.

The sibling `TestCountLiteralRatchet` (`:47-78`) does it right: ceilings 3 and 2 against a
3-match fixture, pinning the count exactly, plus a clean-corpus leg.

---

### R2-MAJ7 — `gate_precheck`'s flag assertions union across dispatches, so per-call flag loss is invisible

**Files:** `tests/test_gate_precheck.py:55-56, 98-110, 137-144` · `scripts/gate_precheck.py:31-32, 69-95`

```python
def flags(self) -> set[str]:
    return {a for c in self.calls for a in c if a.startswith("--")}
```

Stage `s10` dispatches **four** separate `validate.py --check <name> --no-archive` calls.
`test_prechecks_never_archive` asserts `"--no-archive" in r.flags()` — the union — so dropping
the flag from three of the four passes, and three prechecks then archive a timestamped report
and dirty the tree before every reviewer dispatch. The correct form is
`all("--no-archive" in c for c in r.calls)`.

`test_the_submission_gate_is_a_superset_of_s13` (`:137-144`) is worse than its docstring:
it promises *"Submission must not be able to pass on less than a wave close does"* and asserts
`s13.flags() - {"--no-archive"} <= subs.flags()` — a subset test between two flag sets
(`{"--force-latex"} ⊆ {"--strict","--force-latex","--no-archive"}`). It says nothing about
*which checks* each stage runs. Replacing `submission`'s `__strict__` with a two-check list
leaves it green. The `- {"--no-archive"}` is inert (both sides carry it).

---

### R2-MAJ8 — the only live-corpus leg of the verifies-alias guard is deselected by the documented default command

**File:** `tests/test_verifies_alias_guard.py:259-260`

```
$ uv run --no-sync python -m pytest tests/test_verifies_alias_guard.py -q --collect-only
15/16 tests collected (1 deselected)
$ ... -m '' --collect-only
16 tests collected
```

The single deselected test is
`TestLiveGraphHasNoFabricatedEdges::test_no_lean_edge_is_alias_rooted_or_tail_resolved`. Every
other test in the file drives `extract_verifies_edges` against stubbed `_LEAN_SHORT_INDEX` /
`_TEST_MODULE_ALIASES`. CLAUDE.md's documented default is `pytest tests/ -v` (*"fast tests …
deselects `slow`"*), and `gate_precheck` does not run pytest at all. So on every routine run,
the file cannot detect that the 144 fabricated edges it was written for are back.

---

## 3. IMPORTANT

### R2-I1 — the memo is never exercised end-to-end; `tests/conftest.py` disables it in subprocesses too

`tests/conftest.py` sets `SKEFT_VALIDATION_NO_MEMO=1` at import, and `_memo.memoized`
honours the env var, so **`tests/test_ci_mode.py` and the mutation harness, which shell out to
`validate.py`, also run memo-free**. That is the right call for correctness (it is exactly the
QI-30 hazard, and the file says so). The consequence is that *no test in the suite ever
observes the memo wired into a real `validate.py` run*. Combined with R2-C2 (the key tests are
decoupled from the checks) the memo's only binding coverage is
`TestMemoizedSetIsFrozen.test_exactly_the_frozen_set_is_memoized`, which asserts two names.

Answering the brief's question directly: **the conftest env var does not silently weaken any
existing assertion** — I found no test that depends on memo behaviour and would degrade. It
narrows *what can be tested*, not what is asserted.

### R2-I2 — `_memo`'s docstring mis-describes which guards need `unwrap`, and `unwrap` is enforced by convention only

`_memo.py:293-297` claims *"the flag-propagation test reads `co_names` for `_cfg`, **the
cannot-measure baseline scans the source for early-return sites** … They unwrap through this
attribute."* `tests/test_cannot_measure_baseline.py` does **not** resolve a check function at
all — it parses the check *files* with `ast` (`:135`) — so it neither needs nor uses `unwrap`.

**Full census of sites that resolve a check from the registry and then introspect it:**

| site | introspects | unwraps? |
|---|---|---|
| `tests/test_validate_flag_propagation.py:73` | `__code__.co_names` (:187,188,213,241) | **yes** |
| `tests/test_validation_memo.py:302` | `__code__.co_names` (:304) | **yes** |
| `tests/test_validation_memo.py:287` | `hasattr(s.func, "__memo_body__")` | n/a (that is the probe) |
| `tests/test_d5_mutation_obligation.py:755` | `spec.func.__name__` | **no** — safe only because `_memo.py:303` copies `__name__` |

So the discipline holds today. What is missing is a guard: nothing fails if a *new*
introspecting test forgets `unwrap`. A one-line test — "every registry introspection in
`tests/` goes through `_memo.unwrap`" — is not currently possible to write generically, but a
cheaper equivalent is to make `memoize_check` return a `functools.wraps`-style object whose
`__code__` raises, so a forgotten unwrap fails loudly instead of vacuously.

### R2-I3 — the dangling-closure ratchet fabricates its population from its own baseline

`tests/test_d5_graph_atlas.py:138-157` builds a ledger of exactly `67` ghosts against
`graph_atlas.py:182`'s function-local `_LEDGER_DANGLING_BASELINE = 66`, and a second of `66`.
Both legs restate the constant ±1, so a legitimate re-measurement of the population breaks
them with no defect present, and — more to the point — the defect the docstring names
(*headroom*: baseline 67 against a population of 66) is undetectable, because the population is
derived from the baseline. The invariant that would bite (`baseline == live dangling count`,
zero slack) is asserted nowhere. Contrast `test_d5_mutation_obligation.py`'s
`test_the_ceiling_has_ZERO_headroom`, which does it correctly.

### R2-I4 — `test_validate_public_surface`'s public-surface guard has silently lost half its population

`tests/test_validate_public_surface.py:380-396`. The filter is
`getattr(getattr(v, n), "__module__", "") == "validate"`; `expected` names eight symbols.
**Measured live:**

```
live public set: ['archive_results', 'main', 'print_results', 'run_checks']   size: 4   expected-set size: 8
```

`Detail`, `CheckResult`, `CheckSpec`, `register_check` now live in `validation._registry` and
are re-exported, so the filter no longer sees them. The assertion is one-directional
(`public - expected`), so the shrinkage is silent and the guard's coverage decays toward
`{main}` as the ADR-009 split completes. Same class as the `EXPECTED_SURFACE` measurement
failure the file's own docstring documents at `:38-53`.

### R2-I5 — `--strict` does not bypass the `paper_latex_compiles` per-draft cache

`scripts/validation/checks/papers_prose.py:507, 561` gate the cache on `_cfg.FORCE_LATEX`
only. The memo's documented rule — *"`--strict` is the Paper Submission Gate … the one place
where paying 200 s to re-measure from scratch is obviously worth more than the cache"*
(`_memo.py:219-227`) — is not applied to the second cache landed in the same commit. It is
mitigated *at the gate* because `gate_precheck submission` passes `--force-latex` alongside
`--strict` (`gate_precheck.py:87-88`), but a bare `validate.py --strict` reads cached
compile verdicts. No test covers the `--strict` × latex-cache interaction; the analogous memo
test (`test_strict_mode_bypasses`) exists and passes, which makes the asymmetry easy to miss.

### R2-I6 — `TestGraphTestNodeCoverage` re-implements the extractor it tests (self-agreement), and its own comment records it going vacuous once already

`tests/test_validate_public_surface.py:426-440`. The test walks `tests/**/test_*.py` with
`ast`, counts `FunctionDef`s whose name starts with `test_`, and asserts equality with
`extract_python_test_nodes()`. Any scope predicate shared by both sides is invisible — today
that includes `AsyncFunctionDef` exclusion and the silent `except SyntaxError: continue`. The
comment at `:426-430` documents the previous instance (*"Both sides used the SAME
non-recursive glob, so the equality held VACUOUSLY"*); the fix aligned the globs but left the
structure. `tests/test_ci_mode.py:72` names this class by name as an anti-pattern it is
deliberately avoiding — and it is still here.

### R2-I7 — `test_a_drifted_title_warns_by_default` does not reach the drift branch

`tests/test_d5_citations.py:282-302`. The docstring claims *"the exact BLOCKER pattern: the
registry says 'in A relativistic', the paper says 'in relativistic'"*, but the fixture's
`page1` is a *wholly different* title, so the check takes the NOT-FOUND branch. The file
admits this at `:344-348`. Its inputs are byte-identical to
`test_a_NOT_FOUND_flag_stays_advisory_even_under_strict` (`:303-306`) except for `strict`, and
the surviving assertion `any(d.warning for d in r.details)` is satisfied by any warning from
any detail. `bibitem_title_primary_source` is one of the four `PRODUCTION_SEEDED` names, so
the production probe carries the weight — but this test does not.

### R2-I8 — the `FIXTURE_ONLY_CEILING` ratchet is arithmetically honest but structurally unverifiable, and 55 of 59 checks remain fixture-only

Re-filing pass-1 **R3-C2** (status `🔧 PARTIAL`) — it survived. Measured:
`len(validate._CHECKS) == 59`, `len(PRODUCTION_SEEDED) == 4`, `FIXTURE_ONLY_CEILING == 55`.
Zero headroom in both directions (`test_the_ceiling_has_ZERO_headroom` forces the ceiling to
equal the population), so the ratchet does bite. Two honest caveats the branch states itself
and I confirm:

* `TestProductionSeedingRatchet`'s own docstring: *"This class does NOT verify that any
  seeding happened — nothing in a repository can."* `PRODUCTION_SEEDED` is a hand-maintained
  list, i.e. the "hand-maintained list parallel to a registry" shape from the brief §4, held in
  check only by `test_production_seeded_names_are_registered_checks`.
* **93 % of checks (55/59) have never been shown to fail against a real artifact.** That is
  the honest state, not a regression — but the four that were swept are the four pass-1 named,
  and my R2-C1/C2/C3/MAJ3 are four *more* checks/guards that provably cannot fire, found in one
  session. The base rate suggests the remaining 55 hide more.

### R2-I9 — the cannot-measure baseline's stated measurement does not match the shipped state

`tests/test_cannot_measure_baseline.py:19-21`: *"MEASURED 2026-08-04 across the 59 checks —
60 cannot-measure return sites: **35 FAIL (58%) and 25 PASS**, the latter collapsing to the
**22** (check, kind) pairs frozen below."* Measured now: **54 sites, 21 PASS, 21 frozen
pairs**. One entry (`tracked_hypotheses_fresh`) was removed on 2026-08-05 per the file's own
⚠ note and the prose counts were not updated. This is the brief §4 last bullet — *a document
describing a repaired guard* — inside the guard itself.

### R2-I10 — the production-seeded memo tests DO restore content, but their mtime side effect makes `counts_fresh` stale on every suite run

This answers the brief's explicit question about `tests/test_validation_memo.py`.

**Restoration: yes, correctly.** `_seeded` (`:79-90`) reads the original bytes *before* any
write, restores inside `finally`, and then re-asserts `path.read_bytes() == original`. A
failing assertion in the caller cannot leave the tree mutated. The residual hazard is only a
hard kill (SIGKILL / timeout / power) mid-window, and the suite is single-process
(no `pytest-xdist`, no `pytest-randomly` installed — verified), so there is no concurrent
reader inside the process.

**The side effect is real and I measured it.** The four production files the tests rewrite
carry the suite's timestamp afterwards:

```
2026-08-05 11:31:45.869078  lean/SKEFTHawking/A1Ext.lean
2026-08-05 11:31:45.869893  lean/lakefile.toml
2026-08-05 11:31:45.870381  lean/lake-manifest.json
2026-08-05 11:31:45.871460  src/core/constants.py
2026-08-05 11:30:29.469089  docs/counts.json        <- 76 s OLDER
```

11:31:45 is the moment my `pytest tests/` run reached `tests/test_validation_memo.py`.
`freshness.py:95-116` computes staleness from **mtime**:
`src.stat().st_mtime > counts_mtime` over `_COUNTS_SOURCES` (which includes
`src/core/constants.py`) and `newest_lean > counts_mtime` over `lean/**/*.lean`. So **running
the test suite makes `counts_fresh` stale**, and `check_counts_fresh` responds by shelling out
to `update_counts.py` — the regenerator `_config.CI_SKIP` describes as *"1800 s, needs lake"*.

Content is restored; mtime is not. The fix is one line in `_seeded`: capture
`os.stat(path)` up front and `os.utime(path, ns=(st.st_atime_ns, st.st_mtime_ns))` after the
restore. Without it, every developer who runs the suite pays a counts regeneration on their
next `validate.py`, which is precisely the kind of cost that teaches people to skip gates.

---

## 4. MINOR

* **R2-MIN1** — `tests/test_d5_mutation_obligation.py:712-713` transposes two commit ids: it
  lists `865db716 / 637d1184` in the order `bibitem_title_primary_source /
  recurrence_reopens_closures`, but `git log` shows `865db716 = "QI-34 — the recurrence guard
  read the truncated field"` and `637d1184 = "QI-33 — --strict now has a caller"`. The
  provenance note is the only durable record of those probes, so the mapping matters.
* **R2-MIN2** — `tests/test_always_pass_dispositions.py:103` puts
  `@pytest.mark.skipif(shutil.which("pdflatex") is None)` on the whole `TestLatexCompileVerdict`
  class. `pdflatex` is present here (`/Library/TeX/texbin/pdflatex`), so the class ran — but on
  a TeX-less runner the entire ADR-009 item-3 regression suite vanishes with a green tick, which
  is the "smaller suite reports greener" inversion `--ci` was meant to stop (and, per R2-C1,
  does not).
* **R2-MIN3** — `tests/test_validate_registry_contract.py`: `test_check_count_is_frozen`
  (`:82-91`) and `test_names_are_unique` (`:118-123`) are both strictly implied by
  `test_registration_order_is_frozen`'s `actual == EXPECTED_CHECKS` (`:95`) and can never fail
  independently; `test_every_check_has_a_description` (`:114-116`) can only fail on an empty
  string, since `description` is a required positional.
* **R2-MIN4** — `tests/test_ci_mode.py:112-114` (`assert isinstance(why, str) and len(why) > 30`)
  measures prose length, not justification; `tests/test_native_decide_ratchet.py:109`
  (`assert any("lowering the ceiling" in (d.message or "") …)`) is a change-detector on a hint
  string; `tests/test_ci_mode.py:183` (`assert _cfg.STRICT_MODE is False`) asserts the module
  default, so it holds even if `main()` never touched the flag.
* **R2-MIN5** — `tests/test_d5_lean_toolchain.py:236-238` (`_resolve_lean_root()` vs
  `_H.PROJECT_ROOT / "lean"`) and `tests/test_d5_freshness.py:583-590` (`CLAIM_CLUSTERS_PATH.name
  == "claim_clusters.json"`, `all(p.is_absolute() …)`) restate one-line production expressions
  through the same module state — change-detectors on constants, not tests of behaviour. Same
  shape at `tests/test_d5_bundles_readiness.py:355, 359` (assert a tuple/frozenset literal's
  contents without calling any check) and `:322, :341` (fixture sized from
  `_ROSTER_LITERAL_THRESHOLD`, so raising the threshold to 500 keeps both green).
* **R2-MIN6** — `tests/test_d5_freshness.py:321-336`'s `_StoredFakeClient.execute` returns
  early when `produce is None`, leaving stored outputs untouched so the check compares them to
  themselves. No current test trips it (`setup_method` + `_run` always set `produce`), but it is
  one default argument away from a green "stored output matches a fresh run" that examined
  nothing. Raise instead of no-op.
* **R2-MIN7** — `tests/test_d5_lean_substrate.py:212-227`'s "ONE owner" guard uses a regex
  matching one exact spelling (`{d.get("name", "") for d in`) and a magic `body[:6000]` window
  that overruns both target functions (~5,839 and ~5,711 chars) into the next declaration. A
  re-implementation written any other way passes.
* **R2-MIN8** — `tests/test_build_graph.py:557` `test_write_survives_pg_unavailable` has no
  assertion (the only such test in the 775 in changed files). **Pre-existing on `main`** — not a
  branch finding, listed for completeness.

---

## 5. NOT REPRODUCED — claims I checked and could not confirm

* *"`scripts/validate.py` still holds 5 `@register_check` decorators outside the cannot-measure
  scanner's scope."* `rg -n "@register_check" scripts/validate.py` returns 5 hits at lines 34,
  36, 148, 205, 504 — **all inside comments and docstrings**. There are zero live
  `@register_check` decorators in `validate.py`; every one of the 59 lives under
  `scripts/validation/checks/`, which is the scanner's scope. The scanner's scope gap is real
  but is the *non-recursive* `glob("*.py")` and the two syntactic kinds (R2-MAJ1), not
  `validate.py`.

---

## 6. Whole-of-suite mutation measurement — the result that argues FOR this suite

To answer "do the tests test anything" at the population level rather than by sampling, I
neutered **each of the 59 registered checks in turn** — inserting
`return CheckResult(passed=True, details=[])` as the first statement of the *production* check
body, in `scripts/validation/checks/*.py` — and ran every `tests/test_*.py` that mentions that
check by name. A check whose neutering leaves those files green has no test that can
distinguish it from a no-op. Each iteration restored the file from a byte copy; `git status`
after the sweep shows no modification to any tracked source.

```
total checks probed: 59
UNDETECTED (neutering left the suite green): 0
```

**All 59 are covered.** That is a real, and unusual, result: it means every registered check
has at least one test that can tell it apart from a no-op. On the crude axis, this suite is
not theatre. Reviewers reading only my CRITICALs should weigh this against them.

**What it does NOT establish**, and this is the whole gap my findings live in: a whole-body
mutation is coarse. It proves a test can distinguish *check* from *nothing*. It does not prove
a test can distinguish *correct* from *subtly wrong*. The decisive counter-demonstration:

> I restored the actual historical defect — `_BUNDLE_CODE_RE`'s `D\d{1,2}` reverted to
> `D[1-9]` at `scripts/build_graph.py:1656`, the regex whose failure on two-digit codes
> `build_graph.py:1640-1654` records as having rendered *"D12 … 'Blockers 0' while carrying 36
> open ReviewFindings"* and minted **false FLAGS edges** — and ran the whole suite:
>
> ```
> 5482 passed, 5 skipped, 118 deselected, 7 warnings in 284.53s
> ```
>
> Byte-identical to the clean baseline. Restored; `git diff scripts/build_graph.py` empty.

So: 59/59 checks are protected against being *deleted*, and the one real-world regression I
reproduced verbatim is invisible. Both facts are true and both belong in the record.

**The thinnest margins** — five checks where exactly ONE test fails under total neutering, so
one deleted or weakened test drops them to zero coverage:
`count_literals`, `disclosure_consistency`, `numerical_literals`, `paper_toolchain_pin_drift`,
`tracked_hypothesis_ledger`. Note `numerical_literals` is also R2-MAJ6.

### 6.1 Full table

| check | test files run | tests FAILED under neutering | tests passed |
|---|---:|---:|---:|
| `count_literals` | 5 | **1** | 55 |
| `disclosure_consistency` | 6 | **1** | 160 |
| `numerical_literals` | 5 | **1** | 55 |
| `paper_toolchain_pin_drift` | 6 | **1** | 125 |
| `tracked_hypothesis_ledger` | 5 | **1** | 66 |
| `lean_source` | 7 | **2** | 185 |
| `tracked_hypotheses_fresh` | 4 | **2** | 57 |
| `accepted_findings_carry_rationale` | 5 | **3** | 109 |
| `atlas_hypothesis_discipline` | 3 | **3** | 44 |
| `bundle_registry_consistency` | 4 | **3** | 65 |
| `cgl_fdr` | 4 | **3** | 74 |
| `claim_clusters_fresh` | 3 | **3** | 55 |
| `cross_path_consistency` | 3 | **3** | 48 |
| `d1_hierarchy_table` | 8 | **3** | 166 |
| `elaboration_knob_watchlist` | 4 | **3** | 56 |
| `formulas` | 77 | **3** | 2786 |
| `identities` | 16 | **3** | 986 |
| `notebook_exec` | 5 | **3** | 63 |
| `notebook_stored_outputs_current` | 4 | **3** | 58 |
| `notebooks` | 6 | **3** | 123 |
| `paper_provenance` | 4 | **3** | 57 |
| `physical_bounds` | 4 | **3** | 102 |
| `placeholder_not_cited` | 5 | **3** | 95 |
| `provenance_doi_in_registry` | 5 | **3** | 116 |
| `review_docs_mint_findings` | 3 | **3** | 43 |
| `review_severity_declared` | 5 | **3** | 46 |
| `theorem_name_embedded_citations` | 6 | **3** | 168 |
| `bundle_source_freshness` | 6 | **4** | 97 |
| `f_hierarchy_claims` | 5 | **4** | 118 |
| `inventory_index_autogen_fresh` | 6 | **4** | 135 |
| `lean_docstring_refs_resolve` | 6 | **4** | 89 |
| `numerical` | 50 | **4** | 2239 |
| `quantum_network` | 4 | **4** | 86 |
| `vacuous_statement_audit` | 7 | **4** | 152 |
| `bibitem_title_primary_source` | 5 | **5** | 68 |
| `bundle_metadata_matches_graph` | 3 | **5** | 44 |
| `citation_primary_sources_present` | 6 | **5** | 119 |
| `counts_fresh` | 6 | **5** | 86 |
| `lean_build` | 5 | **5** | 104 |
| `native_decide_regression` | 5 | **5** | 74 |
| `proxy_body_audit` | 7 | **5** | 180 |
| `readiness_submission_gate` | 7 | **5** | 91 |
| `tables_fresh` | 5 | **5** | 100 |
| `theorems` | 51 | **5** | 2059 |
| `viz_consistency` | 3 | **5** | 34 |
| `axiom_closure_allowlist` | 7 | **6** | 111 |
| `bundle_consistency` | 5 | **6** | 112 |
| `bundle_figure_integrity` | 5 | **6** | 66 |
| `nogo_substrate_integrity` | 5 | **6** | 48 |
| `paper_latex_compiles` | 8 | **6** | 120 |
| `readiness_verdicts_agree` | 4 | **6** | 54 |
| `paper_table` | 6 | **7** | 129 |
| `recurrence_reopens_closures` | 7 | **7** | 176 |
| `axiom_count_prose_consistency` | 5 | **8** | 148 |
| `formula_grounding` | 9 | **8** | 251 |
| `atlas_integrity` | 5 | **9** | 140 |
| `parameter_provenance` | 5 | **9** | 70 |
| `graph_integrity` | 6 | **10** | 82 |
| `prose_theorem_reference_coverage` | 6 | **10** | 174 |

Harness: `scratchpad/mutate.sh` + `scratchpad/checkmap.json` (AST map of every
`@register_check`'d function's first body statement). Not committed — it mutates production
source and is a review instrument, not a fixture.

---

## 7. Verdict

**YES WITH FIXES.**

**Merge blockers — this branch ships guards that cannot fire:**

* **R2-C1** — `--ci`'s coverage floor is dead code against the failure mode it was built for,
  and `tests/test_ci_mode.py:163` pins the tautology that keeps it dead. The mode is the
  branch's answer to pass-1 R5-C1; as shipped it manufactures exactly the green tick the
  docstring calls *"worse than no CI"*. Either fix the floor to count *measuring* checks or
  strike the claim from `_config.py` and `test_ci_mode.py`'s docstrings.
* **R2-C3** — the memo caches and replays a `SKIPPED — lake not found` PASS. Demonstrated.
  This is a one-line fix (refuse to cache an all-`SKIPPED` result) plus one test, and it must
  land before the memo is relied on, because the poisoned key survives every non-`--strict`
  run.

**Fix-before-merge, cheap:**

* **R2-C2** — add per-check key tests that resolve the registered spec. Without them the
  memo's stated justification is not present in the repository, and I proved two independent
  key-deletions that the whole suite tolerates.

**Everything else routes to follow-up, not to the merge gate.** R2-MAJ1…MAJ8 and the
IMPORTANTs are tests that are weaker than they claim, in a suite that is otherwise a genuine
improvement on `main`: 5,482 green tests, **0 of 59 checks undetected under a whole-population
production mutation sweep**, one no-assert test in 775 new ones, zero
`pytest.skip`-on-missing-artifact sites in the ten `test_d5_*` files, and a candid record of
its own repaired vacuities. None of them makes anything *worse* than `main`, which had no
guard at all in these positions.

**One process note for the register.** Three of the four claims I inherited from a breadth
scan and re-measured survived; one did not (§5). The standing rule — *a filed finding's count
and consumer are claims* — earned its keep again.

**Submission blockers (→ ADR-010, explicitly not merge blockers):** R2-I8's residue — 55 of
59 checks have never been seeded in a production artifact, and R2-MAJ3 shows what that costs
(`_infer_bundle_from_text`, whose regression corrupted D12's blocker count and minted false
FLAGS edges, has zero real coverage anywhere in 5,482 tests).
