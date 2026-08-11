# R3 — ratchets, ceilings, baselines and thresholds

**Branch:** `infra/adr-009-validation-modularization` @ `db430c65`
**Worktree:** `.claude/worktrees/rv3` (detached at `db430c65`)
**Dimension:** every ratchet, ceiling, baseline and threshold on this branch, plus the
hand-maintained registries in `src/core/constants.py`.
**Verdict:** **YES-WITH-FIXES** — 1 CRITICAL, 2 MAJOR, 3 IMPORTANT, 5 MINOR.

---

## Method

Environment: the worktree has no `.venv` and no `lean/.lake/build`. All measurements were run
as `PYTHONPATH=. <main-checkout>/.venv/bin/python …` with **cwd = the worktree**, verified to
resolve `src.core.constants` from the worktree (`constants.__file__` printed and checked). All
check invocations go through `validate._CHECKS` — i.e. the production check bodies, not
re-implementations, per Rule 6.

Every "can it fire?" answer below is a **QI-30 production probe**: the defect was written into
the real artifact the check reads (a real `paper_draft.tex`, real `src/core/constants.py`, real
`lean/SKEFTHawking/*.lean`, real `lean/lean_deps.json`), the check was run, the red verdict was
observed, the artifact was restored with `git checkout --`, and `__pycache__` was cleared
between every `.py` mutation. `git status --porcelain` is clean at the end of this report.

⚠️ **Two things I could NOT measure and say so plainly:**
1. The **live measured-check count on a fully provisioned tree**. This worktree lacks a Lean
   build, so `axiom_closure_allowlist` cannot measure; a `--ci` run here reports `54 of 56`.
   Whether a provisioned runner reaches exactly 56 is **unverified**.
2. `bibitem_title_primary_source` was measured live (7 DROP-WORD, strict) but **not re-seeded**
   — the branch records its own production probe (QI-33, commit `865db716`) and a re-run costs
   ~25 min of pdfminer.

---

## The table

| constant | site | live measured value (predicate) | headroom | its test asserts against | can it fire? (verified how) |
|---|---|---|---|---|---|
| `NATIVE_DECIDE_DECL_CLOSURE_CEILING` = 546 | `constants.py:2473` | **546** — decls in `lean_deps.json` whose `axiom_deps_core ∪ axiom_deps_project` contains a native_decide axiom (`update_counts.native_decide_decls`) | **0** | live check output (`test_ratchets_have_zero_headroom`) | **YES** — added `"Lean.ofReduceBool"` to one decl in the real `lean/lean_deps.json` → `547 EXCEEDS ceiling 546`, `passed=False`; restored → PASS |
| `COUNT_LITERAL_CEILING` = 107 | `constants.py:2501` | **107** — count-literal regex matches across 64 real drafts | **0** | live check output | **YES** — appended `The library contains 999 theorems.` to `papers/D10/paper_draft.tex` → `108 … EXCEEDS by 1`, `passed=False` |
| `NUMERICAL_LITERAL_CEILING` = 116 | `constants.py:2502` | **116** — `find_inline_numerical_literals` hits outside `\input{tables/}`/captions | **0** | live check output | **YES** — appended `$3.77 \times 10^{-9}$ s$^{-1}$` to `papers/D10/paper_draft.tex` → `117 … EXCEEDS by 1`, `passed=False` |
| `ARISTOTLE_REGISTRY_UNRESOLVED_CEILING` = 14 | `constants.py:1389` | **14** — `validate_helpers.unresolved_aristotle_keys()` | **0** | live check output (`theorems`) | **YES** — renamed `'acousticMetric_det'` → `'r3_ghost_registry_probe'` in the real `src/core/constants.py` (count-preserving, so the import assert still passes) → `15 … above the frozen ceiling of 14`, `passed=False` |
| `MAXHEARTBEATS_PROOF_BODY_CEILING` = 22 | `lean_toolchain.py:590` | **22** — `set_option maxHeartbeats` lines attaching to a `theorem`/`lemma`/`example` within 12 lines | **0** | live check output (`test_d5_lean_toolchain` + meta-test) | **YES** — inserted `set_option maxHeartbeats 400000 in` above `AcousticMetric.lean:91` → `23 … EXCEEDS by 1`, `passed=False` |
| `BUNDLE_HANDWRITTEN_TABLE_CEILING` = 4 | `papers_prose.py:459` | **4** — hand-written `\begin{tabular}` across the 21 bundle drafts | **0** | live check output | **YES** — appended a `tabular` to `papers/D10/paper_draft.tex` → `5 … EXCEEDS by 1`, `passed=False` |
| `LEGACY_DRAFT_UNRESOLVED_REF_CEILING` = 79 | `constants.py:1422` | **79** — ABSENT-verdict tokens across the 43 legacy drafts, same extractor+resolver as the bundle leg (43 drafts / 814 candidates) | **0** | live check output (`test_d5_prose_lean_refs::test_the_live_legacy_ceiling_has_ZERO_headroom`) | **YES** — added `\texttt{r3\_ghost\_theorem\_probe}` to `papers/paper12_polariton/paper_draft.tex` → `80 … exceeds the frozen ceiling of 79`, `passed=False`. **The 81→79 move in `c7148779` left it at exact zero headroom.** |
| `BIBITEM_TITLE_DRIFT_CEILING` = 7 | `constants.py:1447` | **7** DROP-WORD (`--strict`; alongside 58 NOT-FOUND advisory, 303 PDF caches checked) | **0** | live registry (`test_d5_citations::test_the_live_drift_ceiling_has_ZERO_headroom`) | **Only under `--strict`** (`summary_passed = not STRICT_MODE or not over_ceiling`); live count re-measured = 7. Production probe **not re-run** — branch records QI-33 |
| `VACUOUS_STATEMENT_BASELINE` (48 names) | `constants.py:2524` | **48** — 30 matched by the type-thin leg + 23 by the body-thin leg, 5 in both, **0 stale** | **0 stale**, but see IMPORTANT-1 | `len(...) >= 40` (`test_substrate_integrity_gates.py:367`) — **a floor 8 below the live 48**, and there is **no staleness test** | **YES** on new debt — cloned a baselined thin decl under a new name into the real `lean/lean_deps.json` → `NEW content-thin statement 'r3_probe_vacuous_new' [reflexive (X=X)]`, `passed=False` |
| `CI_MIN_CHECKS_RUN` = 56 | `_config.py:124` | **54** measured on this (unprovisioned) worktree; 56 = `len(_CHECKS) − len(CI_SKIP)` = 60 − 4 | **unverified on a provisioned tree** | **the definition itself** — `test_ci_mode.py:157` asserts `CI_MIN_CHECKS_RUN == len(_CHECKS) − len(CI_SKIP)` | **The guard fires** (observed `✗ CI COVERAGE FLOOR: 54 of 56 … rc=1`). **The test cannot** — see MAJOR-1 |
| `AWAITING_CEILING` = 0 | `test_d5_mutation_obligation.py:536` | **0** — `len(AWAITING_MUTATION_TEST)` | 0 | `AWAITING_CEILING == len(AWAITING_MUTATION_TEST)` — two constants in the same file | Fires only when someone edits that file; the binding leg is `test_every_check_is_accounted_for` against the live registry. Acceptable, disclosed in the module docstring |
| `FIXTURE_ONLY_CEILING` = 55 | `test_d5_mutation_obligation.py:591` | **55** = 60 registered − 5 `PRODUCTION_SEEDED` | 0 | definitional (two hand-maintained collections) | Fires on a new check. Cannot detect a *false* `PRODUCTION_SEEDED` claim — explicitly disclosed in the class docstring |
| `CANNOT_MEASURE_PASS_BASELINE` (21) + seam floor `>= 54` | `test_cannot_measure_baseline.py:89,~155` | **21** pass-sites / **54** scanned sites | **0 both directions** | live AST scan of the production check modules; `test_no_new_silent_pass` **and** `test_baseline_has_no_stale_entries` | **Healthy.** The best-shaped ratchet on the branch — measured, both-directions, zero stale |
| `_RECURRENCE_MIN_TITLE` / `_RECURRENCE_MIN_OVERLAP` | `checks/reviews.py` (re-exported `validate.py:546`) | not re-measured this pass | — | — | Out of budget; flagged by pass 2 as historically mis-set three times. **Unverified here.** |

**Bottom line on question 1 (zero headroom):** *no* ratchet on this branch has positive headroom.
Every numeric ceiling equals its live population under the check's own predicate. The "ratchet at
zero headroom" idiom is, on the numbers, correctly maintained.

**Bottom line on question 3 (propagation):** every numeric ceiling I probed propagates to
`CheckResult.passed=False` against a defect in the production artifact — 8 of 8 seeded probes went
red and 8 of 8 returned to green on restore.

The defects are in the **tests that guard two of the ratchets**, in the **`--ci` skip mechanism**,
and — the important one — in a **resolver tier that lets the ratcheted check whitelist names it
knows do not exist**.

---

## Findings

### CRITICAL-1 — `prose_theorem_reference_coverage` resolves a prose reference as OK because it is a KEY in a hand-maintained registry, including 14 keys the branch's own ratchet certifies name nothing

**Where:** `scripts/validation/checks/prose_lean_refs.py:429`
```python
    if token in index["registry_keys"]:
        return "OK"
```
built at `prose_lean_refs.py:284–304` from `PLACEHOLDER_THEOREMS`, `AXIOM_METADATA`,
`HYPOTHESIS_REGISTRY`, `ARISTOTLE_THEOREMS`, `PARAMETER_PROVENANCE` and every public callable in
`formulas.py` — **606 keys**, unioned into the same index as the 40 262 real `lean_deps.json`
declarations, and consulted *before* any Lean-name tier.

**What breaks.** The check is registered as *"Bundle-draft verbatim Lean references … resolve in
`lean_deps.json`"* and exists to prevent the `wen_adw_factor_6000` class — prose naming a Lean
declaration that does not exist. For 606 tokens it does not check `lean_deps.json` at all. Among
them are **all 322 `ARISTOTLE_THEOREMS` keys, 14 of which `ARISTOTLE_REGISTRY_UNRESOLVED_CEILING`
exists precisely to record as naming no declaration**, and all 10 `AXIOM_METADATA` keys (every one
a *removed* axiom). The ratchet at `constants.py:1389` bounds the laundering into
`check_formulas_to_theorems`; nothing bounds this second, larger laundering path.

**Concrete failing input, seeded in the PRODUCTION artifact, with a control:**

```
# probe A — a known-stale Aristotle key appended to the real papers/D10/paper_draft.tex
Proved formally as \texttt{DG\_basis\_mul} in the Lean library.
  -> prose_theorem_reference_coverage: passed=True
     "21 bundle drafts scanned / 1052 candidate Lean references — 0 unresolved FAIL(s)"

# probe B — CONTROL, one character different, not a registry key
Proved formally as \texttt{DG\_basis\_mulX} in the Lean library.
  -> prose_theorem_reference_coverage: passed=False
     "unresolved:D10:DG_basis_mulX — \texttt{DG_basis_mulX} does not resolve to any
      declaration in lean/lean_deps.json (no disclaimer context; Class-TN drift)"
```

`DG_basis_mul` is in the check's own printed list of the 14 unresolved registry entries. A bundle
draft may claim it as a formally verified Lean theorem and the gate reports the corpus clean.

**Live corpus exposure** (predicate: token resolves `OK` with the registry tier enabled and does
*not* resolve `OK` with `index["registry_keys"]` emptied, everything else identical):
**29 tokens across the 64 drafts** reach `OK` only through this tier —
23 are `formulas.py` names (legitimate per the docstring), 3 `HYPOTHESIS_REGISTRY`, 1
`PARAMETER_PROVENANCE`, 1 `PLACEHOLDER_THEOREMS`, and **1 is a known-dead Aristotle key**:
`fock_space_finite_dim`, cited in `papers/paper7_chirality_formal/paper_draft.tex` and counted as
*resolved* by the very leg whose ceiling (`LEGACY_DRAFT_UNRESOLVED_REF_CEILING = 79`) is supposed
to freeze that corpus's debt. So the "79" is measured with 14 names pre-exempted.

**Why this is CRITICAL and not MAJOR.** This is the exact question the pass was commissioned to
answer — *where else is an instrument pointed at a population it does not reach* — and it is in the
**same check** that was repaired twice this week (`c7148779` `\lean{}`, `c5f384b4` `\verb`). Both
repairs widened the *extractor*. Neither touched the *resolver*, and the resolver contains a
whitelist of 606 names that bypasses the substrate entirely.

**Suggested shape of a fix (not applied — Rule 7):** the registry tier should be split. A
`formulas.py` name and a `PARAMETER_PROVENANCE` key are legitimately not Lean declarations. An
`ARISTOTLE_THEOREMS` key **claims to be one** — so it should resolve through `lean_deps.json` like
any other token, with `unresolved_aristotle_keys()` subtracted, which is the same "one owner"
move `lean_toolchain.py` already made for `check_formulas_to_theorems`.

---

### MAJOR-1 — `test_ci_mode.py`'s zero-headroom test is STILL self-sealing after the fix that named it

**Where:** `tests/test_ci_mode.py:157–168` vs `scripts/validate.py:735–746`.

`validate.main()` was fixed on 2026-08-05 to count `r.measured` instead of `len(results)`, and its
own comment identifies why the earlier defect was invisible:

> `test_ci_mode.py`'s zero-headroom test asserts `CI_MIN_CHECKS_RUN == len(_CHECKS) - len(CI_SKIP)`
> — the very definition of the quantity being compared — so the guard and its test were jointly
> self-sealing.

**The guard was changed. The test was not.** It still reads:

```python
expected = len(validate._CHECKS) - len(_cfg.CI_SKIP)
assert _cfg.CI_MIN_CHECKS_RUN == expected
```

That is an identity over two hand-maintained collections. The guard now compares against
`sum(r.measured for r in results.values())` — a *different population*, one that shrinks whenever a
check hits a cannot-measure branch.

**Verified by seeding the production artifact.** I edited the real
`scripts/validation/checks/papers_prose.py` so `check_numerical_literals` takes its
`measured=False` early return unconditionally, cleared `__pycache__`, and confirmed the check now
returns `measured=False`. Then:

```
$ pytest tests/test_ci_mode.py -q
12 passed in 0.03s
```

A production check that stopped measuring — the exact state the floor exists to detect — leaves
the "ZERO headroom" test entirely green. Restored; `12 passed` again on the clean tree.

**Consequence.** The floor's headroom is unmeasured by any test, in either direction. If it were
raised above what a provisioned runner can measure, `--ci` would go red on correct work and be
switched off; if lowered, the floor stops guarding. Neither is detectable today. The fix is a test
that runs the live registry and asserts `len([r for r in run_checks().values() if r.measured])`
equals the floor on a provisioned tree.

---

### MAJOR-2 — `CI_SKIP` does not skip: the four checks run in full, then their results are deleted

**Where:** `scripts/validate.py:666` then `675–679`.

```python
results = run_checks(check_filter=args.check)      # runs EVERY registered spec
...
if _cfg.CI_MODE and not args.check:
    for name in list(results):
        if name in _cfg.CI_SKIP:
            del results[name]                       # discard AFTER paying for it
```

`_config.py:92` documents `CI_SKIP` as *"Checks skipped under `--ci`"*, and every one of the four
reasons is a **cost** argument — `counts_fresh`: *"shells to update_counts.py (1800s, needs lake)"*;
`tables_fresh`: *"shells to render_paper_tables.py (300s)"*; `notebook_exec`: *"a fresh runner
executes all 91 from cold"*. None of that cost is avoided.

**Verified by execution, seeded in the production artifact.** I inserted a sentinel write at the
top of the real `check_counts_fresh` body in `scripts/validation/checks/freshness.py`, cleared
`__pycache__`, and ran `scripts/validate.py --ci --no-archive`:

```
$ cat /tmp/r3_ciskip_sentinel.txt
counts_fresh EXECUTED under --ci
$ grep -E "skipped 4" …
  --ci: skipped 4 check(s) whose premise does not hold on a fresh clone:
        claim_clusters_fresh, counts_fresh, notebook_exec, tables_fresh
```

The run reports the check as skipped in the same breath as having executed it. Restored.

**What breaks.** Three things, in increasing severity:
1. The mode delivers none of its stated saving. On a runner with `lake` and cold notebooks this is
   the full ~1800 s + 300 s + 91-notebook cost, paid and thrown away.
2. **A real verdict is computed and discarded.** If `notebook_exec` fails on the runner, `--ci`
   deletes the failure. This is precisely the "computed its verdict and discarded it" pattern the
   branch fixed in `paper_latex_compiles` and cites in `MUTATION_VERIFIED` as an ADR-009 §Deferred
   item.
3. The stated premise ("does not hold on a fresh clone") is applied inconsistently:
   `axiom_closure_allowlist` and `lean_build` also shell to `lake`, are **not** in `CI_SKIP`, and
   **must measure** for the floor to be reachable. On this worktree `axiom_closure_allowlist`
   triggered a from-scratch Mathlib build via `lake env lean --run` (it has a 600 s timeout, so on
   a cold runner it can only ever time out → `measured=False` → the floor can never be met).

**Live evidence the floor itself is sound:** the same run ended
`✗ CI COVERAGE FLOOR: 54 of 56 check(s) actually MEASURED, floor is 56 … rc=1`, naming
`axiom_closure_allowlist, paper_latex_compiles` as unmeasured. The **guard** works. The **skip
mechanism** and the **guard's test** do not.

---

### IMPORTANT-1 — `VACUOUS_STATEMENT_BASELINE` has a seam guard 8 below its live size and no staleness test

**Where:** `src/core/constants.py:2524` (48 names); guard at
`tests/test_substrate_integrity_gates.py:367` — `assert len(VACUOUS_STATEMENT_BASELINE) >= 40`.

Measured live, using the two consumers' own predicates
(`lean_statements._thin_type_label` ∈ `_THIN_HARD`, and
`lean_substrate._STRUCTURAL_NAME_RE` + `_TRIVIAL_BODY_RES` over `_scan_lean_theorem_bodies`):

* 48 baseline names; **30** flagged by the type-thin leg, **23** by the body-thin leg, 5 in both,
  union **48**. **Stale entries: 0.**

So the set is *in fact* exactly at zero staleness — but nothing holds it there:

* The only size assertion is `>= 40` against a live 48: **8 units (17 %) of slack**. This is the
  identical shape pass 2 fixed in `test_cannot_measure_baseline` (`>= 30` against a live 54,
  44 % headroom) — the fix was applied to that file and not to this one.
* There is **no `test_baseline_has_no_stale_entries` equivalent.** `test_cannot_measure_baseline`
  has one and its docstring explains why ("leave the ratchet slack"). A `VACUOUS_STATEMENT_BASELINE`
  entry whose theorem was strengthened or deleted stays in the set forever, and the name it
  reserves is permanently grandfathered for any future declaration.

The ratchet's *forward* direction is sound — I seeded a new reflexive `Eq X X` declaration into the
real `lean/lean_deps.json` and `vacuous_statement_audit` went `passed=False` naming it.

---

### IMPORTANT-2 — a `PLACEHOLDER_THEOREMS` entry is a permanent exemption from both thinness audits, and nothing checks it still describes a placeholder

**Where:** `src/core/constants.py:2187` / `:2426`; consumed as
`exempt = set(PLACEHOLDER_LEAN_NAMES.keys())` at `lean_substrate.py:399` and
`lean_statements.py:467`.

Measured: all **26** registered placeholder names exist in `lean_deps.json` and **all 26 still
elaborate to type `True`** — the registry agrees with derived truth today. But no check asserts
that agreement:

* If a placeholder is genuinely discharged (given a real statement and proof), the entry persists
  and the name keeps a **permanent** exemption from `vacuous_statement_audit` and
  `proxy_body_audit`, and `placeholder_not_cited` keeps forbidding papers from citing a theorem
  that is now real — a gate firing on correct work, which is a gate that gets switched off.
* If the Lean declaration is deleted, the entry names nothing and the registry-key tier in
  CRITICAL-1 launders the dead name into the prose resolver.

Contrast `KERNEL_NOGO_REGISTRY` (45 entries), which **does** have this check:
`nogo_substrate_integrity` verifies every `backing_theorems` entry exists, is kernel-pure and is
non-vacuous, and it passes live. That is the template.

---

### IMPORTANT-3 — the ratchet meta-test's roster is frozen and cannot notice a ratchet that was never added

**Where:** `tests/test_ratchets_have_zero_headroom.py:47–54, 96–105`.

`RATCHETED_CHECKS` is a hand-written 6-tuple; the seam guard is `len(RATCHETED_CHECKS) >= 6`
(currently exactly 6, so no slack) plus a registered-name check. Neither can detect a **new**
ratcheted check that nobody added. Two of the branch's own ratchets are outside the roster:
`prose_theorem_reference_coverage` (its `legacy_ratchet` Detail literally prints `ceiling 79`) and
`bibitem_title_primary_source`.

Both happen to carry their own live zero-headroom tests, so there is **no live gap** — I verified
`test_the_live_legacy_ceiling_has_ZERO_headroom` and
`test_the_live_drift_ceiling_has_ZERO_headroom` both run against the real corpus. But the meta-test
advertises itself as "*every* ratcheted check sits at zero headroom" and, as written, it is a
manually-curated 6 of the 8 check-level ratchets. Deriving the roster by scanning live Details for
`ceiling \d+` (which is already the parse it performs) would make the claim true by construction.

---

### MINOR-1 — `elaboration_knob_watchlist` is registered and documented as non-failing, and now gates

`lean_toolchain.py:617` still reads *"THIS check is a NON-FAILING watchlist … Always passes."*, and
its registered description begins *"Watchlist (advisory)"* — but since the Invariant-#10 leg
landed it returns `passed = not over` and I confirmed it goes `passed=False` on a seeded 23rd
`maxHeartbeats`. Anyone reading `--list` or the docstring will not expect this to block a commit.
Also cosmetic: all 22 violation Details carry `passed=False` inside a `passed=True` CheckResult, so
`print_results` shows 22 `✗` lines under a `✓ PASS` header.

### MINOR-2 — stale check counts in three ratchet docstrings

Live registry is **60**. `_config.py:108–123` says *"48 of 55"*, *"identically `59 - len(CI_SKIP)`
= 55"* and *"48 of 59"*; `test_d5_mutation_obligation.py:12,52,56` says *"59 checks"*, *"4 of 59"*
and *"All 59 registered checks"* while `PRODUCTION_SEEDED` now holds 5 and
`FIXTURE_ONLY_CEILING` is 55 = 60 − 5. The numbers in the prose contradict the numbers the code
enforces.

### MINOR-3 — `run_checks`'s exception path counts a crashed check as MEASURED

`validate.py:243–244` returns `CheckResult(passed=False, error=str(e))`, and `measured` defaults to
`True` (`_registry.py:99`). A check that raises therefore counts toward `CI_MIN_CHECKS_RUN`.
Impact is bounded — `passed=False` reddens the run anyway — but the floor's stated semantics
("checks that actually MEASURED") is not what it computes.

### MINOR-4 — `bibitem_title_primary_source`'s zero-headroom test counts display Details, which are capped at 20

`test_d5_citations.py:332` counts `d.name.startswith("drop_word:")`, but the check emits at most 20
such Details plus a `drop_word:overflow` summary (`citations.py:~965`). At 7 live flags this is
correct; above 20 the test would compare 20 against the ceiling and could pass on slack. Latent,
not live.

### MINOR-5 — a `validate.py --ci --no-archive` run dirties 9 tracked files

After the `--ci` run, `git status` showed
`papers/{D1,D2,D3,D4,D5,E1,F,I1,L2}/bundle_metadata.json` modified (1 line each). I did **not**
isolate the writer — `bundle_metadata_matches_graph`, `readiness_verdicts_agree` and
`readiness_submission_gate` each ran clean individually. Flagged for whoever owns check side
effects: a verification run that mutates tracked artifacts makes "run validate, then diff" an
unreliable review move, and it is how pass 2 lost a stubbed check body and a zeroed
`paper_draft.tex`.

---

## Registries checked against derived truth

| registry | size | agrees with derived truth? | is there a check that proves it? |
|---|---|---|---|
| `ARISTOTLE_THEOREMS` | 322 | 14 keys resolve to no declaration | **Partly.** `theorems` ratchets the 14 into `check_formulas_to_theorems`; the prose resolver launders all 322 unbounded (CRITICAL-1) |
| `AXIOM_METADATA` | 10 | ✅ `lean_deps.json` contains **0** `kind == "axiom"` project declarations; all 10 entries are historical (`removed`/`closed`/`ELIMINATED`/`planned`) and 0 live axioms are missing from it | **No.** No check asserts `{live project axioms} ⊆ AXIOM_METADATA`; `axiom_closure_allowlist` is the nearest and it did not measure here |
| `PLACEHOLDER_THEOREMS` / `PLACEHOLDER_LEAN_NAMES` | 26 / 26 | ✅ all 26 resolve and all 26 still elaborate to `True` | **No** — IMPORTANT-2 |
| `KERNEL_NOGO_REGISTRY` | 45 | ✅ every `backing_theorems` entry exists, kernel-pure, non-vacuous | **Yes** — `nogo_substrate_integrity`, passes live. The model for the others |
| `MODELING_ASSUMPTION_THEOREMS` | 21 | ✅ every `lean_name` resolves | **Yes** — `proxy_body_audit` rejects entries missing `reason`/`discloses` |
| `HYPOTHESIS_REGISTRY` | 48 | 56 tracked Prop-defs, 24 consumed, 24 covered — so 24 registry entries have no consumed Prop | **Partial** — `tracked_hypothesis_ledger` proves *consumers ⊆ registry*, not *registry ⊆ live Props*. I did not chase whether an unconsumed entry is legitimate (landmark hypotheses exist); **flagged, not filed** |
| `PARAMETER_PROVENANCE` | 206 | ✅ 206/206 covered, all LLM-verified, all values match code (78 awaiting human verification, which correctly blocks submission only) | **Yes** — `parameter_provenance` |
| `CITATION_REGISTRY` | 652 | 7 DROP-WORD / 58 NOT-FOUND against 303 cached PDFs | **Yes, ratcheted** — `bibitem_title_primary_source`, strict-only |

---

## Question 4 — are the measured quantities STABLE?

I found **no** ratchet keyed to something that moves for innocent reasons: none reads an mtime, a
timestamp, or a monotonically growing corpus count. `native_decide_regression` explicitly moved
*off* `docs/counts.json` (mtime-based) onto `lean_deps.json` (content-hash), and treats a
`counts.json` disagreement as a warning only — I saw that warning fire correctly during the
`lean_deps.json` mutation probe. `bundle_source_freshness` is mtime-keyed but is deliberately kept
out of `--strict` under CI for exactly this reason (`test_ci_mode.py::TestCiIsNotStrict`), which is
the right call.

The one instability risk is **`CI_MIN_CHECKS_RUN` on a cold runner**: `axiom_closure_allowlist`
shells to `lake env lean --run` with a 600 s timeout, which a fresh clone cannot satisfy (I watched
it start a from-scratch Mathlib build in this worktree), so the floor is unreachable in exactly the
environment `--ci` names in its own docstring. That is MAJOR-2's third bullet.

---

## Restoration

Every mutation was reverted with `git checkout --` and `__pycache__` cleared after each `.py`
edit; `lean/lean_deps.json` was restored from a byte copy. Final state:

```
$ git status --porcelain
(empty)
```
