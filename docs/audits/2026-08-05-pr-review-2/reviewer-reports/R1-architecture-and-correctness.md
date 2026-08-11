# R1 — architecture and correctness

**Reviewer:** R1 · **Branch:** `infra/adr-009-validation-modularization` · **Base:** `main` @ `c2b597e1`
**Date:** 2026-08-05 · **Lens:** is the code correct, and is the structure sound?

Everything below was run from `SK_EFT_Hawking/`. No file outside this report was modified;
no commits, no `lake build`. Probe scripts were written to the session scratchpad, and the
two memo probes were pointed at a throwaway cache (`_memo._cache_path` monkeypatched) so the
developer's `docs/validation/.check_memo.json` was never touched.

---

## Summary

The split itself is **sound**. 12 check modules, 398–1024 lines each, no duplicated helper,
no duplicated regex, no dead constant, no verdict computed-and-discarded at a function tail
(all four measured, §6). H3 is real and correctly placed; H4's divergence is preserved and
frozen; H5 is clean at every site. The behavioural repairs in `build_graph.py`,
`readiness_gates.py`, `bundle_readiness.py` and `atlas_view.py` are each correct and each
lands with a test that fires on a seeded defect.

What is **not** sound is the newest surface. `_memo.py` landed 2026-08-05 and reintroduces
the branch's own defect class in two places, both measured below:

* it **persists a "could not measure" PASS** and replays it after the cause is fixed (R1-MAJ1);
* its "guard 1" covers less than its docstring claims, and I can name an in-tree input that
  moves a verdict without moving the key (R1-MAJ3).

And the `--ci` coverage floor — the guard written specifically to stop a toolchain-less
runner from going green — **cannot fire for that cause** (R1-MAJ2). Its test seeds the defect
by shrinking the registry, which is not the production failure it names.

**Verdict: YES WITH FIXES.** See §7.

---

## 1. CRITICAL

None. Nothing on this branch makes a previously-working guard unable to fire *for its
existing scope*; the three MAJORs are all in surface that did not exist on `main`, and each
has a small, contained fix.

---

## 2. MAJOR

### R1-MAJ1 — `_memo` caches a *cannot-measure* PASS and replays it after the cause is fixed

**Where:** `scripts/validation/_memo.py:265-281` (the store) ×
`scripts/validation/checks/lean_toolchain.py:472-515` (`axiom_closure_allowlist`'s five
toolchain-absent early returns) and `:691-695` (`lean_docstring_refs_resolve`'s
`lean_deps.json`-absent early return).

**What it claims.** `_memo.py:54-58`: *"FAIL-SAFE DIRECTION — Every error path here computes
rather than skips… The cache can only ever make a run slower when it is broken, never
greener."* `_memo.py:43-45`, guard 3: *"Only PASS is cached. A failing check re-runs every
time."*

**What it actually does.** Guard 3 is `if result.passed` — and a check that could not reach
its input returns `passed=True` by design. `tests/test_cannot_measure_baseline.py:97-113`
freezes exactly three such branches for the two memoized checks:
`('axiom_closure_allowlist','exception')`, `('axiom_closure_allowlist','missing-input')`,
`('lean_docstring_refs_resolve','missing-input')`. The memo does not distinguish them from a
measured PASS, so it writes the unmeasured verdict to disk under a key that does not mention
the toolchain — and returns it on every later run until a `.lean` file or a pin file changes.
A degraded run does not stay degraded; it **poisons the next N good runs**.

**How I verified.** `scratchpad/probe1.py` — `axiom_closure_allowlist`, broken toolchain, then
restored, throwaway cache:

```
A) broken LAKE_PATH -> passed= True | details: [('axiom_audit_run',
     "SKIPPED — [Errno 2] No such file or directory: '/nonexistent")]
   memo file written?  True
   entries: ['axiom_closure_allowlist']
B) after toolchain 'restored' -> passed= True | first detail: memo
     SKIPPED (cached) — Lean sources, toolchain pins, AXIOM_METADATA unchanged since ...
```

`scratchpad/probe2.py` — same shape for the second memoized check:

```
A) lean_deps absent -> passed= True [('skipped', 'lean_deps.json absent')]
   memo entries: ['lean_docstring_refs_resolve']
B) lean_deps present again -> passed= True first detail: memo SKIPPED (cached) — ...
   n details: 2
```

In (B) both checks return a cached PASS **without ever invoking `AxiomAudit` / reading the now-
present `lean_deps.json`**.

**Blast radius.** `axiom_closure_allowlist` is the Invariant #15 backstop — the only automated
gate on the project's axiom trust surface. Any workstation, container, worktree slot or agent
sandbox that runs `validate.py` once without `lake` on PATH (the `wtN` slots and
`pre-commit-sync.sh:34-36` both document that git hooks / minimal envs routinely lack it)
leaves that gate answering from cache. Partial mitigation, and it is real: the replayed
details still carry the original `SKIPPED — …` text, so a reader who reads past the verdict
can see it. `--strict` (submission gate) bypasses the memo entirely, so the irreversible
consumer is safe.

**Fix (small).** Refuse to *store* a result whose details indicate non-measurement. Either
have the early returns carry an explicit marker the memo reads, or — cheapest — in
`memoized`, skip the store when any detail message starts with `"SKIPPED"`. Either way, add
the probe above to `tests/test_validation_memo.py`: it is precisely the production-seeded
mutation that class of test is for, and it is the one seed the file does not contain.

---

### R1-MAJ2 — the `--ci` coverage floor cannot detect a missing toolchain, which is the only cause it names

**Where:** `scripts/validate.py:659-677`; `scripts/validation/_config.py:108-119`;
`tests/test_ci_mode.py:125-142`.

**What it claims.** `_config.py:110-118`: *"Dropping the Lean toolchain from a runner makes the
suite ~200 s faster and stops 7 checks that read `lean_deps.json` plus 3 that shell to `lake`
from measuring anything — while the run still reports green… So `--ci` FAILS when fewer checks
execute than this. A missing toolchain becomes a red build reading '48 of 55 ran', not a green
tick."* `validate.py:673-676` repeats the diagnosis in the failure message.

**What it actually does.** `n_ran = len(results)`, and `run_checks` (`validate.py:232-239`)
assigns `results[spec.name]` on **both** branches of its `try/except`. A check whose toolchain
is absent still runs, still returns, still occupies a slot — and returns `passed=True`. So
`n_ran` is a pure function of the registry size minus `CI_SKIP`, independent of what any check
could measure. `48 of 55` is not a reachable state.

**How I verified.**

```
$ uv run --no-sync python -c "... import validate as v; from validation import _config as c"
canonical order len: 59 · registered: 59 · dupes: 0
CI_SKIP: 4 · floor: 55 · after skip: 55
```

`scratchpad/probe7.py` — three specs, one of which raises and two of which take the
`lake not found` early return:

```
specs: 3 -> results (== n_ran under --ci): 3 | verdicts: {'a': True, 'b': False, 'c': True}
```

`len(results)` tracks `len(_CHECKS)`, not measurement.

**Why the test does not catch it.** `test_a_shrunken_suite_FAILS_even_though_every_check_passed`
(`tests/test_ci_mode.py:128-142`) seeds the defect by monkeypatching `_CHECKS` down to 6 specs
against a floor of 9 — i.e. by **deleting registry entries**, which is not how a runner loses a
toolchain. This is QI-30's criterion inverted: the mutation is seeded in a fixture whose shape
the production artifact cannot take. `test_the_LIVE_floor_has_ZERO_headroom` (`:157-167`) then
pins `CI_MIN_CHECKS_RUN == len(_CHECKS) - len(CI_SKIP)`, which makes the tautology explicit and
frozen.

**Blast radius.** `--ci` has no caller today (no workflow file on this branch), so nothing is
currently green-by-mistake. It becomes live the moment CI is wired, which is the stated next
step — and at that point the mode's *entire raison d'être* per its own docstring is inoperative.
The floor still functions as a registry-size ratchet, which is worth having; it is just not
what it says it is.

**Fix.** Count *measurement*, not registration. Cheapest honest version: under `--ci`, fail if
any check returned a detail whose message begins `SKIPPED` (the suite already spells
non-measurement that way, 25 sites, frozen in `test_cannot_measure_baseline.py`). Failing that,
add explicit `--ci` preconditions (`lake`, `pdflatex`, `lean_deps.json` present) that hard-fail
before any check runs. Whichever is chosen, restate the docstring: the current text asserts a
capability the code does not have.

---

### R1-MAJ3 — the memo key omits module-level constants and helper sources; guard 1 is narrower than its docstring

**Where:** `scripts/validation/_memo.py:133-145` (`source_fingerprint`), `:243` (the fold-in),
`:38-40` (the claim).

**What it claims.** `_memo.py:38-40`: *"**The key includes the check function's own source**
(`source_fingerprint`). Editing the check — **including editing what it reads** — invalidates
every entry. This is the guard that makes the others recoverable rather than permanent."*

**What it actually does.** `inspect.getsource(fn)` returns the text of that one `def`. Module-
level constants the body reads, and every helper it calls, are outside the digest.
`check_lean_docstring_refs_resolve` reads three module-level names —
`_DOCSTRING_STRICT_FAMILIES`, `_DOCSTRING_TOKEN_RE`, `_DOCSTRING_BLOCK_RE`
(`lean_toolchain.py:640-647`) — and `_DOCSTRING_STRICT_FAMILIES` is the switch that decides
FAIL vs advisory (`:736`, `:754-769`). Widening it is the most likely future edit to this check
and it moves verdicts without moving the key. `check_axiom_closure_allowlist` likewise calls
`_resolve_lake` / `_resolve_lean_root` (`lean_toolchain.py:59-75`), neither hashed; the latter
honours `LEAN_PROJECT_DIR`, so it can retarget the audit at a different Lean project while the
key keeps hashing `<repo>/lean/SKEFTHawking`.

**How I verified.** `scratchpad/probe2.py` leg C — widen `_DOCSTRING_STRICT_FAMILIES` to cover
every module, recompute the key:

```
C) key unchanged after widening strict families: True
```

And `scratchpad/probe6.py` gives the general shape (verdict flips `True → False` with the key
held fixed; the body is never re-entered):

```
after B evicts: ['chk1']          # B was a cache HIT, not a recompute
run C: body executed? False | verdict: True
```

**Blast radius.** Bounded today: both memoized checks' keys do cover their *file-based* inputs
(I confirmed `lean_source_fingerprint`, `toolchain_pin_fingerprint`, `constants.py`,
`update_counts.py`), and `tests/test_validation_memo.py::TestKeyCoversItsInputs` seeds each of
those in the production tree. The gap is the *next* edit, and the docstring actively tells the
next author it is covered.

**Fix (one line).** Hash the whole defining module:
`inspect.getsource(inspect.getmodule(fn))`. That covers constants and same-module helpers, and
costs nothing. Cross-module helpers (`_H.*`) remain outside; say so in the docstring rather
than claiming closure.

---

## 3. IMPORTANT

### R1-I1 — the H1 alias guard misses the `X = _H.NAME / "y"` form; 5 live sites, and two modules' docstrings deny it

**Re-files pass-1 `R3-I5` (still OPEN)** — confirming it survived, now with a count.

`tests/test_validate_public_surface.py:298-342` only flags a module-level `ast.Assign` whose
value is a bare `ast.Attribute` on `_H`. Any derivation (`BinOp`, `List`) escapes. AST scan
(`scratchpad/scan.py`) over `scripts/validation/**/*.py`:

```
freshness.py:50   _COUNTS_SOURCES     <- LEAN_DEPS_PATH, SRC_DIR, SRC_DIR
freshness.py:195  _TABLES_SOURCES     <- LEAN_DEPS_PATH, SRC_DIR×4, PROJECT_ROOT×4
freshness.py:284  CLAIM_CLUSTERS_PATH <- PAPERS_DIR
notebooks.py:51   NOTEBOOK_EXEC_CACHE <- NOTEBOOKS_DIR
prose_lean_refs.py:290 _PHYSLIB_DIR   <- PROJECT_ROOT
```

Five sites, four of them pinned by `tests/test_d5_freshness.py::TestPathAliasCoupling` /
`test_d5_notebooks`; `_PHYSLIB_DIR` remains the one unpinned site pass-1 named.

The reason to re-file at IMPORTANT rather than MINOR is the **documentation**, which is where
a reader forms their model: `notebooks.py:44-45` reads *"NO LOCAL PATH ALIASES — reach
`_H.<NAME>` at each use"* **six lines above `NOTEBOOK_EXEC_CACHE = _H.NOTEBOOKS_DIR / …`**, and
`freshness.py:21-24` reads *"paths are reached as `_H.<NAME>` at each use rather than through
module-level aliases"* **26 lines above `_COUNTS_SOURCES`**. That is the "document describing a
repaired guard as broken, or a broken guard as fine" face of the class, in the modules the
guard exists for. Either widen the AST predicate to any module-level expression referencing
`_H`, or amend both docstrings to state the exception and why it is safe here.

---

### R1-I2 — `--strict` reachability is documented two ways on the same branch

`scripts/validation/checks/bundles_readiness.py:548-549`:
> *"(`--strict` remains unreachable in practice anyway — no automated caller passes it;
> §Deferred item 6.)"*

`scripts/gate_precheck.py:51,85-87` adds `"submission": ["__strict__"]` →
`validate.py --strict --force-latex --no-archive`, and
`scripts/validation/checks/citations.py:934-940` reasons *from* that caller existing
(*"`--strict` now had a caller (`gate_precheck submission`, added the day before), so this
would have made the submission gate red on 62 entries…"*). Verified: `gate_precheck.py:86`
passes `--strict`, and `tests/test_gate_precheck.py:125-133` asserts it.

Both statements are in the diff. The stale one is load-bearing: it is the stated justification
for `readiness_submission_gate` no longer honouring `--strict`, and it tells the next reader
the submission gate is dead when it is not. One-line docstring fix.

---

### R1-I3 — the commit gate's three check names are not registry-validated; a rename degrades it to a silent SKIP

`scripts/pre-commit-sync.sh:37-39` maps `rc==0 → PASS`, `rc==1 → FAIL`, **anything else →
SKIP**, and `:98-101` treats SKIP as non-blocking by design ("don't wedge the loop on a
transient"). `scripts/validate.py:589-592` returns **rc 2** for an unknown `--check` name. So
renaming any of `formula_grounding`, `placeholder_not_cited`, `native_decide_regression`
silently disarms the commit gate — the one place that hard-blocks `main`.

The asymmetry is the point: `tests/test_ci_mode.py:116-122::test_the_skipped_checks_are_REAL`
does exactly this validation for `_cfg.CI_SKIP` ("*an exclusion naming a check that no longer
exists is silent scope creep*"), and `gate_precheck.py` is safe because `rc |= 2` propagates as
FAIL. Nothing does it for the shell gate. Verified: no test in `tests/` references
`pre-commit-sync.sh`'s check list (`rg 'formula_grounding.*placeholder_not_cited' tests/` → 0
hits); all three names are currently registered.

Fix: one test asserting the three names parsed out of `pre-commit-sync.sh` are in
`validate._CHECKS` — the `test_the_skipped_checks_are_REAL` idiom, one file over.

---

### R1-I4 — Paper 15's Table 2 is now numbered by source-file name, i.e. by the ordering H3 declares non-semantic

`scripts/paper_tables/sources.py:459-489`. The QI-01-class widening (scan the whole
`validation` package, not just `validate.py`) is **correct and necessary** — without it the
table shipped empty from `c3456a23`. But the sort key became `(src.name, dec.lineno, …)`, so
the published "Check" column is now ordered alphabetically by module filename.

Measured:

```
main  row 1: 1 & \texttt{formulas} & Python formulas reference valid Lean theorems
HEAD  row 1: 1 & \texttt{bundle_figure_integrity} & Bundle figures match a fresh render …
(59 rows both sides)
```

ADR-009 H3 exists to say that which module a check lives in has no semantics —
`validate._CANONICAL_ORDER` is the declared truth and is importable. Deriving a *published*
artifact's numbering from the property H3 just declared meaningless re-couples them, and the
table will churn on every module rename or split.

Blast radius today is contained: I measured **0** references to check numbers in
`papers/paper15_methodology/paper_draft.tex` (`rg 'CHECK [0-9]|Check~?[0-9]|check [0-9]+'` →
no hits), so nothing cites a number that moved. Two follow-ons: sort by `_CANONICAL_ORDER`
position, and fix the now-wrong provenance line the table emits,
`% Description: validate.py @register_check decorators`
(`papers/paper15_methodology/tables.py:19` / rendered at
`papers/paper15_methodology/tables/table2_checks.tex:4`).

---

### R1-I5 — a hand-authored table `\input` by a Tier-1 bundle draft sits outside `tables_fresh`'s scope

`scripts/validation/checks/freshness.py:212` and `:219` glob `paper*_*/tables.py` and
`paper*_*/tables/*.tex`. Bundle directories (`D*`, `I*`, `L*`, `E*`, `F`) do not match.

Measured: `papers/I1/tables/table1_stages.tex` is tracked, is `\input{tables/table1_stages.tex}`
by `papers/I1/paper_draft.tex`, and is the only `tables/*.tex` outside `paper*_*/`. Its own
header reads:

> `% Hand-authored for paper I1; tracks docs/WAVE_EXECUTION_PIPELINE.md.`
> `% If WAVE_EXECUTION_PIPELINE.md is updated, sync this table.`

`_TABLES_SOURCES` (`freshness.py:195-204`) already lists
`docs/WAVE_EXECUTION_PIPELINE.md` — but the output glob excludes I1, so that source is watched
for nine legacy papers and not for the bundle that actually renders it. This is the
"hand-maintained list parallel to a registry" face, and the instruction to sync is enforced by
nobody.

No live drift today: the table carries 14 stages (with 3a/3b split) and
`docs/WAVE_EXECUTION_PIPELINE.md` has 14 `## Stage N` headings. Pre-existing on `main`; in
scope here because `tables_fresh` and its source list were both touched.

Note the same scope is spelled *wider* two files away: `scripts/pre-commit-sync.sh:50` restages
`$(git ls-files 'papers/*/tables/*.tex')`. Two globs for one population.

---

### R1-I6 — the LaTeX cache key omits the compiler, and `--force-latex` declines to record what it re-measured

`scripts/validation/checks/papers_prose.py:414-447` (`_draft_input_closure`), `:520-524`,
`:559-565`.

The closure is a genuinely good superset — `\input`/`\include` resolved recursively with
LaTeX's `.tex` default, `\includegraphics` one level, sibling `*.bib`, unresolvable refs kept
as paths so a later appearance moves the hash. I attacked it and could not find a live under-
hash: all 100+ `\includegraphics` targets in `papers/*/paper_draft.tex` carry an extension
(so the "no suffix defaulting for group 2" asymmetry at `:441` is latent, not live); there are
**0** `.sty`/`.cls` files anywhere under `papers/`; **0** graphics paths containing a macro;
and `docs/counts.tex` contains no nested `\input`.

What it does not hash is the **TeX distribution**. A TeX Live upgrade can turn a clean draft
fatal, and all 20 currently-clean bundles would stay cached
(`papers/.latex_compile_cache.json` holds 20 of 21 codes; D3 correctly absent). `--force-latex`
is the documented escape — but `:559` guards the cache *write* with `if not _cfg.FORCE_LATEX`,
so the one run that re-measures after a toolchain change is also the one run that refuses to
record the result. Add the toolchain to the key (`pdflatex --version` digest is one cheap
subprocess, once per run), or at minimum let `--force-latex` rewrite the cache.

---

## 4. MINOR

### R1-MIN1 — `_iter_test_functions` double-yields a test defined in a nested class

**Confirms pass-1 `R1-I4` / `R3-M4`, which the on-disk summary contradicts** (FINDINGS_REGISTER
§"Contradictions", item 1: the summary calls it "correct behaviour"; two reviewers called it
double-minting). The reviewers are right.

`scripts/build_graph.py:1418-1440`: `ast.walk(tree)` yields nested `ClassDef`s at every level,
and the inner loop walks each — so a `def test_*` inside `class Outer: class Inner:` is yielded
twice with two different qualifiers, producing two distinct `test:<mod>::<Class>::<fn>` ids
that `seen_ids` cannot merge.

```
$ probe4.py  ->  [('test_x', 'Outer'), ('test_x', 'Inner')]
```

Not live: measured **4909 `def test_*` across 177 files → 4909 PythonTest nodes**, exact
(`probe3.py`). Two secondary notes: the docstring's "in source order" is false (class-scoped
tests are yielded before module-level ones), and the branch's own count comment at
`build_graph.py:1483-1487` cites 4,416/4,350 — that measurement is now 4909/4909 and should
be restated or dated.

### R1-MIN2 — the memo cache is an unsynchronised, non-atomic read-modify-write

`_memo.py:265-279`: `result = compute()` → `entries = _load()` → mutate → `_store()`; `_store`
does `write_text` (truncate-then-write), no temp+rename, no lock. Two concurrent `validate.py`
runs — routine here, with three worktree slots and `gate_precheck` — can interleave such that
P2's write, made from a snapshot taken before P1's eviction, **resurrects an entry P1 evicted
on a FAIL**. The window is narrow (two file ops, compute already done), and a torn read falls
through to `JSONDecodeError → {}` → recompute, which is the safe direction. But guard 3's
promise ("a FAIL actively evicts… must not leave a stale green key behind") is not true under
concurrency, and the docstring states it unconditionally. Temp-file + `os.replace`, and an
advisory lock or a per-check entry file, both close it.

### R1-MIN3 — `_CAPTION_RE` cannot handle a nested brace

`scripts/validation/_tex.py:92`: `\\caption\{[^}]*\}`. A caption containing any group
(`\caption{Foo \textbf{bar}, 1.5 nK}`) is stripped only to the first `}`, so the tail is
scanned. The direction is safe (over-count → louder), and the check is ratcheted at
116/116 so an over-count fails rather than hides. But the docstring at `:98-105` presents the
caption exclusion as clean, and the identical pattern now feeds **two** subsystems
(`numerical_literals` and P2 Gate 9) whose agreement `readiness_verdicts_agree` asserts — so an
imprecision here is imprecision in both, by construction.

### R1-MIN4 — `validate.py`'s module docstring still describes the pre-split world

`scripts/validate.py:32-43` — *"Each check is a function decorated with `@register_check`. To
add a new check: …"* — with no mention of `_CANONICAL_ORDER`, which is now mandatory (a check
registered without a declared position **raises** at `:196-200`). The most likely next edit to
this file is "add a check", and the instructions for doing so are wrong by omission. `:53-54`
("if `lake` is on PATH, runs `lake build` … If not available, skips gracefully with a warning")
is also now the exact behaviour R1-MAJ1 is about, described as a feature.

---

## 5. What I attacked and could NOT break (recorded so it is not re-attacked)

* **`_CANONICAL_ORDER` / H3.** 59 declared, 59 registered, 0 duplicates, applied at
  `validate.py:515` after the last import — and `test_validate_registry_contract.py` asserts the
  *position* structurally, which is the only way to see it while the tail is coincidentally
  correct. `test_names_are_unique` closes the duplicate-registration hole. Clean.
* **H5.** `rg` over `scripts/` finds every flag read as `_cfg.<FLAG>`; the only
  `from validation._config import <FLAG>` strings in the tree are the ❌ examples inside
  `_config.py`'s own docstring and the assertion message in
  `test_validate_flag_propagation.py:286`. Clean.
* **H4.** `validate_helpers.load_lean_deps()` raises; every call site keeps its own verdict;
  the divergence is frozen in `test_cannot_measure_baseline.py` rather than erased. Correct
  application of the policy line, and `ensure_lean_deps_fresh` (`validate_helpers.py:108-161`)
  correctly scopes itself to full runs so the commit gate cannot trigger ExtractDeps.
* **`except Exception` vs `SystemExit`.** `atlas_view.load_lean_deps_file` is the only library
  offender and is fixed (`atlas_view.py:278-321`); `rg` finds no other `sys.exit`/`SystemExit`
  outside a `__main__` guard in any module a check imports (`build_graph`, `bundle_readiness`,
  `readiness_gates`, `update_counts`, `render_tracked_hypotheses`, `extract_lean_deps`).
* **Verdicts computed then discarded.** AST scan of `scripts/validation/**` for a tail
  `return CheckResult(passed=True)` in a function that also binds `ok`/`passed`/`failed`/… → **0
  hits**. The three known instances (`paper_latex_compiles`, `readiness_submission_gate`,
  `bibitem_title_primary_source`) are all genuinely repaired, and I confirmed both of the first
  two now go **red on live data** (`paper_latex_compiles`: D3, 2 fatal, rc=1;
  `readiness_submission_gate`: 0 green / 3 yellow / 61 red).
* **Duplicated helpers / seams that leak.** AST scan: no function name defined in >1 check
  module (bar a nested local `check`), **0** byte-identical bodies across modules, **0**
  identical compiled regex patterns across modules. The QI-02 merges (`NUMERICAL_LITERAL_RE`,
  `is_native_decide_axiom`, `_SEVERITY_DECL_MAP`, `unresolved_aristotle_keys`) all landed with a
  single owner in a module that imports nothing from the suite, so no cycle is possible.
* **Dead code.** `SEVERITY_VALUES`, `_TEST_MODULE_ALIASES`, `_LEAN_REF_NON_NAMES`,
  `MEMO_SCHEMA`, `tree_fingerprint`, `_ROSTER_LITERAL_THRESHOLD`, `_AXIOM_HIST_WINDOW`,
  `_PHYSLIB_DIR`, `CLAIM_CLUSTERS_PATH` — every one has a live consumer. No registered-but-
  unreachable check; no flag nothing reads.
* **Ratchet headroom.** Measured live: `count_literals` 107/107, `numerical_literals` 116/116,
  `theorems` unresolved 14/14, `prose_theorem_reference_coverage` legacy 81/81,
  `BIBITEM_TITLE_DRIFT_CEILING` 7/7, `CI_MIN_CHECKS_RUN` 55/55. Zero headroom everywhere — the
  house idiom applied correctly. No off-by-one found.
* **Module split coherence.** 12 modules, 398–1024 lines, each readable in one pass. The two
  placements that could be questioned are both documented and defensible: `theorems` in
  `lean_toolchain` ("the migration table never assigned it and it is a registry-count check"),
  and the `lean_substrate` / `lean_toolchain` split on substance-vs-trust-surface — which the
  zero shared helpers between them confirms rather than asserts.
* **Test suite.** `tests/test_validation_memo.py test_validate_public_surface.py
  test_validate_registry_contract.py test_validate_flag_propagation.py test_ci_mode.py
  test_cannot_measure_baseline.py test_gate_precheck.py test_always_pass_dispositions.py`
  → **150 passed in 3.99s**.

---

## 6. Reconciliation with pass 1

| pass-1 id | status after this review |
|---|---|
| `R3-I5` (BinOp path-alias gap) | **RE-FILED, survives** → R1-I1, now with a measured 5-site count |
| `R1-I4` / `R3-M4` (`_iter_test_functions` double-mints) | **CONFIRMED** → R1-MIN1. The reviewers are right and the on-disk summary is wrong; 0 live sites today |
| `R4-I2` (`paper_latex_compiles` unreachable) | **closed correctly** — `gate_precheck s13` passes `--force-latex`, the slow gate is gone, and the check now genuinely fails on D3 |
| `R5-C1` (no CI) | **closed with a caveat** — the mode exists and is tested, but its central guard is R1-MAJ2 |
| `R3-C2` (QI-30 criterion swept to 4 of 59) | **partially reopened** — the two new memoized checks are seeded in production for their *file* inputs but not for the toolchain-absent path (R1-MAJ1) |

---

## 7. Verdict — safe to merge to `main`?

### **YES WITH FIXES**

**Merge blockers (this branch makes something worse, or ships a guard that cannot fire):**

* **R1-MAJ1** — a *cannot-measure* PASS is persisted and replayed on the Invariant #15 axiom
  backstop. New on this branch. Fix is a few lines in `_memo.memoized` plus one production-
  seeded test.
* **R1-MAJ2** — the `--ci` coverage floor cannot fire for the only cause it names, and its test
  seeds a defect the production artifact cannot exhibit. New on this branch. Either fix the
  measurement or rewrite the docstring to claim only what it does — but not ship it as written,
  because the next person to wire CI will trust the text.
* **R1-MAJ3** — one line (`inspect.getmodule`) plus a docstring correction. Cheap enough that
  there is no reason to defer it.

Everything else in §3–§4 is fix-in-flight or follow-up; none of it makes the branch worse than
`main`.

**Explicitly NOT merge blockers (submission blockers → ADR-010):**

`paper_latex_compiles` failing on D3 (2 fatal errors) and `readiness_submission_gate` reporting
0 green / 3 yellow / 61 red mean `validate.py` now exits 1 on a clean tree, and
`gate_precheck s13` / `submission` will fail until the corpus is repaired. **That is the branch
working.** Both checks previously returned `passed=True` while measuring the same reality — one
by discarding its verdict, one by skipping by default. Trading a false green for a truthful red
is the entire point, and the red belongs to the papers, not to this diff.

**Net assessment.** The structure is the strongest thing here: the split is clean, the seams
hold, the ordering hazard is genuinely decoupled, and the repairs to `build_graph`,
`readiness_gates`, `bundle_readiness` and `atlas_view` are each correct and each testable.
The weakness is concentrated in the one component added last and reviewed least — and it fails
in the branch's own signature way, which is the most useful thing I can report about it.
