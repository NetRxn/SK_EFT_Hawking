# R4 — enforcement efficacy (PR review, pass 2)

**Branch:** `infra/adr-009-validation-modularization` · **Base:** `main` @ `c2b597e1`
**Lens:** for each of the 59 registered checks — *can it actually fail, in production, on a real defect?*
**Reviewer id prefix:** `R4-`

---

## 0. Method, and one hazard that affected the whole round

Per check: (1) what defect it claims; (2) trace every `return CheckResult` and every
`passed=` computation; (3) measure the population each leg iterates, in the production
tree; (4) seed the defect where cheap and observe whether the check fires.

**Measurement hazard — the working tree was mutated by concurrent reviewers throughout
this run.** At three separate points `git status --short` showed check bodies stubbed to
`return _CRM(passed=True, details=[])` (`lean_toolchain.check_theorem_count`,
`lean_toolchain.check_lean_source`, `papers_prose.check_paper_provenance`) and seeded
`\texttt{}` refs in `papers/D1/paper_draft.tex` and `papers/paper11_quantum_group/paper_draft.tex`.
Those are other reviewers' mutation probes, not production code. **Every static claim in
this report was therefore re-derived from `git show HEAD:<path>`, not the working tree.**
I wrote nothing to the repo outside this file; my own seeding was done in-process
(monkeypatching a production function's inputs and calling the production body) or against
a `/tmp` copy. Six reviewers seeding a shared checkout concurrently is a real risk to the
integrity of pass 2's numbers — flagging it as a process finding (`R4-MIN4`).

Three fan-out tracers covered `citations.py`/`graph_atlas.py`, `reviews.py`/`prose_lean_refs.py`
and `freshness.py`/`notebooks.py`/`lean_substrate.py`. Their load-bearing counts were
independently re-measured by me before filing (see each finding's "verified" line).

---

## 1. Headline

**The branch's new memoization surface can cache a PASS that measured nothing, and I proved
it end to end on the production check.** That is not a hypothetical: `axiom_closure_allowlist`
has six return paths that yield `passed=True` when it could not measure, `_memo`'s guard 3
("only PASS is cached") treats all six as cacheable, and the key contains nothing that
distinguishes "measured clean" from "toolchain absent".

Beyond that, the enforcement picture is: of 59 registered checks, **11 cannot fail on the
defect they advertise** and a further **24 can fail only on a narrowed, ratcheted or
strict-mode-only sliver** of it. Five of the eleven are `--strict`-only, and `--strict` has one
manual caller — so in the routine run that gates every wave they contribute nothing.

The three checks I most expected to be load-bearing and found hollow:
`bundle_consistency` (implements none of its three advertised comparisons),
`tables_fresh` / `claim_clusters_fresh` (a corrupted production table cell passes), and
`bundle_figure_integrity` (a dead derivation block silently substitutes a hand-typed roster
covering 5.6 % of shipped figures).

---

## 1a. Finding index — **32 findings: 0 CRITICAL, 7 MAJOR, 21 IMPORTANT, 4 MINOR**

| id | severity | one line |
|---|---|---|
| `R4-MAJ1` | MAJOR | the memo caches a cannot-measure PASS for `axiom_closure_allowlist` (proven end to end) |
| `R4-MAJ2` | MAJOR | `bundle_consistency` implements none of its three advertised comparisons |
| `R4-MAJ3` | MAJOR | `bundle_figure_integrity`'s registry derivation is dead code; 7 of 124 figures checked |
| `R4-MAJ4` | MAJOR | `review_docs_mint_findings` evades on capitalisation and on the substring `pass`; 2 live BLOCKERs dropped |
| `R4-MAJ5` | MAJOR | Invariant #8 asserted over 206 parameters from 37 measurements; `graph_integrity` reuses the same narrowing |
| `R4-MAJ6` | MAJOR | `tables_fresh` / `claim_clusters_fresh` cannot see content drift; the R4-I7 fix re-tests mtime |
| `R4-MAJ7` | MAJOR | `counts_fresh` wedges permanently red on an empty `git diff` and auto-heals the real defect |
| `R4-I1` | IMPORTANT | the LaTeX cache is not bypassed by `--strict`/`--no-memo`; key omits body source and TeX toolchain |
| `R4-I2` | IMPORTANT | the cannot-measure ratchet misses 24 of 48 sites and a whole third shape |
| `R4-I3` | IMPORTANT | `cross_path_consistency`: bit-identical legs; all-skip → `passed=True, details=[]` |
| `R4-I4` | IMPORTANT | `readiness_verdicts_agree` reverse leg dead by construction (0 of 704 gates blocked at P2) |
| `R4-I5` | IMPORTANT | `readiness_verdicts_agree` counts a GREEN bundle as "heatmap-RED cross-checked" |
| `R4-I6` | IMPORTANT | `formula_grounding`: pass-1 "dead legs" NOT reproduced; residual = 2-of-522 grounding-kind coverage |
| `R4-I7` | IMPORTANT | `numerical`'s hand-maintained `expected` dict with a silent `continue` |
| `R4-I8` | IMPORTANT | `theorem_name_embedded_citations` cannot fail outside `--strict`, population 1 |
| `R4-I9` | IMPORTANT | `bibitem_title_primary_source` cannot fail in default mode; fabricated titles never fail |
| `R4-I10` | IMPORTANT | three null registry fields opt a bibkey out of all three citation checks (28 % already exempt) |
| `R4-I11` | IMPORTANT | citation cache-agreement measures 37 of 652, reported as "Every … agrees" |
| `R4-I12` | IMPORTANT | 3 of `atlas_integrity`'s 5 legs dead (one tautological, one empty, one unreachable) |
| `R4-I13` | IMPORTANT | `graph_integrity` fails open on ImportError; hand-written 21-code roster fallback |
| `R4-I14` | IMPORTANT | `recurrence_reopens_closures` threshold 1.7× above corpus max; `NOT FIXED` suppresses |
| `R4-I15` | IMPORTANT | `review_severity_declared`: 5 of 273 docs, aggregate count not per-finding |
| `R4-I16` | IMPORTANT | `prose_theorem_reference_coverage`: 36-entry prefix list waves 43 tokens through unchecked |
| `R4-I17` | IMPORTANT | `accepted_findings_carry_rationale` is length-only with a 2× dead band |
| `R4-I18` | IMPORTANT | `notebook_exec` runs 0 notebooks today; a cell tag turns a raise into "executed successfully" |
| `R4-I19` | IMPORTANT | `bundle_source_freshness` unfailable outside `--strict`, and **writes git-tracked files** |
| `R4-I20` | IMPORTANT | `tracked_hypothesis_ledger` blind to a hypothesis added by the change under review |
| `R4-I21` | IMPORTANT | three name-list guards cover 1.6 % / 1.6 % / 4.8 % of their canonical populations |
| `R4-I22` | IMPORTANT | `placeholder_not_cited` / `disclosure_consistency` suppressed by ordinary prose; ~9 and 0 live sites |
| `R4-I23` | IMPORTANT | `inventory_index_autogen_fresh` loses its own scope silently |
| `R4-I24` | IMPORTANT | `notebook_stored_outputs_current` covers 2 of 43 shipped notebooks |
| `R4-I25` | IMPORTANT | `viz_consistency` cannot fail; 25 live warnings, green |
| `R4-MIN1`–`R4-MIN4` | MINOR | three by-design never-fail checks in the headline count; two stale in-code claims; concurrent-seeding process hazard |

*(`R4-I25` and `R4-MIN1`–`4` bring the IMPORTANT count to 21 and MINOR to 4; total 32.)*

---

## 2. Findings

Severity vocabulary per the brief: `CRITICAL` · `MAJOR` · `IMPORTANT` · `MINOR`.

---

### `R4-MAJ1` — MAJOR — the memo caches a **cannot-measure** PASS, and the key cannot tell it apart from a measured one

**File:** `scripts/validation/_memo.py:265-279` (guard 3) × `scripts/validation/checks/lean_toolchain.py:426-437, 472-515`

**Claims.** `_memo.py:43-45`: *"**Only PASS is cached.** A failing check re-runs every time, so
a red check can never be memoized away."* And `lean_toolchain.py:469-470`: *"The key names
every input that can move the verdict."*

**What it actually does.** `check_axiom_closure_allowlist` has **six** return paths that yield
`passed=True` without measuring anything:

| line | condition | detail text |
|---|---|---|
| 474 | `not lake_bin` | `SKIPPED — lake not found` |
| 480 | `not audit_src.exists()` | `SKIPPED — AxiomAudit.lean not found` |
| 498 | `subprocess.TimeoutExpired` | `SKIPPED — AxiomAudit timed out` |
| 501 | any `Exception` | `SKIPPED — <exc>` |
| **505** | **`result.returncode != 0`** | `SKIPPED — AxiomAudit exited N` |
| 513 | `json.JSONDecodeError` | `SKIPPED — could not parse output` |

`memoized()` records any `result.passed` truthy verdict. The key is
`lean_source_fingerprint ∥ toolchain_pin_fingerprint ∥ files_fingerprint([constants.py, update_counts.py]) ∥ source_fingerprint(body)`.
**None of those covers toolchain availability or Lean *build state*** — and the check's
measurement is entirely a function of the built environment (`AxiomAudit` reads the compiled
env, not the sources). `lean_source_fingerprint` hashes `lean/SKEFTHawking/**/*.lean`; it does
not hash `lean/.lake/build`.

**How I verified.** Drove the *production* registered check with a throwaway cache file:

```
STEP 1: lake unavailable (LAKE_PATH=/nonexistent/lake)
  passed= True  0.11s
   - axiom_audit_run True SKIPPED — [Errno 2] No such file or directory: '/nonexistent/lake'
  cache now: {"axiom_closure_allowlist": {"key": "667d2fcea758a94b4a42079a", "details": [[...SKIPPED...]]}}
STEP 2: lake restored (LAKE_PATH removed) -- same tree, same key?
  passed= True  0.07s
   - memo True SKIPPED (cached) — Lean sources, toolchain pins, AXIOM_METADATA unchanged
                                  since the last PASS; --no-memo (or --strict) re-measures
   - axiom_audit_run True SKIPPED — [Errno 2] No such file or directory: '/nonexistent/lake'
```

The poisoned key is `667d2fcea758a94b4a42079a` — **byte-identical to the key under which the
developer's live cache (`docs/validation/.check_memo.json`) currently holds a real
measurement.** A poisoned entry is indistinguishable from a genuine one by key, by schema, or
by verdict; only the replayed `Detail` text differs, and nothing reads it.

**Realistic trigger, no adversary needed.** `rm -rf lean/.lake/build` is the project's own
documented "trusted clean baseline" step (CLAUDE.md). Any `validate.py` run between that and
the next successful `lake build` takes the `returncode != 0` path → PASS → cached. The next
run, on a fully-built tree, replays the skip in 0.07 s and reports the 145 s soundness gate
green. It stays green until someone edits a `.lean` file, a pin, `constants.py`,
`update_counts.py`, or the check body.

**Blast radius.** `axiom_closure_allowlist` is the Invariant #15 backstop — the only automated
check on the project's kernel-trust surface. `--strict` does bypass the memo, so the
submission gate re-measures; every routine run does not.

**Fix.** The memo must not cache a PASS whose provenance is "could not measure". Either
(a) convert the six SKIP paths to `passed=False` (the `theorems` / `native_decide_regression`
policy already adopted three lines away in the same file), or (b) have `memoized()` refuse to
store a result carrying a `SKIPPED` sentinel, or (c) fold a *measurement-reached* flag into
`CheckResult` and gate storage on it.

---

### `R4-MAJ2` — MAJOR — `bundle_consistency` implements **none** of the three comparisons it advertises

**File:** `scripts/validation/checks/bundles_readiness.py:613-733`

**Claims.** Registration string: *"Cross-bundle clusters' member sentences agree on numerical
content across bundle boundaries."* Docstring: member sentences must agree on
(i) same primary-source bibkey, (ii) same numerical value within ±2σ or 1 %, (iii) same Lean
theorem reference.

**What it actually does.** The body never opens a sentence, a bibkey, a value or a Lean name.
It reads `papers/cluster_bundle_index.json` and branches purely on the index's own
`match_kind` string:

* `"exact"` → `Detail(..., True, "normalized_hash guarantees identical content")` — the verdict
  is *asserted from the index field*, not measured;
* `"normalized"` → `Detail(..., True, ...)` "manual review recommended" — advisory;
* anything else → `Detail(..., False, "unknown match_kind")`.

So the only reachable failures are: index file missing (`passed=False, error=...`),
index unparseable, or a cluster carrying an unrecognised `match_kind` literal. **There is no
code path on which a numerical disagreement between two bundles can turn this check red.**

**How I verified.**

```
$ uv run --no-sync python -c "... json.loads(papers/cluster_bundle_index.json) ..."
clusters: 3   cluster_count field: 3   cross_bundle: 2
match_kind of cross-bundle: Counter({'exact': 2})
```

Both live cross-bundle clusters take the no-op `exact` branch. `grep` over the check body for
`sigma|bibkey|tolerance|value` → no matches.

**Blast radius.** Cross-bundle numerical agreement is the failure class that the flagship-vs-deep
bundle architecture makes structurally likely; this is the only check nominally guarding it.
Empty population (2) *and* an empty implementation.

---

### `R4-MAJ3` — MAJOR — `bundle_figure_integrity`'s registry derivation is **dead code**; production always uses the hand-maintained roster the comment says it exists to avoid

**File:** `scripts/validation/checks/bundles_readiness.py:104-134`

**Claims.** In-body comment: *"Derived from FIGURE_REGISTRY rather than hand-maintained: a
hand-listed roster means the NEXT bundle figure ships unguarded… The literal below is the
fallback if the registry is unreadable."*

**What it actually does.** The derivation loads `review_figures.py` via
`importlib.util.spec_from_file_location("_review_figures", ...)` + `exec_module`, without
registering the module in `sys.modules`. `review_figures.py` uses `@dataclass`, and
`dataclasses._is_type` dereferences `sys.modules.get(cls.__module__).__dict__` — which is
`None`. **Every run raises `AttributeError` and falls into the hardcoded fallback.**

**How I verified.** Ran the check's own lines 110-124 verbatim:

```
DERIVATION FAILED -> AttributeError 'NoneType' object has no attribute '__dict__'
=> production uses the HARDCODED fallback SPECS (7 figures, D11+D12 only)
registry (imported properly): total specs 137   d11/d12: {'D11': 4, 'D12': 3}
shipped bundle PNGs: 124  {'D11': 4, 'D12': 3, 'D5': 7, 'D8': 3, 'D9': 4, 'E1': 2,
  'E2': 4, 'I1': 6, 'I2': 5, 'L1': 1, 'L2': 2, 'L3': 1, ... 50 dirs}
```

Three compounding narrowings:
1. the derivation is dead, so the roster is hand-maintained after all;
2. even working, `fs.name.startswith(("d11_","d12_"))` keeps 7 of 137 registry specs;
3. **7 of 124 shipped bundle PNGs (5.6 %) are checked.** D5, D8, D9, E1, E2, I1, I2, L1–L3 all
   ship figures that are never checked for legibility or drift.

**And guarantee #1 cannot fail at all.** The "byte-identical to a fresh render" comparison emits
`Detail(f"drift:{bundle}:{png}", True, ..., warning=True)` (line 182-187) — `passed=True`. Only
the 8 pt legibility floor contributes to the verdict.

**Blast radius.** The docstring names this as the binding for a checker that "had **zero
consumers repo-wide** — it was honest but not binding". It is binding for 5.6 % of the corpus.

---

### `R4-MAJ4` — MAJOR — `review_docs_mint_findings` evades on capitalisation and on the substring `pass`; two live BLOCKERs are already dropped

**File:** `scripts/validation/checks/reviews.py:446-448` (`_SEVERITY_HEADING`), `:455` (`_RESOLVED_HEADING`)

**Claims.** *"Every bundle Stage-13 review document mints at least one ReviewFinding node"* —
written for the round-9 BLOCKER 8.2 class, *"a review declaring four BLOCKERs minted zero nodes"*.

**What it actually does.**
* `_SEVERITY_HEADING` is compiled with `re.M` **only — no `re.I`** (verified against `HEAD`), while
  `_RESOLVED_HEADING` one line below *is* `re.I`. A heading reading `### Findings — a Blocker
  defect …` is not seen as a finding heading at all, and the document is not even counted as
  `checked`.
* `_RESOLVED_HEADING = re.compile(r'PASS|RESOLVED|resolved', re.I)` has **no word boundaries**, so
  `bypass`, `bypassable`, `passes`, `surpassed`, `compass` inside a heading reclassify a real
  finding as a resolution note.

**How I verified** (fan-out tracer, production seeds into real review docs, reverted):

```
### Findings — a CRITICAL defect: the tetrad closure guard is bypassable, see 🔴 BLOCKER
  ✓ PASS  review_docs_mint_findings   (135 documents checked — unchanged)
### Findings — a CRITICAL defect in the tetrad bound that this document declares
  ✗ FAIL — 136 document(s) checked; 1 mint zero
### Findings — a Blocker defect in the tetrad bound that this document declares
  ✓ PASS  — 135 document(s) checked; 0 mint zero
```

Live corpus scan: of 1,222 severity-labelled headings, 4 are dropped by `_RESOLVED_HEADING`, **2
of them by a substring match inside another word — and both are real, unresolved BLOCKERs**:

```
### 8.2 — 🔴 BLOCKER — (3b) opened a new blocking-closure bypass: …
### 8.1 — 🔴 BLOCKER — the round-8 blocking-closure guard is bypassable two ways, …
```

Scope: 118 of 273 review documents already mint zero findings and are skipped; any of them can
acquire a title-case blocker heading invisibly.

**Fix.** `re.I` on `_SEVERITY_HEADING`; `\b(PASS(ED|ES)?|RESOLVED)\b` and non-greedy `.*?` on
`_RESOLVED_HEADING`.

---

### `R4-MAJ5` — MAJOR — Invariant #8 is asserted over 206 parameters on the strength of 37 measurements, and `graph_integrity` re-uses the *same* narrowed measurement

**File:** `scripts/validation/checks/citations.py:153-184` (skip at `:161`), `scripts/build_graph.py:287,310`, `scripts/validation/checks/graph_atlas.py:333`

**Claims.** `parameter_provenance` emits `Detail("value_consistency", True, "All provenance
values match code")`. `graph_integrity` gates on `conflicts == 0 and orphan_claims == 0`.

**What it actually does.** `_lookup_provenance_value` resolves only 4 hardcoded fundamentals
plus `group.key` splits landing in `ATOMS` / `EXPERIMENTS` / `POLARITON_PLATFORMS`. Everything
else returns `None` and is discarded by `if actual is not None:` — **no counter, no warning, no
detail**. And `graph_integrity`'s `conflicts` metric is produced by
`build_graph.extract_parameter_nodes` through the *same* `_lookup_code_value is None → skip`.
Two checks, one measurement, narrowed identically.

**How I verified (my own re-measurement, not inherited):**

```
$ uv run --no-sync python  # production _lookup_provenance_value over the live registry
entries: 206 | null value: 0 | value-compared: 37 | silently skipped: 169
skipped sample: ['MATHER_1982_GRADIENT_REDUCTION', 'Steinhauer.T_H_measured',
 'V_FERMI_GRAPHENE', 'ALPHA_GRAPHENE_HBN', 'Dean_bilayer_nozzle.c_s', ...]
```

Tracer seeded a 3.7× value forgery on `MATHER_1982_GRADIENT_REDUCTION` in-memory →
`passed=True`, no detail mentions it.

A provenance entry naming a parameter that does not exist in the codebase is invisible to
**both** directions: leg 1 walks code → registry, leg 4 walks registry → code but discards
non-resolving keys. 169 entries are currently in that state and may assert any value.

**Blast radius.** Invariant #8 gates published experimental numbers. `graph_integrity`
additionally computes 21 metrics and gates on 2; `orphans=37539`, `ungrounded=243`,
`broken_chains=36`, `missing_provenance=47` are warnings, and `pg_sync=divergent` /
`sentence_chain_incomplete=144` are computed and never surfaced at all.

---

### `R4-I1` — IMPORTANT — the `paper_latex_compiles` cache is **not** bypassed by `--strict`, `--no-memo`, or the test-suite env var

**File:** `scripts/validation/checks/papers_prose.py:508, 524, 562` · `scripts/validate.py:572-576` · `scripts/validation/_config.py:66-71`

**Claims.** `_memo.memoized`'s docstring: *"`--strict` implies it, and that is a deliberate
asymmetry… `--strict` is the Paper Submission Gate (Invariant #12), the one irreversible
consumer… so the Paper Submission Gate never reads a cached verdict."* And
`SKEFT_VALIDATION_NO_MEMO=1` is set suite-wide by `tests/conftest.py:26` for exactly the
QI-30 fixture-poisoning reason.

**What it actually does.** `paper_latex_compiles` does not use `_memo` at all — it rolls its own
`papers/.latex_compile_cache.json`, gated solely on `_cfg.FORCE_LATEX`. `validate.main()` sets
`_cfg.FORCE_LATEX = args.force_latex` and nothing else touches it:

```
$ grep -n "FORCE_LATEX\|NO_MEMO\|STRICT_MODE" scripts/validate.py
573:    _cfg.STRICT_MODE = args.strict
575:    _cfg.FORCE_LATEX = args.force_latex
576:    _cfg.NO_MEMO = args.no_memo
```

So `validate.py --strict` reads a cached LaTeX verdict, `--no-memo` does not bypass it, and
`SKEFT_VALIDATION_NO_MEMO=1` does not either. Two additional key gaps versus `_memo`'s own
guards: the cache key has **no `source_fingerprint`** (editing `_LATEX_FATAL_RE` or the check
body leaves every entry valid — `_memo` guard 1 is the one *"that makes the others recoverable"*),
and **no TeX-toolchain fingerprint** (a `tlmgr` update or a removed `.sty` changes the compile
outcome with no key movement — the exact hazard `toolchain_pin_fingerprint` exists for on the
Lean side).

**How I verified.** Flag wiring above; closure measured over all 21 drafts —
`total closure files 100, nonexistent 0` (so the closure itself is sound for on-disk inputs:
every `\includegraphics` carries an explicit extension and both `\bibliography{}` users have a
sibling `.bib`). The gap is the *out-of-closure* inputs and the missing bypass.

Detection itself works: I compiled a production D1 copy with one seeded
`\thisCommandDoesNotExist` in `/tmp` and the production regex fired —
`production _LATEX_FATAL_RE matches: 3`.

**Blast radius.** The submission gate's most submission-relevant check is the one check the
submission gate does not force to re-measure.

---

### `R4-I2` — IMPORTANT — the cannot-measure ratchet bounds only the population its *syntax* happens to match; **24 of 48** literal `passed=True` returns are invisible to it

**File:** `tests/test_cannot_measure_baseline.py:82-84, 126-164`

**Claims.** *"the honest move is to make the population explicit and bounded: every entry is a
decision on the record, and a NEW silent PASS fails this test."* Docstring: *"MEASURED
2026-08-04 across the 59 checks — 60 cannot-measure return sites: 35 FAIL and 25 PASS."*

**What it actually does.** The scan recognises a cannot-measure branch only if the `return` is
inside an `except` handler, or inside an `if` **whose test syntactically contains a call to one
of six names** (`exists`, `is_file`, `is_dir`, `lean_deps_present`, `counts_present`, `which`).
Two whole shapes fall outside:

* a guard that stores the probe in a local first — `pdflatex = shutil.which(...)` then
  `if pdflatex is None:` — is invisible while `if shutil.which(...) is None:` is caught;
* a guard on a *result* rather than a *presence* — `if result.returncode != 0`, `if not drafts`,
  `if not cross_bundle_clusters`, `if not lake_bin`.

**How I verified.** AST scan over `git show HEAD:` copies of all 13 check modules:

```
HEAD: literal passed=True returns in registered checks: 48
  seen by the ratchet: 24   INVISIBLE: 24
   GUARDED-BUT-UNSEEN: axiom_closure_allowlist   474 -> not lake_bin
   GUARDED-BUT-UNSEEN: axiom_closure_allowlist   505 -> result.returncode != 0
   GUARDED-BUT-UNSEEN: bundle_consistency        681 -> not cross_bundle_clusters
   GUARDED-BUT-UNSEEN: bundle_figure_integrity    99 -> not hasattr(viz,'bundle_figure_typeset_pt')
   GUARDED-BUT-UNSEEN: bundle_source_freshness   644 -> not findings
   GUARDED-BUT-UNSEEN: inventory_index_autogen_fresh 727 -> stale
   GUARDED-BUT-UNSEEN: lean_build                364 -> not lake_bin
   GUARDED-BUT-UNSEEN: lean_build                379 -> not has_lakefile
   GUARDED-BUT-UNSEEN: paper_latex_compiles      497 -> pdflatex is None
   GUARDED-BUT-UNSEEN: paper_toolchain_pin_drift 934 -> live_ver is None or live_rev is None
   GUARDED-BUT-UNSEEN: paper_toolchain_pin_drift 942 -> not drafts
   GUARDED-BUT-UNSEEN: tracked_hypotheses_fresh  589 -> old == new
```

**Nine of those twelve are genuine cannot-measure or empty-population PASSes** —
including both of `axiom_closure_allowlist`'s toolchain paths, i.e. the two that `R4-MAJ1`
turns into a durable cached green.

A **third shape is invisible by construction**: an empty population reached with no `return`
site at all (`all([]) is True`, or an `all_pass = True` surviving a `for` over an empty glob).
The scanner cannot see it even in principle. Live instances found:

* `cross_path_consistency` — both legs skipped → `details = []`, `passed=True` (`R4-I3`);
* `_tables_is_stale`'s `if not specs: return False` (`freshness.py:228`) → `tables_fresh` PASS;
* `_claim_clusters_is_stale`'s `if not v2_files: return False` (`freshness.py:312`) → PASS;
* `all_pass = True` surviving an empty `for … in glob()` in `notebooks`, `viz_consistency`,
  `notebook_exec`, `proxy_body_audit`;
* the `not any_fail` fall-through in `placeholder_not_cited` and `disclosure_consistency`.

The docstring claims the population is *"explicit and **bounded**"* and that *"a NEW silent PASS
fails this test"*. It bounds the exception/presence-guard population only. Adding a third branch
kind — a `for` over a `glob`/comprehension whose empty case reaches a `passed=True` — would make
the ratchet match its own claim. Note the team already recognises this class: the empty-scope
**FAIL** at `freshness.py:427` (`notebook_stored_outputs_current`) is exactly the right fix,
applied once.

This **re-files and sharpens pass-1 `R3-I9`** ("the eight always-pass checks population is a
syntactic lower bound"), now with the count and the specific 12 sites.

**Blast radius.** The ratchet is the branch's stated answer to ADR-009 §Deferred item 4. It is
a real ratchet over half the population, presented as a bound over all of it.

---

### `R4-I3` — IMPORTANT — `cross_path_consistency`: two legs, **bit-identical** verdicts, and a silent all-skip that returns PASS with zero details

**Re-files pass-1 `R4-I1`, whose mechanism the register recorded as "not reproduced".**
**File:** `scripts/validation/checks/physics.py:732-790`

**What the register said.** Leg 2 is leg 1 scaled by 2 on both sides, *"and the two sides differ
in the 6th significant digit… Leg 2 therefore does constrain `decoherence_parameter`'s factor
of 2, which leg 1 does not."* That narrow point is correct and I do not dispute it.

**What I measured, which the register did not.** The two legs' *relative differences* — the
quantities actually compared against the 0.5 % tolerance — are **bit-identical**:

```
ratio dk_spec/dd_spec = 2.0    dk_form/dd_direct = 2.0
rel_diff leg1 = 4.127685699545415e-06
rel_diff leg2 = 4.127685699545415e-06
BIT-IDENTICAL: True
```

`spectrum_summary`'s `delta_k_at_T_H` is exactly `2 × delta_diss_at_T_H`, and
`decoherence_parameter` is exactly `2Γ/κ`. So leg 2 contributes exactly one bit of information
beyond leg 1 — the integer 2 — and cannot fail independently for any drift in the numerical
path. A check registered as *"different code paths agree"* runs one independent comparison.

**And the stronger defect, unreported in pass 1:** both legs are wrapped in
`if X > 0 and Y > 0:`. When the guard fails the leg is skipped with **no `Detail` emitted at
all**, and the terminal `return CheckResult(passed=all_pass, details=details)` returns a bare
green. Demonstrated on the production check by making the dissipation vanish:

```
$ # sp.spectrum_summary patched to return delta_diss_at_T_H = delta_k_at_T_H = 0.0
passed = True | n details = 0 | details: []
```

This is the purest instance of the branch's target defect in the suite: a PASS with an *empty*
report. It is invisible to `test_cannot_measure_baseline` (no `return` site in the guard).

**Also confirmed:** the register's re-filed point stands — line 754 inlines
`gamma_eff * (T_H/c_s)**2 / kappa` instead of calling the canonical `formulas.py` entry point,
so the check registered to *"catch duplicate implementations that drift apart"* introduces a
third one. Still ⬜ open.

---

### `R4-I4` — IMPORTANT — `readiness_verdicts_agree`'s reverse leg is **dead by construction**, not merely empty

**Re-files pass-1 `R4-I8` (⬜ open). Mechanism and measurement now supplied.**
**File:** `scripts/validation/checks/bundles_readiness.py:422-434` × `scripts/bundle_readiness.py:383-392`

**The leg.** `if readiness != 'GREEN': continue` … `if bundle in blocked_at_gate: DISAGREE`.

**Why it cannot fire.** `aggregate_by_bundle` — the producer of `readiness` — already demotes
GREEN → YELLOW whenever `blocked_p1.get(b)` is non-empty:

```python
gate_block = sorted(blocked_p1.get(b, []))
if readiness == "GREEN" and gate_block:
    readiness = "YELLOW"
```

So `readiness == 'GREEN'` ⟹ no blocked **P1** gate. The check's `blocked_at_gate` is built
without a priority filter, so it would additionally catch a blocked **P2** gate — except that
**no gate anywhere in the graph is ever blocked at priority 2**:

```
ReadinessGate nodes: 704
state x priority: Counter({('passed',1):417, ('passed',2):102, ('blocked',1):96,
                           ('open',1):49, ('needs-recheck',2):33, ('needs-recheck',1):7})
papers with blocked P2 (and no P1): []
bundles: 21   readiness: Counter({'RED':16, 'YELLOW':4, 'GREEN':1})
GREEN bundles: ['D9']
REVERSE-LEG reachable set (GREEN and in blocked_at_gate): []
```

`blocked_at_gate ⊆ blocked_p1` exactly. `FixPropagation` is declared `priority=2` at
`readiness_gates.py:689` but *escalates to P1 when blocked*, so `('blocked', 2)` is
unproducible by any current evaluator. The leg is unreachable, not merely unexercised — and
its own failure message hardcodes "P1 gate(s) … are blocked", i.e. it was written for a case
its producer forecloses.

**Blast radius.** The leg exists because *"D6 rendered GREEN in `BUNDLE_READINESS_HEATMAP.md`
with NarrativeGrounding blocked"*. That defect was fixed **in the producer**
(`_blocked_p1_gates_by_paper`, 2026-07-31/08-04). The cross-check added afterwards can no
longer observe a regression in that producer, because it consumes the producer's own output.
An independent reverse check would have to compare the heatmap against the raw gate nodes
*before* the demotion.

---

### `R4-I5` — IMPORTANT — `readiness_verdicts_agree` reports GREEN bundles as "heatmap-RED cross-checked"

**File:** `scripts/validation/checks/bundles_readiness.py:434, 470-473`

The reverse loop does `checked += 1` for every GREEN bundle that is not gate-blocked; the
summary then reads `f"{checked} heatmap-RED bundles cross-checked"`. Live run:

```
✓ summary — 17 heatmap-RED bundles cross-checked, 0 disagreement(s)
   (followed by exactly 16 RED bundle details)
```

Measured: 16 RED + 1 GREEN (D9) = 17. The report overstates its own coverage by counting a leg
that (per `R4-I4`) can never contribute a verdict. Small, but it is the report-inflation shape
this audit exists to remove.

---

### `R4-I6` — IMPORTANT — `formula_grounding`: pass-1's "two legs are dead" does **not** reproduce; the residual is a near-empty population

**Re-verification of pass-1 `R4-I6` (⬜ open) — result: NOT REPRODUCED as filed.**
**File:** `scripts/validation/checks/lean_statements.py:330-352, 358-401`

Both advertised legs **fire** when a production-shaped defect is seeded. I monkeypatched
`_parse_formula_lean_refs` (production function, production `lean_deps.json`, production
`PLACEHOLDER_LEAN_NAMES`) to add one real placeholder / one real reflexive declaration to the
ref set and called the production check body:

```
seeding placeholder ref: module_summary_marker | thin ref: three_gaps
  leg placeholder_grounded: passed=False fired=True  msg=formula grounded on a placeholder/True stub (Invariant #4)
  leg thin_grounded:        passed=False fired=True  msg=formula grounded on a reflexive/tautological theorem …
control (unseeded): True
```

They are **reachable but currently empty**:

```
refs: 522   resolve: 522
LEG placeholder_grounded hits: 0     (26 such declarations exist corpus-wide)
LEG thin_grounded hits:        0     (71 such declarations exist corpus-wide)
LEG B vacuous-wrapper refs:    1
FORMULA_GROUNDING_KIND entries: 2
```

**The residual finding, re-filed at lower severity:** the R-05 "grounding-kind honesty"
machinery (legs A/C, `lean_statements.py:381-401`) iterates `FORMULA_GROUNDING_KIND.items()` —
**2 entries against 522 refs (0.4 %)**. Leg B compensates only for the single vacuous-wrapper
shape (1 live ref). So the honest statement of what this check enforces today is
"all 522 refs resolve, and 2 of them have a declared grounding kind".

Recommend the register mark `R4-I6` **corrected**, not merely closed: "dead" was wrong, and a
future reader taking that at face value would delete a working guard.

---

### `R4-I7` — IMPORTANT — `numerical` carries a hand-maintained reference table parallel to `EXPERIMENTS`, with a silent `continue`

**File:** `scripts/validation/checks/physics.py:61-78`

`expected` is a literal dict of three platform names; the loop opens
`if name not in expected: continue`. A fourth experiment added to `constants.EXPERIMENTS` is
silently exempt from *"Experimental parameters match reference values"* — no detail, no warning,
no coverage number in the report.

```
get_all_experiments keys: ['Heidelberg','Steinhauer','Trento']
checked by `numerical`: all 3   SILENTLY SKIPPED: []
```

Coverage is 3/3 **today**; the defect is structural, and no test asserts
`set(expected) == set(get_all_experiments())`. Same shape as the `bundle_registry`
parallel-roster class this branch spent commits fixing elsewhere (`R1-I2`, `bundle_registry_consistency`).

---

### `R4-I8` — IMPORTANT — `theorem_name_embedded_citations` cannot fail outside `--strict`, over a population of **1**

**File:** `scripts/validation/checks/prose_lean_refs.py:830-832` (verified against `HEAD`)

```python
passed = True
if _cfg.STRICT_MODE and n_warn > 0:
    passed = False
```

`STRICT_MODE` defaults `False` and is set only by `--strict`. Population: 40,262 lean_deps
entries → 3 short names carry a year segment → 2 are dropped by `_EMBED_AUTHOR_STOPWORDS`
→ `n_checked = 1`. Tracer seeded a `verlinde_2017_…_halenka_miller` prose mention into a real
bundle draft with no matching bibitem:

```
default : ✓ PASS  — 3 embedded-citation mismatch(es) (advisory)
--strict: ✗ FAIL  — 3 embedded-citation mismatch(es) (strict mode: mismatches FAIL)
```

Three phantom-citation warnings and a green verdict. This is the D5 phantom-citation incident
the check was written for, reproducing green in the routine suite.

---

### `R4-I9` — IMPORTANT — `bibitem_title_primary_source` is structurally incapable of failing in default mode, and a *fabricated* title never fails in either mode

**File:** `scripts/validation/checks/citations.py:955` (`summary_passed = not _cfg.STRICT_MODE or not over_ceiling`), `:994`

Verified by the tracer, seeding an 8th DROP-WORD against `BIBITEM_TITLE_DRIFT_CEILING = 7`:

```
STRICT=False: passed=True  | 8 DROP-WORD drift flag(s) / 58 NOT-FOUND
STRICT=True : passed=False | 8 DROP-WORD drift flag(s) / 58 NOT-FOUND
```

Worse, the docstring's *"a NEW one fails today"* is false for the general defect: a
*hallucinated* title yields NOT-FOUND, not DROP-WORD, and NOT-FOUND is hardcoded
`passed=True` at `:994` in **both** modes:

```
[AKN1998 title -> 'TOTALLY FABRICATED TITLE XYZZY']
  STRICT=False: passed=True | 7 DROP-WORD / 59 NOT-FOUND
  STRICT=True : passed=True | 7 DROP-WORD / 59 NOT-FOUND
```

---

### `R4-I10` — IMPORTANT — three registry fields opt a bibkey out of **all three** citation checks at once, and the module docstring says they cannot

**File:** `scripts/validation/checks/citations.py:375-379`, `:498`, `:823-828`; docstring at `:9-16`

Docstring: *"its discovery is driven by the cache found on disk rather than by a registry
field, **so blanking one field cannot opt a bibkey out**."* True of the content half's
discovery only. The **existence** half exempts on a 3-field conjunction
(`doi`/`arxiv`/`primary_source_path` all null → `textbook-exempt`), the content half then
`continue`s because the discovered cache is a `.pdf`, and `bibitem_title_primary_source` skips
it because `ps_path is None`.

Tracer seeded, in-memory, on `AKN1998` (which has a real PDF on disk):

```
[citation_primary_sources_present] passed=True
   summary | 529 bibkeys cited across 64 papers — 367 cached / 11 inprep-exempt
             / 151 textbook-exempt / 0 need cache      (was 368 cached / 150 exempt)
[bibitem_title_primary_source] passed=True
   summary | checked 302 PDF caches … skipped: 110 textbook   (was 303 / 109)
```

A fabricated title slid from "cached" to "textbook-exempt" and produced zero signal in three
checks. **The exemption is already load-bearing: 150 of 529 cited bibkeys (28 %) sit outside
the existence gate on three null fields.**

---

### `R4-I11` — IMPORTANT — `citation_primary_sources_present` content half measures **37 of 652** registry entries, then reports "Every … cache header agrees"

**File:** `scripts/validation/checks/citations.py:477-595`; skips at `:493`, `:498`, `:521`, `:526`; PASS detail `:588-593`

```
registry total                                  : 652
declared .abstract.txt path taken               : 62
fell back to discovery, found                   : 427
   of which .pdf/.json -> SKIPPED silently (:498): 420
no cache resolved at all -> `continue` (:493)   : 163
--- comparisons that actually RAN ---
Title 38 | Authors 38 | DOI 27 | arXiv 25
had a cache but NO 'Title:' header              : 29   (25 of the 62 DECLARED caches)
```

Every regex is guarded by `if m_x and reg_x`, so a header-less cache passes every comparison
vacuously. Verified: falsifying `Jacquet2022`'s registry title (a *declared* `.abstract.txt`
entry whose cache begins with raw abstract prose) → `passed=True`. 5.8 % coverage rendered as
a universal quantifier.

---

### `R4-I12` — IMPORTANT — three of `atlas_integrity`'s five advertised legs are dead on production data

**File:** `scripts/validation/checks/graph_atlas.py:367-374, 378-386, 390-394`

* `kind_consistency` (`:367`) needs a duplicate FQN. Measured: `nodes: 26103, distinct fqn:
  26103, fqn appearing >1: 0`, and `atlas_kind` is a pure function of the record — even a
  duplicate would agree with itself. **Unreachable.**
* `no_undisclosed_project_axiom` (`:378`) — measured `records with ≥1 GENUINE project axiom:
  0` of 40,262 (all 829 `axiom_deps_project` entries are `native_decide` artefacts;
  independently re-measured by me: `records with a GENUINE project axiom: 0`). A legitimate
  future tripwire, but zero iterations today.
* `open_nodes_registry_backed` (`:390`) is **tautological**: it tests
  `not id.startswith("hyp:") or atlas_kind != "UNKNOWN"` over unknowns that
  `atlas_view.py:164-170` constructs with `node_id = f"hyp:{key}"` and
  `"atlas_kind": "UNKNOWN"` as literals. Unfalsifiable for any content of
  `HYPOTHESIS_REGISTRY`.

Legs 4 (`dependent_theorems_resolve`, 72 refs across 18 of 48 hypotheses) and 5
(`apex_not_closed`, 4 apexes) **do** fire on seeded defects. Net: 2 of 5 live.

---

### `R4-I13` — IMPORTANT — `graph_integrity` fails open when its own analysis module cannot import

**File:** `scripts/validation/checks/graph_atlas.py:233-242`

```python
except ImportError as exc:
    return CheckResult(passed=all(d.passed for d in roster_details),
                       details=roster_details + [Detail("import", True, "... skipping", warning=True)])
```

`conflicts`, `orphan_claims`, `orphans`, `ungrounded`, `broken_chains` and
`missing_provenance` all vanish and the check reports PASS on the roster/ledger legs alone.
This is the same fail-open shape the file's own comments at `:144-150` and `:221-227` were
written to remove from the two adjacent handlers — it survives here.

Related: `graph_atlas.py:56-61` holds a **hand-written 21-code bundle roster** as the fallback
when `bundle_registry` cannot be imported — the exact parallel-roster class the docstring at
`:44-50` memorialises (*"`validate.py` `BUNDLE_CODES` omitted D10–D12"*).

---

### `R4-I14` — IMPORTANT — `recurrence_reopens_closures` sits 1.7× above the live corpus maximum, and its resolution-notice filter matches `NOT FIXED`

**File:** `scripts/validation/checks/reviews.py:44` (`_RECURRENCE_MIN_OVERLAP = 0.45`, verified against `HEAD`), `:62-64`, `:273-275`, `:298-300`

Measured with the check's own normaliser over the live corpus:

```
findings 1561 | closed 603 | blocking closures 372 | pairs compared 7087
median 0.0444  p99 0.1628  MAX 0.2667
above 0.45: 0     above 0.375: 0
```

Every pair in the repository is below both bands. A *verbatim* recurrence seeded into a later
same-bundle review FIRED; a **reworded restatement of the same defect** (J = 0.348) PASSED —
and rewording is what the check's own motivating example (*"the 'effective modulus' misnomer
was closed and re-raised across five rounds"*) actually is.

Compounding: `_RECURRENCE_RESOLUTION_NOTICE_RE` matches `\bFIXED\b` and `\bRESOLVED\b`
case-insensitively, so a heading reading `### 8.1 — 🔴 BLOCKER — NOT FIXED — <verbatim
restatement>` — the standard adversarial-review idiom for a recurrence — is dropped as "a
heading announcing the fix". Verified: byte-identical to the seed that FIRED, plus the two
words `NOT FIXED`, → `✓ PASS`. 80 of 958 open findings (8.4 %) already match this regex.

---

### `R4-I15` — IMPORTANT — `review_severity_declared` enforces an aggregate count over 5 of 273 documents

**File:** `scripts/validation/checks/reviews.py:346` (`_CUTOFF = "2026-08-01"`), `:385-386`

```
total md 273 | before cutoff 247 | on/after 26 | checked (>=1 heading) 5
```

All five were authored on the cutoff day; there are no review directories dated after it.
Stripping **all 33** severity declarations from a 2026-07-31 document → `✓ PASS`.

And the in-scope test is `n_sev < n_head` — a file-level count, with nothing binding a
`- **Severity:**` line to the heading it belongs to. Verified: deleting every real declaration
from a 5-heading document and prepending five bare `- **Severity:** advisory` lines at the top
→ `✓ PASS — 0 with findings that do not declare severity`.

---

### `R4-I16` — IMPORTANT — `prose_theorem_reference_coverage`: a hand-maintained 36-entry prefix list waves 43 live tokens through with no lookup

**File:** `scripts/validation/checks/prose_lean_refs.py:62-71` → `:365-366` → `:481`

```
raw \texttt{} matches: 2137 -> candidates: 821  (61.6 % dropped)
verdicts: OK 583 | MATHLIB 43 | ABSENT 7 | PRIVATE 2 | PHYSLIB 1 | allowlist-hits 35
```

`MATHLIB` is a bare prefix-string match — no Mathlib lookup ever happens. Verified:
`\texttt{Real.utterly\_bogus\_lemma\_r4}` → `✓ PASS`. The sibling project-namespace leg is
sound (`\texttt{SKEFTHawking.totally_invented_r4}` → FIRED), and the core leg plus the legacy
ratchet both fire on seeds, so this check is **YES** overall — but five hand-maintained lists
(`_PROSE_MATHLIB_PREFIXES` 36, `_PROSE_REF_ALLOWLIST` 22 with 35 live hits,
`_PROSE_FILE_SUFFIXES` 20, `_EMBED_AUTHOR_STOPWORDS` 24, `_PROSE_REF_WAIVERS` 1) sit parallel
to the registry.

Related: the ±200-char disclaimer window (`:99-121`, applied `:495-497`, `:550-551`) is a
self-serve exemption — the same seeded bogus ref preceded by *"The bound is not yet tight."*
→ `✓ PASS`. 45,923 of 1,195,564 bundle-draft characters (3.8 %) already sit inside such a
window.

---

### `R4-I17` — IMPORTANT — `accepted_findings_carry_rationale` measures length, with a 2× dead band

**File:** `scripts/validation/checks/reviews.py:589` (`MIN_CHARS = 40`), `:579-582`

```
accepted records 140 | shortest rationales: 79, 121, 127, 127, 134 | median 377
under 40: 0    under 60: 0
```

A 43-character bare restatement — `"Accepted. We accept this finding as stated."` — PASSES,
which is precisely the input the docstring says must fail (*"'accepted' with a one-line
restatement of the finding is not a decision"*). Missing ledger → `passed=True` (annotated
in-body as a known H1-silent site).

---

## 3. MINOR

* **`R4-MIN1`** — three checks (`atlas_hypothesis_discipline`, `elaboration_knob_watchlist`,
  `paper_toolchain_pin_drift`) are hardcoded `passed=True` **by design and by declaration**.
  That is defensible individually; collectively they occupy 3 of the 59 slots in the
  *"59 checks passed"* headline, and `paper_toolchain_pin_drift` has no `--strict` leg at all,
  so the pin-drift sites it reports are never enforced anywhere.
  Verified for `atlas_hypothesis_discipline`: emptying `HYPOTHESIS_REGISTRY` → PASS; injecting
  500 junk headline hypotheses → PASS.
* **`R4-MIN2`** — `_memo.py:293-298` claims *"the cannot-measure baseline scans the source for
  early-return sites… They unwrap through this attribute [`__memo_body__`] instead."*
  `tests/test_cannot_measure_baseline.py` is a pure AST scan of the *files* and never touches
  the function objects; it does not use `__memo_body__`. The guard happens to work; the stated
  reason is wrong, and a future refactor relying on that sentence would be misled.
* **`R4-MIN3`** — `citations.py:20-22` still says *"`--strict` is passed by NO automated
  caller… those strict paths are unreachable in practice today"*, while `citations.py:731` and
  `scripts/gate_precheck.py:51,86` say the opposite. Two comments in one file disagree about
  whether strict mode has a consumer (pass-1 `R4-I11` fixed the fact, not the prose).
* **`R4-MIN4`** *(process)* — six reviewers seeding mutations into one shared checkout
  concurrently is a measurement hazard, and it bit this round: I observed three check bodies
  stubbed to unconditional PASS mid-review. Future passes should give each reviewer a git
  worktree.

---

## 4. Re-verification of pass-1 findings I was asked to re-check

| pass-1 id | pass-1 claim | pass-2 result |
|---|---|---|
| `R4-I1` | `cross_path_consistency`'s two legs "are one assertion" | **Re-filed as `R4-I3`, mechanism corrected.** The register's rebuttal is right that leg 2 constrains the factor 2. But the two legs' `rel_diff` values are **bit-identical**, so leg 2 cannot fail independently on any numerical drift; and *both* legs silently skip to `passed=True, details=[]`, which pass 1 missed entirely. |
| `R4-I6` | two advertised `formula_grounding` legs are dead | **NOT REPRODUCED.** Both legs fire on a production-seeded defect (`passed=False`, correct message). Corpus contains 26 placeholder and 71 reflexive declarations that would trip them. Residual re-filed at IMPORTANT: `FORMULA_GROUNDING_KIND` covers 2 of 522 refs. Register should mark this **corrected**, not closed. |
| `R4-I8` | `readiness_verdicts_agree`'s reverse leg is unreachable | **CONFIRMED, with mechanism.** GREEN is demoted by the producer whenever a P1 gate is blocked, and 0 of 704 gates are ever blocked at P2 → `blocked_at_gate ⊆ blocked_p1` → the leg is dead by construction. Re-filed as `R4-I4`. |

Two pass-1 findings marked ✅ that I re-verified unprompted, and which are **not closed**:

| pass-1 id | recorded status | pass-2 result |
|---|---|---|
| `R4-I7` — the three freshness regenerators cannot fail on staleness | ✅ `1a7f016d` | **Displaced, not closed** (`R4-MAJ6`, `R4-MAJ7`). The new `post_regenerate` leg is reachable — I fired it — but it re-tests the same **mtime** predicate. A corrupted production table cell (`0.55 → 999.999`) passes; a bare `touch` with an empty `git diff` wedges `counts_fresh` permanently red. |
| `R4-I10` — `notebook_exec` skip-cache fingerprint too narrow | ✅ `dd195033` | **Half closed** (`R4-I18`). The `rglob` widening correctly covers the `src/` module half. Cell **metadata** is still outside `_notebook_code_hash`, and `NotebookClient` is built without `force_raise_errors=True`, so a `raises-exception` tag both defeats the check and leaves the cache key unmoved. |

Also re-filed as surviving: `R3-I9` (always-pass population is a syntactic lower bound) —
now quantified at 24 of 48 invisible sites plus a whole third shape, see `R4-I2`.
And `R5-I2` (notebook stored-output correctness covers 2 of 91) — confirmed, and sharpened:
the meaningful denominator is **43 shipped notebooks**, not 91 (`R4-I24`).

---

## 5. Empty-population census

Checks whose verdict is computed over a population that is currently ≤ 2, or that would pass
vacuously if the population emptied:

| check | population | size today | consequence if empty |
|---|---|---|---|
| `bundle_consistency` | cross-bundle clusters | **2** (both `exact` → no-op branch) | explicit `passed=True` + "nothing to verify" |
| `formula_grounding` legs A/C | `FORMULA_GROUNDING_KIND` | **2** of 522 refs | `kind_violations = []` → PASS |
| `theorem_name_embedded_citations` | year-token prose mentions | **1** | `n_warn = 0` → PASS (and PASS anyway outside `--strict`) |
| `cross_path_consistency` | guarded comparison legs | 2, both skippable | `details = []`, `passed=True` |
| `atlas_integrity` `no_undisclosed_project_axiom` | genuine project axioms | **0** of 40,262 | `not untracked` → True |
| `bundle_figure_integrity` | figures in the hardcoded roster | **7** of 124 shipped | `n_fail = 0` → PASS |
| `review_severity_declared` | post-cutoff docs with headings | **5** of 273 | `checked = 0` → PASS |
| `recurrence_reopens_closures` | pairs above J = 0.45 | **0** of 7,087 | `0 contradicted` → PASS |
| `numerical` | experiments in the literal `expected` dict | 3 of 3 | a 4th experiment is silently exempt |
| `paper_toolchain_pin_drift` | drafts | 65 | explicit `passed=True` on `not drafts` |
| `bundle_source_freshness` | findings | 23 | explicit `passed=True` on `not findings` |
| `tables_fresh` | `papers/paper*_*/tables.py` specs | **9**, all legacy dirs, **0 bundles** | `if not specs: return False` → PASS; empties when specs migrate to bundles |
| `claim_clusters_fresh` | v2 `claims_review.json` files | 27 (6 producing clusters) | `if not v2_files: return False` → PASS |
| `notebook_stored_outputs_current` | `D1[12]_*.ipynb` | **2** of 43 shipped | empty scope → FAIL (correct — the one check that gets this right) |
| `disclosure_consistency` | disclosed names with an overclaim verb in window | **0** of 21 registry names | `not any_fail` → PASS |
| `placeholder_not_cited` | in-window placeholder mentions | **9** occurrences, 2 keys | `not any_fail` → PASS |
| `atlas_integrity` `kind_consistency` | duplicate FQNs | **0** of 26,103 | unreachable |
| `recurrence_reopens_closures` §-number tie-breaker | pairs in [0.45, 0.55) | **0** | dead band inside a dead band |

Only **one** of these — `notebook_stored_outputs_current` — treats an empty scope as a failure.
That is the correct pattern and it exists in-tree; it is simply not applied anywhere else.

---

## 6. Per-check table

`can-it-fail` = can this check turn red on the defect its registration string advertises,
in a routine `uv run python scripts/validate.py` run?

| # | check | what it claims | can-it-fail | evidence |
|---|---|---|---|---|
| 1 | `formulas` | Python formulas reference valid Lean theorems | PARTIAL | seed fires, but maps **7 of 429** public functions and resolves against a flat 19,108-name set (`R4-I21`) |
| 2 | `placeholder_not_cited` | placeholder theorems not cited as verified | PARTIAL | seed fires; one unrelated sentence containing `conjectur` suppresses it; ~9 live sites (`R4-I22`) |
| 3 | `disclosure_consistency` | no paper presents a disclosed vacuous proxy as establishing | PARTIAL | 60-char window defeated by an appositive; **0 in-window sites live** (`R4-I22`) |
| 4 | `proxy_body_audit` | structurally-named theorems not proved by a trivial body | PARTIAL | seed fires; name regex drops **749 of 787** trivially-bodied theorems (`R4-I21`) |
| 5 | `tracked_hypothesis_ledger` | consumed tracked-hypothesis Props are registered | PARTIAL | blind to a hypothesis added by the change under review (`R4-I20`) |
| 6 | `tracked_hypotheses_fresh` | PERMANENT_TRACKED_HYPOTHESES.md up to date | YES | pass-1 `R4-I4` bare-`except` fail-open fixed `0077714a`; `old == new` PASS is the correct terminal |
| 7 | `formula_grounding` | every formulas.py ref resolves to a real non-placeholder theorem | YES | **seeded both legs in production → `passed=False`** (`R4-I6`); legs A/C population 2 of 522 |
| 8 | `vacuous_statement_audit` | no content-thin theorem statements | YES | ratchet vs `VACUOUS_STATEMENT_BASELINE` (48); `lean_deps` absent → PASS |
| 9 | `nogo_substrate_integrity` | every provably-false no-go has a kernel-pure backing theorem | YES | pass-1 `R4-I5` closed the empty-backing free pass and the dead `sorryAx` conjunct (`0077714a`) |
| 10 | `native_decide_regression` | trust surface does not grow past ceiling | YES | live 546 vs ceiling 546 — zero headroom, fails on +1; missing `lean_deps` → **FAIL** (correct) |
| 11 | `numerical` | experimental parameters match reference values | PARTIAL | hand-maintained 3-key `expected` dict, silent `continue` (`R4-I7`) |
| 12 | `identities` | mathematical identities hold | YES | 7 concrete assertions, exceptions → FAIL |
| 13 | `paper_table` | Paper 1's shipped Table 1 matches the canonical solver | YES | parses the shipped `.tex` at displayed precision; empty `tabular` → FAIL |
| 14 | `d1_hierarchy_table` | D1 hierarchy table matches the evaluator | YES | same pattern |
| 15 | `f_hierarchy_claims` | flagship inline corrections match the evaluator | YES | same pattern |
| 16 | `theorems` | Aristotle registry entries resolve (ratcheted) | YES | 14 unresolved vs ceiling 14 — zero headroom; missing `lean_deps` → FAIL |
| 17 | `notebooks` | notebooks import physics from src.core | PARTIAL | seed fires; 14 hand-typed forbidden names, 7 real, vs 429 (`R4-I21`) |
| 18 | `lean_source` | key theorem names found in Lean source | PARTIAL | 11 hardcoded spot-checks against 2,039 files; a rename outside the 11 is invisible |
| 19 | `lean_build` | Lean project builds cleanly | PARTIAL | two toolchain-absent PASS legs (`not lake_bin`, `not has_lakefile`), both invisible to the ratchet (`R4-I2`) |
| 20 | `axiom_closure_allowlist` | every declaration's axiom closure is allow-listed | **PARTIAL — and cacheably NO** | six cannot-measure PASS paths, memoized; poisoning proven (`R4-MAJ1`). Non-allow-listed axioms are WARN outside `--strict` |
| 21 | `elaboration_knob_watchlist` | advisory watchlist | **NO** (by design) | `return CheckResult(passed=True, ...)` terminal; declared non-gating |
| 22 | `bundle_figure_integrity` | bundle figures match a fresh render and are legible | PARTIAL | registry derivation dead; 7 of 124 figures; drift leg advisory-only (`R4-MAJ3`) |
| 23 | `viz_consistency` | notebook visualizations use imported physics | **NO** | unconditional `passed=True` at `notebooks.py:199`; 25 live warnings, green (`R4-I25`) |
| 24 | `notebook_exec` | all notebooks execute without errors | **PARTIAL — measuring nothing today** | 91/91 skipped in 0.2 s; a `raises-exception` cell tag turns a `RuntimeError` into "executed successfully" and is outside the cache key (`R4-I18`) |
| 25 | `physical_bounds` | computed quantities within physical bounds | YES | 15–18 concrete assertions over 3 platforms |
| 26 | `cross_path_consistency` | different code paths agree within 0.5 %/1 % | **PARTIAL** | one independent comparison, bit-identical legs, all-skip → `passed=True, details=[]` (`R4-I3`) |
| 27 | `paper_provenance` | figure refs resolve, no placeholder bibliography | PARTIAL | theorem-reference leg removed 2026-08-05 (QI-32, had been empty since 2026-03-26); remaining legs live |
| 28 | `parameter_provenance` | every experimental parameter has verified provenance | **PARTIAL** | value leg measures 37 of 206 (`R4-MAJ5`) |
| 29 | `counts_fresh` | counts.json/tex up to date | **YES, on a non-defect** | mtime-only; a bare `touch` wedges it permanently red, a content change auto-heals and is never reported (`R4-MAJ7`) |
| 30 | `tables_fresh` | paper tables up to date | **PARTIAL** | `0.55 → 999.999` in a production table → PASS; 9 specs, all legacy dirs, 0 bundles (`R4-MAJ6`) |
| 31 | `claim_clusters_fresh` | claim_clusters.json up to date | **PARTIAL** | `cluster_count 3 → 999` + `clusters: []` → PASS, reported "999 cluster(s)" (`R4-MAJ6`) |
| 32 | `numerical_literals` | papers free of inline unit-bearing literals | YES | ratchet vs `NUMERICAL_LITERAL_CEILING`; fails on growth only |
| 33 | `graph_integrity` | orphans, conflicts, broken chains | **PARTIAL** | 21 metrics, gates on 2; 38,009 issues advisory; fails open on ImportError (`R4-MAJ5`, `R4-I13`) |
| 34 | `atlas_integrity` | 5 named consistency legs | **PARTIAL** | 3 of 5 legs dead on production data (`R4-I12`) |
| 35 | `atlas_hypothesis_discipline` | hypothesis distribution (INFO) | **NO** (by design) | `passed=True` literal; empty registry → PASS |
| 36 | `count_literals` | counts referenced via macros, not literals | YES | ratchet vs `COUNT_LITERAL_CEILING = 107` |
| 37 | `recurrence_reopens_closures` | a closure isn't contradicted by a later recurrence | **PARTIAL** | threshold 0.45 vs corpus max 0.267; `NOT FIXED` suppresses (`R4-I14`) |
| 38 | `review_severity_declared` | reviews from the cutoff declare severity | **PARTIAL** | 5 of 273 docs; aggregate count, not per-finding (`R4-I15`) |
| 39 | `review_docs_mint_findings` | every Stage-13 review mints ≥1 finding | **PARTIAL** | case-sensitive severity regex; `PASS` substring drops 2 live BLOCKERs (`R4-MAJ4`) |
| 40 | `accepted_findings_carry_rationale` | every accepted record justifies acceptance | **PARTIAL** | length-only, 2× dead band; missing ledger → PASS (`R4-I17`) |
| 41 | `bundle_metadata_matches_graph` | bundle_metadata.json counts equal the graph's | YES | direct equality on live graph counts |
| 42 | `notebook_stored_outputs_current` | companion notebooks' stored outputs match | YES (narrow) | both seeds fire; hardcoded `D1[12]_*.ipynb` glob = **2 of 43** shipped notebooks (`R4-I24`) |
| 43 | `readiness_verdicts_agree` | heatmap and gate return the same verdict | PARTIAL | forward leg live (16 bundles); reverse leg dead by construction (`R4-I4`); summary miscounts (`R4-I5`) |
| 44 | `readiness_submission_gate` | every paper has all P1 gates passed | YES | inversion fixed 2026-08-03 (ADR-009 §Deferred 2); 96 blocked P1 gates live |
| 45 | `citation_primary_sources_present` | every cited bibitem has a primary-source cache | **PARTIAL** | 3-field exemption bypasses all three checks; content half 37 of 652 (`R4-I10`, `R4-I11`) |
| 46 | `provenance_doi_in_registry` | provenance DOIs resolve to registry bibkeys | YES (narrow) | hard-fail population 16 refs across 12 of 206 entries; 120-DOI leg is `--strict` only |
| 47 | `bundle_consistency` | cross-bundle clusters agree on numerical content | **NO** | none of the three advertised comparisons is implemented (`R4-MAJ2`) |
| 48 | `bundle_source_freshness` | bundle source mtime ≤ last lift | **NO** in default mode | 11 stale bundles today → `0 FAIL / 11 WARN` → PASS; also **writes git-tracked `bundle_metadata.json`** during the run (`R4-I19`) |
| 49 | `bibitem_title_primary_source` | registry titles match cache PDF titles | **NO** in default mode | `not STRICT_MODE or not over_ceiling`; fabricated titles never fail (`R4-I9`) |
| 50 | `quantum_network` | QN Python formulas satisfy the Lean identities | YES | 16 concrete numeric assertions + a 12-name Lean roster; missing dir → FAIL |
| 51 | `bundle_registry_consistency` | one source of truth for the bundle roster | YES | `glob`→`rglob` fixed `6c89beaa` (pass-1 `R1-I2`); 12 consumers asserted |
| 52 | `paper_latex_compiles` | bundle drafts compile under pdflatex | YES, with a cache gap | detection verified on a production draft copy; cache not bypassed by `--strict`/`--no-memo`, no source or TeX-toolchain fingerprint (`R4-I1`) |
| 53 | `axiom_count_prose_consistency` | prose axiom claims agree with counts.json | PARTIAL | hard-fail only when live count is 0 and a non-historical singular claim exists; numeric plural drift is advisory (`fail=False` literal, `:709`) |
| 54 | `prose_theorem_reference_coverage` | bundle `\texttt{}` Lean refs resolve | YES | both legs fired on production seeds; 36-entry Mathlib prefix list waves 43 tokens through (`R4-I16`) |
| 55 | `theorem_name_embedded_citations` | author+year decl names have bibliography entries | **NO** in default mode | `passed = True` literal unless `--strict`; population 1 (`R4-I8`) |
| 56 | `inventory_index_autogen_fresh` | advisory: autogen blocks match counts.json | **NO** (by design) | terminal `passed=True`; `stale` branch also returns PASS |
| 57 | `lean_docstring_refs_resolve` | Lean docstring names resolve | YES (strict families) | memoized on Lean sources + pins; strict families FAIL, rest advisory (844 advisory details today) |
| 58 | `paper_toolchain_pin_drift` | advisory: draft pins match live pins | **NO** (by design) | every path `passed=True`; no `--strict` leg exists |
| 59 | `cgl_fdr` | CGL FDR derivation produces correct results | YES | 4 concrete legs, each a boolean from `src.second_order.cgl_derivation`; exceptions → FAIL |

*(Roster verified: `len(validate._CHECKS) == 59`; the 59 rows above cover every registered name.)*

**Tally.** `NO` on the advertised defect — **11**:
`bundle_consistency`, `viz_consistency`, `bundle_source_freshness` (default mode),
`bibitem_title_primary_source` (default mode), `theorem_name_embedded_citations` (default mode),
`atlas_hypothesis_discipline`, `elaboration_knob_watchlist`, `paper_toolchain_pin_drift`,
`inventory_index_autogen_fresh`, plus `axiom_closure_allowlist` *once the memo has cached a
skip*, plus `bundle_figure_integrity`'s guarantee #1.
`PARTIAL` — **24**. `YES` (including narrow/ratcheted) — the remaining 24.

**Five of the eleven are `--strict`-only.** `--strict` has exactly one caller
(`scripts/gate_precheck.py:51,86`, the manual `submission` stage). So in the routine
`uv run python scripts/validate.py` that gates every wave, those five contribute nothing.

---

## 7. Findings — freshness / notebooks / lean_substrate

---

### `R4-MAJ6` — MAJOR — `tables_fresh` and `claim_clusters_fresh` cannot see content drift; pass-1 `R4-I7`'s fix re-tests the same **mtime** predicate

**File:** `scripts/validation/checks/freshness.py:57-92` (`_verify_regeneration`), `:222-235`, `:277`, `:287-319`, `:380`

**Re-verification of pass-1 `R4-I7` ("the three freshness regenerators cannot fail on staleness",
marked ✅ `1a7f016d`).** The new `post_regenerate` leg **is** reachable — forced by future-dating
a source:

```
$ touch -t 210001010000 src/core/formulas.py
  ✗ post_regenerate — render_paper_tables.py exited 0 but the artifact is STILL STALE
                      (formulas.py newer than oldest output)
```

But it calls the **same** mtime-only `is_stale` closure, so it adds no measurement dimension.
Content corruption of the shipped artifact is invisible:

```
$ # papers/paper1_first_order/tables/table1_experimental_params.tex: 0.55 -> 999.999
$ uv run --no-sync python scripts/validate.py --check tables_fresh
  ✓ staleness — fresh (13 output files across 9 papers)     Overall: 1/1 checks passed
$ grep -c 999.999 papers/paper1_first_order/tables/table1_experimental_params.tex
1                      # corruption untouched

$ # papers/claim_clusters.json: cluster_count 3 -> 999, clusters: []
$ uv run --no-sync python scripts/validate.py --check claim_clusters_fresh
  ✓ staleness — fresh (27 v2 paper(s) tracked)
  ✓ summary   — 999 cluster(s) across 6 paper(s)            Overall: 1/1 checks passed
```

Papers `\input{}` those `.tex` files. A hand-edited numeric cell in a published table passes
both `tables_fresh` and its new post-regeneration verification. **`R4-I7` is displaced, not
closed:** the fix made the check able to fail, on the wrong predicate.

Compounding, `_tables_specs()` globs `papers/paper*_*/tables.py` — **9 specs, all in legacy
`paperNN_*` dirs; zero of the 21 publication bundles has a `tables.py`** — and
`papers/I1/tables/table1_stages.tex` (14th output on disk) is outside the 13 in scope. When
table specs migrate into bundle dirs, the glob empties and `if not specs: return False` makes
`tables_fresh` green-pass forever with no diagnostic.

---

### `R4-MAJ7` — MAJOR — `counts_fresh` now reports only the harmless case and wedges red on it

**File:** `scripts/validation/checks/freshness.py:155, 165`

`update_counts.py:741-742` deliberately skips byte-identical writes; `_counts_is_stale()` is a
pure **mtime** comparison. Consequences in both directions:

* a *content* change makes `update_counts.py` rewrite the artifact, the mtime advances, and the
  check goes green — so the harmful case is auto-healed and never reported;
* a *mtime-only* change (`git checkout`, `stash pop`, rebase, branch switch, or a bare `touch`)
  puts the check into a state **no number of re-runs can clear**:

```
$ touch src/core/constants.py        # git diff --stat -> EMPTY
$ validate.py --check counts_fresh   # run 1
  ⚠ staleness       — stale: constants.py newer than counts.json
  ✓ regenerate      — update_counts.py succeeded
  ✗ post_regenerate — update_counts.py exited 0 but the artifact is STILL STALE …
  Overall: 0/1 checks passed
$ ...                                # run 2: byte-identical, still 0/1
```

I confirmed the tree is in that state right now, independently of the seeding:
`_counts_is_stale() -> (True, 'constants.py newer than counts.json')`. `passed` at `:165` is
`COUNTS_JSON_PATH.exists() and COUNTS_TEX_PATH.exists()` — existence, never content.

A guard that fires on correct data and cannot fire on the defect is worse than no guard; it
trains the reader to ignore the red.

---

### `R4-I18` — IMPORTANT — `notebook_exec` executes **zero** notebooks today, and a cell tag silently converts a raised exception into "executed successfully"

**File:** `scripts/validation/checks/notebooks.py:249-257` (`_notebook_code_hash`), `:321-360`

```
$ time uv run --no-sync python scripts/validate.py --check notebook_exec
  ✓ … SKIPPED — unchanged, previously vetted   (×91)
  Overall: 1/1 checks passed                    Completed in 0.2s
```

That is the cache working as designed — but a reader of "notebook_exec: PASS" is reading a
cache hit, not 91 clean runs. The defect on top of it: `_notebook_code_hash` hashes **only
`cell.source`**, and `NotebookClient` is constructed without `force_raise_errors=True`, so
nbclient's `raises-exception` cell tag both defeats the check and is invisible to the cache key:

```
# appended cell: metadata {"tags":["raises-exception"]}, source: raise RuntimeError('R4 SEEDED FAILURE')
$ validate.py --check notebook_exec
  ✓ Phase5b_SMAnomalyDrinfeld_Stakeholder.ipynb — 4 code cells executed successfully
```

Without the tag the identical cell FAILs. Because the tag lives in metadata, **adding it to an
existing cell does not move the code hash**, so the cache keeps skipping too. Two-line fix:
`force_raise_errors=True`, and fold `cell.metadata` into `_notebook_code_hash`.

This **re-files pass-1 `R4-I10`** (skip-cache fingerprint too narrow, ✅ `dd195033`): the
`rglob` widening correctly closed the `src/` module half — notebooks reference no literal data
paths and import only `src` + third-party (measured) — but cell metadata, `pyproject.toml`,
`uv.lock` and the kernel version remain outside the fingerprint.

---

### `R4-I19` — IMPORTANT — `bundle_source_freshness` cannot fail on staleness outside `--strict`, and **writes to git-tracked files during a read-only validation run**

**File:** `scripts/validation/checks/freshness.py:617-686` → `scripts/check_bundle_source_freshness.py:161-176, 180-183, 195-199`

Every stale-bundle finding the delegate emits is `{"passed": True, "warning": True}`. Only two
sites emit `passed=False` (mapping doc missing; unparseable metadata). The wrapper returns
`passed=(n_fail == 0)`, so staleness is structurally unfailable in the default mode:

```
$ validate.py --check bundle_source_freshness
  ✓ summary — 23 sub-findings: 0 FAIL / 11 WARN / 12 PASS       Overall: 1/1 passed
$ validate.py --check bundle_source_freshness --strict
  ✗ summary — 23 sub-findings: 11 FAIL / 0 WARN / 12 PASS
```

**And the check mutates the repo.** `check_bundle_source_freshness.py:187` and `:204`
`write_text()` `freshness_stale` into `papers/<bundle>/bundle_metadata.json` — files I verified
are **git-tracked** (`git ls-files papers/D1/bundle_metadata.json` → tracked; 9 currently carry
`"freshness_stale": true`). A validation run can therefore dirty the working tree, and it does
so on an **mtime** signal (`rglob("*")` over source-paper dirs), so a `git checkout` manufactures
the flag. `bundle_metadata_matches_graph` then reads the same file.

Empty-population leg at `:643`: `if not findings: return passed=True, "no bundle directories
initialized yet"` — 23 today; a drift in `_VALID_BUNDLE_TARGETS` or the metadata filename
green-passes silently.

---

### `R4-I20` — IMPORTANT — `tracked_hypothesis_ledger` is blind to a hypothesis introduced by the change under review

**File:** `scripts/validation/checks/lean_substrate.py:514-522` vs `:526-532`

The `tracked` **population** is read from the generated `lean_deps.json`; the `consumed` set is
read from **live `.lean` source**. `lean_deps.json` is currently older than the newest `.lean`
file, so a newly added hypothesis is not in the population at all:

```lean
def H_SeededR4Hypothesis : Prop := True
theorem seeded_r4_consumer (h : H_SeededR4Hypothesis) : True := trivial
```
```
$ validate.py --check tracked_hypothesis_ledger
  ✓ surface — 56 tracked Prop-defs; 24 consumed; 24 covered (registry 48 + non-LB 0)
  Overall: 1/1 checks passed
```

It *does* fire when the registry loses a key already known to `lean_deps.json` (seeded rename of
`H_BilocalPointlikeLimit` → FAIL with the correct message). **Invariant #16 exists to stop an
undisclosed load-bearing hypothesis entering the substrate, and the moment it enters is exactly
the moment this check cannot see it** — it catches the hypothesis one `lean_deps.json`
regeneration later, i.e. after the PR merges.

---

### `R4-I21` — IMPORTANT — three name-list guards cover 1.6 %, 1.6 % and 4.8 % of their canonical populations

Grouped because they are one shape: a hand-typed list standing in for a derived one.

* **`notebooks`** (`notebooks.py:60-67`) — 14 forbidden names, **7 of which exist in
  `formulas.py`**, against **429 public functions**; one entry (`count_formula`) defines nothing
  anywhere in `src/`. The detector is `re.search(rf'def\s+{fn}\s*\(')`, so an inline
  re-implementation or a copy under another name is invisible. Fires correctly when it applies
  (seeded `def damping_rate(` → FAIL).
* **`formulas`** (`lean_substrate.py:61-69`) — the `mapping` list covers **7 of 429** public
  functions. The second leg resolves against `all_lean_names`, built from a raw
  `line.startswith('theorem ')` scan of 2,039 files → **19,108 names** + 308 Aristotle keys, so
  membership proves only "a theorem with this name exists somewhere", not the right module and
  not `sorry`-free. Pass-1 `R4-I3`'s fix tightens 14 of 19,416 names.
* **`proxy_body_audit`** (`lean_substrate.py:329-334`) — the funnel, measured on the production
  library:

```
theorems scanned                       = 20033
matching _STRUCTURAL_NAME_RE           =   712  (3.6%)
trivially-bodied (ANY name)            =   787
trivially-bodied AND structurally-named=    38
=> trivially-bodied theorems DROPPED   =   749  (95.2%)
```

  Renaming a trivially-closed theorem to dodge the regex is a one-token evasion. The check
  fires on seeds (`theorem seeded_r4_dim_count : True := trivial` → FAIL).

---

### `R4-I22` — IMPORTANT — `placeholder_not_cited` and `disclosure_consistency` are suppressed by ordinary prose, and operate on ~9 and ~5 live sites

**File:** `scripts/validation/checks/lean_substrate.py:153-161` (`_HEDGE_CLAIM_RE`), `:291` (`AFTER = 60`)

`_HEDGE_CLAIM_RE`'s own comment says hedges are *"CLAIM-SPECIFIC MULTI-WORD phrases, **NOT**
bare ambiguous single words"* — but `conjectur` and `_TODO` are bare stems in the alternation,
with a ±320-char window. One unrelated sentence flips a real overclaim to green:

```
seed A: "…\texttt{equivalence_preserves_tensor} is formally verified in Lean, establishing the result end-to-end."
  ✗ D5 — presents placeholder(s) as formally verified without a hedge
seed B: identical + "This is unrelated to the conjectural extension discussed elsewhere."
  ✓ all_papers — no placeholder cited as a verified result across 64 paper draft(s)
```

`conjectur` occurs **115 times** across the 64 drafts; `deferred to` 32 times. Live population:
**9 token occurrences total**, 2 registry keys, 1 with a verify-claim in window (hedged).

`disclosure_consistency`'s 60-character window is defeated by one appositive clause
(`"…, together with the per-item lemmas of Section 4 and the numerical scan, establishes…"` →
PASS). Live population: 21 disclosed names, **4 appear anywhere in the corpus (5 occurrences),
0 with an overclaim verb within 60 chars** — against 202 overclaim verbs and 322 ledger hedges
in the corpus at large. The failing leg matches nothing today.

---

### `R4-I23` — IMPORTANT — `inventory_index_autogen_fresh` loses its own scope silently

**File:** `scripts/validation/checks/freshness.py:695-733` — all four return sites are `passed=True`

Falsifying `40262 → 77777` in the index is detected as stale but still passes (documented
advisory). The finding is the second-order one: renaming the marker
(`<!-- AUTOGEN` → `<!-- AUTOGEN SEEDED`) makes the block invisible and the check reports
**`✓ all autogen blocks fresh`** — the advisory warning itself disappears. A scope-emptying edit
to the Inventory Index is undetectable even at warning level, and this is the only guard on
those numbers.

---

### `R4-I24` — IMPORTANT — `notebook_stored_outputs_current` is the suite's strongest check and covers **2 of 43** shipped notebooks

**File:** `scripts/validation/checks/freshness.py:422`

Both seeds fire cleanly (a falsified stream text and a Plotly annotation leaf), and the
empty-scope **FAIL** at `:427-431` is a genuine improvement over the house pattern. But the
scope is a hardcoded character class, `D1[12]_*.ipynb`:

```
notebooks matching D1[12]_*.ipynb                              =  2   (verified: ls -> 2)
notebooks referenced from papers/ or docs/ (shipped artifacts) = 43
notebooks total                                                = 91
```

41 cited notebooks ship stored outputs with no stored-output guard, and `notebook_exec` — which
the summary line points at as the fallback — has no opinion about stored output at all, which is
this check's own founding observation at `:388-391`. Scope should derive from the bundle
registry / `PAPER_DRAFT_MAPPING`, not from a two-character glob. Re-files pass-1 `R5-I2`.

---

### `R4-I25` — IMPORTANT — `viz_consistency` cannot fail; 25 live warnings, green

**File:** `scripts/validation/checks/notebooks.py:199` — unconditional `return CheckResult(passed=True, …)`

Terminal literal `passed=True` with 25 warnings currently emitted. Unlike the three
`R4-MIN1` checks, this one's registration string
(*"Notebook visualizations use imported physics and consistent style"*) does not declare itself
advisory, and its docstring header calls it "warnings only" only in a comment.

---

## 8. Verdict

**NO — not safe to merge as-is.**

Three merge blockers — each is *this branch* shipping a guard that cannot fire, or making an
existing one weaker:

1. **`R4-MAJ1`** — the memoization surface landed on 2026-08-05 caches a cannot-measure PASS
   for the project's only automated kernel-trust gate, under a key indistinguishable from a
   real measurement, reachable by the repo's own documented `rm -rf .lake/build` workflow.
   Proven end to end. This is the branch introducing the defect class it exists to fight.
2. **`R4-I1`** — the second new cache (`paper_latex_compiles`) is exempt from `--strict`,
   `--no-memo` and `SKEFT_VALIDATION_NO_MEMO`, contradicting the guarantee `_memo`'s docstring
   states for the submission gate, and its key omits both the check body and the TeX toolchain.
3. **`R4-MAJ3`** — `bundle_figure_integrity`'s registry derivation raises on every run, so the
   check silently uses the hand-maintained roster its own comment exists to prevent. This is a
   dead-code defect in a check the branch presents as "the binding".

A fourth is borderline and I am counting it as a blocker on the branch's own terms:

4. **`R4-MAJ7`** — `counts_fresh`'s repair (this branch, pass-1 `R4-I7`) turned an always-pass
   into a check that **wedges permanently red on an empty `git diff`** and still cannot see the
   defect. `_counts_is_stale() -> (True, 'constants.py newer than counts.json')` is the tree's
   state right now. A gate that a `git checkout` can jam red, whose failure text blames the
   generator, will be routed around; that makes the suite less trustworthy than before the fix.
   The fix is small (compare content, or `touch` the artifact when the generator reports
   byte-identical) and belongs with the change that introduced the behaviour.

`R4-MAJ2` (`bundle_consistency` implements none of its three advertised comparisons),
`R4-MAJ4` (`review_docs_mint_findings` evades on capitalisation, two live BLOCKERs already
dropped) and `R4-MAJ6` (a corrupted production table cell passes `tables_fresh`) are severe but
**pre-existing** — they route to follow-up, not to this merge. `R4-I19`'s side effect
(a validation run writing git-tracked `bundle_metadata.json`) is also pre-existing but should be
fixed early: it makes every other measurement in this review round harder to trust.

**Not merge blockers** (submission-blockers → ADR-010): `R4-MAJ5`, `R4-I8`, `R4-I9`, `R4-I10`,
`R4-I11`, `R4-I14`, `R4-I15`, `R4-I16`, `R4-I17`, `R4-I21`, `R4-I22`, `R4-I24` — corpus and
coverage debt, not a regression this branch introduces.

**Minimum to flip to `YES WITH FIXES`** (all four small and local):

1. `memoized()` must refuse to store a PASS that did not measure — or convert
   `axiom_closure_allowlist`'s six SKIP paths to `passed=False`, matching the policy its two
   file-neighbours (`theorems`, `native_decide_regression`) already use six lines away.
2. Wire `--strict` and `--no-memo` (and `SKEFT_VALIDATION_NO_MEMO`) to `FORCE_LATEX`; add
   `source_fingerprint` and a `pdflatex --version` digest to the per-draft key.
3. Fix or delete `bundle_figure_integrity`'s dead derivation block (`sys.modules` registration,
   or just `import review_figures`), and drop the `d11_`/`d12_` filter.
4. Make `counts_fresh` compare content, not mtime.

**Recommended in the same pass, cheap and high-yield:** `re.I` on `_SEVERITY_HEADING` and word
boundaries on `_RESOLVED_HEADING` (`R4-MAJ4` — two live BLOCKERs currently hidden);
`force_raise_errors=True` plus `cell.metadata` in the notebook hash (`R4-I18`); and a third
branch kind in `test_cannot_measure_baseline` for the empty-population shape (`R4-I2`), which is
the one change that would stop this whole class regrowing.
