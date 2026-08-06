# R5 — documentation accuracy

**Reviewer dimension:** does the documentation describe the code that actually exists?
**Branch:** `infra/adr-009-validation-modularization` @ `db430c65` · **worktree:** `.claude/worktrees/rv5`
**Date:** 2026-08-05

**VERDICT: NO — on this dimension only.** The *code* on this branch is sound and I found no defect
in it; every finding below is a document that describes it wrongly, and every fix is a text edit.
But six of them are load-bearing enough that an operator acting on the document would act wrongly,
and two of those are statements the branch's own earlier review already corrected once. Ship the
code; do not ship these four documents as the durable account of it until F1–F6 are corrected.

**27 findings: 6 MAJOR · 7 IMPORTANT · 14 MINOR.**

The code on this branch is in better shape than its documentation. Four production documents
(`VALIDATION_ARCHITECTURE`, `VALIDATION_GATE_TOPOLOGY`, `CHECK_AUTHORING_GUIDE`,
`QA_QI_INFRASTRUCTURE_MAP`) were written at `8f5328ee` (2026-08-05 20:35), and the code did move
under them in the four commits that follow (`9140ffeb`, `c7148779`, `9f62deaa`, `c5f384b4`). But
that is the *smaller* half of the problem. **Two of them were already wrong about the code at the
moment they were committed**, because the changes they misdescribe landed *before* they were
written — `2577fdbc` (08-04 22:47, gave `--strict` an automated caller; F1) and `2512c36e`
(08-05 17:00, gave `elaboration_knob_watchlist` a hard-failing leg; F7). That is the same failure
class this branch exists to close, one level up: **a document reporting a state it did not
measure.**

Nothing here is a soundness defect. Everything here is an operator who reads a production document,
believes a number or a "cannot fire" / "is enforced by", and decides.

---

## Verification method

- Own worktree at `db430c65`, `lean/.lake` APFS-cloned from main (`lake build` replays in 13.8 s),
  gitignored caches (`docs/validation/.check_memo.json`, `notebooks/.notebook_exec_cache.json`,
  `papers/.latex_compile_cache.json`) copied from main so memo/latex/notebook state is warm.
- **My first full-suite run was itself a broken instrument** and I am reporting it as such:
  `uv run --no-sync` created an *empty* `.venv` in the fresh worktree, so 20 checks died on
  `No module named 'numpy'` and the suite read 37/60. `uv sync` first; re-run. (Brief rule 6, applied
  to me.) Every count below states its predicate.
- Counts taken live via `validate._CHECKS` / AST scans, not by grep over prose.

---

## Findings

### MAJOR

#### F1 — "`--strict` has no automated caller" is still asserted in two production documents, ~22 h after it became false, and after the branch's own review already flagged it

`docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md:317` (the §6 "Enforcement reality" mermaid — the
section the document itself calls *"the section that matters… if you take one thing from this
document, take that table"*):

```
ST["6 checks with a --strict-only leg —<br/>nothing passes --strict"]
```

`docs/adrs/ADR-009-…md:756-757`:
> …nothing automated passes the flag, and there is no CI at all (verified: no `.github/workflows`,
> no submission-gate runner in `scripts/`).

and `:769-770`:
> …because nothing automated passes `--strict`, those five are exercised only if a human runs the flag.

**Truth:** `scripts/gate_precheck.py:65,99-101` — `"submission": ["__strict__"]` →
`validate.py --strict --force-latex --no-archive`. Landed in `2577fdbc` (2026-08-04 22:47), i.e. a
submission-gate runner in `scripts/` **does** exist. Verified by reading `gate_precheck.py`.

What makes this MAJOR rather than MINOR: ADR-009 item 6 already carries the correction at `:723-726`
(*"⚠️ SUPERSEDED 2026-08-05 … Reviewer R3 found the same sentence restated in five live sites"*), and
the *same item's* later paragraphs contradict it verbatim. A reader who reaches `:756` after reading
`:723` cannot tell which is current. `scripts/validation/checks/bundles_readiness.py:617-621` shows
the correct pattern — it strikes its own stale parenthetical and names the commit.

Remaining live sites (grep, excluding audit-report copies):
`QA_QI_INFRASTRUCTURE_MAP.md:317`, `ADR-009:756`, `ADR-009:769`, `tests/test_d5_citations.py:9`,
`tests/test_d5_mutation_obligation.py:445`.

Also affected: `ADR-009:771-772` offers as future work *"(ii) mechanize a submission-gate runner that
passes `--strict`"* — already built.

---

#### F2 — the documented trigger for the entire Late-Phase-6 Absorption Protocol cannot fire for 9 of 21 bundles, and no document says so

`docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md:30` (Stage C), `:86`, `:164`, `:184`;
`docs/BUNDLE_LIFT_PROCEDURE.md:33`; workspace `CLAUDE.md` mandatory-reference #10 all describe the
absorption signal as `validate.py --check bundle_source_freshness` setting
`bundle_metadata.json.freshness_stale = true`.

After `9f62deaa`, a bundle **all** of whose declared sources name an absent directory takes a new
`UNMEASURABLE` branch (`scripts/check_bundle_source_freshness.py:185-199`) that `continue`s — it
writes neither `freshness_stale=true` nor `false`. The branch's own message says it:

> …freshness is NOT established for this bundle — **the Stage-C absorption trigger cannot fire.**

**Measured independently** (my own instrument, `bundle_migration.parse_mapping` over
`docs/PAPER_DRAFT_MAPPING.md`, predicate = *declared source whose `papers/<source>/` directory does
not exist*): **9 of 21 bundles are 100 % absent — D6, D7, D8, D9, D10, D11, D12, I2, I3** — and
**89 of 180** source assignments portfolio-wide are absent. This reproduces `9f62deaa`'s commit
message exactly (including D3 = 31 declared / 22 measurable).

Consequence for a reader: `BUNDLE_LIFT_PROCEDURE.md:33` makes `freshness_stale=true` OR
`stage13_redo_required=true` the precondition for an *append* lift. For those 9 bundles the first
disjunct is now unreachable, so the procedure silently degrades to a single manual flag — and
`LATE_PHASE6_ABSORPTION_PROTOCOL.md` §Stage C still calls the trigger "automation".

The code change is right. The three documents that consume it were not updated.

---

#### F3 — the whole `scripts/validation/` package is absent from every document whose job is to describe it

`grep -n "scripts/validation\|validation/checks\|validate_helpers"` over
`SK_EFT_Hawking_Inventory_Index.md`, `SK_EFT_Hawking_Inventory.md`, `README.md`, repo `CLAUDE.md`
returns **nothing**. The 12-module / 9,382-line / 60-check package that ADR-009 created does not
appear in:

| document | what it says instead | live |
|---|---|---|
| `SK_EFT_Hawking_Inventory.md:1091` (§7 SCRIPTS — "comprehensive source of truth for all modules") | `validate.py` — **17** cross-layer validation checks | 60, in 12 modules |
| `SK_EFT_Hawking_Inventory_Index.md:609` (§11, hand-maintained, outside the AUTOGEN markers) | full validation suite (**21 checks**) | 60 |
| `README.md:410` | `# ~28 cross-layer validation checks` | 60 |
| `README.md:394-397` ("Full project tree") | `scripts/` one-liner naming 11 scripts; no `validation/` | 12-module package |

The workspace `CLAUDE.md` states the Inventory is *"your responsibility to keep synced and fully
updated at all times"*, and the repo `CLAUDE.md` routes *"changing anything — quick module/Lean/counts
map"* to the Inventory Index. Both send a reader to a document that describes a `validate.py`
architecture that has not existed since Phase 2 of this branch.

`inventory_index_autogen_fresh` cannot catch this: line 609 is outside the `<!-- AUTOGEN -->`
markers (`SK_EFT_Hawking_Inventory_Index.md:26-49,110-112,139-171` are the only generated blocks).

---

#### F4 — `VALIDATION_ARCHITECTURE.md` presents H3 as structurally prevented; the named test covers 1 of the 3 declared regenerators, and ADR-009 already says so

`VALIDATION_ARCHITECTURE.md:96`:

| H3 | import order silently becomes execution order | `_CANONICAL_ORDER` owns it | `test_regenerators_precede_their_consumers` |

and `:86-88` — *"three checks in `freshness.py` regenerate artifacts other checks read — their
position relative to their consumers is semantic."*

`tests/test_validate_registry_contract.py:102-113` asserts **only**:

```python
for consumer in _COUNTS_CONSUMERS:           # = ('axiom_count_prose_consistency',
    assert order['counts_fresh'] < order[consumer]   #    'inventory_index_autogen_fresh')
```

`_REGENERATORS = ('counts_fresh', 'tables_fresh', 'claim_clusters_fresh')` (`:77`) — `tables_fresh`
and `claim_clusters_fresh` are asserted against **no consumer at all**; the tuple appears only inside
an error message. ADR-009 §Deferred item 0(d) (`:559-566`) states this precisely — *"narrower than its
name … Widening this property is part of item 0's fix, and it will fail on the current ordering"* —
and item 0 is marked **✅ DISPOSITIONED** with the widening never performed (second half DECLINED).

So the architecture document promotes a partially-verified property to "structurally prevented" and
drops the caveat its own source carries. This is the branch's signature defect in prose form: the
count of what was asserted is not evidence that the population was reached.

---

#### F5 — the 59 → 60 roster change is unreconciled across every document in scope

`9140ffeb` added `bundle_tables_use_pipeline` (in `papers_prose.py`). Live: **60** registered checks
(`len(validate._CHECKS)`), **60** `@register_check` decorators under `scripts/validation/checks/`,
`_CANONICAL_ORDER` length 60. Every count below was taken with that predicate.

| site | claim | live |
|---|---|---|
| `VALIDATION_ARCHITECTURE.md:18,31` | "the **59 checks**", "12 modules, 59 checks" | 60 |
| `CHECK_AUTHORING_GUIDE.md:71` | "**4 of 59 production-seeded**, 55 fixture-only" | **5 of 60**, 55 fixture-only |
| `QA_QI_INFRASTRUCTURE_MAP.md:93,138,312,358,366-368,379,406-407,425` | 9 separate "59"s | 60 |
| `QA_QI_INFRASTRUCTURE_MAP.md:144` | `papers_prose` \| **6** | 7 |
| repo `CLAUDE.md:109` | "full validation suite (59 checks…)" | 60 |
| `ADR-009` (≈12 sites) | 59 | 60 (historical in most; `:165`, `:178`, `:184` are contract statements) |

Note the predicate trap, in the branch's own house style: **"55 fixture-only" is still correct**
(`FIXTURE_ONLY_CEILING = 55`, live `60 − 5 = 55`, zero headroom). Only the numerator and the
denominator moved. `PRODUCTION_SEEDED` is now 5 — `bundle_tables_use_pipeline` was added to it in
`9140ffeb` — so "4 of 59" understates the sweep's progress *and* misstates the roster.

`tests/test_d5_mutation_obligation.py:585` carries the same stale text in a code comment
("55 of 59 as of 2026-08-05") and `:571` cites "82 vs ceiling 81" for
`prose_theorem_reference_coverage`, whose ceiling `c7148779` moved to
`LEGACY_DRAFT_UNRESOLVED_REF_CEILING = 79`.

---

#### F6 — the field-ownership table names one writer per field; two fields have more, and one of the extra writers is documented elsewhere in the same repo

`VALIDATION_GATE_TOPOLOGY.md:63-73` opens *"A recurring failure mode is a check telling you to run a
script that cannot fix the field"* and then lists a single writer per field.

| field | table says | also written by | does it matter? |
|---|---|---|---|
| `freshness_stale` | `check_bundle_source_freshness.py` | `bundle_append.py:318`, `:388` (clears on lift) · `bundle_source_manifest.py:133` (initialises `false`) | **yes** — a lift clears the flag, so `freshness_stale == false` does not mean "the freshness check ran and found it fresh" |
| `stage13_status` | the Stage-13/9/10 review cycle | `bundle_append.py:320-321` (demotes `green` → `pending` on a lift) | **less** — `bundle_append` only ever *demotes*, so the table's operational advice ("re-running the counts writer will NOT clear it") remains correct |

`docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md:184` **already records** `bundle_append.py:318` as a
`freshness_stale` writer, in a paragraph explicitly written to correct a prior misstatement of the
same field's ownership ("Corrected 2026-07-31 … Overloading it misled two separate reviewers and one
remediation"). The newer document re-introduces the incompleteness the older one was amended to fix.
Combined with F2 (a bundle whose sources are all absent gets **neither** value written), the field
now has three writers and one silent non-writer, and the table shows one writer.

---

### IMPORTANT

#### F7 — "4 always-pass checks, all deliberately advisory" — now 3; the change landed 3½ h before the document was re-based

`QA_QI_INFRASTRUCTURE_MAP.md:316` and `:342-343` name
`elaboration_knob_watchlist`, `paper_toolchain_pin_drift`, `viz_consistency`,
`inventory_index_autogen_fresh`. `ADR-009` §Deferred item 3's table (`:600`) likewise rules
`elaboration_knob_watchlist` **"advisory — keep"**.

`2512c36e` (08-05 17:00) gave it a hard leg:
`scripts/validation/checks/lean_toolchain.py:714` → `return CheckResult(passed=not over, …)`, where
`over = len(violations) > MAXHEARTBEATS_PROOF_BODY_CEILING` (`= 22`, `:590`). AST scan of `passed=`
return values confirms the other three are still literal-`True`-only; this one is not.

The map was re-based at `8f5328ee` (08-05 20:35).

---

#### F8 — Pipeline Invariant #10 is documented as absolute with one named exception; it is enforced as a frozen 22-site ratchet, and no document says the 22 exist

`docs/WAVE_EXECUTION_PIPELINE.md:675-681`, repo `CLAUDE.md` ("Hard rules (do not violate)") and
workspace `CLAUDE.md` all state: no `set_option maxHeartbeats` in any `theorem`/`lemma`/`example`/
tactic-bodied `def`; **"`ExtractDeps.lean` is currently the only such file"** claiming the exception.

Live run output (`validate.py`, `elaboration_knob_watchlist`, this worktree):

```
⚠ invariant_10 — 22 `maxHeartbeats` site(s) in a proof body (ceiling 22)
✗ lean/SKEFTHawking/QuantumGroupAntipode.lean:353 — maxHeartbeats 1600000 on a `theorem` …
… 21 more across Uqsl2AffineHopf.lean, Uqsl3Hopf.lean, QuantumGroupCoproduct.lean
```

The ratchet is correct engineering (zero headroom, may only decrease, discharge plan stated at
`lean_toolchain.py:565-589`) and it is *new* — before 2026-08-05 the invariant had **no enforcement
anywhere**, which the code comment says outright. What is missing is the disclosure: a rule stated
as absolute in three places, with 22 live grandfathered violations, none of which any document
mentions. An agent reading `CLAUDE.md`'s "do not violate" list has no way to learn that 22 sites
already do.

Also: the check's **registered description** — the string a reader sees in `--list` — is
*"proof-body maxRecDepth / synthInstance knobs — a performance / Mathlib-CI-portability signal, NOT a
soundness or axiom-closure issue"*. It does not mention `maxHeartbeats` or Invariant #10, i.e. it does
not describe its own hard-failing leg.

---

#### F9 — `--strict`'s documented effect is incomplete in both flag tables, in two independent ways

`VALIDATION_GATE_TOPOLOGY.md:50-56` and `VALIDATION_ARCHITECTURE.md:104-112` both describe `--strict`
as *"promote submission advisories to hard failures"* + *"implies `--no-memo`"*.

1. **It also bypasses the `paper_latex_compiles` per-draft cache.**
   `scripts/validation/checks/papers_prose.py:591-592`:
   `_bypass_cache = (_cfg.FORCE_LATEX or _cfg.NO_MEMO or _cfg.STRICT_MODE or os.environ["SKEFT_VALIDATION_NO_MEMO"]=="1")`.
   The `FORCE_LATEX` row is documented as the *only* way to bypass that cache. `SKEFT_VALIDATION_NO_MEMO`
   appears in no production document at all (it is set suite-wide by `tests/conftest.py:26`).
2. **After `9f62deaa`, `--strict` hard-fails on 9 bundles for unmeasurability.**
   `scripts/validation/checks/freshness.py:719-721`: `if _cfg.STRICT_MODE and warning: passed = False`.
   The new `UNMEASURABLE` finding is `warning=True`, so the tier-3 submission gate now goes red on
   D6–D12, I2, I3 for a reason no document describes. `VALIDATION_GATE_TOPOLOGY.md:58-61` explains
   `--strict`'s scoping using `bundle_source_freshness` as its worked example and describes only the
   mtime-WARN case.

---

#### F10 — the tier-0 row omits that the sync gate exits 0 for **every** worktree commit, and mis-scopes "fail-open"

`VALIDATION_GATE_TOPOLOGY.md:16` — tier 0, *"blocks?"* column: **"fail-open; hard-blocks on `main` only"**.

- `scripts/pre-commit-sync.sh:21-26`: if `--git-dir != --git-common-dir` (any linked worktree) the
  gate prints and `exit 0` — **no incremental `lake build`, none of the three named checks**, on any
  branch. The `wt1/wt2/wt3` lean-worker slots are linked worktrees, so the tier-0 substrate gate does
  not run for the slots where much of the Lean work is committed. `QA_QI_INFRASTRUCTURE_MAP.md:336-337`
  states this; the document whose stated purpose is *"what runs when, and what it blocks"* does not.
- "fail-open" is true only of the sync gate. The leak-path guard and the IP-disclosure guard in
  `.git/hooks/pre-commit` `exit 1` on **any** branch. (The hook is untracked — `git ls-files` returns
  nothing for it, confirming the map's claim — but it is readable at `.git/hooks/pre-commit` in the
  main checkout, so I read it rather than assuming.)

---

#### F11 — Pipeline Invariant #14's bundle roster contradicts `scripts/bundle_registry.py`, and the check that guards the roster cannot see it

`docs/WAVE_EXECUTION_PIPELINE.md:689` (Invariant #14): *"one of `F`, `D1`–`D9`, `L1`–`L3`, `I1`–`I3`,
`E1`, `E2` — **18 targets** as of the 2026-06-10 D9 authorization"*.

`scripts/bundle_registry.py` — `BUNDLE_CODES` has **21**: `F, D1…D12, L1, L2, L3, I1, I2, I3, E1, E2`.
`VALIDATION_GATE_TOPOLOGY.md:45`'s own "14 of 21 bundles" uses the correct denominator.

`check_bundle_registry_consistency` (`bundles_readiness.py:839-871`) has three legs — leg A compares
the registry to `docs/PAPER_STRATEGY.md` §6 only; leg B to `_ROSTER_CONSUMERS` modules; leg C is an
AST walk over `scripts/*.py`. **No `.md` outside `PAPER_STRATEGY.md` is in the population**, so an
invariant in the pipeline law can carry an 18-bundle roster indefinitely while the check reports a
single source of truth. This is a clean instance of the question the pass exists to answer.

---

#### F12 — `STRICT_MODE` "read by 6 checks" is 7 (and the hand-maintained test list is the 6)

`VALIDATION_ARCHITECTURE.md:108` — *"`STRICT_MODE` … read by 6 checks"*.

AST scan for `_cfg.STRICT_MODE` inside a check body: **7** —
`axiom_closure_allowlist`, `bibitem_title_primary_source`, `bundle_source_freshness`,
`parameter_provenance`, `provenance_doi_in_registry`, `theorem_name_embedded_citations`, **and
`paper_latex_compiles`** (plus `_memo.memoized`, which is the framework, not a check).

**Predicate matters and the docs split on it.** `VALIDATION_GATE_TOPOLOGY.md:52` says `--strict`
*"promotes **6** submission advisories to hard failures"* — that is still correct; `paper_latex_compiles`
reads the flag as a *cache bypass*, not an advisory promotion. `VALIDATION_ARCHITECTURE.md`'s
predicate is "read by", and under its own predicate the number is 7.

Consequence beyond the prose: `tests/test_validate_flag_propagation.py:200-223` is a hand-maintained
parametrize list of the same six, so `paper_latex_compiles`'s `STRICT_MODE` read has **no** H5
`co_names` guard (it is guarded only for `FORCE_LATEX`). The `CHECK_AUTHORING_GUIDE.md:133` checklist
item *"a hand-maintained list parallel to a registry"* fired on its own guard.

---

#### F13 — `CHECK_AUTHORING_GUIDE` §2.3's obligation ("add a test asserting the two agree") is enforced for 6 of the ~9 live check-side ceilings, and the seam guard cannot see the gap

§2.3: *"Measure the live value, set the ceiling to exactly it, and add a test asserting the two agree."*
The enforcing suite is `tests/test_ratchets_have_zero_headroom.py`, whose own docstring says reviewer
R3 *"measured all **ten** ceilings"*.

`RATCHETED_CHECKS` (`:47-54`) covers **six**: `native_decide_regression`, `count_literals`,
`numerical_literals`, `theorems`, `elaboration_knob_watchlist`, `bundle_tables_use_pipeline` — all
six correctly at zero headroom in my run (546/546, 107/107, 116/116, 14/14, 22/22, 4/4). Not covered:

- `prose_theorem_reference_coverage` — `LEGACY_DRAFT_UNRESOLVED_REF_CEILING`, live *"79 unresolved vs
  ceiling 79"*. In fact at zero headroom, but **unguarded** — and note it could not simply be added:
  `_population_and_ceiling` takes the first integer in the message, which for this check is `21`
  ("21 bundle drafts scanned"), so a naive addition would fail on a correct ratchet.
- `bibitem_title_primary_source` — `BIBITEM_TITLE_DRIFT_CEILING = 7`.
- `vacuous_statement_audit` — `VACUOUS_STATEMENT_BASELINE`, live *"23 grandfathered … / 30
  grandfathered …"*; phrasing is `baseline N`, not `(ceiling N)`, so it is invisible to the regex.
- `reviews`' *"dangling supersession finding_id(s) … baseline 66"* — same.

`test_the_covered_set_is_declared` guards only `len(RATCHETED_CHECKS) >= 6`, i.e. exactly the current
size, so it detects a *removal* but never the four that were never added. The guide states the
obligation without the scope; the suite's own docstring ("all ten ceilings") is the evidence that the
scope was known and not carried into the roster.

---

### MINOR

| # | site | claim | live |
|---|---|---|---|
| F14 | `VALIDATION_ARCHITECTURE.md:31` | `checks/` ≈ **8,969 lines** | **9,382** (`wc -l`, 12 files, `__init__.py` excluded). Not reproducible under any predicate at the doc's own commit `8f5328ee`: all-lines-incl-`__init__` 9,200 / excl 9,195 / non-blank 8,197. Closest historical match is `19ddba6d` (8,964), several commits earlier. |
| F15 | `VALIDATION_ARCHITECTURE.md:18` / `QA_QI:137` | validate.py **~720** / **~740** lines | **759** (753 at `8f5328ee`) |
| F16 | `VALIDATION_ARCHITECTURE.md:116` | "43 of **55** checks finished under one second" | population unexplained and stale under every reading (roster 60; `--ci` population now `60 − 4 = 56`) |
| F17 | `ADR-009:949` (addendum II) | `paper_latex_compiles` "is now a **third default red**, correctly" | `VALIDATION_GATE_TOPOLOGY.md:44` says ✅ green (D3 fixed). Two in-scope docs disagree; the ADR is the stale one. |
| F18 | `ADR-009:474-475` | post-regenerator readers at **54 / 55 / 57** | **55 / 56 / 58** (all shifted +1 by `bundle_tables_use_pipeline` at 33). Pre-regenerator 4/6/7/8/9 and `counts_fresh` 29 still correct; conclusion unaffected. |
| F19 | `ADR-009:523` | graph builders at **33, 41, 43, 44** | **34, 42, 44, 45**; still after the last regenerator (31), so the decline stands |
| F20 | `ADR-009:675` | `axiom_closure_allowlist` — "**five** separate PASS returns" | **6** (`passed=True, measured=False` at `lean_toolchain.py:474,480,498,501,505,513`). `_memo.py:330` says six. |
| F21 | `QA_QI:198-199` | "`build_graph_json()` runs **4×** per validate run" | ADR-009 `:517-519` measured **5 invocations across the four builder checks**. The map has the check count where the invocation count belongs. |
| F22 | `QA_QI:32` | "**24 return sites** now declare `measured`" | **25** (AST over `scripts/validation/**`, 157 `CheckResult` return sites total) |
| F23 | `VALIDATION_GATE_TOPOLOGY.md:83` | `pytest tests/` "~285 s, **5,554** tests" | brief reports 5,575 passed / 5 skipped on the same head; the three late commits add 127 lines of tests |
| F24 | repo `CLAUDE.md:107` vs `VALIDATION_GATE_TOPOLOGY.md:83` | "fast tests (~**2.5 min**)" vs "**~285 s**" | two in-scope documents give incompatible figures for the same command |
| F25 | `README.md:393` | "tests/ — **4,823** pytest cases across **132** files" | 4,965 `def test_*` across 170 files in `tests/` |
| F26 | `WAVE_EXECUTION_PIPELINE.md:679`, both `CLAUDE.md`s | ExtractDeps "walks all **2,237+** declarations" | `README.md:271` says 32,309 declarations. Literally true because of the `+`, but the figure is ~14× stale and is used to justify the invariant's only exception. |
| F27 | — | `scripts/validation/checks/papers_prose.py:475` | an unescaped `\i` in a docstring emits a `SyntaxWarning` on **every** `validate.py` invocation (visible in all three of my runs); no document mentions it |

---

## Claims verified as CORRECT

Recorded so the coverage of this pass is legible.

| document | claim | verified value | verdict |
|---|---|---|---|
| `GATE_TOPOLOGY` §1 | tier 0 runs exactly 3 named checks: `formula_grounding`, `placeholder_not_cited`, `native_decide_regression` | `pre-commit-sync.sh:96` — exactly those three | ✅ |
| `GATE_TOPOLOGY` §1 | tier 0 = leak/IP guard · `pre-commit-notebooks.sh` (staged `.ipynb` only) · `pre-commit-sync.sh` (incremental `lake build` if `.lean` staged) | `.git/hooks/pre-commit` + `pre-commit-sync.sh:54-70` | ✅ |
| `GATE_TOPOLOGY` §1 | tier 1 = `s9` (2 checks) · `s10` (4 checks) | `gate_precheck.py:44-46` — `["viz_consistency","bundle_figure_integrity"]`, 4-name s10 | ✅ |
| `GATE_TOPOLOGY` §1 | tier 3 = full suite + the six `--strict` legs | `gate_precheck.py:65,99-101` | ✅ |
| `GATE_TOPOLOGY` §2 | a paper-side red cannot block a commit | tier 0's three checks are all substrate-side | ✅ |
| `GATE_TOPOLOGY` §2 | denominator "of 21 bundles" | `bundle_registry.BUNDLE_CODES` = 21 | ✅ |
| `GATE_TOPOLOGY` §3 | `--strict` promotes **6** submission advisories | 6 advisory-promoting legs (see F12 for the other predicate) | ✅ |
| `GATE_TOPOLOGY` §3 | `--ci` skips the 3 mtime regenerators + `notebook_exec`; enforces the coverage floor; never archives | `_config.CI_SKIP` = exactly those four; `validate.py:708` excludes `args.ci` from archival; `:736-751` counts `r.measured` against the floor | ✅ |
| `VALIDATION_ARCHITECTURE` §2 | `validate._CHECKS is _registry._CHECKS` asserted | `tests/test_validate_public_surface.py:167-171` | ✅ |
| `VALIDATION_ARCHITECTURE` §3 | H1 / H4 / H5 named tests exist | `test_validate_public_surface.py:173`, `tests/test_cannot_measure_baseline.py`, `tests/test_validate_flag_propagation.py` | ✅ |
| `VALIDATION_ARCHITECTURE` §3 | H5's footnote: guard *additionally* requires `_cfg` in `co_names` | `test_validate_flag_propagation.py:227-243` — exactly that assertion, with the reasoning | ✅ |
| `VALIDATION_ARCHITECTURE` §5 | memo cache at `docs/validation/.check_memo.json`; non-measurement never cached; `--strict` implies `--no-memo`; `conftest` disables suite-wide; `TestCheckKeysSpanTheirInputs` exists | `_memo.py:94,293-294,325`; `tests/conftest.py:26`; `test_validation_memo.py:423` | ✅ |
| `VALIDATION_ARCHITECTURE` §6 | no CI; `CI_DEFAULTS_ASSESSMENT.md` is the account | no `.github/`; file present | ✅ |
| `CHECK_AUTHORING_GUIDE` §2.3 | ratchets carry zero headroom | `CI_MIN_CHECKS_RUN = 56` = `60 − len(CI_SKIP=4)`, bumped in the same commit that added the 60th check; `FIXTURE_ONLY_CEILING = 55` = `60 − 5`; `MAXHEARTBEATS_PROOF_BODY_CEILING = 22` = live 22 | ✅ |
| `CHECK_AUTHORING_GUIDE` §2.4 | "55 fixture-only (`FIXTURE_ONLY_CEILING`)" | 55 — correct despite "4 of 59" being wrong (F5) | ✅ |
| `CHECK_AUTHORING_GUIDE` §2.7 | backlog empty, `AWAITING_CEILING` 0 | `AWAITING_MUTATION_TEST = frozenset()`, `AWAITING_CEILING = 0`, `MUTATION_VERIFIED` = 60 = registered | ✅ |
| `CHECK_AUTHORING_GUIDE` §3 | module routing table | covers all 12 modules under `checks/` | ✅ |
| `QA_QI` §6 | `.git/hooks/pre-commit` is local-only and uncommitted | `git ls-files` → 0 matches | ✅ |
| `QA_QI` §1 | per-module check counts | 11 of 12 rows correct; only `papers_prose` (6→7) drifted | ✅/F5 |
| `ADR-009` §Deferred | **8 of 8 dispositioned** (0–7 each carry a disposition) | header `:446-449` + each item's marker | ✅ |
| `ADR-009` item 6(a) | *the filing's* "two gates" was wrong | 6 (at time of writing); now 7 by the "reads" predicate — the item's conclusion stands | ✅ |
| `GATE_TOPOLOGY` §2 | `paper_latex_compiles` ✅ **green** (D3's `\Imm` fixed) | run B: *"21/21 bundle drafts clean … 0 with fatal errors"* | ✅ |
| `GATE_TOPOLOGY` §2 | `bundle_metadata_matches_graph` ❌ **14 of 21** | run B: *"21 bundle metadata blob(s) compared … **14** with drift"* | ✅ |
| `GATE_TOPOLOGY` §2 | `readiness_submission_gate` ❌ **0 green / 3 yellow / 61 red across 64 papers** | run B: verbatim identical | ✅ |
| `c7148779` + `c5f384b4` | the `\lean{}`-alias + `\verb` repairs reach the whole population | run B: *"21 bundle drafts scanned / **1051** candidate Lean references — 0 unresolved"* (was 671) | ✅ |
| `9f62deaa` commit claims | 9 all-absent bundles; 89 of 180 assignments absent; D3 "5 of 31" → 5 of 22 | reproduced independently, and run B names exactly D6, D7, D8, D9, D10, D11, D12, I2, I3 as UNMEASURABLE | ✅ |
| brief's stated head state | 58/60, substrate clean, both reds paper-corpus | run B: *"Overall: 58/60 … SUBSTRATE: clean … PAPER CORPUS (2)"* | ✅ |

### §Deferred 0–7, item by item

| item | current text | verdict |
|---|---|---|
| **0** | ✅ DISPOSITIONED — first half fixed, second half declined | **Prose defect.** Clause (d) (`:559-566`) still presents the H3-property widening as *"part of item 0's fix"* that *"will fail on the current ordering"*; it was never done, and `VALIDATION_ARCHITECTURE` then cites the un-widened test as H3's enforcement (F4). Indices in (a) and the decline are off by one (F18, F19). Disposition itself is sound. |
| **1** | ✅ DONE 2026-08-03 | correct; `native_decide_regression` computes from `lean_deps.json`, `counts.json` used as a staleness signal — verified in source |
| **2** | ✅ DONE (`fd470314`) | correct; check hard-fails, and it is red in my run for the stated reason |
| **3** | ✅ DISPOSITIONED — 8 always-pass checks decided individually | **stale in one row**: `elaboration_knob_watchlist` is no longer advisory-only (F7) |
| **4** | ✅ DISPOSITIONED — type change declined, generator ratcheted | correct; one count stale (F20). `test_cannot_measure_baseline.py` present and ratcheting |
| **5** | ⛔ premise false, merge declined | correct — `count_literals` is a ratchet (`COUNT_LITERAL_CEILING = 107`) and the two predicates are genuinely different |
| **6** | ✅ DISPOSITIONED — declined as filed | **Prose defect, the branch's worst.** `2577fdbc` falsified the no-caller sub-clause; the SUPERSEDED note at `:723-726` says so and two later paragraphs (`:756`, `:769`) still assert it verbatim (F1) |
| **7** | ✅ DONE — both halves | correct; both rules present in `build_graph.py`; the self-corrections (144 not 10; `ComputationCorrectness` not a consumer) are the model the rest of the ADR should follow |

---

## The reverse failure — load-bearing behaviour no document describes

1. **The `scripts/validation/` package itself** (F3) — 12 modules, 9,382 lines, in none of the three
   inventory/tree documents.
2. **`pre-commit-sync.sh` exits 0 for every linked-worktree commit** (F10) — in `QA_QI`, absent from
   the gate-topology document.
3. **`SKEFT_VALIDATION_NO_MEMO=1`** (F9) — a production bypass for *two* caches, in no production
   document; only `_memo.py`'s docstring and pass-2 reviewer reports.
4. **`--strict` bypasses the LaTeX per-draft cache** (F9.1).
5. **`elaboration_knob_watchlist`'s Invariant-#10 leg** (F7, F8) — a hard-failing ratchet that its own
   registered description does not mention.
6. **`bundle_append.py` / `bundle_source_manifest.py` as metadata writers** (F6).

---

## Cost figures (`VALIDATION_GATE_TOPOLOGY.md` §5, `VALIDATION_ARCHITECTURE.md` §5)

All measured in the rv5 worktree at `db430c65`, `.lake` cloned from main, caches seeded from main,
`uv sync` done, single-run wall clock.

> ⚠️ **Instrument caveat, stated up front.** This pass runs six reviewer worktrees on one machine.
> I confirmed by `ps`/`lsof` that reviewer R2's `rv2` worktree was running a full `validate.py --json`
> concurrently from ~22:58 onward. **Every wall-clock figure below is an upper bound**, and the two
> taken after 22:58 are explicitly contended. The two full-suite runs (22:48–22:54, 22:54–22:57)
> predate it, but I cannot rule out contention from the other four worktrees at any point. Treat the
> ✅ verdicts as "the doc's figure is consistent with what I measured", not as a tight reproduction.

| doc claim | predicate as I ran it | measured | verdict |
|---|---|---|---|
| full suite **134.2 s** "steady state" (`GATE_TOPOLOGY` §5, `VALIDATION_ARCHITECTURE` §5, `QA_QI` §re-basis, `ADR-009` addendum II) | `validate.py --no-archive`, second run in the tree (regenerators already fired, memo/latex/notebook caches warm) | **144.1 s** (`Completed in 144.1s`; `time` wall 2:24.6) | ✅ **holds** — within 7 % under concurrent load |
| — | *first* run in a freshly checked-out tree (mtime regenerators fire, notebook/latex caches cold) | **366.4 s** | the "~378 s" figure the brief cites is this case. **§5 never states its preconditions**, and the two differ by 2.5×. That is the one substantive gap in the cost section. |
| `axiom_closure_allowlist` **0.1 s** memo-warm | `--check axiom_closure_allowlist` | **0.31 s** wall for the whole `uv run` invocation | ✅ (the doc's 0.1 s is the check body; the difference is process start) |
| `axiom_closure_allowlist` **171.6 s** cold | `--check axiom_closure_allowlist --no-memo` | wall **488.0 s**, but **user CPU 167.2 s** | ✅ **holds.** The wall figure is contention + first-touch paging on a 22 GB freshly-cloned `.lake`; the *CPU* figure lands within 3 % of the doc's 171.6 s. Reporting the wall clock alone here would have been the wrong measurement. |
| `paper_latex_compiles` **16.6 s** for 21 drafts | `--check paper_latex_compiles --force-latex` | **35.8 s** — ⚠️ **CONTENDED, see note** | **not a finding.** I discovered mid-measurement that reviewer R2's worktree (`rv2`) was running a full `validate.py --json` concurrently (`pid 42393`, cwd confirmed via `lsof`). Every per-check timing after 22:58 shares the machine with it, so I withdraw this as evidence against the doc. Re-measure on a quiet machine. |
| `paper_latex_compiles` **~0 s** cached | `--check paper_latex_compiles` | **0.11 s** | ✅ |
| tier 0 **"<1 s + build"** | the three named checks, each a separate `uv run` | 0.67 + 0.22 + 0.42 = **1.31 s** | ✅ approximately; slightly understated because each is its own interpreter start |

**The generalisable point for §5.** Every cost figure in these documents is stated without its
preconditions. "Steady state" is doing all the work in "full suite, steady state — 134.2 s", and it
happens to be true; but a reader on a fresh clone measures 366 s and has no way to tell whether the
document is stale or their tree is cold. Three of the four per-check figures reproduce; the fourth was contended and is withdrawn.
State the preconditions next to the number — and for the cold `axiom_closure_allowlist` figure, say
whether it is CPU or wall.

---

*Reviewer R5, PR review pass 3. Report written to disk per brief rule 2. Nothing was fixed.*
