# R2 — adversarial review of the four newest commits

**Branch:** `infra/adr-009-validation-modularization` · **Head:** `db430c65`
**Scope:** `c7148779`, `9f62deaa`, `c5f384b4`, `db430c65` — the four commits written after
passes 1 and 2 closed, and unreviewed until now.
**Worktree:** `.claude/worktrees/rv2` (detached at `db430c65`). All execution below ran there.
**Date:** 2026-08-05

---

## Verdict

**NO — do not merge as-is.**

The three repairs are each *correct as far as they go* and each is genuinely mutation-verified.
But two of the three close only the sub-case they were derived from, and the branch's own
signature defect — **an instrument reporting a count as if it were a population** — is still live
at HEAD in both of them:

- the `\texttt`-alias fix does not reach **D11 and D12**, which route **336** Lean references
  through a *wrapped* alias. A fabricated Lean name seeded into the real `papers/D11/paper_draft.tex`
  in the form D11 actually uses is **not detected**; the identical name written as `\texttt{}` is.
- the freshness fix keys on the source directory **existing**, not on it being **measurable**. An
  existing-but-empty source directory reproduces the exact vacuous string the commit was written
  to eliminate, verbatim.

Separately, these commits **broke a committed paper draft** (`paper15_methodology` no longer
compiles) and nothing caught it, because `paper_latex_compiles` — the check whose docstring cites
the 2026-06-10 *paper15* incident as its reason for existing — is scoped to bundle drafts and does
not compile paper15.

**Counts:** 1 CRITICAL · 4 MAJOR · 3 IMPORTANT · 8 MINOR.

### Area coverage

| # | area | status |
|---|---|---|
| 1 | the regexes | **NOT cleared** — C1, m3–m6, m8. Injection/backtracking/overlap sub-questions cleared. |
| 2 | the offset bug class | **CLEARED** — offsets correct for both span sources; exemption window verified by execution. |
| 3 | allowlist / prefix additions | **CLEARED** — all five verified in the pinned Mathlib source; 0 project declarations shadowed today. |
| 4 | the 81 → 79 ratchet | **CLEARED with a caveat (I2)** — 79 is the live value, exact, and the guard is not self-sealing. |
| 5 | the freshness fix | **NOT cleared** — M1, I3, m1, m2. `stage13_redo_required` sub-finding confirmed unaffected. |
| 6 | do the new tests fail on revert | **CLEARED** — all three mutations caught, `__pycache__` purged between runs. |

---

## CRITICAL

### C1 — The `\texttt`-alias fix does not reach D11 or D12: 336 bundle references still invisible, and a real drift in them is undetectable

**File:** `scripts/validation/checks/prose_lean_refs.py:66-68`
(`_PROSE_VERBATIM_ALIAS_DEF_RE`), consumed at `:71-82`, `:209-212`.

`c7148779`'s stated design goal is generalisation:

> *"Fix discovers aliases from the preamble rather than hardcoding `\lean`, so the next bundle
> that defines `\leanref` does not reopen the hole."*

That claim is false at the moment it was written. The regex requires the macro body to be
*exactly* `\texttt{#1}`:

```
r"\\(?:newcommand|renewcommand|providecommand)\s*\{?\s*\\([A-Za-z]+)\s*\}?"
r"\s*\[1\]\s*\{\s*\\(?:texttt|mathtt|verb|url|path|code)\s*\{\s*#1\s*\}\s*\}"
```

D11 and D12 — both **publication bundles**, both already in `BUNDLE_CODES` at the time of the fix
— define a *wrapped* alias:

```latex
\newcommand{\thm}[1]{{\def\_{\char`\_\allowbreak}\texttt{#1}}}
```

The extra `{...\def...}` wrapper defeats the pattern. (D10 defines the *plain* form
`\newcommand{\thm}[1]{\texttt{#1}}` and **is** picked up — so the corpus contained both variants,
and the difference between them is the whole hole.)

**Measured** (`_prose_verbatim_macros` / `_extract_prose_lean_candidates`, live corpus):

| draft | `\thm{}` sites | macros discovered | candidates extracted | candidates if `\thm` recognised |
|---|---|---|---|---|
| D11 | 139 | `{texttt}` | **5** | **100** |
| D12 | 197 | `{texttt}` | **4** | **136** |
| D10 | 37 | `{texttt, thm}` | 41 | 41 |

**336 reference sites in two bundle drafts are outside the check.** Corpus-wide sweep for
one-argument macros whose body mentions `texttt`/`mathtt`/`\verb`/`ttfamily` and which
`_prose_verbatim_macros` does *not* return: **336 unreached use sites, all of them in bundle
drafts, all D11/D12.** No legacy draft is affected.

The summary line reads the same way the pre-fix one did: `21 bundle drafts scanned / 1051
candidate Lean references`. It is 1 051 of ≈ 1 278.

**Verification — production-seeded (QI-30), not a fixture.** A fabricated Lean name written into
the real `papers/D11/paper_draft.tex`:

```
seeded as   We use \thm{ghost\_theorem\_xyz} for the bound.
  → ✓ summary — 21 bundle drafts scanned / 1051 candidate Lean references — 0 unresolved FAIL(s)
  → Overall: 1/1 checks passed

seeded as   We use \texttt{ghost\_theorem\_xyz} for the bound.
  → ✗ unresolved:D11:ghost_theorem_xyz — papers/D11/paper_draft.tex:673 …
  → Overall: 0/1 checks passed
```

Draft restored; `git status` clean. The `wen_adw_factor_6000` failure class the check exists to
prevent is currently unpreventable in D11 and D12.

**Not a false FAIL today:** with `\thm` recognised, all 236 D11+D12 candidates resolve (D11:
97 OK / 1 MATHLIB / 2 ABSENT-but-disclaimed; D12: 132 OK / 2 MATHLIB / 2 ABSENT-but-disclaimed).
The drafts are sound. The instrument is blind — exactly the finding pattern that motivated this
pass, reproduced inside the commit that claims to have closed it.

**What a fix needs (not applied — report only):** the alias body test should be
*"contains `\texttt{#1}` / `\mathtt{#1}` anywhere"*, not *"is exactly"*; plus a per-draft
**population guard** per `CHECK_AUTHORING_GUIDE.md §2.5` — assert candidate count against the
number of one-argument-macro call sites in the draft, so the next wrapper variant fails loudly
instead of scoring 4.

---

## MAJOR

### M1 — The freshness fix keys on *existence*, not *measurability*: an empty source directory restores the vacuous PASS verbatim

**File:** `scripts/check_bundle_source_freshness.py:175-176`

```python
absent_sources = [s for s in sources if not (PAPERS_DIR / s).is_dir()]
measurable     = [s for s in sources if s not in set(absent_sources)]
```

`_latest_source_mtime` (`:59-78`) returns `None` in **three** cases, not one:

1. the directory does not exist (`:62-63`);
2. the directory exists but contains no files;
3. the directory exists but every file is filtered out — a dotfile / anything under
   `__pycache__` (`:69`), or `bundle_metadata.json` / `append_log.json` (`:73`).

The fix covers only case 1. Cases 2 and 3 pass `is_dir()`, enter `measurable`, are skipped by the
staleness loop (which still discards `None` at `:181`), and fall to the `else` branch at `:227`,
which prints the same verdict as before — now with the word *"measurable"* in it, which makes it
actively misleading.

**Verification — production-seeded against the real `papers/`.** D9's only declared source is the
synthetic token `D9_initial_draft`. Creating that directory in the worktree:

| seeded state of `papers/D9_initial_draft/` | verdict |
|---|---|
| (absent — HEAD) | `[WARN] D9: UNMEASURABLE: all 1 declared source(s) name a directory absent…` |
| empty dir | `[PASS] D9: fresh: all 1 measurable source paper(s) older than last_lift (2026-06-10)` |
| contains only `.gitkeep` | `[PASS] D9: fresh: all 1 measurable source paper(s) older than last_lift (2026-06-10)` |
| contains only `__pycache__/x.pyc` | `[PASS] D9: fresh: all 1 measurable source paper(s) older than last_lift (2026-06-10)` |

`passed=True`, `warning=False`, freshness asserted over a population of zero — the commit's own
description of the bug it was fixing. Directory removed; `git status` clean.

This is not academic: a source directory whose contents are gitignored, archived, or emptied is
the ordinary shape of a stale mapping entry, and `papers/` mapping tokens are already synthetic.
The correct predicate is the one the loop actually uses —
`measurable = [s for s in sources if _latest_source_mtime(s) is not None]` — computed once and
reused, which also removes m2.

### M2 — These commits broke `papers/paper15_methodology/paper_draft.tex`; it no longer compiles

**File:** `papers/paper15_methodology/tables/table2_checks.tex:63`
(touched by `c7148779` and again by `db430c65`)

Both commits edited row 55 of the autogenerated check table to mirror the new
`@register_check(...)` description string. The description contains raw LaTeX control sequences,
which were written into the table unescaped:

```latex
55 & \texttt{prose\_theorem\_reference\_coverage} & Bundle-draft verbatim Lean references ---
\texttt{}, preamble aliases for it (D8/D9's \lean{}), and \verb (D6) --- resolve in
lean\_deps.json \\
```

`paper15_methodology/paper_draft.tex` defines no `\lean` macro (`grep`: no
`\newcommand{\lean}`), and `\verb ` with a following space is not a legal `\verb` invocation. The
file is `\input{}` at `paper_draft.tex:136`.

**Verification — by execution.**

```
$ cd papers/paper15_methodology && pdflatex -interaction=nonstopmode -halt-on-error paper_draft.tex
! Undefined control sequence.
l.63 ...{}, preamble aliases for it (D8/D9's \lean
!  ==> Fatal error occurred, no output PDF file produced!
```

Substituting `git show 076b19cc:papers/paper15_methodology/tables/table2_checks.tex` (the parent
of the four commits) and recompiling: **`Output written`, clean.** The regression is squarely
these commits.

Root cause is generic, not local: the table renderer copies the `@register_check` description
verbatim, so **any** future check description containing a backslash macro breaks this paper. The
docstring of `paper_latex_compiles` already records that the 2026-06-10 paper15 incident was
"108 fatal LaTeX errors injected by unescaped `&`/`_` … in autogenerated tables", fixed by
"table-generator escaping". That escaping does not cover control sequences.

### M3 — `paper_latex_compiles` is pointed at a population it does not reach: 15 of 43 legacy drafts are fatally broken while it reports 21/21 clean

**File:** `scripts/validation/checks/papers_prose.py:529-531` (description), `:605`
(`for code in BUNDLE_CODES:`)

This is the pass's central question, answered concretely — and it is what let M2 through.

The check's own docstring states its raison d'être as *"the 2026-06-10 paper15 incident … was
invisible to every structural check"*. It then iterates `BUNDLE_CODES` only, so **paper15 is
outside the scope of the check paper15 motivated**.

**Verification — compiled all 43 non-bundle drafts with the same one-pass `pdflatex
-halt-on-error` invocation the check uses:**

```
FATAL paper11_quantum_group           :: ! Undefined control sequence.
FATAL paper15_methodology             :: ! Undefined control sequence.        ← NEW, this branch
FATAL paper16_graphene_sk_eft         :: ! Missing $ inserted.
FATAL paper17_dark_sector             :: ! Undefined control sequence.
FATAL paper21_majorana_rung           :: ! LaTeX Error: Unicode character ∧
FATAL paper22_ew_phase_transition     :: ! LaTeX Error: Unicode character Λ
FATAL paper25_gravitational_waves     :: ! LaTeX Error: Unicode character Γ
FATAL paper26_bh_entropy              :: ! Double subscript.
FATAL paper2_second_order             :: ! LaTeX Error: Unicode character ✓
FATAL paper31_vestigial_inflation_no_go :: ! Double subscript.
FATAL paper33_ewbg_chirality_wall     :: ! LaTeX Error: \mathsf allowed only in math mode.
FATAL paper40_higher_curvature        :: ! LaTeX Error: Unicode character ℝ
FATAL paper43_einstein_cartan         :: ! Double subscript.
FATAL paper7_chirality_formal         :: ! LaTeX Error: Unicode character ι
FATAL paper8_chirality_master         :: ! LaTeX Error: Environment theorem undefined.
```

Concurrently:

```
$ validate.py --check paper_latex_compiles --force-latex
✓ PASS  21/21 bundle drafts clean … 0 with fatal errors
```

14 of the 15 are pre-existing (out of this review's scope, and legacy drafts are declared
historical snapshots — the scope is *stated*, not hidden). But this branch itself made exactly the
opposite argument one check over: the QI-32 legacy leg was added to
`prose_theorem_reference_coverage` because *"deleting that leg and leaving 43 drafts uncovered
would be a walk-back"* (`prose_lean_refs.py:591-602`). The same argument applies here and was not
made, and the cost of not making it is M2.

### M4 — The ADR-010 measurement "D12 references zero Lean modules" is a product of the same blind spot the document warns about two sections earlier

**File:** `docs/audits/2026-08-05-adr010-measurement/MEASUREMENTS.md:141-154`, carried into
`docs/adrs/ADR-010-publication-portfolio-reassessment.md` by `db430c65`.

M2's strict homing predicate is stated as *"a declaration/module named inside a
`\texttt{}`/`\lean{}` span"*. The document contains an explicit warning box (`:135-140`) that its
first pass returned D8 = 0 and D9 = 0 because both use `\newcommand{\lean}[1]{\texttt{#1}}` — and
then publishes:

> **D12 references zero Lean modules.** D7 references four, D10 three, D6 eight. … the
> late-authorized D-tier containers are not merely short, they are **barely attached to the
> substrate at all**.

D11 and D12 use `\thm{}`, which is in neither term of the stated predicate. The correction the
document applied for `\lean` was not applied for `\thm`.

**Verification.** I could not reproduce the published absolute numbers (my reconstruction of the
strict predicate gives D8 = 28 vs the published 37, D10 = 15 vs 3), so I report the **delta under
a single internally-consistent predicate**, holding everything but the alias set fixed:

| bundle | modules named, `\texttt`+`\lean` only | with `\thm` recognised |
|---|---|---|
| D11 | 2 | **23** |
| D12 | **0** | **13** |
| D6 / D7 / D8 / D9 / D10 | 8 / 4 / 28 / 73 / 15 | unchanged |

Independently of predicate calibration: **D12's prose names 132 distinct project declarations and
D11's names 97**, every one of which resolves in `lean_deps.json` (verdict breakdown D11
`{OK: 97, MATHLIB: 1, ABSENT: 2}`, D12 `{OK: 132, MATHLIB: 2, ABSENT: 2}`). "References zero Lean
modules" cannot survive that. The two bundles singled out as least attached to the substrate are
the two the instrument could not see, and the M2 §"barely attached" conclusion — which feeds
ADR-010's portfolio recommendations — needs re-measuring before anything rests on it.

The following M6 claims **did** reproduce exactly and are sound: nine UNMEASURABLE bundles
(D6–D12, I2, I3 — confirmed from the live run); **89 of 180** source assignments naming an absent
directory (recomputed: 180 assignments, 89 absent; 80 distinct sources, 39 absent); D3 "5 of 31 →
truthfully of 22" (live: 22 measurable + 9 absent).

---

## IMPORTANT

### I1 — The new live-corpus freshness test writes to nine tracked files on every run

**File:** `tests/test_d5_freshness.py:559` (`test_the_LIVE_corpus_reports_no_vacuous_freshness`)

The test calls `check_bundle_source_freshness.check()` against the **real** `papers/` tree, and
`check()` has a side effect — `:241-246` rewrites `bundle_metadata.json` to clear
`freshness_stale`.

**Verification.**

```
$ git checkout -- papers/
$ pytest "tests/test_d5_freshness.py::…::test_the_LIVE_corpus_reports_no_vacuous_freshness" -q
1 passed in 0.04s
$ git status --short papers/ | wc -l
9
```

Diff on each: `- "freshness_stale": true` → `+ "freshness_stale": false` (D1, D2, D3, D4, D5, E1,
F, I1, L2). A single test run silently flips nine committed bundle-state flags. The brief itself
names this hazard class ("pass 2 … left a stubbed check body and a zero-byte `paper_draft.tex`
mid-run"). Production-seeded assertions are right; the write path needs to be behind a flag, or
the test needs a copied tree.

### I2 — The 79 ceiling has zero headroom *and* the live value depends on an untracked build artifact: the check FAILS in any tree without a vendored PhysLib

**File:** `src/core/constants.py:1422`; `scripts/validation/checks/prose_lean_refs.py:453-456`
(`_physlib_declares`), `:355-361` (`_physlib_dir`)

The ratchet itself is sound: the live corpus carries **exactly 79** unresolved legacy references
against `LEGACY_DRAFT_UNRESOLVED_REF_CEILING = 79`, and
`test_the_live_legacy_ceiling_has_ZERO_headroom` (`tests/test_d5_prose_lean_refs.py:188-205`)
runs the **real** check and asserts `== ceil`, not `<=`. It is not self-sealing: an extractor that
lost population would drive the count below 79 and fail the test. **Area 4 is cleared on its own
terms.**

What is not sound is the environment coupling. `_physlib_dir()` resolves to
`lean/.lake/packages/Physlib` — an **untracked build artifact**. My worktree, being a fresh
`git worktree` checkout, had no `.lake/`, and the first run I made gave:

```
✗ summary — … 1 unresolved FAIL(s) … 83 unresolved vs ceiling 79
✗ unresolved:D10:MatrixMap.of_kraus_CP — papers/D10/paper_draft.tex:235
✗ legacy_ratchet — 83 … exceeds the frozen ceiling of 79
Overall: 0/1 checks passed
```

After symlinking main's `lean/.lake/packages`, the identical command returns 79/79 and PASS. The
four-token delta (`MatrixMap.of_kraus_CP`, `EuclideanSpace.basisFun`, `H.IsHermitian`, `lp.single`,
`NeutrinoMixing.standParam`) is the PhysLib resolution tier degrading to ABSENT.

At 81 there was slack to absorb it; at 79 there is none. Any CI job, fresh clone, or reviewer
worktree that has not run `lake build` will see `prose_theorem_reference_coverage` red **and**
`test_the_live_legacy_ceiling_has_ZERO_headroom` red — and, per the check's own message, will be
told a NEW unresolved reference was added to a legacy draft, which is false. This tightening was
introduced by `c7148779` without a note about the dependency.

(I flag this as a *reproduction hazard* too, per brief rule 6: my first measurement of this
branch was wrong for exactly this reason, and the report's numbers are all from the
PhysLib-present configuration.)

### I3 — "Guards are production-seeded per QI-30" overstates what the freshness guard establishes

**File:** commit `9f62deaa` message; `tests/test_d5_mutation_obligation.py:565-591`

`PRODUCTION_SEEDED` is defined in-tree as *"a name enters `PRODUCTION_SEEDED` only when someone
has written a defect into the REAL artifact the check reads and watched `validate.py --check
<name>` go red."* `bundle_source_freshness` is **not** in that set and `FIXTURE_ONLY_CEILING`
stays at 55 — correctly, because the new test only *reads* the live corpus; no defect was seeded
into it. And when I did seed one (M1: `mkdir papers/D9_initial_draft`), **the check did not go
red — it went green with a vacuous PASS.**

So the commit-message claim is not just terminologically loose; the substantive property it
asserts is the one M1 disproves.

---

## MINOR

- **m1 — the UNMEASURABLE branch's `continue` skips the stale-flag clear.**
  `check_bundle_source_freshness.py:199` returns before `:240-246`. A bundle carrying
  `freshness_stale: true` that later becomes all-absent would keep the flag pinned true forever
  in the dashboard. No bundle is in that state today (all nine UNMEASURABLE bundles read `false`).
  The `stage13_redo_required` sub-finding is **unaffected** — it is emitted at `:131-140`, before
  the branch; confirmed live (D11 and D12 each emit both findings).
- **m2 — `measurable = [s for s in sources if s not in set(absent_sources)]`** (`:176`) rebuilds
  the set once per element. Correct (sources are dict keys, so no duplicates) but O(n²) and
  self-obscuring; collapses to one comprehension once M1's predicate is used.
- **m3 — `_PROSE_VERB_RE` under-matches legal LaTeX delimiters.** `(?P<d>[^A-Za-z0-9\s*])`
  excludes digits, which LaTeX permits (`\verb1alpha_beta1` → `[]`, verified). Excluding letters,
  `*` and whitespace is correct. Zero digit-delimited spans in the corpus (all 327 use `|`).
  Not matching newlines (`.` without `re.S`) is **correct** — `\verb` cannot span a line.
- **m4 — one unbalanced `\verb` silently swallows the next `\verb` on the same line.**
  `\verb|first_ref and later \verb|second_ref| end` → `[]` (both dropped: the greedy-avoidance
  works, but the first match consumes through the second `\verb`). Corpus is currently balanced:
  327 `\verb` occurrences, 327 matched spans, delta 0 on every draft.
- **m5 — alias forms still unhandled:** `\newcommand*`, `\DeclareRobustCommand`, `\let\x\texttt`,
  and any two-argument wrapper. Zero in the corpus today; `\newcommand*` in particular is one
  character away from a form that *is* handled, and `\providecommand` is already in the
  alternation, so the omission looks accidental rather than scoped.
- **m6 — span ordering.** `:209-212` appends all brace spans then all `\verb` spans, so `out` is
  not offset-ordered. `offsets[0]` (`:561`, `:577`, `:583`) therefore reports the first *brace*
  occurrence, which may not be the earliest occurrence in the file. Cosmetic (line numbers in
  detail messages only); the disclaimer exemption uses `all(...)` and is order-independent.
- **m7 — measurement drift in the guard's own docstring.** `test_the_LIVE_D6_draft_has_its_verb_refs_scanned`
  says D6 "before this … contributed ~9 candidates"; reverting `\verb` support measures **17**.
  Harmless, but it is a number in a test docstring that was not measured.
- **m8 — nested-brace `\texttt{}` bodies remain invisible** (`[^{}]+` cannot cross a brace): 30
  sites corpus-wide, including genuine Lean names carrying markup, e.g.
  `\texttt{div\_lt\_div\_iff$_{0}$}` (paper43, ×2) and `\texttt{TensorialAt.mkHom\textsubscript{2}}`
  (paper44). Pre-existing, not from these commits; listed because it is the same population-reach
  question and would be closed by the same population guard C1 asks for.

---

## Cleared — with the evidence

**Area 2 — offsets.** The `spans` rewrite is correct for both sources. `m.start()` is the macro
start in each case (brace form: index of `\texttt`/alias; verb form: index of `\verb`, not of the
body — verified: `A \verb|alpha_beta| B` → `[('alpha_beta', 2)]`, `s.index("\\verb") == 2`). The
±200 exemption window therefore behaves identically for both:

```
"deferred" + 150 chars + \verb|alpha_beta|  → off=160, disclaimed=True
"deferred" + 400 chars + \verb|alpha_beta|  → off=410, disclaimed=False
```

Mixed source (`\texttt` at 610 with `deferred` in range, `\verb` at 1031 out of range) → correct
`True` / `False` respectively. No mis-exemption.

**Regex injection / catastrophic backtracking.** Alias names are captured by `([A-Za-z]+)` —
letters only — and are additionally `re.escape`d before joining (`:82`). No metacharacter can
reach the alternation, and the resulting pattern is a literal alternation followed by a bounded
`\{([^{}]+)\}`. No nested quantifier, no backtracking blowup. Sorting by descending length makes
the alternation prefix-safe.

**Overlap / double-counting.** Zero across the entire 64-draft corpus: 0 overlapping
(brace-span, verb-span) pairs, and 0 duplicate `(token, offset)` pairs. Tokens appearing in both
forms merge on the `by_token` key, so `n_candidates` (unique tokens per draft) cannot double-count.

**`\verb` in comments / verbatim environments.** Zero candidate tokens from `%`-prefixed lines,
zero from inline `%` tails, zero from inside `verbatim`/`lstlisting`/`minted`/`Verbatim`
environments, corpus-wide. The extractor strips no comments, so this is a property of the corpus
rather than the code — but there is nothing to find today.

**`\texttt` whitespace variant.** Zero `\texttt\s+\{` in the corpus, so requiring `\texttt{`
costs nothing.

**Area 3 — allowlist and prefix additions.** All five verified in the *pinned* Mathlib
(`lean/.lake/packages/mathlib`), not taken on the prose's word:

| addition | verification |
|---|---|
| `binEntropy_lt_log_two` | `Mathlib/Analysis/SpecialFunctions/BinaryEntropy.lean:139` ✅ (matches the commit's claim) |
| `geometric_hahn_banach_compact_closed` | `Mathlib/Analysis/LocallyConvex/Separation.lean:197` ✅ (matches) |
| `fin_cases` | `Mathlib/Tactic/FinCases.lean:91` — tactic syntax ✅ |
| `Rigid.` | `Mathlib/CategoryTheory/Monoidal/Rigid/{Basic,Braided,Functor,…}.lean` ✅ |
| `ObjectProperty.` | `Mathlib/CategoryTheory/ObjectProperty/FullSubcategory.lean` etc. ✅ |

**Blast radius of the two bare prefixes, measured, not reasoned:** `Rigid.` and `ObjectProperty.`
together swallow exactly **three** tokens corpus-wide — `Rigid.Basic` (paper14:38),
`ObjectProperty.FullSubcategory` (paper14:213), `ObjectProperty.IsMonoidal` (paper14:215). All
three resolve `ABSENT` without the prefixes, so the additions are load-bearing and not
ceiling-buying. **Zero** project declarations or dotted suffixes begin with `Rigid.` or
`ObjectProperty.`, so nothing is shadowed today. `Rigid.` is broad for a bare top-level namespace
and would silently swallow a future `SKEFTHawking.…Rigid.*` family — worth a comment, not a
finding. None of the three allowlist entries collides with a project short name.

**Area 6 — mutation verification.** Each mutation applied to the **production** module (not a
fixture), `__pycache__` purged before each run, source restored via `git checkout` after each:

| mutation | tests failed |
|---|---|
| A: `_prose_verbatim_macros` → `frozenset({"texttt"})` (alias support reverted) | 3 — `test_alias_definitions_are_discovered`, `test_alias_uses_become_candidates`, **`test_the_LIVE_D9_draft_has_its_alias_refs_scanned`** (the production-seeded one) |
| B: delete the `spans += [… _PROSE_VERB_RE …]` line | 3 — `test_verb_spans_become_candidates`, `test_verb_does_not_swallow_across_two_spans`, **`test_the_LIVE_D6_draft_has_its_verb_refs_scanned`** (17 candidates vs the required > 80) |
| C: `if sources and not measurable:` → `if False:` | 2 — `test_an_absent_source_directory_is_UNMEASURABLE_not_fresh`, **`test_the_LIVE_corpus_reports_no_vacuous_freshness`** (D6 claims freshness) |

Baseline `tests/test_d5_prose_lean_refs.py tests/test_d5_freshness.py`: **64 passed**. All three
guards genuinely fire. What they do not do is *generalise* — none of them would have caught C1 or
M1, because each asserts a per-draft threshold for the specific draft that motivated it rather
than a population invariant.

**`--strict` promotion is real.** `freshness.py:720-721` sets `passed=False` for any warning
finding under `_cfg.STRICT_MODE`; verified live:
`validate.py --check bundle_source_freshness --strict` → `23 sub-findings: 11 FAIL / 0 WARN /
12 PASS (strict mode: WARN promoted to FAIL)`, `Overall: 0/1`. The commit's claim that
`--strict` blocks the submission gate on UNMEASURABLE holds.

---

## Reproduction notes

- Worktree `.claude/worktrees/rv2` at `db430c65`, `uv sync` run once, then
  `uv run --no-sync python …` throughout.
- **`lean/.lake/packages` must be present** (I symlinked main's) or every number in this report
  shifts — see I2. All figures above are from the PhysLib-present configuration.
- Every seeded artifact (`papers/D11/paper_draft.tex`, `papers/D9_initial_draft/`,
  `papers/paper15_methodology/tables/table2_checks.tex`, both production modules) was restored;
  worktree `git status` is clean apart from the untracked `lean/.lake` symlink.
- Nothing was fixed. Report only, per brief rule 7.
