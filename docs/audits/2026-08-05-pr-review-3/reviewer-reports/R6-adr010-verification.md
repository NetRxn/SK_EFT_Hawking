# R6 — adversarial re-verification of the ADR-010 measurement claims

**Reviewer:** R6 · **Date:** 2026-08-05 · **Head:** `db430c65` · **Worktree:** `.claude/worktrees/rv6`
**Dimension:** assume the 2026-08-05 re-measurements in
`docs/audits/2026-08-05-adr010-measurement/MEASUREMENTS.md` are wrong until independently reproduced.

## Verdict

**YES-WITH-FIXES, but the fixes are load-bearing.**

The measurement pass is largely sound where it measured carefully. **M1 (page counts), M4a (78
theorems), M5 (17/8 stubs) and M6 (the freshness mechanism) reproduce — several of them exactly.**
M4a in particular reproduces to the declaration: 85 shared references, 78 of them `theorem`, every
leaf name unambiguous across the full 30 001-declaration corpus. **The D6+D9 merge case is real and
survives adversarial re-derivation intact.**

But three of the pass's own headline numbers do not survive, and one of them is the same defect the
pass was written to catch:

- **ADR-010's "D11 and D12 reference zero Lean declarations" is false.** D12 names 160 project
  declarations (132 theorems) across 13 modules; D11 names 125 (98 theorems) across 25 modules.
- **The instrument that produced that error is still broken at HEAD.** `prose_lean_refs.py`'s alias
  discovery cannot see D11/D12's `\thm{}` macro. The check reports `PASS — 21 bundle drafts scanned
  / 1051 candidate Lean references`. The population is **1 302**. **251 references (19 %) are
  outside the instrument** — the third instance of this branch's signature defect, live after two
  commits fixing exactly it.
- **"The audit's ~340 is low by 4–5×" is a unit swap, not a correction.** The audit's predicate is
  written out verbatim in its own text ("**162 `PinPlus*.lean` modules**"), it reproduces at 164,
  and it is scoped to ten named arcs — not to the 2 039-module corpus the re-measurement used.

## Severity counts

| | count |
|---|---|
| CRITICAL | 3 |
| MAJOR | 5 |
| IMPORTANT | 6 |
| MINOR | 3 |
| **total** | **17** |

---

## Instrument statement (Rule 6 — does my own instrument reach the population?)

Everything below is derived from three scratch tools I wrote from scratch (`/tmp/r6/`), reusing
nothing from the measurement pass:

1. **`leanscan.py`** — parses all 2 039 `.lean` files under `lean/SKEFTHawking/` directly, stripping
   block/line comments, tracking `namespace`/`section` nesting, and taking column-0 declaration
   headers. Yields **30 001 human-written declarations** (21 221 `theorem`, 6 731 `def`, 894
   `lemma`, 466 `structure`, 342 `abbrev`, 235 `instance`, 98 `inductive`, 14 `class`) across 2 039
   modules. This is deliberately *source*-derived, not `lean_deps.json`-derived, so it is
   independent of the compiler-companion question.
2. **`extract_refs.py`** — extracts verbatim spans from bundle drafts handling **all** forms:
   `\texttt{}` (brace-balanced, nested-brace safe), `\verb<delim>…<delim>` with arbitrary delimiter,
   `verbatim`/`lstlisting`/`alltt` environments, **and any preamble `\newcommand`/`\renewcommand`/
   `\providecommand` one-argument macro whose *body contains* `\texttt|\verb|\url|\path|\mono|\code`
   anywhere** — not only bodies that are literally `\texttt{#1}`.
3. **`resolve.py` / `m2.py`** — resolves span tokens against the declaration and module universes,
   un-escaping `\_`, accepting full dotted names and unambiguous leaves, and treating `Foo.lean` as
   a module reference.

**Reach evidence.** My alias discovery finds `lean` in D8/D9 **and `thm` in D10/D11/D12**. My span
counts: D6 260 spans (235 `\verb` + 20 `\texttt`), D9 205, D12 213, D11 176. My D9 declaration
resolution equals the published one exactly (169 refs / 150 theorems) and my D6 theorem count equals
it exactly (147) — i.e. my instrument lands on the same population the pass reached where the pass
reached it, and on more where it did not.

**Rule 6 fired on me once, and I record it.** My first independent PDF rebuild gave **D10 = 4 pages**
against the published 5, and I nearly filed it. D8 and D10 are the two bundles that use
`\bibliography{}` (BibTeX) rather than an inline `thebibliography`; three bare `pdflatex` passes drop
their bibliographies. Re-run under `latexmk -pdf`, D10 = 5. **My instrument was wrong, not theirs.**
See finding I-12 for the fact that this same hole is latent in the pass's stated rebuild predicate.

---

## Claim table

| claim | published | R6 value | R6 predicate | verdict |
|---|---|---|---|---|
| **M1** page counts, all 21 | F 23, D1 10, D2 11, D3 59, D4 31, D5 14, D6 12, D7 3, D8 9, D9 12, D10 5, D11 9, D12 11, L1 3, L2 4, L3 4, I1 23, I2 15, I3 18, E1 5, E2 5 | **identical, all 21** | fresh compile of every `paper_draft.tex` at `db430c65` into `/tmp/r6/pdf`, 3 `pdflatex` passes (`latexmk -pdf` for the two BibTeX bundles), page count read from `Output written on … (N pages)` in the log | **CONFIRM** |
| **M1** charter values | F 80–150, D1/D4–D7/D9–D11 40, D2 30, D3 50, D8 45, D12 35, L 4, I1 25, I2/I3 15, E 2–3 | identical | `PAPER_STRATEGY.md` §6 table, lines 383–403, read directly | **CONFIRM** |
| **M1.1** Tier-1 186 pp / 480 pp = 38.8 % | 38.8 % | 186/480 = **38.75 %** | sum of the 12 D rows | **CONFIRM** |
| **M1.1** tier fills 15 / 39 / 92 / 102 / 167 % | as published | 15.3 / 38.8 / 91.7 / 101.8 / 166.7 % | ranges at upper bound, as stated | **CONFIRM** (see MIN-15 on range sensitivity) |
| **M1.1** section counts per bundle | 12,8,5,30,10,12,7,7,13,8,7,9,9,3,6,3,14,9,10,8,8 | **identical** | `^\s*\\section\{` on comment-stripped source | **CONFIRM** |
| **M1.2(b)** D-tier 6 290 w vs I-tier 7 184 w | D shallower than I | means D 6 969 / I 7 661 — same direction; **medians D 7 276 > I 7 094** | whitespace tokens after stripping preamble, comments, control sequences, bibliography | **REFRAME** (MAJ-8) |
| **M1.2(b)** "`\input` closure carries more display maths" | stated as mechanism | **no bundle has an `\input` closure**; D3 and D4 `\input` nothing | `grep -n '\\input{' papers/*/paper_draft.tex` | **REFUTE** (MAJ-7) |
| **M1.2(c)** "Nine of twelve D-tier at ~40pp" | nine | **eight** (D1,D4,D5,D6,D7,D9,D10,D11) | `PAPER_STRATEGY.md` §6 Length column | **REFUTE** (IMP-9) |
| **M2** denominator 2 039 | 2 039 | **2 039**; 0 import-only aggregates; top-level `SKEFTHawking.lean` correctly outside | `find lean/SKEFTHawking -name '*.lean' \| wc -l`; per-file check for bodies beyond `import` | **CONFIRM** |
| **M2** un-homed 1 403 (loose) – 1 633 (strict) | band | **1 466 – 1 622** | strict = verbatim spans (all three forms) + `source_manifest.md`; loosest = module/decl leaf as bare substring anywhere in draft + manifests | **CONFIRM** (band reproduces; floor holds) |
| **M2** "the audit's ~340 has no recoverable predicate" | no predicate | predicate is stated **verbatim** at `CROSS-absorbability-and-strategy-drift.md:192` and aggregated at `:203`, caveated at `:971` | read the audit | **REFUTE** (CRIT-3) |
| **M2** "~340 low by 4–5×" | ❌ audit wrong | **category error** — audit counts modules in 10 named arcs; measurement counts all modules corpus-wide | see CRIT-3 | **REFUTE** |
| **M2 arc** `PinPlus*` 2 914 decls / 180 modules vs audit's 162 ("18× low") | 18× low | audit's **162 = `PinPlus*.lean` module files**; I count **164**. Human-written decls = **2 042**; lean_deps non-autogen = 2 874 | `find lean/SKEFTHawking -name 'PinPlus*.lean' \| wc -l` = 164; source parse | **REFUTE** (CRIT-3 / MAJ-4) |
| **M2 arc** autogen filter correctness | `_AUTOGEN_RE` excludes companions | filter removes ~776 `.eq_1/.injEq/.noConfusion/…`; **leaves 748 structure/inductive companions** (`Summand.s`, `SummandType.ofNat`, `inst*`, `.ctorElim`, `.elim`) | diff of lean_deps non-autogen set against my source parse | **REFRAME** (MAJ-4) |
| **M2 arc** zero `papers/` hits for PinPlus | 0 | **0** | `grep -rl "PinPlus" papers/` | **CONFIRM** |
| **M2 arc** `GenericSUd*` = 5 hits in D8, "four filenames and a glob" | 5 | **5** — `GenericSUdQuantitative.lean`, `GenericSUdMatrixMercatorLog.lean`, `GenericSUdSkHeadlineCascadeConcrete.lean`, `GenericSUdSkLengthExponent.lean`, `FKLW/GenericSUd*` | grep on D8 | **CONFIRM (exact)** |
| **M2 arc** Smith* 9 hits, all false positives | 9 | **4** hits, all false positives (I1 bib `Tooby-Smith`; L2 "Smith homomorphism"; D2 "Wu's formula"; D6 bib `X. Wu`) | literal grep on the 21 bundle drafts | **REFRAME** (IMP-13) |
| **M2** per-bundle module table (D6 = 8, D12 = 0, D10 = 3, D11 = 9) | as published | **D6 = 72, D12 = 13, D10 = 14, D11 = 25** | strict predicate above | **REFUTE** (CRIT-1, MAJ-5) |
| **M4a** D6 ∩ D9 = 78 theorems | 78 | **78 theorems** (85 shared refs, 7 `def`) | intersection of resolved declaration sets; kind from source parse | **CONFIRM (exact)** |
| **M4a** shared = 50.3 % of D9 | 50.3 % | **50.3 %** (85/169) | ditto | **CONFIRM (exact)** |
| **M4a** are they real theorems, same declarations? | implied | **yes** — 78/85 `kind = theorem`; **0 of the 85 leaf names is ambiguous** across all 30 001 declarations; all resolve under `SKEFTHawking.QuantumNetwork.*` across 47 modules | leaf-ambiguity scan over the whole corpus | **CONFIRM** |
| **M4b** D4 §9 3 420 w / D8 5 285 w = 65 % | 65 % | **3 662 / 5 521 = 66.3 %** (my counter runs ~5 % high corpus-wide) | lines 834–1394 of D4 vs D8 body | **CONFIRM** |
| **M4b** shared declaration refs = 3 | 3 | **3** — exactly `cliffordT_accPt_one_unconditional`, `skLevel_polylog`, `solovayKitaev_dawson_nielsen_quantitative_…_unconditional` | resolved-declaration intersection | **CONFIRM (exact)** |
| **M4b** shared 8-gram shingles = 5 of 3 979 (0.1 %) | 5 | **5 of 3 221 (0.16 %)** | lowercase word 8-grams, math stripped | **CONFIRM** |
| **M4b** "almost disjoint substrate" | disjoint | **33 of D4's 40 and 21 of D8's 39 refs are in the same `SKEFTHawking.FKLW.*` subtree**; 4 shared modules; 41 % long-word vocabulary overlap; 3-gram overlap 3.8 % | namespace histogram + n-gram sweep n=3..8 | **REFRAME** (MIN-17) |
| **M5** 17 stubs across 8 bundles after the bibliography | 17 / 8 | **17 / 8** — D1 4, D4 3, I1 3, D2 2, D5 2, L1 1, L3 1, I2 1 | `^\s*%+\s*\\section\{` split at `\begin{thebibliography}` / `\bibliography{` | **CONFIRM (exact)** |
| **M5** "before the bibliography: 7, all in D3 — a distinct phenomenon" | distinct | **same phenomenon** — D3's 7 sit at lines 2368–2452, after the last live section, immediately before the bib at 2484; their own inline comments read "empty post-§28 stub" | read D3:2360–2490 | **REFUTE** (IMP-10) |
| **M5** commented words 95–437, ≤ 8 % of live | ≤ 8 % | 108–796 by my block predicate; **but 0 words of manuscript prose** — every block is `Lifted from …` / `TODO: lift content from …` bookkeeping | read D1:1179–1235, D2:1375–1400, D3:2360–2460 | **CONFIRM, strengthened** |
| **M6** 89 of 180 source assignments name an absent directory | 89/180 (49 %) | **89/180 confirmed from the check's own per-bundle output**; my independent mapping parser gives 95/186 (51 %) | own table parser of `PAPER_DRAFT_MAPPING.md` §1 + `papers/<src>` existence | **CONFIRM** |
| **M6** nine fully vacuous bundles = D6–D12 + I2 + I3 | nine | **nine — D6, D7, D8, D9, D10, D11, D12, I2, I3** | independent parse *and* `scripts/check_bundle_source_freshness.py` run | **CONFIRM (exact)** |
| **M6** per-bundle source counts (D6 3, D8 13, D7/D9/D10/D11/D12 1 each) | as published | **identical** | ditto | **CONFIRM (exact)** |
| **M6** self-triggering: D1 stale from a generated table | stated | **confirmed** — the only non-`__pycache__` file in `papers/paper1_first_order/` newer than 2026-06-01 is `tables/table1_experimental_params.tex`, whose line 1 reads `% AUTOGENERATED by scripts/render_paper_tables.py`; `papers/D1/bundle_metadata.json` has `freshness_stale: true` | `find … -newermt`, header read | **CONFIRM (exact)** |
| **M2/ADR-010** `bundle_lean_module_coverage` does not exist | doesn't exist | **doesn't exist** — absent from `validate.py --list`; the only occurrences are the audit's own *proposal* (`CROSS-…:734` "**Add** a `bundle_lean_module_coverage` check") | `--list` + grep | **CONFIRM** |

---

## Findings

### CRITICAL

**CRIT-1 — `ADR-010:139` "D11 and D12 reference zero Lean declarations" is false; D12 names 160.**

`docs/adrs/ADR-010-publication-portfolio-reassessment.md:136–141` prints a table headed
*"Declaration-level references that resolve to real project theorems"* with `D12 = 0`, and the prose
beneath it reads **"D11 and D12 reference zero Lean declarations."** `MEASUREMENTS.md:145,151` says
the same in module terms: *"**D12 references zero Lean modules.** D7 references four, D10 three, D6
eight."* This is the evidence for ADR-010's *"the late D-tier containers … are barely attached to the
substrate they were authorized to present"* — a sentence that is doing portfolio-disposition work.

Measured:

| | D6 | D7 | D10 | D11 | D12 |
|---|---|---|---|---|---|
| published (modules) | 8 | 4 | 3 | 9 | **0** |
| R6 (modules, strict) | **72** | 4 | **14** | **25** | **13** |
| R6 (declarations resolving to real project decls) | 189 | 20 | 35 | **125** | **160** |
| R6 (of which `theorem`) | 147 | 11 | 33 | **98** | **132** |
| verbatim spans in the draft | 260 | 36 | 58 | 176 | **213** |

D12 writes **197 `\thm{}`** spans against 15 `\texttt{}`. D11 writes **139 `\thm{}`** against 29
`\texttt{}`. D10 writes 37 `\thm{}` against 19 `\texttt{}`. Spot-verified end to end:

```
$ grep -o '\\thm{[^}]*}' papers/D12/paper_draft.tex | head
\thm{IsCountRule}
\thm{falseAlarm}
\thm{hasSum\_poissonMeasureReal}
\thm{affinity\_le\_binaryAffinity}
$ grep -rn "^theorem affinity_le_binaryAffinity" lean/SKEFTHawking/
lean/SKEFTHawking/Detection/PoissonDiscrimination.lean:119:theorem affinity_le_binaryAffinity …
```

D12's 13 modules are `Detection/{PoissonDiscrimination,ShotNoise,MatchedFilter,NEPAlgebra,
FilterFloors,GaussianThreshold}`, `Electrothermal/{ETFModel,ETFResponsivity,BolometricFloors}`,
`Control/{RotatingWave,DriveCalibration,CompositeReadoutCeilings}` — i.e. exactly the substrate D12
was authorized to present. **Reversing this row weakens ADR-010's stated case for treating the late
D-tier as unattached, and it is the row that most directly feeds a merge/disposition decision.**

**CRIT-2 — the branch's signature defect is live at HEAD: `\thm{}` is invisible to
`prose_theorem_reference_coverage`; 251 references (19 %) unscanned while it reports PASS.**

`scripts/validation/checks/prose_lean_refs.py:66–68`:

```python
_PROSE_VERBATIM_ALIAS_DEF_RE = re.compile(
    r"\\(?:newcommand|renewcommand|providecommand)\s*\{?\s*\\([A-Za-z]+)\s*\}?"
    r"\s*\[1\]\s*\{\s*\\(?:texttt|mathtt|verb|url|path|code)\s*\{\s*#1\s*\}\s*\}")
```

The body must be **literally** `\texttt{#1}`. D8/D9 satisfy that (`\newcommand{\lean}[1]{\texttt{#1}}`)
— which is why commit `c7148779` closed. D11 and D12 do not:

```
papers/D11/paper_draft.tex:21  \newcommand{\thm}[1]{{\def\_{\char`\_\allowbreak}\texttt{#1}}}
papers/D12/paper_draft.tex:32  \newcommand{\thm}[1]{{\def\_{\char`\_\allowbreak}\texttt{#1}}}
```

Run against the production module at `db430c65`:

```
$ uv run --no-sync python -c "…from validation.checks.prose_lean_refs import
    _prose_verbatim_macros, _extract_prose_lean_candidates…"
D6  macros=['texttt']           candidates=169
D8  macros=['lean','texttt']    candidates=49
D9  macros=['lean','texttt']    candidates=169
D10 macros=['texttt','thm']     candidates=47
D11 macros=['texttt']           candidates=7      ← 139 \thm spans in the draft
D12 macros=['texttt']           candidates=4      ← 197 \thm spans in the draft
```

Monkeypatching `thm` into the discovered macro set (nothing else changed):

```
D10 47   (unchanged — its alias body IS \texttt{#1})
D11 7 → 112     (+105)
D12 4 → 150     (+146)
```

The live check reports:

```
✓ PASS  prose_theorem_reference_coverage
  ✓ summary — 21 bundle drafts scanned / 1051 candidate Lean references — 0 unresolved FAIL(s)
```

**1 051 of 1 302 — 251 references (19.3 %) outside the instrument, rendered as a green PASS.** This
is the branch's own defect class, at the same file, for the third time, after `c7148779` (288 refs)
and `c5f384b4` (276 refs). The BRIEF's question — *"where else is an instrument pointed at a
population it does not actually reach — and would we know?"* — answers itself here: **no, we would
not have known**, because the check's own summary line reports what it scanned, not what exists.
The fix is one character class wide (match `\texttt` *anywhere in* the macro body rather than as the
whole body), but I am not applying it (Rule 7).

*Not previously reported:* neither `\thm` nor D11/D12 appears in the pass-1 or pass-2 corpora, nor in
the three commits' messages, nor in `MEASUREMENTS.md`, which names only `\texttt`, `\lean` and
`\verb` as the three forms (`MEASUREMENTS.md:127,268`).

**CRIT-3 — "the audit's ~340 is low by 4–5×" is a unit swap; the audit's predicate is recoverable
and reproduces at 164.**

`MEASUREMENTS.md:118` asserts the audit's ~340 *"has **no recoverable predicate** and no backing
check"* and grades M2 **❌**. `ADR-010:160` and `:476` carry that forward: *"The inherited '~340' is
low by 4–5×, and had no recoverable predicate"*, and D5's scope is restated as *"1 403–1 633 modules,
not ~340. The scope is 4–5× what the [audit believed]"*.

The predicate is written out in the audit, in the row the figure comes from —
`docs/audits/2026-08-01-publication-readiness/CROSS-absorbability-and-strategy-drift.md:192`:

> **162 `PinPlus*.lean` modules + ~88 `Smith*`/`Wu*`/`SingularManifold*` modules**

and the aggregate at `:203`:

> **Aggregate: roughly 340 kernel-verified Lean modules across ten arcs are named in no bundle
> draft.**

with an explicit accuracy caveat at `:971`: *"Treat ~340 as the right order of magnitude, not an
exact figure."*

Reproduction of the load-bearing sub-figure:

```
$ find lean/SKEFTHawking -name 'PinPlus*.lean' | wc -l
     164
$ git ls-tree -r --name-only 474063f0 lean/SKEFTHawking | grep -c '/PinPlus[^/]*\.lean$'
164          # 474063f0 = the audit-date commit; unchanged since
```

**164 against the audit's 162 — 1.2 % apart, under a stated, reproducible predicate.** The
measurement pass replaced *modules in ten named arcs* with *all modules corpus-wide*, and then graded
the audit ❌ for the difference. Three consequences:

1. `MEASUREMENTS.md:118` ("no recoverable predicate") is factually wrong about the audit's text.
2. The 4–5× framing compares two different populations. Both numbers can be right at once — and are.
3. `ADR-010:476` scopes D5 to *"1 403–1 633 modules, not ~340"* as a **correction**. It is not a
   correction; it is a re-scoping from ten arcs to the whole corpus. That may still be the right
   scope for D5, but the justification currently on the page ("the audit was wrong by 4–5×") does not
   support it, and a reader who checks will find the audit was not wrong.

Sub-figures that do *not* reproduce: `~88 Smith*/Wu*/SingularManifold*` modules — I count 10 by leaf
prefix, 44 by name-substring. The audit wrote "~88" with a tilde and caveated the aggregate; I record
it as unreproduced rather than refuted, since I cannot recover which of the three families it summed.

### MAJOR

**MAJ-4 — the `PinPlus* = 2 914` declaration count is ~30 % inflated by compiler companions the
`_AUTOGEN_RE` filter does not remove.**

The brief asks whether 2 914 is inflated by `.eq_1`/`.proof_2` companions. Measured against
`lean/lean_deps.json` (40 262 records):

| population | count |
|---|---|
| lean_deps records whose name contains `PinPlus` | 3 690 |
| … removed by an `.eq_N/.proof_N/.injEq/.noConfusion/.casesOn/.recOn/.sizeOf_spec/.ctorIdx/.inj/.match_N` filter | 816 |
| … remaining (≈ the published 2 914) | **2 874** |
| … of those, **absent from my column-0 source parse** | **848** |
| … of those 848, `Parent.field` where `Parent` is a source `structure`/`inductive`/`class` | **748** |
| **human-written source declarations containing `PinPlus`** | **2 042** |

The filter correctly strips the classic companions but leaves **structure field projections and
auto-derived instances**: `PinPlusAdamsSparseness.Summand.{s,t,type}`,
`PinPlusAdamsSparseness.SummandType.{ctorElim,ctorElimType,ofNat,ofNat_ctorIdx}`,
`CellularCohomologyMod2.inst{AddCommGroup,AddTorsor…,Nonempty}PinPlusStr`,
`PinPlusAdamsAbutment.inst{AddCommGroup,Fintype,NeZero…}`, `SummandType.A1.elim`, and 740 more of the
same shape. These are generated by the elaborator, exactly like `.eq_1`.

So the number a referee would recognise as "PinPlus theorems and definitions someone wrote" is
**2 042**, not 2 914. The direction of M2's conclusion is unaffected (the arc is large and un-homed),
but the "18×" multiplier is doubly wrong — wrong unit (CRIT-3) *and* an inflated numerator.

`ADR-010:167` prints `2 914 … across 180 modules (not 162)` — the "(not 162)" phrase attaches a
declaration count and a module count to the same comparison in a single parenthesis.

**MAJ-5 — `MEASUREMENTS.md` §M2's per-bundle table contradicts its own §M4a; it was computed before
the `\verb` repair and never re-run.**

`MEASUREMENTS.md:145` publishes D6 = **8** modules referenced. `MEASUREMENTS.md:279` publishes, for
the same D6, **175 resolved declaration references / 147 theorems**, of which **78 theorems are shared
with D9**. Those 85 shared references alone live in **47 distinct modules** (I enumerated them:
`QuantumNetwork.{SecretKeyRate, FidelityKrausDP, BellNegativity, Rate, CoherenceFidelity,
NamedChannelDiamondExact, SpamProcessFidelity, HaarPauli, PLOBRateBound, MixedState, QECSuppression,
DiamondNormAttainment, …}`). **D6 cannot simultaneously reach 8 modules and name declarations living
in 47.** My measurement: D6 reaches 72 modules.

The pass's own warning box at `MEASUREMENTS.md:286` records that the `\verb` blind spot was found
*while re-measuring M4a* and fixed in `c5f384b4`. §M4a was then re-run; **§M2 was not.** Its D6 = 8,
D3 = 55, D8 = 37, D7 = 4 row is pre-fix output. ADR-010 §Context reprints cells from it.

**MAJ-6 — `ADR-010:138–140`'s table mixes module counts and declaration counts under one heading.**

The table is headed *"Declaration-level references that resolve to real project theorems"*:

| D12 | D10 | D7 | D6 | D8 | D9 | D3 |
|---|---|---|---|---|---|---|
| **0** | 3 | 20 | 175 | 39 | 169 | 175 |

Tracing each cell to its source: `D6 = 175`, `D9 = 169` come from `MEASUREMENTS.md` §M4a's
*declaration* row; `D8 = 39` from §M4b's *declaration* row; but **`D12 = 0` and `D10 = 3` are the
§M2 *module* row** (`MEASUREMENTS.md:145`). `D7 = 20` and `D3 = 175` appear in no published table at
all. Two of seven cells are a different quantity from the row's own heading, and one of those two
(`D12 = 0`) is the cell the following sentence quotes. `D11` is asserted in the prose ("D11 and D12
reference zero Lean declarations") without appearing in the table at all.

My values under one consistent predicate: D12 160, D10 35, D7 20, D6 189, D8 39, D9 169, D3 112.

**MAJ-7 — `MEASUREMENTS.md:82` / `ADR-010:116`'s stated mechanism for the page-vs-word gap is
backwards: there is no `\input` closure.**

> *"Page count flatters the D tier because its `\input` closure carries more display maths; words do
> not."*

```
$ grep -n '\\input{' papers/{F,D1,…,E2}/paper_draft.tex
```
Every bundle's only `\input` is `../../docs/counts.tex` (macro **definitions**, zero typeset output),
plus one table in I1. **D3 (59 pp), D4 (31 pp), D7, D8, D10 and D12 `\input` nothing whatsoever** —
and D3 and D4 are precisely the two D-tier drafts with the highest page counts and the lowest w/pp.
The claimed mechanism is not merely unsupported; the bundles it is invoked to explain are the ones
with no `\input` at all. (A display-maths explanation may still be right — but it has to be measured
on the drafts' own math environments, not on an `\input` closure that does not exist.)

**MAJ-8 — "the deep tier is shallower than the infrastructure tier" is a mean artifact of n = 12 vs
n = 3 and does not survive a median.**

`MEASUREMENTS.md:80` / `ADR-010:115`: *"D-tier bundles average **6 290** words and I-tier bundles
average **7 184**. The tier that exists to be long carries less prose per bundle than the tier that
exists to document tooling."*

The means reproduce, and so does the direction under my own counter (D 6 969, I 7 661). But the gap
is carried entirely by two barely-started bundles inside a 12-member tier:

| statistic | published numbers | R6 numbers |
|---|---|---|
| D-tier mean | 6 290 | 6 969 |
| **D-tier median** | **6 525** | **7 276** |
| I-tier mean | 7 184 | 7 661 |
| **I-tier median** | **6 593** | **7 094** |

On the pass's **own** figures the medians are 6 525 vs 6 593 — **1 % apart**. On mine the D-tier
median **exceeds** the I-tier median. Removing D7 (1 712 w) and D10 (2 513 w) — the two bundles M1
independently flags at 8 % and 12 % of charter — moves the D-tier mean to ~7 340, above the I tier.

The sentence is used in `ADR-010` to support a claim about the *tier* ("the tier that exists to be
long"). What the data support is a claim about *two bundles*. A three-member comparison group makes
the mean unusable here, and the paragraph does not disclose the spread.

### IMPORTANT

**IMP-9 — "Nine of the twelve D-tier bundles carry the identical ~40pp charter" — it is eight, and
the sentence's own parenthetical enumerates eight.**

`MEASUREMENTS.md:85`, `ADR-010:118`, and the `db430c65` commit message all say **nine**. The
parenthetical lists **D1, D4, D5, D6, D7, D9, D10, D11 — eight names** — then accounts for the
remaining four (D2 30, D3 50, D8 45, D12 35). 8 + 4 = 12. `PAPER_STRATEGY.md` §6 lines 386–397
confirm exactly eight `~40pp` rows. Self-inconsistent within one sentence; the claim it supports
("a number that nine bundles share was not derived from nine different substrates") holds at eight.

**IMP-10 — M5's "before the bibliography: 7, all in D3 — a distinct phenomenon (commented sections
inside a live body)" is wrong; they are trailing stubs like the other 17.**

`MEASUREMENTS.md:333`. D3's seven commented `\section`s are at lines 2368, 2382, 2396, 2410, 2424,
2438, 2452 — after the last live section, immediately before `\begin{thebibliography}` at 2484 (only
a `BUNDLE_APPEND_INSERT_HERE` marker and a `\section*{Methods and tools disclosure}` intervene).
Their own inline comment states the reason:

> `%% D3 Stage-13 fix-pass 2026-05-11: header commented out per BLOCKER 4.1`
> `%% (empty post-§28 stub renders as TOC entry with no body in compiled PDF).`

Identical mechanism, identical rationale, identical `bundle_append.py` provenance as the 17
after-bibliography stubs. The correct figure is **24 trailing lift stubs across 9 bundles**, D3
holding the most — which matters, because D3 is the bundle M1 singles out as the portfolio's
healthiest.

**IMP-11 — none of the M1–M6 instruments was committed; the pass is not reproducible from the
artifact.**

`git show --stat db430c65` adds `docs/audits/2026-08-05-adr010-measurement/MEASUREMENTS.md` and
nothing else executable. The directory contains one file. Every number in the pass therefore rests on
prose descriptions of ephemeral scripts. This is directly why MAJ-5 (the §M2/§M4a contradiction)
could not be caught by re-running §M2 after the `\verb` fix, and why CRIT-1's `\thm` gap is
invisible: there is no instrument on disk whose alias handling can be inspected. The pass's own
governing rule — *"a count is meaningless without its predicate"* — is satisfied in prose but not in
code, and a prose predicate cannot be re-executed against a changed corpus.

**IMP-12 — M1's stated rebuild predicate ("two `pdflatex` passes") silently drops the bibliography
for D8 and D10.**

`MEASUREMENTS.md:28–30`: *"8 of 21 PDFs were stale against their `.tex` and were rebuilt with two
`pdflatex` passes."* D8 and D10 are the only two bundles using `\bibliography{}` (BibTeX) rather than
an inline `thebibliography`; a bare `pdflatex` sequence yields `[?]` citations and no bibliography
section. **I hit this exactly**: my first independent pass returned D10 = 4 pages; under
`latexmk -pdf` it is 5 (the missing page is the reference list).

The published numbers are unaffected — neither D8 (PDF mtime 2026-06-10) nor D10 (2026-08-01) was in
the rebuilt set of 8 (all of which carry mtime 2026-08-05 21:38: F, D1, D2, D3, D4, D5, D9, E1). But
the predicate as written would have lost a page from D10 had it been stale, and it is published as
the method future measurements should follow.

**IMP-13 — M2's "Smith* … 9 [hits], but every one a false positive" does not reproduce at 9.**

`MEASUREMENTS.md:162`. Literal occurrences of `Smith` or `\bWu\b` across the 21 bundle drafts: **4**.

```
papers/I1/paper_draft.tex:1796  \bibitem{physlean} J.~Tooby-Smith, "PhysLean: Lean 4 for physics,"
papers/L2/paper_draft.tex:318   string-bordism $\mathbb{Z}_{24}$ class and the associated Smith
papers/D2/paper_draft.tex:339   Wu's formula and Poincaré duality) in the field \texttt{even\_unimod}
papers/D6/paper_draft.tex:1042  K. Hietala, R. Rand, S.-H. Hung, X. Wu, and M. Hicks,
```

The **conclusion reproduces exactly** — all four are a bibliography author name or ordinary
mathematical prose, none is a substrate reference. Only the count differs. Filed because the pass's
verdict column is what ADR-010 quotes.

**IMP-14 — "1 403 is a floor" holds, but for a different reason than stated, and the loose predicate
is looser than any I could construct.**

`MEASUREMENTS.md:130–133` argues 1 403 is a floor because the loose rule "accepts a bare leaf
substring, and 49 homed modules have a leaf of ≤ 8 characters, five of them literally `Basic`". The
floor claim survives my instruments (my loosest predicate gives **1 466** un-homed ≥ 1 403), so
**CONFIRM**. But my loosest predicate — module leaf *or* any declaration leaf as a bare substring
anywhere in a draft *or its `source_manifest.md`* — homes only **573** modules against the published
loose figure of **636**. Since I cannot construct a predicate as permissive as the published one, its
63-module surplus is unexplained and unauditable (see IMP-11). This does not change the band's
conclusion; it does mean the band's lower edge cannot be independently confirmed at its stated value.

### MINOR

**MIN-15 — the "15 %" flagship fill and "167 %" tier-4 fill are the upper-bound reading; the lower
bound halves one and inflates the other.**

The predicate ("a range is read at its **upper** bound") is stated, so this is disclosure, not error.
But `F` = 80–150 pp and `E1/E2` = 2–3 pp are the only two ranges, and they sit at both extremes of
the monotonicity argument. At the **lower** bound: F = 23/80 = **29 %** (not 15 %), E = 10/4 =
**250 %** (not 167 %). The conclusion is unchanged and in fact **strengthens** — the spread from
smallest to largest container widens — but `ADR-010:103`'s tier table prints the single number, and
the flagship's headline figure moves by a factor of two on a choice made in a footnote.

**MIN-16 — M4b's "MISREAD" verdict misattributes the misreading.**

The `db430c65` commit message grades *"D4 §9 = 62 % of D8 → **MISREAD**"* and
`MEASUREMENTS.md:303` says the 62 % *"is a comparison of lengths, not a measure of shared content,
**and ADR-010 §C3 inherited it as the latter**"*. The audit's own sentence
(`CROSS-portfolio-coherence.md:172`) is explicitly a length comparison — *"3,206 words, which is 62 %
of D8's entire 5,186-word manuscript"* — and the paragraph around it draws the **priority-and-
attribution** conclusion the measurement pass then re-derives ("both bundles assert priority over the
same result", `:180–189`), listing exactly the 3 shared declarations + 2 shared modules that M4b
reports as its finding. The misreading, if any, happened in ADR-010, not in the audit; the verdict
column reads as an error by the audit and should be re-pointed.

**MIN-17 — "almost disjoint substrate" overstates; both sections present the same Lean subtree.**

`MEASUREMENTS.md:317`: *"D4 §9 and D8 are independently written treatments of the same subject over
**almost disjoint substrate**. Merging them would remove almost no duplicate text."* The
text-overlap half is solid (I reproduce 3 shared declarations and 5 shared 8-grams exactly). But:

- **33 of D4's 40** declaration references and **21 of D8's 39** are in `SKEFTHawking.FKLW.*` — D8's
  own namespace.
- They share **4 modules** (`FKLW.{FibSU2Density, GenericSU2GeneratingSet,
  GenericSolovayKitaevQuantitative, SolovayKitaevQuantitative}`) and 3 declaration-hosting modules.
- 3-gram shingle overlap 3.8 %; long-word (≥ 7 char) vocabulary overlap **41.3 %**.

So the two sections are not treatments over disjoint substrate — they are **two papers presenting
different theorems from the same Lean library subtree, with no ownership boundary between them.**
The remedy M4b proposes (decide who owns the claim, re-point the other) is right; the diagnosis that
frames it as merely a naming/priority conflict understates that the *library* is shared even though
the *theorems cited* are not.

---

## What the pass got right, recorded because remediation depends on it

- **M4a is exact and adversarially robust.** 85 shared references, **78 theorems**, 50.3 % of D9,
  reproduced from a from-scratch source parse. All 85 leaf names are **unambiguous across all 30 001
  project declarations**, so these are the same declarations, not name collisions — the specific
  concern the brief raised. All resolve under `SKEFTHawking.QuantumNetwork.*`, across 47 modules.
  **The D6+D9 merge case stands.**
- **All 21 page counts reproduce exactly** from independent recompilation, including the two BibTeX
  bundles once compiled correctly. The charter values parse correctly from `PAPER_STRATEGY.md` §6.
- **M6 reproduces exactly**, mechanism and scope: nine vacuous bundles (D6–D12 + I2 + I3), 89/180
  absent assignments, per-bundle source counts, and the self-triggering diagnosis (D1 marked stale by
  `tables/table1_experimental_params.tex`, header `% AUTOGENERATED by scripts/render_paper_tables.py`).
  The `UNMEASURABLE` repair in `check_bundle_source_freshness.py:175–199` is correct and I confirmed
  it fires on exactly those nine.
- **M5 reproduces exactly** (17/8, per-bundle distribution), and its "immaterial" conclusion is
  **stronger** than published: the commented regions contain **zero words of manuscript prose** —
  every one is `%% Lifted from …` / `%% TODO: lift content from …` bookkeeping. Un-commenting D1's
  four would render four empty headings, adding 0 % of publishable content, not 8 %.
- **`bundle_lean_module_coverage` genuinely does not exist**, and M2 is right that `SYNTHESIS.md`
  §5 item 5 describes it in the present tense. (It is listed as a *proposal* at
  `CROSS-absorbability-and-strategy-drift.md:734`: "**Add** a `bundle_lean_module_coverage` check".)
- **`GenericSUd*`**: 5 references, all in D8, four `.lean` filenames plus one `FKLW/GenericSUd*`
  glob — reproduced exactly, line for line.
- **`grep -rl "PinPlus" papers/` = 0.** The arc really is absent from the manuscript layer.
- The **un-homed band** reproduces (my 1 466–1 622 against the published 1 403–1 633), and the
  **denominator 2 039 is clean** — no import-only aggregate modules under `lean/SKEFTHawking/`, and
  the top-level `lean/SKEFTHawking.lean` aggregate is correctly outside the tree.

## Recommended dispositions

| finding | action |
|---|---|
| CRIT-1 | Strike "D11 and D12 reference zero Lean declarations" from `ADR-010:139`; re-measure the row with `\thm` recognised. |
| CRIT-2 | Widen `_PROSE_VERBATIM_ALIAS_DEF_RE` to match `\texttt` **anywhere in** the macro body. Add D11/D12 to the check's fixture set. Consider making the summary line report *unmatched verbatim macros* rather than only matched candidates — the systemic guard against a fourth instance. |
| CRIT-3 | Re-grade M2 from ❌ to "different population"; cite `CROSS-absorbability-…:192/:203/:971`. Re-justify `ADR-010` D5's scope on its own merits, not on the audit being wrong. |
| MAJ-4 | Extend the autogen filter to structure/inductive companions and re-state the arc size; or state the count as "modules", which reproduces at 164. |
| MAJ-5 | Re-run §M2's per-bundle table post-`\verb` **and** post-`\thm`; reconcile against §M4a. |
| MAJ-6 | Re-derive `ADR-010:138`'s table under a single predicate; add D11. |
| MAJ-7 | Delete or re-derive the `\input`-closure explanation. |
| MAJ-8 | Publish median alongside mean, or restrict the claim to the two bundles that carry it. |
| IMP-11 | Commit the measurement scripts under `docs/audits/2026-08-05-adr010-measurement/`. |
| others | Text corrections as described. |
