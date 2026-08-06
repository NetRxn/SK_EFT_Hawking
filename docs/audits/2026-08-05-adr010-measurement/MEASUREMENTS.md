# ADR-010 measurement pass — re-measuring the inherited figures

**Purpose.** [ADR-010](../../adrs/ADR-010-publication-portfolio-reassessment.md) was authored as a
*charter* on 2026-08-04, and its own EVIDENCE CLASS box records that nine load-bearing figures in
its §Context are **inherited from the 2026-08-01 audit and never independently checked**. The
charter names re-measuring them as *"the analysis's FIRST task, not a footnote to it"* (§C4).

This document is that pass. Every figure below is measured here, from the artifact, with the
**predicate stated** — per the standing rule that
[a count is meaningless without its predicate](../2026-08-05-pr-review-2/FINDINGS_REGISTER_PASS2.md).

**Status legend:** ✅ reproduces · ⚠️ reproduces but the predicate matters · ❌ does not reproduce.

| # | inherited claim | source | verdict |
|---|---|---|---|
| M1 | Tier-1 aggregate ~181 pp vs ~475 pp charter | `SYNTHESIS.md` §1 | ✅ **186 pp / 480 pp** |
| M2 | ~340 un-homed Lean modules across 10 arcs | `SYNTHESIS.md` §3 Class 6 | ❌ **1 403–1 633 of 2 039** |
| M3 | 8 fully-closed phases with no bundle home | `SYNTHESIS.md` §3 Class 6 | ⚠️ see M3 |
| M4 | D6/D9 share 78 identical Lean theorems; D4 §9 = 62 % of D8 | `CROSS-portfolio-coherence.md` | ✅ **78 exactly** / ⚠️ **62 % is a SIZE ratio** |
| M5 | 16 stub sections across 7 bundles, after the bibliography | `SYNTHESIS.md` §3 Class 4 | ✅ **17 / 8**, but immaterial |
| M6 | Stage-C absorption trigger dead for D6–D12 | `SYNTHESIS.md` §2 | ⚠️ **dead, wrong reason, 9 bundles** |

---

## M1 — page counts vs charter ✅ reproduces, and sharpens

**Predicate.** `pages` = `kMDItemNumberOfPages` of `papers/<code>/paper_draft.pdf`, **freshly
recompiled** (8 of 21 PDFs were stale against their `.tex` and were rebuilt with two `pdflatex`
passes before measuring — all 21 exit 0). `charter` = the *Length* column of `PAPER_STRATEGY.md`
§6, parsed from the table rather than hand-copied; a range is read at its **upper** bound.
`words` = whitespace tokens of the body after stripping the preamble, LaTeX comments, control
sequences, and everything from `\begin{thebibliography}` onward.

| code | tier | charter | pp | % charter | words | §§ | w/§ | w/pp |
|---|---|---|---|---|---|---|---|---|
| F | 0 | 80–150 pp | 23 | 15 % | 12 421 | 12 | 1 035 | 540 |
| D1 | 1 | ~40 pp | 10 | 25 % | 5 366 | 8 | 671 | 537 |
| D2 | 1 | ~30 pp | 11 | 37 % | 7 188 | 5 | 1 438 | 653 |
| D3 | 1 | ~50 pp | 59 | **118 %** | 12 103 | 30 | 403 | **205** |
| D4 | 1 | ~40 pp | 31 | 78 % | 7 607 | 10 | 761 | **245** |
| D5 | 1 | ~40 pp | 14 | 35 % | 7 706 | 12 | 642 | 550 |
| D6 | 1 | ~40 pp | 12 | 30 % | 7 649 | 7 | 1 093 | 637 |
| D7 | 1 | ~40 pp | 3 | **8 %** | 1 712 | 7 | 245 | 571 |
| D8 | 1 | ~45 pp | 9 | 20 % | 5 174 | 13 | 398 | 575 |
| D9 | 1 | ~40 pp | 12 | 30 % | 6 134 | 8 | 767 | 511 |
| D10 | 1 | ~40 pp | 5 | 12 % | 2 513 | 7 | 359 | 503 |
| D11 | 1 | ~40 pp | 9 | 22 % | 5 412 | 9 | 601 | 601 |
| D12 | 1 | ~35 pp | 11 | 31 % | 6 915 | 9 | 768 | 629 |
| L1 | 2 | 4 pp | 3 | 75 % | 1 736 | 3 | 579 | 579 |
| L2 | 2 | 4 pp | 4 | 100 % | 2 396 | 6 | 399 | 599 |
| L3 | 2 | 4 pp | 4 | 100 % | 1 901 | 3 | 634 | 475 |
| I1 | 3 | ~25 pp | 23 | 92 % | 9 898 | 14 | 707 | 430 |
| I2 | 3 | ~15 pp | 15 | 100 % | 5 060 | 9 | 562 | 337 |
| I3 | 3 | ~15 pp | 18 | **120 %** | 6 593 | 10 | 659 | 366 |
| E1 | 4 | 2–3 pp | 5 | **167 %** | 2 564 | 8 | 320 | 513 |
| E2 | 4 | 2–3 pp | 5 | **167 %** | 2 813 | 8 | 352 | 563 |

### M1.1 The aggregate reproduces

| tier | n | actual | charter | fill | words | words/bundle |
|---|---|---|---|---|---|---|
| 0 — flagship | 1 | 23 pp | 150 pp | **15.3 %** | 12 421 | 12 421 |
| 1 — deep | 12 | 186 pp | 480 pp | **38.8 %** | 75 479 | **6 290** |
| 2 — PRL | 3 | 11 pp | 12 pp | 91.7 % | 6 033 | 2 011 |
| 3 — infrastructure | 3 | 56 pp | 55 pp | **101.8 %** | 21 551 | **7 184** |
| 4 — experimental | 2 | 10 pp | 6 pp | **166.7 %** | 5 377 | 2 689 |

The audit's *"~181 pp against a ~475 pp charter"* is **confirmed** (186 / 480 here; the small delta
is the 8 stale PDFs it measured, and the upper-bound reading of ranges).

### M1.2 What the audit did not extract — three findings that change the diagnosis

**(a) Fill fraction is monotone in charter size, and only the D tier misses.** Tiers 2, 3 and 4 sit
at 92 %, 102 % and 167 %. The D tier sits at 39 % and the flagship at 15 %. This is not a
distribution of individual authoring failures — **every small container is filled or overfilled and
every large one is starved.** An explanation that runs through author effort has to explain why
effort correlates inversely with container size.

**(b) The "deep" tier is not deeper than the infrastructure tier.** By content rather than
typeset length, D-tier bundles average **6 290 words** and I-tier bundles average **7 184**. The
tier that exists to be long carries *less* prose per bundle than the tier that exists to document
tooling. Page count flatters the D tier because its `\input` closure carries more display maths;
words do not.

**(c) The charter number is a tier template, not an estimate.** **Nine of the twelve** D-tier
bundles carry the *identical* `~40pp` charter (D1, D4, D5, D6, D7, D9, D10, D11 — plus D2 at 30,
D3 at 50, D8 at 45, D12 at 35). A number that nine bundles share was not derived from nine
different substrates. It is the default that comes with the tier label.

> **This is the mechanism, stated in one line:** the charter page number is assigned **by tier
> convention at authorization time**, before any substrate is measured, and delivered length is
> essentially uncorrelated with it (~9–23 pp for everything that is not a 4 pp letter, whether the
> charter says 15 or 150). *"Late-stage work keeps pulling into D"* is therefore not a naming
> accident — **D is the tier whose template default is largest, so anything routed there
> automatically acquires a ~40 pp charter it was never sized against.**
>
> This is candidate generator **1** in ADR-010 §Context (*"authorization has no content floor"*),
> now with the evidence. It supersedes generator **2** (`BUNDLE_LIFT_PROCEDURE` §3a stubs) as the
> primary: §3a explains D3's *shape*, but D3 is the one bundle that **meets** its target — see (d).

**(d) The one bundle that hits its charter is the one that hits it by stitching.** D3 is at 118 %
of a 50 pp target with **205 w/pp** — less than half the corpus norm of ~550 — across **30
sections at 403 words each**. D4 is the same pattern at 245 w/pp. Page count is therefore not a
safe content floor on its own; whatever control D3 specifies must be density-aware, or it will
score the stitched lift as the portfolio's healthiest bundle. It currently does.

### M1.3 Side finding — commented-out `\section` stubs

Scanning `^\s*%+\s*\\section\{` anywhere in the body finds **24 stubs across 9 bundles**, against
the audit's *"16 across 7"*. The predicates differ (the audit counted only stubs **after the
bibliography**); M5 resolves the discrepancy. Distribution: D3 7, D1 4, D4 3, I1 3, D2 2, D5 2,
L1 1, L3 1, I2 1.

---

## M2 — un-homed Lean modules ❌ the inherited ~340 is low by 4–5×

**Predicate.** The audit's *"~340"* has **no recoverable predicate and no backing check** —
`bundle_lean_module_coverage`, which `SYNTHESIS.md` §5 item 5 says *"surfaces the ~340 unlifted
modules"*, **does not exist**; it is a proposed instrument, and `validate.py --list` has no such
check. So the figure cannot be reproduced, only replaced. Two predicates are measured here and
reported as a **band**, because the honest answer is bracketed rather than pointlike:

| | homing rule | homed | un-homed |
|---|---|---|---|
| **loose** | module leaf name, or any project-declaration leaf, appears anywhere in a bundle draft | 636 | **1 403 (68.8 %)** |
| **strict** | full dotted module name, or a declaration/module named inside a `\texttt{}`/`\lean{}` span, or the module named in a `source_manifest.md` | 406 | **1 633 (80.1 %)** |

Denominator = **2 039** `.lean` files under `lean/SKEFTHawking/` (2 012 of which declare
something). The loose rule deliberately **over**-counts homed — it accepts a bare leaf substring,
and 49 homed modules have a leaf of ≤ 8 characters, five of them literally `Basic`, which matches
ordinary prose. So **1 403 is a floor**: under any predicate a referee would accept, the un-homed
count is larger. Either way the inherited ~340 understates the gap by **4–5×**.

> ⚠️ **My first strict pass was itself wrong, in the same way the check was.** It read only
> `\texttt{}` and returned D8 = 0 and D9 = 0 modules referenced. Both bundles route every Lean
> reference through `\newcommand{\lean}[1]{\texttt{#1}}`. Correcting the predicate moved D8 to 37
> and D9 to 73. **The same blind spot was live in `prose_theorem_reference_coverage`** — 288
> references beyond the check while it reported PASS — fixed in `c7148779`.

### Modules referenced per bundle (strict)

| F | D1 | D2 | D3 | D4 | D5 | D6 | D7 | D8 | D9 | D10 | D11 | D12 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 37 | 16 | 55 | 55 | 60 | 29 | **8** | **4** | 37 | 73 | **3** | **9** | **0** |

| L1 | L2 | L3 | I1 | I2 | I3 | E1 | E2 |
|---|---|---|---|---|---|---|---|
| 3 | 13 | 3 | 55 | 46 | 51 | 7 | 18 |

**D12 references zero Lean modules.** D7 references four, D10 three, D6 eight. Read against M1:
the late-authorized D-tier containers are not merely short, they are **barely attached to the
substrate at all**. I3 alone (a Tier-3 infrastructure paper with a 15 pp charter) references 51 —
more than D6, D7, D10, D11 and D12 **combined** (24).

### Named arcs

| arc | declarations | modules | literal hits in bundle drafts |
|---|---|---|---|
| `PinPlus*` | **2 914** | 180 | **0** — confirmed absent portfolio-wide |
| `Smith*` | 395 | 20 | 9, but **every one a false positive** (`Tooby-Smith`, the PhysLean author, in I1's bibliography; "Smith homomorphism" prose in L2) |
| `Wu*` | 14 | 4 | 0 |
| `GenericSUd*` | 556 | 106 | 5, all in D8 — see below |

The audit's counts for this arc are **badly low**: it reported *"162 `PinPlus*` + ~88 Smith/Wu"*.
Measured against non-autogenerated project declarations: **2 914 `PinPlus*`** (18× the claim) and
**409 Smith/Wu**. Its *conclusion* — the entire Pin⁺ ℤ/16 arc has zero `papers/` hits — is
**correct and now much more consequential**, because the un-homed arc is an order of magnitude
larger than the audit believed.

**`GenericSUd*` — the audit's claim is half right and the half that fails is the load-bearing
half.** D8 does reference the substrate, five times, but **every one is a `\lean{...}` reference
to a FILE** (`GenericSUdQuantitative.lean`, `GenericSUdMatrixMercatorLog.lean`, …) plus one
family gesture, `\lean{FKLW/GenericSUd*}`. Against **556 declarations across 106 modules**, D8's
headline substrate reaches the manuscript as **four filenames and a glob**. The audit called it
"un-homed" and was wrong on the letter; the substance — that D8 does not actually present the
substrate it advertises — survives the correction intact.

---

## M3 — closed phases with no bundle home ⚠️ the premise is unmeasurable as stated

All eight named phases have roadmaps on disk (`docs/roadmaps/Phase{6h,6j,6k,6l,6q,6r,6r_prime,6s}_Roadmap.md`).
But **"a phase has no bundle home" is not a machine-answerable question today**, and that is
itself the finding: nothing associates a *phase* with a *bundle* except `PAPER_DRAFT_MAPPING.md`,
whose late-phase entries are synthetic tokens naming directories that do not exist (M6). So the
claim can be neither confirmed nor refuted from the artifacts — there is no join key.

What **is** measurable is M2's module-level result, which is the same finding at finer grain and
without the missing join: **1 403–1 633 modules reach no bundle draft.** ADR-010's D5 ("unabsorbed
work is homed or its absence is justified") should be keyed to modules, not phases, for exactly
this reason.

---

## M6 — the Stage-C absorption trigger ⚠️ dead as claimed, for a different reason, across 9 bundles

`scripts/check_bundle_source_freshness.py` read in full (233 lines) — the charter records that
its author had **not** read it.

**The audit's observation is right: the trigger cannot fire for the late bundles.** Its stated
mechanism — *"every bundle authorized since D6 is sourceless (no entries in
`PAPER_DRAFT_MAPPING.md`)"* — is **false**. Every one of D6–D12 has entries: D6 has 3, D8 has 13,
D7/D9/D10/D11/D12 have 1 each.

**The actual mechanism.** Those entries are **synthetic tokens naming directories that do not
exist** — `_phase6t_lean_only`, `_phase6w_W7_lean_only`, `D9_initial_draft`, `D12_initial_draft`.
`_latest_source_mtime()` returns `None` for a missing directory (`:63`), the staleness loop skips
any `None` (`if mt is not None and mt > last_lift`, `:161`), and control falls to the `else`
branch, which prints

> `fresh: all 1 source paper(s) older than last_lift (2026-06-10)` — with `passed=True`, `warning=False`

**a freshness verdict computed over zero measurable sources.** That is the string the audit quoted
verbatim; it read it as evidence of *no sources* when it is evidence of *unmeasurable sources
silently scored as fresh*. This is ADR-009's defect class — **absence of measurement rendered as
success** — living inside the absorption instrument itself.

**Scope is wider than the audit's.** Bundles whose sources are **100 % absent directories**, so
whose freshness verdict is entirely vacuous:

> **D6, D7, D8, D9, D10, D11, D12, and also I2 and I3** — **nine**, not seven.

Portfolio-wide, **89 of 180 source assignments (49 %) name a directory that does not exist.** Even
the bundles that *do* fire (D1 4/12 stale, D3 5/31, F 11/63) are computing over roughly half a
population.

### A second, independent defect in the same instrument: it is self-triggering

`_latest_source_mtime()` walks `rglob("*")` and takes the max mtime of **every** file, excluding
only dotfiles, `__pycache__`, and (when the source is itself a bundle) two bookkeeping files. It
therefore counts **generated** artifacts as author activity. Measured: the *only* file in
`papers/paper1_first_order/` modified since June is
**`tables/table1_experimental_params.tex` — a generated table** — and that alone is what marks D1
`freshness-stale`. LaTeX `.aux`/`.log`/`.pdf` output does the same.

So running the table pipeline, or compiling a draft, makes bundles report stale. **The instrument
reports its own side effects as evidence that an author changed something.** A signal that fires
on the tool's own action is one the reader learns to ignore — and per
`VALIDATION_GATE_TOPOLOGY.md` §3, a gate that fires on correct work gets switched off.

### What this means for ADR-010 D6

The charter's D6 requires the repair to follow `REMEDIATION_PLAN.md` §6a — *identify the defect
class → establish what existing machinery covers it, by reading the code → describe the residue →
request approval → only then build.* Steps 1–3 are now done and recorded above. **Step 4 is the
operator's**, so no new absorption instrument is built here.

Two residue items are separable, and only the first is a new instrument:

1. **NEW BUILD, needs approval** — a trigger that watches **Lean-module** mtimes for
   phase-sourced bundles. This is the audit's proposal and it is the right shape, but it is a new
   instrument and D6 gates it.
2. **BUG FIX, in scope** — a source whose directory is absent must report as **unmeasurable**,
   not silently fresh. This is `CheckResult.measured` applied to the instrument that most needs
   it, and it converts nine false greens into a visible gap **without** building anything. Applied
   below.

---

## M4 — the two claims the merge hypothesis rests on

ADR-010 §C3 calls these *"the two largest duplication findings"* and treats them as the evidence
that D6+D9 and D4/D8 *"are boundary failures between bundles that should not be separate."*
**One of them is that. The other is not duplication at all**, and the two need different remedies.

**Predicate.** For each bundle, the set of Lean **declaration names** it names inside a verbatim
span (`\texttt{}`, a preamble alias, or `\verb`) that **resolve to a real project declaration** in
`lean_deps.json`; pairwise intersection. Naming the same theorem is the evidence of a boundary
failure — naming the same *module* is much weaker. Text overlap is measured separately as
lowercase word 8-gram (shingle) intersection.

### M4(a) D6 ∩ D9 = **78 theorems** ✅ reproduces exactly

| | D6 | D9 |
|---|---|---|
| resolved declaration references | 175 | 169 |
| of which theorems | 147 | 150 |
| **shared with the other** | **85 refs / 78 theorems** | **85 refs / 78 theorems** |
| share of own references | **48.6 %** | **50.3 %** |

The audit's number is **exact**. This is a genuine, large boundary failure: two Tier-1 bundles
targeting the same journal, each naming ~half its Lean corpus in common with the other. **The
merge case for D6+D9 is real and is the strongest single result in this pass.**

> ⚠️ **My first measurement of this returned ZERO, and I nearly filed "the audit is wrong."**
> D6 writes its references as `\verb`, which my extractor did not read — the *same* blind spot as
> `prose_theorem_reference_coverage`. The project rule *a failed reproduction is itself a
> measurement that can be wrong* fired again, on the very claim that decides a merge. Fixed in
> `c5f384b4`; the corrected pass is what produced 78.

Two further pairs surfaced once `\verb` was visible, both **containment** rather than overlap:
**D3 ⊃ L3** (9 shared = 53 % of L3) and **D3 ⊃ L1** (8 shared = 62 % of L1). A 4 pp letter whose
substrate is ~60 % inside a 50 pp deep paper is a different question from D6/D9 — it is the normal
letter/long-paper relationship — but it bears on ADR-010's L1 disposition (§Open item 3).

### M4(b) D4 §9 vs D8 — ⚠️ the 62 % is a **size ratio**, and the texts share ~nothing

The audit's own wording (`CROSS-portfolio-coherence.md:172`) is *"3,206 words, which is 62 % of
D8's entire 5,186-word manuscript."* Re-measured: D4 §9 = **3 420 words**, D8 body = **5 285
words**, ratio **65 %**. The arithmetic reproduces.

**But it is a comparison of lengths, not a measure of shared content**, and ADR-010 §C3 inherited
it as the latter. Measured directly:

| | value |
|---|---|
| D4 §9 declaration references | 38 |
| D8 declaration references | 39 |
| **shared** | **3** (`cliffordT_accPt_one_unconditional`, `skLevel_polylog`, `solovayKitaev_dawson_nielsen_quantitative_..._unconditional`) |
| shared 8-gram shingles | **5 of 3 979 = 0.1 %** |

D4 §9 and D8 are **independently written treatments of the same subject** (quantitative
Solovay–Kitaev / gate compilation) over **almost disjoint substrate**. Merging them would remove
almost no duplicate text, because there is almost none.

**So the remedy differs from D6/D9's.** D6/D9 is duplication — one corpus presented twice, and a
merge deletes half of it. D4 §9 / D8 is a **priority and attribution conflict**: two containers
claiming the same *topic* while backing it with different theorems, which is resolved by deciding
who owns the claim and re-pointing the other, not by concatenation. ADR-010's distribution
recommendation must not treat them as one finding.

---

## M5 — stub sections ✅ reproduces (17/8 vs 16/7), and is **immaterial**

**Predicate.** `^\s*%+\s*\\section\{` — a commented-out sectioning command — split by position
relative to `\begin{thebibliography}`.

- **After the bibliography: 17 across 8 bundles** — D1 4, D4 3, I1 3, D2 2, D5 2, L1 1, L3 1,
  I2 1. The audit's *"16 across 7"* essentially reproduces; the extra bundle is I2.
- **Before the bibliography: 7, all in D3** — a distinct phenomenon (commented sections inside a
  live body) that the audit folded into the same number.

**The sub-claim that matters does not survive.** `SYNTHESIS.md` says D1 has four *"so part of its
73 % shortfall is self-inflicted commenting rather than missing work."* Measured, the commented
regions contain:

| bundle | stubs | commented words | live words | restoring them would add |
|---|---|---|---|---|
| D1 | 4 | 428 | 5 366 | **8 %** |
| D2 | 2 | 437 | 7 188 | 6 % |
| D4 | 3 | 416 | 7 607 | 5 % |
| D5 | 2 | 275 | 7 706 | 4 % |
| I1 | 3 | 312 | 9 898 | 3 % |
| L1 / L3 / I2 | 1 each | 97 / 102 / 95 | — | 6 % / 5 % / 2 % |

These are **placeholder headings with a sentence or two attached**, not withheld content.
Un-commenting all four of D1's would move it from 25 % of charter to about 27 % — two points of a
seventy-five-point gap. "Self-inflicted" is the wrong reading, and chasing it would spend
remediation effort on a distractor. The shortfall is missing work.
