# ADR-010 — Publication portfolio: purpose, distribution, and late-phase absorption

- **Status:** **PROPOSED — CHARTER ACCEPTED; MEASUREMENT PASS COMPLETE, ANALYSIS IN PROGRESS (2026-08-05).**
  This document was authored *before* the analysis it commissions, deliberately: the operator's framing
  and constraints were given in a live session and would otherwise be lost at the next compaction.
  §Decision states the *criteria and method* the re-assessment must satisfy. §Open records what is
  **not** decided — most importantly the roster number, which is **not** to be assumed.

  > ✅ **EVIDENCE CLASS — the re-measurement this box demanded is DONE, 2026-08-05.**
  > Full working, with every predicate stated:
  > [`docs/audits/2026-08-05-adr010-measurement/MEASUREMENTS.md`](../audits/2026-08-05-adr010-measurement/MEASUREMENTS.md).
  >
  > The prior revision recorded that **§Context's figures were inherited from the 2026-08-01 audit and
  > never independently checked**, and that re-measuring them was *"the analysis's FIRST task, not a
  > footnote to it."* Six were re-measured. The verdict is **not** that the audit was unreliable — it
  > is that **three of the six meant something different from what this ADR inherited**:
  >
  > | inherited | measured | consequence |
  > |---|---|---|
  > | Tier-1 ~181 pp vs ~475 pp | ✅ **186 / 480 pp** | holds; §Context (a)–(d) below now say *why* |
  > | ~340 un-homed modules | ⚠️ **different unit** — see CORRECTION below | the un-homed population is large, but the ❌ verdict is withdrawn |
  > | 162 `PinPlus*` modules | ✅ **164 files** — the audit was RIGHT | the earlier ❌ compared declarations to modules |
  > | D6/D9 share 78 theorems | ✅ **78, exactly** | the merge case for D6+D9 is real |
  > | D4 §9 = 62 % of D8 | ⚠️ **true, but a SIZE ratio** | texts share **0.1 %**; not duplication — see C3 |
  > | 16 stub sections / 7 bundles | ✅ **17 / 8** — but ≤ 8 % of any bundle | immaterial; drop from remediation |
  >
  > **Two further findings came out of the pass and are not in the audit at all:** the fill-vs-charter
  > gradient that identifies the D-tier mechanism (§Context), and the fact that the absorption
  > instrument's failure has a *different cause* than the audit assigned it (§Context, M6).
  >
  > ⚠️ **CORRECTION 2026-08-06 — two figures above were WRONG, both mine.** Full working:
  > [`MEASUREMENTS.md` §CORRECTIONS](../audits/2026-08-05-adr010-measurement/MEASUREMENTS.md).
  >
  > 1. **"D11 and D12 reference zero Lean declarations" is FALSE** — an extraction artifact. Both
  >    route every reference through a `\thm{}` wrapper the extractor could not see. Re-measured:
  >    **D11 = 95 declarations / 22 modules, D12 = 132 / 13.** No bundle references zero. The
  >    inference that late authorization yields substrate-detached containers is WITHDRAWN.
  > 2. **"the audit's ~340 is low by 4–5×" was a UNIT SWAP.** The audit said 162 `PinPlus*.lean`
  >    **modules**; there are **164** — a 1.2 % difference. The re-measurement compared
  >    **declarations** to **modules** and reported the ratio as the audit's error.
  >
  > **The re-measurement was, repeatedly, a correction of the measurer.** Reading only `\texttt{}`
  > — the assumption the validation suite itself shipped — made D8/D9 look like they referenced
  > **zero** Lean modules and made D6 ∩ D9 come out **0** instead of 78. Filing "the audit is wrong"
  > off that would have killed the best-evidenced merge in the portfolio. Fixed across `c7148779`,
  > `c5f384b4` and `39e7ac3a`; see §Consequences.
  >
  > **What survives both corrections: M1's length finding, M4a's 78 shared theorems, M5 and M6 —
  > so the D6+D9 merge case, which the portfolio decision actually turns on, is untouched.**
  **No roster change, no `PAPER_STRATEGY.md` edit and no manuscript edit is authorized by this ADR.**
- **Decider:** John Roehm (project owner). Direction given 2026-08-04:
  > *"My intent is to publish the strongest form of any paper we deliver. I've noticed that the naming
  > convention & late stage work keeps pulling into D (depth) but then we regularly don't have anywhere
  > near enough content (e.g., 60pg turns into 11pgs). I'm not going to dictate the spread — I'd like a
  > strategic re-assessment of the purpose of all of the papers, in context of the absorbed & unabsorbed
  > roadmap work, and a recommendation on an optimal distribution, as well as a more solidified plan for
  > late phase absorption into the plan. Remember, the original strategy was written before many
  > different avenues we started to deliver on. The big picture wasn't re-evaluated."*
- **Sequencing (operator ruling, same session):** **the QA/QI infrastructure must be re-solidified and in
  place first.** [ADR-009](ADR-009-validation-suite-modularization.md) closes and merges before the
  portfolio analysis begins. The dials this ADR's recommendations will be measured by are the ones
  ADR-009 is currently repairing; recommending against broken instrumentation repeats the failure that
  produced the audit.
- **Scope:** the purpose, boundaries, count and sequencing of the publication bundles; the mechanism by
  which late-phase work reaches a bundle; and the process rules that govern bundle authorization.
  **Out of scope:** the content of any individual manuscript (that is the remediation goal that follows),
  the validation suite (ADR-009), and Claude-Code onboarding (ADR-008, deferred).
- **Related:** [`docs/PAPER_STRATEGY.md`](../PAPER_STRATEGY.md) (the document under re-assessment) ·
  [`docs/PAPER_DRAFT_MAPPING.md`](../PAPER_DRAFT_MAPPING.md) ·
  [`docs/BUNDLE_LIFT_PROCEDURE.md`](../BUNDLE_LIFT_PROCEDURE.md) ·
  [`docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md`](../LATE_PHASE6_ABSORPTION_PROTOCOL.md) ·
  [`docs/audits/2026-08-01-publication-readiness/`](../audits/2026-08-01-publication-readiness/)
  (SYNTHESIS · REMEDIATION_PLAN · CROSS-portfolio-coherence · CROSS-absorbability-and-strategy-drift ·
  CROSS-build-integrity · 10 per-bundle reports) ·
  [`docs/audits/2026-08-05-adr010-measurement/MEASUREMENTS.md`](../audits/2026-08-05-adr010-measurement/MEASUREMENTS.md)
  (**this ADR's own evidence base** — every §Context figure re-measured with its predicate stated) ·
  `scripts/bundle_registry.py` (the machine roster) ·
  Pipeline Invariant #14 (`WAVE_EXECUTION_PIPELINE.md:689`).

---

## Context

### The pathology the operator named

**Late work keeps being authorized into Tier-1 "deep" containers that then never reach their charter.**
The roster grew 13 → 14 → 15 → 16 → 17 → 18 → 20 → 21 by successive authorizations
(`PAPER_STRATEGY.md:27` records the full chain), each adding a *depth* paper. Re-measured 2026-08-05:
**Tier-1 aggregate is 186 pp against a 480 pp charter — 39 %** (the audit's ~181/~475 reproduces). A
40 pp target ships as 10; D7's ships as **3**. Only **D3** meets its page target, and it does so at less
than half the corpus's words-per-page — see (d). *(D3's LaTeX no longer fails: the undefined `\Imm` was
fixed under ADR-009 and all 21 bundles now compile clean, so the audit's "the one bundle that does not
compile" is superseded.)*

This is a *structural* outcome, not a series of individual authoring failures, and the re-assessment must
name the mechanism rather than the symptom. Three candidate generators were documented. **The
2026-08-05 measurement pass adjudicates between them** — generator 1 is the primary, 3 is its enabler,
and 2 explains a different symptom than the one it was assigned to.

1. **Authorization has no content floor. ← PRIMARY, now evidenced.** Invariant #14 requires user
   authorization to add a bundle target, but nothing at authorization time asserts that substrate exists
   to fill it. A bundle is created, then hopefully filled.
2. **`BUNDLE_LIFT_PROCEDURE` §3a inserts one section stub per source.** Real, but it explains *shape*,
   and the bundle it best describes — D3, 30 sections, 205 w/pp against a ~550 corpus norm — is the one
   bundle that **exceeds** its page charter. §3a is therefore the generator of *padding*, not of the
   shortfall. Both need controls, and they are different controls.
3. **Nothing measures the gap continuously.** Confirmed: page-count vs charter is computed nowhere. This
   is what lets generator 1 run undetected for the ~15 months between authorization and review.

### The measurement that identifies the mechanism

Fill fraction against charter, by tier (2026-08-05, freshly recompiled PDFs):

| tier | n | actual | charter | **fill** | words / bundle |
|---|---|---|---|---|---|
| 0 — flagship | 1 | 23 pp | 150 pp | **15 %** | 12 421 |
| 1 — **deep** | 12 | 186 pp | 480 pp | **39 %** | **6 290** |
| 2 — PRL | 3 | 11 pp | 12 pp | 92 % | 2 011 |
| 3 — infrastructure | 3 | 56 pp | 55 pp | **102 %** | **7 184** |
| 4 — experimental | 2 | 10 pp | 6 pp | **167 %** | 2 689 |

Three things follow, none of which is in the audit:

**(a) Fill is monotone in charter size, and only the big containers miss.** Every tier with a small
charter is filled or overfilled. Any explanation running through author effort has to explain why effort
correlates *inversely* with container size.

**(b) The "deep" tier is not deeper than the infrastructure tier.** By words rather than typeset length,
D-tier bundles average **6 290** and I-tier bundles **7 184**. The tier that exists to be long carries
*less* prose per bundle than the tier that exists to document tooling.

**(c) The charter number is a tier template, not an estimate.** **Nine of the twelve** D-tier bundles
carry the *identical* `~40pp` charter. A number nine bundles share was not derived from nine different
substrates.

> **The mechanism, in one line.** The charter page number is assigned **by tier convention at
> authorization time, before any substrate is measured**, and delivered length is essentially
> uncorrelated with it — ~9–23 pp for everything that is not a 4 pp letter, whether the charter says 15
> or 150. So the operator's *"naming convention keeps pulling into D"* is not a naming accident:
> **D is the tier whose template default is largest, so anything routed there automatically acquires a
> ~40 pp charter it was never sized against.** The shortfall is created at authorization, not at
> authoring.

**(d) A page-count floor alone would score the portfolio backwards.** D3 meets 118 % of its charter at
**205 w/pp** — under half the corpus norm — across 30 sections averaging 403 words. D4 is the same
pattern at 245 w/pp. Whatever control D3 specifies must be **density-aware**, or the stitched lift ranks
as the healthiest bundle in the portfolio. It currently does.

### The substrate attachment is worse than the length gap

Declaration-level references that resolve to real project theorems, per bundle:

| D12 | D10 | D7 | D6 | D8 | D9 | D3 |
|---|---|---|---|---|---|---|
| **0** | 3 | 20 | 175 | 39 | 169 | 175 |

⚠️ **WITHDRAWN 2026-08-06 — this paragraph was an extraction artifact.** It read "D11 and D12
reference zero Lean declarations. D10 references three." Re-measured after the verbatim repairs:
**D6 = 153, D7 = 11, D8 = 37, D9 = 150, D10 = 34, D11 = 95, D12 = 132** declarations. No bundle
references zero; the thinnest is D7 at 11. There is no substrate-attachment finding here, and the
length finding in M1 stands on its own without it.

### The strategy document predates most of what was delivered

`PAPER_STRATEGY.md` describes "twenty-one publication targets" (`:27`) but its architecture section still
frames Tier 1 as twelve themed deep papers whose boundaries were drawn before Phases 6AA–6EE existed. The
audit found the drafts are in several places **more honest than the strategy document describing them**
(`SYNTHESIS.md` §4): D5's measured 0.83σ/1.04σ against the charter's advertised 3.5–5.7σ; I3's §8.9
withdrawal against §2.4's priority claims. *"Where they conflict, the strategy doc is usually the thing
that needs fixing."*

### Work that has no home

- **1 403–1 633 of the 2 039 Lean modules appear in no bundle draft** — measured 2026-08-05 as a band
  between a deliberately generous and a strict homing predicate, because the honest answer is bracketed.
  The inherited *"~340"* is low by **4–5×**, and had **no recoverable predicate and no backing check**:
  `bundle_lean_module_coverage`, which `SYNTHESIS.md` §5 says *"surfaces the ~340 unlifted modules"*,
  **does not exist**.
- The **8 fully-closed phases** (6h, 6j, 6k, 6l, 6q, 6r, 6r′, 6s) all have roadmaps, but *"a phase has
  no bundle home"* is **not machine-answerable today** — nothing joins a phase to a bundle except
  `PAPER_DRAFT_MAPPING.md`, whose late-phase entries name directories that do not exist (see below). D5
  should therefore be keyed to **modules**, which are measurable, not phases, which are not.
- The **entire Pin⁺ ℤ/16 arc** is un-homed and is far larger than the audit believed: **2 914
  `PinPlus*`** declarations across 180 modules (not 162) and **409 Smith/Wu** (not ~88), with **zero**
  `papers/` hits — that half of the claim is confirmed exactly.
- **`GenericSUd*` — the audit was wrong on the letter and right on the substance.** D8 *does* reference
  it, five times, but every reference is to a **file** (`\lean{GenericSUdQuantitative.lean}`) plus one
  glob, `\lean{FKLW/GenericSUd*}`. Against **556 declarations across 106 modules**, D8's advertised
  headline substrate reaches the manuscript as four filenames and a wildcard.
- **17 commented-out stub sections across 8 bundles sit after the bibliography** (the audit's "16 across
  7" reproduces). ⚠️ **But the sub-claim that D1's *"73 % shortfall is self-inflicted commenting"* does
  not survive:** the commented regions hold **95–437 words each**, ≤ 8 % of any bundle's live text.
  Restoring all four of D1's would move it from 25 % of charter to ~27 %. These are placeholder headings,
  not withheld content — **drop this from the remediation plan; it is a distractor.**

### Late-phase absorption is structurally dead for the newer half of the roster

`LATE_PHASE6_ABSORPTION_PROTOCOL`'s Stage-C trigger **does not fire for the late bundles** — the audit's
observation, confirmed. **Its stated mechanism is wrong, and the correct one is worse.**

The audit said *"every bundle authorized since D6 is sourceless (no entries in
`PAPER_DRAFT_MAPPING.md`)."* Every one of D6–D12 **has** entries: D6 has 3, D8 has 13, the rest 1 each.

What is actually true (`check_bundle_source_freshness.py` read in full, 2026-08-05 — the prior revision
of this ADR recorded that its author had **not** read it): those entries are **synthetic tokens naming
directories that do not exist** — `_phase6t_lean_only`, `D9_initial_draft`, `D12_initial_draft`.
`_latest_source_mtime()` returns `None` for a missing directory, the staleness loop skips every `None`,
and control falls to the `else` branch, which announces

> `fresh: all 1 source paper(s) older than last_lift (2026-06-10)` — `passed=True`, `warning=False`

**a freshness verdict computed over zero measurable sources.** That is the exact string the audit quoted;
it read it as evidence of *no sources* when it is evidence of *unmeasurable sources silently scored as
fresh*. This is ADR-009's defect class — **absence of measurement rendered as success** — living inside
the absorption instrument.

**Scope is wider than the audit's: nine bundles, not seven** — D6–D12 **plus I2 and I3**. Portfolio-wide,
**89 of 180 source assignments (49 %) name a directory that does not exist**, so even the bundles that
*do* fire were computing over roughly half a population (D3 reported "5 of 31"; it is truthfully 5 of 22).

**A second, independent defect in the same instrument: it is self-triggering.** `_latest_source_mtime()`
takes the max mtime of *every* file under a source directory, so it counts **generated** artifacts as
author activity. The only file in `papers/paper1_first_order/` modified since June is
`tables/table1_experimental_params.tex` — a generated table — and that alone is what marks D1
`freshness-stale`. LaTeX `.aux`/`.log`/`.pdf` output does the same. **The instrument reports its own side
effects as evidence that an author changed something**, and per `VALIDATION_GATE_TOPOLOGY.md` §3 a gate
that fires on correct work gets switched off.

The vacuous-PASS half is **fixed** (`9f62deaa`): an absent source directory now reports `UNMEASURABLE` at
WARN rather than claiming freshness, which converts nine false greens into a visible gap. The trigger the
late bundles actually need — one that watches **Lean-module** mtimes — is a **new instrument** and stays
gated behind D6 / `REMEDIATION_PLAN.md` §6a's approval step. Not built.

### Two documents disagree with the live roster

- **Pipeline Invariant #14** (`WAVE_EXECUTION_PIPELINE.md:689`) enumerates
  `F, D1–D9, L1–L3, I1–I3, E1, E2` — *"18 targets as of the 2026-06-10 D9 authorization"* — an enum that
  **cannot legally hold D10, D11 or D12**. Verified directly 2026-08-04.
- **`PAPER_STRATEGY.md:341`** still carries *"All 14 bundles have shipped Stage 9 + Stage 10 + Stage 13
  reviewer triples GREEN"* from 2026-05-07.

Both are instances of the audit's own finding **X-14**: roster count/membership stale across 36 doc and
script sites, *including three rule texts*.

---

## Constraints — verified, and load-bearing for any recommendation

### C1. The roster is machine-gated in three legs. A number is not a change-set.

`validate.py --check bundle_registry_consistency` (`scripts/validation/checks/bundles_readiness.py:745`,
read in full 2026-08-04) enforces the single source of truth in three independent legs. **Any roster
change must move all of them together or the suite goes red:**

- **Leg A — documentary agreement.** `bundle_registry.parse_strategy_roster()` parses
  **`PAPER_STRATEGY.md` §6 "Summary table"** into `{code: tier}` and requires exact equality with the
  registry, on **codes *and* tiers**. A bundle authorized in the strategy doc but never registered — or
  registered but absent from §6 — fails here. This is the leg with teeth for the actual failure mode.
- **Leg B — consumer agreement.** Every module in `_ROSTER_CONSUMERS` must expose bundle-keyed attributes
  whose key sets equal the registry's **exactly**. Seven modules today:
  `sentence_state` (`_VALID_BUNDLE_TARGETS`) · `validate` (`BUNDLE_CODES`) ·
  `bundle_readiness` (`_BUNDLE_ORDER`, `_TIER_OF`) · `review_runner` (`TIER_OF`) ·
  `bundle_source_manifest` (`_TIER_OF`, `_BUNDLE_TITLES`, `_BUNDLE_TARGET_JOURNAL`, `_BUNDLE_SUBPHASE`) ·
  `datastar_bundles` (`_TIER_OF`, `_BUNDLE_TITLES`) · `aristotle_usage_by_bundle` (`ALL_BUNDLES`).
- **Leg C — no re-hardcoding.** An AST walk over `scripts/*.py` fails any literal dict/list/tuple/set
  holding **≥ 6** distinct bundle codes outside `bundle_registry.py`. This is the leg that stops the
  *next* authorization from regressing the seven-places problem.

The gate exists because the roster **was** hardcoded in seven places, and every omission failed *silently
and differently* — `validate.py` skipped D10 in the one check that catches Lean theorem-name drift in
prose; `bundle_readiness.py` rendered 19 of 21 bundles while looking complete. **ADR-010's recommendation
must therefore ship as a complete change-set — §6 table, registry, seven consumers, Invariant #14's enum,
and the 36 prose sites — not as a target number.**

### C2. The live roster is 21. Nothing on disk supports 14.

`scripts/bundle_registry.py → BUNDLE_CODES` = **21**, verified 2026-08-04:
`D1–D12, E1, E2, F, I1–I3, L1–L3`.

A prior session recorded a *"roster decision: 21 → 14 (author's call, operator delegated)"*. **That figure
is unsupported by any document in the repository and must not be carried forward.** It is additionally one
of the stale counts the audit itself files as **P0 defect X-11** (*"Manuscripts state the roster as 14, 15
and 17"*). Correction recorded 2026-08-04.

### C3. The audit's own recommendation is 21 → 16 — as INPUT, not a conclusion.

Stated twice, in detail:
- `SYNTHESIS.md` §5 **D-1** — *"Roster consolidation, 21 → 16."*
- `CROSS-portfolio-coherence.md` §6.4 — *"Recommended roster — 16 targets"*, with a full per-target table
  and estimated page deltas.

The proposed merges: **D6+D9+D12 → D6★** (device/network certification stack) · **D10+D11 → D10★**
(condensed-matter/molecular substrate) · **E1+E2 → E★** · **D7 folded into D1** · **D4 §9 → D8**.
21 − 5 = 16. Rationale: the two largest duplication findings (D6/D9 sharing 78 identical Lean theorems;
D4 §9 = 62 % of the entire D8 manuscript, with both papers asserting priority over it) **are boundary
failures between bundles that should not be separate**.

> ⚠️ **CORRECTED 2026-08-05 — this rationale calls them "the two largest duplication findings", and only
> one of them is a duplication finding.**
>
> - **D6/D9 is duplication, and the number is exact.** Measured: D6 and D9 share **85 resolved
>   declaration references, of which exactly 78 are theorems** — **48.6 % of D6's** corpus and **50.3 %
>   of D9's**. Two Tier-1 bundles targeting the same journal, each naming half its Lean corpus in common
>   with the other. **The strongest single result in the measurement pass, and the merge case for D6+D9
>   stands on it.**
> - **D4 §9 / D8 is NOT duplication.** The audit's own wording is *"3 206 words, which is 62 % of D8's
>   entire 5 186-word manuscript"* — **a comparison of lengths**, which this ADR inherited as a measure
>   of shared content. Measured directly, they share **3 of 38 declaration references** and **5 of 3 979
>   text shingles (0.1 %)**. They are **independently written treatments of the same subject over almost
>   disjoint substrate.**
>
> **The two therefore need different remedies, and the recommendation must not fuse them.** Merging
> D6+D9 deletes a duplicated corpus. Merging D4 §9 into D8 would delete almost nothing, because there is
> almost nothing shared — what is actually wrong there is a **priority and attribution conflict**: two
> containers claiming the same *topic* while backing it with different theorems. That is resolved by
> deciding who owns the claim and re-pointing the other, not by concatenation.
>
> A third pattern surfaced that the audit did not record, and it is **containment, not overlap**:
> **D3 ⊃ L3** (53 % of L3's references) and **D3 ⊃ L1** (62 % of L1's). That is the normal
> letter/long-paper relationship rather than a defect, but it bears on §Open item 3 (L1's disposition).

The audit also records what it would *not* do: *"shrink the targets to match the current drafts… would be
the walk-back this project's own remediation posture forbids."*

**This is a starting hypothesis to evaluate against the substrate, not a decision to ratify.**

### C4. The analysis must be done from the substrate, by the author, with the content actually read.

Operator constraint, given explicitly (2026-08-04):

> *"I'm really worried about you making decisions on the most appropriate way to combine the papers since
> the content is clearly not in your context."*

Accordingly: **no merge, split or retirement may be recommended on the strength of a summary, a bundle
name, an audit table, or a subagent report.** Each recommendation must rest on the manuscripts and the
Lean modules themselves, read directly. Where a recommendation rests on something not read, it must say
so. This mirrors the standing lesson already recorded in `QA_QI_INFRASTRUCTURE_MAP.md` §9 — *a filed
finding's blast radius is a claim, not a measurement* — which this workstream has now violated twice and
caught twice.

### C5. Claim strength is not the flexible variable.

Governing posture, unchanged (`REMEDIATION_PLAN.md` §0, memory `feedback-remediation-build-dont-walkback`):
**the publication schedule moves; the claims do not.** A container may be resized because the substrate
is genuinely a different shape than the charter assumed — never because resizing is the cheap way to make
a shortfall disappear. The distinction is the whole subject of `REMEDIATION_PLAN.md` §0 and must be
explicit in every recommendation this ADR makes.

---

## Decision

### D1 — ADR-010 is a document, and its execution is a separate goal

The deliverable is **this ADR, completed**: a researched, densely-linked analysis a later goal can execute
from. This ADR's own completion **does not** edit `PAPER_STRATEGY.md`, `PAPER_DRAFT_MAPPING.md`,
`bundle_registry.py`, Invariant #14, or any manuscript. Separating analysis from execution is deliberate:
the roster change is a coordinated multi-file change-set (C1) that should be reviewed as a plan before it
is made as a diff.

### D2 — Every target gets a re-derived purpose statement

For each of the 21 current bundles, the analysis states: **audience, venue, the claim only this container
can make, the substrate that backs it (named Lean modules / phases), and its honest current size against
its charter.** Re-derived from what exists now — *not* inherited from `PAPER_STRATEGY.md`, which predates
most delivered avenues and was never re-evaluated as a whole (§Context).

A target whose purpose cannot be stated without reference to another target's substrate is a boundary
failure and must be named as one.

### D3 — The D-tier gravity pathology is diagnosed at the mechanism, and a control is specified

The analysis must (a) identify which of the three candidate generators in §Context actually produces the
shortfall — with evidence — and (b) specify the control that stops recurrence. A control is acceptable
only if it is *checkable*: a rule that depends on an author remembering it is the state we are already in.

Explicitly in scope for the control: **a content floor at authorization time** (does substrate exist to
fill this container before it is created?), and **continuous measurement of size against charter** rather
than discovery at review.

### D4 — Distribution is recommended per-target, with the merge/split/retire decision justified individually

Not a headline number. For each proposed change: what moves, why the substrate says so, what the
resulting container's charter becomes, and what breaks (C1's change-set). The audit's 21 → 16 is the
starting hypothesis (C3); departures from it are expected and must be argued.

### D5 — Unabsorbed work is homed or its absence is justified

The ~340 modules, the 8 closed phases, the Pin⁺ ℤ/16 arc and the `GenericSUd*` substrate each get a
destination or a written reason they have none. "No home" is an acceptable outcome — *"defensive
publication of the substrate, not a paper"* is a legitimate disposition — but it must be a decision, not
an omission.

### D5a — INTAKE ARCHITECTURE (operator authorization, 2026-08-06)

The operator has **authorized shifting publication content and strategy** — including re-tiering
(a "D" whose substrate is really a letter) — to distribute correctly and to map the **entire
roadmap portfolio** into the publication strategy. This supersedes the earlier "no roster change
authorized" line **for content/strategy**; §C1's machine-roster change-set discipline still binds.

The stated requirement is not a one-time re-sort. It is that **new roadmaps in arbitrary domains
must onboard ergonomically** — absorbing into existing work or creating a publication — **without
breaking the structure ADR-010 builds**.

**Design (full working: `docs/architecture/.working-docs/PUBLICATION_INTAKE_DESIGN.md`).** A
bundle **declares its apex theorems**; its substrate is the **derived transitive closure** of
those apexes from `lean_deps.json` (verified computable: one real theorem yields 1 128 deps across
72 modules, zero extraction timeouts). Absorption, un-homed detection, cross-bundle overlap and —
critically — **content sufficiency** all become consequences of that single join.

This is what makes **tier a function of substrate shape**: one apex over a shallow closure is a
letter; several interlocking apexes over a deep closure is a deep paper. That is the inversion
§Context's mechanism finding demands, and it is why the earlier "arc map" idea is **RETRACTED** —
measured, neither directories nor name prefixes partition the substrate, so an arc map would be a
hand-maintained heuristic.

⚠️ **Unsolved, operator-flagged:** the atlas/apex concept postdates papers/bundles, and there is
**no streamlined way to create apex nodes when a new roadmap or phase is built out**. Proposed
hook is **wave close** — the moment of maximum author context. Retrofitting existing bundles is
authorized **only with full per-bundle context review** (contributing roadmaps, cited Lean,
claims record), one bundle at a time.

⚠️ **Hard constraint:** closures, apexes and un-homed substrate must **emit graph nodes/edges** so
human review of the final product is not a secondary conversation. Read `scripts/build_graph.py`'s
extractor contract before fixing the shape.

#### D5a status — measured and partly BUILT (2026-08-06)

**Three of the design's four open questions are closed by measurement**
(`docs/audits/2026-08-06-closure-probe/FINDINGS.md`; the probe reproduces §M4(a)'s independent
**D6 ∩ D9 = 78** exactly before anything rests on it):

- **Overlap is meaningful after all.** 70 % of homed declarations sit in exactly ONE bundle's
  closure and maximum ubiquity across 21 bundles is **7**. No shared-foundations blob, so raw
  closure is already distinctive — `name_deps_project` is project-closed (0 of 279 602 edges leave
  `SKEFTHawking`), which excludes Mathlib upstream.
- **Un-homed ≈ 1 400 modules, robustly.** Closure homes 631 modules where §M2's loose rule homed
  636 and its strict rule 406 — two unrelated mechanisms landing within 2 of each other. Closure
  homes **2.3×** what direct reference does (631 vs 275).
- **Closures cross bundles sparsely.** D6∩D9 Jaccard **0.482** — the one entangled pair, and the
  pair the portfolio decision turns on — against 0.146 / 0.135 / 0.000 elsewhere.

**Closure shape flags three targets whose tier does not match their substrate:** **L2** is a letter
on a deep-paper substrate (39 modules, depth 14), and **D7** and **D1** are shaped like letters.
That is a signal about where to look under D4, not a decision — tier is also a claim about audience.

**Built:** `scripts/bundle_closure.py` (derivation), `bundle_apex_resolves` (gate on the one
hand-maintained input), and the graph integration §D5a's hard constraint requires — `CLAIMS_APEX`
edges plus a closure **overlay** on Lean/module/Paper nodes, following `_overlay_atlas`'s
view-not-store precedent rather than adding ~10 k links to a 14 040-edge graph. Shape and remaining
sequencing: `docs/architecture/.working-docs/PUBLICATION_INTAKE_SHAPE.md`.

**Nothing is declared yet, deliberately** *(as of 2026-08-06)*. An undeclared bundle's substrate is
**UNKNOWN, not empty**, and the check returns `measured=False` rather than a clean pass. Apex
retrofit stays gated on the operator's per-bundle full-context review condition above.

> ✅ **SUPERSEDED 2026-08-07 — the retrofit is COMPLETE.** All 21 bundles declare apexes,
> `UNDECLARED_APEX_CEILING = 0`, and every apex resolves (`bundle_apex_resolves` clean). Each was
> declared under the per-bundle full-context review this section requires, with a `FINDINGS.md`
> per bundle under `docs/audits/2026-08-0{6,7}-*-retrofit/`. Closure is therefore measurable
> portfolio-wide, which is what made the §D4 adjudication below possible.

⚠️ **Closure truncates at `private` declarations** — `ExtractDeps` omits them, so 553 distinct
targets (1 278 edges, 0.46 %) stop a walk. Bounded, but `closure_truncated_private` travels with
every published closure size; a size reported alone reads as complete when it is not.

### D6 — Late-phase absorption is repaired, not merely described

The analysis specifies: how a sourceless bundle (D6–D12 today) acquires a working freshness trigger; what
`check_bundle_source_freshness.py` must track instead of source-paper mtimes (Lean-module mtimes are the
audit's proposal, and must be evaluated rather than assumed); and how the content floor from D3 is
measured continuously. Any instrument proposed here follows `REMEDIATION_PLAN.md` §6a's standing rule —
**identify the defect class → establish what existing machinery covers it, by reading the code → describe
the residue → request approval → only then build.** Never build before the third step.

### D7 — Process-document drift is corrected as part of the change-set

Invariant #14's 18-target enum, `PAPER_STRATEGY.md:341`'s "All 14 bundles", and the 36-site roster drift
(X-14) are listed with their fixes. The mechanism that let a *rule text* go stale is itself a finding: a
rule enumerating a roster is a hardcoded roster, and Leg C exists because that pattern is known-bad in
code. Whether the same discipline should apply to prose is an open question for D3's control.

---

## Open — NOT decided by this ADR

1. ✅ **DECIDED 2026-08-09 — the roster is 21, unchanged.** `SYNTHESIS.md` §5 listed D-1 among
   *"decisions required from the operator"*; the operator declined to dictate the spread twice, and
   on 2026-08-09 delegated the call outright — *"entirely your call how this gets divided up,
   provided it's organized professionally and coherently, and lends itself to expansion / absorption
   as new work lands over time."* **21 is the answer, and it is an output rather than a target:**
   every one of the audit's six proposed merges was tested against the manuscripts read in full and
   all six fail (§D4 adjudication), and the one retirement not proposed by the audit — L1 — was
   itself reversed on evidence (item 3). The three delegated criteria are met by the *idiom*, not by
   the number: the portfolio is organized as **splash/deep pairs** (L1/D3, L3/D3, E1/D1, E2/D1,
   declared in print four times), which is exactly the structure that absorbs new work — a new wave
   lands in the deep container and the splash re-points at it, with no roster change. **Do not carry
   "14", "16" or "20".**
2. ✅ **ANSWERED 2026-08-08 — ship it, and the redundancy worry is refuted.**
   `molecularHamiltonian_essSelfAdjoint` is live and kernel-pure with all three formerly-disclosed
   inputs discharged, so there is nothing to wait for. And **PhysLib does not make the in-tree
   Kato–Rellich redundant**: measured against the resolved package at pin `c4843367`, the strings
   `Kato`, `Rellich`, `relBound` and `RelativelyBounded` occur **nowhere** in it. PhysLib supplies
   `IsEssentiallySelfAdjoint` as a definition plus the von Neumann *defect-index* criterion — a
   different and, for a molecular many-body Coulomb Hamiltonian, harder route. D10 built the
   theorem the library does not have.
3. ⚠️ **ANSWERED 2026-08-08 — then REVERSED 2026-08-09. KEEP L1.** The retirement argument is
   retained in full at [`ADJUDICATION.md`](../audits/2026-08-08-adr010-d4-adjudication/ADJUDICATION.md) §5
   because how it failed matters more than that it failed. Both premises were refuted **by a
   document already on disk**: `papers/D3:662-663` states in print that L1 ships the same content
   as a four-page PRL splash of D3, so the shared declarations are the *design*; and L1 is the only
   bundle in the portfolio whose draft length matches its charter, in a portfolio whose named
   pathology is under-filled containers. The retirement was ruled from the EVIDENCE ledger's
   *summary* of the L1 retrofit rather than the retrofit itself — the same substitution the D6/D9
   analysis in this ADR exists to warn against — and it applied **inconsistent standards inside one
   document**, treating E1/E2's identical splash overlap as legitimate design and L1's as
   redundancy. The one real defect is a prior-art gap (no 2017 GW170817-constraint citations),
   tracked as TODO-D34.
4. ✅ **ANSWERED 2026-08-08 — disclose and ratchet, per bundle.** Measured: **five bundles carry
   `native_decide` in their declared-apex closure** (D4 19, L2 6, F 3, D2 3, I2 1 — 32 total), and
   **all five already disclose it in prose**; the other sixteen measure zero, including every
   bundle that claims kernel purity in print. The state was clean and unguarded, so it is now
   enforced by `bundle_native_decide_debt` + `NATIVE_DECIDE_BUNDLE_DEBT`: debt is attributed to the
   manuscript that rests on it, may only shrink, must be disclosed, and zero is *asserted* rather
   than assumed. **D8 is the precedent for paying down** — it eliminated four sweeps (largest ~16.7 M
   tuples) by structural reproof, one of which strengthened the statement by dropping a hypothesis.
5. ✅ **SETTLED 2026-08-09 by reading the source the audit said it had not read — it was never an
   open physics question.** It does not bear on the merge either way: E1 contains no Γ_H, δ_diss or
   dissipative correction at all, and E1+E2 fails on length independently.

   **The multiplier is `v_F²`, and the prefactor is exactly 1.** In relativistic hydrodynamics the
   momentum density is `w/v_F²`, so the momentum-diffusion constant is `ν = η v_F²/w = (η/sT)·v_F²`
   at `μ=0` where `w = Ts`. The sound-attenuation coefficient carries `[2(d−1)/d]η + ζ`, which in
   **d = 2** is `2(1)/2 = 1` times `η`, with `ζ = 0` by conformal symmetry — a fact this project's
   own Phase-5w survey states (*"Bulk viscosity vanishes identically (ζ = 0) by conformal
   symmetry"*). Two dimensions is the one case where the shear prefactor is unity, so there is no
   surviving O(1) ambiguity. `c_s` is a property of the *dispersion*, not of the inertia, and enters
   only through `k_H = κ/c_s`, which the formula already carries; a `c_s²` multiplier is the
   units-patch answer, not the physics answer.

   ⚠️ **The 17 % vs 3.2 % spread was never a physics fork — it is an inconsistent parameter
   pairing.** For a conformal Dirac fluid `c_s = v_F/√2` exactly, so `(η/sT)v_F² ≡ 2(η/sT)c_s²` and
   the two routes differ by exactly **2**, as the monolayer platforms show (17.3 % → 34.2 %). The
   5.2× seen at the Dean device comes from pairing the **monolayer** `v_F = 10⁶ m/s` with the
   **bilayer** `c_s = 4.4×10⁵ m/s`, a pair that violates `c_s = v_F/√2` — and `constants.py`'s own
   provenance says why, attributing the lower bilayer `c_s` to *"bilayer band structure"*. The
   internally consistent conformal value for the Dean device is **δ_diss ≈ 6.5 %** against
   δ_disp ≈ −2.8 %: dissipative dominates by ~2.3×, same sign inversion, no near-cancellation.

   ⚠️ **Two corrections to this ADR's own earlier entry, both of which were measurement errors.**
   (i) The 2026-08-08 note said *"`formulas.py` is dimensionally sound so only the prose is wrong."*
   The first half is true and the conclusion is false: the defective expression is at
   `src/graphene/hawking_predictions.py:107`, which re-derives the formula instead of importing the
   canonical path — so the audit was right that code is affected and merely named the wrong file.
   Pipeline Invariant 1 exists to prevent exactly this. (ii) The recommendation of `v_F²` was right
   for the wrong reason, and the 17 % that accompanied it is an artifact.

   **The source already answered it.** `Lit-Search/Phase-5w/5w-SK-EFT Hawking framework meets the
   graphene Dirac fluid.md` gives `Γ_sound ~ (η/w)k² ~ 10¹⁰ s⁻¹`. E2 prints `Γ_H ≈ 0.3 s⁻¹` —
   **eleven orders below its own cited source**, which is the same eleven orders the draft then
   reports as a physics result. The audit flagged that it had not traced the derivation
   (*"I did not trace Γ_H … to Lit-Search/Phase-5w"*); tracing it is what closed the question.

   **Residual, and it is narrow:** `Dean_bilayer_nozzle.v_F` carries **no `PARAMETER_PROVENANCE`
   entry** — alone among that platform's six parameters — and bilayer graphene has quadratic band
   touching, so no emergent light cone and no `v_F` in the Dirac sense. The relation is a monolayer
   identity applied to a bilayer device. That is a disclosure-and-provenance obligation, not a
   blocker. Tracked as TODO-D31.

Items 2–5 were recorded here because each **changes a container's charter**, so the distribution
recommendation must state its dependence on them rather than silently assuming a resolution.

**All five are now answered** (roster **21**, decided under operator delegation 2026-08-09). Nothing
in this list still blocks a bundle. What items 3 and 5 leave behind is **remediation with a known
answer** — L1's prior-art gap (TODO-D34) and E2's Γ_H propagation plus the bilayer `v_F` provenance
(TODO-D31) — not adjudication.

⚠️ **Every answer above states its own predicate, because three of the four turned on one.** D10's
redundancy question inverted once PhysLib was read rather than assumed; the D10+D11 merge rested on
a withdrawn measurement; item 5's *"and `formulas.py`"* was half wrong. **The pattern across this
whole ADR is that the measurement, not the conclusion, is where the errors live** — which is why C4
requires the substrate to be read directly and why each answer here names what was measured, what
was not, and by what rule.

---

## Consequences

**Accepted.** Publication is deferred further. Per C5 that is the intended trade: the schedule is the
flexible variable. The audit already states the consequence plainly — *"no Tier-1 bundle ships on the
previous timeline"* — and the roster analysis is upstream of even that.

**A sequencing trap to avoid.** `CROSS-portfolio-coherence.md` §6.4 warns that merges should land
*before* further Stage-13 or lift work on D6/D7/D9/D10/D11/D12/E1/E2, *"or that work is spent on
containers that are about to be dissolved."* Conversely `SYNTHESIS.md` §6 Phase 2 notes that removing
D9's content from D6 **drops D6 to ~7 pp** — the length gap widens before it closes. Both are true; the
analysis must sequence around them explicitly.

**Risk if not done.** The generator keeps running: the next authorized bundle is another under-filled
depth container, and the ~340 un-homed modules keep growing. The audit's verdict — *no bundle in the
portfolio is submittable today; best grade C−* — is the current state of a portfolio whose strategy was
last evaluated whole before Phases 6AA–6EE existed.

**Risk if done badly.** A roster change that moves the number without moving C1's change-set turns the
suite red in seven consumers at once and, worse, can be "fixed" by editing the registry to match a stale
consumer — re-fragmenting the single source of truth the gate exists to protect.

### What the measurement pass cost, and what it bought (2026-08-05)

The pass could not be completed without repairing three instruments, because each was **reporting PASS
over a population it never reached** — the same defect class ADR-009 exists to close, found three more
times outside the validation suite's own guards:

| commit | defect | scale |
|---|---|---|
| `c7148779` | `prose_theorem_reference_coverage` read only `\texttt{}`; D8/D9 route every Lean reference through `\newcommand{\lean}[1]{\texttt{#1}}` | **288** references unscanned |
| `c5f384b4` | same check could not see `\verb`; D6 writes **235** of those against 25 `\texttt` | **276** more, and it surfaced 2 real unresolved D6 references |
| `9f62deaa` | `check_bundle_source_freshness` scored an **absent** source directory as fresh | **9** bundles with a fully vacuous freshness PASS |

Candidate references scanned went **671 → 1 051**. Every one of the 380 newly-visible bundle references
**resolves**: the drafts were sound and the instrument was blind, which is the more dangerous of the two
failures because it is invisible from the outside.

> **The lesson, stated so it generalizes.** All three were found the same way — not by auditing the
> checks, but by **measuring the corpus independently and noticing the two numbers disagreed.** The
> check's own summary is what made it look thorough: *"21 bundle drafts scanned / 671 candidate Lean
> references"* reads as coverage. It was 671 of 1 051. **A count of what was scanned is not evidence
> that the population was reached**, and no amount of guarding *inside* an instrument detects an
> instrument pointed at the wrong set.
>
> This is also why C4's *"read the substrate directly"* is load-bearing rather than ceremonial. Three
> times in one pass my own measurement inherited the check's blind spot and produced a confident wrong
> answer — D8 and D9 referencing "zero" Lean modules, and **D6 ∩ D9 = 0** against the audit's 78.
> Filing that as "the audit is wrong" would have destroyed the best-evidenced merge in the portfolio on
> the strength of a broken regex.

### What remains before this ADR can recommend

The measurement pass discharges the EVIDENCE CLASS gate; it does **not** discharge D2, D4 or D5, all of
which require reading manuscript content the pass deliberately did not read (C4). Outstanding:

1. **D2** — per-target re-derived purpose statements, from the manuscripts.
2. **D4** — the per-target merge/split/retire recommendation.

   > ✅ **DISCHARGED 2026-08-08 — operator delegated the grouping call; full working in
   > [`docs/audits/2026-08-08-adr010-d4-adjudication/ADJUDICATION.md`](../audits/2026-08-08-adr010-d4-adjudication/ADJUDICATION.md).**
   > Every proposed merge was tested against the manuscripts read in full, and **all six fail**.
   > A retirement the audit never proposed — L1 — was then argued *and reversed on evidence the
   > following day* (§Open item 3). **Roster: 21, unchanged**, and the number is an output, not a
   > target.
   >
   > ⚠️ **The sentence this box replaces carried a claim withdrawn the day after it was written** —
   > *"D11 and D12 reference zero Lean declarations"* was an extraction artifact (see the EVIDENCE
   > CLASS box at the top: D11 = 95 declarations / 22 modules). The D10+D11 merge was therefore
   > never argued from evidence; it was deferred pending evidence that turned out to be wrong.
   > Measured now: `D10 ∩ D11 = 0`, and the two manuscripts are methodologically opposed — D10 is
   > built on PhysLib's analytic substrate, D11 imports no PhysLib and exists to show the analytic
   > route is unnecessary.
   >
   > **The portfolio's problem was never the count.** It was content in the wrong containers: D6
   > holds D9's paper (44 % of its draft), D4 held D8's apexes, D1 held D7's, L1 holds a claim D3
   > already develops. Three of the four are fixed by **reassignment**, which changes the roster by
   > zero. That is why 21 → 16 could only have been reached without reading the drafts.
3. **D5** — homing dispositions for **1 403–1 633** modules, not ~340. The scope is 4–5× what the
   charter assumed, which may itself change the shape of the answer (a per-arc disposition rather than a
   per-module one).
4. **D6 step 4** — operator approval for the Lean-module-mtime absorption trigger.
5. **D7** — the roster-drift change-set, unchanged.

---

## Alternatives considered

1. **Execute the roster change directly, skipping the ADR.** Rejected by the operator: the content is not
   in context, the change-set is coordinated across a dozen files and three enforcement legs, and the
   decision is theirs. The ADR is the review surface.
2. **Ratify the audit's 21 → 16 as-is.** Rejected as insufficient diligence. The audit's own §7 lists what
   it could not check — including the 78 D6/D9 theorem statements against the Lean, which is exactly the
   evidence that decides whether D6+D9 is a merge or a contradiction.
3. **Shrink the charters to match the current drafts.** Rejected — the audit names this as the walk-back
   the remediation posture forbids (C5), and several bundles demonstrably have the substrate for a real
   article.
4. **Do this before ADR-009.** Rejected by the operator: the dials that measure a bundle's readiness are
   the ones under repair, and recommending against broken instrumentation is what produced the audit.

---

## References

- `docs/audits/2026-08-01-publication-readiness/SYNTHESIS.md` — verdict, 80 P0 findings, the systemic
  finding (§2), the six defect classes (§3), what is genuinely sound (§4), the five operator decisions
  (§5), the remediation sequence (§6).
- `.../REMEDIATION_PLAN.md` — the BUILD (B1–B8) / CORRECT-TO-SUBSTRATE / FACTUAL triage that supersedes
  SYNTHESIS §6 Phase 1, and §6a's build-authorization rule.
- `.../CROSS-portfolio-coherence.md` §5 (every inconsistent roster statement), §6.4 (the 16-target
  recommendation and table), §7 (what the auditor could not check).
- `.../CROSS-absorbability-and-strategy-drift.md` — the 60-item drift ledger and the absorption analysis.
- `scripts/bundle_registry.py` — the machine roster; `parse_strategy_roster()` is Leg A's parser.
- `scripts/validation/checks/bundles_readiness.py:745` — `bundle_registry_consistency`, the three-leg gate.
- `docs/WAVE_EXECUTION_PIPELINE.md:689` — Invariant #14, carrying the stale 18-target enum.
- `docs/audits/2026-08-05-adr010-measurement/MEASUREMENTS.md` — M1–M6, the re-measurement pass that
  discharges the EVIDENCE CLASS gate.
- `docs/architecture/.working-docs/RESUME_STATE.md` — the live tracker for both workstreams.
- [ADR-009](ADR-009-validation-suite-modularization.md) — must close and merge first.
