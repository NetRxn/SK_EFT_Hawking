# Publication intake — the closure design (RESUME POINT)

**Status: DESIGN, not built. Authored 2026-08-06 to survive compaction.**
Operator wants the apex / graph / shape work done in a **post-compact session**. This file is the
resume point; read it before touching anything below.

---

## 1. What the operator authorized (2026-08-06)

> *"I'm authorizing shifting the publication content and strategy as needed to ensure we're
> distributing correctly, and that our entire roadmap portfolio is mapped into the publication
> strategy. Critically, I want to ensure that as we continue to develop roadmaps in arbitrary
> domains over time, that we have an easy onboarding strategy, either absorbing into existing
> work, or creating new publications. Doing so must be ergonomic & not break the structure we
> build as part of ADR010."*

So the deliverable is **an intake architecture**, not a roster edit. Re-tiering (a D that should
be an L) is explicitly in scope. ADR-010's earlier "no roster change authorized" line is
SUPERSEDED for content/strategy — the machine-roster change-set discipline (§C1) still applies.

Also standing, from the same session: **ADR-010 and the paper-corpus work happen ON the ADR-009
branch**, so the infrastructure is validated by use before merging. Do not propose merging.

## 2. ⛔ "Arc" is RETRACTED — do not reintroduce it

I used "arc" for three different things at once — a **naming/directory cluster**, a **phase**
(temporal), and a **body of research** (semantic). None of them is what a paper is made of, and
the confusion is what made the implementation feel unclear.

Measured, so it does not get re-proposed: two thirds of the Lean tree sits **flat at the root**,
so a subtree map covers a minority. Name-prefix clustering covers most of the remainder but
fragments into ~190 clusters at natural granularity (`PinPlus`, `PinPlusKT`, `PinPlusCharPair`,
`PinPlusTraceCapstone` are four "arcs" that are obviously one). **Neither directories nor names
partition the substrate.** An arc map would be a hand-maintained heuristic — the exact defect
class this branch spent a session removing.

## 3. The unit that works: a claim and its dependency closure

**Verified before proposing.** `lean_deps.json` carries per-declaration project dependencies
(`name_deps_project`), essentially complete, **zero extraction timeouts**. Walking the closure of
one real theorem (`subHomConnecting_openDuality`) returns **1 128 transitive dependencies across
72 modules**, in about a second.

So:

- a bundle **DECLARES its apex theorems** — the results it claims, which its abstract already
  asserts in prose. A handful of names.
- its **substrate is DERIVED** — the transitive closure of those apexes. Never declared, cannot
  drift.

Everything else falls out of that one join:

| question | answer |
|---|---|
| what substrate does this bundle rest on? | closure of its apexes |
| when must it absorb? | anything in that closure changed (content hash, **not mtime**) |
| what is un-homed? | declarations in no bundle's closure |
| do two bundles overlap? | closure intersection — computed, not asserted |
| **does it have enough substrate?** | **closure size / depth — measurable** |

The last row is the empty category H1 identified: **content-sufficiency checks = 0**, because
nobody could say what "enough" meant. Closure depth is a candidate definition.

And it dissolves the D-vs-L question: **one apex over a shallow closure is a letter; several
interlocking apexes over a deep closure is a deep paper.** Tier becomes a *function of substrate
shape* instead of a template chosen at authorization — which is the exact inversion the D-tier
diagnosis (ADR-010 §Context) demands, and something an arc map could never provide.

## 4. Onboarding — the ergonomics the operator asked for

New roadmap ships theorems. Either:

- they enter an existing bundle's closure automatically, because an apex already depends on them
  → **no action at all**; or
- they don't, and surface as un-homed → the operator names an apex and picks a destination →
  **one line: the name of the result being claimed.**

Survives restructuring: merging two bundles concatenates apex lists, splitting partitions them,
and the derived half never moves.

## 5. ⚠️ The apex-creation gap (operator-flagged, UNSOLVED)

> *"the atlas/apex was introduced after papers/bundles — I don't know if we actually have a
> streamlined way of creating new apex nodes when we're building out new roadmaps/phases."*

Correct, and it is the real gap. Apexes were never part of how work **arrives**. Retrofitting
existing bundles is a one-time migration; it does not solve the ongoing case.

**Proposed hook: wave close.** A wave is where a result becomes real, it already passes a gate,
and it is the moment of maximum author context. Ask once, there: *what does this establish, and
which publication claims it?* — instead of reconstructing it months later from Lean.

**Operator conditions on me authoring apexes:** allowed *only* with **full context review per
bundle** — contributing roadmaps, the Lean it cites, its claims record. One bundle at a time, not
a sweep. An apex asserted without reading the substrate is the same "authorization before
measurement" pattern that produced the D-tier problem.

## 6. Hard constraint: graph / dashboard integration

> *"It's also meant to integrate perfectly with the graph/dashboard so that human review of the
> final product isn't a secondary conversation."*

Closures, apex declarations and un-homed substrate must **emit graph nodes and edges**, not just
check output. **Read the extractor contract in `scripts/build_graph.py` BEFORE designing the
shape** — this was not done as of writing.

## 7. Open questions to settle before building

1. **Distinctive vs raw closure.** Everything sits on singular-homology foundations, so raw
   intersection says every bundle overlaps everything. D6/D9 sharing *named* theorems is a
   different fact from sharing foundations. Overlap is meaningless until this is defined.
2. **Un-homed will be loud initially.** Substrate supporting no apex is genuinely un-homed —
   that is the point, but expect a large first reading.
3. **Apex declarations are hand-maintained.** Small, but real, and must be checkable that an apex
   resolves to a live theorem (machinery now exists).
4. **Does an apex's closure cross bundles legitimately?** If yes the map is many-to-many and the
   ergonomics change. Check before drafting.

## 8. Cheapest next step (needs no approval)

Compute closures for a few current bundles from their existing prose references and see whether
the numbers separate the letters from the deep papers the way §3 predicts. If they do, the design
is real; if not, that is learned before anyone commits. The autogen fix has LANDED, so closure numbers now rest on Lean's classification rather than a regex.

## 9. Heuristic surfaces still open (the "arc-like" audit)

Operator asked how much else rests on name-matching rather than real infrastructure. Audited:

| # | surface | status |
|---|---|---|
| H1 | lakefile exe roots parsed by regex | **FIXED** — `tomllib` |
| H2 | module reachability by regex import-walk | **KEPT DELIBERATELY** — see below |
| H3 | autogen declarations detected by NAME PATTERN (`_AUTOGEN_RE`) | **FIXED** — see below |
| H4 | `_PAPER_SIDE_MODULES` hand-listed | **FIXED** — partition now total + enforced; also fixed memoized checks being attributed to the `_memo` wrapper |
| H5 | prose candidate filter runs BEFORE resolution | **FIXED** — resolve first, judge only what fails |

⚠️ **H5 shipped a 5× SUITE REGRESSION on the first attempt — read before touching the
resolver.** `_resolve_prose_ref`'s last two tiers (`_lean_source_declares`,
`_physlib_declares`) each substring-search the WHOLE concatenated Lean/PhysLib source.
Removing the shape filter sent 2 568 of 5 384 tokens into a full-corpus scan apiece and
took the suite **320 s → 1 569 s**. I did not notice; the operator did.

The property actually wanted is narrower: a token resolving against the NAME INDEX
(cheap set lookups) must never be filtered first. The source scan is a last-resort tier
and may be reserved for tokens that failed the cheap tiers AND look like identifiers.
`_resolve_prose_ref(…, deep=False)` stops before those tiers. **Baseline is ~320 s —
time the suite explicitly after touching this, don't eyeball it.**

**H3 result — the regex was wrong in BOTH directions, and closures now inherit a
structural answer.** `ExtractDeps` emits an `autogen` field computed from Lean's own
predicates (`Name.isInternalDetail`, `isAuxRecursor`, `isNoConfusion`). Measured against
the regex it replaced: they agreed on **barely half** the population — the regex **missed
~2 300** (mostly `X.eq_1`, whose name carries no leading underscore) and **over-claimed
~2 700** (`ctorIdx`, `noConfusionType`, `sizeOf_spec`).

Lean's three PUBLIC predicates do not reach the reserved-suffix residue, and
`isReservedName` is `private opaque` so it cannot be called. `validate_helpers.autogen_index`
adds a supplement for those suffixes **guarded structurally** — the parent (or grandparent,
for `X.mk.injEq`) must have `kind` `inductive` or `structure`, read from `lean_deps.json`.
A bare suffix match would misclassify an author-written `Foo.injEq`.

Totals: Lean predicates alone 4 948; with the guarded supplement **7 236**. Project
author-written declarations: **33 221**. `atlas_view.py` now consumes the flag; the atlas
rebuilds identically (432 obstructions), so this is a correctness fix with no behaviour
change — the safest possible outcome for a classifier swap.

⚠️ **Cold vs warm re-extraction, measured 2026-08-06.** Editing `ExtractDeps.lean`
invalidates the per-decl JSON cache (its pin hashes that file), so this was the COLD path:
**23 min 14 s**, against **3 min 14 s** warm. Budget accordingly — any future `ExtractDeps`
edit pays the cold cost.

**H2 — a proposed "fix" that was WRONG, recorded so it is not retried.** Sourcing reachability
from `lean_deps.json` looked strictly better (ground truth from the real build). It **broke the
guard**: `lean_deps.json` LAGS the tree, so a module orphaned *this commit* stays recorded as
built and the check goes silent. Caught by mutation. The build record answers *what was compiled
last time*; the question is *what does the tree declare now*. Same subject, different tense. The
import walk stays primary; the build record is now a `build_record_lag` cross-check.

**H3 is the one that matters for this design.** `_AUTOGEN_RE` classifies `.casesOn` / `.injEq` /
`._eq_1` by name. `lean_deps.json` records `kind` but nothing marks internal declarations, so
every count downstream — including R6's finding that the filter leaves ~30 % structure companions
in — rests on a regex. Fix it **at `ExtractDeps`** (Lean knows this structurally), not downstream.
**Closure numbers inherit this**, which is why it precedes §8.

## 10. Where the evidence lives

- `docs/audits/2026-08-05-adr010-measurement/MEASUREMENTS.md` — M1–M6 **+ §CORRECTIONS** (two of
  my own figures were wrong: "D11/D12 reference zero" was an extraction artifact; "~340 low by
  4–5×" was a unit swap — the audit was right)
- `docs/audits/2026-08-05-pr-review-3/` — 8 reviewers, `FINDINGS_REGISTER_PASS3.md`,
  `H1-goal-fit.md` (the monotone-in-emptiness result), `H2-plugin-and-seams.md`,
  `VERIFIED-C2-sorry-guard.md`
- `docs/adrs/ADR-010-publication-portfolio-reassessment.md` — the charter + corrections
