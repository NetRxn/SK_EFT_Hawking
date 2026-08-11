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

## 7. Open questions — THREE OF FOUR NOW SETTLED BY MEASUREMENT

Measured 2026-08-06 across all 21 bundles; full numbers and method in
**`docs/audits/2026-08-06-closure-probe/FINDINGS.md`**. The probe reproduces M4(a)'s
independent **D6 ∩ D9 = 78** exactly, so the resolution path is sound before anything rests on it.

1. ~~**Distinctive vs raw closure.**~~ **CLOSED — the worry was unfounded; drop the
   complication.** 70 % of homed declarations appear in exactly ONE bundle's closure, and
   **maximum ubiquity across 21 bundles is 7, reached by one declaration**. There is no
   shared-foundations blob, so raw closure is already distinctive and no second definition is
   needed. *Why*: `name_deps_project` is **project-closed** (verified — 0 of 279 602 edges leave
   `SKEFTHawking`), so Mathlib, the genuinely universal substrate, is excluded upstream.
2. ~~**Un-homed will be loud.**~~ **CLOSED — ~1 400 modules, and the number is robust.** Closure
   homes **631** modules; M2's loose name-based rule homed 636 and its strict rule 406. Two
   mechanisms with nothing in common — substring presence vs dependency reachability — land
   within 2 modules of each other. Closure homes **2.3×** what direct reference does (631 vs 275),
   which is the design paying for itself.
3. **Apex declarations are hand-maintained.** UNCHANGED, still a build item — an apex must be
   checkable against a live declaration (machinery now exists).
4. ~~**Does a closure cross bundles?**~~ **CLOSED — yes, sparsely.** D6∩D9 Jaccard **0.482** (the
   one genuinely entangled pair — the same pair the portfolio decision turns on), D4∩D8 0.146,
   D8∩D9 0.135, L2∩D9 **0**. Many-to-many, but not a mesh.

⚠️ **New constraint the probe surfaced — closure has bounded holes.** 12.4 % of dependency edges
name a declaration absent from `lean_deps.json` and the walk stops there. Almost all are
proof-internal artifacts and constructors (leaves — nothing lost), but **553 distinct `_private.*`
declarations (1 278 edges, 0.46 %) are genuinely lossy**: `ExtractDeps` omits `private`
declarations, so a closure routing through one truncates silently. **State this wherever a closure
size is reported** — unstated, it is another absence rendered as success.

## 8. ✅ DONE — closure shape separates most bundles, and flags three

Seeded from existing prose references (a **lower bound** — no apexes are declared yet):

- **As §3 predicted:** L1 (1 module, depth 1) and L3 (5, depth 3) are genuinely shallow; D9
  (142 modules, depth 18) and D8 (289, depth 24) are genuinely deep.
- **Against the roster:** **D7 (6 modules) and D1 (18) are shaped like letters**, and L2 carries a
  deep substrate (39 modules, depth 14) for a PRL.

That is a signal about where to look; it does **not** decide anything, because tier is also a claim
about audience and framing, not only about substrate.

### ⚠️ Correction after the first three retrofits — depth is NOT the tier discriminator

§3 proposed *"one apex over a shallow closure is a letter; several interlocking apexes over a deep
closure is a deep paper."* Measured against real apex declarations, that rule **misses a third case
and gets it backwards**:

| bundle | apexes | closure | modules | depth | **apexes / closure** |
|---|---|---|---|---|---|
| D6 | 11 | 51 | 4 | 3 | **22 %** |
| D9 | 25 | 623 | 68 | 12 | **4 %** |
| L2 | 8 | 430 | 40 | 14 | **2 %** |

**L2 is a letter with a deep substrate, and that is entirely legitimate** — a PRL making one crisp
claim (`N_f ≡ 0 mod 3`) resting on 430 declarations of algebraic topology (Ext over `A(1)`, Rokhlin,
spin manifolds) is a good letter, not a mis-tiered deep paper. My earlier reading of "L2 is a letter
on a deep-paper substrate" as a *problem* was wrong.

The discriminator that survives contact with the data is the **ratio**: a deep paper's apexes sit
atop a large derived body (D9, 4 %); a letter's single claim can also sit atop a large body (L2,
2 %). What stands out is the **opposite** shape — **D6's apexes are 22 % of its own substrate**,
i.e. its claims very nearly *are* the substrate, resting on almost nothing derived beneath them.

So: **depth measures how much machinery a claim rests on; the apex/closure ratio measures whether a
bundle has substrate underneath its claims at all.** The second is the one that flags a thin
bundle. Neither decides tier by itself.

## 9. Heuristic surfaces still open (the "arc-like" audit)

Operator asked how much else rests on name-matching rather than real infrastructure. Audited:

| # | surface | status |
|---|---|---|
| H1 | lakefile exe roots parsed by regex | **FIXED** — `tomllib` |
| H2 | module reachability by regex import-walk | **KEPT DELIBERATELY** — see below |
| H3 | autogen declarations detected by NAME PATTERN (`_AUTOGEN_RE`) | **FIXED** — see below |
| H4 | `_PAPER_SIDE_MODULES` hand-listed | **FIXED** — partition now total + enforced; also fixed memoized checks being attributed to the `_memo` wrapper |
| H5 | prose candidate filter runs BEFORE resolution | **FIXED** — resolve first, judge only what fails |
| H3′ | **`build_graph.py` kept its OWN autogen name regex** | **FIXED 2026-08-06** — see below |

**H3′ — the same defect survived H3 in the one place §6 cares most about.** H3 fixed
`ExtractDeps`, `atlas_view` and `validate.py`, but `build_graph.py` carried an independent
`_AUTOGEN_SHORT_RE` deciding which declarations become graph nodes and what a module node's
`declaration_count` says. So the **graph — the artifact human review actually reads** — was
classifying one population differently from the checks that ratchet on it.

Both call sites now go through `validate_helpers.autogen_index`, and the regex is **deleted**, not
merely unused. Measured over the live corpus: the new drop set is a **strict superset** of the old
— **270** compiler-generated declarations removed from the graph, **0** author-written declarations
affected. Four of them were being ranked as OBSTRUCTIONS on the atlas negative frontier
(`X.mk.inj` inside no-go namespaces — the exact R6-M1 defect class), so the frontier a `/goal` loop
reads to steer away from dead paths goes 403 → 399.

The residue the regex caught and Lean's public predicates do not (`inj`, `ctorElim`,
`ctorElimType`, `ofNat` — plus `repr`/`decEq`, whose parent is the *derived instance*, needing
their own branch) was added to the supplement **under the parent-kind guard**, verified against the
corpus: every `.repr` (76) and `.decEq` (34) has an `instance` parent; all 419 `.inj` have an
inductive/structure parent or grandparent. A bare suffix match would delete an author-written
`Sheaf.restriction.inj` — which is what the deleted regex did.

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
