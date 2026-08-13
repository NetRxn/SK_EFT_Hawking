# ADR-013 — The module census: one derived answer to "what is this module", and the retirement of the Inventory pair

- **Status:** 📝 **PROPOSED — nothing built (drafted 2026-08-13).** §Plan is the authority on what
  is built. This document lands before the code, per the architecture rule that *a doc written
  afterwards is a changelog; only one written first is a specification*.
- **Supersedes:** the hand-maintained halves of `SK_EFT_Hawking_Inventory_Index.md` and
  `SK_EFT_Hawking_Inventory.md`. It does not supersede any prior ADR.
- **Sequence:** written through the `architecture-change` skill. Orient · measure · specify are
  complete; the pilot ran before this document was written, and it changed the design.

---

## Context

Two hand-maintained files answer *what is this module*: an Index (pointers) and an Inventory
(prose). Both began as catalogues of a small repo and neither kept up with it.

**Measured 2026-08-13, all figures from the live tree:**

| | Index | Inventory |
|---|---|---|
| created | 2026-03-27 at 6 KB | 2026-03-24 at 40 KB |
| today | 79 KB | 319 KB, 87 commits |
| code consumers | 4 (`sync_manifest`, `pre-commit-sync.sh`, `update_inventory_index`, `freshness`) | **none** |
| generator | AUTOGEN blocks only | none |
| gate | `inventory_index_autogen_fresh` | none |

**The Inventory's largest section catalogues a population it stopped tracking.** §2 is 194 KB —
61% of the file — and names 85 of the 2040 live Lean modules: **4.2% coverage**. Every path it
names still exists, so it is not wrong; it is a hand catalogue of a population that grew past it.
And §2 is not a module catalogue at all. It has three subsections, two of which are phase-arc
narrative (*"Verified-quantum-compilation arc, Phases 6u→6z"*), which is wave history that
`docs/roadmaps/` owns.

**Most of the Index restates artifacts that are already derived and gated.** Section by section:
§3 Lean module map → `docs/counts.json` `lean.module_names` and the graph's `module:` nodes;
§4 headline theorems → `lean/lean_deps.json`, `lean/atlas_view.json`; §5 tracked Props →
`docs/PERMANENT_TRACKED_HYPOTHESES.md`; §6 pipeline invariants → `WAVE_EXECUTION_PIPELINE.md`;
§7 bundle status → `docs/BUNDLE_READINESS_HEATMAP.md` and `bundle_registry.BUNDLE_CODES`;
§9 Aristotle → `ARISTOTLE_THEOREMS` in `src/core/constants.py`.

⚠️ **The failure mode this creates is the one this project is named for.** A half-generated
document inherits the credibility of its generated half. Measured earlier the same day: the
Index's AUTOGEN table was fresh while the prose around it was two months stale — a theorem count
roughly half the generated one, a bundle roster short of the live one, and a sentence asserting
this repo has no `CLAUDE.md`, which it has and which is the primary bootstrap. Every gate was
green, because every gate looked only inside the markers.

**What neither derived artifact covers** is *what Python modules and scripts exist and what they
do*. That is the only genuinely unique content across both files — Index §8 and §11, Inventory
§1, roughly 27 KB of 398 KB.

---

## Constraints — verified, and load-bearing for the design

**C1 — The plugin already classifies the Inventory as a judgment doc.**
`.claude/plugins/skeft-qa/skills/sync/SKILL.md:55` is the *only* reference to either file
anywhere in the plugin: the prose Inventory is *"flag-only — never silently regenerated."*
It was never intended to be generated, which is why it has no generator to fix.

**C2 — Regeneration is registered, not wired.** `scripts/sync_manifest.py` declares
`Edge(output, inputs, command)`; `sync.py --fast` runs the cheap subset;
`scripts/pre-commit-sync.sh:50` regenerates **and auto-restages** that subset on every commit; a
`*_fresh` check gates each at tiers 2–3. A new derived artifact inherits all four by declaring one
edge. The `/sync` skill needs no edit — it runs the manifest.

**C3 — `SURFACE_INVENTORY.md` is deliberately NOT auto-synced** (`QA_QI_INFRASTRUCTURE_MAP` §2,
"no — deliberately"). The census is cheap, so it belongs in the auto-restaged set beside the
Index — which makes it its own artifact rather than a section of `SURFACE_INVENTORY.md`.

**C4 — The docstrings already carry the content, and nothing has ever measured them.**
Pilot, 2026-08-13, over `src/` and `scripts/` excluding `.temp`:

| | count | share |
|---|---:|---:|
| modules | 318 | |
| substantive module docstring | 311 | 98% |
| title-only docstring | 3 | 1% |
| no docstring | 4 | 1% |

The four are `src/{dark_sector,fermi_hubbard,graphene}/__init__.py` and
`scripts/tests/test_system2.py`. **The derived artifact is 32.6 KB**, against 398 KB
hand-maintained today, and fits in a single `Read`.

**C5 — The census is only as good as the docstrings, and one loss is measured.**
`src/core/transonic_background.py`: the Inventory's hand prose says *"1D BEC transonic flow
solver. Parameterizes velocity as smooth tanh transition through horizon."*; the module docstring
says *"Transonic Background Solver for 1D BEC Flow"*. Taking the first **paragraph** instead of
the first line costs +3 KB and does **not** recover it — that docstring has no second sentence.
This is a real coverage loss and it is why D6 exists.

**C7 — THE LAW MANDATES THE HAND MAINTENANCE, AND ITS GATE IS A MANUAL SAMPLE.**
`WAVE_EXECUTION_PIPELINE.md` **Stage 12: DOCUMENT SYNC** (lines 509–575) is the mechanism that
was supposed to keep both files fresh. It carries a *what to update* table naming
`SK_EFT_Hawking_Inventory.md` ("module descriptions, section content") and
`SK_EFT_Hawking_Inventory_Index.md` ("counts table, section→update mapping"); a four-step
**Inventory maintenance** procedure; and a six-item *Watch for* list — new modules absent from
§1, new theorems missing from §2's table, new Aristotle runs from §3, notebooks and papers from
§4–5, formula changes from §10, descriptions referencing superseded behaviour.

Its **gate** is *"full `validate.py` passes; manual spot-check of three count-sensitive files"*.

⚠️ **Nothing mechanical asserts any of those sections — measured: zero checks reference §1, §2 or
the `Last synced` date.** So the enforcement for a 319 KB hand catalogue was a hand-run sample of
three files, and the outcome is C4's 4.2% Lean coverage and a two-month-stale narrative. **This
is not a discipline failure to be exhorted away; it is a mechanism that cannot scale to the
population it governs**, and it is the direct cause of the drift this ADR removes.

It also makes this a **law amendment**, not a file retirement: Stage 12 must change in the same
work, or the pipeline will mandate maintaining files that no longer exist.

**C6 — The population I reported before was wrong twice, which is why C4 is stated as a
derivation.** An earlier pass in this session reported "44 of 112 modules undocumented". The
population was `scripts/*.py` **top level only** — 112 against a real 318 — and the metric was
*does this filename appear in a doc*, a proxy, rather than *does this module have a docstring*,
the decider. Both numbers are withdrawn; C4 supersedes them.

---

## Decision

**D1 — One derived artifact answers "what is this module": the module census.**
`docs/architecture/MODULE_CENSUS.md`, generated from the source of `src/**/*.py` and
`scripts/**/*.py`. Every row is `path | first paragraph of the module docstring`. No hand-edited
region, no AUTOGEN markers — **the whole file is generated**, like `SURFACE_INVENTORY.md`, so the
mixed-generation failure cannot recur in it.

**D2 — The decider is `ast.get_docstring`, never a regex over source.** A source scan finds a
docstring-shaped string inside a function and calls the module documented
(`CHECK_AUTHORING_GUIDE` §2.5). The generator parses and asks the AST.

**D3 — The census reports what it cannot describe, beside what it can.** Two populations are
listed by name in the artifact itself: modules with **no** docstring, and modules whose docstring
is **title-only**. A surface silent about its blind spot reads as complete.

**D4 — Both populations are ratcheted down-only, at their live values.** `NO_DOCSTRING_CEILING`
and `TITLE_ONLY_CEILING`, frozen at the C4 measurement, lowered in the commit that lowers the
population. Nothing blocks today; the first regression does. Zero headroom, per
`CHECK_AUTHORING_GUIDE` §2.3.

⚠️ **Not a hard fail on absence, deliberately.** Three of the four are `__init__.py`, where a
docstring is a style question rather than a defect, and a gate that fires on correct work gets
switched off (`VALIDATION_GATE_TOPOLOGY` §3). The ratchet gets the same pressure without the
false positive.

**D5 — The census is registered as a sync edge, not wired by hand.** One `Edge` in
`sync_manifest.py` with `src/**/*.py, scripts/**/*.py` as inputs. It is cheap, so it lands in
`--fast`, which means `pre-commit-sync.sh` regenerates and restages it on every commit and
`/sync` picks it up with no edit. Gated by a new `module_census_fresh`.

**D6 — The Inventory's richer prose migrates into the docstrings BEFORE the file is retired.**
Where §1's hand-written `Purpose:` says more than the module's docstring, that sentence moves
**into the docstring**. The information survives at the source, the census picks it up on the next
run, and the retirement loses nothing. Bounded: §1 is 18 KB over roughly 40 modules.

⚠️ **This is the step that makes retirement safe, and skipping it converts D8 into a deletion of
hand-authored content.** It runs first and is verified per-module, not sampled.

**D7 — `SK_EFT_Hawking_Inventory_Index.md` is retired after the census is green.** Its unique
content is §8 and §11, which the census supersedes; everything else is a second account of a
derived artifact. Retirement unwires four code sites, three test files, three architecture
documents and `CLAUDE.md`'s routing row.

**D8 — `SK_EFT_Hawking_Inventory.md` is retired after D6 completes.** No code consumer, 4.2%
Lean coverage, and its largest section duplicates the roadmaps.

**D9 — The ~60 roadmap and audit mentions stay.** They are dated records of what was true when
written. Rewriting them is the drift this ADR exists to stop, not the fix.

**D11 — Stage 12 of the pipeline law is amended in the same work (C7).** The two Inventory rows
leave the *what to update* table; the four-step **Inventory maintenance** procedure and the
six-item *Watch for* list are deleted, replaced by a single line stating that the module census is
derived and regenerated by the sync edge.

⚠️ **Stage 12's gate STRENGTHENS rather than weakens.** It currently reads *"full `validate.py`
passes; manual spot-check of three count-sensitive files"*. After this change `validate.py` itself
gates the census, so a hand-run sample of three files is replaced by a derivation over all 318 —
the first time this stage's obligation is mechanically checkable at all.

⚠️ **Amending the law is a decision, not a consequence, which is why it is a numbered decision.**
`WAVE_EXECUTION_PIPELINE.md` is the process law and `WAVE_PIPELINE_RATIONALE.md` carries the
*why* behind each rule — **a rule whose stated reason no longer holds is the next rule somebody
relitigates**, so the rationale entry changes with it, per `docs/architecture/README.md`.

**D10 — The mutation obligation MOVES; it is not deleted.** `inventory_index_autogen_fresh`'s
four production-seeded mutations, its `PRODUCTION_SEEDED` membership and its `MUTATION_VERIFIED`
entry transfer to `module_census_fresh`. `FIXTURE_ONLY_CEILING` is re-measured in the same commit.
Deleting a check that carries a mutation entry silently loosens the ratchet that tracks them.

---

## Overlap reconciliation with prior ADRs

**ADR-009 (validation modularization)** — the new check goes in
`scripts/validation/checks/freshness.py`, which owns generated-artifact freshness, and takes a
position in `validate._CANONICAL_ORDER`. The census reads source, not `docs/counts.json`, so it
has no regenerator-ordering dependency.

**ADR-012 (finding lifecycle)** — the census's two ratcheted populations are *not* review
findings and do not enter the queue. A finding is a defect someone must close; a title-only
docstring is a measured population with a down-only ceiling. Conflating them would put 7 items
into a queue whose purpose is dispatch.

**ADR-010 / ADR-011** — no overlap. Neither touches module documentation.

---

## Pilot — run before this document was written

`census_pilot.py` against the live tree produced C4 and C5. Two design changes came out of it:

1. **The gate became a ratchet rather than a hard fail** (D4), because the four
   no-docstring modules are mostly `__init__.py`.
2. **D6 was added.** The pilot's own output next to the Inventory's prose showed the
   `transonic_background.py` loss, which the design had not anticipated. Without D6 this ADR
   would have proposed deleting hand-authored content and called it a cleanup.

---

## Plan

Phases are ordered so nothing is unwired before its replacement is green.

| phase | what | gate |
|---|---|---|
| **P1** | Ship `scripts/module_census.py` + `MODULE_CENSUS.md` + `module_census_fresh` with both ratchets, register the `Edge`, add to `pre-commit-sync.sh`'s restage list. Production-seeded mutation for each leg. | census green, mutations red-then-green |
| **P2** | D6 — migrate the Inventory's richer `Purpose:` prose into module docstrings, per module. | census re-run shows the migrated text |
| **P3** | D10 — move the mutation obligation; re-measure `FIXTURE_ONLY_CEILING`. | `test_d5_mutation_obligation` green |
| **P4** | D7 — retire the Index: unwire `sync_manifest`, `pre-commit-sync.sh`, `update_inventory_index.py`, `freshness.py`, three test files, `CLAUDE.md`, three architecture docs. | full fast suite green |
| **P5** | D8 — retire the Inventory; correct the generated pointer string that names it. | `doc_refs_resolve` green |
| **P4b** | D11 — amend `WAVE_EXECUTION_PIPELINE.md` Stage 12 and its `WAVE_PIPELINE_RATIONALE.md` entry. **Lands with P4/P5, never after.** | the law names no retired file |
| **P6** | Docs in the same commit as each phase: `QA_QI_INFRASTRUCTURE_MAP` §2 + §2.1 rewritten from "the pair" to "the census", `CLAUDE.md` when-to-read row, `SURFACE_INVENTORY` census row. | `architecture_inventory_fresh` green |

⚠️ **P1 must be green before P4 touches anything.** Between them the Python/script population has
two homes; before P1 it has one; after P4 it has one. There is no ordering in which it has none.

⚠️ **P4b is not optional and not deferrable.** The law is read on every wave; a Stage 12 that
mandates maintaining a deleted file is worse than the drift being fixed, because it sends every
future wave to a path that no longer exists. If P4/P5 land without it, the change is incomplete
regardless of what the suite says — no check reads the law.

---

## Consequences

**Good.** One answer to "what is this module", derived, gated, auto-regenerated at the commit
gate. 398 KB of hand-maintained files become a 32.6 KB derived one. Mixed generation disappears
rather than being managed. Module documentation becomes measurable and ratchetable for the first
time.

**Costs.** Module descriptions become exactly as good as the docstrings — where a docstring is a
bare title, the census is a bare title (C5). D6 bounds the immediate loss; the standing cost is
that improving a description now means editing the module, which is where it belongs.

**Accepted risk.** `MODULE_CENSUS.md` regenerates on every commit that touches `src/` or
`scripts/`, so it appears in most diffs — the same cost `SK_EFT_Hawking_Inventory_Index.md`
already carries at tier 0 today.

---

## Alternatives considered

**Generate the Index's derivable sections instead of retiring it.** Rejected: it keeps a large
file whose sections restate five other derived artifacts, and preserves mixed generation — the
specific property the operator objected to.

**Fully generate the whole Index including §8/§11.** This is what D1 does, minus the sections that
duplicate other artifacts. The difference is scope, not mechanism.

**Archive the Inventory unchanged rather than migrating its prose.** Rejected: it makes the
content unfindable in practice while claiming it is preserved, and D6 is bounded work.

**Push everything into per-module docstrings and have no census.** Rejected: there would be no
single place to see the population, and no way to gate coverage.

---

## References

- `CHECK_AUTHORING_GUIDE.md` §2.3 (zero-headroom ratchets), §2.4 (production-seeded mutation),
  §2.5 (guard the seam; use `ast`, assert the call)
- `QA_QI_INFRASTRUCTURE_MAP.md` §2 (writers and staleness keys), §2.1 (the pair — rewritten by P6)
- `VALIDATION_GATE_TOPOLOGY.md` §3 (a gate that fires on correct work gets switched off)
- `scripts/sync_manifest.py` (the `Edge` roster), `scripts/pre-commit-sync.sh:50` (restage set)
