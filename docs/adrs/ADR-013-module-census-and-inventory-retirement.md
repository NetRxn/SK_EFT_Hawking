# ADR-013 — The module census: one derived answer to "what is this module", and the retirement of the Inventory pair

- **Status:** ✅ **ACCEPTED — P1, P2, P4, P4b, P5, P6 SHIPPED 2026-08-13.** P3 folded into P4
  (see the corrected D10 — its transfer did not exist). D3 (notebook census) and D5 (shell
  census) remain open and are tracked in the plan table. This document landed before the code,
  per the architecture rule that *a doc written afterwards is a changelog; only one written
  first is a specification* — and the sequence paid: the pilot changed the design, D2's audit
  showed the "accepted loss" was no loss, and D10's stated transfer turned out not to exist.
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
`.claude/plugins/skeft-qa/skills/sync/SKILL.md:55` is the plugin's **only** reference to either
file, and it names the prose Inventory alone — the Index appears nowhere under
`.claude/plugins/`. It classifies the Inventory as a judgment doc: *"flag-only — never silently
regenerated."* The Inventory was never intended to be generated, which is why it has no generator
to fix.

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
| module docstring present | **314** | 99% |
| no docstring | **4** | 1% |

The four are `src/{dark_sector,fermi_hubbard,graphene}/__init__.py` and
`scripts/tests/test_system2.py`. The derived artifact is ~33 KB against 398 KB
hand-maintained today, and fits in a single `Read`.

⚠️ **AN EARLIER DRAFT OF THIS TABLE CLAIMED A THIRD POPULATION — "title-only: 3" — AND IT DOES
NOT EXIST.** It came from a character-count threshold (first paragraph ≤ 60 chars), and the
population a threshold produces moves with the threshold: 3 at ≤60 chars, 8 for "docstring is one
line", 10 for "one line without terminal punctuation". Read directly, the three it flagged are
*correct work* — `scripts/lean_slots/__init__.py` is `"ADR-008 shared Lean slot control plane."`,
`scripts/slotctl.py` is `"Repository entry point for the ADR-008 Lean slot controller."` A
non-arbitrary predicate — *the docstring restates the module name and adds no new word* — returns
**zero**. The row is withdrawn, and D4's second ratchet with it: it would have fired on correct
work, which is the `VALIDATION_GATE_TOPOLOGY` §3 failure this document invokes elsewhere.

⚠️ **The pilot must ship.** `scripts/module_census.py` lands in P1 carrying this derivation, so
C4 is reproducible by anyone. The numbers above were produced by a scratch script; for a document
whose C6 withdraws two of its own prior figures, an unreproducible baseline is not acceptable.

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

**C8 — THE CENSUS CHANGES THE DISCLOSURE SURFACE, AND THAT WAS FOUND BY SHIPPING IT.**
P1's first commit was blocked by the repo's IP disclosure guard. The census is not a pure
re-presentation of existing text: it **lifts module docstrings out of `src/` and republishes
them in `docs/`**, on an artifact that regenerates and re-stages itself on every commit. Any
term under IP watch that appears in any module docstring therefore crosses that boundary
automatically and repeatedly, with no human in the loop.

**The design consequence, which is now a standing property rather than an accident:**

* A docstring is no longer only source. It is published prose, and the census is the
  publisher. Whoever writes one is writing into `docs/`.
* The guard that catches it is the **public repo's pre-commit hook, on the staged delta** —
  the standing mechanism, and the right one, because it fires at the moment the text is
  introduced.
* ⚠️ **A forward gate cannot see backwards.** Anything committed before a term entered a
  watchlist is invisible to it, permanently. Measured 2026-08-13: fourteen such hits stood
  in the public tree, all predating the watchlist by six weeks to three months, and nothing
  had ever looked. That backstop now exists as an **ad-hoc** sweep on the private side, run
  when the delta gate structurally cannot help — a term added to a watchlist, a new asset,
  before a filing, after a bulk import. **It is deliberately not a scheduled check:**
  everything it can see is by definition already public, so running it daily would spend
  minutes re-reporting what nobody can undo.

**This does not change any decision above; it adds an obligation to P2 and P5.** Migrating
prose *into* docstrings (D6) now means migrating it into a published surface, so that step
inherits the disclosure question rather than being a pure refactor. Whatever is moved is
staged through the hook, which is exactly where it should be judged.

**C6 — The population I reported before was wrong twice, which is why C4 is stated as a
derivation.** An earlier pass in this session reported "44 of 112 modules undocumented". The
population was `scripts/*.py` **top level only** — 112 against a real 318 — and the metric was
*does this filename appear in a doc*, a proxy, rather than *does this module have a docstring*,
the decider. Both numbers are withdrawn; C4 supersedes them.

---

## Decision

**D1 — One derived artifact answers "what is this module": the module census.**
**`docs/MODULE_CENSUS.md`** — generated from the source of `src/**/*.py` and `scripts/**/*.py`.
Every row is `path | first paragraph of the module docstring`. No hand-edited region, no AUTOGEN
markers — **the whole file is generated**, like `SURFACE_INVENTORY.md`, so the mixed-generation
failure cannot recur in it.

⚠️ **It is sited at `docs/`, NOT `docs/architecture/`, for two independent reasons.**
*(1)* `docs/architecture/README.md`'s "what is deliberately NOT here" table declares that this
directory does not own *"what does this module do"* — putting the census there contradicts the
scope boundary written into the directory's own index. *(2)* It would fail
`architecture_inventory_fresh` **on the day it landed**: leg 2 forbids a census count in any
narrative under `docs/architecture/`, and two module docstrings carry Phase-6i wave numbers that
match it — `bundle_migration.py`'s *"Phase 6i Wave **7.1** bundle-aware migration"* and
`review_runner.py`'s *"Wave **7.2** bundle-aware review orchestrator"* read as `1 bundle` and
`2 bundle`. Since D1 makes the file wholly generated there would be nothing to edit, and the
offender set is a function of arbitrary prose across 318 docstrings, so an unrelated docstring
edit could redden the suite later. Measured before siting, not after.

**D1b — Scope boundary, stated so nobody rebuilds a second catalogue.** The census covers
**Python only** — `src/` and `scripts/`. Lean is answered by `docs/counts.json`
(`lean.module_names`), `lean/lean_deps.json` and `lean/atlas_view.json`, all derived from the
extraction chokepoint and unable to drift. Notebooks, papers and tests are answered by counts in
`docs/counts.json` and by their own directories. **Nothing else is in scope, and the census header
says so on its face.** An unstated boundary is how the next hand catalogue gets started.

**D2 — The decider is `ast.get_docstring`, never a regex over source.** A source scan finds a
docstring-shaped string inside a function and calls the module documented
(`CHECK_AUTHORING_GUIDE` §2.5). The generator parses and asks the AST.

**D3 — The census reports what it cannot describe, beside what it can.** Modules with **no**
docstring are listed by name in the artifact itself. A surface silent about its blind spot reads
as complete.

**D4 — That population is ratcheted down-only at its live value.** `NO_DOCSTRING_CEILING = 4`,
lowered in the commit that lowers the population. Nothing blocks today; the first regression
does. Zero headroom, per `CHECK_AUTHORING_GUIDE` §2.3. It reads **source**, not the generated
artifact, so the auto-regen path cannot launder a regression past it.

⚠️ **Not a hard fail on absence, deliberately.** Three of the four are `__init__.py`, where a
docstring is a style question rather than a defect, and a gate that fires on correct work gets
switched off (`VALIDATION_GATE_TOPOLOGY` §3). The ratchet gets the same pressure without the
false positive.

⚠️ **ONE RATCHET, NOT TWO — this reverses an operator choice on new evidence, and says so.**
The operator chose "ratchet both populations, down-only" when presented with two. The second
population turned out to be a measurement artifact of my own threshold, not a thing (C4). Shipping
it would have gated docstring *style* against an arbitrary character count and reddened the suite
over three good docstrings. The choice was sound on the information given; the information was
wrong, and re-deriving it is what step 2 of this sequence is for.

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

⚠️ **D6 COVERS THREE BODIES OF PROSE, NOT ONE — an earlier draft named only Inventory §1 and the
asymmetry was unexplained.** Measured: §1 holds **52** `Purpose:` entries over 52 `src/` paths and
**zero** `scripts/` paths, so "roughly 40 modules" understated it and the scripts were uncovered.
The three:

* **Inventory §1** — 52 `src/` `Purpose:` entries. Three of its backticked paths are bare
  basenames (`constants.py`, `formulas.py`, `mean_field.py`) that do not resolve from the repo
  root, so migration re-anchors rather than transplants.
* **Index §11** — the scripts prose, which the census's `scripts/` half supersedes only where a
  docstring already says as much.
* **Index §3.1** — the hand-maintained Lean subdirectory table's `Purpose` column. ⚠️ **This is
  the object the operator asked about by name**, and its counts are derivable while its prose is
  not. The counts die with the file; the prose migrates into the corresponding
  `lean/SKEFTHawking/<family>/` module docstrings, or is explicitly accepted as lost — silently
  deleting it is the failure C5 exists to prevent.

⚠️ **Inventory §4, §5, §6, §7 and §10 are NOT yet audited.** The Context's claim that the unique
content is "§1 plus Index §8/§11" is established for those sections only. §4 (notebooks), §5
(papers), §6 (tests), §7 (scripts) and §10 (formulas ↔ Lean theorem names) each have a *count* in
`docs/counts.json` as their derived counterpart, **not a description**. P2 audits all five before
P5 deletes the file; whatever is unique either migrates or is named as accepted loss. Retiring a
319 KB file having read two of its ten sections is the sampling this ADR is replacing.

**D7 — `SK_EFT_Hawking_Inventory_Index.md` is retired after the census is green.** Its unique
content is §8 and §11, which the census supersedes; everything else is a second account of a
derived artifact. Retirement unwires **four code sites** (`sync_manifest.py`, `pre-commit-sync.sh`,
`update_inventory_index.py`, `freshness.py`), **six test files**, **four architecture documents**
(`README.md` included — it both routes to the pair and describes the check being deleted) and the
live routing rows in `CLAUDE.md`, `README.md`, `PAPER_STRATEGY.md` and `RESEARCH_STATUS_OVERVIEW.md`.

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

**D2 RESOLVED 2026-08-13 — §1's API enumeration is NOT a regression, measured.** The operator's
rule is that replacing hand-rolled with derived is always preferred and *regressions are
show-stoppers*, so this was audited before P5 deleted anything.

| measured at HEAD | result |
|---|---|
| module blocks §1 actually details | **27** of 318 — 8.5% coverage, against a header claiming 132 modules |
| files it names that no longer exist | **0** |
| enumerated names appearing nowhere in their module | **0** |
| per-module line counts that are STALE | **24 of 27** — `constants.py` claims 242 lines against 6730, off by 28× |

So the *names* are accurate and the *numbers* are almost entirely wrong. And the names are not
unique content: every one is recoverable from the AST, authoritatively, which is how this audit
compared them.

**The only candidate-unique content was the per-name gloss, and the code already carries more.**
`ATOMS` and `EXPERIMENTS` are glossed in §1 as one line each; in `constants.py` they sit under
banner comments citing NIST, Kempen et al. (2002) and Falke et al. (2008) — provenance §1 never
had. The symbol is the right home for the gloss; a parallel file is precisely the drift mechanism
this ADR removes.

**Deriving it inline was measured and rejected.** 3524 public top-level names across the 318
modules is roughly +62 KB onto a 38 KB census — 2.6×, which breaks the *fits in a single `Read`*
property C4 justifies the census on. It would also duplicate what `grep` and the language server
already answer instantly, which is building beside an existing mechanism.

**Disposition: deleted, not migrated, and not an accepted loss** — there is nothing to lose. The
27 stale line counts are removed with it, which is a net gain in accuracy.

**D10 — The mutation obligation MOVES; it is not deleted.** `inventory_index_autogen_fresh`'s
four production-seeded mutations, its `PRODUCTION_SEEDED` membership and its `MUTATION_VERIFIED`
entry transfer to `module_census_fresh`. `FIXTURE_ONLY_CEILING` is re-measured in the same commit.
Deleting a check that carries a mutation entry silently loosens the ratchet that tracks them.

⚠️ **D10 CORRECTED 2026-08-13, measured at HEAD. Nothing transfers, and that is the stronger
result.** Three of the Index check's four legs guard hazards the census **does not have**:

| Index leg | what it guards | census |
|---|---|---|
| `size_ceiling` | the Index bloating past the limit it declares for itself | no declared ceiling — it is generated whole |
| `no_counts_outside_autogen` | a hand-written count drifting in the narrative | **no narrative exists** |
| `narrative_seam` | an unmatched `AUTOGEN` marker masking the lines after it | **no markers, no hand-edited region** |
| AUTOGEN freshness (advisory) | the generated block going stale | census `stale` leg — **blocking, not advisory** |

The census is *stronger* on the only leg with a counterpart, and the other three are moot by
construction. That is the whole point of D1: the hazard is designed out rather than guarded.
"The obligation moves" would have had P3 manufacture legs for hazards that cannot occur.

**P3 therefore cannot be a standalone commit, and folds into P4.** `test_d5_mutation_obligation`
requires **every registered check** to carry a `MUTATION_VERIFIED` entry — measured: 83 of 83.
Removing the Index check's entry while the check still exists turns that test red. The entry and
the check are deleted together or not at all.

**`FIXTURE_ONLY_CEILING` stays 54; measured, not assumed.** It counts registered checks *not*
production-seeded — live 54 against a ceiling of 54, **zero slack**. `inventory_index_autogen_fresh`
IS production-seeded, so deleting it moves registered 83→82 and `PRODUCTION_SEEDED` 29→28 while
the fixture-only count is untouched. A ceiling that may only be lowered therefore holds at 54,
and P4 lowers `CI_MIN_CHECKS_RUN` alone.

⚠️ **`CI_MIN_CHECKS_RUN`'s arithmetic in the table below is STALE.** It reads "+1 at P1 and −1 at
P4 … nets to zero". A second check (`existential_witness_disclosure`) took it to **79** on
2026-08-13, so P4's −1 lands on 79 and the plan no longer nets to zero. The one-in-one-out framing
was only ever true of this ADR's own checks.

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

⚠️ **P1's registration list is derived from code, not quoted — and an earlier draft of this plan
named four of the eleven sites.** A check that registers without them breaks frozen contracts on
arrival. The full set, each verified at HEAD:

| site | why |
|---|---|
| `scripts/validation/checks/freshness.py` | the check itself |
| `validate._CANONICAL_ORDER` | execution order is data, not import order (H3) |
| re-export in `scripts/validate.py` | the module-attribute surface other tooling reads |
| `EXPECTED_CHECKS` in `tests/test_validate_registry_contract.py` | frozen **count *and* order** — two tests fire |
| `EXPECTED_CHECK_FUNCTIONS` in `tests/test_validate_public_surface.py` | frozen function roster |
| `CI_MIN_CHECKS_RUN` in `scripts/validation/_config.py` | ⚠️ **+1 at P1, −1 at P4 — but it NO LONGER NETS TO ZERO.** `existential_witness_disclosure` took it to **79** on 2026-08-13, so P4's −1 lands on 79, not 78. "One in, one out" was only ever true of this ADR's own checks; re-read the live value before changing it |
| `tests/test_d5_mutation_obligation.py` | `MUTATION_VERIFIED` + `PRODUCTION_SEEDED` + `FIXTURE_ONLY_CEILING` |
| `tests/test_cannot_measure_baseline.py` | two zero-headroom floors, both re-measured at P4. ⚠️ `existential_witness_disclosure` was added to `CANNOT_MEASURE_PASS_BASELINE` 2026-08-13 |
| `tests/test_sync_manifest.py` | asserts the edge roster by name |
| `scripts/verify_scope.py` | the `code` bucket (`src/`, `scripts/`) must reach `module_census_fresh` — those are its inputs |
| `docs/architecture/SURFACE_INVENTORY.md` | regenerated |

`CI_SKIP` correctly takes no entry: the census is cheap.

| phase | what | gate |
|---|---|---|
| **P1** | Ship `scripts/module_census.py` (carrying C4's derivation, so the baseline is reproducible) + `docs/MODULE_CENSUS.md` + `module_census_fresh` with `NO_DOCSTRING_CEILING`, register the `Edge`, add to `pre-commit-sync.sh`'s restage list, **and every row of the table above**. Production-seeded mutation per leg. | census green, mutation red-then-green, registry-contract tests green |
| **P2** | D6 — migrate the Inventory's richer `Purpose:` prose into module docstrings, per module. ⚠️ Per C8 a docstring is now a **published** surface, so each migration is staged through the disclosure hook and judged there — this is not a pure refactor. | census re-run shows the migrated text; disclosure hook clean |
| ~~**P3**~~ | **FOLDED INTO P4 (2026-08-13).** D10's transfer does not exist — three of the Index check's four legs guard hazards the census does not have, and the fourth is stronger on the census. The entry removals cannot precede the deletion, because every registered check must carry a `MUTATION_VERIFIED` entry. See the corrected D10. | — |
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

⚠️ **P4 IS ORDER-SENSITIVE WITHIN ITSELF.** `sync_manifest._index_autogen_stale` imports
`update_inventory_index.compute_stale`. Delete the script while its `Edge` survives and
`stale_artifacts()` raises inside `sync.py --fast` — **on every commit**, for everyone. The Edge
comes out in the same commit as the script, or before it. (`pre-commit-sync.sh:50` is safe either
way; it guards with `[ -f "$f" ]`, so a mid-migration checkout degrades quietly rather than
breaking.)

⚠️ **P5's GATE CANNOT SEE MOST OF THE BLAST RADIUS, AND THAT WOULD BE FALSE ASSURANCE.**
`doc_refs_resolve` scans **`docs/architecture/*.md` only**. The retirement's largest consumer is
the repo front door: `README.md` carries four live routing rows ("See what's been built →
Inventory_Index", "Check the full inventory → Inventory"), plus `docs/PAPER_STRATEGY.md`
("module-level ground truth") and `docs/RESEARCH_STATUS_OVERVIEW.md`. None is reachable by that
check. `docs/architecture/README.md`'s references are markdown links, whose form the leg's
path-like regex does not match either. **P6 repoints all of them by hand and the gate is a manual
grep, stated as such** — a green `doc_refs_resolve` after P5 proves less than it appears to.

⚠️ **D9 does not exempt these.** Dated roadmap and audit records stay; **live routing rows are
repointed.** The distinction is whether the sentence tells a reader where to go now.

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
