# Bundle Directory Schema

**Phase 7a.1.1 deliverable.** Canonical reference for the on-disk layout and
machine-readable metadata of every `papers/<bundle>/` directory.

Single source of truth for the consumers of this schema:

- `scripts/bundle_source_manifest.py` — initializes layout + writes `source_manifest.md` + `bundle_metadata.json`
- `scripts/bundle_append.py` — absorbs new source into bundle; updates `change_log.md` + `append_log.json` + `bundle_metadata.json`
- `scripts/check_bundle_source_freshness.py` — `validate.py --check bundle_source_freshness` (CHECK 22)
- `scripts/datastar_bundles.py` — feeds dashboard "Bundles" tab from `bundle_metadata.json`
- `scripts/bundle_closure.py` — derives each bundle's substrate from its declared `apex_theorems`; `validate.py --check bundle_apex_resolves`
- `docs/BUNDLE_LIFT_PROCEDURE.md` — canonical 14-step lift workflow (consumes the schema)
- `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md` — robustness protocol (consumes the schema)

---

## On-disk layout

```
papers/<bundle>/
  paper_draft.tex            # main LaTeX, the bundle's content (built incrementally)
  bibliography.bib           # merged from source-paper bibliographies
  figures/                   # figures lifted from source papers + new bundle-specific
  tables/                    # auto-rendered from tables.py (Phase 5v pipeline)
  sentence_state.json        # sentence-level provenance with bundle_destination tags
  audit_log.jsonl            # claims-reviewer + figure-reviewer audit trail (append-only)
  READINESS_GATES.md         # per-bundle gate panel (analog of per-paper file)
  tables.py                  # optional; spec for auto-rendered tables
  claims_review.json         # Stage 10 output (skeft-qa:claims-reviewer)
  figures/figure_review_report.json  # Stage 9 output (skeft-qa:figure-reviewer)
  source_manifest.md         # human-facing list of contributing sources (auto-gen)
  change_log.md              # human-readable append history
  append_log.json            # machine-readable append history
  bundle_metadata.json       # canonical machine-readable bundle state (this schema)
```

**Mandatory:** `paper_draft.tex`, `source_manifest.md`, `change_log.md`, `append_log.json`, `bundle_metadata.json`. All others are produced incrementally as the lift proceeds; their absence is not an error in early stages.

---

## `bundle_metadata.json` schema

```json
{
  "bundle_target": "I1",
  "tier": 3,
  "title": "Verification Methodology with Worked Cases",
  "target_journal": "CPC | Phys. Rep.",
  "length_target": {"unit": "pages", "floor": 15, "ceiling": 38, "source": "PAPER_STRATEGY.md §6"},
  "compiled_pages": null,
  "phase7_subphase": "7a",
  "stage9_status": "pending",
  "stage10_status": "pending",
  "stage13_status": "pending",
  "stage13_redo_required": false,
  "freshness_stale": false,
  "source_manifest_last_regen": "2026-04-30T12:00:00Z",
  "last_lift": "2026-04-30T12:00:00Z",
  "last_stage9_review": null,
  "last_stage10_review": null,
  "last_stage13_review": null,
  "blockers_open": 0,
  "advisories_open": 0,
  "stage13_review_doc": null,
  "stage13_review_kind": null,
  "audit_log_path": "papers/I1/audit_log.jsonl",
  "supersession_ledger_anchor": "docs/review_finding_supersessions.json",
  "notes": null
}
```

### Field semantics

| Field | Type | Allowed values | Updated by |
|---|---|---|---|
| `bundle_target` | string | any code on the authorized roster (`scripts/bundle_registry.py`) | created at init; never mutates |
| `tier` | int | `0` (F), `1` (D*), `2` (L*), `3` (I*), `4` (E*) | created at init |
| `title` | string | freeform | created at init from `PAPER_STRATEGY.md` |
| `target_journal` | string | freeform (e.g., `"PRL"`, `"PRD"`, `"CPC \| Phys. Rep."`) | created at init from `PAPER_STRATEGY.md` |
| `length_target` | object \| null | `{unit, floor, ceiling, source}` — see below | **hand-declared** (ADR-011 §Phase 1) |
| `compiled_pages` | int \| null | ≥1 | `compile_bundle_pdf.py` on every compile |
| `compile_gate_ok` | bool \| null | — | `compile_bundle_pdf.py`; the last gate verdict. **A `true` here is what licenses the recompile skip** — a draft whose last verdict was FAIL recompiles every run, because skipping asserts the gate passed |
| `phase7_subphase` | string | `7a`, `7b`, `7c`, ... | set by `bundle_source_manifest.py` based on roadmap |
| `stage{9,10,13}_status` | string | `green` \| `yellow` \| `red` \| `pending` \| `pending-redo` \| `skeleton` \| `not_started` | **`scripts/record_review.py`** (ADR-011 Phase 2); `pending` also at init, and on append |
| `stage13_review_kind` | string \| null | `full-adversarial` \| `attribution-sweep` \| `section-scoped` \| `figure-only` | `record_review.py`; required for any Stage-13 verdict |
| `stage13_redo_required` | bool | — | set `true` by `bundle_append.py` on every absorption; set `false` by Stage-13 reviewer when bundle review re-clears |
| `freshness_stale` | bool | — | set `true` by CHECK 22 if any source paper modified after `last_lift`; cleared after Stage-13 re-invocation |
| `source_manifest_last_regen` | ISO timestamp | UTC `YYYY-MM-DDTHH:MM:SSZ` | `bundle_source_manifest.py` on every run |
| `last_lift` | ISO timestamp | — | `bundle_append.py` on every successful append |
| `last_stage{9,10,13}_review` | ISO timestamp \| null | — | reviewer-agent invocation |
| `blockers_open` | int | ≥0 | reviewer-agent (sum across stages 9/10/13) |
| `advisories_open` | int | ≥0 | reviewer-agent |
| `stage13_review_doc` | string \| null | path | `record_review.py`; must exist on disk. Latest Stage-13 doc under `papers/AutomatedReviews/<DATE>-bundle-stage13/<X>.md` |
| `audit_log_path` | string | path | created at init |
| `supersession_ledger_anchor` | string | path | created at init; canonical `docs/review_finding_supersessions.json` |
| `notes` | string \| null | freeform | optional human notes (e.g., "I2 ships software-only pending Mathlib upstream") |
| `apex_theorems` | list \| absent | `["<fqn>"]` or `[{"name", "claims", "declared"}]` | **hand-declared** — the results this bundle claims (ADR-010 §D5a) |

#### `apex_theorems` — the one hand-maintained input to the substrate closure

The bundle's substrate is the **derived transitive closure** of these apexes over
`name_deps_project` (`scripts/bundle_closure.py`), so nothing about the substrate is declared and
nothing about it can drift. That concentrates the whole drift risk into these few names, which is
why `validate.py --check bundle_apex_resolves` gates them: an apex naming no live declaration, or
naming something other than a theorem, fails the suite.

It lives **here**, per bundle, rather than in a central registry, because merging two bundles must
concatenate apex lists and splitting must partition them — co-located lists do that by moving a
file.

⚠️ **Absent is UNKNOWN, not empty.** A bundle that has never declared apexes has an *unknown*
substrate; the closure machinery reports `closure_measurable: false` and publishes no size, and
`bundle_apex_resolves` counts it against `UNDECLARED_APEX_CEILING` — a shrink-only ratchet, now at
its target of **0**, so any bundle added without declared apexes fails the suite. (Read the live
value from `scripts/validation/checks/bundles_readiness.py`, never from this sentence.) Writing
`"apex_theorems": []` to quiet a tool is therefore not a fix — it asserts the bundle claims nothing.

Declaring apexes for an existing bundle requires **full per-bundle context review** — contributing
roadmaps, the Lean cited, the claims record — one bundle at a time (ADR-010 §D5a, operator
condition). For new work the intended moment is **wave close**, where the author context is
already loaded.

⚠️ **The `claims` string is a PUBLISHED ASSERTION, and it has two readers.**
`apex_theorem_claims_grounded` (ADR-015 D3) requires it to be present, not a restatement of the
theorem's own name, and to carry no numeral its statement cannot account for.
`apex_claims_not_vacuous` (ADR-016) requires the declaration underneath it not to be one the
project records or derives as content-free — `PLACEHOLDER_THEOREMS`, a `True` / reflexive
statement, `VACUOUS_STATEMENT_BASELINE`, a `definitional` / `vacuous_proxy` disclosure, or a
trivial proof witness.

**The one escape from the second is DISCLOSURE, in the `claims` string itself.** A bundle may keep
a content-thin apex by saying so in the words a referee reads — *"⚠️ DEFINITIONAL ENCODING … an
`rfl` sanity-check"* is the live idiom, written by drafters before any check asked for it. That
moves the row out of the undisclosed ratchet and **not** out of the total, so honesty is never room
to add another. Adding the declaration to a suppression register is not a repair and is refused by
ADR-016 D4; the repairs are **strengthen the theorem**, **withdraw the apex**, or **say what the
statement actually carries**.

#### `stage{9,10,13}_status` — who writes a `green`, and what it takes

Use **`scripts/record_review.py`**. It is the only writer that produces a verdict, and it
refuses three things a hand edit cannot be stopped from doing:

- a **Stage-13 green while Stage 9 or 10 is not green** (`BUNDLE_LIFT_PROCEDURE.md:9`);
- a **Stage-13 verdict with no `stage13_review_kind`** — a targeted attribution sweep and a
  full fresh-context adversarial pass are different evidence, and only `full-adversarial`
  earns a green;
- a **`--doc` that does not exist on disk.**

⚠️ **Until 2026-08-08 nothing wrote `green` at all.** Creation set `pending` and
`bundle_append.py` demoted `green` back to `pending`; no code path produced one. Every green
in the corpus was a hand edit, which is why bundle status could not be read as evidence of
review (`END_TO_END_MAP.md` §8, transition 2). Hand edits remain possible — they are caught
after the fact by `validate.py --check bundle_reviewer_stage_ordering` and
`--check bundle_stage13_claim_consistent`, not prevented.

The value set is wider than `Phase7a_Roadmap.md:91-93` declares: the live corpus also uses
`pending-redo`, `skeleton` and `not_started`. All seven are declared in
`_STAGE_STATUS_VALUES`, and an undeclared value is a finding rather than silently read as
"not green, therefore safe".

#### `length_target` — the charter's size commitment, and the only field `bundle_manuscript_length` can fail on

```json
"length_target": {"unit": "pages", "floor": 24, "ceiling": 60, "source": "PAPER_STRATEGY.md §6"}
"length_target": {"unit": "word_equivalents", "ceiling": 3750, "source": "PRL author guide"}
```

- `unit` — `pages` for article-class targets, `word_equivalents` for letter-class ones (PRL counts
  text + 300/figure + tables + captions + references, so a page count is the wrong instrument).
- `floor` — optional. Omit where the venue has none; a letter has no floor. Where present it
  catches **the failure a ceiling cannot**: a deep paper that is really a letter.
- `ceiling` — required.
- `source` — where the numbers came from, so a later reader can re-derive rather than trust them.

⚠️ **`null` is UNDECLARED, not unlimited.** A bundle whose target is not yet settled records
`"length_target": null`, and `bundle_manuscript_length` reports it **UNMEASURED — never PASS**.
The same holds when the draft does not compile: no page count exists, so no verdict is available,
and a check that cannot measure must say so rather than pass (ADR-009 D2).

⚠️ **This is a current commitment, not a freeze.** Venues and the roster may still move
(ADR-010 §Open item 1; operator direction 2026-08-08). Re-targeting a bundle means editing this
field and its `source` — it is data with provenance, not a constant.

### Aggregate verdict (computed, not stored)

The bundle's overall verdict (🟢/🟡/🔴) is computed by `scripts/bundle_readiness.py --heatmap` from the three `stage{9,10,13}_status` fields plus `blockers_open`. Rules (consistent with existing heatmap logic):

- 🟢 GREEN: all three stages `green` AND `blockers_open == 0`
- 🟡 YELLOW: all three stages `green` OR `pending`, `blockers_open == 0`, `advisories_open ≤ 5`
- 🔴 RED: any stage `red` OR `blockers_open ≥ 1`

`pending` stages are treated as "not yet attempted" and do not block YELLOW; only `red` stages block.

---

## `append_log.json` schema

Append-only record of every absorption event.

```json
{
  "bundle_target": "D5",
  "events": [
    {
      "date": "2026-04-30T13:00:00Z",
      "source_paper": "paper17_dark_sector",
      "lift_action": "Lift-section",
      "bundle_section_inserted": "§ Cosmological constraints / §§ SFDM cluster mergers",
      "insertion_point_hint": "§2-§3",
      "new_top_level_section": false,
      "new_section_rationale": "",
      "lean_modules_referenced": [
        "DarkSectorClassification",
        "DarkSectorCausalStructure"
      ],
      "citation_count_added": 12,
      "stage13_redo_required": true,
      "agent_run_id": "bundle_append-2026-04-30-13:00",
      "notes": "Initial lift; D5 §2-§3 from paper17 SFDM cluster-merger forecast."
    }
  ]
}
```

The `agent_run_id` is `bundle_append-<ISO timestamp>` for fully reproducible idempotency.

`bundle_section_inserted` is the **resolved** anchor — the section (and, in the normal
case, the subsection) the lift actually landed in — not the caller's `--insertion-point`
hint, which is preserved separately as `insertion_point_hint`. The absorption protocol
reads the anchor to find a lift, and a hint like `§13` names a position no reader can
locate in the draft. `new_top_level_section` / `new_section_rationale` record the ADR-011
F-02 decision: a source registration lands as a `\subsection` inside an existing section
unless the operator explicitly said the bundle's argument structure is changing.

Events written before F-02 (2026-08-09) carry the hint in `bundle_section_inserted` and
omit the three newer fields; readers must tolerate both shapes. One hand-authored event
(bundle F, `lift_action: "Revision"`) has no `bundle_section_inserted` at all.

---

## `source_manifest.md` format

Auto-generated; do not hand-edit. One row per source paper that maps to this bundle.

```markdown
# Bundle <X> — Source Manifest

**Auto-generated:** 2026-04-30
**Tool:** `scripts/bundle_source_manifest.py`
**Source mapping:** `docs/PAPER_DRAFT_MAPPING.md`
**Bundle anchor list:** `docs/agents/claims-reviewer-bundle-prompts.md` §<X>

## Contributing source papers

| Source paper | Bundle section | Lift action | Phase / Wave | Last source modification |
|---|---|---|---|---|
| `paper17_dark_sector` | §2-§3 | Lift-section | Phase 5x W1 | 2026-04-15 |
| `paper29_bbn_unified` | §4 | Lift-section | Phase 6h W2 | 2026-04-20 |

## Coverage notes

- Insertion points are the hint from `PAPER_DRAFT_MAPPING.md`'s "New destination(s)" column.
- "Last source modification" is the latest mtime in `papers/<source>/`.
- `Lift-flagship` rows appear in the F bundle's manifest as well as the source's primary bundle.
```

---

## `change_log.md` format

Human-readable bundle-level history. One H2 per dated event.

```markdown
# Bundle <X> — Change Log

## 2026-04-30 — Initial lift (paper17 → D5 §2-§3)

Phase 7b sub-wave 7b.1.1: Lift paper17 SFDM cluster-merger content into D5 §2-§3.

- Sentences migrated: 184
- Bibkeys merged: 12
- Figures lifted: 3 (renamed `fig_sfdm_*.png`)
- Stage-13 redo required: yes (next sweep covers the new §2-§3)
```

---

## Cross-references

- `docs/BUNDLE_LIFT_PROCEDURE.md` — 14-step canonical lift workflow that consumes this schema
- `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md` — robustness protocol (Stages A-G)
- `docs/PAPER_STRATEGY.md` — bundle architecture; §6 is the human-authoritative roster
- `docs/PAPER_DRAFT_MAPPING.md` — per-source → per-bundle assignment table
- `docs/agents/claims-reviewer-bundle-prompts.md` — per-bundle Stage-13 anchor list
- **`scripts/bundle_registry.py` — THE source of truth for bundle code + tier + title + target journal + subphase.** Authorizing a bundle means one row in `PAPER_STRATEGY.md` §6 and one `Bundle(...)` record here; every other module derives from it, and `validate.py --check bundle_registry_consistency` fails the suite if one re-hardcodes the roster or drifts from the strategy doc.
- `scripts/sentence_state.py` — `_VALID_BUNDLE_TARGETS`, a back-compat alias re-exported from `bundle_registry` (it was the *nominal* source of truth until 2026-07-30, but six other modules kept their own copies)
- Pipeline Invariant #14 (`WAVE_EXECUTION_PIPELINE.md`) — bundle assignment mandatory at Stage 1

---

*Created Phase 7a sub-wave 7a.1.1 (2026-04-30). The schema is consumed by ≥4 scripts; any breaking change must update all consumers in the same wave.*

---

**Validation footnote (2026-05-07).** Validated against the bundles' actual on-disk state through Phase 7 absorption Session 5 (2026-05-08), when the roster stood at 14. Schema breaking-change discipline has been maintained since — no field renames, no removed fields, only optional additions — and every roster growth after that date (I3, D6, D7, D8, D9, D10, D11, D12) has been an additive enum extension breaking no prior consumer.

⚠️ **`_VALID_BUNDLE_TARGETS` is an alias, not a roster.** It re-exports `VALID_BUNDLE_TARGETS` from `scripts/bundle_registry.py`, which is the single owner; `scripts/sentence_state.py` and `scripts/review_runner.py` consume the alias. This footnote used to enumerate the enum's members inline in the present tense, which is a copy of a registry rather than a reference to one: it went stale on the next authorization and then contradicted the code it documents. **Read the members from the registry** (censused in `docs/architecture/SURFACE_INVENTORY.md`), and do not restore a list here.
