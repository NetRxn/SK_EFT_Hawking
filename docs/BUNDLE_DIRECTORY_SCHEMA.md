# Bundle Directory Schema

**Phase 7a.1.1 deliverable.** Canonical reference for the on-disk layout and
machine-readable metadata of every `papers/<bundle>/` directory.

Single source of truth for the consumers of this schema:

- `scripts/bundle_source_manifest.py` — initializes layout + writes `source_manifest.md` + `bundle_metadata.json`
- `scripts/bundle_append.py` — absorbs new source into bundle; updates `change_log.md` + `append_log.json` + `bundle_metadata.json`
- `scripts/check_bundle_source_freshness.py` — `validate.py --check bundle_source_freshness` (CHECK 22)
- `scripts/datastar_bundles.py` — feeds dashboard "Bundles" tab from `bundle_metadata.json`
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
  claims_review.json         # Stage 10 output (physics-qa:claims-reviewer)
  figures/figure_review_report.json  # Stage 9 output (physics-qa:figure-reviewer)
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
  "audit_log_path": "papers/I1/audit_log.jsonl",
  "supersession_ledger_anchor": "docs/review_finding_supersessions.json",
  "notes": null
}
```

### Field semantics

| Field | Type | Allowed values | Updated by |
|---|---|---|---|
| `bundle_target` | string | one of `_VALID_BUNDLE_TARGETS` (`F`, `D1`–`D5`, `L1`–`L3`, `I1`, `I2`, `E1`, `E2`) | created at init; never mutates |
| `tier` | int | `0` (F), `1` (D*), `2` (L*), `3` (I*), `4` (E*) | created at init |
| `title` | string | freeform | created at init from `PAPER_STRATEGY.md` |
| `target_journal` | string | freeform (e.g., `"PRL"`, `"PRD"`, `"CPC \| Phys. Rep."`) | created at init from `PAPER_STRATEGY.md` |
| `phase7_subphase` | string | `7a`, `7b`, `7c`, ... | set by `bundle_source_manifest.py` based on roadmap |
| `stage{9,10,13}_status` | string | `pending` \| `green` \| `yellow` \| `red` | reviewer-agent invocation (Stage 9/10/13) |
| `stage13_redo_required` | bool | — | set `true` by `bundle_append.py` on every absorption; set `false` by Stage-13 reviewer when bundle review re-clears |
| `freshness_stale` | bool | — | set `true` by CHECK 22 if any source paper modified after `last_lift`; cleared after Stage-13 re-invocation |
| `source_manifest_last_regen` | ISO timestamp | UTC `YYYY-MM-DDTHH:MM:SSZ` | `bundle_source_manifest.py` on every run |
| `last_lift` | ISO timestamp | — | `bundle_append.py` on every successful append |
| `last_stage{9,10,13}_review` | ISO timestamp \| null | — | reviewer-agent invocation |
| `blockers_open` | int | ≥0 | reviewer-agent (sum across stages 9/10/13) |
| `advisories_open` | int | ≥0 | reviewer-agent |
| `stage13_review_doc` | string \| null | path | reviewer-agent points to latest Stage-13 doc under `papers/AutomatedReviews/<DATE>-bundle-stage13/<X>.md` |
| `audit_log_path` | string | path | created at init |
| `supersession_ledger_anchor` | string | path | created at init; canonical `docs/review_finding_supersessions.json` |
| `notes` | string \| null | freeform | optional human notes (e.g., "I2 ships software-only pending Mathlib upstream") |

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
      "bundle_section_inserted": "§2-§3",
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
- `docs/PAPER_STRATEGY.md` — 13-bundle architecture; defines tier + title + target_journal
- `docs/PAPER_DRAFT_MAPPING.md` — per-source → per-bundle assignment table
- `docs/agents/claims-reviewer-bundle-prompts.md` — per-bundle Stage-13 anchor list
- `scripts/sentence_state.py` — `_VALID_BUNDLE_TARGETS` enum (the sole source of truth for bundle codes)
- Pipeline Invariant #14 (`WAVE_EXECUTION_PIPELINE.md`) — bundle assignment mandatory at Stage 1

---

*Created Phase 7a sub-wave 7a.1.1 (2026-04-30). The schema is consumed by ≥4 scripts; any breaking change must update all consumers in the same wave.*

---

**Validation footnote (2026-05-07).** Validated against 14 bundles' actual on-disk state through Phase 7 absorption Session 5 (2026-05-08). Schema breaking-change discipline maintained — no field renames, no removed fields, only optional additions. The `_VALID_BUNDLE_TARGETS` enum now covers `F, D1–D5, L1–L3, I1, I2, I3, E1, E2` (14 entries) since I3 authorization at Phase 6n Session 4 under Pipeline Invariant #14; this is an additive enum extension and does not break any prior consumer.
