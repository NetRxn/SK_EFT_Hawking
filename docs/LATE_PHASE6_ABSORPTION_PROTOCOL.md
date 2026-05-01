# Late-Phase-6 Absorption Protocol

**Phase 7a sub-wave 7a.1.6 deliverable** (initial draft; updated with examples on first absorption event).

Step-by-step protocol for absorbing a new Phase 6X wave's output (e.g., Phase 6n, 6o, ...) into already-drafted bundles after Phase 7 sub-phases have started. The load-bearing **robustness** document for the Phase 7 architecture.

**Design rationale.** User direction 2026-04-30: *"i anticipate more phase 6 items being added, make sure the process you put in place for 7a's & the corresponding roadmap is robust to new items that may pop in past 6m."* The bundle architecture (`PAPER_STRATEGY.md` + `PAPER_DRAFT_MAPPING.md`) was designed assuming the source-paper roster is roughly stable; this protocol documents how *append-only* expansion happens with minimal re-work.

**Default branch:** D.2 (additive append via `bundle_append.py`). D.1 is passive; D.3 requires manual author judgment.

---

## Scenario

A new Phase 6X wave ships after Phase 7a (or any subsequent Phase 7 sub-phase) has started. The wave produces:
- Lean modules in `lean/SKEFTHawking/<NewModule>.lean`
- Per-paper drafts in `papers/paperN_*/` (per Pipeline standards)
- Optional working-docs syntheses in `temporary/working-docs/`

Phase 7's bundles must absorb the new content without redrafting.

---

## Protocol Stages

| Stage | Action | Owner | Trigger |
|---|---|---|---|
| **A** | Phase 6X completes its own per-paper Stage-13 closure | Phase 6X | Phase 6X internal |
| **B** | Add row(s) to `PAPER_DRAFT_MAPPING.md` per Pipeline Invariant #14 | Phase 6X owner | Phase 6X close |
| **C** | `bundle_source_manifest.py` re-run; `validate.py --check bundle_source_freshness` flags affected bundles `freshness-stale` | automation | mapping update |
| **D** | Branch by bundle state (D.1 / D.2 / D.3) | Phase 7 owner | freshness flag |
| **E** | F (flagship) auto-flags `freshness-stale` if any Tier-1 bundle absorbs new content | automation | downstream propagation |
| **F** | Stage-13 re-invocation per affected bundle; BLOCKERs resolved | Phase 7 owner + reviewer agents | re-review queue |
| **G** | `validate.py --check bundle_consistency` re-run; `cluster_bundle_index.json` re-frozen | automation | post-review closure |

---

### Stage A — Phase 6X completes its own per-paper Stage-13 closure

Phase 6X follows its own roadmap; produces Lean modules, per-paper drafts, working-docs syntheses. Phase 6X-internal Stage-13 closure (per-paper Stage 13 against its own anchor list) must be GREEN before Stage B.

**Gate:** `validate.py --check readiness_submission_gate` shows no RED papers among Phase 6X's contributions.

### Stage B — Bundle assignment

Phase 6X owner adds a row (or several) to `docs/PAPER_DRAFT_MAPPING.md` Table 1 per Pipeline Invariant #14:

```markdown
| `paperNN_topic` | <Title> | Phase 6X W<wave> | **<Bundle> §<N>** | Lift-section |
```

Each new source paper has explicit `bundle_destination(s)` and `lift_action`. If the new content does not fit any of the existing 13 bundles, **user authorization is required** for a 14th+ bundle target (Pipeline Invariant #14).

**Authorization gates inside Stage B:**
- ≥1 new bundle target → user authorization
- Mapping addition that overrides existing bundle assignment → user authorization
- New `Lift-flagship` row (F absorbs new content directly, not through a Tier-1 sibling) → user authorization

### Stage C — Source manifest detection

Automation:

```bash
uv run python scripts/bundle_source_manifest.py            # all bundles
uv run python scripts/validate.py --check bundle_source_freshness
```

Effects:
- New source rows appear in each affected bundle's `source_manifest.md`.
- `validate.py --check bundle_source_freshness` flags affected bundles `freshness-stale=true` and sets `bundle_metadata.json.freshness_stale=true`.

### Stage D — Branch by bundle state

For each affected bundle, classify into one of three branches:

#### D.1 — Bundle not yet drafted (passive pickup)

`papers/<bundle>/paper_draft.tex` does not exist.

**Action:** none. The new source will be picked up automatically when the bundle's scheduled Phase 7X drafting wave runs (per `Phase7_Roadmap.md` wave catalog).

**Owner:** none (passive).

#### D.2 — Bundle drafted, append-only revision

`paper_draft.tex` exists AND new content is purely additive (new mechanism family, new substrate, new section per `bundle_section_hint`).

**Action:**

```bash
uv run python scripts/bundle_append.py \
    --bundle <X> \
    --source-paper <new_paper> \
    --insertion-point '<§N>' \
    --notes "Late absorption: Phase 6X W<wave> <topic>" \
    --lean-modules "<Module1>,<Module2>"
```

This:
- Appends a new section skeleton at the bundle's insertion point.
- Updates `change_log.md`, `append_log.json`, `bundle_metadata.json`.
- Sets `stage13_redo_required=true`.

Then proceed to Stage F (Stage-13 re-invocation).

**Owner:** Phase 7 sub-phase owner.

#### D.3 — Bundle drafted, revision required

`paper_draft.tex` exists AND new content overturns or refines a prior verdict already documented in the bundle (e.g., a Phase 6n result that flips a Phase 6m NO-GO to PARTIAL-VIABLE on a previously-closed mechanism).

**Action:** **manual author-driven section revision**. No automation can determine whether new content "revises" prior content; the Phase 6X owner flags this in the `PAPER_DRAFT_MAPPING.md` row.

Steps:
1. Author edits the affected `paper_draft.tex` section directly.
2. `change_log.md` entry: "YYYY-MM-DD — REVISION required by Phase 6X W<wave>: <description>".
3. `append_log.json` entry with `lift_action: "Revision"` and `notes` describing the substantive change.
4. Manually set `bundle_metadata.json.stage13_redo_required=true` and `freshness_stale=true`.
5. Proceed to Stage F.

**Owner:** Phase 7 sub-phase owner + lead author. **Stage F re-review is mandatory** (no advisory-only path).

**Authorization gate:** if revision substantially changes bundle's published-claim profile, user authorization is required.

---

### Stage E — Cross-bundle propagation

F (flagship) sources from every Tier-1 bundle. Whenever any Tier-1 bundle absorbs new content (D.2 or D.3), F's `freshness_stale` flag is auto-set during the next `validate.py --check bundle_source_freshness` run because F's source mtimes (its Tier-1 inputs) advance.

The Phase 6X owner notes downstream-affected bundles in the `PAPER_DRAFT_MAPPING.md` row's "New destination(s)" column where applicable (e.g., `**D5 §13** + **F §8.4**`).

**Owner:** automation (validate.py); annotation by Phase 6X owner.

---

### Stage F — Re-review

Each `freshness-stale` bundle re-invokes the canonical reviewer triple per `BUNDLE_LIFT_PROCEDURE.md` §8 / §9 / §10 / §11, with `bundle_target=<X>`:

| Stage | Agent | Output | Pass criterion |
|---|---|---|---|
| 9 | `physics-qa:figure-reviewer` (`bundle_target=<X>`) | `papers/<X>/figures/figure_review_report.json` | ALL PASS |
| 10 | `physics-qa:claims-reviewer` (`bundle_target=<X>`) | `papers/<X>/claims_review.json` | zero FAIL |
| 13 | `adversarial-reviewer` via `scripts/review_runner.py --bundle <X> --prep-brief` | `papers/AutomatedReviews/<DATE>-bundle-stage13/<X>.md` | zero BLOCKER |

**BLOCKER resolution:** per `BUNDLE_LIFT_PROCEDURE.md` §11. Author fixes → supersession ledger append → re-invoke same reviewer fresh context → iterate to clean.

**Update:** `bundle_metadata.json.stage{9,10,13}_status` updated; `freshness_stale` cleared once `blockers_open == 0` and all three statuses GREEN.

**Mandatory dashboard refresh** (every sub-wave exit per `BUNDLE_LIFT_PROCEDURE.md` §13):

```bash
uv run python scripts/datastar_bundles.py
uv run python scripts/bundle_readiness.py --heatmap
uv run python scripts/validate.py --check bundle_consistency --check bundle_source_freshness
```

---

### Stage G — Cross-bundle consistency final pass

```bash
uv run python scripts/validate.py --check bundle_consistency
```

Any cross-bundle cluster drift surfaced by sentence-level provenance reformation must be resolved.

If sentence-level migration was needed (prose_state.json affected), re-run:

```bash
uv run python scripts/bundle_migration.py --paper <new_paper>
uv run python scripts/bundle_clusters.py
```

`papers/cluster_bundle_index.json` re-frozen.

**Authorization gate:** if cross-bundle cluster drift introduces a contradiction across siblings (e.g., flagship F asserts X and the new D5 §13 asserts ¬X), user authorization is required to resolve which version is canonical.

---

## Branch decision (D.1 vs D.2 vs D.3) — quick reference

| Condition | Branch | Owner |
|---|---|---|
| `papers/<bundle>/paper_draft.tex` does not exist | **D.1** | passive (no action) |
| `paper_draft.tex` exists AND new content is additive | **D.2** | Phase 7 sub-phase owner |
| `paper_draft.tex` exists AND new content overturns/refines prior content | **D.3** | Phase 7 owner + lead author |

---

## Worked example (synthetic, pending first real absorption)

**Scenario:** Phase 6n ships in 2026-Q3 — a new mechanism family for dark-energy substrate constraints (call it `paper46_phase6n_topic`). It maps to D5 §14 (additive) and F §10.6 (downstream propagation).

**Stage A:** Phase 6n's per-paper Stage-13 closure GREEN.

**Stage B:** add row to `PAPER_DRAFT_MAPPING.md`:
```markdown
| `paper46_phase6n_topic` | New mechanism family X | Phase 6n W3 | **D5 §14** + **F §10.6** | Lift-section |
```

**Stage C:** `bundle_source_manifest.py` re-run; D5 + F flagged `freshness_stale`.

**Stage D:** D5 → branch D.2 (paper_draft.tex exists, additive). F → branch D.1 if F not yet drafted (likely; F is Phase 7g) OR D.2 if drafted.

**For D.2 (D5):**
```bash
uv run python scripts/bundle_append.py \
    --bundle D5 --source-paper paper46_phase6n_topic \
    --insertion-point '§14' \
    --notes "Phase 6n W3 absorption: new mechanism family X" \
    --lean-modules "Phase6nMechanismX"
```

**Stage E:** F auto-flagged `freshness_stale` after next CHECK 22 run (F lifts from D5).

**Stage F:** Re-invoke reviewer triple on D5; on F if drafted; resolve BLOCKERs.

**Stage G:** `validate.py --check bundle_consistency` re-run.

---

## User authorization gates (consolidated)

The following protocol stages may require explicit user authorization before proceeding:

1. **Stage B** — if Phase 6X output does not fit any of the existing 13 bundle targets (Pipeline Invariant #14, 14th+ bundle target).
2. **Stage B** — if mapping addition overrides existing bundle assignment for a previously-mapped paper.
3. **Stage B** — if new `Lift-flagship` row absorbs Phase 6X content directly into F without going through a Tier-1 sibling.
4. **Stage D.3** — if revision substantially changes bundle's published-claim profile.
5. **Stage G** — if cross-bundle cluster drift introduces a contradiction across siblings.

---

## Cross-references

- `docs/BUNDLE_LIFT_PROCEDURE.md` — canonical lift workflow (Stages F / G re-use §8 / §9 / §10 / §11 / §13 from there)
- `docs/BUNDLE_DIRECTORY_SCHEMA.md` — `bundle_metadata.json` schema; `append_log.json` schema
- `docs/PAPER_STRATEGY.md` — 13-bundle architecture; defines bundles eligible for late absorption
- `docs/PAPER_DRAFT_MAPPING.md` — per-source → per-bundle assignment table; modified during Stage B
- `docs/agents/claims-reviewer-bundle-prompts.md` — per-bundle Stage-13 anchor list (consumed by Stage F)
- `scripts/bundle_source_manifest.py` — Stage C automation
- `scripts/bundle_append.py` — Stage D.2 automation
- `scripts/check_bundle_source_freshness.py` — Stage C / E flag-setting
- `scripts/bundle_migration.py` + `scripts/bundle_clusters.py` — Stage G automation
- `scripts/validate.py --check bundle_source_freshness` (CHECK 22) — automation entrypoint
- `scripts/validate.py --check bundle_consistency` (CHECK 21) — Stage G entrypoint
- Pipeline Invariant #14 — bundle assignment mandatory at Stage 1; user authorization for new bundle targets

---

*Created Phase 7a sub-wave 7a.1.6 (2026-05-01). Updated with worked-example examples on first real absorption event. Cross-referenced from `BUNDLE_LIFT_PROCEDURE.md`, `Phase7_Roadmap.md`, `Phase7a_Roadmap.md`, `WAVE_EXECUTION_PIPELINE.md`.*
