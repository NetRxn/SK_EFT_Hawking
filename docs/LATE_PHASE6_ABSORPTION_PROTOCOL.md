# Late-Phase-6 Absorption Protocol

**Phase 7a sub-wave 7a.1.6 initial draft (2026-05-01); audited and FROZEN at sub-wave 7a.4 (2026-05-01) via conceptual rehearsal of "what if a hypothetical Phase 6n landed during sub-wave 7a.2/7a.3."** Updated with worked-example examples on first real absorption event.

Step-by-step protocol for absorbing a new Phase 6X wave's output (e.g., Phase 6n, 6o, ...) into already-drafted bundles after Phase 7 sub-phases have started. The load-bearing **robustness** document for the Phase 7 architecture.

**Design rationale.** User direction 2026-04-30: *"i anticipate more phase 6 items being added, make sure the process you put in place for 7a's & the corresponding roadmap is robust to new items that may pop in past 6m."* The bundle architecture (`PAPER_STRATEGY.md` + `PAPER_DRAFT_MAPPING.md`) was designed assuming the source-paper roster is roughly stable; this protocol documents how *append-only* expansion happens with minimal re-work.

**Default branch:** D.2 (additive append via `bundle_append.py`). D.1 is passive; D.3 requires manual author judgment. **D.4** (sourceless / Lean-only late absorption) is added at sub-wave 7a.4 freeze after the I2 lift demonstrated that fully-sourceless bundles are a real pattern, not a hypothetical.

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

#### Stage A.alt — Lean-only Phase 6X output (no per-paper draft)

If Phase 6X output is purely Lean-module + working-docs synthesis with **no per-paper draft** (analogous to I2's sourceless pattern from Phase 7a sub-wave 7a.3), Stage A's per-paper Stage-13-closure precondition does not apply. Substitute:

- **Gate (Lean-only):** the Phase 6X Lean modules build cleanly under `lake build` (zero sorry, zero new axioms, zero retroactive cuts) per `WAVE_EXECUTION_PIPELINE.md` Stage 5; substantive content is documented in a working-docs file under `temporary/working-docs/`; ARCHITECTURE_SCOPE.md updated.

- **Stage B variant:** the `PAPER_DRAFT_MAPPING.md` row uses `Lift-action: Synthesize` (not `Lift-section`) and the source-paper key is the synthetic `<bundle>_initial_draft` form (matching `BUNDLE_LIFT_PROCEDURE.md` §3b sourceless path). Concretely:

  ```markdown
  | `<bundle>_initial_draft` | <Title> | Phase 6X W<wave> | **<Bundle> §<N>** | Synthesize |
  ```

- **Stage D variant:** the bundle treats this as **D.4** (sourceless append) rather than D.2 — see Stage D below.

The remainder of the protocol (Stages C, E, F, G) applies unchanged.

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

For each affected bundle, classify into one of four branches:

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

#### D.4 — Sourceless / Lean-only late absorption

`paper_draft.tex` exists AND new content is purely additive (D.2 form) but the contributing Phase 6X output has **no per-paper draft** — only Lean modules + working-docs synthesis. The bundle absorbs the Lean substrate directly.

**Action:** structurally identical to D.2, but use the synthetic source-paper key:

```bash
uv run python scripts/bundle_append.py \
    --bundle <X> \
    --source-paper "<bundle>_phase6X_W<wave>_lean_only" \
    --insertion-point '<§N>' \
    --notes "Late absorption (sourceless): Phase 6X W<wave> <topic> — Lean-only substrate" \
    --lean-modules "<Module1>,<Module2>,..."
```

Citations in §<N> reference Lean modules / theorem names directly (no `\cite{paperN_topic}` since no source per-paper draft exists). Stage F re-review is mandatory; the synthetic key is recorded in `append_log.json` for audit-trail purposes.

**Owner:** Phase 7 sub-phase owner. Stage A.alt gate (Lean-only build clean) must have passed before invoking D.4.

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
| 9 | `skeft-qa:figure-reviewer` (`bundle_target=<X>`) | `papers/<X>/figures/figure_review_report.json` | ALL PASS |
| 10 | `skeft-qa:claims-reviewer` (`bundle_target=<X>`) | `papers/<X>/claims_review.json` | zero FAIL |
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

## Branch decision (D.1 vs D.2 vs D.3 vs D.4) — quick reference

| Condition | Branch | Owner | Stage A gate |
|---|---|---|---|
| `papers/<bundle>/paper_draft.tex` does not exist | **D.1** | passive (no action) | n/a (deferred) |
| `paper_draft.tex` exists AND new content is additive AND Phase 6X has per-paper draft | **D.2** | Phase 7 sub-phase owner | A (per-paper Stage-13 GREEN) |
| `paper_draft.tex` exists AND new content overturns/refines prior content | **D.3** | Phase 7 owner + lead author | A (per-paper Stage-13 GREEN) |
| `paper_draft.tex` exists AND new content is additive AND Phase 6X is Lean-only | **D.4** | Phase 7 sub-phase owner | A.alt (Lean build clean) |

---

## Worked example (real: Phase 6o Wave 4a Track 4 — FLS BEC depletion-factor return)

**Scenario:** Phase 6o Wave 4a Track 4 ships 2026-05-07/08 — a verdict-(B) honest-correction follow-up to Phase 7 absorption Session 5 (user-call C2). Wave produces a strict-extension Lean structure (`SakharovExtended` wrapping unchanged `SakharovConditions` + `lambdaJ : ℝ` + `lambdaHK : ℝ` + load-bearing `depletion : ℝ` field + Prop-typed substrate-physics witness) plus 5 substantive theorems (JTGR16-JTGR20 in `JacobsonThermoGRDarkEnergy.lean` §8). The substantive shift: the prior `sakharov_..._iff_lambda_j_eq_lambda_hk` biconditional reading is honestly retired in favour of one-way (⇒) implication per Volovik-Jannes 2012 §VII forward-only argument and FLS BEC primary-source verification (arXiv:1103.4841 + arXiv:1204.3039 Eq. 71). No standalone per-paper draft (Phase 6o research-only scope) — sourceless / Lean-only output triggers branch D.4. It maps to D5 §11 + §11.5 (additive prose addendum updating an existing structural-caveat embedded subsection) and F §10 (one-sentence pointer in dark-sector summary).

**Stage A.alt** (Lean-only): `lake build SKEFTHawking.JacobsonThermoGRDarkEnergy` clean (1.5s); full library `lake build` clean (8586 jobs); zero sorry / zero new axioms; substantive content documented at `temporary/working-docs/phase6o/wave_4a_session1_close.md`; `ARCHITECTURE_SCOPE.md` Phase 6n / 6o coda updated (this file's Phase 6m closure block is supplemented, not modified).

**Stage B (sourceless variant):** add row to `PAPER_DRAFT_MAPPING.md`:
```markdown
| `_phase6o_W4a_lean_only` | FLS BEC depletion-factor / Sakharov 4-criterion verdict-(B) closure | Phase 6o Wave 4a Track 4 | **D5 §11** + **D5 §11.5** + **F §10** | Revision (honest verdict-(B) downgrade) |
```

User authorization: granted at Phase 7 absorption Session 5 user-call C2 (substrate-derived `lambdaJEqLambdaHK` refactor; risk-disclosed (⇐) may not hold). Lift action is **Revision** (not pure Synthesize) because the prior biconditional reading is being downgraded — a refinement of an already-shipped verdict, even though absent any per-paper draft on the source side.

**Stage C:** `bundle_source_manifest.py` re-run; D5 + F flagged `freshness_stale`.

**Stage D:** D5 → branch **D.4** (sourceless / Lean-only late absorption with substantive prose addendum + load-bearing structure-shape change at the substrate layer; existing `SakharovConditions` + JTGR6-9 untouched). F → branch D.2 (drafted; cross-ref upgrade only via D5 propagation).

**For D.4 (D5):**
```bash
uv run python scripts/bundle_append.py \
    --bundle D5 \
    --source-paper "_phase6o_W4a_lean_only" \
    --insertion-point '§11' \
    --notes "Late absorption (sourceless): Phase 6o Wave 4a Track 4 verdict-(B) honest closure — Lean-only substrate; SakharovExtended strict-extension + JTGR16-20 + retired biconditional → one-way implication" \
    --lean-modules "JacobsonThermoGRDarkEnergy"
```

The strict-extension-layer pattern is load-bearing here: keeping the legacy `SakharovConditions` 4-Boolean structure unchanged preserves all downstream callers (`BiconditionalReformulation`, `SakharovHorizonCrooks`, etc.) without invasive refactor. Pre-existing `_iff_` aliases in `BiconditionalReformulation.lean` were renamed to `_implies_` at Phase 7 absorption Session 4 (anticipating this verdict); aging citations in already-closed bundles preserve via `@[deprecated]` aliases per the post-freeze refinement absorbed in `BUNDLE_LIFT_PROCEDURE.md` Session-5 footnote.

**Stage E:** F auto-flagged `freshness_stale` after next CHECK 22 run (F lifts from D5 §10 dark-sector summary).

**Stage F:** Re-invoke reviewer triple on D5 (figure / claims / adversarial). The bundle's existing 13/14 ALL-GREEN heatmap status preserved post-absorption; D5 §11 prose addendum + §11.5 update verified via pdflatex (12pp clean); 3 new bibitems (Finazzi-Liberati-Sindoni 2012 PRL/Proc + Belenchia-Liberati-Mohd 2014) added to `CITATION_REGISTRY` with primary-source PDFs cached. Cross-bundle propagation: F flagged + cross-ref upgrade only (one-sentence pointer); L3 cross-ref preserved via D3 §17.5 ↔ L3 substrate-class-context paragraph.

**Stage G:** `validate.py --check bundle_consistency --check bundle_source_freshness` re-run; `papers/cluster_bundle_index.json` re-frozen.

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
- `docs/PAPER_STRATEGY.md` — 17-bundle architecture; defines bundles eligible for late absorption
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

*Created Phase 7a sub-wave 7a.1.6 (2026-05-01). **FROZEN at sub-wave 7a.4 (2026-05-01)** via conceptual rehearsal of "what if a hypothetical Phase 6n landed during sub-wave 7a.2/7a.3." Two refinements absorbed: (1) Stage A.alt for Lean-only Phase 6X output (no per-paper draft) — promoted from hypothetical to real after I2's sourceless-bundle pattern; (2) D.4 branch in Stage D for sourceless late absorption. Stages F (re-review per `BUNDLE_LIFT_PROCEDURE.md` §8/§9/§10/§11/§13) and G (cross-bundle consistency) inherit the same hardened ordering and BLOCKER-resolution discipline frozen in `BUNDLE_LIFT_PROCEDURE.md` 7a.4. Updated with worked-example examples on first real absorption event. Cross-referenced from `BUNDLE_LIFT_PROCEDURE.md`, `Phase7_Roadmap.md`, `Phase7a_Roadmap.md`, `WAVE_EXECUTION_PIPELINE.md`.*

---

**Post-freeze validation footnote (2026-05-07).** Phase 7 absorption Sessions 1–5 (2026-05-06 → 2026-05-08) executed this protocol across 16+ Phase 6n + 6o handles via D.2 / D.3 / D.4 branches without protocol revision. Three D.3 user-auth gates closed with substantive bundle revision: GATE 1 — I1 §3 reframing of FirstOrderKMS as first-order Glorioso-Liu projection (Phase 6n W2a); GATE 2 — D3 §17.5 + L3 substrate-class context paragraph for Sakharov ↔ horizon-Crooks unification with Verlinde-vs-Jacobson distinction enforced (Phase 6n W2d); GATE 3 — D2 §2 + L2 paired splash for Schellekens-chain reframing of 24|c₋ as Möller-Scheithauer 2024 c=24 holomorphic-VOA classification corollary (Phase 6o W2b). The honest verdict-(B) closure of Phase 6o Wave 4a Track 4 (the worked example above) demonstrates the Stage D.4 + Stage F path applied to a *retraction*-shaped late absorption — where new substrate evidence honestly downgrades a prior biconditional claim to a one-way implication — without overrunning the bundle's existing reviewer triple or requiring a fresh bundle target.
