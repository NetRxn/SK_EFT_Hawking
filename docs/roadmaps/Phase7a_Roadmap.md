# Phase 7a: Pre-Flight Cleanup + Workflow Hardening + Robustness Infrastructure + Infrastructure Bundles (I1, I2)

**Created:** 2026-04-30. **Parent:** `Phase7_Roadmap.md` (umbrella; 16-wave drafting roadmap). **Scope:** First sub-phase of Phase 7, executing Phase 7 umbrella Waves 0 + 1 + 2 plus a *new* robustness-infrastructure sub-wave inserted between them.

## Strategic Summary

**Three goals.** (1) Source-level blocker cleanup across all 32+ per-paper drafts (Phase 7 umbrella Wave 0). (2) Robustness infrastructure for absorbing late-arriving Phase 6 outputs into already-drafted bundles. (3) Workflow hardening via the lightest-weight bundles I1 + I2 (Phase 7 umbrella Waves 1–2), producing a battle-tested `BUNDLE_LIFT_PROCEDURE.md` that subsequent Phase 7b/7c/... sub-phases consume.

**Why robustness infrastructure is load-bearing here, not deferred.** User direction 2026-04-30: *"i anticipate more phase 6 items being added, make sure the process you put in place for 7a's & the corresponding roadmap is robust to new items that may pop in past 6m."* The bundle architecture (`PAPER_STRATEGY.md` + `PAPER_DRAFT_MAPPING.md`) was designed assuming the source-paper roster is roughly stable; post-Phase-6m, additional Phase 6 waves are anticipated. Phase 7a builds the **append-only protocol** that lets bundles absorb new Phase 6 outputs without rework, and tests it on I1 + I2 before higher-stakes bundles (D3, D5, F) are drafted.

**What "robust" means concretely.**
- A new Phase 6n wave shipping after Phase 7 starts produces Lean modules + per-paper drafts via existing pipeline.
- The new content reaches its assigned bundle automatically via `PAPER_DRAFT_MAPPING.md` update.
- The bundle absorbs the content via documented append protocol — no full re-draft.
- Validation flags affected bundles RED until Stage-13 re-invocation closes.
- Cross-bundle sibling consistency checked via `validate.py --check bundle_consistency` (existing CHECK 21 from Phase 6i Wave 7.3).

**Phase 7a does NOT block on hypothetical Phase 6n.** The robustness machinery is built proactively; Phase 6n is a future user trigger, not a Phase 7a prerequisite. If Phase 7a closes before any Phase 6n materializes, the infrastructure sits unused but ready.

---

## Entry State (2026-04-30)

- Phase 6m R6 Lean closure SHIPPED (50 substantive thms across 4 modules; Phase 6m material → D5 §8–§12 + §10.5/§11.5 per `PAPER_DRAFT_MAPPING.md` 2026-04-30 update)
- Phase 7 umbrella roadmap drafted (`Phase7_Roadmap.md`)
- 32 per-paper drafts in `papers/paperN_*/` (entry state)
- 13 bundle directories DO NOT YET EXIST
- Bundle infrastructure SHIPPED (Phase 6i Wave 7): sentence-state schema, reviewer prompts, validate.py CHECK 21, BUNDLE_READINESS_HEATMAP, dashboard tab, Pipeline Invariant #14
- Bundle readiness from 2026-04-29 sweep: 4 🟢 (L1, I1, I2, E2) + 4 🟡 (D1, D2, E1, L2) + 5 🔴 (F, D3, D5, L3, D4)
- ~204 open findings; ~86 blockers; ~121 CitationIntegrity dominate

---

## Phase 7a Sub-Wave Plan

### 7a.0 — Pre-flight: source-level blocker cleanup [Pipeline: Stages 7, 12, 13]

**Goal.** Bring all per-paper Stage-13 panels to 🟢/🟡 before any bundle lift. Cleaning sources upstream eliminates downstream rework when the same finding would otherwise surface across 2–3 bundles.

**Sub-sub-waves (7a.0.1–7a.0.5; matches Phase 7 umbrella Wave 0 sub-waves):**

- **7a.0.1** — CitationIntegrity bulk sweep (~121 findings via `back_fill_primary_sources.py --fetch` + per-paper DOI confirmations)
- **7a.0.2** — CountFreshness regen (~14 findings via `update_counts.py` + `render_paper_tables.py`)
- **7a.0.3** — ParameterProvenance human verification (~14 findings via provenance dashboard `localhost:8050`)
- **7a.0.4** — Misc finding triage (~55 unclassified)
- **7a.0.5** — Per-paper Stage-13 re-invocation (`adversarial-reviewer` per affected paper, fresh context); supersession ledger updates (`docs/review_finding_supersessions.json`); heatmap regen (`scripts/bundle_readiness.py --heatmap`); dashboard refresh (`scripts/datastar_bundles.py`); spot-check `localhost:8050` "Bundles" tab

**Decision Gate 7a.0:** every paper at 🟢/🟡 per-paper readiness. Bundle-level RED may persist (those are bundle-architectural, not source-quality). No bundle finding traces back to an unresolved source-paper finding.

**Effort:** ~3–4 person-weeks (per Phase 7 umbrella Wave 0 estimate).

---

### 7a.1 — Robustness infrastructure for late Phase 6 absorption [PRIORITY; new sub-wave inserted in Phase 7a] **[SHIPPED 2026-05-01]**

**Goal.** Build the **append-only bundle architecture** + tooling + validation + protocol *before* drafting any bundle, so that I1 + I2 (sub-waves 7a.2–7a.3) immediately use it. Validates the design on the lowest-stakes bundles before D3/D5/F apply it.

**Why pre-bundle, not deferred.** If we draft I1/I2 with a non-append-aware structure and *then* discover the structure can't absorb a hypothetical Phase 6n output, we redo I1/I2. Building the append architecture first exposes design decisions before they get bound to LaTeX.

**Sub-sub-waves:**

#### 7a.1.1 — Append-only bundle directory layout

Each bundle directory (created in Phase 7a sub-wave 7a.2 onward) will contain:

```
papers/<bundle>/
  paper_draft.tex            # main LaTeX
  figures/                    # figures (lifted from source papers + new bundle-specific)
  tables/                     # auto-rendered from tables.py
  sentence_state.json         # sentence-level provenance with bundle_destination
  audit_log.jsonl             # claims-reviewer + figure-reviewer audit trail
  READINESS_GATES.md          # per-bundle gate panel
  source_manifest.md          # NEW: contributing sources list, auto-generated
  change_log.md               # NEW: human-readable append history
  append_log.json             # NEW: machine-readable append history
  bundle_metadata.json        # NEW: bundle target, tier, sequencing, dependencies
```

Two new files (`source_manifest.md`, `change_log.md`) are human-facing; one (`append_log.json`) is machine-facing for tooling; one (`bundle_metadata.json`) is metadata for the dashboard.

**`bundle_metadata.json` schema (load-bearing for dashboard integration via `scripts/datastar_bundles.py`):**

```json
{
  "bundle_target": "I1",
  "tier": 3,
  "title": "Verification Methodology with Worked Cases",
  "target_journal": "CPC | Phys. Rep.",
  "phase7_subphase": "7a",
  "stage9_status": "pending | green | red",
  "stage10_status": "pending | green | red",
  "stage13_status": "pending | green | yellow | red",
  "stage13_redo_required": false,
  "freshness_stale": false,
  "source_manifest_last_regen": "<ISO timestamp>",
  "last_lift": "<ISO timestamp>",
  "last_stage9_review": "<ISO timestamp>",
  "last_stage10_review": "<ISO timestamp>",
  "last_stage13_review": "<ISO timestamp>",
  "blockers_open": 0,
  "advisories_open": 0,
  "stage13_review_doc": "papers/AutomatedReviews/<DATE>-bundle-stage13/<bundle>.md",
  "audit_log_path": "papers/<bundle>/audit_log.jsonl",
  "supersession_ledger_anchor": "docs/review_finding_supersessions.json"
}
```

The schema is consumed by `scripts/datastar_bundles.py` (Phase 6i Wave 7.5) which feeds the provenance dashboard "Bundles" tab; per-field uses documented in `scripts/datastar_bundles.py` docstrings (or inline if it's a thin script). Phase 7a sub-wave 7a.1.2 ensures `scripts/bundle_source_manifest.py` initializes `bundle_metadata.json` on bundle creation; subsequent reviewer agents (Stage 9/10/13) update the relevant `*_status`/`last_*_review` fields on each invocation.

**Append protocol.** When a new source contributes to a bundle:
- New `paper_draft.tex` `\section` (or `\subsection`) appended at the bundle's designated insertion point (per `PAPER_DRAFT_MAPPING.md` row).
- `source_manifest.md` updated with new source row.
- `change_log.md` gains a dated entry: "2026-MM-DD — Phase 6X Wave Y absorbed (paperN_topic + Lean modules); inserted §X.Y".
- `append_log.json` gains structured entry: `{date, source_paper, bundle_section_inserted, lean_modules_referenced, citation_count_added, stage13_redo_required: true}`.
- `sentence_state.json` migrated: new sentences inherit bundle_destination from their source paper's bundle assignment.
- Citation registry merge: any new bibkeys propagate from source paper's bibliography to bundle bibliography.

#### 7a.1.2 — `scripts/bundle_source_manifest.py`

Auto-generates `papers/<bundle>/source_manifest.md` by reading `PAPER_DRAFT_MAPPING.md`. Filters by bundle target. Emits:
- Source paper directory name
- Lift action (Lift-section / Lift-letter / Lift-companion / Retain-in-place)
- Phase / Wave provenance
- Date of last source-paper modification
- Bundle insertion point (e.g., D5 §8)

Re-run on demand or on `PAPER_DRAFT_MAPPING.md` modification (file-watcher hook deferred to Phase 7b).

#### 7a.1.3 — `scripts/bundle_append.py`

Semi-automated tool for absorbing a new source into an already-drafted bundle. Inputs:
- `--bundle <bundle_target>` (e.g., `D5`)
- `--source-paper <paperN_topic>` (the new source)
- `--insertion-point <section_id>` (e.g., `§13`)
- `--bundle-section-hint <hint>` (optional)

Effects:
- Validates source exists and is mapped to `<bundle_target>` in `PAPER_DRAFT_MAPPING.md`
- Appends `\section{<source title>}` (or `\subsection`) skeleton to `papers/<bundle>/paper_draft.tex` at insertion point
- Updates `papers/<bundle>/source_manifest.md`, `change_log.md`, `append_log.json` with the absorption record
- Migrates source paper's `sentence_state.json` entries with `bundle_destination` field set
- Merges source paper's bibliography into bundle bibliography (handles bibkey collisions per Phase 6m citation-merge precedent)
- Sets `stage13_redo_required: true` on the bundle's metadata
- Emits actionable next-steps (Stage-13 re-invocation, figure regen, etc.)

#### 7a.1.4 — `validate.py` CHECK 22 — `bundle_source_freshness`

Detects when a source paper has been modified since the bundle's last lift. Triggers RED bundle status until Stage-13 re-invocation closes.

Logic:
- For each bundle, read `append_log.json` to find last-lift timestamp per source
- Compare against source paper's `audit_log.jsonl` last-modification timestamp
- If source modified after last lift: bundle is `freshness-stale`; emit advisory finding
- If source has unincorporated `paper_draft.tex` content (per sentence-state diff): emit WARN
- If `stage13_redo_required: true` in `append_log.json`: emit WARN until next Stage-13 review clears

Default: advisory; promotable to FAIL at Phase 8 submission gate.

#### 7a.1.5 — `docs/BUNDLE_LIFT_PROCEDURE.md`

Canonical document describing the bundle-lift workflow. **Treats Stages 9, 10, 13 as three distinct reviewer-agent invocations** (per `WAVE_EXECUTION_PIPELINE.md` Stage 9, Stage 10, and Stage 13 separation); previous draft of this roadmap conflated them.

**Sections:**

1. **Pre-lift checks**
   - Source paper at 🟢/🟡 per-paper readiness (verify in `BUNDLE_READINESS_HEATMAP.md` + `papers/<source>/READINESS_GATES.md`)
   - `PAPER_DRAFT_MAPPING.md` row exists for source → bundle mapping
   - Bundle directory does not exist (initial lift) OR is `freshness-stale` (append)
   - Pipeline Invariant #14: bundle target identified at Stage 1 of source-paper wave

2. **Bundle directory creation** (file structure per sub-wave 7a.1.1; `bundle_metadata.json` schema per 7a.1.1)

3. **Initial lift** — `scripts/bundle_append.py --bundle <X> --source-paper <P> --insertion-point <§>` in initial-lift mode (creates bundle directory + paper_draft.tex skeleton)

4. **Sentence-state migration** — `scripts/sentence_state.py` propagates `bundle_destination` field; `scripts/bundle_clusters.py` updates `papers/cluster_bundle_index.json` with new cross-bundle clusters

5. **Citation merge** — source-paper bibliography → `papers/<X>/bibliography.bib`; bibkey-collision handling per Phase 6m citation-merge precedent

6. **Figure migration** — copy source figures to `papers/<X>/figures/`; preserve `# viz-ref:` tags from source for `validate.py --check viz_consistency`

7. **Bundle `paper_draft.tex` skeleton** — header, abstract, sections per source manifest, `\input{tables/<spec>.tex}` blocks for auto-rendered tables (per `WAVE_EXECUTION_PIPELINE.md` Stage 12 paper-tabular-numerical-content section)

8. **Stage 9 — figure review (LLM visual review)**
   - **Agent:** `physics-qa:figure-reviewer` (plugin agent at `.claude/plugins/physics-qa/agents/figure-reviewer.md`)
   - **Invocation:** parameter `bundle_target=<X>` (per `docs/agents/claims-reviewer-bundle-prompts.md` row for `<X>`)
   - **Output:** `papers/<X>/figures/figure_review_report.json` + per-figure findings appended to `papers/<X>/audit_log.jsonl`
   - **Update:** `bundle_metadata.json.stage9_status` ← review verdict; `last_stage9_review` ← ISO timestamp
   - **Pass criterion:** ALL PASS, no FAIL, no MINOR (per Stage 9 gate in `WAVE_EXECUTION_PIPELINE.md`)

9. **Stage 10 — paper claims review (LLM content review)**
   - **Agent:** `physics-qa:claims-reviewer` (plugin agent at `.claude/plugins/physics-qa/agents/claims-reviewer.md`)
   - **Invocation:** parameter `bundle_target=<X>`
   - **Output:** `papers/<X>/claims_review.json` + findings appended to `papers/<X>/audit_log.jsonl`
   - **Anchor list:** `docs/agents/claims-reviewer-bundle-prompts.md` row for `<X>` (per-bundle anchor of load-bearing claims + citations the bundle's review must verify)
   - **Update:** `bundle_metadata.json.stage10_status` ← review verdict; `last_stage10_review` ← ISO timestamp
   - **Pass criterion:** zero FAIL findings (numerical-claim agreement within 0.5%; "formally verified" claims match Lean state; citation DOIs resolve; etc.)

10. **Stage 13 — adversarial review (fresh-context Opus sweep)**
    - **Agent:** `adversarial-reviewer` (plugin agent at `.claude/plugins/physics-qa/agents/adversarial-reviewer.md`)
    - **Orchestrator:** `scripts/review_runner.py --bundle <X> --prep-brief` (Phase 6i Wave 7.4 deliverable; bundle-aware Stage-13 entry point)
    - **Output:** `papers/AutomatedReviews/<DATE>-bundle-stage13/<X>.md` (structured markdown report)
    - **Auto-pickup:** `scripts/build_graph.extract_review_finding_nodes` → `ReviewFinding` nodes with `FLAGS` edges to bundle; `BLOCKER` findings flip the affected `ReadinessGate` to `blocked`
    - **Per-bundle profile (per Phase 6i Wave 7.2):** Tier 0 (F) review-paper style; Tier 1 (D1–D5) intra-bundle consistency + cross-bundle cross-bridge checks; Tier 2 (L1–L3) stand-alone PRL depth; Tier 3 (I1, I2) software/methodology review; Tier 4 (E1, E2) lightweight letter + device-parameter audit
    - **Update:** `bundle_metadata.json.stage13_status` ← review verdict; `last_stage13_review` ← ISO timestamp; `stage13_review_doc` ← path
    - **Pass criterion:** zero `BLOCKER` findings under `papers/AutomatedReviews/` with `status != fixed`

11. **BLOCKER resolution loop** (applies to any of Stage 9/10/13)
    - Reviewer agent emits BLOCKER → entry in `papers/<X>/audit_log.jsonl` + (Stage 13) `ReviewFinding` graph node
    - Author / contributor fixes via direct edit to `paper_draft.tex` / `figures/` / source paper / Lean module as appropriate
    - Supersession ledger entry: append to `docs/review_finding_supersessions.json` with `meta.status: open → fixed | accepted` per closed finding
    - Re-invoke the *same* reviewer agent in fresh context (`bundle_target=<X>`); confirm BLOCKER cleared
    - If clean: `bundle_metadata.json.<stage>_status` advances; if not: iterate
    - Per `WAVE_EXECUTION_PIPELINE.md` Stage 13: "The author fixes; the author re-invokes. Separation of the fix-and-review roles is the whole reason the agent exists."

12. **Iteration to GREEN** — repeat Stage 9 → Stage 10 → Stage 13 → BLOCKER loop until `bundle_metadata.json` shows `stage9_status = stage10_status = stage13_status = green` AND `blockers_open = 0`

13. **Dashboard refresh + heatmap regen (mandatory exit step)**
    - `uv run python scripts/datastar_bundles.py` (regenerate provenance dashboard "Bundles" tab data; Phase 6i Wave 7.5 script)
    - `uv run python scripts/bundle_readiness.py --heatmap` (regenerate `docs/BUNDLE_READINESS_HEATMAP.md`)
    - Spot-check `localhost:8050` /bundles tab via `uv run python scripts/provenance_dashboard.py`
    - `validate.py --check bundle_consistency` PASS (CHECK 21; cross-bundle cluster integrity)
    - `validate.py --check bundle_source_freshness` PASS (CHECK 22; new in 7a.1.4)

14. **Bundle close** — `papers/<X>/READINESS_GATES.md` panel populated; `change_log.md` final entry; `audit_log.jsonl` final state archived; `bundle_metadata.json` snapshot

Procedure document is initially drafted after I1 (sub-wave 7a.2); refined after I2 (sub-wave 7a.3); frozen at sub-wave 7a.4. Subsequent Phase 7b/7c/... waves consume the frozen procedure.

**Cross-references (internal to BUNDLE_LIFT_PROCEDURE.md):**
- §8/§9/§10 ↔ `WAVE_EXECUTION_PIPELINE.md` Stage 9/10/13 sections
- Anchor list ↔ `docs/agents/claims-reviewer-bundle-prompts.md`
- Per-bundle anchors ↔ `PAPER_STRATEGY.md` §2.X for the target bundle
- Source manifest ↔ `PAPER_DRAFT_MAPPING.md` row for the bundle
- Sentence-state schema ↔ `scripts/sentence_state.py`
- Cross-bundle cluster registry ↔ `papers/cluster_bundle_index.json`
- Supersession ledger ↔ `docs/review_finding_supersessions.json`

#### 7a.1.6 — `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md` [robustness deliverable]

Step-by-step protocol for absorbing a new Phase 6X wave's output into already-drafted bundles. The load-bearing robustness document.

**Protocol stages:**

**Stage A — Phase 6X wave completes.**
- Phase 6X follows its own roadmap; produces Lean modules, per-paper drafts, working-docs syntheses
- Phase 6X-internal Stage-13 closure (per-paper Stage 13 against its own anchor list) must be GREEN before Stage B

**Stage B — Bundle assignment.**
- Phase 6X owner adds row(s) to `PAPER_DRAFT_MAPPING.md` per Pipeline Invariant #14
- Each new source paper has explicit `bundle_destination(s)` and `lift_action`
- If new content does not fit existing 13 bundles → user-authorization gate for 14th+ bundle target (per Invariant #14)

**Stage C — Source manifest detection.**
- `scripts/bundle_source_manifest.py` re-run for affected bundles
- New source rows appear in each affected bundle's `source_manifest.md`
- `validate.py --check bundle_source_freshness` flags affected bundles as `freshness-stale`

**Stage D — Branching by bundle state.**

- **D.1 — Bundle not yet drafted (no `papers/<bundle>/paper_draft.tex`):** the new source will be picked up automatically when the bundle's Phase 7X drafting wave runs. No action beyond Stage B/C.
- **D.2 — Bundle drafted, append-only revision:** Phase 6X output is purely additive (new mechanism family, new substrate, new section). Run `scripts/bundle_append.py --bundle <X> --source-paper <new> --insertion-point <new_§N+>`. Stage-13 re-invocation per affected bundle.
- **D.3 — Bundle drafted, revision required:** Phase 6X output overturns or refines a prior Phase 6 verdict already documented in the bundle. Author-driven section revision (manual edit, with `change_log.md` entry); not automatable. Stage-13 re-invocation mandatory.

**Stage E — Cross-bundle propagation.**
- F (flagship) bundle sources from every Tier 1 bundle. Whenever any Tier 1 bundle absorbs new content, F's `freshness-stale` flag triggers automatically.
- Phase 6X owner notes downstream-affected bundles in the PAPER_DRAFT_MAPPING.md row.

**Stage F — Re-review (per `BUNDLE_LIFT_PROCEDURE.md` §8/§9/§10/§11).**
- Each `freshness-stale` bundle re-invokes the full reviewer triple with `bundle_target=<X>`:
  1. `physics-qa:figure-reviewer` (Stage 9; if new figures absorbed)
  2. `physics-qa:claims-reviewer` (Stage 10; with bundle-prompts anchor for `<X>`)
  3. `adversarial-reviewer` via `scripts/review_runner.py --bundle <X> --prep-brief` (Stage 13; output to `papers/AutomatedReviews/<DATE>-bundle-stage13/<X>.md`)
- BLOCKERs surfaced from new content resolved per BLOCKER resolution loop in `BUNDLE_LIFT_PROCEDURE.md` §11
- `bundle_metadata.json` `stage{9,10,13}_status` updated; `freshness_stale` flag clears once `blockers_open = 0` and all three statuses GREEN
- Heatmap regenerated via `scripts/bundle_readiness.py --heatmap`; dashboard refreshed via `scripts/datastar_bundles.py`

**Stage G — Cross-bundle consistency final pass.**
- `validate.py --check bundle_consistency` re-run
- Any cross-bundle cluster drift surfaced by sentence-level provenance reformation resolved
- `cluster_bundle_index.json` re-frozen

**Document is updated with examples after the first absorption event** (which may not occur in Phase 7a if no Phase 6n materializes).

**Effort for 7a.1 sub-sub-waves:** ~1.5–2 person-weeks total
- 7a.1.1: 0.5 person-week (design + first directory layout)
- 7a.1.2: 0.5 person-week (manifest script)
- 7a.1.3: 0.5 person-week (append script)
- 7a.1.4: 0.25 person-week (validate.py check)
- 7a.1.5: 0.25 person-week (procedure doc; iterates with 7a.2/7a.3)
- 7a.1.6: 0.25 person-week (protocol doc; iterates with 7a.2/7a.3)

**Decision Gate 7a.1:** infrastructure is *ready*; design is validated by sub-waves 7a.2 + 7a.3 actually using it.

**Status 2026-05-01:** GATE PASSED. All six sub-sub-waves shipped:
- 7a.1.1 → `docs/BUNDLE_DIRECTORY_SCHEMA.md` (canonical schema for `bundle_metadata.json` + `append_log.json` + on-disk layout)
- 7a.1.2 → `scripts/bundle_source_manifest.py` (smoke-tested; all 13 bundle directories initialized)
- 7a.1.3 → `scripts/bundle_append.py` (smoke-tested with paper15+paper44 → I1 §1+§12)
- 7a.1.4 → `scripts/check_bundle_source_freshness.py` + validate.py CHECK 22 registered (smoke-tested; passing with 1 expected WARN on I1)
- 7a.1.5 → `docs/BUNDLE_LIFT_PROCEDURE.md` (14-step canonical procedure; Stages 9/10/13 separated)
- 7a.1.6 → `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md` (Stages A-G with branches D.1/D.2/D.3 + worked synthetic example)

---

### 7a.2 — Bundle I1 consolidation (Phase 7 umbrella Wave 1) [Pipeline: Stages 1, 7, 9, 10, 12, 13]

**Goal.** Lift `paper15` (verification methodology) + Phase 6f W7 catch-up `paper44` (Riemannian connection — I1 sidebar primary) + Phase 6f W1-W6 substrate rosters (algebraic-GR backbone first-formalization claims) + Phase 6g W5 structural-Prop scoping pattern (Mathlib-dependency-fallback case study) into `papers/I1/paper_draft.tex` per `PAPER_DRAFT_MAPPING.md` I1 row.

**Why I1 first.** I1 has 0 open findings and 0 blockers entering Phase 7a (after sub-wave 7a.0 cleanup; was also 🟢 entering Wave 0). It's the lightest bundle to consolidate, establishes the lift workflow under low-stakes content trade-offs. Crucially, I1 *uses* the sub-wave 7a.1 robustness infrastructure on its first invocation — validates the design before D3/D5/F apply it.

**Procedure (per `BUNDLE_LIFT_PROCEDURE.md` from sub-wave 7a.1.5; steps numbered to match canonical procedure):**

1. **Pre-lift checks** (procedure §1) — paper15 + paper44 + Phase 6f W1-W6 + Phase 6g W5 source rosters confirmed at 🟢/🟡 per `BUNDLE_READINESS_HEATMAP.md`; `PAPER_DRAFT_MAPPING.md` I1 row exists.

2. **Bundle directory creation** (procedure §2) — `papers/I1/` with file structure per sub-wave 7a.1.1; `bundle_metadata.json` initialized with `bundle_target: I1`, `tier: 3`, `phase7_subphase: 7a`, `target_journal: "CPC | Phys. Rep."`.

3. **Stage 1 bundle scoping** — outline I1 section structure: §1 Introduction; §2 Three-layer architecture overview; §3 Worked case 1 (Aristotle FirstOrderKMS counterexample); §4 Worked case 2 (gap-solution-bounded conjecture disproof); §5 Worked case 3 (chirality-wall axiom decomposition); §6 14-stage wave execution pipeline; §7 Preemptive-strengthening discipline; §8 Sentence-level provenance + cross-paper consistency clusters; §9 Three-layer Python ↔ Lean ↔ Aristotle architecture; §10 Stage 13 adversarial-reviewer pattern; §11 Phase 6f W1-W6 first-formalization claims sidebar; §12 Phase 6f W7 Riemannian connection sidebar; §13 Phase 6g W5 structural-Prop scoping pattern; §14 Lessons + future work.

4. **Initial lift** (procedure §3) — `scripts/bundle_append.py --bundle I1 --source-paper paper15 --insertion-point §1` (initial-lift mode); then `--source-paper paper44 --insertion-point §12` (append mode); then Phase 6f-6g substrate rosters per sub-section assignments.

5. **Sentence-state migration** (procedure §4) — every paper15 + paper44 sentence acquires `bundle_destination: "I1"` field with `bundle_section_hint`. `scripts/bundle_clusters.py` updates `papers/cluster_bundle_index.json`.

6. **Citation merge** (procedure §5) — paper15 + paper44 bibliographies merge into `papers/I1/bibliography.bib`; bibkey-collision handling per Phase 6m citation-merge precedent.

7. **Figure migration** (procedure §6) — 3-layer architecture diagram, 14-stage pipeline diagram, sentence-state cluster diagram, etc. preserve `# viz-ref:` tags from source.

8. **`paper_draft.tex` skeleton** (procedure §7) — header, abstract, sections per scoping outline, `\input{tables/<spec>.tex}` blocks for any auto-rendered tables.

9. **Stage 9 figure review** (procedure §8) — `physics-qa:figure-reviewer` with `bundle_target=I1`. Output: `papers/I1/figures/figure_review_report.json`. Update: `bundle_metadata.json.stage9_status`. Pass criterion: ALL PASS.

10. **Stage 10 paper claims review** (procedure §9) — `physics-qa:claims-reviewer` with `bundle_target=I1`. Anchors per `docs/agents/claims-reviewer-bundle-prompts.md` I1 row (WAVE_EXECUTION_PIPELINE.md content, FirstOrderKMS counterexample, gap-solution-bounded counterexample, chirality-wall decomposition, Phase 6f W1-W6 first-formalization claims, Phase 6g W5 structural-Prop scoping pattern). Output: `papers/I1/claims_review.json`. Update: `bundle_metadata.json.stage10_status`. Pass: zero FAIL.

11. **Stage 13 adversarial review** (procedure §10) — `adversarial-reviewer` agent via `scripts/review_runner.py --bundle I1 --prep-brief`. Output: `papers/AutomatedReviews/<DATE>-bundle-stage13/I1.md`. Per-bundle profile: Tier 3 (software/methodology — each worked case must trace to a reproducible Aristotle run ID or commit-pinned counterexample). Update: `bundle_metadata.json.stage13_status` + `last_stage13_review` + `stage13_review_doc`. Pass: zero `BLOCKER` findings.

12. **BLOCKER resolution loop** (procedure §11) — for any BLOCKER surfaced in steps 9/10/11: author fix; supersession ledger entry; re-invoke same reviewer; iterate to clean.

13. **Iteration to GREEN** (procedure §12) — until `bundle_metadata.json.stage{9,10,13}_status = green` + `blockers_open = 0`.

14. **Dashboard refresh + heatmap regen** (procedure §13) — `scripts/datastar_bundles.py` → `scripts/bundle_readiness.py --heatmap` → spot-check `localhost:8050`; `validate.py --check bundle_consistency --check bundle_source_freshness` PASS.

15. **Bundle close** (procedure §14) — `papers/I1/READINESS_GATES.md` panel populated; `change_log.md` reflects close state; `audit_log.jsonl` archived snapshot; `bundle_metadata.json` final snapshot.

**Stage-13 anchors (per `docs/agents/claims-reviewer-bundle-prompts.md` I1 row):** WAVE_EXECUTION_PIPELINE.md content; FirstOrderKMS Aristotle counterexample; gap-solution-bounded counterexample; chirality-wall axiom decomposition; Phase 6f W1-W6 first-formalization claims; Phase 6g W5 structural-Prop scoping pattern.

**Effort:** ~2–3 person-weeks (matches Phase 7 umbrella Wave 1 estimate).

**Decision Gate 7a.2:** I1 at 🟢; lift procedure proven on a lightweight bundle.

---

### 7a.3 — Bundle I2 consolidation (Phase 7 umbrella Wave 2) [Pipeline: Stages 1, 7, 9, 10, 12, 13]

**Goal.** Lift Phase 5c VerifiedJackknife material + Phase 5o Wave 4 lean-tensor-categories library content + Phase 5o Wave 5 Mathlib upstream coordination memo into `papers/I2/paper_draft.tex`.

**Why I2 second.** Also 🟢 entry-state. Software-paper format is structurally distinct from physics-paper format (per Phase 7 umbrella Wave 2 rationale); doing it second prevents physics-paper conventions from contaminating I2. Also exercises the I1-derived lift procedure on a different deliverable shape, surfacing procedure refinements for sub-wave 7a.4.

**Coordination:** Per `PAPER_STRATEGY.md` §5, I2 depends on Phase 5o Wave 5 Mathlib upstream cycle. If Mathlib-acceptance is delayed beyond Phase 7a's drafting timeline, ship I2 as software-only (note in §5); the Mathlib upstream becomes a separate JOSS update later. Annotated in `bundle_metadata.json.target_journal` and `bundle_metadata.json.notes` as a deferred-dependency note.

**Procedure:** identical to sub-wave 7a.2 (I1) steps 1–15 per `BUNDLE_LIFT_PROCEDURE.md`, with bundle-target `I2` and Stage-13 anchors per `docs/agents/claims-reviewer-bundle-prompts.md` I2 row (Phase 5o Wave 5 lean-tensor-categories upstream coordination + VerifiedJackknife jackknife-variance-non-negative theorem). Per-bundle profile: Tier 3 (software/methodology). Output Stage-13 doc: `papers/AutomatedReviews/<DATE>-bundle-stage13/I2.md`.

**Effort:** ~1.5–2 person-weeks.

**Decision Gate 7a.3:** I2 at 🟢; lift procedure refined for software-paper deliverable shape.

---

### 7a.4 — `BUNDLE_LIFT_PROCEDURE.md` and `LATE_PHASE6_ABSORPTION_PROTOCOL.md` post-I1/I2 refinement [Pipeline: Stage 12]

**Goal.** Capture lessons from sub-waves 7a.2 + 7a.3, refine the procedure documents drafted in sub-wave 7a.1.5/7a.1.6, and freeze them as canonical references for subsequent Phase 7b/7c/... waves.

**Sub-sub-tasks:**

- 7a.4.1: Audit `BUNDLE_LIFT_PROCEDURE.md` against actual I1 + I2 lift execution — flag steps that were overlooked, ambiguous, or out-of-order. Update document.
- 7a.4.2: Audit `LATE_PHASE6_ABSORPTION_PROTOCOL.md` against the conceptual rehearsal of "what if a hypothetical Phase 6n landed during sub-wave 7a.2/7a.3." (No actual Phase 6n is required.) Document any gaps.
- 7a.4.3: Update CLAUDE.md Tier-2 references to add `BUNDLE_LIFT_PROCEDURE.md` + `LATE_PHASE6_ABSORPTION_PROTOCOL.md` (reference #9 + #10).
- 7a.4.4: Update `WAVE_EXECUTION_PIPELINE.md` Stage 10 section to note the bundle-lift procedure as the canonical Stage 10 activity for Phase 7+ waves.

**Effort:** ~0.5 person-week.

**Decision Gate 7a.4:** procedure documents frozen; CLAUDE.md + pipeline reference Phase 7a deliverables; subsequent Phase 7b can begin without procedure-document iteration.

---

### 7a.5 — Phase 7b trigger conditions [Decision gate]

**Goal.** Confirm Phase 7a's prerequisites for Phase 7b are met, scope Phase 7b, and either authorize start or defer.

**Phase 7b candidate scope:** D5 bundle consolidation (Phase 7 umbrella Wave 3) + initial Tier-2 PRL extraction L1, L3 (Waves 4–5; the two Tier-2 PRLs that don't depend on Tier-1 deep papers being drafted first because their sources are paper25 + paper27 standalone).

**Trigger conditions:**

1. Phase 7a Decision Gates 7a.0–7a.4 all PASS
2. I1 + I2 at 🟢
3. `BUNDLE_LIFT_PROCEDURE.md` + `LATE_PHASE6_ABSORPTION_PROTOCOL.md` frozen
4. `bundle_append.py` + `bundle_source_manifest.py` battle-tested on I1 + I2
5. `validate.py --check bundle_source_freshness` operational
6. No major lifecycle issues surfaced (e.g., Mathlib upstream-cycle delay impacting I2 in unrecoverable way; if so, I2 ships as software-only with deferred-dependency note and Phase 7a still closes)
7. User authorization for Phase 7b start

**Outputs at Phase 7a close:**
- 2 bundles drafted (I1, I2) at 🟢
- Robustness infrastructure operational (4 new artifacts: `bundle_append.py`, `bundle_source_manifest.py`, validate.py CHECK 22, `BUNDLE_LIFT_PROCEDURE.md`, `LATE_PHASE6_ABSORPTION_PROTOCOL.md`)
- 32 source papers at 🟢/🟡 per-paper readiness
- Heatmap regenerated reflecting Phase 7a closure

**Decision Gate 7a.5:** Phase 7a CLOSES; Phase 7b authorization received from user; `Phase7b_Roadmap.md` drafted (carries forward Phase 7 umbrella Wave 3+ scope).

---

## QA Pipeline Integration [load-bearing automation section]

Phase 7a sub-waves 7a.2 + 7a.3 (and all subsequent Phase 7b/7c/... sub-phases) drive every bundle through a three-agent QA pipeline anchored on `WAVE_EXECUTION_PIPELINE.md` Stages 9, 10, 13. The agents operate independently; each writes to its own output location; findings consolidate via the supersession ledger and bundle audit log.

**Three-agent reviewer pipeline (canonical):**

| Stage | Agent | Plugin path | Orchestrator | Output | Pass criterion |
|---|---|---|---|---|---|
| **9** | `physics-qa:figure-reviewer` | `.claude/plugins/physics-qa/agents/figure-reviewer.md` | direct (Skill tool with `bundle_target=<X>`) | `papers/<X>/figures/figure_review_report.json` + `papers/<X>/audit_log.jsonl` entries | ALL PASS, no FAIL, no MINOR |
| **10** | `physics-qa:claims-reviewer` | `.claude/plugins/physics-qa/agents/claims-reviewer.md` | direct (Skill tool with `bundle_target=<X>`) | `papers/<X>/claims_review.json` + `papers/<X>/audit_log.jsonl` entries | zero FAIL findings |
| **13** | `adversarial-reviewer` | `.claude/plugins/physics-qa/agents/adversarial-reviewer.md` | `scripts/review_runner.py --bundle <X> --prep-brief` | `papers/AutomatedReviews/<DATE>-bundle-stage13/<X>.md` | zero `BLOCKER` findings (status != fixed) |

**Per-bundle profiles for Stage 13** (per Phase 6i Wave 7.2; from `docs/agents/claims-reviewer-bundle-prompts.md`):
- **Tier 0 (F):** review-paper style — verify cited published L*/D* claims against the citation cache
- **Tier 1 (D1–D5):** intra-bundle consistency across lifted sections + cross-bundle cross-bridge checks (via `papers/cluster_bundle_index.json`)
- **Tier 2 (L1–L3):** stand-alone PRL depth; do not penalize absent broader scope; carry the bundle-specific anchor
- **Tier 3 (I1, I2):** software/methodology review — each worked case must trace to a reproducible Aristotle run ID or commit-pinned counterexample
- **Tier 4 (E1, E2):** lightweight letter review + device-parameter audit pass

**BLOCKER resolution loop** (applies to any of the three reviewer outputs):

```
reviewer agent emits BLOCKER
  ↓
audit_log.jsonl entry (Stage 9/10) OR ReviewFinding graph node (Stage 13)
  ↓
author/contributor fixes via paper_draft.tex / figures/ / source paper / Lean module edit
  ↓
docs/review_finding_supersessions.json append: meta.status: open → fixed | accepted
  ↓
re-invoke same reviewer agent in fresh context with bundle_target=<X>
  ↓
[clean] → bundle_metadata.json.<stage>_status: green
[not clean] → iterate
```

**Dashboard integration:**

- `bundle_metadata.json` schema (per sub-wave 7a.1.1 spec) is the **canonical machine-readable bundle state**. Every reviewer agent invocation updates the relevant `stage{9,10,13}_status` + `last_*_review` fields.
- `scripts/datastar_bundles.py` (Phase 6i Wave 7.5) reads `bundle_metadata.json` across all 13 bundle directories, aggregates into a dashboard-consumable JSON payload, and refreshes the provenance dashboard "Bundles" tab.
- `scripts/bundle_readiness.py --heatmap` reads the same source + the supersession ledger and regenerates `docs/BUNDLE_READINESS_HEATMAP.md`.
- **Mandatory exit step for every Phase 7 sub-wave:** run both scripts; spot-check `localhost:8050` /bundles; commit the regenerated docs.

**Cross-bundle consistency:**

- `papers/cluster_bundle_index.json` (Phase 6i Wave 7.1) is the cross-bundle cluster registry; sentence-level claims that span bundles (e.g., a Phase 6m result cited in both D5 §9 and F §8) are tracked here.
- `validate.py --check bundle_consistency` (CHECK 21; Phase 6i Wave 7.3) walks the registry and flags member-sentence drift.
- `validate.py --check bundle_source_freshness` (CHECK 22; new in 7a.1.4) flags bundles whose source papers have been modified since last lift.
- Both checks must PASS at every sub-wave exit.

**Late-Phase-6 absorption uses the same pipeline.** When a new Phase 6X wave triggers `LATE_PHASE6_ABSORPTION_PROTOCOL.md` Stage F, the reviewer triple is re-invoked with `bundle_target=<X>` exactly as in initial-lift. No separate "absorption review" pipeline; the canonical pipeline handles both initial-lift and late-absorption uniformly.

**Cross-references:**
- `WAVE_EXECUTION_PIPELINE.md` Stage 9 ↔ figure-reviewer
- `WAVE_EXECUTION_PIPELINE.md` Stage 10 ↔ claims-reviewer
- `WAVE_EXECUTION_PIPELINE.md` Stage 13 ↔ adversarial-reviewer + review_runner.py
- `docs/agents/claims-reviewer-bundle-prompts.md` ↔ per-bundle anchor lists for all 13 bundles
- `docs/BUNDLE_READINESS_HEATMAP.md` ↔ aggregated state output
- `docs/review_finding_supersessions.json` ↔ author-driven finding closures
- `papers/cluster_bundle_index.json` ↔ cross-bundle cluster registry
- `BUNDLE_LIFT_PROCEDURE.md` §8/§9/§10/§11 ↔ canonical agent invocation steps (Phase 7a sub-wave 7a.1.5 deliverable)

---

## Late-Phase-6 Hot-Swap Protocol [load-bearing robustness section]

The protocol designed in sub-wave 7a.1.6 and frozen in 7a.4. Reproduced here for in-roadmap visibility.

**Scenario.** A new Phase 6X wave (e.g., Phase 6n, 6o, ...) ships after Phase 7a or any subsequent Phase 7 sub-phase has started. The new wave produces Lean modules, per-paper drafts, and working-docs syntheses per its own roadmap. Phase 7's bundles must absorb the content with minimal re-work.

**Protocol stages (per `LATE_PHASE6_ABSORPTION_PROTOCOL.md`):**

| Stage | Action | Owner | Trigger |
|---|---|---|---|
| **A** | Phase 6X completes its own per-paper Stage-13 closure | Phase 6X | Phase 6X internal |
| **B** | Phase 6X owner adds row(s) to `PAPER_DRAFT_MAPPING.md` per Pipeline Invariant #14 | Phase 6X owner | Phase 6X close |
| **C** | `bundle_source_manifest.py` re-run; `validate.py --check bundle_source_freshness` flags affected bundles `freshness-stale` | automation | mapping update |
| **D.1** | If bundle not yet drafted: no action; pickup at scheduled wave | (passive) | bundle scheduling |
| **D.2** | If bundle drafted + append-only: `bundle_append.py` runs; Stage-13 re-invocation queued | Phase 7 owner | freshness flag |
| **D.3** | If bundle drafted + revision required: author-driven section revision; `change_log.md` entry; Stage-13 re-invocation queued | Phase 7 owner | freshness flag + revision detect |
| **E** | F (flagship) auto-flags `freshness-stale` if any Tier-1 bundle absorbs new content | automation | downstream propagation |
| **F** | Stage-13 re-invocation per affected bundle with `bundle_target=<X>`; BLOCKERs resolved | Phase 7 owner + reviewer agents | re-review queue |
| **G** | `validate.py --check bundle_consistency` re-run; cluster_bundle_index.json re-frozen | automation | post-review closure |

**Branch decision (D.1 vs D.2 vs D.3):**
- **D.1** if `papers/<bundle>/paper_draft.tex` does not exist
- **D.2** if `paper_draft.tex` exists AND new content is purely additive (new mechanism family, new substrate, new section per `bundle_section_hint`)
- **D.3** if `paper_draft.tex` exists AND new content overturns/refines a prior Phase 6 verdict already documented in the bundle (e.g., a Phase 6n result that flips a Phase 6m NO-GO to PARTIAL-VIABLE on a previously-closed mechanism)

**D.3 requires manual author judgment.** No automation can determine whether new content "revises" prior content; the Phase 6X owner flags this in the PAPER_DRAFT_MAPPING.md row.

**User authorization gates inside the protocol:**
- Stage B may require user authorization if the new Phase 6X output does not fit any of the existing 13 bundle targets — Pipeline Invariant #14 requires authorization for 14th+ bundle target.
- Stage D.3 (revision) may require user authorization if the revision substantially changes a bundle's published-claim profile.
- Stage G (cross-bundle final pass) requires user authorization if cross-bundle cluster drift introduces a contradiction across siblings (e.g., flagship F asserts X and the new D5 §13 asserts ¬X).

---

## Phase 7a Effort Aggregate

| Sub-wave | Effort | Cumulative |
|---|---|---|
| 7a.0 (pre-flight cleanup) | 3–4 wk | 3–4 wk |
| 7a.1 (robustness infra) | 1.5–2 wk | 4.5–6 wk |
| 7a.2 (I1 consolidation) | 2–3 wk | 6.5–9 wk |
| 7a.3 (I2 consolidation) | 1.5–2 wk | 8–11 wk |
| 7a.4 (procedure freeze) | 0.5 wk | 8.5–11.5 wk |
| 7a.5 (Phase 7b gate) | 0 wk | 8.5–11.5 wk |

**Total Phase 7a:** ~8.5–11.5 person-weeks; ~2–3 person-months.

**Parallelism opportunities:**
- 7a.1 (robustness infra) can run in parallel with 7a.0 (cleanup) — different file domains; non-overlapping
- 7a.2 (I1) and 7a.3 (I2) can partially overlap once 7a.1 ships, since different content domains
- Effective wall-clock with reasonable parallelism: ~4–6 weeks

**Per `feedback_ignore_pm_estimates.md`:** these PM estimates are reference-only.

---

## Phase 7a Decision Gates

- **Gate 7a.0** — every paper's per-paper Stage-13 panel at 🟢/🟡; bundle-level RED may persist
- **Gate 7a.1** — robustness infrastructure operational; `bundle_append.py` + `bundle_source_manifest.py` + validate.py CHECK 22 deployed; procedure docs drafted
- **Gate 7a.2** — I1 at 🟢; lift procedure proven on lightweight bundle
- **Gate 7a.3** — I2 at 🟢; lift procedure refined for software-paper shape
- **Gate 7a.4** — procedure docs frozen as canonical references for Phase 7b/7c/...
- **Gate 7a.5** — Phase 7a CLOSES; Phase 7b authorization received

---

## Risks and Mitigations

**Risk: 7a.0 finding count exceeds 2026-04-29 sweep projection.** The heatmap is from a sweep before Phase 6m R6 closure; freshness may have shifted. Phase 6m R6 may have introduced new findings or eliminated some.
*Mitigation:* Run `BUNDLE_READINESS_HEATMAP.md` regen at sub-wave 7a.0 entry to get a fresh snapshot. If finding count is materially different, adjust sub-wave 7a.0 scope.

**Risk: Robustness infra design inadequate for unanticipated Phase 6X output shapes.** A future Phase 6X may produce content the current append protocol doesn't cleanly handle (e.g., a structural-substrate paper that should anchor multiple bundles; or a paper that is itself bundle-shaped requiring direct Tier 1 status).
*Mitigation:* Sub-wave 7a.1.6 protocol documents D.3 (revision required) as the manual-judgment fallback. The protocol does NOT claim full automation; it claims "structured handling with documented branch points and user authorization gates."

**Risk: I1 or I2 surfaces lift-procedure issues that require infra revision.** Sub-waves 7a.2/7a.3 are the validation of sub-wave 7a.1's design. If a procedure issue is unfixable by polish-level edits, may require infra rewrite.
*Mitigation:* Sub-wave 7a.1 budgets ~1.5–2 person-weeks; if 7a.2 reveals an unfixable issue, rebudget 7a.1 by 0.5–1 person-week and re-iterate.

**Risk: Paper44 (Phase 6f W7 + W8) draft not yet at submission-ready state.** I1's sidebar primary content is paper44, which is "expanding session-by-session" per `PAPER_DRAFT_MAPPING.md`. If paper44 is still mid-Wave-8 at sub-wave 7a.2 entry, I1 lift cannot complete its sidebar.
*Mitigation:* Lift the paper44 content that *is* shipped (Sessions 1+2+3 SHIPPED 2026-04-29; Sessions 4-5 may complete during Phase 7a); flag remaining content for late-Phase-6 absorption protocol if paper44 ships post-I1 lift. Since I1 is 🟢 entry-state and paper44 sessions 1–3 are shipped, the lift is viable at the current snapshot.

**Risk: User Phase 6n trigger during Phase 7a runtime.** If Phase 6n is triggered during Phase 7a execution, Phase 7a's robustness infra is the *first invocation* of the protocol — design risk with no test cycle.
*Mitigation:* Sub-wave 7a.4 audit specifically rehearses the protocol against a hypothetical Phase 6n. If user does trigger Phase 6n during Phase 7a, the rehearsal becomes a live test; document outcomes in `LATE_PHASE6_ABSORPTION_PROTOCOL.md` v2.

---

## Phase 7a Cross-References

**Parent / sibling roadmaps:**
- `Phase7_Roadmap.md` — umbrella drafting roadmap (parent)
- `Phase6m_Roadmap.md` — most recent Phase 6 sub-phase; D5 source manifest
- `Phase6i_Roadmap.md` — bundle infrastructure (Wave 7) prerequisite
- (future) `Phase7b_Roadmap.md` — successor sub-phase, scoped post-Gate 7a.5

**Strategy + mapping documents:**
- `docs/PAPER_STRATEGY.md` — 13-bundle architecture (canonical)
- `docs/PAPER_DRAFT_MAPPING.md` — per-existing-draft → per-bundle assignment table; the source of truth for `bundle_source_manifest.py`
- `docs/agents/claims-reviewer-bundle-prompts.md` — per-bundle Stage-13 anchor list

**New Phase 7a artifacts (delivered):**
- `scripts/bundle_source_manifest.py`
- `scripts/bundle_append.py`
- `scripts/check_bundle_source_freshness.py` (validate.py CHECK 22)
- `docs/BUNDLE_LIFT_PROCEDURE.md`
- `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md`
- `papers/I1/` directory (full bundle)
- `papers/I2/` directory (full bundle)

**Pipeline references:**
- `WAVE_EXECUTION_PIPELINE.md` — 14-stage process; sub-wave 7a.4.4 updates Stage 10 section
- `CLAUDE.md` Tier-2 references — sub-wave 7a.4.3 adds new entries

**Bundle infrastructure (existing):**
- `scripts/sentence_state.py` — `bundle_destination` schema
- `scripts/bundle_migration.py` — sentence-state migration  
- `scripts/bundle_clusters.py` — cross-bundle cluster registry
- `scripts/bundle_readiness.py` — heatmap aggregator
- `scripts/check_bundle_consistency.py` — validate.py CHECK 21
- `papers/cluster_bundle_index.json` — cross-bundle cluster registry

---

## Anticipated Phase 7b Scope (preview, not committed)

After Phase 7a closes:

**Phase 7b — D5 Consolidation + Tier-2 PRL Splashes (paper25, paper27)**

Sub-wave plan:
- 7b.0: heatmap regen + freshness check
- 7b.1: D5 lift (Phase 6m material + paper17 + paper29 + paper31 + paper32 + paper34 + paper42b §7)
- 7b.2: L1 lift (paper25 standalone)
- 7b.3: L3 lift (paper27 standalone; resolve 1 critical blocker first)
- 7b.4: D5 ↔ L1 cross-bundle consistency (D5 §6 references L1)
- 7b.5: BUNDLE_LIFT_PROCEDURE.md update with deep-paper + Tier-2-splash patterns
- 7b.6: Phase 7c trigger gate

Anticipated effort: ~9–12 person-weeks.

(The detailed Phase 7b roadmap is drafted at Phase 7a sub-wave 7a.5 once Gate 7a.5 PASS confirmed.)

---

*Created 2026-04-30. Phase 7a is the first sub-phase of Phase 7. Robustness infrastructure for late-arriving Phase 6 outputs is the load-bearing design driver per user direction. Updates atomically as sub-waves close.*
