# Bundle Lift Procedure

**Phase 7a sub-wave 7a.1.5 deliverable** (initial draft; refined post-I1/I2 in 7a.4).

Canonical 14-step workflow for lifting per-paper draft content into a publication bundle (`papers/<X>/`). Consumed by all Phase 7 sub-phases (7a–7g) and by the late-Phase-6 absorption protocol (`docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md`).

**Stages 9, 10, 13 are three distinct reviewer-agent invocations.** Each writes to its own output location; findings consolidate via the supersession ledger. Do not conflate them.

---

## Pre-conditions

- Bundle target identified at Stage 1 of every contributing source paper's wave (Pipeline Invariant #14).
- Source papers at 🟢/🟡 per-paper readiness (verify in `docs/BUNDLE_READINESS_HEATMAP.md` + each `papers/<source>/READINESS_GATES.md`).
- `docs/PAPER_DRAFT_MAPPING.md` row exists for every contributing source → bundle mapping.
- Project at `validate.py` GREEN with optional `bundle_source_freshness` advisories acceptable.

---

## Procedure

### §1. Pre-lift checks

- Confirm 🟢/🟡 source-paper readiness via `BUNDLE_READINESS_HEATMAP.md`.
- Confirm mapping rows exist:
  ```bash
  uv run python scripts/bundle_source_manifest.py --bundle <X> --report
  ```
- Bundle directory state:
  - **Initial lift** (no `papers/<X>/paper_draft.tex` yet): proceed to §2.
  - **Append** (`paper_draft.tex` exists): verify `bundle_metadata.json.freshness_stale=true` OR `stage13_redo_required=true` to confirm a lift is genuinely needed.

### §2. Bundle directory creation / refresh

```bash
uv run python scripts/bundle_source_manifest.py --bundle <X>
```

Creates (idempotent):
- `papers/<X>/{figures,tables}/`
- `papers/<X>/source_manifest.md`
- `papers/<X>/append_log.json`
- `papers/<X>/change_log.md`
- `papers/<X>/audit_log.jsonl`
- `papers/<X>/bundle_metadata.json`

Schema: `docs/BUNDLE_DIRECTORY_SCHEMA.md`.

### §3. Initial lift / append (per source paper)

> **Framing (load-bearing).** Bundles are *synthesis-driven new compositions*, not stitched-together copies of source per-paper drafts. The per-paper material is **substrate** — raw research content the bundle draws from — but the bundle's narrative arc, section structure, and prose are **authored fresh** with cross-program synthesis as the goal. The `bundle_append.py` script registers a source as contributing to the bundle and inserts a structural anchor (a section heading + TODO comment) so the bookkeeping (`source_manifest.md`, `append_log.json`) stays accurate; it does NOT copy source prose. Section bodies are authored in §7 below.

For each contributing source:

```bash
uv run python scripts/bundle_append.py \
    --bundle <X> \
    --source-paper <paperN_topic> \
    --insertion-point '<§N>' \
    --notes "<short rationale>" \
    --lean-modules "<comma-separated Lean module names if applicable>" \
    [--initial-lift]
```

The first invocation per bundle uses `--initial-lift` to create the `paper_draft.tex` skeleton. Subsequent calls register additional sources without copying their content.

After append: `bundle_metadata.json.last_lift` = now; `stage13_redo_required` = true; `stage{9,10,13}_status` reset to `pending`.

### §4. Sentence-state migration

After all source-paper appends for the bundle have run (often a single sub-wave), migrate sentence-level provenance:

```bash
uv run python scripts/bundle_migration.py --paper <paperN_topic>   # for each source
uv run python scripts/bundle_clusters.py                            # update cross-bundle clusters
```

Effects:
- Every non-tombstoned sentence in `papers/<source>/prose_state.json` acquires `bundle_destination = <X>`.
- `papers/cluster_bundle_index.json` re-projects clusters via the updated mapping.

### §5. Citation merge

Manual / scripted task (no script wraps this yet — defer to ad-hoc `bibtool` invocations or hand-merge):

- Copy each source's bibitems from `papers/<source>/paper_draft.tex` (or `papers/<source>/bibliography.bib` if present) into `papers/<X>/bibliography.bib`.
- Resolve bibkey collisions per Phase 6m citation-merge precedent: prefer the entry already in `CITATION_REGISTRY`; flag conflicts in the bundle's `change_log.md`.
- Re-run `validate.py --check citation_primary_sources_present` to ensure every absorbed bibkey resolves to a primary-source cache file.

### §6. Figure migration

- Copy each source's referenced figures from `papers/<source>/figures/` into `papers/<X>/figures/`.
- Preserve `# viz-ref:` tags on the corresponding figure entries (else CHECK 6 / `viz_consistency` flags drift).
- Bundle-specific re-renders (e.g., scale changes, multi-panel composites) go through `src/core/visualizations.py` per Pipeline Invariant #3.

### §7. Paper-draft authoring (synthesis-driven)

This is the substantive bundle work. The `\section` skeleton from §3 is just structural — the prose is authored fresh.

- **Synthesis, not copy.** For each section, draw on relevant per-paper material in `papers/<source>/paper_draft.tex` + working-docs notes + Lean modules + WAVE_EXECUTION_PIPELINE.md / ARCHITECTURE_SCOPE.md as substrate. Author the section's prose to advance the bundle's overarching narrative, not to preserve source-paper structure. A bundle's section §N typically synthesizes ideas from 2–5 sources + cross-bundle context, not 1-to-1 lift from one source.
- Cite source per-paper drafts with `\cite{paperN_topic}` if/where the bundle's claim depends on a result derived in that source. Otherwise reference Lean modules / theorem names directly.
- Replace inline numerical literals with `\input{tables/<spec_id>.tex}` per Phase 5v table-pipeline pattern.
- Bundle headline claims should advance the program's synthesis: cross-program structural results, multi-mechanism falsifiers, methodology lessons that transcend any single wave, etc. — not just "results from waves X+Y bundled together."
- Verify draft compiles:
  ```bash
  cd papers/<X>/ && pdflatex paper_draft.tex
  ```

**Reviewer scope (per user direction 2026-05-01):** Stages 9 / 10 / 13 (§§8–10 below) review the **bundle paper**, not the source per-paper drafts. Findings on `papers/paperN_*/` are not in Phase 7's scope; per-paper material that gets synthesized into a bundle is reviewed via the bundle's own stage triple.

### §8. Stage 9 — figure review (LLM visual review)

**Agent:** `physics-qa:figure-reviewer` (plugin agent at `.claude/plugins/physics-qa/agents/figure-reviewer.md`).

**Invocation:** direct via Skill tool with parameter `bundle_target=<X>`.

**Output:**
- `papers/<X>/figures/figure_review_report.json`
- per-figure findings appended to `papers/<X>/audit_log.jsonl`

**Update:** `bundle_metadata.json.stage9_status` ← review verdict (`green` / `yellow` / `red`); `last_stage9_review` ← ISO timestamp.

**Pass criterion:** ALL PASS, no FAIL, no MINOR (per `WAVE_EXECUTION_PIPELINE.md` Stage 9 gate).

### §9. Stage 10 — paper claims review (LLM content review)

**Agent:** `physics-qa:claims-reviewer` (plugin agent at `.claude/plugins/physics-qa/agents/claims-reviewer.md`).

**Invocation:** direct via Skill tool with parameter `bundle_target=<X>`.

**Anchor list:** `docs/agents/claims-reviewer-bundle-prompts.md` row for `<X>` (per-bundle anchor of load-bearing claims + citations the bundle's review must verify).

**Output:**
- `papers/<X>/claims_review.json`
- findings appended to `papers/<X>/audit_log.jsonl`

**Update:** `bundle_metadata.json.stage10_status` ← review verdict; `last_stage10_review` ← ISO timestamp.

**Pass criterion:** zero FAIL findings — numerical-claim agreement within 0.5%; "formally verified" claims match Lean state; citation DOIs resolve.

### §10. Stage 13 — adversarial review (fresh-context Opus sweep)

**Agent:** `adversarial-reviewer` (plugin agent at `.claude/plugins/physics-qa/agents/adversarial-reviewer.md`).

**Orchestrator:** `scripts/review_runner.py --bundle <X> --prep-brief` (Phase 6i Wave 7.4 deliverable; bundle-aware Stage-13 entry point).

**Output:** `papers/AutomatedReviews/<DATE>-bundle-stage13/<X>.md` (structured markdown report).

**Auto-pickup:** `scripts/build_graph.extract_review_finding_nodes` → `ReviewFinding` graph nodes with `FLAGS` edges to bundle. `BLOCKER` findings flip the affected `ReadinessGate` to `blocked`.

**Per-bundle profile (`docs/agents/claims-reviewer-bundle-prompts.md`):**
- Tier 0 (F): review-paper style — verify cited published L*/D* claims against citation cache.
- Tier 1 (D1–D5): intra-bundle consistency across lifted sections + cross-bundle cross-bridge checks.
- Tier 2 (L1–L3): stand-alone PRL depth; carry the bundle-specific anchor.
- Tier 3 (I1, I2): software/methodology review — each worked case must trace to a reproducible Aristotle run ID or commit-pinned counterexample.
- Tier 4 (E1, E2): lightweight letter review + device-parameter audit pass.

**Update:** `bundle_metadata.json.stage13_status` ← review verdict; `last_stage13_review` ← ISO timestamp; `stage13_review_doc` ← path.

**Pass criterion:** zero `BLOCKER` findings under `papers/AutomatedReviews/` with `status != fixed`.

### §11. BLOCKER resolution loop

For any BLOCKER surfaced in §8 / §9 / §10:

1. Reviewer agent emits BLOCKER → `audit_log.jsonl` entry (Stage 9/10) or `ReviewFinding` graph node (Stage 13).
2. **Author** (not reviewer) fixes via direct edit to `paper_draft.tex` / `figures/` / source paper / Lean module as appropriate.
3. Append entry to `docs/review_finding_supersessions.json` with `meta.status: open → fixed | accepted` per closed finding.
4. Re-invoke the *same* reviewer agent in fresh context with `bundle_target=<X>`.
5. Confirm BLOCKER cleared. If clean: `bundle_metadata.json.<stage>_status` advances. If not: iterate from step 2.

Per `WAVE_EXECUTION_PIPELINE.md` Stage 13: *"The author fixes; the author re-invokes. Separation of the fix-and-review roles is the whole reason the agent exists."*

### §12. Iteration to GREEN

Repeat §8 → §9 → §10 → §11 until `bundle_metadata.json` shows:

- `stage9_status == "green"`
- `stage10_status == "green"`
- `stage13_status == "green"`
- `blockers_open == 0`
- `stage13_redo_required == false`
- `freshness_stale == false`

### §13. Dashboard refresh + heatmap regen (mandatory exit step)

```bash
uv run python scripts/datastar_bundles.py            # regen dashboard data
uv run python scripts/bundle_readiness.py --heatmap  # regen BUNDLE_READINESS_HEATMAP.md
uv run python scripts/validate.py --check bundle_consistency --check bundle_source_freshness
uv run python scripts/provenance_dashboard.py        # spot-check localhost:8050 /bundles
```

All four must succeed before bundle close. Commit the regenerated `docs/BUNDLE_READINESS_HEATMAP.md` + `papers/cluster_bundle_index.json`.

### §14. Bundle close

- `papers/<X>/READINESS_GATES.md` panel populated (manually authored or copied from latest Stage-13 review doc).
- `change_log.md` final entry: "YYYY-MM-DD — Bundle <X> CLOSED at GREEN. <person-week effort>. Phase 7<sub-phase>."
- `audit_log.jsonl` final state archived (no operation needed; append-only file).
- `bundle_metadata.json` final snapshot committed.

---

## Cross-references

- `WAVE_EXECUTION_PIPELINE.md` Stage 9 ↔ §8 (figure review)
- `WAVE_EXECUTION_PIPELINE.md` Stage 10 ↔ §9 (claims review)
- `WAVE_EXECUTION_PIPELINE.md` Stage 13 ↔ §10 (adversarial review)
- `docs/BUNDLE_DIRECTORY_SCHEMA.md` — `bundle_metadata.json` + `append_log.json` schemas
- `docs/agents/claims-reviewer-bundle-prompts.md` — per-bundle Stage-13 anchor list
- `docs/PAPER_STRATEGY.md` §2 — bundle profiles
- `docs/PAPER_DRAFT_MAPPING.md` — per-source → per-bundle assignment table
- `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md` — re-uses §3 / §4 / §10 / §11 / §13 for late absorption
- `papers/cluster_bundle_index.json` — cross-bundle cluster registry
- `docs/review_finding_supersessions.json` — author-driven finding closures (append-only)
- Pipeline Invariant #14 — bundle assignment mandatory at Stage 1

---

*Created Phase 7a sub-wave 7a.1.5 (2026-05-01). Initial draft. Refines after I1 + I2 lift execution per sub-wave 7a.4. Subsequent Phase 7b/7c/... waves consume the frozen procedure.*
