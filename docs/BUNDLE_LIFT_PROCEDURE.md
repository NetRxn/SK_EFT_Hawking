# Bundle Lift Procedure

**Phase 7a sub-wave 7a.1.5 initial draft (2026-05-01); refined and FROZEN in sub-wave 7a.4 (2026-05-01) against actual I1 + I2 lift execution.**

Canonical 14-step workflow for lifting per-paper draft content into a publication bundle (`papers/<X>/`). Consumed by all Phase 7 sub-phases (7a–7g) and by the late-Phase-6 absorption protocol (`docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md`).

**Stages 9, 10, 13 are three distinct reviewer-agent invocations.** Each writes to its own output location; findings consolidate via the supersession ledger. Do not conflate them.

**Reviewer-stage ordering is a hard gate.** Stage 13 (adversarial review) may not be invoked until **both** Stage 9 (figure review) AND Stage 10 (claims review) are GREEN, with all fixes from those stages applied. Stages 9 and 10 may run in parallel against the same bundle if the bundle has no figure-prose dependencies; otherwise sequence them. Across *different* bundles, all three stages may run in parallel — multi-bundle parallelism is encouraged when the work is independent.

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

### §3. Initial lift / append (per source paper, OR sourceless synthesis)

> **Framing (load-bearing).** Bundles are *synthesis-driven new compositions*, not stitched-together copies of source per-paper drafts. The per-paper material is **substrate** — raw research content the bundle draws from — but the bundle's narrative arc, section structure, and prose are **authored fresh** with cross-program synthesis as the goal. The `bundle_append.py` script registers a source as contributing to the bundle and inserts a structural anchor (a section heading + TODO comment) so the bookkeeping (`source_manifest.md`, `append_log.json`) stays accurate; it does NOT copy source prose. Section bodies are authored in §7 below.

**Two paths:**

#### §3a. Sourced bundle (typical case)

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

#### §3b. Sourceless bundle (fresh synthesis from Lean substrate; e.g. I2)

Some bundles have no per-paper-draft sources to lift — their substrate is Lean modules + working-docs synthesis only. The canonical example from Phase 7a is **I2** (lean-tensor-categories + VerifiedJackknife software/methodology paper). For these:

```bash
uv run python scripts/bundle_append.py \
    --bundle <X> \
    --source-paper "<X>_initial_draft" \
    --insertion-point '§1' \
    --notes "Sourceless synthesis: substrate is <N> Lean modules + working-docs notes" \
    --lean-modules "<comma-separated Lean module names>" \
    --initial-lift
```

The synthetic source-paper key (`<X>_initial_draft`) registers the lift event in `append_log.json` even though no `papers/<key>/` directory exists. `bundle_metadata.json` should record `notes: "fresh-authored as a synthesis-driven new composition (no per-paper-draft sources to lift; sourceless per PAPER_DRAFT_MAPPING.md)"`.

#### §3c. Common to §3a / §3b

After append: `bundle_metadata.json.last_lift` = now; `stage13_redo_required` = true; `stage{9,10,13}_status` reset to `pending`.

#### §3d. Bookkeeping-only events (no content change)

Sometimes source-paper mtimes drift but the bundle's own `paper_draft.tex` does **not** need a content lift. Verified cases include:

- **Auto-regenerated artifacts in source-paper dirs** (e.g., `scripts/render_paper_tables.py` rewriting `tables/*.tex`) when the bundle does not `\input` those source tables. Bundle compile path is decoupled; source mtimes are misleading.
- **Per-paper prose revisions that have no counterpart in the bundle draft.** If a source paper's abstract is rewritten but the bundle draft was already written without quoting that abstract verbatim, no propagation is needed.
- **Inline absorption that bypassed the formal `bundle_append.py` cycle.** If a bundle draft was edited directly to absorb source-paper changes without going through `--initial-lift` / append, that edit needs to be retroactively recorded.

In these cases, `validate.py --check bundle_source_freshness` will flag the bundle stale, but a real lift would be inappropriate (no `\section` to insert; no stage9/10/13 redo is warranted because reviewed content is unchanged).

The canonical tool is:

```bash
uv run python scripts/bundle_append.py --bundle <X> --bookkeeping-only \
    --lift-action <Action> \
    --notes "<why no content change is needed; reference the specific drift>"
```

Where `<Action>` is one of:
- `Freshness-bookkeeping` — generic source-mtime drift acknowledgement
- `Prose-revision-bookkeeping` — source paper prose was revised but bundle prose was already aligned
- `Inline-absorption-record` — retroactively records a bundle-draft edit that absorbed source-paper content outside the formal append cycle

Effects (vs `§3a`/`§3b` full lifts):
- Appends `lift_action: "<Action>"`, `stage13_redo_required: false`, `bundle_section_inserted: "(n/a — bookkeeping)"` to `append_log.json`
- Appends a dated H2 to `change_log.md` flagged `(bookkeeping)`
- Bumps `bundle_metadata.json.last_lift` and clears `freshness_stale`
- **Does NOT** touch `paper_draft.tex`
- **Does NOT** flip `stage{9,10,13}_status` — the prior review remains valid

The notes field is required; it carries the entire explanation of why no content change was needed, so it should specifically name the drifted files and the verification (`grep`, manual inspection, or compile-time decoupling) that justifies the bookkeeping path over a real lift.

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
- **Use Unicode glyphs in figure source, not HTML entities.** kaleido renders HTML entities literally (e.g. `&rarr;` ships as the literal string `&rarr;` in the PNG, breaking review). Use `→`, `←`, `↔`, `⊗`, `⊕`, `≅`, `≃`, `∈`, etc. directly. Verified during I2 round-3 figure review (i2_fig5).
- **Tier-3 reproducibility-anchor requirement (I-bundles only):** every worked-case figure in I1 / I2 must cite either an Aristotle run ID (e.g. `270e77a0`, `79e07d55`) **or** a commit-pinned counterexample (`commit:<sha>`) inside the figure's caption. Stage 13 will FAIL the figure if the anchor is missing or unresolvable. The reproducibility-anchor block has the form:
  ```
  Reproduces: Aristotle run <ID> (sealed YYYY-MM-DD)
  ```
  Batch-level Aristotle run IDs (one ID covering multiple sub-lemmas) are an advisory yellow, not a fail — Stage 10 will attempt registry pin in a follow-up round.

### §7. Paper-draft authoring (synthesis-driven)

This is the substantive bundle work. The `\section` skeleton from §3 is just structural — the prose is authored fresh.

- **Synthesis, not copy.** For each section, draw on relevant per-paper material in `papers/<source>/paper_draft.tex` + working-docs notes + Lean modules + WAVE_EXECUTION_PIPELINE.md / ARCHITECTURE_SCOPE.md as substrate. Author the section's prose to advance the bundle's overarching narrative, not to preserve source-paper structure. A bundle's section §N typically synthesizes ideas from 2–5 sources + cross-bundle context, not 1-to-1 lift from one source.
- Cite source per-paper drafts with `\cite{paperN_topic}` if/where the bundle's claim depends on a result derived in that source. Otherwise reference Lean modules / theorem names directly.
- Replace inline numerical literals with `\input{tables/<spec_id>.tex}` per Phase 5v table-pipeline pattern.
- Bundle headline claims should advance the program's synthesis: cross-program structural results, multi-mechanism falsifiers, methodology lessons that transcend any single wave, etc. — not just "results from waves X+Y bundled together."
- **LaTeX compile gate (mandatory before §8).** Run:
  ```bash
  cd papers/<X>/ && pdflatex paper_draft.tex
  ```
  After every substantive edit. The compile must produce a clean PDF with no `Missing $` / `Misplaced &` / `Undefined control sequence` errors. Lifted source-paper tables can carry latent bugs (e.g., during I1 sub-wave 7a.2 the lifted `tables/table1_stages.tex` had 4 cells in a 3-column tabular and was missing Stages 4 + 14 — caught by compile, not by Stage 9). **Stage 9 may not be invoked until LaTeX compiles cleanly.**

**Substantive content gates (mandatory before §8):**

1. **4-table cross-registry attribution audit.** When citing a registry entry, verify *which* of the four canonical tables in `src/core/constants.py` it lives in:
   - `AXIOM_METADATA` — formal axioms with eliminability tier (currently 1: `gapped_interface_axiom`, hard)
   - `PLACEHOLDER_THEOREMS` — sorry-free theorem stubs awaiting full proof
   - `HYPOTHESIS_REGISTRY` — tracked-hypothesis Props (algebraic / model / cross-program tiers)
   - `BORDISM_HYPOTHESES` — bordism-specific tracked hypotheses (e.g., Shapiro-style side-channels)

   The four tables together form the *structural-axiom landscape*. A name found in HYPOTHESIS_REGISTRY misattributed to AXIOM_METADATA is a Stage 13 BLOCKER (caught during I1 sub-wave 7a.2 round-2). Use `git grep "<name>" src/core/constants.py` to verify table membership before writing the citation.

2. **Hedging discipline on quantitative claims.** Never hedge a count or numerical literal with "alt convention" or "+N depending on convention" without proving the convention sensitivity. If counts disagree across tools, find the truth — convention drift framing masks actual content drift. (I2 sub-wave 7a.3 round-2 → round-3: §5 number-field count "161 ± 3 alt convention" was actually 164 canonical; the +3 was real drift, not convention sensitivity.)

3. **Cross-program prior-art verifiability.** When claiming prior art in cross-language formalization ecosystems (Coq UniMath, Agda categories, Isabelle/AFP, HOL4, Mizar, Idris, Megalodon, etc.), every claim must resolve to a verifiable URL or canonical ecosystem reference. Hallucinated cross-language libraries (e.g., "Steinberg pivotal-Coq library", "Agda unimath" — UniMath is Coq, not Agda, "Isabelle/AFP Tensor Networks") are an attribution failure caught by Stage 13 (I2 sub-wave 7a.3 round-2). When in doubt, cite the ecosystem at the project level (UniMath; Mathlib4) rather than naming a specific library that may not exist.

4. **Definition before broadening.** When broadening an attribution from a narrow to a wider class (e.g., "Microsoft" → "broader research community pursuing Majorana platforms"), verify each addition belongs in the broadened category. Surface code is *abelian-stabilizer-class* QEC, not non-Abelian-anyon TQC; do not group them in a non-Abelian-anyon parenthetical (I2 sub-wave 7a.3 round-2 → round-3).

**Reviewer scope (per user direction 2026-05-01):** Stages 9 / 10 / 13 (§§8–10 below) review the **bundle paper**, not the source per-paper drafts. Findings on `papers/paperN_*/` are not in Phase 7's scope; per-paper material that gets synthesized into a bundle is reviewed via the bundle's own stage triple.

### §8. Stage 9 — figure review (LLM visual review)

**Agent:** `physics-qa:figure-reviewer` (plugin agent at `.claude/plugins/physics-qa/agents/figure-reviewer.md`).

**Invocation:** direct via Skill tool with parameter `bundle_target=<X>`.

**Plugin-agent fallback path.** If `physics-qa:figure-reviewer` is not available as a `subagent_type` in the current runtime (observed during Phase 7a 7a.2/7a.3 execution), fall back to a `general-purpose` Agent invocation prompted to load and follow the agent definition file at `.claude/plugins/physics-qa/agents/figure-reviewer.md`. The fallback path produces equivalent output to the direct Skill invocation but adds ~1 round-trip; prefer the direct path when available.

**Output:**
- `papers/<X>/figures/figure_review_report.json`
- per-figure findings appended to `papers/<X>/audit_log.jsonl`

**Update:** `bundle_metadata.json.stage9_status` ← review verdict (`green` / `yellow` / `red`); `last_stage9_review` ← ISO timestamp.

**Pass criterion:** ALL PASS, no FAIL, no MINOR (per `WAVE_EXECUTION_PIPELINE.md` Stage 9 gate).

### §9. Stage 10 — paper claims review (LLM content review)

**Agent:** `physics-qa:claims-reviewer` (plugin agent at `.claude/plugins/physics-qa/agents/claims-reviewer.md`).

**Invocation:** direct via Skill tool with parameter `bundle_target=<X>`. Plugin-agent fallback path same as §8.

**Multi-bundle parallelism is fine** — two `claims-reviewer` invocations against *different* bundles (e.g., I1 + I2 simultaneously) run independently. Same-bundle invocations must be sequential. Verified during Phase 7a sub-waves 7a.2 + 7a.3 (user-confirmed: *"oh i see - good job scoping - multi-paper is fine."*).

**Anchor list:** `docs/agents/claims-reviewer-bundle-prompts.md` row for `<X>` (per-bundle anchor of load-bearing claims + citations the bundle's review must verify).

**Output:**
- `papers/<X>/claims_review.json`
- findings appended to `papers/<X>/audit_log.jsonl`

**Update:** `bundle_metadata.json.stage10_status` ← review verdict; `last_stage10_review` ← ISO timestamp.

**Pass criterion:** zero FAIL findings — numerical-claim agreement within 0.5%; "formally verified" claims match Lean state; citation DOIs resolve.

### §10. Stage 13 — adversarial review (fresh-context Opus sweep)

**Agent:** `adversarial-reviewer` (plugin agent at `.claude/plugins/physics-qa/agents/adversarial-reviewer.md`).

**Orchestrator:** `scripts/review_runner.py --bundle <X> --prep-brief` (Phase 6i Wave 7.4 deliverable; bundle-aware Stage-13 entry point).

**Hard pre-condition.** Stage 13 may not be invoked until Stages 9 and 10 are both GREEN with all fixes applied. Per user direction 2026-05-01: *"Claims & figure reviewers should always run and fixes should be implemented before adversarial review is conducted."* Invoking Stage 13 against a bundle still showing yellow/red on Stage 9 or 10 wastes the adversarial reviewer's budget on already-known issues.

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
3. **All-occurrence verification.** Before declaring a referential fix complete, `git grep` for the old reference across the whole bundle directory and any cross-referencing files. Filenames, theorem names, and counts often appear multiple times in a single `paper_draft.tex` (one in §2 prose, another in §5 table, another in §9 footnote). I2 sub-wave 7a.3 round-2 caught a missed second occurrence of `tests/test_jackknife.py` at line 232 after the round-1 fix had only updated line 17. The grep must be empty before claiming fixed.
4. Append entry to `docs/review_finding_supersessions.json` with `meta.status: open → fixed | accepted` per closed finding. The entry must include deterministic-recheck evidence (file:line + replacement text) so a future fresh-context reviewer can verify the closure without re-running the agent. As of 2026-05-01 the ledger has 174 entries spanning Phase 6i + Phase 7a; the disciplined append-only pattern is what allows multi-round Stage-13 cycles to converge.
5. Re-invoke the *same* reviewer agent in fresh context with `bundle_target=<X>`.
6. Confirm BLOCKER cleared. If clean: `bundle_metadata.json.<stage>_status` advances. If not: iterate from step 2.

**Round-broadening discipline (post-7a.3 lesson).** When fixing a finding by *broadening* an attribution or citation list (e.g., "Microsoft Quantum" → "broader research community"), the round-2 broadening must not introduce *new* findings the round-1 narrow form did not have. Verify each new addition is categorically consistent with the surrounding parenthetical (see §7 substantive-content gate #4 above). Empirically, this pattern was observed in I2 sub-wave 7a.3 round-2 → round-3 (Google Quantum AI surface-code work introduced into a non-Abelian-anyon parenthetical) and is now a candidate Stage-14 ratified QI rule (`qi-round-broadening-introduces-new-issues`).

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

*Created Phase 7a sub-wave 7a.1.5 (2026-05-01). **FROZEN at sub-wave 7a.4 (2026-05-01)** after I1 + I2 lift execution. Twelve concrete refinements absorbed: (1) hard-gated reviewer ordering (§§ preamble + §10), (2) sourceless-bundle path (§3b), (3) Unicode in figure source (§6), (4) Tier-3 reproducibility-anchor block (§6), (5) LaTeX compile gate before Stage 9 (§7), (6) 4-table cross-registry attribution audit (§7 gate 1), (7) hedging discipline (§7 gate 2), (8) cross-program prior-art verifiability (§7 gate 3), (9) broadening categorical-consistency check (§7 gate 4 + §11 round-broadening discipline), (10) plugin-agent fallback path (§§8–10), (11) multi-bundle parallelism explicit (§9), (12) all-occurrence grep + supersession-ledger discipline (§11 steps 3–4). Subsequent Phase 7b/7c/... waves consume the frozen procedure without further iteration.*

---

**Post-freeze validation footnote (2026-05-07).** Phase 7 absorption Sessions 1–5 (2026-05-06 → 2026-05-08) have validated the procedure across all 14 bundles' D.2 / D.3 / D.4 absorption events without procedural revision. Six refinements absorbed at Session 5: (a) primary-source WebFetch standing-policy escalation (when a numerical magnitude in a Lean constant / paper claim / registry entry is registry-anchored or unverified, fetch the primary-source PDF and verify before relying on it); (b) honest downgrade of unsourced Bayes-factor claims to AIC/BIC information-criteria framing where the cited sources are AIC-only (e.g., Luciano arXiv:2506.03019 Table II); (c) strict-extension-layer pattern for backwards-compatible structure-shape changes (e.g., `SakharovExtended` wrapping unchanged `SakharovConditions`); (d) Prop-typed conditional witness for substrate-physics grounding at constructor time; (e) deprecated-alias preservation for cross-bundle citation continuity (`@[deprecated]` aliases keep older theorem names cite-able while body content refactors); (f) methodology-misnaming correction (rename `_bayes_factor_` → `_information_criteria_` for sources whose methodology is AIC/BIC-only, not Bayes). These refinements operate within the existing 14-step procedure — no procedural step is added or modified.
