# Phase 5v: Knowledge Graph Foundation + Paper Readiness System

## Technical Roadmap — April 2026

*Prepared 2026-04-15 | Triggered by: April Perplexity review round surfacing 13 distinct failure modes that the existing pipeline could not catch, combined with an undercount of Lean declarations in the knowledge graph caused by silent short-name collisions.*

**Scope:** Close the process gaps that allowed the April review issues to reach draft state, by (a) fixing the knowledge-graph foundation so it accurately reflects the full codebase, (b) extending the schema to cover the process dimensions (reviews, tests, production runs, placeholders, contradictions, readiness gates), (c) migrating from JSON-derived reads to PG+AGE as source of truth now that scale warrants it, (d) building a per-paper readiness state machine with auto-invalidation on upstream changes, (e) adding an internal adversarial-review pipeline stage backed by a fresh-context Opus agent, and (f) surfacing all of the above in the dashboard.

**Separate from:**
- Phase 5u (April paper revisions — edits themselves) — content track
- Phase 5p/q/r/s (Lean formalization waves) — proof track
- Phase 6 (vestigial MC at scale) — compute track

**Why a separate phase:** These are **process fixes**, not paper edits. The April review surfaced issues the existing 12-stage pipeline could not detect: placeholder Lean proofs that pass `lake build`, paper-internal citation mismatches that pass `CHECK 14`, parameter drift from primary sources that `CHECK 15` can't see, narrative overclaims in prose that no stage inspects. Phase 5u fixes the current papers; Phase 5v ensures the next round catches these issues before they ship.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
> 1. Read CLAUDE.md, WAVE_EXECUTION_PIPELINE.md, Inventory Index
> 2. Read `docs/KNOWLEDGE_GRAPH.md` — existing KG spec (Phase 1 / 1.5 live; original Phase 2 / 3 now absorbed here)
> 3. Read `temporary/working-docs/reviews/papers/2026-04-12-Perplexity/SK_EFT_Hawking — Master Systematic Update Checklist.md` — the 13-dimension problem taxonomy is derived from these findings
> 4. Read `.claude/plugins/physics-qa/agents/claims-reviewer.md` and `figure-reviewer.md` — existing QA agents that Stage 13 extends
> 5. Do NOT build the readiness state machine (Wave 4) until Waves 1–3 land; the schema and node coverage must be complete first

---

## Design Principles

1. **Priority 1 (correct product) before Priority 2 (user experience) before Priority 3 (efficiency).** When a wave surfaces a tradeoff, resolve it in this order. All 11 readiness gates are correctness-class; dashboard polish is UX-class.
2. **Graph-native, not bolt-on.** Every new concept (reviews, tests, production runs, readiness, contradictions, placeholders) lands as first-class nodes + edges — not a parallel data file. The graph is the single source of truth.
3. **Auto-discovery over hand-maintained registries.** If the filesystem has the answer, the extractor should read it directly. `PAPER_DEPENDENCIES`, manual figure registration, hand-added review records — all replaced by crawlers.
4. **Silent failures become loud.** Every drop, skip, collision, ambiguity, missing-target emits a log line. The Wave 0 fix (short-name collisions) established this pattern; all subsequent extractors follow it.
5. **Auto-invalidation.** When any node changes, all downstream ReadinessGate instances flip to `needs-recheck`. Cross-paper fix propagation (e.g., Paper 10 Stolz removal → Paper 9 still-present) is the exact failure mode this eliminates.

---

## Follow-up TODOs surfaced by the retrofit pass

### Paper 2 Table 1 — Bogoliubov wavenumber small-k expansion (Lean + formulas.py)

Paper 2 Table 1 reports `δ^(2)(ω=κ)` and `δ^(2)(ω=5κ)` at values ~10⁻⁵–10⁻¹². These are off-shell evaluations using the Bogoliubov-corrected horizon wavenumber:

    k_H ≈ (ω/c_s)·(1 − ω²ξ²/(2c_s²))

This is a perturbative small-kξ expansion of the existing `bogoliubovDispersion` theorem in `HawkingUniversality.lean`. It is **not yet canonicalized**. Paper 2's current table values live only in the paper; the off-shell wavenumber convention isn't a pipeline function.

**Work to register:**
1. **Lean (`lean/SKEFTHawking/WKBAnalysis.lean`)** — Add theorem `bogoliubov_wavenumber_small_k_approx`:
   - Statement: for `ω c_s ξ : ℝ`, `0 < c_s`, the approximation `k ≈ (ω/c_s)·(1 − (ωξ/c_s)²/2)` satisfies the Bogoliubov dispersion to O((ωξ/c_s)⁴):
     `|c_s²·k²·(1 + (kξ)²) − ω²| ≤ (ωξ/c_s)⁴ · ω²` (exact coefficient TBD)
   - Cite parent theorem `bogoliubov_superluminal` (already proved)
   - Target tactic: `nlinarith` or manual algebraic rewrite; escalate to `polyrith` if needed
   - **Work this via lean-lsp/MCP in a focused session (no Aristotle)**
2. **formulas.py** — Add `bogoliubov_wavenumber_small_k(omega, c_s, xi)` with docstring: `Lean: bogoliubov_wavenumber_small_k_approx`, `Aristotle: manual`, `Source: Paper 2 §5 Eq. (N)` (fill in N after final numbering)
3. **tests/** — Add test verifying the small-k expansion matches `bogoliubov_superluminal`'s full expression within tolerance for Steinhauer/Heidelberg/Trento regimes
4. **paper_tables/sources.py** — Add `platform_correction_rows(platforms, omega_factors=(1, 5))` that uses the new wavenumber function + existing `second_order_correction`
5. **papers/paper2_second_order/tables.py** — Spec Table 1 pointing at the new source; retrofit `paper_draft.tex` inline table to `\input{tables/...}`

**Not scope-expansion of Phase 2** (which is marked COMPLETE) — this is a retrofit-driven follow-up that formalizes a convention the paper has been using implicitly. Adding the theorem only sharpens existing formal content.

---

## Absorption of Original KG Roadmap

The existing `docs/KNOWLEDGE_GRAPH.md` lists a Phase 2 and Phase 3 that predate this scoping exercise. Status of each item under Phase 5v:

| Original item | Phase 5v disposition | Rationale |
|---|---|---|
| **Phase 2** — PG+AGE becomes source of truth, generate Python dicts from graph, dashboard write-capability | **Wave 3** (renamed) | Timing is right: JSON scale passing where PG indices will win. |
| **Phase 3** — Paper-to-foundation traversal from `.tex` | **Superseded by Wave 4** (ReadinessGate drill-down) | ReadinessGate system is strictly more powerful — every paper claim rolls up into gates with evidence chains, which is the same query shape as the original traversal but also carries state. |
| **Phase 3** — CI-style automated monitoring | **Superseded by Waves 6–7** (Stage 13 adversarial + Stage 14 QI register) | Stage 13 runs the adversarial sweep on every pipeline execution; Stage 14 tracks process improvements over time. Strictly more than the original "CI monitoring" scope. |
| **Phase 3** — Export to JSON-LD / W3C PROV | **Wave 8** (renamed, kept) | Orthogonal to readiness; external-consumption-only feature (arXiv companion, OpenAIRE, cross-repo provenance). Still valuable, doesn't belong in 1–7. |
| **Phase 3** — Notebook `from src.core.graph import trace_claim` | **Wave 8** (renamed, kept) | Author-workflow tool, standalone. Paired naturally with JSON-LD export in an "external API" wave. |

**Net:** Original Phases 2+3 are fully absorbed. Three items (PG source-of-truth, JSON-LD, notebook API) survive as Waves 3 and 8; two (paper traversal, CI monitoring) are superseded by stronger constructs in Waves 4–7.

---

## Readiness Gate Taxonomy (11 gates per paper)

Derived from the 13-dimension problem space, with two consolidations: `SourceFidelity` folds into `CitationIntegrity` (both are primary-source correspondence); `TestCoverageShape` folds into `ComputationCorrectness` (test shape is a sub-check).

### Priority 1 — Correctness (8 gates)

| # | Gate | Checks | Failed by (April) |
|---|---|---|---|
| 1 | **CitationIntegrity** | Every `\bibitem` arXiv ID resolves to a paper whose title/authors match the claimed reference; every DOI resolves; body-text attributions (author name strings) match `CITATION_REGISTRY` | Paper 7 TPF→galaxy survey; Paper 12 Burkhard→LLM paper; Paper 3 NastaseSonnenschein→MRI paper; Paper 7 "Tong"→"Thorngren" |
| 2 | **CrossPaperConsistency** | Same construct described consistently across companion papers; no `CONTRADICTS` edge without `SUPPORTS` resolution | Paper 7↔8 TPF author-name; Papers 8–11 theorem-count drift; Paper 10 Stolz removed, Paper 9 still cites |
| 3 | **ParameterProvenance** | Every experimental parameter has `human_verified_date` traceable to named source table/figure; deep-research inputs round-tripped to primary | Paper 12 c_s=0.5 vs Falque-measured 0.40 μm/ps (paper's own table contradicts body) |
| 4 | **ComputationCorrectness** | Every formula has at least one `VERIFIES` edge with `test_kind ∈ {golden, identity, roundtrip}` (bounds-only tests alone are insufficient); golden values cross-checked against independent derivation | `compute_dissipative_correction` missing k_H² for 7+ months; tests asserted \|δ_diss\|<0.1 and passed a ~10⁷× error |
| 5 | **LeanProofSubstance** | No Lean declaration with body `rfl`/`decide`/`Equiv.refl`/`trivial` on a non-trivial statement is cited as "verified" in any paper; all such decls carry a `PlaceholderMarker` with upgrade deadline | `sixteen_convergence_full` (tautological — returns its hypothesis); `dai_freed_spin_z4` (`Equiv.refl` on ZMod 16, claims bordism verification) |
| 6 | **AssumptionDisclosure** | Every structure-field constraint + every `HYPOTHESIS_REGISTRY` entry that a cited theorem depends on is named explicitly in the paper's assumptions section | Paper 10 spin-manifold + framing assumption undisclosed; Papers 1/2 tanh-profile κ explained only in caption |
| 7 | **NarrativeGrounding** | Every `ProseClaim` (prose statement not tied to a Formula) has either a `SUPPORTS` edge to a formal artifact or an explicit "interpretive" tag | "all the same 16" narrative; "Ramanujan" Dedekind-eta attribution; "quaternionic structure of spinors" causal origin; "E8 lattice" vs "E8 manifold" conflation |
| 8 | **ProductionRunHealth** | Every `PRODUCES` edge targets a run with status `success`; no paper claim depends on a crashed or zero-output run | Paper 6 "Monte Carlo evidence" with BrokenPipeError on 14/14 workers |

### Priority 2 — User experience / trust signals (3 gates)

| # | Gate | Checks | Failed by (April) |
|---|---|---|---|
| 9 | **CountFreshness** | Every count literal in `.tex` resolves through `counts.tex` macros to current `counts.json`; `REPORTS` edge matches current `CountMetric` node | Paper 15 "94 modules, 33 sorry" vs current 132 modules, 0 sorry |
| 10 | **FirstClaimVerification** | Every "first in any proof assistant" claim has a ledger entry confirming search of Lean/Mathlib/Agda/Coq/Rocq | "First Ext over A(1)" unvetted |
| 11 | **FixPropagation** | Every `ReviewFinding` with `status=fixed` has a `SUPERSEDES` edge; fix landed in all impacted papers (cross-paper propagation check) | Paper 10 Stolz1993 removed; Paper 9 still cites |

Paper-level aggregate: green if all 11 pass, yellow if any P2 open, red if any P1 open.

---

## Wave Structure

```
Wave 0 — DONE this session — Short-name collision fix
Wave 1 — Foundation: counts wiring + auto-discovery + tpf_evasion_margin rename
Wave 2 — Schema extension: 8 new node types + 7 new edge types
Wave 3 — Graph-as-source-of-truth: PG+AGE migration (originally KG Phase 2)
Wave 4 — Readiness state machine: 11 gates × 15 papers = 165 gate instances
Wave 5 — Dashboard readiness surface
Wave 6 — Stage 13: Internal adversarial review (Opus, fresh context)
Wave 7 — Stage 14: Meta-process QI register
Wave 8 — External API: JSON-LD / W3C PROV export + notebook helper (originally KG Phase 3 residue)
```

---

## Wave 0 — Short-name collision fix [DONE 2026-04-15]

**Problem.** `build_graph.extract_lean_declaration_nodes` keyed node IDs on the last namespace component (`lean:{short_name}`). ~42% of Lean declarations were silently dropped when two decls shared a short name in different namespaces. Downstream edge extractors compounded the issue by looking up theorems by short name, silently resolving to the wrong target when collisions existed.

**Fix.** `scripts/build_graph.py`:
- Node ID changed to `lean:{full_name}`
- Autogen helpers filtered at extraction time (`noConfusion`, `casesOn`, `recOn`, etc. — 2,145 noise decls)
- Short-name → full-name index built during node extraction; consumed by edge extractors via `_resolve_lean_short()`
- Ambiguous short names log a WARNING and skip the edge (previously silent)
- HYPOTHESIS_REGISTRY full-name entries now resolve correctly (ASSUMES edges went 0 → 5)
- `meta.full_name` field added to every Lean node for UI display

**Impact.**
| Metric | Pre | Post | Delta |
|---|---|---|---|
| Lean declaration nodes | 3,317 | 3,619 | +302 substantive recovered |
| ASSUMES edges | 0 | 5 | hypothesis-registry wiring restored |
| PROVED_BY | 305 | 304 | -1 (was silently wrong on `tpf_evasion_margin`) |
| Autogen noise | silent drop | filtered + logged | visible |
| Real collisions | silent | logged (1: `tpf_evasion_margin`) | visible |

**Tests.** All 35 tests in `tests/test_build_graph.py` + `tests/test_graph_integrity.py` pass.

**Known residual.** One genuine short-name collision surfaces a WARNING: `tpf_evasion_margin` exists in both `ChiralityWall.lean:298` (proves `evaded_count ≥ 2`) and `LatticeHamiltonian.lean:158` (proves `card TPFViolation - 1 = 2`). Same name, different statements. Resolved in Wave 1.

---

## Wave 1 — Foundation fixes

### Wave 1a — `tpf_evasion_margin` rename [Pipeline: Stages 3a, 5, 12] — DONE 2026-04-15

**Blast radius audit (verified via grep across code/papers/roadmaps/tests):**
- [x] `lean/SKEFTHawking/ChiralityWall.lean:298` (theorem)
- [x] `lean/SKEFTHawking/LatticeHamiltonian.lean:158` (theorem)
- [x] `src/core/constants.py:877` (`ARISTOTLE_THEOREMS['tpf_evasion_margin'] = 'b1ea2eb7'`)
- [x] `src/core/aristotle_interface.py:547` (`SorryGap` registration)
- [x] `docs/analysis/chirality_wall_analysis.md:208` (description)
- [x] No references in `papers/*/paper_draft.tex` (confirmed)
- [x] No references in `formulas.py` `Lean:` refs (confirmed — not in VERIFIED_BY edges)
- [x] No references in any `docs/roadmaps/*.md` (confirmed)
- [x] Historical `docs/aristotle_results/*/lean_aristotle/**/*.lean` not touched (archival snapshots)

**Rename applied:**
- `ChiralityWall.tpf_evasion_margin` → `tpf_evades_at_least_two` (matches statement `evaded_count ≥ 2`)
- `LatticeHamiltonian.tpf_evasion_margin` → `tpf_violation_surplus` (matches statement `card TPFViolation - 1 = 2`)

Both theorems retain their inline docstrings + added a Phase 5v Wave 1a provenance note referencing the other file.

**Verification:**
- [x] `cd lean && lake build` — clean (8397 jobs; only pre-existing simp-arg linter warnings)
- [x] `uv run python scripts/extract_lean_deps.py` — refreshed
- [x] `uv run python scripts/build_graph.py --json` — **zero ambiguity WARNINGs** (previously 1)
- [x] Both new short names resolve uniquely: `tpf_evades_at_least_two` → 1 node, `tpf_violation_surplus` → 1 node, `tpf_evasion_margin` → 0 nodes
- [x] `ARISTOTLE_THEOREMS['tpf_evades_at_least_two']` PROVED_BY `b1ea2eb7` edge resolves as `lean:SKEFTHawking.ChiralityWall.tpf_evades_at_least_two → aristotle:b1ea2eb7`
- [x] PROVED_BY edge count: 304 → 305 (the previously-skipped ambiguous edge now lands cleanly)
- [x] All 35 graph tests pass (`test_build_graph.py` + `test_graph_integrity.py`)

**Outcome.** Single remaining Wave 0 residual cleared. Graph is fully collision-free.

### Wave 1b — `counts.json` wiring [Pipeline: Stage 12] — DONE 2026-04-15

**Problem (corrected 2026-04-15 after direct inspection).**
`scripts/update_counts.py` exists and works correctly — it produces both
`docs/counts.json` and `docs/counts.tex` with 13 fields each (theorems,
modules, axioms, sorry, tests, figures, notebooks, papers, aristotle, etc.).
Current outputs are fresh and accurate (3,021 theorems / 133 modules / 322
Aristotle-proved).

The **actual gap** is downstream of the script:
1. `update_counts.py` is NOT wired into `validate.py` — no automated re-run
2. **Zero paper `.tex` files actually use `\input{docs/counts.tex}`** — Paper 15 mentions the pattern in prose but never consumes it
3. No `count_literals` check to enforce macro usage

**Fix:**
- [x] `validate.py` invokes `update_counts.py` via new CHECK 15b (`counts_fresh`); staleness-checked against `lean_deps.json`, `constants.py`, `visualizations.py`, and `SKEFTHawking/*.lean` mtimes
- [x] Extended `update_counts.py` with additional macros (`\sorrypercent`, `\leandefinitions`, `\aristotleruns`)
- [x] New `validate.py` CHECK 17 `count_literals`: WARN-level; catches `N theorems`, `N Lean modules`, `N sorry`, `N Aristotle-proved` patterns; exempts papers that `\input` `counts.tex` or use the macros
- [x] Paper 15 retrofitted with `\input{../../docs/counts.tex}` + 7 macro substitutions (abstract, intro bullets, invariant 9, Aristotle results, scaling section) — **serves as reference implementation**; 3 literals remain (`25 theorems` for a specific Aristotle run, `33 sorry` in outdated batch-plan context, `200 theorems` growth-rate heuristic); deferred pending Paper 15 full rewrite
- [ ] Paper 15 full rewrite — **deferred post-5v** (paper content is broadly stale; see `project_paper15_rewrite.md` in memory)
- [ ] Retrofit Papers 1–14 — **not blocking this wave**; CHECK 17 WARN surfaces remaining 64 literals; cleanup scheduled as a cross-cutting sweep after Wave 5

**Gate:** `validate.py --check counts_fresh` passes; `validate.py --check count_literals` runs and surfaces residual literals with paper-granular WARNs; Paper 15 macros resolve via `\input`.

### Wave 1c — Auto-discovery extractors (current-schema only) [Pipeline: Stages 1, 12] — DONE 2026-04-15

**Problem.** Graph has 9 Papers (of 15), 22 HAS_FIGURE edges, 76/101 figures surfacing, 0 tests, 0 production runs, 0 review findings. All because extractors are gated on hand-maintained Python dicts (`PAPER_DEPENDENCIES`, hand-coded `PAPER_FIGURE_MAP`, etc.).

**Done this wave (current-schema extractors — no new node types):**
- [x] `extract_paper_nodes` — auto-discovers every `papers/paper*_*/paper_draft.tex`; merges with `PAPER_DEPENDENCIES` metadata when available; papers without provenance entries get a minimal node (parses `\title{}`, flags `has_provenance_entry: false`). Graph Papers: **9 → 15**.
- [x] `extract_figure_nodes` — auto-discovers `fig_*` functions in `visualizations.py` not already covered by `FIGURE_REGISTRY.function` field (73 of 76 registered figures map to a fig_* function); remaining are surfaced with `registered: false`. Graph Figures: **76 → 104** (no dupes; +28 fs-discovered).
- [x] `extract_has_figure_edges` — parses `\includegraphics{...}` from each paper's `.tex`; matches against both raw name and `fig_`-prefixed variants. Graph HAS_FIGURE: **22 → 32**; logs count of unresolved references (12 currently — bare-name figures like `mtc_hierarchy`, `su3k_fusion` that bypass the `visualizations.py` canonical invariant — a real finding for the readiness system to track).

**Deferred to Wave 2 (require new node types not yet in schema):**
- [x] `extract_python_test_nodes` + `extract_verifies_edges` → PythonTest + VERIFIES (Wave 2c — DONE; 1831 tests; 515 bounds / 772 identity / 177 golden / 6 roundtrip / 361 unknown; 23 formulas are bounds-only — direct targets for ComputationCorrectness gate)
  - **Refinement (2026-04-15, post-UI-pass):** tightened `referenced_names` extraction to import-scope names only (walks ImportFrom/Import at module level; filters name references to those in the import set). Previously walked all AST `Name` nodes which swamped `_resolve_lean_short` with Python-local/Lean-projection coincidences (`cs`, `n`, `d`, `coeffs`, etc.). Also deduped ambiguity warnings to one WARNING per unique short name per build; repeats log at DEBUG. Result: 1126 → 680 VERIFIES edges (dropped low-signal matches); 30+ WARNING lines → 1 (the genuine `gs_conditions` collision between `ChiralityWall` and `ChiralityWallStatus`). Avg referenced_names per test: 2.4.
- [x] `extract_review_finding_nodes` + `extract_flags_edges` → ReviewFinding + FLAGS (Wave 2d — DONE; 56 findings extracted from 4 Perplexity review docs, 34 FLAGS→Paper edges inferred from body text; severity/status classification coarse — refinement deferred to Wave 6 when adversarial-reviewer emits structured output natively)
- [x] `extract_production_run_nodes` → ProductionRun (Wave 2e — DONE; 14 runs extracted; status heuristic from paired .log tail). PRODUCES edges deferred to Wave 4 where run-to-claim mapping is curated.
- [x] `extract_placeholder_marker_nodes` → PlaceholderMarker (Wave 2b — DONE)
- [x] `extract_prose_claim_nodes` → ProseClaim (Wave 2f — DONE; 113 abstract sentences across 15 papers, heuristic tags `first-claim` / `unification-claim` / `attribution-claim` / `feasibility-claim` / `simulation-evidence-claim`)
- [x] `extract_count_metric_nodes` + `extract_reports_edges` → CountMetric + REPORTS (Wave 2g — DONE; 14 canonical metrics; 9 stale REPORTS edges surface project-total claims in Papers 4/6/7/8/9 that drift from canonical)

**Deferred to a later sweep (not blocking):**
- [ ] Derive `skPrefix` in `ExtractDeps.lean` from `lakefile.toml` (currently hardcoded `` `SKEFTHawking``)
- [ ] Resolve the 12 bare-name paper figures — decide per figure whether to add viz.py function, move to orphan FigureFile node type, or document as external

**Gate for Wave 1c (done):** Graph shows 15 Papers, 104 Figures (all pipeline-discoverable), HAS_FIGURE auto-computed from paper `.tex`, all 35 existing tests pass.

---

## Wave 2 — Schema extension for readiness

### Wave 2a — Schema skeleton (node types + edge types) — DONE 2026-04-15

Registered 8 new node types in `SHAPE_MAP` and 8 new edge types in the
schema docs. All stub extractors return `[]`; nodes materialize as each
wiring wave lands (2b–2g, then 4).

| Node | Shape | Wired in | Purpose |
|---|---|---|---|
| **ProseClaim** | circle | Wave 2e | Narrative statements not tied to a Formula |
| **PythonTest** | square | Wave 2a+ | Test functions + test_kind ∈ {golden, bounds, identity, roundtrip} |
| **ReviewFinding** | triangle | Wave 2c / 6 | Adversarial review findings (internal + external) |
| **ProductionRun** | circle | Wave 2d | MC/RHMC run records + status |
| **PlaceholderMarker** | diamond | Wave 2b | Lean decls with trivial body on non-trivial statement |
| **Contradiction** | triangle | Wave 2f | Concrete cross-paper inconsistency instance |
| **CountMetric** | diamond | Wave 2g | counts.json snapshot at a point in time |
| **ReadinessGate** | square | Wave 4 | Per-paper × per-dimension state (11 gates × 15 papers) |

Verified: `SHAPE_MAP` has 22 types, graph emits 14 (the 8 new ones are
stubs), same totals as pre-Wave 2a (4086 nodes / 1468 edges), all 35
graph tests pass. `docs/KNOWLEDGE_GRAPH.md` schema table updated to
reflect 22 node types + 20 edge types (12 base + 8 readiness).

### Wave 2b — New edge types

| Edge | From → To | Attributes | Purpose |
|---|---|---|---|
| `VERIFIES` | PythonTest → Formula/Parameter/LeanTheorem | `test_kind` | Coverage + shape |
| `FLAGS` | ReviewFinding → any | `severity`, `status`, `fix_commit?` | Audit trail |
| `SUPERSEDES` | ReviewFinding → ReviewFinding | `resolved_by` | Later review closes/reopens earlier |
| `PRODUCES` | ProductionRun → Formula/PaperClaim | `data_path` | Run generated data this depends on |
| `REPORTS` | Paper → CountMetric | `paper_value`, `delta_pct` | Paper reports a count; compare vs canonical |
| **`SUPPORTS`** | artifact → artifact | `evidence` | Mutual reinforcement (dual of CONTRADICTS) |
| `CONTRADICTS` | artifact → artifact | `conflict_detail` | Cross-artifact inconsistency |
| `IMPACTED_BY` | ReadinessGate → any | — | Gate flips to `needs-recheck` if upstream changes |

### Wave 2c — Schema tests

- [ ] Extend `tests/test_build_graph.py` — every new node type has at least one assertion that it extracts correctly
- [ ] Extend `tests/test_graph_integrity.py` — new edge types participate in integrity checks where applicable (orphaned ReviewFindings, stale CountMetrics, bounds-only-test formulas)
- [ ] Update `docs/KNOWLEDGE_GRAPH.md` schema table to reflect 22 node types + 18 edge types

**Gate:** Graph export round-trips; all new types surface in dashboard graph-tab filter pills; test suite green.

---

## Wave 3 — Graph-as-source-of-truth migration (originally KG Phase 2)

**Trigger.** At current scale (~4,050 nodes, ~1,475 edges, projected ~5,500 nodes / ~3,500 edges post-Wave 1c), the full-graph-rebuild-per-request JSON approach is approaching the limit where sub-second dashboard responses matter for UX. PG+AGE with proper indexing serves Cypher-traversal queries in milliseconds even at 10× scale.

### Wave 3a — Source-of-truth flip

- [ ] Add a `graph_source_mode` env var with values `{json, pg}`; default `json` for backward compat
- [ ] When `pg`: dashboard `/api/graph*` endpoints query PG+AGE via Cypher; JSON extraction becomes a CI-time validator (build graph, diff against PG, fail on divergence)
- [ ] Python registries become derived: `src/core/generate_from_graph.py` regenerates `constants.py` Aristotle registry + `provenance.py` parameter provenance + `citations.py` + `visualizations.py` figure list from PG
- [ ] Add a write path: `write_to_graph(node_type, attrs)` inserts into PG + emits a migration to keep the Python dict consistent during the transition period
- [ ] Generated files carry `# GENERATED FROM GRAPH — DO NOT EDIT BY HAND` banner

**Append-only logs that also migrate to PG tables in Wave 3:**
- `docs/citation_verifications.jsonl` → `citation_verifications` table (primary key `(bibkey, bibitem_hash)`, most-recent-wins at query time). `scripts/citation_cache.py` swaps flat-file reads for `psycopg` queries; agent-facing API unchanged.
- `docs/QI_REGISTER.md` (Wave 7a) → `qi_items` table when that wave lands.
- `docs/validation/reports/validation_*.json` archives → optional `validation_runs` table for historical trend charts on the dashboard.

All three schemas are deliberately PG-shaped (ISO-8601 timestamps, scalar columns, composite PKs) so migration is mechanical when Wave 3 fires.

### Wave 3b — Migration & verification

- [ ] One-shot full migration: JSON → PG+AGE seed, comparison test to confirm byte-identical reads
- [ ] `validate.py` CHECK 17 (new): `graph_source_parity` — json-rebuild vs PG-read diff = 0
- [ ] Switch `graph_source_mode` default to `pg` in `dashboard`; keep `json` for scripts
- [ ] 30-day deprecation window where both paths remain; after Wave 4 lands, retire JSON path

### Wave 3c — Dashboard write-back

- [ ] "Mark gate reviewed" button → PG update via `/api/readiness/mark_reviewed`
- [ ] Human parameter verification → `PARAMETER_PROVENANCE.human_verified_date` persists to PG, regenerated `provenance.py` picks it up
- [ ] Review-finding status transitions (open → fixed → verified) persist to PG

**Gate:** Dashboard runs on `pg` mode by default; CHECK 17 passes; `constants.py`/`provenance.py` regeneration produces byte-identical output; write-back paths tested with at least one parameter verification and one gate transition.

---

## Wave 4 — Readiness state machine — DONE 2026-04-15

### Wave 4a — Gate extraction — DONE

For each Paper × each of 11 gate definitions, emit a `ReadinessGate` node with state `{open, in-review, passed, blocked, needs-recheck}` and aggregate evidence. 15 papers × 11 gates = 165 gate instances.

Gate evaluators (one Python function per gate):

```python
# scripts/readiness/gates.py
def evaluate_citation_integrity(paper_node) -> GateResult: ...
def evaluate_cross_paper_consistency(paper_node) -> GateResult: ...
def evaluate_parameter_provenance(paper_node) -> GateResult: ...
def evaluate_computation_correctness(paper_node) -> GateResult: ...
def evaluate_lean_proof_substance(paper_node) -> GateResult: ...
def evaluate_assumption_disclosure(paper_node) -> GateResult: ...
def evaluate_narrative_grounding(paper_node) -> GateResult: ...
def evaluate_production_run_health(paper_node) -> GateResult: ...
def evaluate_count_freshness(paper_node) -> GateResult: ...
def evaluate_first_claim_verification(paper_node) -> GateResult: ...
def evaluate_fix_propagation(paper_node) -> GateResult: ...
```

Each returns `{state, evidence: [node_ids], blockers: [finding_ids], owner, last_evaluated}`.

**Live snapshot (initial 165-gate run, 2026-04-15):**
- 165 ReadinessGate nodes across 15 papers × 11 gates
- State distribution: 90 passed / 37 blocked / 30 needs-recheck / 8 open
- Paper state: **15/15 RED** (all papers have ≥1 P1 blocked — as expected given April adversarial-review-not-yet-remediated state)
- Gate blocker patterns:
  - CitationIntegrity: ~14 papers (bibkey registry coverage — registry has 44 entries but many papers cite keys not in it)
  - NarrativeGrounding: 8 papers ("interesting" prose claims without SUPPORTS edges)
  - ComputationCorrectness: 6 papers (formulas with no tests or bounds-only tests)
  - ParameterProvenance: 4 papers (parameters without `human_verified_date`)
  - ProductionRunHealth: Paper 6 (MC claim without successful run — the exact April finding)
  - LeanProofSubstance: Paper 9 (cites a placeholder theorem)

Paper 6 gate output exemplifies the whole point — automatic surfacing of the April MC failure:

```
  ❌ P1 NarrativeGrounding  blocked  "Monte Carlo evidence" claim lacks SUPPORTS edge
  ❌ P1 ProductionRunHealth blocked  paper prose claims MC evidence but no successful ProductionRun linked
  ⚠️  P1 CrossPaperConsistency needs-recheck  3 inter-paper count disagreements
```

### Wave 4b — Auto-invalidation — DEFERRED

Explicit `IMPACTED_BY` edges + hash-diff propagation are **deferred** because the whole-graph rebuild is currently fast enough (~10s) that every `build_graph.py` run re-evaluates all gates from fresh state. Auto-invalidation happens implicitly: change any input, rebuild, all dependent gates flip visibly. Re-enable IMPACTED_BY in Wave 3 (PG SoT) when incremental re-evaluation becomes the performance-limiting concern.

### Wave 4c — CHECK 18 readiness_submission_gate — DONE

- [x] `scripts/validate.py` registers `readiness_submission_gate` check
- [x] Aggregates 165 ReadinessGate nodes into per-paper state (green / yellow / red)
- [x] Red = any P1/P2 gate blocked; yellow = all P1 passed but ≥1 P2 advisory; green = all 11 gates passed
- [x] WARN-only during rollout (expected to flag all 15 papers red until remediation) — escalate to FAIL when papers start hitting green

**Gate for Wave 4 (met):** 165 gate instances evaluate on every `build_graph.py` run; gate blockers surface as structured blockers lists per GateResult; CHECK 18 summary shows `0 green / 0 yellow / 15 red` snapshot at wave-completion; all 35 graph tests pass.

---

## Wave 5 — Dashboard readiness surface — PARTIAL DONE 2026-04-15

### Wave 5a — Readiness tab — DONE (with UI enhancement pass)

- [x] Added "Paper Readiness" as 7th tab alongside existing 6
- [x] Heatmap: rows = 15 papers, columns = 11 gates (compact gate abbreviations in rotated headers), cells colored green/red/yellow/grey by gate state
- [x] **Paper-focus sidebar** (UI enhancement pass): click paper name or any gate cell → sticky right-side panel shows all 11 gates for that paper with evidence/blockers expanded for the selected gate and auto-expanded for any non-passed gates. Replaces the inline per-cell detail panel.
- [x] **Filter row** (UI enhancement pass): buttons for red/yellow/green paper-state filter + dropdown for "blocked by gate X" + click any gate header in the heatmap to toggle the gate filter. "Clear filters" button resets.
- [x] Legend + priority labels (P1 / P2) under every gate header
- [x] Summary row: green/yellow/red counts, paper total, last-evaluated timestamp
- [x] `/api/readiness` Flask endpoint returns structured gate data; dashboard renders via safe-DOM construction (no innerHTML with untrusted content — verified by security hook)
- [x] Headless render tests: GET `/?tab=readiness` returns 200; GET `/api/readiness` returns 200 with 15 papers × 11 gates
- [ ] Trend chart: gates-passed over time — **deferred** (requires historical snapshots in `docs/validation/reports/`; can wire once that archive is populated)

### Wave 5b — Graph-tab integration — DEFERRED

Deferred to a follow-up session. Scope when revisited:
- 3rd traversal mode "Readiness" in graph tab
- ReviewFinding node shape/color
- SUPPORTS/CONTRADICTS green/red dashed edges (once SUPPORTS/CONTRADICTS edges are emitted)
- Per-paper mini-pill summary in Paper Focus dropdown

### Wave 5c — Action buttons — DEFERRED

Depends on Wave 3 (PG SoT write-back). Scope:
- "Mark reviewed" button → gate state transition persisted to PG
- "Accept with note" for P2 gates
- "Trigger adversarial review" → manual Stage 13 invocation

**Gate for Wave 5a (met):** Dashboard tab live at `localhost:8050/?tab=readiness`; 15 papers × 11 gates visible; click-through detail works; API endpoint tested clean.

---

## Wave 6 — Stage 13: Internal adversarial review — PARTIAL DONE 2026-04-15

### Wave 6a — Agent definition — DONE

New physics-qa plugin agent:

- **Location:** `.claude/plugins/physics-qa/agents/adversarial-reviewer.md`
- **Model:** `claude-opus-4-6` (latest Opus, fresh context window — no prior session state)
- **Tools:** Read, Grep, Glob, Bash (for `curl` DOI resolution), WebFetch (for arXiv title verification)
- **Color:** red (adversarial distinct from yellow claims-reviewer + cyan figure-reviewer)

**System prompt (sketch):**
> You are an adversarial reviewer for the SK-EFT Hawking project. Your job is to find every way a paper can be wrong that the internal pipeline missed. You are NOT authoring; you are NOT defending. You are looking for:
> - Citations that resolve to the wrong paper (fetch the arXiv ID, verify title + authors match)
> - Numerical values that drift from their primary source (fetch the source, compare)
> - Lean theorems cited as "verified" whose body is `rfl` / `Equiv.refl` / `decide` on a non-trivial statement
> - Cross-paper contradictions (Paper A says X, Paper B says not-X, same construct)
> - Narrative claims without formal support ("all the same X", "rooted in Y", etc.)
> - Count literals that don't match current `counts.json`
>
> For each finding, emit a JSON ReviewFinding with `severity`, `gate_affected`, `evidence_path`, and `fix_suggestion`.

### Wave 6b — Pipeline integration — DONE

- [x] Stage 13 added to `docs/WAVE_EXECUTION_PIPELINE.md`: purpose, actions, rules, gate, non-use cases. References `docs/READINESS_GATES.md` as the canonical gate source.
- [x] Stage 14 (Meta-process QI) added alongside Stage 13, marked advisory.
- [x] Output of Stage 13 already flows through `extract_review_finding_nodes` → ReviewFinding nodes → FLAGS edges → FixPropagation gate (wired in Wave 2d). Output path convention updated to `{YYYY-MM-DD-HHMM}-internal-adversarial/`.
- [x] Loopback rule documented: BLOCKER severity reopens the affected ReadinessGate; paper cannot advance until re-invocation shows no new BLOCKERs.
- [x] Citation-severity elevation: every citation finding is BLOCKER at submission time (per-user feedback, non-negotiable).

### Wave 6c — Triggering — COVERED (docs)

On-demand invocation is the primary trigger path: users run `"Run the adversarial-reviewer on paper<N>_<name>"` in Claude Code. This is documented in the agent file + Stage 13 pipeline section.

Remaining items deferred:
- [ ] Dashboard "Trigger adversarial review" button — depends on Wave 5c (which depends on Wave 3 write-back)
- [ ] Scheduled pre-submit gate: CHECK 18 extended to require a Stage-13 pass within last 7 days against current paper content hash — can land whenever
- [ ] Cron sweep via the existing `schedule` skill — optional; defer until submission cadence justifies it

**Gate for Wave 6 (met):** Agent definition installed and debiased; READINESS_GATES.md exists as canonical source; Stage 13 + 14 documented in pipeline; citation cache + HHMM output format in place. Next: first real-world invocation on a draft paper (test rather than roadmap deliverable).

---

## Wave 7 — Stage 14: Meta-process Quality Improvement register — PARTIAL DONE 2026-04-15

**Distinction from Stage 13.** Stage 13 catches paper-level issues. Stage 14 catches **process-level** issues — recurring patterns across multiple papers or review rounds that indicate a pipeline gap (e.g., "bounds-only tests allowed a 10⁷× bug through", "fix-propagation lag across companion papers"). Stage 14 feeds improvements back into the pipeline itself.

### Wave 7a — QI register — DONE

- [x] `docs/QI_REGISTER.md` — auto-generated via `scripts/qi_register.py` from current ReviewFinding graph nodes
- [x] Each QI item carries: `id`, `pattern_summary`, `gate_affected`, `occurrences`, `affected_papers`, `severity_mix`, `first_observed`, `last_observed`, `status`, `owner`, `target_date`, `evidence_on_close`, `representative_findings`
- [x] Classification: finding → readiness gate via keyword-pattern lookup; gate clusters emerge from findings touching the same gate across ≥2 papers
- [x] `--snapshot` flag emits timestamped `docs/QI_REGISTER_{date}.md`
- [x] Seeded from the April review round: 56 findings → 7 QI items. Biggest cluster: CitationIntegrity with 20 findings across 7 papers (confirms the April citation-handling pattern as a systemic issue warranting remediation, not a one-off)
- [ ] Manual-field persistence across regenerations (owner, target_date, etc. preserved on re-run) — deferred to follow-up refinement

### Wave 7b — Dashboard "Process Health" tab — DONE

- [x] Added "Process Health" as 8th dashboard tab
- [x] `/api/qi` endpoint: runs `qi_register.cluster_findings` against current ReviewFinding nodes; returns items with severity mix, affected papers, occurrence counts, representative findings
- [x] Tab renders QI items as severity-color-bordered cards (critical/major/minor/advisory)
- [x] Each card shows: gate pill, occurrence count, status, first/last seen, affected-paper chips, representative findings list
- [x] Toolbar: "open only" / "all" filter
- [x] Safe-DOM construction (createElement + textContent throughout)
- [x] Verified: GET /?tab=qi returns 200; /api/qi returns 7 items from 56 findings
- [ ] Trend chart: findings-per-gate-per-month — **deferred** (same blocker as readiness trend: needs historical snapshots)
- [ ] FixPropagation gate reading QI register for past target_dates — **deferred** (requires persistent manual-field state on QI items, not yet wired)

### Wave 7c — Pipeline integration — DONE

- [x] Stage 14 documented in `docs/WAVE_EXECUTION_PIPELINE.md` (Wave 6b commit)
- [x] Stage 14 is advisory; user-facing report emitted on run
- [ ] Loopback escalation of `severity=critical` QI items to remediation waves — recommended via Phase 5w roadmap when warranted

**Gate for Wave 7 (met):** `docs/QI_REGISTER.md` exists, auto-regenerates from current ReviewFindings, captures the April round as 7 distinct process-level patterns. Pipeline Stage 14 documented; run with `uv run python scripts/qi_register.py`.

---

## Wave 8 — External API surface (originally KG Phase 3 residue)

### Wave 8a — JSON-LD / W3C PROV export

- [ ] `scripts/export_jsonld.py` — emit graph as [W3C PROV-JSON](https://www.w3.org/TR/prov-json/) with SK-EFT-specific ontology
- [ ] Map: Paper → `prov:Entity`, LeanTheorem → `prov:Entity`, AristotleRun → `prov:Activity`, PROVED_BY → `prov:wasGeneratedBy`, etc.
- [ ] Deliverable: `papers/provenance_bundle.jsonld` — suitable for arXiv ancillary file, OpenAIRE, Zenodo
- [ ] CI job: regenerate on every graph change; commit if diff > trivial

### Wave 8b — Notebook helper

- [ ] `src/core/graph.py` — `trace_claim(paper, claim_index) -> ProvenanceChain`
- [ ] Returns structured object: `{formula, lean_theorem, aristotle_run, parameters[], sources[], figures[], gates_status}`
- [ ] Notebook usage:
  ```python
  from src.core.graph import trace_claim
  chain = trace_claim('paper1', claim_index=3)
  chain.render_markdown()  # inserts provenance table into notebook cell
  ```
- [ ] Used in stakeholder notebooks as the pedagogical provenance exposition tool

**Gate:** JSON-LD export validates against PROV-JSON schema; notebook helper surfaces correct chain for at least 3 test claims across 3 papers; imported cleanly from `Phase1_Technical.ipynb`.

---

## Wave 9 — Dashboard remediation + Proof-Chain-Viz [session 2026-04-24]

**Trigger.** After Waves 1-8 lands, the KG dashboard is usable in principle but not in practice:
1. Every `/api/graph*` endpoint called `build_graph_json()` from scratch — ~15s per request in the steady state, ~1-2min on a stale `lean_deps.json` because the handler shelled out to `lake env lean --run ExtractDeps.lean` synchronously. Paper Focus and Logical Focus chained multiple 15s rebuilds per click. `build_graph_json()` also wrote to PG+AGE inline on every call, doubling effective cost when Postgres was up and silently warning-but-still-slow when it was down.
2. Filter pills used `flex-wrap: wrap` inside a fixed-height (48px) absolutely-positioned topbar with `z-index: 100`. When ≥10 node types were present, pills floated upward past the topbar into the outer dashboard's title + tab bar — making the whole tab-nav unusable.
3. `"Formulas (200)"` filter-pill labels read as pagination, not as a total count.
4. Lean graph has 2820 LeanTheorem nodes but only 305 PROVED_BY + 493 USED_BY + 4 DEPENDS_ON_AXIOM edges — no proof-to-proof dependency edges because `ExtractDeps.lean` emits only *axiom* closures (`axiom_deps_project/_core`), not full `name_deps`.
5. The Proof-Chain-Viz design (`Lit-Search/Phase-5v/Designs/Proof-Chein-Viz-Dashboard`) needs wiring — registry fields (`chain_id`, `is_milestone`), three endpoints (`/api/chain/{id}/summary|milestones|subgraph`), and a dashboard tab with L0/L1/L2 zoom levels.

### Wave 9a — Dashboard perf + UX (Phase 1) — DONE 2026-04-24

**A1+A3 — In-memory graph cache:** Added `get_cached_graph()` in `scripts/provenance_dashboard.py` with an mtime-based fingerprint across `lean_deps.json`, core Python registries, paper `.tex` files, all `SKEFTHawking/*.lean`, `build_graph.py`, `readiness_gates.py`, and `counts.json`. Cache invalidates lazily on next request after any input changes. **Measured: cold build 1.47s → cached hit ~0.9ms (≈ 1600× speedup).** `/api/graph`, `/api/graph/trace`, `/api/graph/impact`, `/api/readiness` all now served from the cache. Added `/api/graph/rebuild` (POST/GET) for manual invalidation when stat() can't see a change (e.g., docstring edit without mtime bump on the watched set).

**A2 — PG+AGE write decoupled:** `build_graph.build_graph_json()` now takes `sync_pg: bool = False`. Dashboard schedules PG sync on a debounced background thread (`_schedule_pg_sync`, one writer at a time, coalesces if a newer fingerprint arrives while a write is in flight). HTTP responses never block on DB connectivity. `--no-pg-sync` CLI flag added to the dashboard for local dev without Postgres. The bare `lake build --json` path is unchanged (tests still pass).

**A3 — Trace/impact indexes rebuilt per request:** `api_trace` and `api_impact` previously scanned the full edge list inside each recursion step — O(E × V) worst case. Now build outgoing/incoming adjacency indexes once per request (O(E)) then walk iteratively. **Measured: `/api/graph/trace` and `/api/graph/impact` both respond in 1-2ms on 8.3K-node graph** (vs. ≥15s before).

**A5 — Topbar overflow fix:** Split `.kg-topbar` into two rows (`primary` + `secondary`), each scrolls horizontally with `overflow-x: auto` + `flex-wrap: nowrap`. Filter pills moved to the secondary row. Added `--kg-topbar-h` CSS variable synced to real topbar height via `ResizeObserver`; `.kg-graph-container { top: var(--kg-topbar-h) }` follows. Capped topbar at `max-height: 45vh` as a safety rail. **Effect: pills can never overflow upward into the outer dashboard chrome.**

**A6 — Filter-pill label clarity:** `"Formulas (200)"` pattern replaced with a two-span layout: bold type name + muted trailing tabular-numeric badge (`"Formulas 200"` visually). Pluralised the name so the count reads as a total (`Parameter` ↔ `Parameters`). Added tooltip: `"200 Formulas in current graph — click to toggle"`. Inner KG filter pills only; outer dashboard tabs (`Formulas (47)`, etc.) left unchanged — those are navigation-count labels, not filter toggles.

**A-prewarm — Cache warmup on server start:** Dashboard `--no-prewarm` flag optional; by default spawns a daemon thread on startup that pays the first `get_cached_graph()` cost so the first user request is fast (or, if `lean_deps.json` is stale, the prewarm eats the `lake` extraction time while the server accepts connections — the first `/api/graph` request blocks on cache lock rather than repeating the work).

**Shipped files:** `scripts/build_graph.py` (sync_pg kwarg), `scripts/provenance_dashboard.py` (cache layer, four endpoints, CLI flags), `scripts/templates/partials/graph_tab.html` (two-row topbar, ResizeObserver, pill renderer). `tests/test_build_graph.py` passes unchanged.

### Wave 9b — Filter composition + search (Phase 2) — DONE 2026-04-24

- [x] A7: Paper focus, logical focus, type-pill filter, search, and core-axiom toggle AND-compose via a single `filterState` object. Dropdowns no longer silently clear each other. Verified via Playwright: search "graphene" (20 matches) ∩ Paper Focus paper16 = 2 visible nodes.
- [x] Free-text search box with 120ms debounce; matches label + short-id only (stripping `SKEFTHawking.` prefix so the project name doesn't match everything).
- [x] "Clear filters" button appears when any filter is active; resets search, paper focus, logical focus, and type pills to defaults.
- [x] Live `<visible>/<total>` stat in the topbar stats strip.
- [ ] A9 chain-filter pills — blocked on Wave 9d populating `chain_id` on nodes; will land with the chain viz work.

### Wave 9c — name_deps edges + PG+AGE source-of-truth (Phase 3) — IN PROGRESS 2026-04-24

**Scope refined per user 2026-04-24: emit `name_deps` but gate behind env var so default JSON stays the same size. Dashboard fetches proof-dep edges on demand via new endpoint. Full PG source-of-truth flip stays in later sub-wave.**

Shipped this session:
- [x] `ExtractDeps.lean` extended with `collectProjectNameDeps` (uses `Expr.getUsedConstantsAsSet`, filtered to in-package refs only). New per-decl field `name_deps_project` added to JSON output. Axioms/opaques/structures get empty list (no value to introspect).
- [x] `scripts/build_graph.py::extract_uses_edges` — converts `name_deps_project` to `USES` edges between Lean declaration nodes. Gated by env var `SK_EFT_INCLUDE_USES=1`; returns `[]` otherwise so the default `/api/graph` payload keeps its current ~5 MB size.
- [x] Dashboard endpoint `/api/graph/uses_edges` — flips the env var transiently and rebuilds only the USES subset; caches the result separately keyed to the same fingerprint as the main graph. Returns a `hint` string if `lean_deps.json` predates the Wave 9c upgrade so the UI can prompt the user to re-extract.
- [x] Dashboard toggle "Proof Deps" in the secondary row. Fetches USES edges on first activation, merges into the D3 link array (without rebuilding nodes), re-runs applyFilters. Toggling off just removes them — no re-fetch. Shows a loading state ("Proof Deps…") during the initial fetch.
- [x] Tests still pass (`tests/test_build_graph.py`, `tests/test_graph_integrity.py`).

Pending (deferred to a follow-up sub-wave; no blocker for current UX value):
- [ ] `scripts/sync_graph_to_pg.py` — standalone, idempotent PG+AGE sync script with `USES` edges written as AGE relationships. Runs on demand or via cron; the dashboard doesn't invoke it.
- [ ] `/api/graph/cypher` endpoint (read-only) — execute parameterised Cypher against AGE for bounded subgraph lookups. Falls back to in-memory traversal when AGE unavailable.
- [ ] Env var `SK_EFT_GRAPH_SOURCE={json,pg}`; `validate.py --check graph_source_parity` comparing JSON-rebuild vs PG-read.
- [ ] Retire the full-graph-per-request JSON path in favor of PG-served subgraphs keyed on paper/chain/focus when at 10× current node count.
- [ ] **Open for next Lean-heavy session:** `ExtractDeps.lean` with `name_deps_project` takes >5 min to complete (vs. ~60s originally) — `Expr.getUsedConstantsAsSet` on elaborated tactic-generated proof terms is the bottleneck. Worth optimising by scanning the type signature + `syntax` value (before elaboration) instead of the fully-unfolded proof, or by caching per-module and extracting incrementally. Until then, users run the extractor manually and accept the wait.

### Wave 9d — Proof-Chain-Viz (dynamic chain discovery) — DONE 2026-04-24

**Dynamic taxonomy per user 2026-04-24**: adding a new module entry to `MODULE_CHAIN_MAP` creates a new chain in the dashboard with no other registry plumbing. The chain list is derived from the set of `chain_id` values actually present on nodes — no hardcoded enum.

Shipped this session:
- [x] `src/core/constants.py::MODULE_CHAIN_MAP` — 98 modules mapped into 9 chains: `hawking`, `graphene` (dual with hawking), `generations`, `gauge-emergence`, `chirality-wall`, `fracton`, `vestigial`, `dark-sector`, `gate-engineering`. Modules legitimately belonging to multiple chains use a list value (e.g. `DiracFluidMetric` → `['hawking', 'graphene']`).
- [x] `src/core/constants.py::CHAIN_MILESTONES` — 32 milestone short names registered with per-chain order hints. Every `LeanAxiom` is implicitly a milestone (trust-boundary clarity per SUBGRAPH_CONTRACT §2).
- [x] `scripts/build_graph.py::extract_lean_declaration_nodes` now stamps every Lean node with `meta.chain_ids: list[str]`, `meta.is_milestone: bool`, `meta.milestone_order: int | None`.
- [x] Three endpoints per the design contract:
  - `GET /api/chain/list` — enumerates chain_ids with per-chain node counts + count of unclassified Lean decls
  - `GET /api/chain/{id}/summary` — L0 verdict strip (counts by kind + verdict heuristic + milestone count)
  - `GET /api/chain/{id}/milestones` — L1 milestone DAG with `hop_count` computed via bounded BFS (depth ≤ 5) through non-milestone intermediates
  - `GET /api/chain/{id}/subgraph` — L2 full chain subgraph + 1-hop externals (same shape as /api/graph)
- [x] `scripts/templates/partials/chains_tab.html` — new 9th tab "Research Status" with:
  - L0 verdict strip per chain (colored dot + title + counts + verdict badge + expand chevron)
  - L1 milestone DAG via deterministic topo-layered layout (`layoutDAG()` — no force sim; figures must be reproducible)
  - L2 deep-link to KG tab filtered by `#chain=<id>` (pending KG-side filter handling)
  - Safe-DOM construction throughout (no innerHTML with untrusted content — blocked by security hook)
- [x] Live screenshot verification via Playwright — all 9 chains render with correct per-chain counts; drill-down to milestone DAG works.

Live numbers (cached build, 2026-04-24):
```
chain                 node count
─────────────────────────────────
gauge-emergence         1,095
hawking                   487
chirality-wall            458
vestigial                 262
dark-sector               211
fracton                   204
generations               195
gate-engineering          171
graphene                   39
─────────────────────────────────
unclassified Lean        1,794
```

The 1,794 unclassified Lean decls are mostly pipeline machinery (SK axioms, helper scaffolding) not yet mapped — adding module names to MODULE_CHAIN_MAP auto-absorbs them into chains on next graph rebuild. No code change required.

Follow-ups (tracked in working docs, not blocking):
- [ ] Register real Lean short names in `CHAIN_MILESTONES` — my initial set was speculative; only ~11 of 32 match live decls. Cross-reference against `SK_EFT_Hawking_Inventory.md` key results per module.
- [ ] KG tab picks up `#chain=<id>` hash → applies chain filter to current view.
- [ ] Editorial overlay YAML (`docs/chain_overlays.yaml`) for per-chain prose (verdict text, implication, sidenotes) — L0 strip renders prose from overlay, figures + numbers from graph.
- [ ] Improve `_chain_summary` verdict heuristic (currently flags gauge-emergence as "structural known gaps" on a placeholder-string match that triggers too eagerly).

### Wave 9e — Lean extraction perf fix (Phase 3b) — DONE 2026-04-24

**Corrected baseline:** The original "extraction takes 60s" estimate was stale — by 2026-04-24 the SK-EFT codebase had grown to 7,655 decls across 158 Lean modules and baseline `lake env lean --run ExtractDeps.lean` is ~7 minutes regardless of name_deps work. The 9c-introduced `collectProjectNameDeps` added another ~1–3 min of Expr traversal on top, bringing total to ~10 min. No rewrite of `getUsedConstantsAsSet` can compress the aggregate cost below O(total-expr-size).

**Solution shipped:**
- [x] `collectProjectNameDeps` rewritten to use `for n in used do` iterator (no `.toList` materialisation) + `IO.monoMsNow` per-decl 250ms time budget; slow decls emit empty `name_deps_project` + `name_deps_timed_out: true` flag.
- [x] Slow-decl list written to `lean/lean_name_deps_slow.json` (regression signal).
- [x] **Feature gated behind `EXTRACT_NAME_DEPS` env var.** Default = OFF → extraction matches pre-9c baseline (~7 min). Set `EXTRACT_NAME_DEPS=1` to opt into full proof-dep extraction (adds ~3–5 min).
- [x] Fixed Lean 4.29 `String.trim` deprecation (→ `String.trimAscii`) which was polluting stdout with a warning and breaking JSON parsing.
- [x] `scripts/extract_lean_deps.py` hardened: strips any non-JSON prefix from stdout before parsing; surfaces `[name_deps]` status lines from stderr via logger.
- [x] Each decl's JSON output carries `name_deps_extracted` (bool) so consumers can distinguish "extraction was disabled" from "extraction ran and found nothing".

**Verified (2026-04-24 15:19):** fast-path run completes in 7:05.78, exit 0, 4.3 MB output, 7,655 decls, `name_deps_extracted: false` on all. Tests 51/51 pass against the regenerated `lean_deps.json`.

**Known follow-up (not blocking):** a full `EXTRACT_NAME_DEPS=1` run on the current codebase likely takes ~10–12 min. Acceptable as a "once per Lean source change" cost; dashboard never triggers it automatically (Wave 9a's `_suppress_lake_refresh` guard).

### Wave 9f — PG+AGE source-of-truth flip (Phase 3a) — DONE 2026-04-24

Also flagged "this sounds bad" on 2026-04-24 — I undersold the cost/benefit in the earlier deferral. The in-memory cache is fine for one-user UX, but:
- PG+AGE enables real Cypher subgraph queries on demand (no more full-graph reload to answer "who uses this theorem?")
- Durable state across dashboard restarts — nothing rebuilds on cold start
- `USES` edges live in AGE, not in the JSON artifact — size stays flat as more edges land
- Multi-process readers without serialising through the HTTP cache

**Shipped 2026-04-24:**
- [x] `scripts/sync_graph_to_pg.py` — standalone idempotent sync script. Builds graph via `build_graph_json(sync_pg=False)`, writes nodes + all edges to AGE `sk_eft` graph. Flags `--dry-run` (build + summary, no PG write) and `--pretty` (per-type breakdown). Respects `SK_EFT_INCLUDE_USES=1` for proof-dep edges. **Verified: 8,518 nodes + 2,661 edges written in 13.6s; verification query confirms counts match.**
- [x] `POST /api/graph/cypher` endpoint — read-only Cypher against AGE. Guards: write-clause regex (CREATE/DELETE/MERGE/SET/REMOVE/DROP/DETACH/CALL db.) → 400; 4000-char query cap; 5s connect timeout. Returns `{rows, count, ms, query}`. **Verified via curl: LeanTheorem count = 2938 in 18ms; write blocked correctly; data queries return real names in 13ms.**
- [x] Env var `SK_EFT_GRAPH_SOURCE={json,pg}` — `json` (default) = in-memory cache; `pg` routes future subgraph endpoints to Cypher.
- [x] Startup validation: if `SK_EFT_GRAPH_SOURCE=pg`, dashboard checks AGE connectivity via a `MATCH (n) RETURN count(n)` probe before accepting any HTTP requests; exits with `[PG] connectivity check FAILED` + setup hint if unreachable. **Verified: clean startup with 8,518 nodes reported.**

**Deferred (not blocking — follow-up):**
- [ ] Wire `SK_EFT_GRAPH_SOURCE=pg` to route `/api/graph/trace`, `/api/graph/impact`, `/api/chain/*/subgraph` to Cypher queries instead of the in-memory cache. Currently in-memory path is fast enough (~1–2 ms per request) that this is cosmetic; gain becomes real once USES edges (1000s more per theorem) land in PG and the in-memory full-graph response grows. Make this sub-wave before Wave 9g's `USES` populated scenarios.
- [ ] `scripts/validate.py --check graph_source_parity` — rebuild in json mode, query PG via /api/graph/cypher, assert node/edge count identity + per-type breakdown identical.

**Gate (met for Wave 9f core):** sync script + cypher endpoint + env var + startup check all functional and verified end-to-end.

### Wave 9d — Proof-Chain-Viz wiring (Phase 4) — DONE 2026-04-24

See "Wave 9d — Proof-Chain-Viz (dynamic chain discovery) — DONE 2026-04-24" section above (immediately after Wave 9c) for the full shipped list. Summary: 9 chains auto-discovered from `MODULE_CHAIN_MAP`, 4 endpoints (`/api/chain/{list,summary,milestones,subgraph}`), new dashboard tab, verified live via Playwright.

Follow-ups are listed in the Wave 9d shipped section — not blocking for Wave 9 as a whole.

### Wave 9g — Paper Provenance (v2 design) — PENDING 2026-04-24

**Trigger.** User added `Lit-Search/Phase-5v/Designs/Proof-Chein-Viz-Dashboard-v2/` on 2026-04-24 with a new Paper Provenance feature: per-paper split view showing the paper body with per-claim dossiers across 8 vetting layers. The v2 design is additive to v1 (chain viz unchanged); subgraph contract is identical to v1.

**Ship target (user direction 2026-04-24):** live interactive dashboard tab alongside the other 9 tabs. **Not** a side artifact, standalone HTML file, exported report, or anything the user has to open separately. Same app, same Flask server, same click-through navigation as Knowledge Graph / Paper Readiness / Research Status. The design folder's static HTML is a *mockup* — the shipped feature is a tab in `scripts/templates/dashboard.html` with dynamic data from backend endpoints.

**Design summary** (from direct read of `Paper Provenance.html`, `paper-provenance.js`, `paper-review.js`):
- Split view: left = paper body with inline `<span class="claim" data-claim="id">` anchors; right = dossier with per-claim findings matrix.
- Top banner: meter (PASS/WARN/FAIL/INFO counts), verdict pill, layer filter chips with nav counter.
- 8 vetting layers: NUM · THM · AX · HYP · CIT · PAR · FIG · QUA (see paper-review.js for exact emitting code paths).
- 49-claim mock for `paper12_polariton` with 2 FAIL / 12 WARN / 35 PASS / 4 INFO.
- Keyboard nav: ← → cycle, F/W jump to next FAIL/WARN, Esc clears filter then deselects.
- In-memory "mark vetted" toggle (not persisted in the mock — production must POST to an endpoint).

**Codebase-side audit** (from agent + direct reads; the mapping below is the key planning artifact):

| Layer | Existing data source | Gap |
|---|---|---|
| NUM | `papers/paper*/claims_review.json[layer_1_numerical_claims]` (emitted by `physics-qa:claims-reviewer` agent) + `formulas.py` for recompute | None if claims_review exists; fallback recompute otherwise |
| THM | `lean_deps.json` (name, kind, axiom_deps_project, name_deps_project post-Wave-9e) + `ARISTOTLE_THEOREMS` + `PAPER_DEPENDENCIES[paper].lean_modules` | None |
| AX | `AXIOM_METADATA` + `axiom_deps_project` on each theorem | None |
| HYP | `HYPOTHESIS_REGISTRY` with `dependent_theorems[]` field | None |
| CIT | `CITATION_REGISTRY` + `claims_review.json[citation_integrity]` + `\bibitem` + `\cite` scan of paper `.tex` | None |
| PAR | `PARAMETER_PROVENANCE` (`llm_verified_date`, `human_verified_date`, `tier`) + `claims_review.json[parameter_provenance]` | None |
| FIG | `papers/paper*/figures/figure_review_report.json` (emitted by `physics-qa:figure-reviewer`) | Only 2 papers have this — most need agent runs |
| QUA | `claims_review.json[qualitative_claims]` (hand-authored in that file) | Same limitation — depends on claims-reviewer run |

**The two non-trivial gaps** are:
1. **Paper body as HTML with claim-span anchors.** No `.tex → HTML` step exists. Current: `pdflatex` only. Need a new `scripts/render_paper_html.py` that runs pandoc and post-processes output to wrap claim spans based on a manifest. Two options for the manifest:
   - **(A) `\claim{id}{body-text}` LaTeX macro**: author the claim IDs directly in the `.tex` source; pandoc carries them as `<span class="claim" id="...">` with zero post-processing. Requires editing every paper's `.tex` once, but the source-of-truth stays in one place.
   - **(B) Side-file manifest `papers/<paper>/claim_manifest.json`** mapping `{claim_id: text_snippet}`; render-HTML step regex-matches snippets and wraps spans. Zero `.tex` edits, but fragile to prose edits.
   - **Recommended: option A** — editorial authoring of claim spans is load-bearing, don't want this fragile.
2. **Adversarial-reviewer output is Markdown, not JSON.** Findings currently live in `papers/AutomatedReviews/*/paper{N}.md` with YAML frontmatter + heading-structured sections. Parsing to `findings[]` requires regex. Either (a) update the agent prompt to also emit a sibling `.json` alongside the `.md`, or (b) add a parser. (a) is cleaner.

**Plan:**
- [ ] 9g-1: Agent prompt update — `physics-qa:adversarial-reviewer` additionally emits `findings.json` alongside `paper{N}.md`. Schema: `{gate, severity, location, observed, expected, fix, evidence?}`.
- [ ] 9g-2: `scripts/render_paper_html.py` — pandoc `.tex` → HTML, post-process to strip LaTeX artifacts; add `\claim{id}{body}` macro registration in paper TeX preamble (`docs/tex-macros/claim.sty`) so pandoc emits stable spans. Output: `papers/<paper>/paper_rendered.html`.
- [ ] 9g-3: Per-paper `claims_manifest.json` or inline `\claim{...}` — retrofit Paper 12 polariton first as the design's reference case (49 claims to author IDs for).
- [ ] 9g-4: Backend endpoint `GET /api/papers/<paper_id>/provenance` — synthesises 8-layer verdict by joining `claims_review.json` + `figure_review_report.json` + registries + adversarial findings. Returns the exact JSON shape `paper-review.js` consumes (`REVIEW_META` + `CLAIMS` keyed by claim_id + `LAYERS` definition).
- [ ] 9g-5: Backend endpoint `GET /api/papers/<paper_id>/rendered_html` — serves the pandoc-produced HTML (strips head/body wrappers; returns `<article>…</article>`).
- [ ] 9g-6: Optional `POST /api/papers/<paper_id>/claims/<claim_id>/vet` — persist the "mark vetted" action. Writes to `papers/<paper>/human_vetted.json` or a new PG table (matches Wave 9f flip decision).
- [ ] 9g-7: New **interactive tab** `scripts/templates/partials/paper_provenance_tab.html` — live, not a static artifact. Ports the design's split view. Paper selector dropdown lists all 18 papers with their current readiness-state badge. Right-pane dossier and margin mini-rail update in response to click/keyboard events against the live `/api/papers/<paper_id>/provenance` feed (no baked-in JSON). `paper-provenance.js` logic + CSS ported, rewritten where needed for the existing safe-DOM policy (no innerHTML with untrusted content — enforced by the dashboard's security hook).
- [ ] 9g-8: Wire to main dashboard — new 10th tab link in `dashboard.html`. Picks up paper_id from URL (`?tab=paper&paper=paper12_polariton`) so deep-links from the Knowledge Graph / Readiness tabs work (click a paper node → land on its provenance view).

**Gate:** Paper 12 polariton renders end-to-end — click a claim → dossier shows 8-layer matrix pulled from live registries + claims_review.json; FAIL on Giacobino2025 matches the real `CITATION_REGISTRY` state; all 4 of Wave 9g's registrations tested with Playwright.

**Estimated effort:** 3–4 days. Largest chunk is 9g-2 + 9g-3 (paper-HTML pipeline + claim authoring); the endpoint + tab are ~1 day combined.

---

## Execution Order & Estimates

| Wave | Blockers | Est. | Note |
|---|---|---|---|
| 0 | — | 0 (done) | Short-name fix landed this session |
| 1a | 0 | 0.25d | Mechanical rename + lake build |
| 1b | — | 0.5d | `update_counts.py` wiring |
| 1c | — | 1.5d | 6 extractors; some (ProductionRun log parsing) are tricky |
| 2a | 1c | 0.5d | Additive node types |
| 2b | 2a | 0.5d | Additive edge types |
| 2c | 2a, 2b | 0.5d | Tests + docs |
| 3a | 2 | 1.5d | Config flag + dual-path |
| 3b | 3a | 1d | Migration + parity CHECK 17 |
| 3c | 3a, 5a | 1d | Write-back (soft-coupled to Wave 5) |
| 4a | 2, 3 | 2d | 11 gate evaluators |
| 4b | 4a | 1d | Invalidation propagation |
| 4c | 4a | 0.5d | CHECK 18 |
| 5a | 4 | 1.5d | Heatmap + paper focus |
| 5b | 4, 2 | 1d | Graph tab extensions |
| 5c | 3c, 4 | 0.5d | Action buttons |
| 6a | — | 0.5d | Agent definition (can start early, uses Wave 1c review extraction) |
| 6b | 6a, 4 | 1d | Pipeline stage doc + loopback logic |
| 6c | 6b | 0.5d | Triggering |
| 7a | 6 | 0.5d | QI register generator |
| 7b | 5a | 1d | Dashboard tab |
| 7c | 7a | 0.25d | Pipeline doc |
| 8a | 3 | 0.5d | JSON-LD export |
| 8b | 3 | 0.5d | Notebook helper |
| 9a | — | 0 (done 2026-04-24) | Dashboard perf + UX (cache + topbar + pill labels + reload-hang root-cause) |
| 9b | — | 0 (done 2026-04-24) | Filter composition + search (AND-compose; Playwright-verified) |
| 9c | — | partial (done 2026-04-24) | name_deps extraction in ExtractDeps.lean + /api/graph/uses_edges + UI toggle |
| 9d | — | 0 (done 2026-04-24) | Dynamic chain viz — 9 chains, L0/L1 tab, 4 endpoints, Playwright-verified |
| 9e | — | 0 (done 2026-04-24) | Lean extraction: env-var gate for name_deps; baseline ~7 min preserved |
| 9f | — | 0 (done 2026-04-24) | PG+AGE flip: sync script + /api/graph/cypher + SK_EFT_GRAPH_SOURCE + startup check |
| 9g | 9e, 9f | 3-4d | **Paper Provenance (v2 design)** — 10th interactive tab + 8-layer dossier + claim-span HTML pipeline |

**Critical path:** Wave 1 → 2 → 3 → 4 → 5a → 4c → 6b → submission-gate functional. ~10 days focused work.

**Parallelizable tracks after Wave 2:**
- Adversarial agent (6a) can be authored while 3 is in progress
- External API (8) can proceed after 3 independently of 4/5/6/7

**Wave 9 (dashboard) current state (2026-04-24):** Waves 9a/b/c/d/e/f all landed. Remaining: **9g (Paper Provenance)** — the largest deliverable.

**9g sequencing for the next session:**
- 9g-1 (adversarial-reviewer JSON output) + 9g-3 (claim-ID authoring in paper TeX) can happen in parallel.
- 9g-2 (render_paper_html.py + claim.sty) is small but gates 9g-5, 9g-7.
- 9g-4 (provenance endpoint) reads existing `claims_review.json` + registries; can be built end-to-end without waiting for claim anchoring.
- 9g-7 (interactive tab) is the user-facing payoff — ports `paper-provenance.js` + CSS to the dashboard's safe-DOM policy; deep-link via `?tab=paper&paper=<id>`.
- 9g-6 (POST vet) is optional + depends on whether vet state lives in PG (would slot naturally after 9f) or in a JSON sidecar.

---

## Success Criteria (end of Phase 5v)

**Original Phase 5v goals (tracking Waves 0–8):**
- [ ] All 13 April-review failure modes are caught by at least one ReadinessGate in the current graph
- [x] Dashboard readiness tab shows all 18 papers × 11 gates; current state visible at a glance (Wave 5a done)
- [ ] Running Stage 13 adversarial review against a known-bad paper (e.g., pre-fix Paper 7) flags the TPF citation issue; running against a known-good paper clears cleanly
- [ ] `validate.py` CHECK 17 (graph parity) passes in CI — needs Wave 9f landed
- [x] `counts.json` is the single source of truth for every count reference in every paper (Wave 1b done)
- [x] `docs/QI_REGISTER.md` tracks the seed findings from April; first regenerated report emitted to user (Wave 7a done)
- [ ] PG+AGE is source of truth; Python registries are regenerated artifacts — pending Wave 9f
- [x] No silent drops, no silent collisions, no silent misses — every gap emits a log line (Wave 0 + 1c done)

**Wave 9 dashboard extension goals (added mid-phase, 2026-04-24):**
- [x] Dashboard doesn't hang on cold start (reload-hang fixed Wave 9a)
- [x] `/api/graph*` endpoints respond in milliseconds on cached hits (Wave 9a: 14.8s → 0.9ms)
- [x] Filter composition works — search + paper focus + logical focus AND together (Wave 9b)
- [x] Research Status tab shows 9 chains auto-discovered from `MODULE_CHAIN_MAP` (Wave 9d)
- [ ] Lean re-extraction with `name_deps_project` completes in <120s (Wave 9e)
- [ ] Dashboard operates in `SK_EFT_GRAPH_SOURCE=pg` mode with Cypher-powered subgraph queries (Wave 9f)
- [ ] Paper Provenance tab renders paper12_polariton end-to-end with live 8-layer verdicts per claim (Wave 9g)

---

## Pipeline Updates (for WAVE_EXECUTION_PIPELINE.md)

Two new stages to be inserted after Stage 12:

```
Stage 13: ADVERSARIAL REVIEW         → Gate: all P1 ReadinessGates pass; P2 gates passed-or-accepted
Stage 14: META-PROCESS QI            → Advisory; emits QI_REGISTER update + user-facing report
```

Both stages reference `ReviewFinding` and `ReadinessGate` nodes as their primary data. Stage 13 is a blocking gate for submission; Stage 14 is advisory but generates a tracked artifact.

---

## References

- `docs/KNOWLEDGE_GRAPH.md` — original KG spec (Phases 1 / 1.5 complete; 2 / 3 absorbed here)
- `docs/WAVE_EXECUTION_PIPELINE.md` — the 12-stage law; Phase 5v extends to 14
- `temporary/working-docs/reviews/papers/2026-04-12-Perplexity/SK_EFT_Hawking — Master Systematic Update Checklist.md` — source of the 13-dimension taxonomy
- `docs/roadmaps/Phase5u_Paper_Revision_Roadmap.md` — April paper-revision sibling track (content; 5v is process)
- `.claude/plugins/physics-qa/agents/claims-reviewer.md`, `figure-reviewer.md` — existing QA agents; Wave 6 adds `adversarial-reviewer.md`
- `scripts/build_graph.py` (Wave 0 fix applied), `scripts/graph_integrity.py`, `scripts/provenance_dashboard.py` — implementation anchors
