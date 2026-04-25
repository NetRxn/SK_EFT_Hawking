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

### Wave 1d — Stale-reference detection [planned 2026-04-26]

**Trigger.** Two QI candidates surfaced within 24 hours each pointing at the same architectural gap: paper prose carries cross-document references (Lean theorem names, tracked hypotheses, citation DOIs/arXiv IDs) that go stale faster than Stage-13 manual sweeps can catch. Three structural validate.py CHECKs close the loop.

**Origin QI candidates:**
- 2026-04-25, paper20 Stage-13 review — Phase 5z Wave 1 strengthening pass renamed/removed three theorems referenced by paper draft prose. Suggested action: `validate.py --check paper_lean_refs`. Folds into existing `qi-leanproofsubstance` cluster.
- 2026-04-25, qi-assumptiondisclosure cluster (6 findings across 4 papers) — papers cite Lean theorems as "verified" but the theorems carry tracked `Prop` hypotheses (e.g. `H_VestigialRelicCarriesZ16Charge`, `H_AdiabaticRegimeCorrection`) that the paper's assumptions section doesn't disclose. Same architectural class.
- 2026-04-26, paper20 citation-verification round (Stage-13 deferred-REQUIRED-1.11 closure) — surfaced **1 entirely fabricated citation** (`WetterichNJL` = nonexistent PLB 901, 136223 (2024); CrossRef 404; not in any deep research; appeared in three load-bearing places: `CITATION_REGISTRY` + Lean docstring + paper TeX) and **3 wrong-arXiv** entries (registry pointed at name-shaped wrong-target arXiv IDs that resolved to unrelated papers — all 200-OK fetches, only fuzzy-title-match catches them). Severity: critical per WAVE_EXECUTION_PIPELINE.md §Stage 14. Report: `papers/AutomatedReviews/2026-04-26-0130-citation-verification/paper20_scalar_rung.md`.

**Architectural rationale (why Wave 1d, not Wave 10g).** All three checks are pipeline plumbing — same class as Wave 1b's `counts_fresh` / `count_literals`. Independent timing — they don't gate on Wave 10's 8-day critical path. Both `paper_lean_refs` and `paper_hypothesis_disclosure` are structural mirrors of claims-reviewer-v2 finding classes (Class TN and Class HD respectively, see Wave 10a) but the cheap deterministic versions land here without waiting on Wave 10's agent infrastructure.

**Deliverables (3 CHECKs):**

- [ ] **`validate.py --check paper_lean_refs`** [offline; cheap, ~50 LOC]
  - Walk every `papers/paper*/paper_draft.tex` for `\texttt{<Module>.<identifier>}` (also `\mathtt{...}`, `\verb|...|`, `\begin{lstlisting}[language=Lean]` blocks).
  - Match against the live declarations in `lean/lean_deps.json` (always populated; no `EXTRACT_NAME_DEPS` flag needed).
  - FAIL = strengthening-pass paper drift (the 2026-04-25 failure class). Sentence-precise location reporting.
  - Strengthens **Gate 5 LeanProofSubstance** + **Gate 9 NumericalFreshness**.

- [ ] **`validate.py --check paper_hypothesis_disclosure`** [offline; cheap, ~80 LOC]
  - For each paper, walk `PAPER_DEPENDENCIES[paper].lean_modules` → collect every cited Lean theorem's incoming `ASSUMES` edges (already wired Wave 1c via `HYPOTHESIS_REGISTRY.dependent_theorems[]`).
  - For each tracked hypothesis depended on by a paper-cited theorem, grep the paper's TeX for the hypothesis name AND for an "Assumptions" / "Hypotheses" section listing it.
  - FAIL = paper claims "verified" without disclosing the load-bearing hypothesis (the qi-assumptiondisclosure pattern).
  - Strengthens **Gate 6 AssumptionDisclosure**.

- [ ] **`validate.py --check citation_live_resolution`** [network; gated by Stage-13 readiness, NOT default suite, ~80 LOC]
  - Walk every `CITATION_REGISTRY` entry with non-null `doi`. HEAD `https://api.crossref.org/works/{doi}` — 404 distinguishes fabricated DOI cleanly (the WetterichNJL pattern).
  - For non-null `arxiv`, HEAD `https://arxiv.org/abs/{arxiv}`. **200 alone is insufficient** — also pull title and fuzzy-match (token-set ratio ≥ 0.6) against `CITATION_REGISTRY[bibkey]['title']`. The 3 wrong-arXiv cases were all 200-OK but pointed at unrelated papers.
  - For pre-arXiv era (~1993 and earlier): NASA ADS as proxy (`https://ui.adsabs.harvard.edu/abs/{bibcode}/abstract`) — APS direct returns 403 to WebFetch-class agents.
  - For ISBN-only textbook entries: Routledge/WorldCat returns 403; flag as `partial_match` not `fetch_failed`.
  - Cache via existing `scripts/citation_cache.py` 90-day staleness policy. Reviewer field: `llm-webfetch:YYYY-MM-DD` for LLM-driven; `human:<userid>` for spot-check.
  - Run as part of `validate.py --check readiness_submission_gate` (Stage 13) — NOT default suite — so offline CI doesn't block on network.
  - **Severity: critical** per WAVE_EXECUTION_PIPELINE.md §Stage 14.
  - Strengthens **Gate 1 CitationIntegrity**.

**Implementation constraints** (from 2026-04-26 evidence — see `temporary/working-docs/phase5v_wave1d_handoff.md` for full taxonomy):
- CrossRef HEAD probes — 404 = fabricated; cache 90 days.
- arXiv HEAD + title fuzzy-match — never trust 200-OK alone.
- NASA ADS for pre-arXiv; APS/Routledge/WorldCat blocked to WebFetch-class agents.
- Reuse `scripts/citation_cache.py`'s `bibitem_hash`, `lookup_latest`, `is_stale`, `append_record`.

**QI register update.** After Wave 1d lands, re-run `scripts/qi_register.py` to surface the 2026-04-26 critical-severity finding under `qi-citationintegrity`. Wave 1d closure cites `evidence_on_close = phase5v-wave-1d-commit-sha` for both qi-leanproofsubstance and qi-citationintegrity items.

**Effort:** ~1 session (~3-4h) for all three checks combined. paper_lean_refs is the cheapest (~50 LOC, regex + dict lookup); paper_hypothesis_disclosure builds on existing ASSUMES extraction (~80 LOC); citation_live_resolution reuses citation_cache.py infrastructure (~80 LOC + integration).

**Gate for Wave 1d:** all three CHECKs registered in `validate.py`; offline checks (paper_lean_refs, paper_hypothesis_disclosure) run in default suite; citation_live_resolution gated to Stage-13. QI register regen surfaces fabricated-citation finding as critical. paper20 + papers with tracked-hypothesis deps cleared on first run (or remediated via documented action plan).

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

### Wave 9h — Datastar realignment across all dashboard tabs — DONE 2026-04-24

**Trigger.** User flagged 2026-04-24: "we moved implementations from datastar to HTMX" — actually the truth is the dashboard *drifted* from its own declared stack. Commit `ea97745` (2026-04-03, another agent) is labelled "HTMX→Datastar migration" and added the `<script src="...datastar...">` tag, but the CDN URL was `https://cdn.jsdelivr.net/npm/@starfederation/datastar` which 404s. **No templates were ever ported to use Datastar attributes.** Subsequent dashboard work (readiness_tab, qi_tab, chains_tab, paper_provenance_tab — including everything I shipped in Waves 9a/b/d/g this session) used vanilla JS + fetch, matching the already-drifted pattern rather than the declared stack decision in `project_knowledge_graph_status.md`:

**REQUIRED READING before touching ANY dashboard template in this wave:**
- `docs/references/Datastar_Dashboard_Reference.md` — consolidated in-repo reference with attribute cheat sheet, action reference, SSE event format, `datastar-py` SDK integration patterns, SK-EFT signal-name vocabulary, security policy, and migration checklist. Pulled from upstream 2026-04-24 so sessions don't need to WebFetch.
- `feedback_dashboard_datastar_stack.md` memory — records why the drift happened and how to avoid repeating it.

> Stack: PG 17 (local Homebrew) + Apache AGE + D3.js + **Datastar (replaces HTMX)** + Flask

The per-session memory `reference_datastar_docs.md` also flags Datastar docs as "required reading for dashboard development, not in LLM training data" — which I missed. Going forward, dashboard work MUST consult that memory and the Datastar attribute + SSE references before shipping.

**CDN URL fixed 2026-04-24** (`datastar@v1.0.0-beta.11` canonical GH-tagged build, verified 200 / 40 KB) so Datastar actually loads in the browser. But ZERO tabs consume it — this wave ports them.

**Plan (comprehensive, not per-tab):**

- [x] **9h-1 Audit baseline.** Matrix of tabs × interactivity compiled; all 4 tabs + graph inventoried (fetch endpoints, DOM state, keyboard handlers, URL params).
- [x] **9h-2 Datastar-Python SDK.** `datastar-py@0.8.0` promoted from `[optional-deps].graph` to main deps. Flask glue layer in `scripts/datastar_helpers.py` provides `is_datastar_request()` / `read_signals()` / `sse_response()` / `esc()` — Flask isn't a first-class SDK framework so this is the minimal shim.
- [x] **9h-3 Signal vocabulary.** Shared: `$activePaper`, `$activeClaim`, `$activeGate`, `$paperStateFilter`, `$gateFilter`, `$filterLayers`, `$qiShowOpenOnly`, `$expandedChain`, `$kgMode`, `$kgLayout`. Documented in `docs/references/Datastar_Dashboard_Reference.md` §6.
- [x] **9h-4 Port readiness_tab.** Heatmap + focus pane + 4 filter-button state toggles + gate-head column-filter. 503 LOC → 172 LOC (66% reduction). Server-rendered heatmap table + focus pane via SSE patch_elements; filter row static Datastar attrs.
- [x] **9h-5 Port qi_tab.** 256 LOC → 107 LOC (58% reduction). Open/all toggle bound to `$qiShowOpenOnly`.
- [x] **9h-6 Port chains_tab.** 436 LOC → 131 LOC (70% reduction). L1 milestone DAG now renders as SSR SVG (layoutDAG ported to Python) rather than client-side D3-free geometry.
- [x] **9h-7 Port paper_provenance_tab.** 545 LOC → 198 LOC (64% reduction). Keyboard nav (`←/→/F/W/Esc`) wired as Datastar `data-on:keydown__window` expressions that pass a `nav` payload; server-side `_pp_apply_nav` computes the next `activeClaim`. Deep-link via `?paper=…` URL param populated into `$activePaper` at template time.
- [x] **9h-8 Graph tab decision.** D3 canvas stays vanilla per the roadmap rationale; `data-signals="{kgMode:'explore',kgLayout:'force',kgActivePaper:'',kgSearch:''}"` on `#kg-wrap` so cross-tab navigation can set state programmatically. Documented inline.
- [x] **9h-9 Remove vanilla JS duplication.** Every tab partial's `<script>` block is gone except graph_tab (D3 exception). Verified: `grep -l 'fetch(' scripts/templates/partials/*.html` only hits graph_tab.
- [x] **9h-10 Preserve existing security policy.** `datastar_helpers.esc()` wraps every interpolated value in SSE-emitted HTML; Datastar handles `data-text` escaping. Security hook still active; no `innerHTML` with untrusted data introduced.
- [x] **9h-11 Playwright smoke test.** Cycled through readiness → qi → chains → paper → graph. All load with `data-signals` root, server-rendered morph targets populate, filter/nav/keyboard interactions work end-to-end, zero console errors, all 6 API endpoints return 200 on both SSE and JSON paths.

**Shipped (2026-04-24):**

| File | Change |
|---|---|
| `pyproject.toml` | `datastar-py>=0.5` promoted to main deps |
| `scripts/datastar_helpers.py` | New — Flask glue layer |
| `scripts/provenance_dashboard.py` | Auto-negotiate on `/api/readiness`, `/api/qi`, `/api/chain/list`, `/api/papers/<id>/provenance`; ~17 new `_*_html` / `_*_sse_events` helpers |
| `scripts/templates/dashboard.html` | CDN pin `v1.0.0-beta.11` → `v1.0.1` (beta uses old `merge-fragments` event names; SDK 0.8.0 emits `patch-elements` which v1.0.0+ consumes) |
| `scripts/templates/partials/readiness_tab.html` | Rewrite |
| `scripts/templates/partials/qi_tab.html` | Rewrite |
| `scripts/templates/partials/chains_tab.html` | Rewrite |
| `scripts/templates/partials/paper_provenance_tab.html` | Rewrite |
| `scripts/templates/partials/graph_tab.html` | `data-signals` declaration on `#kg-wrap`; inline rationale |
| `docs/references/Datastar_Dashboard_Reference.md` | Updated CDN pin + event-name rename gotcha |
| `feedback_dashboard_datastar_stack.md` (memory) | Post-port prescriptions: colon syntax mandatory, `data-on-intersect__once` for init, SDK+client version match |

**Key learnings (documented in reference + memory):**

- **Event-name rename ~April 2026**: `datastar-merge-fragments/signals` → `datastar-patch-elements/signals`. The v1.0.0-beta.11 bundle the repo was pinned to uses the old names; datastar-py 0.8.0 emits the new names. Mismatch = fetch fires, server returns 200, client silently drops the events. Pin v1.0.1 and re-verify any bundle bump with `curl bundle.js | grep -oE 'datastar-[a-z-]+'`.
- **Attribute syntax is colon, not hyphen**: `data-on:click` ✓, `data-on-click` ✗. Datastar silently ignores the hyphen form. Same for `data-bind:x`, `data-signals:x`, `data-class:x`.
- **Init fetch**: `data-on-intersect__once="@get(...)"` reliably fires for tab-embedded content. `data-on-load` / `data-init` behaved inconsistently.
- **Flask has no SDK module**: roll-your-own `datastar_helpers.py` with `is_datastar_request` + `read_signals` + `sse_response`. Auto-negotiate by `Accept: text/event-stream` — keep JSON for tests/scripts.

### Wave 9g — Paper Provenance (v2 design) — MOSTLY DONE 2026-04-24

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
- [ ] 9g-2: `scripts/render_paper_html.py` — pandoc `.tex` → HTML, post-process to strip LaTeX artifacts; add `\claim{id}{body}` macro registration in paper TeX preamble (`docs/tex-macros/claim.sty`) so pandoc emits stable spans. Output: `papers/<paper>/paper_rendered.html`. **Partially shipped** (see 9g-v2-render below) — minimal LaTeX→HTML renderer in-process; no pandoc dependency; no `\claim{}` macro yet.
- [ ] 9g-3: Per-paper `claims_manifest.json` or inline `\claim{...}` — retrofit Paper 12 polariton first as the design's reference case. Blocker for inline highlighting of NUM/QUA/PAR-layer claims — today only CIT-layer bibkeys highlight via author-name heuristic.
- [x] 9g-4: Backend endpoint `GET /api/papers/<paper_id>/provenance` — DONE; synthesises 8-layer verdict from claims_review.json + figure_review_report.json + registries. Auto-negotiates SSE (Datastar) vs JSON.
- [ ] 9g-5: Backend endpoint `GET /api/papers/<paper_id>/rendered_html` — **superseded** by in-process `_pp_paper_body_html` which renders the abstract directly; pandoc-pipeline still needed for full-body render.
- [ ] 9g-6: Optional `POST /api/papers/<paper_id>/claims/<claim_id>/vet` — not yet wired; depends on 9f PG write-back decision.
- [x] 9g-7: Interactive tab — DONE (Datastar-native, v2 design, cream theme, banner + filter chips + paper-body + dossier).
- [x] 9g-8: Main dashboard wired; deep-link `?paper=<id>` auto-loads.

**9g-v2-render (shipped 2026-04-24, as part of the Wave 9h final pass):**

Rather than bringing pandoc into the tooling stack for a minor dependency, a minimal LaTeX→HTML renderer was inlined into `provenance_dashboard.py`:

- `_latex_to_html(tex, citation_claims, active_claim)` — walks the tex char-by-char; handles inline math (`$...$` via `_render_math_inline`), italic/bold/code text commands, em/en dashes, paragraph breaks, and drops `\label`/`\ref`/`\begin`/`\end`. Unknown commands pass through as-is so gaps are visible rather than silently eaten.
- `_render_math_inline(expr)` — Greek letters (α β γ δ ε ζ η θ ι κ λ μ …), operators (≈ ± × · ∈ ≤ ≥ ≠ ∞ ∂ ∑ ∫ ℏ …), sub/superscripts rendered as Unicode where possible (`^{10}` → ¹⁰, `^{-1}` → ⁻¹), HTML `<sub>/<sup>` fallback otherwise.
- `_pp_extract_abstract(path)` — regex `\begin{abstract}…\end{abstract}` from the paper's .tex.
- `_pp_wrap_claim_spans(html, claims, active)` — two-pass heuristic: (1) exact quote-substring match on rendered HTML, (2) citation author-name match (`Falque2025` → highlight bare "Falque"). Wraps with color-by-worst-status spans (FAIL = solid red underline, WARN = amber wavy, INFO = blue dotted, PASS = unstyled). Click → sets `$activeClaim` + fetches for dossier matrix.
- `_pp_default_dossier_html(data)` — right-pane default view: PROVENANCE DOSSIER header + BLOCKING ISSUES list + NON-BLOCKING FOLLOW-UPS list from claims_review.json.
- `_pp_dossier_html(data, active)` — per-claim 8-layer matrix with "← back to dossier" button.

**Verified on paper12_polariton**: banner (PID + title + meter 2F/13W/49P/2I + REVIEW 2026-04-13 + ISSUES FOUND badge), filter chips (Numeric 23 / Theorem 7 / Axiom 1 / Hypothesis 2 / Citation 18 / Parameter 8 / Figure 2 / Qualitative 5), abstract with live math inlines (κ ∈ [0.07, 0.11] ps⁻¹ etc.), PROVENANCE DOSSIER default with 3 BLOCKING + 6 NON-BLOCKING, click a claim span → full per-claim matrix with back button.

**Known gap**: inline highlighting only lands on CIT-layer author-name mentions today. Full inline highlighting of NUM/PAR/QUA claims requires 9g-3 (canonical `\claim{id}{text}` anchors in the tex so each claim has a stable position, not a fragile substring match).

**Gate:** Paper 12 polariton renders end-to-end ✓; per-claim matrix + back navigation ✓; blocking/non-blocking surfacing ✓; CDN loads clean; no console errors; data flows through the v2 shape.

---

## Wave 10 — Sentence-level prose audit + verification UX [planned 2026-04-24]

**Trigger.** Wave 9g shipped a per-paper claim dossier matching the v2 mockup, but the user-stated requirement is **prose-level review** — "I want to read the paper and know with 100% certainty exactly what, if anything, backs every word." The Wave 9 dossier surfaces ~30–60 curated claims per paper; a real prose audit covers ~250 sentences per paper, with explicit GROUNDED / INTERPRETIVE / UNGROUNDED tagging on every prose unit.

A rigor-audit on three random papers (5, 10, 16) [results at `/tmp/paper{5,10,16}_rigor_audit.md`] established baseline truth:

- Paper 5 (medium QA coverage): 95 prose units · 9% UNGROUNDED · ~25% rigor-layer-only residual; 8 internal contradictions surfaced (`(20 thms, 0 sorry)` vs `(20 thms, 1 sorry)` in same paper, "five vs four obstacles" stealth drift, missing CITATION_REGISTRY entries, etc.)
- Paper 10 (full claims_review + 50pp adversarial review): 95 prose units · 9% UNGROUNDED · ~10–15% rigor-layer-only residual; **dominated by freshness drift** — Lean v4.28 vs v4.29, Mathlib pin drift, "130 modules" vs actual 167, "2237 thms" vs actual 3729, plus 8 of 23 prior adversarial findings already STALE (resolved but still surfaced as open)
- Paper 16 (zero existing structured QA): 115 prose units · **30% UNGROUNDED** · ~30% rigor-layer-only residual; 16 of 22 bibitems missing from CITATION_REGISTRY, no PAPER_DEPENDENCIES entry, 8 of 11 readiness gates would BLOCK if evaluated

**Key insight.** The rigor layer's value is not "catches new findings" — it is three things at once:
1. **Coverage forcing function**: per-sentence default state of UNCLAIMED makes silent under-coverage structurally visible (paper 16's 30% UNGROUNDED was previously invisible because no agents had run).
2. **Freshness watchdog**: prior reviews go stale on a ~2-week cycle; per-sentence verification timestamps + per-link `last_modified` propagation auto-flip stale verifications to NEEDS_RECHECK. **This is the highest-value capability** — it kills the "fixes ship without re-runs, dashboard now lies" failure mode that paper 10's audit surfaced.
3. **Net-new findings (10–25%)**: internal arithmetic drift, toolchain pin drift, stealth pipeline-vs-prose drift, module-internal-docstring drift. Real but not transformative.

**Architectural decisions** (locked in via design review 2026-04-24, post-feedback revision 2026-04-26):
- **Single agent, not parallel.** Evolve `claims-reviewer` to be sentence-level; do not build a separate `prose-auditor`. Adversarial-reviewer stays distinct (different role: fresh-context external check). Design: `temporary/working-docs/claims_reviewer_v2_design.md`.
- **Agent verdict decoupled from human review state.** Agent verdict captures only chain-resolution status (`PASS|FAIL|WARN|INFO|UNGROUNDED|TRANSITION`); human ratification is a separate orthogonal axis owned by the dashboard. The "parameter LLM-verified-only" condition is a per-link `link_state` flag, not a sentence-level WARN.
- **Reconciliation, not silent supersession.** Prior findings that don't reproduce go to `non_reproducing_prior_findings[]` with `status: candidate_for_supersession`; only deterministic structural checks (re-run grep, re-run lake build counts) auto-close. LLM-judgment findings require human ratify-or-reject before status flips to `superseded`. Asymmetry of risk: silently disappearing a true issue is worse than a stale finding remaining visible.
- **Content-hash sentence IDs.** `sentence:<paper>:<section_slug>:<sha8(normalized_quote)>`. Survives section reorder, sentence insert/delete, benign edits (punctuation, citation insertion, whitespace) via aggressive normalization. Substantive edits = new ID + tombstone old; near-match heuristic offers "carry forward verification?" prompt for rewrites.
- **No backward compat.** Sentence-keyed schema is the only schema; no derived typed-section views to maintain long-term. Feature flag during migration; no downstream consumers to preserve.
- **Verification surface unification.** Paper Provenance becomes the universal verification entry-point because most other tabs lack write-back UX today (only Parameters has Confirm/Reject/Flag). Other tabs become reflective read-views; state is shared.
- **No pandoc.** Extend the existing minimal LaTeX→HTML renderer (Wave 9g final pass) to handle full body — `\section` / `\subsection`, `\begin{itemize}` / `\begin{enumerate}`, displayed equations as text (`\begin{equation}`, `\begin{align}`, `\[...\]`), figure stubs (`\begin{figure}` → `[Figure N: caption]` placeholder). ~1d of work; pandoc dependency avoided.
- **KG schema additions.** New node types `Sentence` + `AuditEvent` + `ClaimCluster`; `ProseClaim` retained (curated high-priority-claim layer from Wave 2f stays as-is; Sentence is the fine-grained full-coverage layer — different roles, both valuable). New edge types `BACKED_BY` + `LOGGED_BY` + `MEMBER_OF` (Sentence → ClaimCluster). Cross-paper claim equivalence always goes through ClaimCluster nodes — `SAME_CLAIM_AS` pairwise edges **are NOT added** (n-ary relationships modeled as 2-cliques are awkward + O(n²); ClaimCluster handles both 2-member and N-member groupings uniformly). New `last_modified` field on every artifact node propagated via dependency walk. Total: **25 node types** (was 22), **25 edge types** (was 22). Design: `temporary/working-docs/sentence_kg_schema_delta.md`.
- **CLI is the only writer.** `scripts/sentence_state.py` is the sole path for human-verification + supersession + audit-log writes. LLMs (and the dashboard backend) call the CLI, never edit JSON directly. Maintains JSON-canonical-at-rest / PG-mirror architecture (Wave 9f) and prevents LLM unsafe-edit failure mode.
- **Paper Contributions tab retires.** Subsumed by per-sentence Paper Provenance once Wave 10 lands. Other 9 tabs keep distinct roles (verification surfaces or exploration views).

### Wave 10a — claims-reviewer v2 schema + prompt

**Five new finding classes** (the rigor-layer-uniquely-finds work):

1. **Class IA — Internal arithmetic / count drift.** Numbers appearing in two places in the paper text with different values; pipeline-computable counts (theorems / sorry / axioms / modules / tests / structural-obstacles) that differ from live pipeline. Cross-checks against `lake build`, `pytest --collect-only`, `grep ^axiom`, `lean_deps.json`, and `len(...)` of fixed-list constants in `formulas.py` / `constants.py`. Maps to Gate 9 NumericalFreshness.

2. **Class TP — Toolchain pin drift.** Literal `Lean v\d+\.\d+\.\d+` in paper vs. `lean-toolchain` file; `Mathlib <8-char-hash>` vs. `lakefile.toml` mathlib rev. Maps to Gate 9.

3. **Class SD — Stealth pipeline-vs-prose drift.** Prose adjectives/numerals describing structured objects with known cardinality (paper says "five obstacles", `formulas.py::structural_obstacles` returns 4). Bounded heuristic: walk integer-returning functions whose name contains `count` / `total` / `n_` plus `len(...)` of fixed-list constants; cross-check paper for those values. Maps to Gate 9 + relevant downstream gate.

4. **Class TN — Theorem-name reference drift.** [NEW 2026-04-26 from paper20 QI candidate.] Regex extract every `\\texttt{<module>.<symbol>}` in paper TeX; lookup in `lean_deps.json` declaration registry (always populated; no `EXTRACT_NAME_DEPS` needed). FAIL on miss. Sentence-level. Maps to Gate 5 LeanProofSubstance + Gate 9. Addresses the Stage 13 paper20 finding pattern: "paper authoring during a Lean refactor leaves stale theorem-name references in prose."

5. **Class HD — Hypothesis disclosure.** [NEW 2026-04-26 from qi-assumptiondisclosure cluster.] When a sentence's chain links to a Lean theorem (kind=`theorem`), walk the theorem's incoming `ASSUMES` edges (already extracted Wave 1c via HYPOTHESIS_REGISTRY). For each tracked-Prop hypothesis (e.g., `H_VestigialRelicCarriesZ16Charge`, `H_AdiabaticRegimeCorrection`, `H_MixedChannelZ16Cancels`), check the paper's prose for a disclosure of the assumption. FAIL if undisclosed. Maps to Gate 6 AssumptionDisclosure. Mechanism is purely structural — uses HYPOTHESIS_REGISTRY data already wired post-Wave 0.

**Wave 10a deliverables:**
- [ ] Update `.claude/plugins/physics-qa/agents/claims-reviewer.md` per `claims_reviewer_v2_design.md` §5
- [ ] Sentence-keyed JSON schema (`sentences[]` is the only primary store; no derived typed-section views) — see design doc §2
- [ ] Five finding classes: IA / TP / SD / TN / HD per above
- [ ] Decoupled verdict semantics: agent verdict in `{PASS, FAIL, WARN, INFO, UNGROUNDED, TRANSITION}` is purely about chain-resolution + recomputation; human ratification state is a separate orthogonal field never set by the agent
- [ ] Reconciliation protocol: prior findings that don't reproduce go to `non_reproducing_prior_findings[]` with `status: candidate_for_supersession`. Auto-close ONLY when the agent re-ran a deterministic structural check (e.g., re-grepped sorry count, re-extracted Lean decl registry) that produced a different result; cite the check in the entry. LLM-judgment findings require human ratify-or-reject via dashboard.
- [ ] Content-hash sentence IDs: `sentence:<paper>:<section_slug>:<sha8(normalized_quote)>`. Define normalization (lowercase, whitespace-collapse, strip TeX markup, strip citations); store raw quote alongside hash so diffs surface
- [ ] Smoke test on paper 12; verify five-finding-class classification correct on hand-curated cases; verify content-hash stability across benign edits

**Effort:** ~1.25d (was 1d; +0.25 for Class TN + Class HD detection logic + content-hash sentence ID).

### Wave 10b — KG schema delta + sentence_state.py CLI

- [ ] Add `Sentence` node type to `SHAPE_MAP` + extractor in `build_graph.py` (consumes `claims_review.json[sentences]`)
- [ ] Add `BACKED_BY` edge extractor; one edge per chain link. Per-link `link_state` derived from agent verdict + freshness only — no human-rated state on edges (per-link verify is UX affordance over the sentence-level `human_state`, not first-class data)
- [ ] Add `AuditEvent` node type + `LOGGED_BY` edge extractor (consumes `papers/<paper>/audit_log.jsonl`). `actor` field always carries `agent:<name>:<run-timestamp>` or `user:<id>` so the chain of findings across multiple agents is traceable per sentence.
- [ ] Add `ClaimCluster` node type for cross-paper claim equivalence (ALL cluster sizes — 2-member through N-member — go through ClaimCluster uniformly; no pairwise SAME_CLAIM_AS edges). Cluster carries `match_kind`, `confidence`, and `constructed_by` metadata
- [ ] Add `MEMBER_OF` edge (Sentence → ClaimCluster); one edge per sentence in cluster
- [ ] `ProseClaim` (Wave 2f) **unchanged** — retained as the curated high-priority-claim layer for abstract-level narrative claims; coexists with fine-grained Sentence layer
- [ ] Add `last_modified` computed field via dependency walk (`scripts/last_modified.py`); populated on every node during build_graph. Direct: file_mtime / human_verified_date / cache_hash_changed_at. Upstream: max over USED_BY / VERIFIED_BY / DEPENDS_ON_AXIOM / ASSUMES / IMPORTS / CITES / GROUNDED_IN / BACKED_BY
- [ ] Sentence tombstone state: when a `sentence_id` from prior run doesn't appear in current run, emit a `tombstoned` Sentence node (preserves audit history; not counted in coverage ribbon). Near-match Levenshtein heuristic surfaces "is this a rewrite of <old_id>?" candidates for one-click verification rollover
- [ ] **`scripts/sentence_state.py` CLI** — sole writer to `prose_state.json` + `audit_log.jsonl`:
   - `mark <sentence_id> verified|interpretive|needs_fix|needs_recheck --notes "..."`
   - `ingest_agent_run <claims_review.json>` — schema-validates, diffs against prior, generates `non_reproducing_prior_findings[]` candidates
   - `reconcile` — interactive supersession candidate review (pairs with deterministic auto-close)
   - `supersede <id> --reason "..."` — explicit human-confirm path
   - `tombstone-sweep` — detect deleted sentences and emit tombstone records + Levenshtein-match suggestions
   - All operations: schema validation → atomic write of prose_state.json + append to audit_log.jsonl. Dashboard backend and any agent-driven workflow calls these subcommands; nobody free-form-edits the JSON.
- [ ] Update `docs/KNOWLEDGE_GRAPH.md` schema tables (22→25 nodes: +Sentence, +AuditEvent, +ClaimCluster; 22→25 edges: +BACKED_BY, +LOGGED_BY, +MEMBER_OF)
- [ ] Validate.py `graph_integrity` extension: `sentence_chain_completeness`, `audit_event_immutability`, `claim_cluster_consistency` (all members of a cluster agree on `human_state`; disagreement flagged as Gate 2 CrossPaperConsistency issue), `last_modified_monotonicity`, `sentence_id_collision_check` (per design doc §8)
- [ ] PG+AGE sync extension (`scripts/sync_graph_to_pg.py`): mirror new node + edge types. PG remains read-only mirror — no `prose_state.json` writes go through PG

**Effort:** ~1.5d (was 1d; +0.5 for sentence_state.py CLI + tombstone state + ClaimCluster).

### Wave 10c — Cross-tab change-bus — DONE 2026-04-26

- [x] **`scripts/verification_state.py`** — append-only `docs/verification_log.jsonl` writer + library API. Sole writer to the log (mirrors sentence_state.py pattern). Subcommands: `record` / `list` / `apply`. Library API: `record_event`, `read_events`, `latest_per_node`, `apply_to_graph(graph)`, `node_id_for(artifact_type, artifact_id)`. Atomic flock'd appends; events validated against required-fields + action/actor enums.
- [x] Verification action on any tab bumps the artifact's `last_modified_explicit`. Wired paths:
  - `/verify` (Parameters tab; legacy vanilla-`fetch`/`safeSetHTML` — HTMX was removed at an earlier checkpoint, full Datastar port is a deferred Wave 9h-followup) — also calls `verification_state.record_event` + `_invalidate_graph_cache()`
  - `POST /api/verification/event` (NEW; generic JSON/form endpoint) — for future Citation verify, axiom-eliminability ratify, etc. Validates required fields + auto-derives `node_id` from `(artifact_type, artifact_id)`
  - `GET /api/verification/state` (NEW) — query event log; supports `?node_id=`, `?artifact_type=`, `?artifact_id=`, `?actor=`, `?latest_only=1`, `?limit=N`
- [x] Propagation pass: `build_graph_json` now calls `verification_state.apply_to_graph` BEFORE `last_modified.annotate_last_modified`, so explicit verification timestamps land on `meta.last_modified_explicit` and get upstreamed along the existing dependency edges (USED_BY, VERIFIED_BY, DEPENDS_ON_AXIOM, ASSUMES, IMPORTS, CITES, GROUNDED_IN, BACKED_BY, VERIFIES). `graph_integrity.run_integrity_checks` mirrors the same two-step apply.
- [x] **Bug fix in `scripts/last_modified.py::_direct_last_modified`** surfaced during smoke test: the function previously read `meta.last_modified` (its own OUTPUT) as a fallback input, making it non-idempotent — second annotation pass would short-circuit upstream propagation by reading the prior pass's annotation. Removed `last_modified` from the input fallback chain; `last_modified_explicit` is now the only caller-controlled override.
- [x] **Schema consolidation** in `last_modified.annotate_last_modified`: graph dict expects `nodes` + `links` (D3 convention; matches `build_graph_json`'s output shape). Earlier draft accepted both `edges` and `links` as a quick patch; consolidated on the single canonical key. All call sites (`build_graph.build_graph_json`, `graph_integrity.run_integrity_checks`) pass `{nodes, links}` consistently.
- [x] Sentence's effective verification: `last_modified.sentence_is_stale` (Wave 10b) flips Sentence to NEEDS_RECHECK when any BACKED_BY target's `last_modified > sentence.human_ratified_at`. Wired into the dashboard via `_pp_compute_stale_findings`.
- [x] Dashboard rendering: `_pp_compute_stale_findings` annotates each per-finding-per-claim entry with `stale: True` when the underlying artifact's verification timestamp post-dates `claims_review.review_date`. `_pp_claim_span_class` adds `pp-claim-span--stale`; CSS adds purple diagonal-stripe overlay (`--pp-stale: #6b3fa0`, `--pp-stale-bg`); per-claim layer matrix rows pick up `data-stale="true"` with a left-edge box-shadow + `pp-stale-badge`. Banner verdict pill picks up `data-v="stale"` (purple background, "NEEDS RECHECK" label) when ANY finding is stale, taking precedence over PASS/ISSUES_FOUND.
- [x] Dashboard graph cache invalidates on verification events: `_graph_fingerprint()` now stats `docs/verification_log.jsonl` + `scripts/verification_state.py` + `scripts/last_modified.py`. New `_invalidate_graph_cache()` helper flips the cache state directly (called inline from `/verify` and `POST /api/verification/event`) so the next request observes the change without waiting for a file mtime tick.
- [x] Smoke test: `paper12_polariton` review date 2026-04-13. Recorded one `Citation:Falque2025 confirm` + one `Parameter:Paris_long.c_s confirm @2026-04-26T15:00`; `_pp_build_data` reports `stale_count=2` of 66 claims; both findings carry `stale: True` + `stale_since` + `stale_actor`. End-to-end propagation verified: param:HBAR confirmed event → 41 downstream USED_BY formulas all carry the bumped timestamp after `annotate_last_modified`. `validate.py --check graph_integrity` PASS in 1.7s.

**Effort:** ~0.5d (actuals matched estimate; +small bug fix to `_direct_last_modified`).

### Wave 10d — Paper Provenance redesign (3-column layout + verification UX)

- [ ] Three-column layout: paper body | sentence inspector | chain-link inspector (collapses to popover on smaller screens)
- [ ] Full-body render via extended minimal LaTeX renderer (sections, lists, displayed equations, figure stubs)
- [ ] Per-sentence state machine UI: `UNCLAIMED` → `AGENT_PROPOSED` → `HUMAN_VERIFIED_{GROUNDED|INTERPRETIVE|UNGROUNDED}` / `NEEDS_RECHECK`
- [ ] Per-link verification UI inside chain inspector: three-state `✓ verified | ⚠ uncertain | ✗ wrong` per BACKED_BY edge
- [ ] **Keyboard-first nav**: `↑↓` sentence, `→` chain inspector, `↑↓` link, `v / i / u / r / n / Esc / Tab`
- [ ] **In-place link expansion**: clicking a link shows artifact source inline (Lean theorem body, parameter card, citation bibitem + cached primary-source title) without leaving the page
- [ ] **Diff-since-last-verified view**: when re-verifying, show only what changed since prior `human_verified_at`; one-click re-verify if changes are non-substantive
- [ ] **Coverage ribbon**: % verified / agent-proposed / unclaimed / stale / ungrounded; submission-readiness gate count
- [ ] **Audit log pane** (collapsible): per-sentence verification history from `audit_log.jsonl`
- [ ] Cross-tab state preservation: `?from=` URL chain, deep-links return to originating sentence
- [ ] Visual encoding (paper body): green/blue/red/amber/grey/purple-striped per state (per design doc §UX)

**Effort:** ~2.5d.

### Wave 10e — Adversarial-reviewer extension

- [ ] Update `.claude/plugins/physics-qa/agents/adversarial-reviewer.md` finding output: `Location` field MUST cite a `sentence_id` from current `claims_review.json` if one exists; falls back to `file:line` otherwise
- [ ] Graph extractor (`extract_review_finding_nodes`) anchors `FLAGS` edges to `Sentence` nodes via sentence_id
- [ ] Paper Provenance inspector pane shows adversarial findings overlaid onto the relevant sentence (not just in QI Process Health)

**Effort:** ~0.5d.

### Wave 10f — Cross-paper ClaimCluster detection + propagation

- [ ] New `claims-reviewer-cross-paper` pass: after individual paper reviews complete, find sentences making the same factual claim across papers (exact quote match → normalized match → semantic match)
- [ ] Emit `ClaimCluster` nodes with `match_kind`, `confidence`, `constructed_by` metadata. Cluster sizes 2+ all handled uniformly via ClaimCluster (no pairwise SAME_CLAIM_AS edges)
- [ ] Emit `MEMBER_OF` edges (Sentence → ClaimCluster), one per member sentence
- [ ] Dashboard: when human verifies a sentence in a ClaimCluster, prompt "Apply to N other members?"; on confirm, propagate state via cluster membership + emit one AuditEvent per propagation with `propagated_from: <source_sentence_id>` metadata
- [ ] Cross-paper coherence check (Gate 2): ClaimClusters with disagreeing member `human_state` values are flagged
- [ ] Verify-once-propagate UX walks cluster membership, not pairwise edges — simpler query + consistent handling for 2-member and N-member clusters

**Effort:** ~0.5d.

### Wave 10g — Retirement + deep-link cleanup

- [ ] **Retire Paper Contributions tab**. URL `/?tab=papers` redirects to `/?tab=paper&paper=<id>` (Paper Provenance with same paper preselected)
- [ ] Paper Readiness heatmap cells deep-link to `/?tab=paper&paper=<id>&filter=gate:<gate>` (Paper Provenance filtered to sentences invoking that gate)
- [ ] KG node detail panel for `Sentence` nodes deep-links back to `/?tab=paper&paper=<id>&sentence=<id>`
- [ ] Process Health QI cards deep-link to affected sentences in their paper(s)
- [ ] Decide whether Research Status (chains) tab survives — if its L1 milestone DAG duplicates `KG?chain=<id>` view, fold into KG; otherwise keep as curated traversal

**Effort:** ~0.25d. (Structural validate.py checks `paper_lean_refs` + `paper_hypothesis_disclosure` previously listed here have moved to **Wave 1d** — same architectural class as Wave 1b's pipeline-plumbing CHECKs, doesn't need to gate on Wave 10's critical path.)

### Wave 10h — Retrofit run

- [ ] Run claims-reviewer-v2 on all 18 papers (Phase 5v + Phase 5u + Phase 5w + Phase 5z papers extant). ~2h wallclock + agent budget
- [ ] Initial state: every sentence `agent_proposed`. Coverage ribbon will show ~0% human-verified across all papers — the verification backlog
- [ ] **Bulk-verify-unchanged** is the critical UX for clearing the backlog (per design doc §UX)
- [ ] Steady state: only `NEEDS_RECHECK` sentences require human re-action per dev cycle

**Effort:** ~2h wallclock + agent batch budget.

### Total Wave 10 effort

**~8 working days + retrofit batch** (revised 2026-04-26 post-feedback; was 7.25d). Expanded from earlier estimate absorbing: Class TN + Class HD finding classes (+0.25d on 10a), sentence_state.py CLI + tombstone state + ClaimCluster (+0.5d on 10b). Structural `validate.py` checks (paper_lean_refs, paper_hypothesis_disclosure) **moved to Wave 1d** 2026-04-26 (independence-of-timing — they're pipeline plumbing, no need to gate on Wave 10's critical path). Critical-path: 9c-followup-cache → 10a → 10b → 10c → 10d → 10h → 10f → 10g.

### Wave 10 success criteria

- [ ] Every prose unit in every paper has a `Sentence` node with proposed chain or explicit UNGROUNDED tag
- [ ] Per-link verification UI works for all chain-link types (formula / theorem / axiom / parameter / citation / hypothesis / aristotle / production_run)
- [ ] Cross-tab change-bus: parameter verification on Parameters tab visibly bumps dependent sentences in Paper Provenance to `NEEDS_RECHECK` within one rebuild
- [ ] Audit log pane shows full verification history per sentence; events are append-only and survive re-runs; actor field traces findings across multiple agents (claims-reviewer v2 → adversarial-reviewer → subsequent rounds)
- [ ] Five finding classes live: Class IA (count drift) + Class TP (toolchain pin drift) + Class SD (stealth cardinality drift) + Class TN (theorem-name reference drift) + Class HD (hypothesis disclosure)
- [ ] `scripts/sentence_state.py` CLI is the sole writer to `prose_state.json` + `audit_log.jsonl`; LLMs never free-form-edit
- [ ] Content-hash sentence IDs survive benign edits + section reorder; tombstone state preserves history for deleted prose
- [ ] Reconciliation (not silent supersession): non-reproducing prior findings land as human-ratifiable candidates unless closed by a deterministic structural recheck
- [ ] Paper 12 (reference paper) reaches 100% `human_verified_*` terminal state via the new UI; submission readiness check passes
- [ ] Paper 16 (worst coverage) drops from 30% UNGROUNDED to baseline ~9% after running the upgraded claims-reviewer + adversarial-reviewer + Wave 10c freshness machinery
- [ ] Paper 20 (new Phase 5z) re-audit shows Class TN findings auto-caught (theorem-name drift via ScalarRungInterpretation strengthening pass — the QI candidate that seeded Class TN)

---

## Wave 9c-followup — name_deps cache independence [planned 2026-04-26]

**Trigger.** Wave 9e shipped `EXTRACT_NAME_DEPS` env-var gating for the ~3-5min name_deps extraction cost. Cache is keyed on `.lean` source content only (see `scripts/extract_lean_deps.py:31`), not on the flag. Consequence: if you ran with `EXTRACT_NAME_DEPS=0`, setting `=1` later does not invalidate the cache — you get the old payload missing `name_deps_project`. User must manually `rm lean/lean_deps.json.hash`. Inconvenient + trap-prone.

**Ship plan (cheap, ~0.25d):**

- [ ] Sidecar artifact approach: split output into `lean/lean_deps.json` (basic decls, always extracted, ~7min) + `lean/lean_deps_proof_deps.json` (opt-in name_deps payload, +3-5min). Each file independently cached + hash-keyed.
- [ ] Basic cache hash = sha256 over `.lean` source content (same as today).
- [ ] Proof-deps cache hash = sha256 over `.lean` source content AND `EXTRACT_NAME_DEPS` flag value. Invalidates when either changes.
- [ ] `load_lean_deps()` loads basic unconditionally; new `load_lean_proof_deps()` loads sidecar iff present.
- [ ] Consumers opt into proof-deps data: build_graph.py `extract_uses_edges` reads sidecar; Wave 10b Class HD extended detection reads sidecar; basic `lean_deps.json` consumers untouched.
- [ ] Unblocks Class HD transitive-proof-dep walks without re-extracting the basic data; unblocks flipping `EXTRACT_NAME_DEPS` mid-session without manual cache invalidation.

**Deferred (Wave 11+):** per-module incremental ExtractDeps refactor so only changed modules re-walk. Currently the full 7655-decl walk runs on any single-file edit. Amortizes to O(decls in changed modules) after refactor. Larger surgery (~1-2d), not blocking Wave 10.

**Gate:** `rm lean/*.json lean/*.json.hash && EXTRACT_NAME_DEPS=0 uv run python -c 'from scripts.extract_lean_deps import load_lean_deps; load_lean_deps()'` produces basic artifact only; follow-up `EXTRACT_NAME_DEPS=1 uv run python -c 'from scripts.extract_lean_deps import load_lean_proof_deps; load_lean_proof_deps()'` extracts proof-deps sidecar without re-walking basic data.

---

## Wave 9h-followup — Datastar port for the Parameters tab [planned 2026-04-26]

**Trigger.** Wave 9h ported four tabs (`readiness_tab` / `qi_tab` / `chains_tab` / `paper_provenance_tab`) to Datastar. The original Provenance Command Center "Parameters" UI in `dashboard.html` was missed — at some prior checkpoint HTMX was removed from that tab and replaced with vanilla `fetch()` + a hand-rolled `safeSetHTML` DOM helper (see `scripts/templates/dashboard.html:996-1028`). The tab works, but it's the only remaining inconsistency with the rest of the dashboard's stack.

Surfaced 2026-04-26 during the Wave 10c change-bus implementation: when wiring the `/verify` endpoint to record verification events, the misleading "HTMX endpoint" docstring made the inconsistency visible.

**Ship plan (~0.5d):**

- [ ] Port the parameter cards in `dashboard.html` to Datastar `data-on:click="@post('/verify', {…})"` actions; replace `verifyParam(key, action, btn)` with a Datastar binding + signal updates.
- [ ] Convert `/verify` and `/save` responses from `text/html` fragments to Datastar SSE `patch_elements` events (or keep the JSON path for vanilla fetch and emit SSE on `Accept: text/event-stream`, matching the auto-negotiate pattern in `_pp_*_html` / `_pp_*_sse_events`).
- [ ] Drop the `safeSetHTML` helper (Datastar handles morph natively); keep the `<script>` block only for the keyboard nav + declaration-browser filter, OR move those to Datastar `data-on:keydown` bindings too.
- [ ] Smoke test: parameter confirm/reject/flag round-trip through Datastar; status badge updates without a full page reload; the change-bus event still records.

**Not blocking** Wave 10c (already shipped) or Wave 10d (Paper Provenance redesign uses the already-Datastar-ified tab). The `/verify` endpoint's change-bus behavior works identically before and after the port.

---

## Cross-phase coordination — Phase 5z research inputs

Phase 5v is process work; **Phase 5z is upstream physics deep research that produces papers needing the new prose-audit pipeline once Wave 10 lands**. Three deep-research deliverables landed 2026-04-24, queued as inputs to forthcoming Phase 5z Lean modules and papers:

1. **[Open Question O.2 — Wetterich-NJL Scalar-Channel ⇌ SM-Higgs structural resolution](../../../Lit-Search/Phase-5z/5z-Open Question 02-Structural.md)**
   Soft verdict: **Scenario A (doublet-compatible)**, structural-analogy strength 3/5. The BHL (Bardeen-Hill-Lindner 1990) construction provides the canonical SU(2)_L × U(1)_Y indexed extension of the Wetterich four-fermion scalar bond; Hill 2025 redux + Cvetič 1999 + Braun-Leonhardt-Pawlowski FRG-NJL series confirm structural transplantability. Output target: Lean module bridging `WetterichNJL.lean` to a gauge-indexed daughter; eventual paper. **Will need Wave 10 prose audit on first draft.**

2. **[Yukawa Couplings as Overlap Integrals on Volovik-Zubkov Fermi-Point Emergent Weyl Modes](../../../Lit-Search/Phase-5z/5z-Yukawa Couplings as Overlap Integrals on Volovik–Zubkov Fermi-Point Emergent Weyl Modes.md)**
   Honest gap: a closed-form Yukawa overlap `y_f = F(FermiPointData, EmergentGaugeData, σ-parameters)` does **not** exist in the published Volovik / Volovik-Zubkov / Selch-Zubkov / Wetterich literature. The deliverable explicitly recommends marking `ScalarRungInterpretation.lean` as carrying a *structural postulate* extending VZ2014 rather than a theorem inherited from primary literature. Direct relevance to **Wave 10 Class IA / TP / SD finding classes**: a paper claiming "we derive Yukawas as VZ overlap integrals" without the structural-postulate disclosure would be exactly the class of overclaim Wave 10's per-sentence rigor audit catches.

3. **[Phase 5z Wave 2 — Sterile-Neutrino Embedding for the Majorana Rung](../../../Lit-Search/Phase-5z/Phase 5z, Wave 2 — Sterile-Neutrino Embedding for the Majorana Rung.md)**
   Recommendation: **Embedding III (Hybrid)** — fundamental Lean field `ν_R : SterileNeutrino` with bridge predicate `MajoranaRung.is_substrate_composite` tying `M_R` to ADW tetrad-condensate scale Λ_ADW. Honest flag: no primary source closes the derivation `Λ_ADW → M_R = (10¹⁰–10¹⁴ GeV)`; recommends Lean signatures with `informal_lemma` axiom marking. Implies forthcoming `MajoranaRung.lean` + `NeutrinoMixing.lean` modules + papers documenting the Embedding-III decision — **subject to Wave 10 audit on submission**.

**Forward dependency.** Each Phase 5z deliverable will produce one or more papers. Those papers cite Lean theorems that don't yet exist in the project (`ScalarRungInterpretation.lean`, `MajoranaRung.lean`, `NeutrinoMixing.lean`, gauge-indexed `WetterichNJL` daughter). When the Lean modules land and papers are drafted, **Wave 10's claims-reviewer v2 + per-sentence audit + freshness watchdog become the trust gate** for these explicitly-novel results — the value of the rigor layer is highest precisely on papers proposing structural extensions beyond prior literature, where the temptation to over-claim "derived" / "proved" / "first" is strongest.

**Load-bearing finding classes for Phase 5z papers:**
- **Class TN (Theorem-name reference drift)** catches prose citing a Lean theorem name that changed or was removed between paper-drafting and Stage-13 re-invocation. The paper20 QI candidate that seeded this class surfaced exactly this pattern: ScalarRungInterpretation anti-tautology strengthening pass renamed/removed three theorems after the first paper draft landed. Every Phase 5z paper will go through the same risk at ingest — Class TN closes the loop.
- **Class HD (Hypothesis disclosure)** is essential for the `informal_lemma`-flagged theorems the Phase 5z deep research explicitly recommends (e.g., `MajoranaRung.is_substrate_composite`, Yukawa overlap VZ-extension postulates, Embedding-III `M_R = Λ_ADW` bridges). Each of these is a tracked `Prop` hypothesis; paper prose claiming "we derive" must disclose the hypothesis as an assumption per Gate 6. Class HD makes this structural + automatic.

The honest `informal_lemma` markers proposed in deliverables 1–3 should map cleanly to per-sentence `INTERPRETIVE` / `UNGROUNDED` tags in the Wave 10 schema, with Class HD fail-locking disclosures that are missing from paper prose.

---

## Execution Order & Estimates

| Wave | Blockers | Est. | Note |
|---|---|---|---|
| 0 | — | 0 (done) | Short-name fix landed this session |
| 1a | 0 | 0.25d | Mechanical rename + lake build |
| 1b | — | 0.5d | `update_counts.py` wiring |
| 1c | — | 1.5d | 6 extractors; some (ProductionRun log parsing) are tricky |
| 1d | — | ~0.5d (3-4h) | **Stale-reference detection (NEW 2026-04-26):** `paper_lean_refs` + `paper_hypothesis_disclosure` (offline) + `citation_live_resolution` (network, Stage-13 gated). Closes 2026-04-25 paper20 theorem-name QI + 2026-04-26 fabricated-citation QI. |
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
| 9h | — | 0 (done 2026-04-24) | **Datastar realignment** — 4 tabs ported (readiness/qi/chains/paper) + graph wrap; 60–70% LOC reduction per tab |
| 9c-followup-cache | — | 0.25d | name_deps sidecar file: basic `lean_deps.json` + opt-in `lean_deps_proof_deps.json` with flag-aware cache hash; unblocks Wave 10b Class HD transitive-proof-dep walks without re-extracting basic data |
| 10a | 9c-followup-cache | 1.25d | claims-reviewer v2: sentence-keyed schema (no derived views) + **five** finding classes (IA / TP / SD / TN / HD) + decoupled verdicts + reconciliation protocol (not silent supersession) + content-hash sentence IDs |
| 10b | 10a | 1.5d | KG schema delta: Sentence + AuditEvent + ClaimCluster nodes (ProseClaim retained), BACKED_BY (no human_state) + LOGGED_BY + MEMBER_OF edges (no pairwise SAME_CLAIM_AS), last_modified propagation, **`scripts/sentence_state.py` CLI as the only writer**, tombstone state |
| 10c | 10b | 0 (done 2026-04-26) | Cross-tab change-bus: verification_state.py log + apply_to_graph; /verify + POST /api/verification/event wired; cascade via existing dep edges; purple-stripe `pp-claim-span--stale` indicator + verdict-pill state. Bug fix to `_direct_last_modified` non-idempotency. |
| 10d | 10b, Wave 9g (renderer) | 2.5d | Paper Provenance redesign: 3-column layout, full-body LaTeX render, keyboard-first nav, per-link verification UI (power-mode toggle; default sentence-level), in-place link expansion, diff-since-last-verified, coverage ribbon, audit log pane with agent-identity chain |
| 10e | 10b | 0.5d | Adversarial-reviewer extension: Location field cites sentence_id; findings overlay onto Paper Provenance inspector |
| 10f | 10a × all-papers retrofit | 0.5d | Cross-paper ClaimCluster detection + MEMBER_OF edges + verify-once-propagate UX (cluster-membership traversal, no pairwise edges) |
| 10g | 10d | 0.25d | Retire Paper Contributions tab; deep-link from Readiness/QI/KG into Paper Provenance. (Structural validate.py CHECKs moved to Wave 1d 2026-04-26.) |
| 10h | 10a | 2h wallclock + agent batch | Retrofit run: re-run claims-reviewer-v2 on all 18 papers |

**Critical path:** Wave 1 → 2 → 3 → 4 → 5a → 4c → 6b → submission-gate functional. ~10 days focused work.

**Parallelizable tracks after Wave 2:**
- Adversarial agent (6a) can be authored while 3 is in progress
- External API (8) can proceed after 3 independently of 4/5/6/7

**Wave 9 (dashboard) current state (2026-04-24):** Waves 9a/b/c/d/e/f/g/h all landed. Wave 10 is the next major deliverable.

**Wave 10 (sentence-level prose audit + verification UX) sequencing:** 9c-followup-cache (sidecar name_deps) unblocks richer Class HD; 10a (claims-reviewer v2) and 10b (KG schema + CLI) must land first; they unlock 10c (change-bus), 10d (UI redesign), 10e (adversarial-reviewer hook). 10f (cross-paper SAME_CLAIM_AS) requires the retrofit (10h) to have run first so per-paper sentences exist. 10g (retirement + deep-link cleanup + structural validate.py checks) is small but should land last to avoid breaking deep-links during the migration.

**Critical path for Wave 10:** 9c-followup-cache → 10a → 10b → 10c → 10d → 10e → 10h (retrofit) → 10f → 10g. ~8.25 days end-to-end (post-feedback-expansion 2026-04-26).

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
- [x] Paper Provenance tab renders paper12_polariton end-to-end with live 8-layer verdicts per claim (Wave 9g + 9h)

**Wave 10 prose-audit goals (added 2026-04-24; revised 2026-04-26):**
- [ ] Every prose unit in every paper has a Sentence node with proposed chain or explicit UNGROUNDED tag (Wave 10a + 10h)
- [ ] Content-hash sentence IDs survive benign edits + section reorder; tombstone state preserves history for deleted prose (Wave 10a + 10b)
- [ ] Five finding classes live: Class IA + Class TP + Class SD + Class TN (theorem-name drift, from paper20 QI seed) + Class HD (hypothesis disclosure, from qi-assumptiondisclosure cluster) (Wave 10a)
- [ ] Agent verdict decoupled from human review state — WARN never triggered by missing human_verified_date (Wave 10a)
- [ ] Reconciliation protocol: non-reproducing prior findings land as human-ratifiable candidates; deterministic structural rechecks auto-close (Wave 10a)
- [ ] `scripts/sentence_state.py` CLI is the sole writer to `prose_state.json` + `audit_log.jsonl`; LLMs never free-form-edit (Wave 10b)
- [ ] AuditEvent `actor` field traces findings across multiple agents (claims-reviewer-v2, adversarial-reviewer, subsequent rounds) (Wave 10b)
- [ ] Per-link verification UI works for every chain-link type (default sentence-level verify; power-mode expands to per-link) (Wave 10d)
- [ ] Cross-tab change-bus auto-flips dependent sentences to NEEDS_RECHECK on any artifact verification (Wave 10c)
- [ ] Audit log surfaces full per-sentence verification history; events append-only and survive re-runs (Wave 10b + 10d)
- [ ] `validate.py --check paper_lean_refs` catches Class TN findings structurally without agent cost (**Wave 1d**)
- [ ] `validate.py --check paper_hypothesis_disclosure` catches Class HD findings structurally (**Wave 1d**)
- [ ] `validate.py --check citation_live_resolution` catches fabricated DOIs + wrong-arXiv via fuzzy-title-match (**Wave 1d**, Stage-13 gated)
- [ ] Paper 12 (reference) reaches 100% human_verified terminal state via the new UI; submission readiness check passes
- [ ] Paper 16 (worst coverage) drops from 30% UNGROUNDED to baseline ~9% after Wave 10c freshness machinery + agents re-run
- [ ] Paper 20 (Phase 5z W1) re-audit auto-catches ScalarRungInterpretation theorem-rename drift via Class TN (the QI candidate that seeded the class)
- [ ] Paper Contributions tab retired; deep-links from Readiness/QI/KG/Process Health all land in correct Paper Provenance state (Wave 10g)

**Wave 9c-followup goals (added 2026-04-26):**
- [ ] Name_deps extraction lives in opt-in sidecar `lean/lean_deps_proof_deps.json` with flag-aware cache hash; `EXTRACT_NAME_DEPS=1` flip does not invalidate the basic cache

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
- `docs/READINESS_GATES.md` — canonical 11-gate taxonomy
- `docs/QI_REGISTER.md` — Stage 14 process-improvement register (auto-generated)
- `docs/PAPER_TABLES_STATUS.md` — per-paper retrofit status of the table-autogeneration framework
- `docs/DASHBOARD.md` — provenance command center documentation
- `temporary/working-docs/reviews/papers/2026-04-12-Perplexity/SK_EFT_Hawking — Master Systematic Update Checklist.md` — source of the 13-dimension taxonomy
- `docs/roadmaps/Phase5u_Paper_Revision_Roadmap.md` — April paper-revision sibling track (content; 5v is process)
- `.claude/plugins/physics-qa/agents/claims-reviewer.md`, `figure-reviewer.md`, `adversarial-reviewer.md` — QA agents (claims-reviewer v2 redesign in Wave 10)
- `scripts/build_graph.py` (Wave 0 fix applied), `scripts/graph_integrity.py`, `scripts/provenance_dashboard.py` — implementation anchors

### Wave 10 design docs (drafted 2026-04-24, pre-implementation review)

- `temporary/working-docs/claims_reviewer_v2_design.md` — evolved claims-reviewer prompt + sentence-keyed schema migration plan
- `temporary/working-docs/sentence_kg_schema_delta.md` — KG schema additions: Sentence + AuditEvent nodes, BACKED_BY + SAME_CLAIM_AS + LOGGED_BY edges, last_modified propagation, validate.py extensions
- `docs/references/Datastar_Dashboard_Reference.md` — Datastar reference (used by Wave 9h port + Wave 10d redesign)

### Phase 5z deep research (forward dependencies of Wave 10's audit pipeline)

- [`Lit-Search/Phase-5z/5z-Open Question 02-Structural.md`](../../../Lit-Search/Phase-5z/5z-Open Question 02-Structural.md) — Wetterich-NJL ⇌ SM-Higgs structural resolution (Scenario A, 3/5 strength; BHL 1990 + Hill 2025 + FRG-NJL load-bearing)
- [`Lit-Search/Phase-5z/5z-Yukawa Couplings as Overlap Integrals on Volovik–Zubkov Fermi-Point Emergent Weyl Modes.md`](../../../Lit-Search/Phase-5z/5z-Yukawa Couplings as Overlap Integrals on Volovik–Zubkov Fermi-Point Emergent Weyl Modes.md) — Yukawa overlap integrals proposed extension to VZ2014 with explicit structural-postulate disclosure recommendation
- [`Lit-Search/Phase-5z/Phase 5z, Wave 2 — Sterile-Neutrino Embedding for the Majorana Rung.md`](../../../Lit-Search/Phase-5z/Phase 5z, Wave 2 — Sterile-Neutrino Embedding for the Majorana Rung.md) — Embedding III (Hybrid) recommendation with `informal_lemma` axiom marking; honest gap on Λ_ADW → M_R derivation
