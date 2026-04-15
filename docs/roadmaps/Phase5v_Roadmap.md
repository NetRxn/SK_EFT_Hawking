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
- [x] `extract_review_finding_nodes` + `extract_flags_edges` → ReviewFinding + FLAGS (Wave 2d — DONE; 56 findings extracted from 4 Perplexity review docs, 34 FLAGS→Paper edges inferred from body text; severity/status classification coarse — refinement deferred to Wave 6 when adversarial-reviewer emits structured output natively)
- [x] `extract_production_run_nodes` → ProductionRun (Wave 2e — DONE; 14 runs extracted; status heuristic from paired .log tail). PRODUCES edges deferred to Wave 4 where run-to-claim mapping is curated.
- [x] `extract_placeholder_marker_nodes` → PlaceholderMarker (Wave 2b — DONE)
- [ ] Widen PaperClaim with `kind ∈ {numeric, theorem-cite, prose}` + ProseClaim subtype (Wave 2f)

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

## Wave 4 — Readiness state machine

### Wave 4a — Gate extraction

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

### Wave 4b — Auto-invalidation

- [ ] `build_graph.compute_source_hash()` already hashes canonical sources. Extend: per-node content hash
- [ ] When any node's content hash changes vs. last graph build, walk `IMPACTED_BY` reverse edges; flip each dependent ReadinessGate to `needs-recheck`
- [ ] `IMPACTED_BY` edges are generated from the gate evaluator's `evidence` list: every node cited as evidence implicitly creates an `IMPACTED_BY` from gate to evidence

### Wave 4c — Pre-submit enforcement

- [ ] New `validate.py` CHECK 18: `readiness_submission_gate` — for each paper marked `submission_pending` in metadata, all P1 gates must be `passed`; P2 gates `passed` or `accepted-with-note`
- [ ] Paper submission workflow requires CHECK 18 green before `pre-submit.sh` (if/when we create such a script) succeeds

**Gate:** All 165 gate instances evaluate on `build_graph.py` run; dashboard shows per-paper state; upstream change to any parameter/formula/claim flips affected gates visibly.

---

## Wave 5 — Dashboard readiness surface

### Wave 5a — Readiness tab

- [ ] New tab: "Paper Readiness" alongside existing 6 tabs
- [ ] Heatmap: rows = papers, columns = 11 gates, cells colored by state
- [ ] Paper focus: click paper row → full gate detail (evidence chain, blockers, last-evaluated)
- [ ] Filter: "papers blocked by gate X" / "papers needs-recheck"
- [ ] Trend chart: gates-passed over time (reads CountMetric + historical snapshots)

### Wave 5b — Graph-tab integration

- [ ] Add 3rd traversal mode: "Readiness" (alongside Explore / Trace / Impact) — click any node, see which ReadinessGates reference it as evidence
- [ ] ReviewFinding nodes render with distinct shape/color; severity visible in size
- [ ] SUPPORTS edges: green-dashed; CONTRADICTS edges: red-dashed (complement)
- [ ] Paper focus dropdown, extended: each paper shows a mini-pill summary of its 11 gates inline

### Wave 5c — Action buttons

- [ ] "Mark reviewed" — transitions gate state (Wave 3c write-back)
- [ ] "Accept with note" — P2 gates only; records a justification
- [ ] "Trigger adversarial review" — manually kicks Stage 13 for a specific paper

**Gate:** Dashboard tab live; `localhost:8050/?tab=readiness` renders; write-back via Wave 3c works; visual review surfaces a dashboard screenshot for each paper matching the 11-gate state.

---

## Wave 6 — Stage 13: Internal adversarial review

### Wave 6a — Agent definition

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

### Wave 6b — Pipeline integration

- [ ] Add Stage 13 to `docs/WAVE_EXECUTION_PIPELINE.md`: *"Internal adversarial review. After all Stage 1–12 gates pass, invoke `adversarial-reviewer` for each paper approaching submission. Fresh-context Opus run; reads only what it discovers via grep/read; emits structured JSON."*
- [ ] Output of Stage 13 → `extract_review_finding_nodes` picks up from `papers/AutomatedReviews/{date}-internal-adversarial/*.md`
- [ ] Loopback rule: any P1-severity finding reopens the relevant ReadinessGate → paper cannot advance until fix + Stage 13 re-run shows clean
- [ ] Loopback rule (P2): paper can advance with WARN acknowledged by user, but finding remains in graph as `status=accepted-with-note`

### Wave 6c — Triggering

- [ ] On-demand: dashboard "Trigger adversarial review" button (Wave 5c)
- [ ] Scheduled: pre-submit gate (CHECK 18) — adversarial review must have run within last 7 days against current paper content hash
- [ ] Optional cron via `scripts/schedule.py` (existing `schedule` skill infrastructure) — weekly sweep of all "near-submission" papers

**Gate:** Adversarial agent installed; runs clean against a known-fixed paper (Paper 7 post-TPF-fix); catches at least 5 known issues in unfixed papers when tested against April-review-preserved state; pipeline Stage 13 documented; loopback tested.

---

## Wave 7 — Stage 14: Meta-process Quality Improvement register

**Distinction from Stage 13.** Stage 13 catches paper-level issues. Stage 14 catches **process-level** issues — recurring patterns across multiple papers or review rounds that indicate a pipeline gap (e.g., "bounds-only tests allowed a 10⁷× bug through", "fix-propagation lag across companion papers"). Stage 14 feeds improvements back into the pipeline itself.

### Wave 7a — QI register

- [ ] `docs/QI_REGISTER.md` — auto-generated from `ReviewFinding` + `Contradiction` nodes whose `pattern_class` is process-level (not paper-local)
- [ ] Each QI item: `{id, pattern, first_observed, occurrences, owner, target_date, status, evidence_on_close, pipeline_stage_affected}`
- [ ] Classification heuristic: if a finding recurs across ≥2 papers, it becomes a QI item candidate
- [ ] User-facing report emitted on each Stage 14 run: `docs/QI_REGISTER_{date}.md` (timestamped snapshot)

### Wave 7b — Dashboard "Process Health" tab

- [ ] Open QI items count, grouped by `pipeline_stage_affected`
- [ ] Trend: findings-per-category-per-month over time (is the pipeline getting better or drifting?)
- [ ] Click QI item → full evidence (all findings that contributed to the pattern detection), linked commits (when resolved)
- [ ] `FixPropagation` gate (gate #11) reads from QI register — if a QI item is `status=open` with a target_date in the past, affected papers flagged

### Wave 7c — Pipeline integration

- [ ] Add Stage 14 to `docs/WAVE_EXECUTION_PIPELINE.md`: *"After Stage 13. Scans all `ReviewFinding` nodes for recurring patterns. Emits QI items + updates `docs/QI_REGISTER.md`."*
- [ ] Stage 14 is advisory — never blocks submission — but emission generates a user notification
- [ ] Loopback: if a QI item is `severity=critical` (e.g., a pipeline gate that allowed a correctness violation), Wave 1b/1c-style remediation waves are suggested

**Gate:** QI register populated from the 13-dimension April findings as seed data; dashboard tab renders; user receives first generated report.

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

**Critical path:** Wave 1 → 2 → 3 → 4 → 5a → 4c → 6b → submission-gate functional. ~10 days focused work.

**Parallelizable tracks after Wave 2:**
- Adversarial agent (6a) can be authored while 3 is in progress
- External API (8) can proceed after 3 independently of 4/5/6/7

---

## Success Criteria (end of Phase 5v)

- [ ] All 13 April-review failure modes are caught by at least one ReadinessGate in the current graph
- [ ] Dashboard readiness tab shows all 15 papers × 11 gates; current state visible at a glance
- [ ] Running Stage 13 adversarial review against a known-bad paper (e.g., pre-fix Paper 7) flags the TPF citation issue; running against a known-good paper clears cleanly
- [ ] `validate.py` CHECK 17 (graph parity) and CHECK 18 (readiness submission gate) pass in CI
- [ ] `counts.json` is the single source of truth for every count reference in every paper
- [ ] `docs/QI_REGISTER.md` tracks the seed findings from April; first regenerated report emitted to user
- [ ] PG+AGE is source of truth; Python registries are regenerated artifacts
- [ ] No silent drops, no silent collisions, no silent misses — every gap emits a log line

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
