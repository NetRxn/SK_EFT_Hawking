# The provenance dashboard — what the operator can see, and what it can change

> **Answers:** What does the operator control surface show, which of its actions persist, and where does it read each panel from?
>
> *(TODO-D8: this line is the required-content contract. `README.md`'s ownership
> table assigns this question to this document; `architecture_inventory_fresh`
> asserts the two agree verbatim, so the assignment cannot drift silently.)*

**Living document.** Start at [`README.md`](README.md). States no counts — the bundle roster,
the gate roster and the graph type lists are in [`SURFACE_INVENTORY.md`](SURFACE_INVENTORY.md).

**Companions:** [`QA_QI_INFRASTRUCTURE_MAP.md`](QA_QI_INFRASTRUCTURE_MAP.md) (where a human
actually decides) · [`VALIDATION_GATE_TOPOLOGY.md`](VALIDATION_GATE_TOPOLOGY.md) §6 (who writes
each field) · [`../KNOWLEDGE_GRAPH.md`](../KNOWLEDGE_GRAPH.md) (the graph schema).

⚠️ **Moved here 2026-08-12 (ADR-012 D22), and the move is the point.** This document sat outside
`docs/architecture/` and accumulated four false claims: two declared inputs that do not exist, a
stale bundle roster, and two API routes that were never implemented. Under this directory's
checks, a path that does not resolve is a hard failure and a census count in the narrative is a
hard failure — so the drift stops being free. Each false claim is corrected below and marked.

---

## What it cannot do — read this before trusting a green badge

⚠️ **The Parameters tab's confirm button does not persist.** `/verify` mutates the imported
`PARAMETER_PROVENANCE` dict in memory and writes only a change-bus event; the green
**HUMAN VERIFIED** badge it renders is byte-identical to a persisted one and reverts on reload.
`ParameterProvenance` is a P1 gate that blocks on that field, and there is no supported per-entry
writer for it — see [`VALIDATION_GATE_TOPOLOGY.md`](VALIDATION_GATE_TOPOLOGY.md) §6 for the full
ownership picture. **A control surface whose approve button does not persist is not yet the
sign-off tool**; repairing it is ADR-012 P9a.

⚠️ **The cross-tab change bus has never written a file.** `docs/verification_log.jsonl` is
described below as the bus's store; it **does not exist on disk** and is not gitignored, so the
freshness layer that depends on it is inert rather than merely empty.
[`END_TO_END_MAP.md`](END_TO_END_MAP.md) §6 names this as the reason.

## Quick Start

```bash
cd SK_EFT_Hawking
uv run python scripts/provenance_dashboard.py          # http://localhost:8050
uv run python scripts/provenance_dashboard.py --port 8051  # custom port
```

### Prerequisites

- `uv sync` to install dependencies
- For the Knowledge Graph tab: PG+AGE container (`docker/docker-compose.graph.yml`)

## Tabs

### Parameters

Card-based view of experimental parameter provenance. Each card shows:
- Parameter key, code value, provenance value, unit
- Tier badge (MEASURED / EXTRACTED / DERIVED / PROJECTED / THEORETICAL)
- Verification status (HUMAN VERIFIED / LLM VERIFIED / UNVERIFIED / CONFLICT)
- Source citation with DOI link
- LLM-extracted excerpt (when available)
- Papers that use this parameter
- Confirm / Reject / Flag action buttons with notes field

**Filters:** Status (all/verified/unverified/conflict), Tier (all/measured/projected/...), Paper

### Formulas

Table of Python formulas from `src/core/formulas.py`. Columns:
- Function name and line number
- Description (first 80 chars of docstring)
- Lean theorem reference (green if present, red MISSING if not)
- Aristotle run ID
- Source citation

### Proof Architecture

Replaces the former Lean/Aristotle tab. Shows the full Lean declaration taxonomy with axiom tracking.

**Summary bar:** Declaration count pills (Axioms, Theorems, Defs, Structures, Inductives, Instances) with total and module counts.

**Axiom Command Panel:** One card per project axiom. Card border color indicates eliminability:
- Green left border = eliminable (can be pushed to first principles)
- Amber left border = hard to eliminate (known limitation)

Each axiom card shows: name, location, eliminability badge, full type signature, blast radius (downstream theorem count), paper dependency, core axiom dependencies, expandable dependency tree, and "View in KG" cross-link.

**Core Axioms Toggle:** Collapsed section showing Lean's foundational axioms (propext, Classical.choice, Quot.sound) with usage counts.

**Declaration Browser:** Table of all Lean modules sorted by total declaration count. Columns: Module, Axioms, Thms, Defs, Structs, Inds, Insts, Total. Kind filter pills allow filtering by declaration type. Modules containing axioms are highlighted.

**Hypothesis Command Panel:** One card per entry in `HYPOTHESIS_REGISTRY` (constants.py). Card border color indicates eliminability (green = algebraic, amber = hard, red = very_hard). Each card shows: hypothesis name, mathematical statement, status (active/proposed/eliminated), eliminability, dependent theorems, source citation, risk assessment, and circularity notes. This tracks load-bearing unproved inputs that enter as theorem parameters, not global axioms.

**Structure Field Assumptions:** Collapsed section listing structures with Prop-valued fields — these are implicit physics hypotheses (e.g., `FluidBackground.soundSpeed_pos : 0 < soundSpeed x`).

### Paper Claims

Paper readiness cards. Each card shows:
- Paper title and topic
- Submission readiness badge (READY / BLOCKED / PENDING HUMAN REVIEW / NO PARAM DEPS)
- Figure count, formula dependency count, bibliography entries
- Key claims list
- Lean verification details (theorem counts per module, Aristotle counts)
- Formula dependencies (expandable)
- Parameter verification progress bar with per-parameter badges

### Citation Registry

Table of all entries from `CITATION_REGISTRY` in `src/core/citations.py`. Columns:
- Citation key, authors, reference string
- DOI link (clickable)
- arXiv link (clickable)
- Usage count (files referencing this citation)
- Provides (what this source contributes — parameters, formulas, etc.)

### Knowledge Graph

Interactive D3 force-directed provenance graph. See `docs/KNOWLEDGE_GRAPH.md` for full documentation.

Key features: 4 layouts (Force/Radial/Hierarchy/Circle), 3 modes (Explore/Trace/Impact), Paper Focus, Logical Focus, shape-encoded semantic roles, Scaffolding toggle, physics controls, detail panel.

### Readiness / QI _(Phase 5v Wave 4–5)_

Per-paper × readiness-gate matrix backed by `scripts/readiness_gates.py` and the `ReadinessGate` graph nodes (roster and priorities: [`SURFACE_INVENTORY.md`](SURFACE_INVENTORY.md#readiness-gates)). Each cell renders the gate's current state (`green` / `amber` / `red` / `needs-recheck`). Sibling QI sub-pane surfaces the QI register (`docs/QI_REGISTER.md`) with action items binned by severity. Driven by the `/api/readiness` SSE endpoint.

⚠️ **CORRECTED 2026-08-12.** This section claimed "click-through to gate-specific evidence (Lean theorems, parameter provenance, production runs, review findings)". **Blockers render as unlinkable prose:** the evaluator holds the whole `ReviewFinding` and keeps 60 characters of its label, so the id is destroyed before the graph sees it and the dashboard touches no `FLAGS` edge at all. There is nothing to click through *to*. ADR-012 P9a S1 builds it; this line becomes true in that commit and not before.

⚠️ **The QI sub-pane is empty by construction.** The derivation keys a register item on the gate name alone, so it can hold at most one item per gate for all time — and most gates are already in `## Closed Items` and can never re-emit. Findings go in and nothing comes out. [`END_TO_END_MAP.md`](END_TO_END_MAP.md) §8 names the cause; ADR-012 P9a repairs it.

### Chains _(Phase 5v)_

Provenance chain inspector. Lists named provenance chains (paper claim → formula → Lean theorem → axioms / hypotheses → primary source) and lets a reviewer step through each link. Companion to the KG tab's Trace mode but linearised for sentence-level audit work.

### Bundles _(Phase 6i Wave 7.5)_

Per-publication-bundle readiness panel over the bundle roster — which is `scripts/bundle_registry.BUNDLE_CODES`, never a hand-written list (`bundle_registry_consistency` Leg C exists because that pattern is known-bad). Sourced from `scripts/datastar_bundles.py`, which assembles per-bundle data from `docs/PAPER_DRAFT_MAPPING.md`, `papers/cluster_bundle_index.json` (cross-bundle ClaimCluster index) and per-paper readiness output. Each bundle card shows: cluster membership, source-freshness flag (`bundle_source_freshness`), Stage-13 reviewer-triple status, and a submission-event log. Submission events are recorded via the tab's inline form (or by POSTing to `/api/bundles/<bundle>/submission_event`).

⚠️ **CORRECTED 2026-08-12, twice over.** This section said "the 18-bundle architecture (1 flagship F + 9 Tier 1 deep + …)" — a hand-written roster **and** a census count in a narrative, both of which this directory forbids; the live roster is larger and the tier split had drifted. It also named `docs/submission_state.json` as an input: **that file does not exist and is not gitignored**, so the submission-event log has no store behind it.

### Paper Provenance v2 _(Phase 5v Wave 10)_

Sentence-level chain-of-backing inspector. Renders the prose of a chosen paper as a stream of `Sentence` nodes (`sentence:<paper>:<section_slug>:<sha8>`), each with its chain to Formula / LeanTheorem / Parameter / PrimarySource / Hypothesis / AristotleRun / ProductionRun artifacts.

⚠️ **CORRECTED 2026-08-12.** This said the chains are the sentences' **`BACKED_BY`** edges. The dashboard contains **zero** occurrences of `BACKED_BY`: the tab reconstructs each chain from `papers/<p>/claims_review.json` (`_pp_sentence_chain_link_states`), reading no graph edge at all. The distinction matters for anything built on top — a sentence-to-finding resolution has to be *built*, not queried, which is why ADR-012 P9a S4 is a task rather than a render change. Per-link verify buttons fire `/api/verification/event` with a `triggered_by: <sentence_id>` field so the audit trail records cross-tab provenance. Right-side drawer shows the `AuditEvent` log (`LOGGED_BY` edges) for the focused sentence, including `re_audit` chains across multiple agent runs. Cluster siblings (cross-paper `ClaimCluster` membership via `MEMBER_OF`) surface inline.

## API Endpoints

**The routes are declared by `@app.route` in `scripts/provenance_dashboard.py`; read them there rather than trusting a table.** The ones a reader is most likely to reach for:

| Endpoint | Method | Returns |
|----------|--------|---------|
| `/` | GET | Dashboard HTML (tab selected via `?tab=` param) |
| `/verify` | POST | Verify/reject/flag a parameter — ⚠️ **in memory only**, see the warning above |
| `/api/graph` | GET | Full graph JSON `{nodes, links, meta}` |
| `/api/graph/trace/<path:node_id>` | GET | Traced node/edge IDs for provenance chain |
| `/api/graph/impact/<path:node_id>` | GET | Impacted node/edge IDs for upstream dependents |
| `/api/graph/integrity` | GET | Integrity report (orphans, conflicts, chains) |
| `/api/readiness` | GET | SSE stream backing the Readiness / QI tab |
| `/api/bundles/<bundle>/submission_event` | POST | Record a submission event |
| `/api/verification/event` | POST | Change-bus event (⚠️ writes no file — see above) |

⚠️ **CORRECTED 2026-08-12.** The table named **`/api/verify`**, which does not exist — the route is
`/verify` — and **`/api/save`**, *"Save accumulated verification actions"*, which has never existed:
the string appears nowhere in the app. A documented endpoint that was never implemented is worse
than an undocumented one, because it reads as a persistence path a reviewer might believe in.

Node IDs containing colons (e.g., `param:Steinhauer.omega_perp`) are handled via Flask `<path:node_id>` routes.

## Architecture

```
Python registries +          build_graph.py           Flask API           Dashboard (Datastar)
prose / audit JSON     -->   (node + edge types  -->  /api/graph     -->  Parameters
(constants.py,                are censused in          /api/trace          Formulas
 provenance.py,               SURFACE_INVENTORY.md;    /api/impact         Proof Architecture
 citations.py,                build_graph.py is        /api/integrity      Paper Claims
 formulas.py,                 authoritative)           /api/readiness      Citation Registry
 lean_deps.json,                                       /api/bundles/...    Knowledge Graph (D3)
 papers/<p>/claims_review.json,                        /api/verification/  Readiness / QI
 papers/<p>/audit_log.jsonl,                           /api/papers/<p>/    Chains
 papers/<p>/prose_state.json,                              provenance      Paper Provenance v2
 papers/claim_clusters.json,                                               Bundles
 papers/cluster_bundle_index.json,                          |
 review_figures.py)                                         v
                                                      PG+AGE (parallel
                                                       rebuildable mirror;
                                                       sk_eft graph on :5433)
```

Schema spans Phase 1 / 1.5 base types + Phase 5v Wave 2a readiness-system types + Phase 5v Wave 10b sentence-level types (`Sentence`, `AuditEvent`, `ClaimCluster` + `BACKED_BY`, `LOGGED_BY`, `MEMBER_OF`). For the canonical type list always defer to `scripts/build_graph.py`. JSON-on-disk is the source of truth; PG+AGE is a rebuildable mirror, not a writer.

## Files

| File | Purpose |
|------|---------|
| `scripts/provenance_dashboard.py` | Flask app, data loading, API endpoints |
| `scripts/templates/dashboard.html` | Main template (all tabs except KG) |
| `scripts/templates/partials/graph_tab.html` | D3 knowledge graph visualization |
| `scripts/build_graph.py` | Graph extraction from registries |
| `scripts/extract_lean_deps.py` | Lean declaration extraction wrapper |
| `scripts/graph_integrity.py` | Integrity checker |

## Keyboard Shortcuts

- `j` / `k` — navigate parameter cards (Parameters tab)
- `y` — confirm current parameter
- `n` — reject current parameter
- `f` — flag current parameter

## Bundle readiness command _(2026-05-07)_

```bash
# Regenerates docs/BUNDLE_READINESS_HEATMAP.md (gate × bundle matrix).
uv run python scripts/bundle_readiness.py --heatmap

# Full per-bundle pass (per-paper rollup + heatmap).
uv run python scripts/bundle_readiness.py
```

The Bundles tab consumes the same per-bundle aggregation that this script writes, sourced through `scripts/datastar_bundles.py` (`PAPER_DRAFT_MAPPING.md` + `papers/cluster_bundle_index.json` + per-paper readiness output). The heatmap markdown is the human-readable mirror; the dashboard renders the live in-memory snapshot, so a bundle's state on disk and on screen agree as long as `scripts/bundle_readiness.py` has been run since the last gate-flipping change.

## Sentence-level provenance _(Phase 5v Wave 10b–10c, 2026-05-07)_

The Paper Provenance v2 tab and the Bundles tab both rely on a tightly enforced write-path discipline:

- **Sole writer for prose / audit state:** `scripts/sentence_state.py` (CLI). All mutations to `papers/<paper>/prose_state.json` and `papers/<paper>/audit_log.jsonl` route through this command — no free-form JSON edits, no ad-hoc scripts. Schema validation, file-lock, and atomic writes are enforced at this chokepoint.
- **Cross-tab change-bus:** verification actions on artifacts (parameters / citations / axioms / hypotheses / aristotle runs / production runs) flow through `scripts/verification_state.py` → `docs/verification_log.jsonl`. ⚠️ **That file does not exist**, so everything described in this bullet and the next two is a design that has never carried an event. The library is real; its store has never been written. The Parameters tab's confirm/reject flow and Paper Provenance v2's per-link verify buttons are both delegates of this same library API. Each event annotates `meta.last_modified_explicit` on the corresponding KG node, propagating upstream so dependent `Sentence` nodes flip to `NEEDS_RECHECK` automatically when their backing artifacts re-verify.
- **`triggered_by` for cross-tab provenance:** verification events fired from a sentence's per-link UI carry `triggered_by: <source_sentence_id>`, so the audit trail surfaces "fired from sentence X's chain inspector" vs an opaque "Parameter X confirmed". Audit-log diffs render an inline `⚲ self` (self-triggered) or `↗ <other_sid>` badge. Field is `null` for events from the Parameters tab or the CLI.
- **Replay-canonical recovery:** the audit log is the canonical record. If a `cmd_mark` succeeds at the audit-event write but fails at the prose_state update (rare partial-failure), `scripts/sentence_state.py rebuild_prose_state --paper <id> --check` walks events in timestamp order and reports drift; `--write` atomically replaces `prose_state.json` with the rebuilt content.
- **Retention policy:** `docs/verification_log.jsonl` is append-only. `read_events` emits a one-shot WARN to stderr when the file exceeds 1 MB recommending `scripts/verification_state.py prune --keep-days 90` (default retention). `prune` refuses to operate without a retention criterion (`--keep-days N` / `--keep-records N` / `--before <ISO-8601>`). `--archive-to <path>` appends pruned events to a sidecar JSONL for recovery.
