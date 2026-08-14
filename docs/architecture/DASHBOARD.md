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

✅ **The Parameters tab's three buttons all persist (ADR-012 P9a, 2026-08-12).** Confirm, Reject
and Flag route through `src.core.provenance_writer`, the single per-entry writer, and the badge
is rendered **only when the write returns ok** — a refusal renders as a refusal.

⚠️ **This section read "the confirm button does not persist" for several hours after it did**,
which is the drift rule 2 exists to prevent, in the document governing the surface that was
repaired. What it described was real: `/verify` mutated the imported dict in memory, wrote only
a change-bus event, and rendered a green **HUMAN VERIFIED** badge byte-identical to a persisted
one — on the field a P1 gate blocks on.

⚠️ **Reject and Flag were fixed second, and their absence was WORSE than the original defect.**
With only Confirm persisting, Reject cleared the date in memory, rendered a red badge, and left
the verification on disk — still green to the gate, with no route to withdraw it. Sign-off
stuck and retraction evaporated; before the writer existed, both were equally ephemeral and the
surface was at least uniformly honest. See
[`VALIDATION_GATE_TOPOLOGY.md`](VALIDATION_GATE_TOPOLOGY.md) §6 for field ownership.

⚠️ **The cross-tab change bus is EMPTY, not inert — and the distinction was measured the hard
way.** `docs/verification_log.jsonl`, the bus's store, is absent from a clean checkout, and an
earlier version of this very section read *"the bus has never written a file, which is stronger
than 'never carried an event'"*. **That was wrong about the mechanism.** The browser test added
for ADR-012 P9a Task 5 clicked Confirm once, and the bus wrote its first event immediately and
correctly. The file was absent because **nobody had ever exercised the confirm path in this
checkout**, not because the writer is broken.

The freshness layer downstream is therefore **unexercised**, which is a much cheaper problem than
inert — and the correction is worth keeping because *"the artifact is missing"* and *"the mechanism
does not work"* are exactly the two readings that a missing file cannot distinguish between.
The log is a runtime artifact and is gitignored, alongside the harness's other per-run logs.

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

**A blocker in the focus pane carries the identity of the finding behind it** — its id, severity, lane and target, as `data-finding-id` / `data-lane` / `data-severity` on each entry (ADR-012 D15 S1). `FixPropagation` is the only gate that reads `FLAGS`, so it is the only one that can populate them; a gate whose evaluator has no node to name renders its prose list **and says that is what it is**, so an un-drillable blocker is visibly a different thing from a drillable one.

⚠️ **The pane shows ten and states the total** (`showing 10 of 44`). The cap used to sit in the evaluator, which meant nothing downstream could tell ten blockers from forty-four — and a total computed there would have reported ten and called itself a disclosure. **A cap can only be disclosed by a layer that can still see what it cut**, so the evaluator now keeps everything, the node payload bounds and states both figures, and the pane bounds the display.

⚠️ **CORRECTED 2026-08-12.** This section previously claimed "click-through to gate-specific evidence (Lean theorems, parameter provenance, production runs, review findings)" while blockers rendered as unlinkable prose — the id was destroyed in the evaluator, which held the whole `ReviewFinding` and kept 60 characters of label. The claim above is the repair, and it is narrower than the sentence it replaces: **review findings drill through; Lean theorems, parameter provenance and production runs still do not.**

⚠️ **The QI sub-pane is empty by construction.** The derivation keys a register item on the gate name alone, so it can hold at most one item per gate for all time — and most gates are already in `## Closed Items` and can never re-emit. Findings go in and nothing comes out.

✅ **REPAIRED (ADR-012 P9a, 2026-08-12), and the sentence above understated the cause.** The gate-keyed id was one of **three** causes, not the one: `unclassified` — the largest single bucket — was dropped rather than reported, and the clustering partitioned on `inferred_paper` alone, so every finding carrying only `inferred_bundle` collapsed onto one sentinel. An item now identifies a **recurrence** (gate, paper set, window) and a closure suppresses its own window rather than its gate forever; the derivation went from zero items to 23. [`END_TO_END_MAP.md`](END_TO_END_MAP.md) §8 carries the full account and the one part still open — `## Open Items` is rebuilt rather than preserved.

### Chains _(Phase 5v)_

Provenance chain inspector. Lists named provenance chains (paper claim → formula → Lean theorem → axioms / hypotheses → primary source) and lets a reviewer step through each link. Companion to the KG tab's Trace mode but linearised for sentence-level audit work.

### Bundles _(Phase 6i Wave 7.5)_

Per-publication-bundle readiness panel over the bundle roster — which is `scripts/bundle_registry.BUNDLE_CODES`, never a hand-written list (`bundle_registry_consistency` Leg C exists because that pattern is known-bad). Sourced from `scripts/datastar_bundles.py`, which assembles per-bundle data from `docs/PAPER_DRAFT_MAPPING.md`, `papers/cluster_bundle_index.json` (cross-bundle ClaimCluster index) and per-paper readiness output. Each bundle card shows: cluster membership, source-freshness flag (`bundle_source_freshness`), Stage-13 reviewer-triple status, and a submission-event log. Submission events are recorded via the tab's inline form (or by POSTing to `/api/bundles/<bundle>/submission_event`).

⚠️ **CORRECTED 2026-08-12, twice over.** This section said "the 18-bundle architecture (1 flagship F + 9 Tier 1 deep + …)" — a hand-written roster **and** a census count in a narrative, both of which this directory forbids; the live roster is larger and the tier split had drifted. It also named `docs/submission_state.json` as an input: **that file does not exist and is not gitignored**, so the submission-event log has no store behind it.

### Flow · Attention · Loops _(ADR-012 P9b/P9c, 2026-08-13)_

The three operator panes, `?tab=flow` · `?tab=attention` · `?tab=loops`. Each is rendered by
its own partial from the data layer described under *The ADR-012 operator surfaces* below;
`index()` builds only the pane whose tab is selected, since each walks the whole graph.

⚠️ **The five non-verdict cell kinds render hatched-grey, not green or red.** `not-tracked`,
`unmeasured`, `missing`, `undeclared` and `warning` are not verdicts, and painting them as
verdicts at the render layer would undo, invisibly, the refusal the data layer is built
around. On failure the panes render an **error**, never an empty pane — `flow_board()` itself
raises rather than returning a board with no rows.

### Paper Provenance v2 _(Phase 5v Wave 10)_

Sentence-level chain-of-backing inspector. Renders the prose of a chosen paper as a stream of `Sentence` nodes (`sentence:<paper>:<section_slug>:<sha8>`), each with its chain to Formula / LeanTheorem / Parameter / PrimarySource / Hypothesis / AristotleRun / ProductionRun artifacts.

⚠️ **CORRECTED 2026-08-12.** This said the chains are the sentences' **`BACKED_BY`** edges. The dashboard contains **zero** occurrences of `BACKED_BY`: the tab reconstructs each chain from `papers/<p>/claims_review.json` (`_pp_sentence_chain_link_states`), reading no graph edge at all. The distinction matters for anything built on top — a sentence-to-finding resolution has to be *built*, not queried, which is why ADR-012 P9a S4 is a task rather than a render change. Per-link verify buttons fire `/api/verification/event` with a `triggered_by: <sentence_id>` field so the audit trail records cross-tab provenance. Right-side drawer shows the `AuditEvent` log (`LOGGED_BY` edges) for the focused sentence, including `re_audit` chains across multiple agent runs. Cluster siblings (cross-paper `ClaimCluster` membership via `MEMBER_OF`) surface inline.

## The ADR-012 operator surfaces — data layers, separate from the app

⚠️ **These live in their own modules, and that is deliberate.** `provenance_dashboard.py` was
already large enough that another four panes inside it would have made every one of them
harder to reason about. Each module below is **pure data — no HTML** — so it can be tested
without booting a server, and the app wires it.

⚠️ **"AND THE APP WIRES IT" WAS FALSE WHEN WRITTEN, FOR THREE OF THE FOUR, AND STAYED FALSE
FOR A DAY.** `dashboard_flow.py`, `dashboard_attention.py` and `dashboard_loops.py` shipped as
2,360 lines that nothing but their own tests imported — no route, no template, no reachable
surface — and **every gate was green**, because an unreferenced module is not a broken
reference, a template-contract test needs a template, and a browser test needs a route.
Wired 2026-08-13 (P9b/P9c: three partials, three tab links, a lazy per-tab build in
`index()`), with both gates D2 requires for dashboard work. The sentence is kept, and this
note beside it, because *pure data, and the app wires it* is a two-part claim whose second
half nothing in the suite was checking.

| module | surface | what it refuses to do |
|---|---|---|
| `scripts/sentence_findings.py` | **S4 — reading-while-blocked.** Marks a sentence when an open finding's `Location:` line range overlaps it | Resolve via `FLAGS`. Every one of those edges targets a `paper:` node, so the marker would render on **no sentence, ever**, and its emptiness would be indistinguishable from a clean corpus |
| `scripts/dashboard_flow.py` | **S2 — the Flow board.** Bundle rows × stage columns, with an open-findings overlay broken down by `lane` | Coerce an unrecognised status to the nearest known one, treat §7.5 as anything but *not tracked*, or present the two known-soft signals (TODO-D50/D51) as authoritative |
| `scripts/dashboard_attention.py` | **S3 — Attention.** The four feeds, side by side | **Merge them.** Different stores, vocabularies and actions; flattening destroys the only property that makes each legible |
| `scripts/dashboard_loops.py` | **P9c — Loops.** `/goal`-level activity from harness state | Render an empty roster as "no loops running". `.claude/dev-harness/` is gitignored, so *nothing known* and *nothing armed* are different answers |

**Every one of them reports what it CANNOT see, beside what it can.** `coverage()` returns the
population the layer reaches *and* the population it does not, and asserts the two partition —
the same discipline the readiness ratchets use, for the same reason: a partition asserted in
prose drifts, and a surface that is silent about its blind spot reads as complete.

⚠️ **S4's marker is a floor, not a total.** Markers cover only the findings whose `Location:`
names a draft line; the rest carry no location or point outside the manuscripts entirely. **An
unmarked sentence is not evidence of a clean sentence**, and the pane says so on its face.

⚠️ **Three states, not two, wherever a thing can be unknown.** A sentence with no line span
(question never asked) versus one with no findings (asked and clean); a loop roster that is
absent versus empty; a Stage-13 review kind that is undeclared versus a bundle never reviewed.
Collapsing any of these pairs renders *unknown* and *fine* identically.

## API Endpoints

**The routes are declared by `@app.route` in `scripts/provenance_dashboard.py`; read them there rather than trusting a table.** The ones a reader is most likely to reach for:

| Endpoint | Method | Returns |
|----------|--------|---------|
| `/` | GET | Dashboard HTML (tab selected via `?tab=` param) |
| `/verify` | POST | Verify/reject/flag a parameter — persists via `src.core.provenance_writer`; the badge renders only when the write returns ok |
| `/api/graph` | GET | Full graph JSON `{nodes, links, meta}` |
| `/api/graph/trace/<path:node_id>` | GET | Traced node/edge IDs for provenance chain |
| `/api/graph/impact/<path:node_id>` | GET | Impacted node/edge IDs for upstream dependents |
| `/api/graph/integrity` | GET | Integrity report (orphans, conflicts, chains) |
| `/api/readiness` | GET | SSE stream backing the Readiness / QI tab |
| `/api/bundles/<bundle>/submission_event` | POST | Record a submission event |
| `/api/verification/event` | POST | Change-bus event → `docs/verification_log.jsonl` (a gitignored runtime artifact; absent until the path is exercised) |

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
| `scripts/templates/dashboard.html` | Main template (nav + the tabs with no partial) |
| `scripts/templates/partials/graph_tab.html` | D3 knowledge graph visualization |
| `scripts/templates/partials/bundles_tab.html` · `chains_tab.html` · `paper_provenance_tab.html` · `qi_tab.html` · `readiness_tab.html` | the Datastar-driven tab bodies |
| `scripts/templates/partials/flow_tab.html` · `attention_tab.html` · `loops_tab.html` | the ADR-012 operator panes (server-rendered, no SSE) |
| `tests/test_template_contract.py` | the gate asserting the server passes every variable these templates dereference |
| `scripts/sentence_findings.py` · `dashboard_flow.py` · `dashboard_attention.py` · `dashboard_loops.py` | the ADR-012 surfaces' data layers — pure data, no HTML |
| `src/core/provenance_writer.py` | the only per-entry writer for the human-verification fields |
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
- **Cross-tab change-bus:** verification actions on artifacts (parameters / citations / axioms / hypotheses / aristotle runs / production runs) flow through `scripts/verification_state.py` → `docs/verification_log.jsonl`. ⚠️ **That store is a gitignored runtime artifact, absent from a clean checkout and written on first use** — measured 2026-08-12, when the ADR-012 P9a browser test clicked Confirm and the bus wrote its first event. This bullet read *"that file does not exist … a design that has never carried an event"*, which was a claim about the **mechanism** derived from the **artifact**, and those are the two readings a missing file cannot distinguish. What is genuinely unexercised is everything downstream: nothing yet *consumes* the events. The Parameters tab's confirm/reject flow and Paper Provenance v2's per-link verify buttons are both delegates of this same library API. Each event annotates `meta.last_modified_explicit` on the corresponding KG node, propagating upstream so dependent `Sentence` nodes flip to `NEEDS_RECHECK` automatically when their backing artifacts re-verify.
- **`triggered_by` for cross-tab provenance:** verification events fired from a sentence's per-link UI carry `triggered_by: <source_sentence_id>`, so the audit trail surfaces "fired from sentence X's chain inspector" vs an opaque "Parameter X confirmed". Audit-log diffs render an inline `⚲ self` (self-triggered) or `↗ <other_sid>` badge. Field is `null` for events from the Parameters tab or the CLI.
- **Replay-canonical recovery:** the audit log is the canonical record. If a `cmd_mark` succeeds at the audit-event write but fails at the prose_state update (rare partial-failure), `scripts/sentence_state.py rebuild_prose_state --paper <id> --check` walks events in timestamp order and reports drift; `--write` atomically replaces `prose_state.json` with the rebuilt content.
- **Retention policy:** `docs/verification_log.jsonl` is append-only. `read_events` emits a one-shot WARN to stderr when the file exceeds 1 MB recommending `scripts/verification_state.py prune --keep-days 90` (default retention). `prune` refuses to operate without a retention criterion (`--keep-days N` / `--keep-records N` / `--before <ISO-8601>`). `--archive-to <path>` appends pruned events to a sidecar JSONL for recovery.
