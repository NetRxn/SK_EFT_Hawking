# SK-EFT Provenance Command Center — Dashboard Documentation

Interactive Flask dashboard for reviewing and verifying parameter provenance, formula citations, Lean proof architecture, paper claims, citation registry, and the provenance knowledge graph.

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

## API Endpoints

| Endpoint | Method | Returns |
|----------|--------|---------|
| `/` | GET | Dashboard HTML (tab selected via `?tab=` param) |
| `/api/verify` | POST | Verify/reject/flag a parameter |
| `/api/save` | POST | Save accumulated verification actions |
| `/api/graph` | GET | Full graph JSON `{nodes, links, meta}` |
| `/api/graph/trace/<node_id>` | GET | Traced node/edge IDs for provenance chain |
| `/api/graph/impact/<node_id>` | GET | Impacted node/edge IDs for upstream dependents |
| `/api/graph/integrity` | GET | Integrity report (orphans, conflicts, chains) |

Node IDs containing colons (e.g., `param:Steinhauer.omega_perp`) are handled via Flask `<path:node_id>` routes.

## Architecture

```
Python registries          build_graph.py           Flask API          Dashboard
(constants.py,        -->  (13 node types,    -->   /api/graph    -->  6 tabs
 provenance.py,             11 edge types,          /api/trace         Datastar
 citations.py,              ~1870 nodes,            /api/impact        D3 KG
 formulas.py,               ~990 edges)             /api/integrity     
 lean_deps.json,                |
 review_figures.py)             v
                         PG+AGE (parallel)
                         sk_eft graph on :5433
```

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
- `c` — confirm current parameter
- `r` — reject current parameter
- `f` — flag current parameter
