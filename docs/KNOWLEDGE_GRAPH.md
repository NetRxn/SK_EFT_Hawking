# Provenance Knowledge Graph

Interactive visualization and integrity checker for the SK-EFT Hawking project's full provenance chain — from primary sources through parameters, formulas, Lean proofs, and Aristotle runs to paper claims and figures.

## Quick Start

```bash
cd SK_EFT_Hawking

# Start the dashboard (opens http://localhost:8050)
uv run python scripts/provenance_dashboard.py

# Navigate to the Knowledge Graph tab, or go directly:
# http://localhost:8050/?tab=graph
```

### Prerequisites

The knowledge graph requires a PostgreSQL + Apache AGE container:

```bash
cd SK_EFT_Hawking/docker
docker compose -f docker-compose.graph.yml up -d
```

This starts PG on port 5433 (separate from any other PG instances). The graph extraction currently works without PG (Phase 1 uses JSON), but the container is needed for Phase 2+.

## Architecture

```
Python registries          build_graph.py           Flask API          D3 visualization
(constants.py,        -->  (8 node types,     -->   /api/graph    -->  Force-directed
 provenance.py,             10 edge types,          /api/trace         SVG with 4 layouts
 citations.py,              ~980 nodes,             /api/impact        + Explore/Trace/
 formulas.py,               ~1058 edges)            /api/integrity     Impact modes
 lean/*.lean,
 review_figures.py)
```

**Phase 1 (current):** Python registries are the source of truth. The graph is extracted on demand by `build_graph.py` and served as JSON via Flask. The D3 visualization renders it interactively.

**Phase 2 (planned):** PG+AGE graph becomes the source of truth. Python dicts are generated from it. Dashboard gains write capability.

## Graph Schema

### Node Types (8)

| Node Type | Count | Source | ID Format |
|-----------|-------|--------|-----------|
| **Paper** | 8 | `PAPER_DEPENDENCIES` in provenance.py | `paper:{key}` |
| **PaperClaim** | 29 | `PAPER_DEPENDENCIES.key_claims` | `claim:{paper}:{index}` |
| **Formula** | 108 | `formulas.py` function defs + docstrings | `formula:{name}` |
| **LeanTheorem** | 676 | `lean/SKEFTHawking/*.lean` | `lean:{name}` |
| **AristotleRun** | 31 | `ARISTOTLE_THEOREMS` in constants.py | `aristotle:{run_id}` |
| **Parameter** | 33 | `PARAMETER_PROVENANCE` in provenance.py | `param:{key}` |
| **PrimarySource** | 31 | `CITATION_REGISTRY` in citations.py | `source:{key}` |
| **Figure** | 64 | `FIGURE_REGISTRY` in review_figures.py | `figure:{name}` |

Every node has a uniform schema: `{id, type, label, name, verification, detail, meta}`.

**Verification status** (computed per node):
- `verified` — fully grounded (human-verified parameter, Lean-proved theorem)
- `llm` — LLM-verified only (parameters awaiting human verification)
- `conflict` — code value disagrees with provenance value (>0.1% relative error)
- `projected` — PROJECTED tier parameter (no primary source expected)
- `unverified` — no verification

### Edge Types (10)

| Edge | From | To | Count | Semantics |
|------|------|----|-------|-----------|
| `CLAIMS` | Paper | PaperClaim | 29 | Paper makes this claim |
| `GROUNDED_IN` | PaperClaim | Formula | 146 | Claim computed by formula |
| `VERIFIED_BY` | Formula | LeanTheorem | 110 | Formula has Lean proof |
| `PROVED_BY` | LeanTheorem | AristotleRun | 210 | Aristotle filled this sorry |
| `USED_BY` | Parameter | Formula | 411 | Formula depends on parameter |
| `SOURCED_FROM` | Parameter | PrimarySource | 8 | Parameter from this paper |
| `DEPENDS_ON` | Paper | Parameter | 65 | Paper uses this parameter |
| `CITES` | Formula | PrimarySource | 40 | Formula cites this source |
| `HAS_FIGURE` | Paper | Figure | 22 | Paper includes this figure |
| `IMPORTS` | Formula | Formula | 17 | Formula calls another formula |

## Interactive Visualization

### Layouts

| Layout | Description | Best For |
|--------|-------------|----------|
| **Force** | Standard force-directed with tunable physics | Overall exploration |
| **Radial** | Concentric rings by node type (sources center, papers outer) | Type distribution |
| **Hierarchy** | Left-to-right DAG: sources → params → formulas → proofs → papers | Provenance chains |
| **Circle** | Nodes on a ring grouped by type | Clean overview, especially with Paper Focus |

Switch layouts using the buttons in the topbar: **Force | Radial | Hierarchy | Circle**

### Interaction Modes

| Mode | Click Behavior | Use Case |
|------|---------------|----------|
| **Explore** | Select node, highlight neighbors, show detail panel | General inspection |
| **Trace** | Highlight full provenance chain (bidirectional BFS) | "Is this claim fully grounded?" |
| **Impact** | Highlight all upstream dependents | "What breaks if I change this?" |

### Controls

- **Filter pills** — toggle visibility by node type (click to show/hide)
- **Paper Focus dropdown** — isolate a single paper's subgraph
- **Physics panel** (⚙ gear icon) — tune force simulation parameters:
  - Repulsion: charge strength (-500 to -10, default -200)
  - Link Distance: edge length (20 to 300, default 100)
  - Gravity: center pull (0 to 0.2, default 0.03)
  - Link Strength: edge stiffness (0.01 to 1.0, default 0.3)
  - Unpin All: release all pinned nodes
- **Drag** a node to pin it in place (white dot indicator)
- **Double-click** a pinned node to release it
- **Scroll** to zoom, **drag background** to pan

### Detail Panel

Click any node to open the detail panel (right side). Shows:
- Node type, name, verification badge
- Description and properties
- Connections list (clickable — navigates to connected nodes)
- "Trace to Foundation" / "Show Impact" action buttons

### Visual Encoding

- **Node color** by type: steel blue (Paper), gold (PaperClaim), amber (Formula), sage (LeanTheorem), green (AristotleRun), berry/pink (Parameter), grey (PrimarySource), purple (Figure)
- **Node size** by type (Papers largest, AristotleRuns smallest)
- **Verification glow**: green ring = verified, amber = LLM only, red pulse = conflict
- **Edges**: light grey default; bright green = traced-ok; red = traced-bad; amber = impact

## API Endpoints

| Endpoint | Method | Returns |
|----------|--------|---------|
| `/api/graph` | GET | Full graph JSON `{nodes, links, meta}` |
| `/api/graph/trace/<node_id>` | GET | `{traced_node_ids, traced_edge_indices}` |
| `/api/graph/impact/<node_id>` | GET | `{impacted_node_ids, impacted_edge_indices}` |
| `/api/graph/integrity` | GET | Integrity report (orphans, conflicts, chains) |

Node IDs contain colons (e.g., `param:Steinhauer.omega_perp`). The Flask routes use `<path:node_id>` to handle this.

## Command-Line Tools

### build_graph.py — Graph Extraction

```bash
# Export full graph as JSON
uv run python scripts/build_graph.py --json --out figures/provenance_graph.json

# Check staleness (hash of source files)
uv run python scripts/build_graph.py --check

# Dump to stdout
uv run python scripts/build_graph.py --json
```

### graph_integrity.py — Integrity Checker

```bash
# Human-readable report
uv run python scripts/graph_integrity.py

# JSON output
uv run python scripts/graph_integrity.py --json
```

Checks:
- **Orphan nodes** — nodes with zero edges
- **Conflicts** — parameter values disagreeing between code and provenance
- **Ungrounded claims** — paper claims without GROUNDED_IN edges
- **Broken provenance chains** — claims grounded in formulas that lack Lean proofs
- **Missing provenance** — parameters without SOURCED_FROM edges (excluding PROJECTED tier)

### validate.py CHECK 16

```bash
uv run python scripts/validate.py --check graph_integrity
```

Integrated as CHECK 16 in the validation suite. Conflicts are hard failures; orphans and structural gaps are warnings.

## Files

| File | Purpose |
|------|---------|
| `scripts/build_graph.py` | Extracts 8 node types + 10 edge types from registries |
| `scripts/graph_integrity.py` | Structural integrity queries |
| `scripts/provenance_dashboard.py` | Flask dashboard + API endpoints |
| `scripts/templates/dashboard.html` | Main dashboard template (Datastar) |
| `scripts/templates/partials/graph_tab.html` | D3 knowledge graph visualization |
| `figures/provenance_graph.json` | Static JSON export of the graph |
| `tests/test_build_graph.py` | 18 extraction tests |
| `tests/test_graph_integrity.py` | 2 integrity tests |
| `docker/docker-compose.graph.yml` | PG+AGE container (port 5433) |

## Dependencies

| Package | Purpose |
|---------|---------|
| `psycopg[binary]>=3.2` | PostgreSQL driver (core dep) |
| `datastar-py>=0.5` | Datastar server integration (optional: `graph` extra) |
| D3.js v7 (CDN) | Graph visualization (loaded in browser) |
| Instrument Sans + IBM Plex Mono (CDN) | Typography (loaded in browser) |

## Phased Roadmap

### Phase 1 (current): Graph View + Explorer
- Graph extracted from Python registries (source of truth unchanged)
- Interactive D3 visualization with 4 layouts and 3 modes
- Integrity queries and CHECK 16 integration
- Static JSON export

### Phase 2: Graph as Source of Truth
- PG+AGE schema with constraints and indexes
- Thin Python query layer: `from src.core.graph import get_parameter, ...`
- Generate Python dicts from graph (backward compat)
- Dashboard write capability (edit provenance directly)

### Phase 3: Advanced Features
- Paper-to-foundation traversal from .tex sections
- Export to JSON-LD / W3C PROV
- CI-style automated monitoring
- Notebook integration: `from src.core.graph import trace_claim`
