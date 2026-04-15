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

**Python registries remain the source of truth.** The graph is extracted on demand by `build_graph.py` and served as JSON via Flask. The D3 visualization renders it interactively. PG+AGE is populated in parallel for Cypher-based traversal queries (dependency trees, blast radius).

### Lean Declaration Extraction

Lean declarations are extracted via a meta-programming script (`lean/SKEFTHawking/ExtractDeps.lean`) that uses `Lean.Environment.collectAxioms` to compute transitive axiom dependencies. The Python wrapper (`scripts/extract_lean_deps.py`) manages staleness checking — re-extraction only happens when `.lean` files change. Output cached at `lean/lean_deps.json`.

### PG+AGE Parallel Write

`build_graph.py` writes all nodes and edges to the `sk_eft` graph in PG+AGE (port 5433) alongside JSON extraction. This is best-effort — if PG is unavailable, JSON extraction still works. PG provides Cypher-based traversal for dependency tree queries in the Proof Architecture tab.

## Graph Schema

### Node Types (22 — Phase 1 + 1.5 + 5v Wave 2a)

**Phase 1 / 1.5 base types (14):**

| Node Type | Shape | Color | Source | ID Format |
|-----------|-------|-------|--------|-----------|
| **Paper** | Square | Steel blue (#2E86AB) | papers/ (fs) + provenance.py | `paper:{key}` |
| **PaperClaim** | Circle | Gold (#E8C547) | provenance.py | `claim:{paper}:{index}` |
| **Formula** | Circle | Amber (#F18F01) | formulas.py | `formula:{name}` |
| **Parameter** | Diamond | Berry (#A23B72) | provenance.py | `param:{key}` |
| **PrimarySource** | Triangle | Grey (#c8ccd0) | citations.py | `source:{key}` |
| **Figure** | Circle | Purple (#9b6dff) | review_figures.py + visualizations.py (fs) | `figure:{name}` |
| **AristotleRun** | Circle | Green (#22c55e) | constants.py | `aristotle:{run_id}` |
| **LeanAxiom** | Diamond | Amber (#d97706) | lean_deps.json | `lean:{full_name}` |
| **Hypothesis** | Diamond | Coral (#f97316) | constants.py HYPOTHESIS_REGISTRY | `hyp:{key}` |
| **LeanTheorem** | Circle | Sage (#5C946E) | lean_deps.json | `lean:{full_name}` |
| **LeanDef** | Circle | Blue (#60a5fa) | lean_deps.json | `lean:{full_name}` |
| **LeanStructure** | Square | Purple (#c084fc) | lean_deps.json | `lean:{full_name}` |
| **LeanInductive** | Square | Amber (#fbbf24) | lean_deps.json | `lean:{full_name}` |
| **LeanInstance** | Circle | Indigo (#818cf8) | lean_deps.json | `lean:{full_name}` |

Note: Lean IDs switched from `{short_name}` to `{full_name}` in Phase 5v Wave 0 to eliminate silent short-name collisions (~42% drop → 0). Short-name lookups still work via `_LEAN_SHORT_INDEX` with ambiguity logging.

**Phase 5v Wave 2a readiness-system types (8 — stubs, wired in Waves 2b–4):**

| Node Type | Shape | Wired in | Purpose |
|-----------|-------|---------|---------|
| **ProseClaim** | Circle | Wave 2e | Narrative statements not tied to a Formula |
| **PythonTest** | Square | Wave 2a+ | Test functions + test_kind ∈ {golden, bounds, identity, roundtrip} |
| **ReviewFinding** | Triangle | Wave 2c / 6 | Internal + external adversarial review findings |
| **ProductionRun** | Circle | Wave 2d | MC/RHMC run records + status |
| **PlaceholderMarker** | Diamond | Wave 2b | Lean decls with trivial body on non-trivial statement |
| **Contradiction** | Triangle | Wave 2f | Concrete cross-paper inconsistency instance |
| **CountMetric** | Diamond | Wave 2g | counts.json snapshot at a point in time |
| **ReadinessGate** | Square | Wave 4 | Per-paper × per-dimension state (11 gates × N papers) |

Every node has a uniform schema: `{id, type, label, name, verification, detail, meta}`.

### Shape Vocabulary

Shapes encode semantic roles — a visual dimension independent of color:

| Shape | Semantic Role | Node Types |
|-------|--------------|------------|
| **Diamond** | Trust boundary — accepted without derivation | LeanAxiom, Hypothesis, Parameter |
| **Circle** | Derived — proven, computed, or generated | LeanTheorem, LeanDef, LeanInstance, Formula, PaperClaim, Figure, AristotleRun |
| **Square** | Structural — defines the framework/vocabulary | LeanStructure, LeanInductive, Paper |
| **Triangle** | External input — comes from outside the system | PrimarySource |

### Verification Status (computed per node)

- `verified` — fully grounded (human-verified parameter, Lean-proved theorem)
- `llm` — LLM-verified only (parameters awaiting human verification)
- `conflict` — code value disagrees with provenance value (>0.1% relative error)
- `projected` — PROJECTED tier parameter (no primary source expected)
- `unverified` — no verification

### Edge Types (20 — Phase 1 + 1.5 + 5v Wave 2a)

**Phase 1 / 1.5 base edges (12):**

| Edge | From | To | Semantics |
|------|------|----|-----------|
| `CLAIMS` | Paper | PaperClaim | Paper makes this claim |
| `GROUNDED_IN` | PaperClaim | Formula | Claim computed by formula |
| `VERIFIED_BY` | Formula | LeanTheorem | Formula has Lean proof |
| `PROVED_BY` | LeanTheorem | AristotleRun | Aristotle filled this sorry |
| `USED_BY` | Parameter | Formula | Formula depends on parameter |
| `SOURCED_FROM` | Parameter | PrimarySource | Parameter from this paper |
| `DEPENDS_ON` | Paper | Parameter | Paper uses this parameter |
| `CITES` | Formula | PrimarySource | Formula cites this source |
| `HAS_FIGURE` | Paper | Figure | Paper includes this figure (auto-discovered from `\includegraphics` in Wave 1c) |
| `IMPORTS` | Formula | Formula | Formula calls another formula |
| `DEPENDS_ON_AXIOM` | LeanTheorem/LeanDef | LeanAxiom | Transitive axiom dependency (from `collectAxioms`) |
| `ASSUMES` | LeanTheorem | Hypothesis | Theorem takes this hypothesis as a parameter (from HYPOTHESIS_REGISTRY.dependent_theorems) |

**Phase 5v Wave 2a readiness-system edges (8):**

| Edge | From | To | Purpose | Wired in |
|------|------|----|---------|----------|
| `VERIFIES` | PythonTest | Formula/Parameter/LeanTheorem | Test covers artifact; carries `test_kind` attribute | Wave 2a+ |
| `FLAGS` | ReviewFinding | any | Review flagged this artifact | Wave 2c |
| `SUPERSEDES` | ReviewFinding | ReviewFinding | Later review resolved/reopened earlier finding | Wave 2c |
| `PRODUCES` | ProductionRun | Formula/PaperClaim | Run generated data this depends on | Wave 2d |
| `REPORTS` | Paper | CountMetric | Paper reports a count value (comparable to canonical) | Wave 2g |
| `SUPPORTS` | artifact | artifact | Mutual reinforcement (dual of CONTRADICTS) | Wave 2f |
| `CONTRADICTS` | artifact | artifact | Cross-artifact inconsistency | Wave 2f |
| `IMPACTED_BY` | ReadinessGate | any | Gate flips to `needs-recheck` if upstream changes | Wave 4 |

### Lean Node Metadata

Lean declaration nodes carry additional metadata in `meta`:

- `meta.shape` — diamond/circle/square/triangle
- `meta.lean_kind` — raw Lean kind (axiom/theorem/def/structure/etc.)
- `meta.axiom_deps_project` — project axiom names this declaration depends on
- `meta.axiom_deps_core` — core axiom names (propext, Classical.choice, etc.)
- `meta.eliminability` — eliminable/hard/unknown (axioms only, from `AXIOM_METADATA`)
- `meta.field_constraints` — structure field names and types (structures only)

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

- **Filter pills** — toggle visibility by node type (click to show/hide). Lean declaration types split into main (Axiom, Theorem) and scaffolding (Def, Structure, Inductive, Instance).
- **Scaffolding toggle** — show/hide Lean scaffolding types (Def, Structure, Inductive, Instance) as a group. Off by default to keep the graph navigable.
- **Core Axioms toggle** — show/hide core Lean axioms (propext, Classical.choice, Quot.sound). Off by default.
- **Paper Focus dropdown** — isolate a single paper's subgraph
- **Logical Focus dropdown** — isolate the subgraph of an axiom or structure. Lists project axioms first, then structures. Uses impact BFS to find all connected nodes.
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

- **Node shape** by semantic role: diamond (trust boundaries: axioms, parameters), square (structural: structures, papers), triangle (external: sources), circle (derived: everything else)
- **Node color** by type: steel blue (Paper), gold (PaperClaim), amber (Formula), sage (LeanTheorem), amber (LeanAxiom), blue (LeanDef), purple (LeanStructure), amber (LeanInductive), indigo (LeanInstance), green (AristotleRun), berry/pink (Parameter), grey (PrimarySource), purple (Figure)
- **Node size** by type (Papers/Axioms largest, Instances smallest)
- **Verification glow**: green ring = verified, amber = LLM only, red pulse = conflict
- **Edges**: light grey default; bright green = traced-ok; red = traced-bad; amber = impact; amber dashed = DEPENDS_ON_AXIOM

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
- **Unclassified axioms** — axioms without eliminability entry in `AXIOM_METADATA`
- **Axiom dependency stats** — DEPENDS_ON_AXIOM edge counts and theorem blast radii
- **PG+AGE sync** — vertex count in PG matches extracted node count

### validate.py CHECK 16

```bash
uv run python scripts/validate.py --check graph_integrity
```

Integrated as CHECK 16 in the validation suite. Conflicts are hard failures; orphans and structural gaps are warnings.

## Files

| File | Purpose |
|------|---------|
| `lean/SKEFTHawking/ExtractDeps.lean` | Lean meta script: declaration extraction + collectAxioms |
| `lean/lean_deps.json` | Cached extraction output (gitignored) |
| `scripts/extract_lean_deps.py` | Python wrapper with staleness check for Lean extraction |
| `scripts/build_graph.py` | Extracts 13 node types + 11 edge types, writes to JSON + PG+AGE |
| `scripts/graph_integrity.py` | Structural integrity queries + axiom checks + PG sync |
| `scripts/provenance_dashboard.py` | Flask dashboard + API endpoints + Proof Architecture data |
| `scripts/templates/dashboard.html` | Main dashboard template (Datastar) |
| `scripts/templates/partials/graph_tab.html` | D3 knowledge graph with shapes, filters, Logical Focus |
| `figures/provenance_graph.json` | Static JSON export of the graph |
| `tests/test_build_graph.py` | Extraction tests (nodes, edges, shapes, PG write) |
| `tests/test_extract_lean_deps.py` | Lean extraction wrapper tests |
| `tests/test_graph_integrity.py` | Integrity tests |
| `docker/docker-compose.graph.yml` | PG+AGE container (port 5433) |

## Dependencies

| Package | Purpose |
|---------|---------|
| `psycopg[binary]>=3.2` | PostgreSQL driver (core dep) |
| `datastar-py>=0.5` | Datastar server integration (optional: `graph` extra) |
| D3.js v7 (CDN) | Graph visualization (loaded in browser) |
| Instrument Sans + IBM Plex Mono (CDN) | Typography (loaded in browser) |

## Phased Roadmap

### Phase 1 (complete): Graph View + Explorer
- Graph extracted from Python registries (source of truth unchanged)
- Interactive D3 visualization with 4 layouts and 3 modes
- Integrity queries and CHECK 16 integration
- Static JSON export

### Phase 1.5 (complete): Lean Proof Architecture + PG+AGE
- Full Lean declaration taxonomy (13 node types) via `ExtractDeps.lean` + `collectAxioms`
- Shape vocabulary: diamond (trust boundaries), square (structural), triangle (external), circle (derived)
- Proof Architecture dashboard tab: axiom command panel, declaration browser, structure field assumptions
- Scaffolding toggle, Logical Focus dropdown, DEPENDS_ON_AXIOM edges
- PG+AGE parallel write (Python registries remain source of truth)
- Axiom eliminability tracking via `AXIOM_METADATA` in constants.py
- Claims-reviewer agent: axiom risk + hypothesis risk assessment

### Phase 2: Graph as Source of Truth
- Flip source of truth from Python dicts to PG+AGE
- Generate Python dicts from graph (backward compat)
- Dashboard write capability (edit provenance directly)

### Phase 3: Advanced Features
- Paper-to-foundation traversal from .tex sections
- Export to JSON-LD / W3C PROV
- CI-style automated monitoring
- Notebook integration: `from src.core.graph import trace_claim`
