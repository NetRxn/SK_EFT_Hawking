"""
Tests for scripts/build_graph.py — Knowledge Graph extraction pipeline.

Tests all 8 node extractors, edge integrity, and full graph export.
"""

import json
import sys
from pathlib import Path
from collections import Counter

import pytest

# Ensure project root is on sys.path
PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT))
sys.path.insert(0, str(PROJECT_ROOT / "scripts"))

from scripts.build_graph import (
    extract_parameter_nodes,
    extract_formula_nodes,
    extract_lean_theorem_nodes,
    extract_lean_declaration_nodes,
    extract_depends_on_axiom_edges,
    extract_aristotle_run_nodes,
    extract_primary_source_nodes,
    extract_paper_nodes,
    extract_paper_claim_nodes,
    extract_figure_nodes,
    extract_all_nodes,
    extract_all_edges,
    extract_claims_edges,
    extract_verified_by_edges,
    extract_sourced_from_edges,
    build_graph_json,
    compute_source_hash,
    SHAPE_MAP,
)


# ═══════════════════════════════════════════════════════════════════════
# Node extractor tests
# ═══════════════════════════════════════════════════════════════════════

class TestExtractParameterNodes:
    """Tests for extract_parameter_nodes()."""

    def test_extract_parameter_nodes(self):
        """Count matches PARAMETER_PROVENANCE; omega_perp exists."""
        from src.core.provenance import PARAMETER_PROVENANCE
        nodes = extract_parameter_nodes()
        assert len(nodes) == len(PARAMETER_PROVENANCE)
        ids = {n['id'] for n in nodes}
        assert 'param:Steinhauer.omega_perp' in ids

    def test_extract_parameter_nodes_have_required_fields(self):
        """Every parameter node has required fields."""
        nodes = extract_parameter_nodes()
        required_keys = {'id', 'type', 'label', 'name', 'verification', 'detail', 'meta'}
        for node in nodes:
            assert required_keys.issubset(node.keys()), f"Missing keys in {node['id']}"
            assert node['type'] == 'Parameter'
            meta = node['meta']
            assert 'value' in meta
            assert 'unit' in meta
            assert 'tier' in meta
            assert 'source' in meta
            assert 'llm_verified' in meta
            assert 'human_verified' in meta


class TestExtractFormulaNodes:
    """Tests for extract_formula_nodes()."""

    def test_extract_formula_nodes(self):
        """Count > 0; hawking_temperature exists with Lean ref."""
        nodes = extract_formula_nodes()
        assert len(nodes) > 0
        ht_nodes = [n for n in nodes if n['name'] == 'hawking_temperature']
        assert len(ht_nodes) == 1
        ht = ht_nodes[0]
        assert len(ht['meta']['lean_refs']) > 0


class TestExtractLeanTheoremNodes:
    """Tests for extract_lean_theorem_nodes()."""

    def test_extract_lean_theorem_nodes(self):
        """Count > 500 (project has 675+ theorems)."""
        nodes = extract_lean_theorem_nodes()
        assert len(nodes) > 500, f"Only found {len(nodes)} Lean theorems"


class TestExtractAristotleRunNodes:
    """Tests for extract_aristotle_run_nodes()."""

    def test_extract_aristotle_run_nodes(self):
        """Count > 0; all are type AristotleRun."""
        nodes = extract_aristotle_run_nodes()
        assert len(nodes) > 0
        for node in nodes:
            assert node['type'] == 'AristotleRun'


class TestExtractPrimarySourceNodes:
    """Tests for extract_primary_source_nodes()."""

    def test_extract_primary_source_nodes(self):
        """Count > 0."""
        nodes = extract_primary_source_nodes()
        assert len(nodes) > 0


class TestExtractPaperNodes:
    """Tests for extract_paper_nodes()."""

    def test_extract_paper_nodes(self):
        """Count >= 7 (project has 8 paper entries)."""
        nodes = extract_paper_nodes()
        assert len(nodes) >= 7


class TestExtractPaperClaimNodes:
    """Tests for extract_paper_claim_nodes()."""

    def test_extract_paper_claim_nodes(self):
        """Count > 0; all have paper in meta."""
        nodes = extract_paper_claim_nodes()
        assert len(nodes) > 0
        for node in nodes:
            assert 'paper' in node['meta'], f"Missing paper in meta for {node['id']}"


class TestExtractFigureNodes:
    """Tests for extract_figure_nodes()."""

    def test_extract_figure_nodes(self):
        """Count > 50 (project has 66 FigureSpecs)."""
        nodes = extract_figure_nodes()
        assert len(nodes) > 50, f"Only found {len(nodes)} figures"


# ═══════════════════════════════════════════════════════════════════════
# Aggregate and integrity tests
# ═══════════════════════════════════════════════════════════════════════

class TestNodeIntegrity:
    """Tests for aggregate node extraction."""

    def test_extract_all_nodes_no_duplicate_ids(self):
        """All node IDs are unique across all extractors."""
        nodes = extract_all_nodes()
        ids = [n['id'] for n in nodes]
        assert len(ids) == len(set(ids)), (
            f"Duplicate node IDs found: {[x for x in ids if ids.count(x) > 1][:5]}"
        )


class TestEdgeIntegrity:
    """Tests for edge extraction."""

    def test_extract_all_edges_not_empty(self):
        """At least some edges are extracted."""
        nodes = extract_all_nodes()
        node_ids = {n['id'] for n in nodes}
        edges = extract_all_edges(node_ids)
        assert len(edges) > 0

    def test_edges_reference_valid_node_ids(self):
        """Every edge source and target exists in the node list."""
        nodes = extract_all_nodes()
        node_ids = {n['id'] for n in nodes}
        edges = extract_all_edges(node_ids)
        for edge in edges:
            assert edge['source'] in node_ids, (
                f"Edge source {edge['source']} not in nodes (type={edge['type']})"
            )
            assert edge['target'] in node_ids, (
                f"Edge target {edge['target']} not in nodes (type={edge['type']})"
            )

    def test_edges_have_required_fields(self):
        """Every edge has source, target, and type."""
        nodes = extract_all_nodes()
        node_ids = {n['id'] for n in nodes}
        edges = extract_all_edges(node_ids)
        for edge in edges:
            assert 'source' in edge
            assert 'target' in edge
            assert 'type' in edge

    def test_claims_edges_exist(self):
        """CLAIMS edges connect papers to their claims."""
        nodes = extract_all_nodes()
        node_ids = {n['id'] for n in nodes}
        edges = extract_claims_edges(node_ids)
        assert len(edges) > 0
        for e in edges:
            assert e['type'] == 'CLAIMS'
            assert e['source'].startswith('paper:')
            assert e['target'].startswith('claim:')

    def test_verified_by_edges_exist(self):
        """VERIFIED_BY edges connect formulas to Lean theorems."""
        nodes = extract_all_nodes()
        node_ids = {n['id'] for n in nodes}
        edges = extract_verified_by_edges(node_ids)
        assert len(edges) > 0
        for e in edges:
            assert e['type'] == 'VERIFIED_BY'
            assert e['source'].startswith('formula:')
            assert e['target'].startswith('lean:')

    def test_sourced_from_edges_exist(self):
        """SOURCED_FROM edges connect parameters to primary sources."""
        nodes = extract_all_nodes()
        node_ids = {n['id'] for n in nodes}
        edges = extract_sourced_from_edges(node_ids)
        assert len(edges) > 0
        for e in edges:
            assert e['type'] == 'SOURCED_FROM'
            assert e['source'].startswith('param:')
            assert e['target'].startswith('source:')


# ═══════════════════════════════════════════════════════════════════════
# Full graph tests
# ═══════════════════════════════════════════════════════════════════════

class TestFullGraph:
    """Tests for build_graph_json()."""

    def test_full_graph_json_export(self):
        """All 8 node types present, >= 6 edge types."""
        graph = build_graph_json()

        # Basic structure
        assert 'nodes' in graph
        assert 'links' in graph
        assert 'meta' in graph
        assert graph['meta']['node_count'] == len(graph['nodes'])
        assert graph['meta']['edge_count'] == len(graph['links'])

        # All 8 node types
        node_types = {n['type'] for n in graph['nodes']}
        expected_node_types = {
            'Parameter', 'Formula', 'LeanTheorem', 'AristotleRun',
            'PrimarySource', 'Paper', 'PaperClaim', 'Figure',
        }
        assert expected_node_types.issubset(node_types), (
            f"Missing node types: {expected_node_types - node_types}"
        )

        # At least 7 edge types (HAS_FIGURE connects papers to figures)
        edge_types = {e['type'] for e in graph['links']}
        assert len(edge_types) >= 7, (
            f"Only {len(edge_types)} edge types found: {edge_types}"
        )
        assert 'HAS_FIGURE' in edge_types, "HAS_FIGURE edges missing"

        # JSON serializable
        json_str = json.dumps(graph, default=str)
        assert len(json_str) > 1000

    def test_source_hash_deterministic(self):
        """Source hash is deterministic across calls."""
        h1 = compute_source_hash()
        h2 = compute_source_hash()
        assert h1 == h2
        assert len(h1) == 16  # truncated to 16 hex chars


# ═══════════════════════════════════════════════════════════════════════
# New node type tests
# ═══════════════════════════════════════════════════════════════════════

class TestExtractLeanDeclarationNodes:
    """Tests for extract_lean_declaration_nodes()."""

    @pytest.fixture(scope="class")
    def lean_nodes(self):
        nodes = extract_lean_declaration_nodes()
        if not nodes:
            pytest.skip("No Lean declarations extracted")
        return nodes

    def test_has_multiple_types(self, lean_nodes):
        """Declaration nodes cover multiple Lean kinds."""
        types = {n['type'] for n in lean_nodes}
        assert 'LeanAxiom' in types or 'LeanTheorem' in types, (
            f"No axiom or theorem nodes found; types present: {types}"
        )
        assert 'LeanTheorem' in types
        assert 'LeanDef' in types
        assert 'LeanStructure' in types or 'LeanInductive' in types, (
            f"No structure/inductive nodes; types: {types}"
        )

    def test_axiom_nodes_have_eliminability(self, lean_nodes):
        """Every LeanAxiom node has eliminability in meta (may be None if not in AXIOM_METADATA)."""
        axioms = [n for n in lean_nodes if n['type'] == 'LeanAxiom']
        for ax in axioms:
            assert 'eliminability' in ax['meta'], f"Missing eliminability in axiom {ax['id']}"

    def test_nodes_have_shape(self, lean_nodes):
        """First 20 declaration nodes have a valid shape."""
        for node in lean_nodes[:20]:
            assert 'shape' in node['meta'], f"Missing shape in {node['id']}"
            assert node['meta']['shape'] in ('diamond', 'circle', 'square', 'triangle'), (
                f"Invalid shape {node['meta']['shape']} in {node['id']}"
            )

    def test_structure_has_field_constraints(self, lean_nodes):
        """At least one LeanStructure node has field_constraints."""
        structs = [n for n in lean_nodes if n['type'] == 'LeanStructure']
        if not structs:
            pytest.skip("No LeanStructure nodes found")
        has_fields = any(len(s['meta'].get('field_constraints', [])) > 0 for s in structs)
        assert has_fields, "No LeanStructure nodes have field_constraints"

    def test_no_duplicate_ids(self, lean_nodes):
        """No duplicate node IDs in declaration nodes."""
        ids = [n['id'] for n in lean_nodes]
        assert len(ids) == len(set(ids)), (
            f"Duplicate declaration IDs: {[x for x in ids if ids.count(x) > 1][:5]}"
        )

    def test_count_greater_than_500(self, lean_nodes):
        """Total declaration count > 500 (project has many declarations)."""
        assert len(lean_nodes) > 500, f"Only found {len(lean_nodes)} declarations"


class TestShapeMap:
    """Tests for SHAPE_MAP constant."""

    def test_all_types_have_shapes(self):
        """All 13 node types have entries in SHAPE_MAP."""
        for t in ['Paper', 'PaperClaim', 'Formula', 'Parameter', 'PrimarySource',
                  'Figure', 'AristotleRun', 'LeanAxiom', 'LeanTheorem', 'LeanDef',
                  'LeanStructure', 'LeanInductive', 'LeanInstance']:
            assert t in SHAPE_MAP, f"Node type {t!r} missing from SHAPE_MAP"

    def test_diamonds_are_trust_boundaries(self):
        """LeanAxiom and Parameter are diamonds (trust boundaries)."""
        assert SHAPE_MAP['LeanAxiom'] == 'diamond'
        assert SHAPE_MAP['Parameter'] == 'diamond'

    def test_all_shapes_are_valid(self):
        """All shape values are in the allowed set."""
        valid = {'diamond', 'circle', 'square', 'triangle'}
        for node_type, shape in SHAPE_MAP.items():
            assert shape in valid, f"{node_type} has invalid shape {shape!r}"


class TestDependsOnAxiomEdges:
    """Tests for extract_depends_on_axiom_edges()."""

    def test_edges_point_to_axioms(self):
        """Every DEPENDS_ON_AXIOM edge target is a LeanAxiom node."""
        nodes = extract_all_nodes()
        node_ids = {n['id'] for n in nodes}
        node_types = {n['id']: n['type'] for n in nodes}
        edges = extract_depends_on_axiom_edges(node_ids)
        for e in edges:
            target_type = node_types.get(e['target'])
            assert target_type == 'LeanAxiom', (
                f"Target {e['target']} is {target_type}, not LeanAxiom"
            )

    def test_edges_have_correct_type(self):
        """All edges returned have type DEPENDS_ON_AXIOM."""
        nodes = extract_all_nodes()
        node_ids = {n['id'] for n in nodes}
        edges = extract_depends_on_axiom_edges(node_ids)
        for e in edges:
            assert e['type'] == 'DEPENDS_ON_AXIOM'

    def test_no_self_edges(self):
        """No edge connects a node to itself."""
        nodes = extract_all_nodes()
        node_ids = {n['id'] for n in nodes}
        edges = extract_depends_on_axiom_edges(node_ids)
        for e in edges:
            assert e['source'] != e['target'], f"Self-edge on {e['source']}"


# ═══════════════════════════════════════════════════════════════════════
# PG+AGE parallel write tests
# ═══════════════════════════════════════════════════════════════════════

class TestPGWrite:
    """Tests for PG+AGE parallel write. Skips if PG unavailable."""

    @pytest.fixture(scope="class")
    def pg_conn(self):
        try:
            import psycopg
            conn = psycopg.connect(
                "host=localhost port=5433 dbname=sk_eft_provenance "
                "user=sk_eft password=sk_eft_local"
            )
            yield conn
            conn.close()
        except Exception:
            pytest.skip("PG+AGE not available")

    @pytest.fixture(scope="class")
    def built_graph(self, pg_conn):
        """Build the graph once per class (expensive — runs Lean extraction)."""
        from scripts.build_graph import build_graph_json
        return build_graph_json()

    def test_write_populates_graph(self, pg_conn, built_graph):
        """Vertices exist in PG after write."""
        with pg_conn.cursor() as cur:
            cur.execute("LOAD 'age'")
            cur.execute("SET search_path = ag_catalog, '$user', public")
            cur.execute("""
                SELECT * FROM cypher('sk_eft', $$
                    MATCH (n) RETURN count(n)
                $$) AS (cnt agtype)
            """)
            count = cur.fetchone()[0]
        # count is agtype, need to parse
        assert int(str(count)) > 0, "PG should have vertices after write"

    def test_write_node_count_matches(self, pg_conn, built_graph):
        """Vertex count in PG matches node count in graph dict."""
        expected = built_graph['meta']['node_count']

        with pg_conn.cursor() as cur:
            cur.execute("LOAD 'age'")
            cur.execute("SET search_path = ag_catalog, '$user', public")
            cur.execute("""
                SELECT * FROM cypher('sk_eft', $$
                    MATCH (n) RETURN count(n)
                $$) AS (cnt agtype)
            """)
            count = int(str(cur.fetchone()[0]))
        assert count == expected, (
            f"PG vertex count {count} != graph node_count {expected}"
        )

    def test_write_survives_pg_unavailable(self):
        """write_graph_to_pg does not raise when PG is unavailable."""
        from scripts.build_graph import write_graph_to_pg
        # Pass a minimal graph — function must never raise
        dummy_graph = {
            'nodes': [{'id': 'test:x', 'type': 'Formula', 'name': 'x',
                       'label': 'x', 'verification': 'verified', 'detail': '',
                       'meta': {'shape': 'circle'}}],
            'links': [],
            'meta': {'node_count': 1, 'edge_count': 0},
        }
        # Should complete without raising regardless of PG availability
        write_graph_to_pg(dummy_graph)
