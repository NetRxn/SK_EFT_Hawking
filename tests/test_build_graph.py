"""
Tests for scripts/build_graph.py — Knowledge Graph extraction pipeline.

Tests all 8 node extractors, edge integrity, and full graph export.

Marked `slow`: `extract_lean_*_nodes` calls `load_lean_deps()` which
invokes `lake env lean --run SKEFTHawking/ExtractDeps.lean` when the
cached hash is stale (5-10 min). Default pytest skips this module;
run with `-m slow` to include.
"""

import json
import sys
from pathlib import Path
from collections import Counter

import pytest
import types

# ⚠️ NOT a module-level `slow` mark. One was here, deselecting ALL 66 functions
# from the default `pytest tests/` run — including `TestAgeLabelCreation`, which
# needs no database and completes in 0.02 s. A guard that only runs under
# `-m slow` is a guard most runs do not have.
#
# The mark now sits on the classes that genuinely need Postgres or a full graph
# build. Anything cheap and DB-free stays on the default path, which is where a
# regression should be caught.

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
    extract_prose_claim_nodes,
    extract_python_test_nodes,
    extract_review_finding_nodes,
    extract_production_run_nodes,
    extract_placeholder_marker_nodes,
    extract_contradiction_nodes,
    extract_count_metric_nodes,
    extract_readiness_gate_nodes,
    extract_verifies_edges,
    extract_flags_edges,
    extract_reports_edges,
    extract_all_nodes,
    extract_all_edges,
    extract_claims_edges,
    extract_verified_by_edges,
    extract_sourced_from_edges,
    discover_paper_draft_paths,
    build_graph_json,
    compute_source_hash,
    SHAPE_MAP,
)

PAPERS_DIR = PROJECT_ROOT / "papers"

_REQUIRED_NODE_FIELDS = {'id', 'type', 'label', 'name', 'verification', 'detail', 'meta'}


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

    def test_formula_verification_is_resolution_based(self):
        """R-06 honest-labels: a formula is 'verified' only when a Lean ref
        actually RESOLVES (present in lean_deps.json), never on the mere presence
        of a `Lean:` string. Every 'verified' formula must have >=1 resolved ref;
        an 'unverified' formula must have 0 resolved refs."""
        nodes = extract_formula_nodes()
        # These metadata keys exist regardless of build state.
        for n in nodes:
            assert 'lean_refs_resolved' in n['meta']
            assert 'lean_refs_dangling' in n['meta']
        # If resolution was actually checked (lean_deps.json present), the label
        # must agree with the resolved-ref set.
        checked = [n for n in nodes if n['meta'].get('lean_resolution_checked')]
        if checked:
            for n in checked:
                if n['verification'] == 'verified':
                    assert n['meta']['lean_refs_resolved'], (
                        f"{n['name']} labelled verified but no ref resolves")
                if n['verification'] == 'unverified':
                    assert not n['meta']['lean_refs_resolved'], (
                        f"{n['name']} labelled unverified but a ref resolves")

    def test_definitional_record_formulas_labelled_honestly(self):
        """R-06 + R-05: a formula grounded only on a declared definitional-record
        theorem (identity wrapper / rfl) is labelled 'definitional-record', not
        'verified'. wrt_s2xs1 grounds on wrt_S2xS1_eq_rank (a rfl equality)."""
        nodes = {n['name']: n for n in extract_formula_nodes()}
        wrt = nodes.get('wrt_s2xs1')
        if wrt is not None and wrt['meta'].get('lean_resolution_checked'):
            assert wrt['verification'] == 'definitional-record', (
                f"wrt_s2xs1 should be definitional-record, got {wrt['verification']}")


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

    def test_bundle_dirs_discovered(self):
        """R-06: publication-target bundle directories (D*, E*, F, I*, L*) are
        discovered as paper nodes, not just the legacy paper*_* dirs."""
        labels = {n['label'] for n in extract_paper_nodes()}
        # At least these bundle targets must appear if they exist on disk.
        for bundle in ('D1', 'D2', 'E1', 'F', 'I1', 'L1'):
            if (PAPERS_DIR / bundle / "paper_draft.tex").exists():
                assert bundle in labels, f"bundle {bundle} not discovered as a paper node"

    def test_discover_paper_draft_paths_matches_glob(self):
        """discover_paper_draft_paths finds every papers/*/paper_draft.tex."""
        found = {p.parent.name for p in discover_paper_draft_paths(PAPERS_DIR)}
        expected = {p.parent.name for p in PAPERS_DIR.glob("*/paper_draft.tex")}
        assert found == expected
        # And it is a strict superset of the old paper*_* glob.
        legacy = {p.parent.name for p in PAPERS_DIR.glob("paper*_*/paper_draft.tex")}
        assert legacy <= found


class TestPaperDirDiscoveryIsSingleSourced:
    """`_iter_paper_dirs` must agree with `discover_paper_draft_paths`.

    `discover_paper_draft_paths`'s docstring states the contract — *"All node/edge
    extractors route through this one helper so discovery cannot drift between them"* —
    and until 2026-08-06 `_iter_paper_dirs` was the one that did not, keeping a bare
    `startswith('paper')` predating the bundle roster. It gates the Sentence layer, the
    BACKED_BY chain, AuditEvent and LOGGED_BY, so the drift cost **1 316 of 3 432 v2
    sentences** — every bundle's prose, invisible to the graph and therefore to every
    gate reading it.

    These two tests fail on the reintroduction of ANY name filter on that path.
    """

    def test_iter_paper_dirs_equals_the_canonical_discovery(self):
        from build_graph import _iter_paper_dirs

        iterated = {key for key, _ in _iter_paper_dirs()}
        canonical = {p.parent.name for p in discover_paper_draft_paths(PAPERS_DIR)}
        assert iterated == canonical, (
            "_iter_paper_dirs has drifted from discover_paper_draft_paths; "
            f"missing={canonical - iterated} extra={iterated - canonical}"
        )

    def test_iter_paper_dirs_reaches_the_bundles_and_the_note(self):
        """The population a name filter would silently drop, named explicitly.

        `note_rt_ch_bounds` is here deliberately: it is neither `paper*`-prefixed nor a
        registered bundle code, so it is exactly what a roster-based filter misses. It
        already had a Paper node — the Paper extractor used the wider population all
        along, which is what made the disagreement invisible.
        """
        from build_graph import _iter_paper_dirs

        iterated = {key for key, _ in _iter_paper_dirs()}
        for name in ('D1', 'D6', 'D12', 'L2', 'I1', 'E1', 'F', 'note_rt_ch_bounds'):
            if (PAPERS_DIR / name / "paper_draft.tex").exists():
                assert name in iterated, f"{name} unreachable from _iter_paper_dirs"

    def test_every_v2_sentence_on_disk_becomes_a_node(self):
        """Population reach, measured end-to-end rather than asserted structurally.

        This is the assertion whose absence let the defect live: the extractor was
        internally consistent and simply never opened 20 of the 49 files. Comparing the
        node count to the artifact count is the only form that could have caught it.
        """
        import json

        from build_graph import extract_sentence_nodes

        on_disk = set()
        for cr in sorted(PAPERS_DIR.glob("*/claims_review.json")):
            try:
                data = json.loads(cr.read_text())
            except (json.JSONDecodeError, OSError):
                continue
            if 'sentences' not in data:  # v1 schema is deliberately ignored
                continue
            on_disk.update(s['id'] for s in data['sentences'] if s.get('id'))

        assert on_disk, "no v2 claims_review sentences found — the test itself is vacuous"

        emitted = {n['id'] for n in extract_sentence_nodes() if n['type'] == 'Sentence'}
        assert on_disk <= emitted, (
            f"{len(on_disk - emitted)} v2 sentence(s) on disk never became nodes; "
            f"e.g. {sorted(on_disk - emitted)[:3]}"
        )


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

@pytest.mark.slow
class TestNodeIntegrity:
    """Tests for aggregate node extraction."""

    def test_extract_all_nodes_no_duplicate_ids(self, all_graph_nodes):
        """All node IDs are unique across all extractors."""
        nodes = all_graph_nodes
        ids = [n['id'] for n in nodes]
        assert len(ids) == len(set(ids)), (
            f"Duplicate node IDs found: {[x for x in ids if ids.count(x) > 1][:5]}"
        )


@pytest.mark.slow
class TestEdgeIntegrity:
    """Tests for edge extraction."""

    def test_extract_all_edges_not_empty(self, all_graph_nodes, all_graph_node_ids, all_graph_edges):
        """At least some edges are extracted."""
        nodes = all_graph_nodes
        node_ids = all_graph_node_ids
        edges = all_graph_edges
        assert len(edges) > 0

    def test_edges_reference_valid_node_ids(self, all_graph_nodes, all_graph_node_ids, all_graph_edges):
        """Every edge source and target exists in the node list, except for
        BACKED_BY edges intentionally emitted with `link_state: missing_target`
        (per `extract_backed_by_edges` design at `build_graph.py:2008` —
        these surface unresolvable claims-review chain links to the
        graph-integrity check rather than silently dropping them)."""
        nodes = all_graph_nodes
        node_ids = all_graph_node_ids
        edges = all_graph_edges
        for edge in edges:
            assert edge['source'] in node_ids, (
                f"Edge source {edge['source']} not in nodes (type={edge['type']})"
            )
            # Skip intentionally-unresolved BACKED_BY edges; the
            # graph-integrity report surfaces these as broken_chains.
            meta = edge.get('meta') or {}
            if (edge.get('type') == 'BACKED_BY'
                    and meta.get('link_state') == 'missing_target'):
                continue
            assert edge['target'] in node_ids, (
                f"Edge target {edge['target']} not in nodes (type={edge['type']})"
            )

    def test_edges_have_required_fields(self, all_graph_nodes, all_graph_node_ids, all_graph_edges):
        """Every edge has source, target, and type."""
        nodes = all_graph_nodes
        node_ids = all_graph_node_ids
        edges = all_graph_edges
        for edge in edges:
            assert 'source' in edge
            assert 'target' in edge
            assert 'type' in edge

    def test_claims_edges_exist(self, all_graph_nodes, all_graph_node_ids):
        """CLAIMS edges connect papers to their claims."""
        nodes = all_graph_nodes
        node_ids = all_graph_node_ids
        edges = extract_claims_edges(node_ids)
        assert len(edges) > 0
        for e in edges:
            assert e['type'] == 'CLAIMS'
            assert e['source'].startswith('paper:')
            assert e['target'].startswith('claim:')

    def test_every_claim_node_has_a_claims_edge(self, all_graph_nodes, all_graph_node_ids):
        """R-06 core: every discovered PaperClaim node (declared, tex-auto, OR
        bundle-discovered) is CLAIMS-connected to its paper — zero orphan claims.
        The pre-remediation graph had 128 orphan claims because CLAIMS edges were
        driven from PAPER_DEPENDENCIES.key_claims alone."""
        nodes = all_graph_nodes
        node_ids = all_graph_node_ids
        claim_ids = {n['id'] for n in nodes if n['type'] == 'PaperClaim'}
        claimed = {e['target'] for e in extract_claims_edges(node_ids)}
        orphans = claim_ids - claimed
        assert not orphans, f"{len(orphans)} orphan claim(s): {sorted(orphans)[:10]}"

    def test_claims_edges_cover_bundle_claims(self, all_graph_nodes, all_graph_node_ids):
        """R-06: claims on a bundle paper (e.g. D1) get CLAIMS edges too."""
        nodes = all_graph_nodes
        node_ids = all_graph_node_ids
        edges = extract_claims_edges(node_ids)
        if 'paper:D1' in node_ids:
            d1_claims = {e['target'] for e in edges if e['source'] == 'paper:D1'}
            d1_claim_nodes = {n['id'] for n in nodes
                              if n['type'] == 'PaperClaim'
                              and n['meta'].get('paper') == 'D1'}
            if d1_claim_nodes:
                assert d1_claim_nodes <= d1_claims

    def test_verified_by_edges_exist(self, all_graph_nodes, all_graph_node_ids):
        """VERIFIED_BY edges connect formulas to Lean theorems."""
        nodes = all_graph_nodes
        node_ids = all_graph_node_ids
        edges = extract_verified_by_edges(node_ids)
        assert len(edges) > 0
        for e in edges:
            assert e['type'] == 'VERIFIED_BY'
            assert e['source'].startswith('formula:')
            assert e['target'].startswith('lean:')

    def test_sourced_from_edges_exist(self, all_graph_nodes, all_graph_node_ids):
        """SOURCED_FROM edges connect parameters to primary sources."""
        nodes = all_graph_nodes
        node_ids = all_graph_node_ids
        edges = extract_sourced_from_edges(node_ids)
        assert len(edges) > 0
        for e in edges:
            assert e['type'] == 'SOURCED_FROM'
            assert e['source'].startswith('param:')
            assert e['target'].startswith('source:')


# ═══════════════════════════════════════════════════════════════════════
# Full graph tests
# ═══════════════════════════════════════════════════════════════════════

@pytest.mark.slow
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

    def test_edges_point_to_axioms(self, all_graph_nodes, all_graph_node_ids):
        """Every DEPENDS_ON_AXIOM edge target is a LeanAxiom node."""
        nodes = all_graph_nodes
        node_ids = all_graph_node_ids
        node_types = {n['id']: n['type'] for n in nodes}
        edges = extract_depends_on_axiom_edges(node_ids)
        for e in edges:
            target_type = node_types.get(e['target'])
            assert target_type == 'LeanAxiom', (
                f"Target {e['target']} is {target_type}, not LeanAxiom"
            )

    def test_edges_have_correct_type(self, all_graph_nodes, all_graph_node_ids):
        """All edges returned have type DEPENDS_ON_AXIOM."""
        nodes = all_graph_nodes
        node_ids = all_graph_node_ids
        edges = extract_depends_on_axiom_edges(node_ids)
        for e in edges:
            assert e['type'] == 'DEPENDS_ON_AXIOM'

    def test_no_self_edges(self, all_graph_nodes, all_graph_node_ids):
        """No edge connects a node to itself."""
        nodes = all_graph_nodes
        node_ids = all_graph_node_ids
        edges = extract_depends_on_axiom_edges(node_ids)
        for e in edges:
            assert e['source'] != e['target'], f"Self-edge on {e['source']}"


# ═══════════════════════════════════════════════════════════════════════
# PG+AGE parallel write tests
# ═══════════════════════════════════════════════════════════════════════

class TestAgeLabelCreation:
    """`_create_age_labels` must actually ISSUE label statements.

    ⚠️ It issued ZERO for a commit. `graph_name` was parameterised in the body and
    not the signature, so every `create_vlabel`/`create_elabel` raised `NameError`
    into `except Exception: pass  # Label already exists` — a broad catch, a false
    comment, and a dead path, all invisible because AGE auto-creates labels on
    `CREATE` so nothing downstream failed.

    Needs no database: a recording fake connection is enough, which is exactly why
    the absence of this test was the gap.
    """

    class _Cur:
        def __init__(self, log): self.log = log
        def __enter__(self): return self
        def __exit__(self, *a): return False
        def execute(self, q, *a): self.log.append(q)

    class _Conn:
        autocommit = False
        def __init__(self): self.log = []
        def cursor(self): return TestAgeLabelCreation._Cur(self.log)

    def test_labels_are_actually_issued(self):
        from scripts.build_graph import _create_age_labels
        conn = self._Conn()
        _create_age_labels(conn, {"Formula", "Theorem"}, {"VERIFIES"}, "throwaway")
        assert sum("create_vlabel" in q for q in conn.log) == 2, (
            f"expected one vlabel per node type; issued {conn.log}")
        assert sum("create_elabel" in q for q in conn.log) == 1

    def test_labels_target_the_graph_they_were_given(self):
        """The half that would have caught the original bug AND a wrong target."""
        from scripts.build_graph import _create_age_labels
        conn = self._Conn()
        _create_age_labels(conn, {"Formula"}, {"VERIFIES"}, "throwaway_xyz")
        creates = [q for q in conn.log if "create_" in q]
        assert creates, "no label statements issued at all"
        assert all("throwaway_xyz" in q for q in creates), creates
        assert not any("'sk_eft'" in q for q in creates), (
            "a label statement targeted PRODUCTION despite being given a name")

    def test_a_non_duplicate_error_is_not_swallowed(self, caplog):
        """The narrowed catch. A broken connection must not read as 'already exists'."""
        import logging

        class Boom(TestAgeLabelCreation._Cur):
            def execute(self, q, *a):
                if "create_" in q:
                    raise RuntimeError("connection lost")
                self.log.append(q)

        class BoomConn(TestAgeLabelCreation._Conn):
            def cursor(self): return Boom(self.log)

        from scripts.build_graph import _create_age_labels
        with caplog.at_level(logging.WARNING):
            _create_age_labels(BoomConn(), {"Formula"}, set(), "throwaway")
        assert "connection lost" in caplog.text, (
            "a real failure was swallowed by the duplicate-label handler")


@pytest.mark.slow
class TestPGWrite:
    """Tests for PG+AGE parallel write. Skips if PG unavailable.

    ⚠️ **THESE WRITE TO A THROWAWAY AGE GRAPH, NEVER TO PRODUCTION.**
    This class used to build the full 49k-node graph with `sync_pg=True` and write
    it to the real `sk_eft` graph on every `-m slow` run. Two consequences, both
    measured by a test-quality audit 2026-08-09:

    * **646 s — 47% of the whole slow suite**, and 36% of the entire test estate,
      to make three assertions about a write path.
    * `write_graph_to_pg` opens with an unconditional `MATCH (n) DETACH DELETE n`,
      so a sibling test passing a one-node dummy left the dashboard's datastore
      holding a single fake node after every full run.

    The write path is identical whether the graph has 49,003 nodes or 4. What the
    size bought was runtime, not coverage. A synthetic graph against a per-run
    throwaway AGE graph tests the same code and cannot touch production data.
    """

    #: Per-run throwaway graph. Created and dropped by the fixture below; the
    #: production name is never passed from a test.
    TEST_GRAPH = "sk_eft_test_pgwrite"

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
        """A SYNTHETIC graph, written to the throwaway AGE graph.

        Small on purpose: the assertions below are "vertices exist" and "the count
        matches the dict", both of which a 4-node graph exercises exactly as well as
        a 49,003-node one. Creates the graph, writes, yields, then drops it — so a
        crashed run leaves no residue in the shared container either.
        """
        from scripts.build_graph import write_graph_to_pg

        def _node(i, ntype="Formula"):
            return {'id': f'synthetic:{i}', 'type': ntype, 'name': f'n{i}',
                    'label': f'n{i}', 'verification': 'verified', 'detail': '',
                    'meta': {'shape': 'circle'}}

        graph = {
            'nodes': [_node(0), _node(1), _node(2, "Theorem"), _node(3, "Theorem")],
            'links': [{'source': 'synthetic:0', 'target': 'synthetic:2',
                       'type': 'VERIFIES'},
                      {'source': 'synthetic:1', 'target': 'synthetic:3',
                       'type': 'VERIFIES'}],
            'meta': {'node_count': 4, 'edge_count': 2},
        }

        with pg_conn.cursor() as cur:
            cur.execute("LOAD 'age'")
            cur.execute("SET search_path = ag_catalog, '$user', public")
            cur.execute(
                "SELECT count(*) FROM ag_catalog.ag_graph WHERE name = %s",
                (self.TEST_GRAPH,))
            if cur.fetchone()[0] == 0:
                cur.execute("SELECT create_graph(%s)", (self.TEST_GRAPH,))
            pg_conn.commit()

        write_graph_to_pg(graph, graph_name=self.TEST_GRAPH)
        yield graph

        with pg_conn.cursor() as cur:
            cur.execute("LOAD 'age'")
            cur.execute("SET search_path = ag_catalog, '$user', public")
            cur.execute("SELECT drop_graph(%s, true)", (self.TEST_GRAPH,))
            pg_conn.commit()

    def test_write_populates_graph(self, pg_conn, built_graph):
        """Vertices exist in PG after write."""
        with pg_conn.cursor() as cur:
            cur.execute("LOAD 'age'")
            cur.execute("SET search_path = ag_catalog, '$user', public")
            cur.execute("""
                SELECT * FROM cypher('sk_eft_test_pgwrite', $$
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
                SELECT * FROM cypher('sk_eft_test_pgwrite', $$
                    MATCH (n) RETURN count(n)
                $$) AS (cnt agtype)
            """)
            count = int(str(cur.fetchone()[0]))
        assert count == expected, (
            f"PG vertex count {count} != graph node_count {expected}"
        )



# ═══════════════════════════════════════════════════════════════════════
# Phase 5v Wave 2c — new node type extractor tests
# ═══════════════════════════════════════════════════════════════════════

def _assert_valid_node(node: dict, expected_type: str, id_prefix: str) -> None:
    assert _REQUIRED_NODE_FIELDS.issubset(node.keys()), (
        f"Missing fields in {node.get('id')}: {_REQUIRED_NODE_FIELDS - node.keys()}"
    )
    assert node['type'] == expected_type, (
        f"Expected type {expected_type!r}, got {node['type']!r} on {node['id']}"
    )
    assert node['id'].startswith(id_prefix), (
        f"Expected id prefix {id_prefix!r}, got {node['id']!r}"
    )


def _assert_unique_ids(nodes: list[dict]) -> None:
    ids = [n['id'] for n in nodes]
    dupes = [x for x in ids if ids.count(x) > 1]
    assert not dupes, f"Duplicate ids: {dupes[:5]}"


class TestExtractProseClaimNodes:
    """ProseClaim — abstract sentences with narrative-claim tagging."""

    def test_returns_list(self):
        assert isinstance(extract_prose_claim_nodes(), list)

    def test_node_shape(self):
        nodes = extract_prose_claim_nodes()
        if not nodes:
            pytest.skip("No ProseClaim nodes (no papers with abstracts?)")
        _assert_unique_ids(nodes)
        for n in nodes[:10]:
            _assert_valid_node(n, 'ProseClaim', 'proseclaim:')
            assert 'paper' in n['meta']
            assert 'sentence_index' in n['meta']
            assert 'interesting' in n['meta']
            assert isinstance(n['meta'].get('tags'), list)


class TestExtractPythonTestNodes:
    """PythonTest — test functions with test_kind classification."""

    def test_returns_list(self):
        assert isinstance(extract_python_test_nodes(), list)

    def test_node_shape(self):
        nodes = extract_python_test_nodes()
        if not nodes:
            pytest.skip("No PythonTest nodes")
        assert len(nodes) > 100, f"Expected >100 test functions, got {len(nodes)}"
        _assert_unique_ids(nodes)
        valid_kinds = {'golden', 'bounds', 'identity', 'roundtrip', 'unknown'}
        for n in nodes[:20]:
            _assert_valid_node(n, 'PythonTest', 'test:')
            test_kind = n['meta'].get('test_kind')
            assert test_kind in valid_kinds, (
                f"Invalid test_kind {test_kind!r} on {n['id']}"
            )
            assert 'module' in n['meta']
            assert 'referenced_names' in n['meta']


class TestSeverityDeclarationIsValidated:
    """A MISTYPED severity must not silently downgrade a finding.

    Found by PR-review reviewer 6, 2026-08-05. `_SEVERITY_DECL_MAP.get(v)` returns
    `None` for `blockr` / `high` / any token outside the vocabulary; severity then fell
    through to `advisory`, and the file-level BLOCKER escalation was skipped because it
    was gated on `_decl is None` — the `**Severity:**` LINE had matched, only its VALUE
    failed. So a typo'd BLOCKER landed as advisory, the paper read YELLOW, and
    `readiness_submission_gate` passed.

    `review_severity_declared` does not catch it: it counts `**Severity:**` lines and
    never validates the token. Nothing else did either — hence these tests.

    They run the real extractor against a review document written into a temp
    `AutomatedReviews` tree, so the parse path is the production one end to end.
    """

    def _extract(self, tmp_path, monkeypatch, body: str):
        import build_graph as bg
        d = tmp_path / "papers" / "AutomatedReviews" / "2026-09-01-probe"
        d.mkdir(parents=True)
        (d / "D12.md").write_text(body)
        monkeypatch.setattr(bg, "PROJECT_ROOT", tmp_path)
        return bg.extract_review_finding_nodes()

    #: `**BLOCKER**` bolded is the corpus's actual marker — `_BLOCKER_RE` requires the
    #: emphasis, which is what stops the word appearing in prose from escalating a
    #: report (two reviewers tripped that rule by quoting the marker while describing
    #: it). A first draft of this fixture wrote it bare and the escalation never fired,
    #: making the test look like the fix had failed.
    _HEADING = ("### 1.1 — a load-bearing defect in the bundle\n\n"
                "- **Severity:** {sev}\n\nThe body declares this a **BLOCKER**.\n")

    def test_a_declared_blocker_is_critical(self):
        """The positive control — the vocabulary maps as documented."""
        from build_graph import _SEVERITY_DECL_MAP
        assert _SEVERITY_DECL_MAP["blocker"] == "critical"

    def test_a_MISTYPED_severity_does_not_land_as_advisory(self, tmp_path, monkeypatch):
        """FIRES ON THE SEEDED DEFECT. `blockr` is unparseable, so the declaration must
        be treated as ABSENT — which lets the BLOCKER marker in the body escalate — and
        must NOT be accepted as the lowest severity there is."""
        nodes = self._extract(tmp_path, monkeypatch, self._HEADING.format(sev="blockr"))
        assert nodes, "the probe document minted no finding"
        sev = nodes[0]["meta"]["severity"]
        assert sev != "advisory", (
            "a mistyped severity silently downgraded the finding to advisory — a "
            "typo'd BLOCKER then reads YELLOW and readiness_submission_gate passes")
        assert sev == "critical", (
            f"an unparseable declaration must fall through to inference and escalation "
            f"exactly as an absent one; got {sev!r}")

    def test_a_VALID_declaration_still_wins_over_the_body(self, tmp_path, monkeypatch):
        """The other direction, and it is load-bearing: the declared field is
        authoritative precisely so a glyph or a quoted marker in the body cannot
        override it (D12 round-12 finding 8.2). The fall-through above must not have
        re-opened that path for well-formed declarations."""
        nodes = self._extract(tmp_path, monkeypatch, self._HEADING.format(sev="advisory"))
        assert nodes and nodes[0]["meta"]["severity"] == "advisory", (
            "a valid `advisory` declaration was overridden by the BLOCKER token in the "
            "body — the declared field is authoritative")


class TestExtractReviewFindingNodes:
    """ReviewFinding — adversarial review findings with severity + status."""

    def test_returns_list(self):
        assert isinstance(extract_review_finding_nodes(), list)

    def test_node_shape(self):
        """⚠️ THIS TEST WAS RED, AND HAD BEEN SINCE THE DECLARED-SEVERITY CONVENTION
        LANDED (fixed 2026-08-05, PR-review reviewer 6). Nobody saw it because
        `pyproject.toml` deselects `slow` and this module carries that marker.

        The accepted set was hand-listed and had drifted from the production mapping in
        both directions at once: it accepted `blocker`, which the extractor never emits
        (it maps `blocker` -> `critical`), and it omitted `critical`, which is the only
        submission-blocking value there is. So the one assertion in this test could
        never pass on a corpus containing a single 🔴.

        It is now DERIVED from `build_graph.SEVERITY_VALUES` — hoisted to module scope
        with the mapping it comes from, for the same reason `_recurrence_norm` was under
        ADR-009 Phase 0 Guard 3: a test that re-states a mapping asserts nothing about
        the mapping, and drifts from it silently."""
        from build_graph import SEVERITY_VALUES
        nodes = extract_review_finding_nodes()
        if not nodes:
            pytest.skip("No ReviewFinding nodes (no AutomatedReviews dir?)")
        _assert_unique_ids(nodes)
        valid_severity = set(SEVERITY_VALUES)
        assert 'critical' in valid_severity, (
            "the submission-blocking severity is not in the derived set — "
            "`readiness_submission_gate` keys on it")
        # Status set extended 2026-05-14 to match the actual schema in
        # docs/review_finding_supersessions.json (overrides the parser-default
        # 'open'/'fixed'). 'accepted' was added in Phase 6i Wave 3 close
        # (~127 ledger entries) for findings acknowledged as out-of-scope
        # architectural facts (distinct from 'fixed' = remediated and
        # 'wontfix' = rejected); 'propagated'/'applied' are single-use
        # variants from later waves.
        valid_status = {
            'open', 'fixed', 'wontfix', 'duplicate', 'unknown',
            'accepted', 'propagated', 'applied',
        }
        for n in nodes[:10]:
            _assert_valid_node(n, 'ReviewFinding', 'review:')
        # Severity and status are set-membership tests over ~1,500 nodes and cost
        # nothing, so they run over ALL of them rather than the first ten. The `[:10]`
        # cap above is for the structural assertions; applied to these it would mean a
        # bad value at node 900 passes, which is the population-shaped blind spot this
        # audit keeps finding. Both fields gate submission readiness.
        bad_sev = {n['id']: n['meta'].get('severity') for n in nodes
                   if n['meta'].get('severity') not in valid_severity}
        assert not bad_sev, f"severities outside {sorted(valid_severity)}: {bad_sev}"
        bad_status = {n['id']: n['meta'].get('status') for n in nodes
                      if n['meta'].get('status') not in valid_status}
        assert not bad_status, f"statuses outside {sorted(valid_status)}: {bad_status}"


class TestExtractProductionRunNodes:
    """ProductionRun — MC / RHMC / Aristotle run records."""

    def test_returns_list(self):
        assert isinstance(extract_production_run_nodes(), list)

    def test_node_shape(self):
        nodes = extract_production_run_nodes()
        if not nodes:
            pytest.skip("No ProductionRun nodes")
        _assert_unique_ids(nodes)
        for n in nodes[:10]:
            _assert_valid_node(n, 'ProductionRun', 'run:')
            assert 'kind' in n['meta']
            assert 'status' in n['meta']


class TestExtractPlaceholderMarkerNodes:
    """PlaceholderMarker — Lean decls with trivial body on non-trivial statement."""

    def test_returns_list(self):
        assert isinstance(extract_placeholder_marker_nodes(), list)

    def test_node_shape(self):
        nodes = extract_placeholder_marker_nodes()
        if not nodes:
            pytest.skip("No PlaceholderMarker nodes")
        _assert_unique_ids(nodes)
        for n in nodes[:10]:
            _assert_valid_node(n, 'PlaceholderMarker', 'placeholder:')
            assert 'lean_full_name' in n['meta']
            assert 'body_pattern' in n['meta']


class TestExtractContradictionNodes:
    """Contradiction — stub extractor (Wave 2f future wiring)."""

    def test_returns_list(self):
        """Stub returns []; if later wired, each node must validate."""
        nodes = extract_contradiction_nodes()
        assert isinstance(nodes, list)
        for n in nodes:
            _assert_valid_node(n, 'Contradiction', 'contradiction:')


class TestExtractCountMetricNodes:
    """CountMetric — snapshots of canonical counts."""

    def test_returns_list(self):
        assert isinstance(extract_count_metric_nodes(), list)

    def test_node_shape(self):
        nodes = extract_count_metric_nodes()
        if not nodes:
            pytest.skip("No CountMetric nodes (counts.json missing?)")
        _assert_unique_ids(nodes)
        for n in nodes[:10]:
            _assert_valid_node(n, 'CountMetric', 'count:')
            assert 'value' in n['meta']
            assert 'metric' in n['meta']


@pytest.mark.slow
class TestExtractReadinessGateNodes:
    """ReadinessGate — per-paper × per-dimension gate state."""

    def test_returns_list(self):
        assert isinstance(extract_readiness_gate_nodes(), list)

    def test_node_shape(self):
        nodes = extract_readiness_gate_nodes()
        if not nodes:
            pytest.skip("No ReadinessGate nodes (readiness_gates import failed?)")
        _assert_unique_ids(nodes)
        valid_states = {'passed', 'blocked', 'needs-recheck', 'in-progress', 'pending', 'open'}
        for n in nodes[:10]:
            _assert_valid_node(n, 'ReadinessGate', 'gate:')
            assert 'paper' in n['meta']
            assert 'gate' in n['meta']
            assert n['meta'].get('state') in valid_states


# ═══════════════════════════════════════════════════════════════════════
# Phase 5v Wave 2c — new edge type tests
# ═══════════════════════════════════════════════════════════════════════

class TestVerifiesEdges:
    """VERIFIES: PythonTest -> Formula / Parameter / LeanTheorem (with test_kind)."""

    def test_edges_carry_test_kind(self, all_graph_node_ids):
        node_ids = all_graph_node_ids
        edges = extract_verifies_edges(node_ids)
        if not edges:
            pytest.skip("No VERIFIES edges")
        valid_kinds = {'golden', 'bounds', 'identity', 'roundtrip', 'unknown'}
        for e in edges:
            assert e['type'] == 'VERIFIES'
            assert e['source'].startswith('test:')
            assert e.get('test_kind') in valid_kinds


class TestFlagsEdges:
    """FLAGS: ReviewFinding -> any artifact."""

    def test_edge_shape(self, all_graph_node_ids):
        node_ids = all_graph_node_ids
        edges = extract_flags_edges(node_ids)
        if not edges:
            pytest.skip("No FLAGS edges")
        for e in edges:
            assert e['type'] == 'FLAGS'
            assert e['source'].startswith('review:')
            assert e['source'] in node_ids
            assert e['target'] in node_ids


class TestReportsEdges:
    """REPORTS: Paper -> CountMetric (paper_value + delta_pct attributes)."""

    def test_edges_carry_delta(self, all_graph_node_ids):
        node_ids = all_graph_node_ids
        edges = extract_reports_edges(node_ids)
        if not edges:
            pytest.skip("No REPORTS edges")
        for e in edges:
            assert e['type'] == 'REPORTS'
            assert e['source'].startswith('paper:')
            assert e['target'].startswith('count:')
            # delta_pct optional (may be None if canonical value missing)
            assert 'paper_value' in e or 'value' in e


class TestPGWriteWithoutPsycopg:
    """The no-psycopg branch. Deliberately NOT marked slow, and NOT in TestPGWrite.

    This guards against re-arming a wipe of the live 49,003-vertex graph, and it
    needs no database at all — so it belongs on the DEFAULT path. It sat inside
    the `slow`-marked TestPGWrite, which meant the single guard against the most
    destructive failure in this suite ran only under `-m slow`.
    """

    TEST_GRAPH = "sk_eft_test_pgwrite_nopsycopg"

    def test_write_survives_pg_unavailable(self, monkeypatch, caplog):
        """`write_graph_to_pg` does not raise when PG is UNAVAILABLE.

        ⚠️ **THIS TEST USED TO DESTROY THE PRODUCTION PROVENANCE GRAPH.** It called
        `write_graph_to_pg` with a one-node dummy and no isolation. The function
        opens with an unconditional `MATCH (n) DETACH DELETE n` against the real
        `sk_eft` AGE graph — so on any machine where Postgres is UP (it has been,
        for days) the test did not exercise the unavailable path at all. It wiped
        **49,003 vertices / 15,919 edges** and left a single fake node `test:x`,
        silently, on every `-m slow` and `-m ''` run. The dashboard's datastore has
        been holding that fake node after every full suite.

        Found by a scoped test-quality audit, 2026-08-09. The graph was rebuilt
        with `build_graph.py --sync-pg`.

        The name was right and the body was wrong: what this asserts is the
        NO-PSYCOPG branch, so `psycopg` is made unimportable and that branch is the
        only one reachable. Nothing touches a live database.

        ⚠️ **THE ISOLATION WAS ONE BYPASSABLE HOOK, AND IT AIMED AT PRODUCTION.**
        Patching `builtins.__import__` does not stop `importlib.import_module`,
        so any refactor of that import re-arms the wipe described above — and the
        call passed the DEFAULT `graph_name`, i.e. the real `sk_eft`. A reviewer
        defeated the hook and this test noticed nothing, because "must not raise"
        is satisfied by the destructive path succeeding.

        Three guards now, because one is what failed:
          1. the call names `TEST_GRAPH`, never production;
          2. `psycopg.connect` is replaced by a sentinel that FAILS the test if
             reached, so the hook being bypassed is loud rather than silent;
          3. the no-psycopg branch must be positively OBSERVED, not inferred from
             the absence of an exception.
        """
        import builtins
        import logging
        import sys as _sys
        from scripts.build_graph import write_graph_to_pg

        caplog.set_level(logging.DEBUG)

        real_import = builtins.__import__

        def _no_psycopg(name, *a, **kw):
            if name == "psycopg" or name.startswith("psycopg."):
                raise ImportError("psycopg unavailable (simulated)")
            return real_import(name, *a, **kw)

        monkeypatch.setattr(builtins, "__import__", _no_psycopg)

        # Guard 2: if the import hook is ever bypassed, connecting must ABORT the
        # test rather than reach `MATCH (n) DETACH DELETE n`.
        _stub = types.ModuleType("psycopg")
        _stub.connect = lambda *a, **k: pytest.fail(
            "psycopg.connect was reached — the no-psycopg branch was NOT taken "
            "and this test was one refactor away from wiping the live graph")
        monkeypatch.setitem(_sys.modules, "psycopg", _stub)

        dummy_graph = {
            'nodes': [{'id': 'test:x', 'type': 'Formula', 'name': 'x',
                       'label': 'x', 'verification': 'verified', 'detail': '',
                       'meta': {'shape': 'circle'}}],
            'links': [],
            'meta': {'node_count': 1, 'edge_count': 0},
        }
        # Guard 1: never the production graph name, even on the branch that is
        # supposed to return before connecting.
        write_graph_to_pg(dummy_graph, graph_name=self.TEST_GRAPH)

        # Guard 3: assert the branch was TAKEN. "Did not raise" is also true of
        # the destructive path completing successfully, which is exactly how the
        # original wipe went unnoticed for days.
        assert any("psycopg" in r.getMessage().lower() for r in caplog.records), (
            "no 'psycopg unavailable' log — the unavailable branch was not "
            "observed, so this test asserts nothing about it")


class TestTheFindingIdMinterIsShared:
    """One minter, importable, and the one production actually uses.

    `close_finding.py` mints ids to WRITE the supersession ledger;
    `extract_review_finding_nodes` mints them to READ it back. Two implementations
    diverging is exactly how 66 review:-scheme ledger records came to reference ids that
    match no node — inert records, whose findings still read `open`.
    """

    def test_mint_finding_id_is_importable_and_stable(self):
        from scripts.build_graph import mint_finding_id
        assert mint_finding_id(
            '2026-08-12-0006-internal-adversarial', 'I1', '5.5'
        ) == 'review:2026-08-12-0006-internal-adversarial:I1:5.5'

    def test_every_minted_node_id_round_trips_through_the_function(self):
        from scripts.build_graph import extract_review_finding_nodes, mint_finding_id
        nodes = extract_review_finding_nodes()
        assert nodes, "no findings extracted — an empty seam is not a clean one"
        for n in nodes:
            m = n['meta']
            assert n['id'] == mint_finding_id(
                m['review_date'], m['review_name'], m['section']), (
                f"{n['id']} was not produced by mint_finding_id — the extractor and the "
                "minter have diverged, which is the orphan class at its source")


class TestRoutingFieldsAreParsedNotInvented:
    """ADR-012 C7: `Gate:` and `Location:` are ALREADY written on 92-93% of findings.

    The first draft of ADR-012 proposed adding two NEW fields for data the system already
    collects and discards at extraction.
    """

    def test_the_field_parser_reads_a_body_line(self):
        from scripts.build_graph import _parse_finding_field
        body = ("- **Gate:** CitationIntegrity\n"
                "- **Location:** `src/core/citations.py:412`\n"
                "- **Observed:** something\n")
        assert _parse_finding_field(body, 'Gate') == 'CitationIntegrity'
        assert _parse_finding_field(body, 'Location') == '`src/core/citations.py:412`'
        assert _parse_finding_field(body, 'Nope') is None
        assert _parse_finding_field('', 'Gate') is None

    def test_the_live_corpus_populates_both_above_their_measured_floor(self):
        from scripts.build_graph import extract_review_finding_nodes
        ns = extract_review_finding_nodes()
        assert ns, "no findings extracted — an empty seam is not a clean one"
        blocks = sum(1 for n in ns if n['meta'].get('blocks'))
        target = sum(1 for n in ns if n['meta'].get('target'))
        # ⚠️ DENOMINATOR. 93%/92% was measured over SEVERITY-GLYPH SECTIONS (1,178).
        # extract_review_finding_nodes returns a WIDER population (1,631) — not every
        # minted node comes from a section carrying the field template. Measured over
        # nodes: Gate 1241/1631 = 76.1%, Location 1164/1631 = 71.4%.
        assert blocks / len(ns) > 0.70, f"blocks coverage collapsed to {blocks}/{len(ns)}"
        assert target / len(ns) > 0.65, f"target coverage collapsed to {target}/{len(ns)}"


class TestLaneAndReleaseSchemesAreDeclaredOnce:
    """ADR-012 D1/D2/D19 — forward-only routing fields."""

    def test_the_lane_map_is_the_single_declaration(self):
        from scripts.build_graph import _LANE_DECL_MAP
        assert set(_LANE_DECL_MAP) == {
            'lean', 'pyrust', 'substrate', 'prose', 'research', 'infra'}

    def test_there_is_no_operator_release_scheme(self):
        """An operator decision that gates work is itself a queue item with a node id, so
        parking behind it is the plain `blocked_by: <id>` case. A separate token would be a
        second decision-record channel beside the queue."""
        from scripts.build_graph import _RELEASE_SCHEMES
        assert _RELEASE_SCHEMES == ('run:', 'phase:', 'pub:', 'research:')

    def test_an_absent_lane_reads_unclassified_not_a_failure(self):
        from scripts.build_graph import _parse_lane
        assert _parse_lane("- **Observed:** x\n") == 'unclassified'

    def test_a_declared_lane_is_normalised_case_insensitively(self):
        from scripts.build_graph import _parse_lane
        assert _parse_lane("- **Lane:** Substrate\n") == 'substrate'
        assert _parse_lane("- **lane:** `prose`\n") == 'prose'

    def test_an_unknown_lane_is_preserved_verbatim_for_the_check_to_name(self):
        """Never coerced to the nearest known lane — silently mapping `substrat` to
        `substrate` is the defect the severity-value leg was written to close."""
        from scripts.build_graph import _parse_lane
        assert _parse_lane("- **Lane:** wizardry\n") == 'wizardry'

    def test_blocked_by_splits_on_commas_and_strips_backticks(self):
        from scripts.build_graph import _parse_blocked_by
        assert _parse_blocked_by("- **Blocked-by:** `review:d:X:1`, run:mlx-2026\n") == \
            ['review:d:X:1', 'run:mlx-2026']
        assert _parse_blocked_by("- **Observed:** none\n") == []

    def test_the_parser_is_case_insensitive_like_every_other_field_scan(self):
        """`reviews.py`'s _SEV_LINE / _SEV_VALUE / _LANE_VALUE all carry re.I. A
        case-sensitive parser here would let the check validate a field the extractor then
        silently fails to read."""
        from scripts.build_graph import _parse_finding_field
        assert _parse_finding_field("- **gate:** CitationIntegrity\n", 'Gate') == \
            'CitationIntegrity'


class TestBlockedByIsADagWithAConsumer:
    """ADR-012 D10. ⚠️ KNOWLEDGE_GRAPH.md already carries three edge types that gates query
    and nothing emits, and PRODUCES sat expired for a whole wave because a fallback masked
    it. A new edge type ships with a consumer and a test proving the consumer sees it."""

    def test_a_release_scheme_is_not_treated_as_a_node_reference(self):
        from scripts.build_graph import _blocked_by_edges, finding_is_dispatchable
        n = {'id': 'review:d:X:1',
             'meta': {'blocked_by': ['run:mlx-rhmc-2026'], 'status': 'open'}}
        assert _blocked_by_edges([n]) == []
        assert finding_is_dispatchable(n, {'review:d:X:1'}, set()) is False

    def test_an_unrecognised_scheme_raises_rather_than_blocking_forever(self):
        from scripts.build_graph import _blocked_by_edges
        n = {'id': 'review:d:X:1', 'meta': {'blocked_by': ['runs:42'], 'status': 'open'}}
        with pytest.raises(ValueError, match='runs:42'):
            _blocked_by_edges([n])

    def test_a_blocked_by_naming_no_node_raises(self):
        from scripts.build_graph import _blocked_by_edges
        n = {'id': 'review:d:X:1',
             'meta': {'blocked_by': ['review:d:X:99'], 'status': 'open'}}
        with pytest.raises(ValueError, match='review:d:X:99'):
            _blocked_by_edges([n])

    def test_a_resolvable_blocker_emits_an_edge_and_gates_dispatch(self):
        from scripts.build_graph import _blocked_by_edges, finding_is_dispatchable
        a = {'id': 'review:d:X:1',
             'meta': {'blocked_by': ['review:d:X:2'], 'status': 'open'}}
        b = {'id': 'review:d:X:2', 'meta': {'blocked_by': [], 'status': 'open'}}
        assert _blocked_by_edges([a, b]) == [
            {'source': 'review:d:X:1', 'target': 'review:d:X:2', 'type': 'BLOCKED_BY'}]
        ids = {'review:d:X:1', 'review:d:X:2'}
        assert finding_is_dispatchable(a, ids, set()) is False
        assert finding_is_dispatchable(a, ids, {'review:d:X:2'}) is True
        assert finding_is_dispatchable(b, ids, set()) is True

    def test_the_live_corpus_emits_without_raising(self):
        """Zero edges today — `blocked_by` is forward-only. The value of this test is that
        it RAISES the day a malformed one is filed, instead of dropping it."""
        from scripts.build_graph import extract_blocked_by_edges
        assert extract_blocked_by_edges() == []
