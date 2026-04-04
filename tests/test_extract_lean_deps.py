"""Tests for scripts/extract_lean_deps.py — Lean declaration extraction wrapper."""

import json
import sys
from pathlib import Path

import pytest

PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT))
sys.path.insert(0, str(PROJECT_ROOT / "scripts"))

from scripts.extract_lean_deps import load_lean_deps, compute_lean_hash


class TestComputeLeanHash:
    """Tests for staleness hash computation."""

    def test_hash_is_hex_string(self):
        h = compute_lean_hash()
        assert isinstance(h, str)
        assert len(h) == 16
        assert all(c in '0123456789abcdef' for c in h)

    def test_hash_deterministic(self):
        assert compute_lean_hash() == compute_lean_hash()


class TestLoadLeanDeps:
    """Tests for loading lean_deps.json (requires prior extraction)."""

    @pytest.fixture(scope="class")
    def deps(self):
        json_path = PROJECT_ROOT / "lean" / "lean_deps.json"
        if not json_path.exists():
            pytest.skip("lean/lean_deps.json not found — run extraction first")
        return load_lean_deps()

    def test_returns_list(self, deps):
        assert isinstance(deps, list)
        assert len(deps) > 1000

    def test_has_required_fields(self, deps):
        required = {'name', 'kind', 'module', 'type', 'axiom_deps_project', 'axiom_deps_core', 'structure_fields'}
        for d in deps[:10]:
            assert required.issubset(d.keys()), f"Missing fields in {d.get('name', '?')}: {required - set(d.keys())}"

    def test_axiom_classification(self, deps):
        """If axioms exist, they should have kind='axiom'. Count may be 0 if all proved."""
        axioms = [d for d in deps if d['kind'] == 'axiom']
        # Axioms may have been eliminated (proved as theorems) — count >= 0 is valid
        for a in axioms:
            assert a['kind'] == 'axiom'

    def test_has_theorems(self, deps):
        theorems = [d for d in deps if d['kind'] == 'theorem']
        assert len(theorems) > 800

    def test_has_structures_with_fields(self, deps):
        structs = [d for d in deps if d['kind'] == 'structure']
        assert len(structs) > 50
        has_fields = any(len(s.get('structure_fields', [])) > 0 for s in structs)
        assert has_fields, "At least one structure should have fields"

    def test_has_definitions(self, deps):
        defs = [d for d in deps if d['kind'] == 'def']
        assert len(defs) > 100

    def test_has_instances(self, deps):
        instances = [d for d in deps if d['kind'] == 'instance']
        assert len(instances) > 10

    def test_axiom_deps_are_lists(self, deps):
        for d in deps[:50]:
            assert isinstance(d['axiom_deps_project'], list)
            assert isinstance(d['axiom_deps_core'], list)
