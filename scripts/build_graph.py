#!/usr/bin/env python3
"""
SK-EFT Hawking Knowledge Graph Builder
=======================================

Extracts nodes and edges from the project's canonical registries
(provenance, formulas, constants, citations, figures, Lean theorems)
and produces a JSON graph suitable for visualization and integrity analysis.

Usage
-----
    # Dump JSON to stdout:
    python scripts/build_graph.py --json

    # Write JSON to file:
    python scripts/build_graph.py --json --out /tmp/graph.json

    # Check source hash staleness only:
    python scripts/build_graph.py --check
"""

from __future__ import annotations

import argparse
import hashlib
import importlib
import importlib.util
import json
import logging
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

logger = logging.getLogger(__name__)

# Path setup
SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent
sys.path.insert(0, str(PROJECT_ROOT))

LEAN_DIR = PROJECT_ROOT / "lean" / "SKEFTHawking"

# Shape map for all 13 node types
SHAPE_MAP: dict[str, str] = {
    'Paper': 'square',
    'PaperClaim': 'circle',
    'Formula': 'circle',
    'Parameter': 'diamond',
    'PrimarySource': 'triangle',
    'Figure': 'circle',
    'AristotleRun': 'circle',
    'LeanAxiom': 'diamond',
    'LeanTheorem': 'circle',
    'LeanDef': 'circle',
    'LeanStructure': 'square',
    'LeanInductive': 'square',
    'LeanInstance': 'circle',
    'Hypothesis': 'diamond',
}

LEAN_KIND_TO_TYPE: dict[str, str] = {
    'axiom': 'LeanAxiom',
    'theorem': 'LeanTheorem',
    'def': 'LeanDef',
    'structure': 'LeanStructure',
    'class': 'LeanStructure',
    'inductive': 'LeanInductive',
    'instance': 'LeanInstance',
    'opaque': 'LeanDef',
}

# Lean auto-generated helper names (recursors, eliminators, boilerplate).
# ExtractDeps filters .ctorInfo/.recInfo/.quotInfo, but Lean also emits
# per-type helpers classified as theorems/defs: `noConfusion`, `casesOn`,
# `recOn`, `sizeOf_spec`, injectivity lemmas, `match_N`, etc. These carry no
# research content and would otherwise pollute the graph with ~2,100 noise
# nodes, crowding out the ~3,600 substantive declarations.
_AUTOGEN_SHORT_RE = re.compile(
    r'^('
    r'noConfusion(Type)?|casesOn|recOn|sizeOf_spec|'
    r'ctorIdx|ctorElim(Type)?|toCtorIdx|'
    r'elim|inj|injEq|'
    r'match_\d+|eq_\d+|'
    r'repr|toString|decEq|fromNat|ofNat|'
    r'below|brecOn|binductionOn'
    r')$'
)

# Populated by extract_lean_declaration_nodes; consumed by
# _resolve_lean_short() in edge extractors. Maps short name -> list of full
# node IDs so short-name collisions surface as ambiguity (logged + skipped)
# instead of silent drops.
_LEAN_SHORT_INDEX: dict[str, list[str]] = {}


def _resolve_lean_short(name: str, node_ids: set) -> str | None:
    """Resolve a Lean declaration reference to its node ID.

    Accepts either a short name (last namespace component) or a full name
    (with dots). Full names resolve directly; short names resolve through
    _LEAN_SHORT_INDEX. Returns None if missing or ambiguous. Ambiguity is
    logged at WARNING level so silent edge loss is visible.
    """
    # Full-name lookup: if the input contains a dot, try direct match first.
    # Registries like HYPOTHESIS_REGISTRY.dependent_theorems and
    # axiom_deps_project store fully-qualified names.
    if '.' in name:
        direct_id = f'lean:{name}'
        if direct_id in node_ids:
            return direct_id
        # Fall through to short-name lookup using the last component,
        # in case the registry name is qualified but the graph only has
        # a differently-prefixed version.
        short = name.rsplit('.', 1)[-1]
    else:
        short = name

    candidates = _LEAN_SHORT_INDEX.get(short, [])
    in_graph = [c for c in candidates if c in node_ids]
    if not in_graph:
        return None
    if len(in_graph) == 1:
        return in_graph[0]
    logger.warning(
        "Ambiguous Lean name %r resolves to %d candidates: %s — edge skipped",
        name, len(in_graph), in_graph,
    )
    return None

# Platform -> Atom mapping for USED_BY / DEPENDS_ON edges
PLATFORM_ATOM_MAP = {
    'Steinhauer': 'Rb87',
    'Heidelberg': 'K39',
    'Trento': 'Na23',
}


# ═══════════════════════════════════════════════════════════════════════
# Source hash
# ═══════════════════════════════════════════════════════════════════════

def compute_source_hash() -> str:
    """SHA-256 hash (truncated to 16 hex chars) of all source registry files + Lean files."""
    hasher = hashlib.sha256()

    source_files = sorted([
        PROJECT_ROOT / "src" / "core" / "provenance.py",
        PROJECT_ROOT / "src" / "core" / "constants.py",
        PROJECT_ROOT / "src" / "core" / "formulas.py",
        PROJECT_ROOT / "src" / "core" / "citations.py",
        PROJECT_ROOT / "scripts" / "review_figures.py",
    ])

    # Add Lean files
    if LEAN_DIR.is_dir():
        lean_files = sorted(LEAN_DIR.glob("*.lean"))
        source_files.extend(lean_files)

    for fp in source_files:
        if fp.is_file():
            hasher.update(fp.read_bytes())

    return hasher.hexdigest()[:16]


# ═══════════════════════════════════════════════════════════════════════
# Node extractors
# ═══════════════════════════════════════════════════════════════════════

def _lookup_code_value(key: str, EXPERIMENTS: dict, ATOMS: dict, POLARITON_PLATFORMS: dict):
    """Look up the actual code value for a provenance key.

    Checks fundamentals by name (HBAR, K_B, A_BOHR), then splits key on '.'
    to look up group.param in EXPERIMENTS, ATOMS, and POLARITON_PLATFORMS.
    Returns None if not found.
    """
    from src.core.constants import HBAR, K_B, A_BOHR

    # Fundamental constants
    fundamentals = {'HBAR': HBAR, 'K_B': K_B, 'A_BOHR': A_BOHR}
    if key in fundamentals:
        return fundamentals[key]

    # Split on '.' for group.param lookup
    parts = key.split('.', 1)
    if len(parts) != 2:
        return None
    group, param = parts

    for registry in (EXPERIMENTS, ATOMS, POLARITON_PLATFORMS):
        if group in registry and param in registry[group]:
            return registry[group][param]

    return None


def extract_parameter_nodes() -> list[dict]:
    """Extract parameter nodes from PARAMETER_PROVENANCE in provenance.py."""
    from src.core.provenance import PARAMETER_PROVENANCE
    from src.core.constants import EXPERIMENTS, ATOMS, POLARITON_PLATFORMS

    nodes = []
    for key, entry in PARAMETER_PROVENANCE.items():
        # Determine verification status
        if entry.get('value') is None:
            status = 'conflict'
        elif entry.get('human_verified_date'):
            status = 'verified'
        elif entry.get('llm_verified_date'):
            status = 'llm'
        elif entry.get('tier') == 'PROJECTED':
            status = 'projected'
        else:
            status = 'unverified'

        detail = entry.get('detail', '')

        # Check for conflict between provenance value and actual code value
        actual = _lookup_code_value(key, EXPERIMENTS, ATOMS, POLARITON_PLATFORMS)
        has_conflict = False
        if entry.get('value') is not None and actual is not None:
            try:
                rel_err = abs(float(actual) - float(entry['value'])) / max(abs(float(actual)), 1e-30)
                has_conflict = rel_err > 0.001
            except (TypeError, ValueError):
                has_conflict = False

        if has_conflict:
            status = 'conflict'
            detail = f"Code value {actual} != provenance value {entry['value']}. {detail}"

        notes = entry.get('notes', '')
        nodes.append({
            'id': f'param:{key}',
            'type': 'Parameter',
            'label': key,
            'name': key,
            'verification': status,
            'detail': detail,
            'meta': {
                'value': _safe_json_value(entry.get('value')),
                'unit': entry.get('unit', ''),
                'tier': entry.get('tier', ''),
                'source': entry.get('source', ''),
                'doi': entry.get('doi'),
                'llm_verified': entry.get('llm_verified_date') is not None,
                'human_verified': entry.get('human_verified_date') is not None,
                'notes': notes if notes else None,
            },
        })

    return nodes


def _safe_json_value(val):
    """Convert a value to something JSON-serializable."""
    import numpy as np
    if isinstance(val, (np.ndarray, np.generic)):
        return val.tolist()
    if isinstance(val, (int, float, str, bool, type(None))):
        return val
    return str(val)


def extract_formula_nodes() -> list[dict]:
    """Extract formula nodes from function definitions in formulas.py."""
    formulas_path = PROJECT_ROOT / "src" / "core" / "formulas.py"
    source = formulas_path.read_text()

    # Parse function definitions and their docstrings
    pattern = re.compile(
        r'^def\s+([a-z_][a-z0-9_]*)\s*\(',
        re.MULTILINE,
    )

    nodes = []
    for match in pattern.finditer(source):
        name = match.group(1)
        # Skip private helpers
        if name.startswith('_'):
            continue

        # Extract docstring if present
        func_start = match.start()
        lean_refs = []
        aristotle_refs = []
        source_refs = []

        # Find the docstring: look for triple-quoted string after the def line
        docstring_match = re.search(
            r'"""(.*?)"""',
            source[func_start:func_start + 3000],
            re.DOTALL,
        )
        if docstring_match:
            docstring = docstring_match.group(1)
            # Extract Lean refs
            lean_match = re.search(r'Lean:\s*(.+?)(?:\n|$)', docstring)
            if lean_match:
                lean_refs = [r.strip() for r in lean_match.group(1).split(',')]

            # Extract Aristotle refs
            arist_match = re.search(r'Aristotle:\s*(.+?)(?:\n|$)', docstring)
            if arist_match:
                aristotle_refs = [r.strip() for r in arist_match.group(1).split(',')]

            # Extract Source refs
            source_matches = re.findall(r'Source:\s*(.+?)(?:\n|$)', docstring)
            source_refs = [s.strip() for s in source_matches]

        # Determine verification and detail
        has_lean = len(lean_refs) > 0
        verification = 'verified' if has_lean else 'unverified'

        # First line of docstring description
        formula_detail = ''
        if docstring_match:
            docstring_text = docstring_match.group(1).strip()
            first_line = docstring_text.split('\n')[0].strip()
            if first_line:
                formula_detail = first_line

        nodes.append({
            'id': f'formula:{name}',
            'type': 'Formula',
            'label': name,
            'name': name,
            'verification': verification,
            'detail': formula_detail,
            'meta': {
                'lean_refs': lean_refs,
                'aristotle_refs': aristotle_refs,
                'source_refs': source_refs,
            },
        })

    return nodes


def extract_lean_declaration_nodes() -> list[dict]:
    """Extract typed declaration nodes from lean_deps.json.

    Produces LeanAxiom, LeanTheorem, LeanDef, LeanStructure, LeanInductive,
    and LeanInstance nodes with shape metadata and dependency info.
    """
    from scripts.extract_lean_deps import load_lean_deps
    from src.core.constants import ARISTOTLE_THEOREMS, AXIOM_METADATA, HYPOTHESIS_REGISTRY

    declarations = load_lean_deps()

    nodes = []
    seen_ids = set()
    _LEAN_SHORT_INDEX.clear()
    _dropped_autogen = 0
    _dropped_duplicate = 0

    for decl in declarations:
        kind = decl.get('kind', '')
        node_type = LEAN_KIND_TO_TYPE.get(kind)
        if node_type is None:
            continue

        full_name = decl.get('name', '')
        # Short name: last component after last '.'
        short_name = full_name.rsplit('.', 1)[-1] if '.' in full_name else full_name

        # Skip Lean auto-generated helpers (noConfusion, casesOn, match_N, etc.).
        if _AUTOGEN_SHORT_RE.match(short_name):
            _dropped_autogen += 1
            continue

        # Use the full name as the node ID so theorems with identical short
        # names in different namespaces do not silently collide. The short
        # name is retained as the display label and registered in
        # _LEAN_SHORT_INDEX for edge resolution.
        node_id = f'lean:{full_name}'
        if node_id in seen_ids:
            _dropped_duplicate += 1
            continue
        seen_ids.add(node_id)
        _LEAN_SHORT_INDEX.setdefault(short_name, []).append(node_id)

        # Module name: strip "SKEFTHawking." prefix, take first component
        raw_module = decl.get('module', '')
        module_stripped = raw_module[len('SKEFTHawking.'):] if raw_module.startswith('SKEFTHawking.') else raw_module
        module_name = module_stripped.split('.')[0] if module_stripped else raw_module

        # Determine method
        if kind == 'axiom':
            method = 'axiom'
        elif short_name in ARISTOTLE_THEOREMS:
            run_id = ARISTOTLE_THEOREMS[short_name]
            method = 'manual' if run_id == 'manual' else 'aristotle'
        else:
            method = 'manual'

        # Axiom eliminability (axioms only)
        ax_meta = AXIOM_METADATA.get(short_name, {}) if kind == 'axiom' else {}
        eliminability = ax_meta.get('eliminability')
        eliminability_reason = ax_meta.get('reason')

        # Dependency short names
        axiom_deps_project_short = [
            n.rsplit('.', 1)[-1] if '.' in n else n
            for n in decl.get('axiom_deps_project', [])
        ]
        axiom_deps_core_short = [
            n.rsplit('.', 1)[-1] if '.' in n else n
            for n in decl.get('axiom_deps_core', [])
        ]

        nodes.append({
            'id': node_id,
            'type': node_type,
            'label': short_name,
            'name': short_name,
            'verification': 'verified',
            'detail': f'{module_name}.lean',
            'meta': {
                'module': module_name,
                'kind': kind,
                'method': method,
                'aristotle_run_id': ARISTOTLE_THEOREMS.get(short_name),
                'shape': SHAPE_MAP.get(node_type, 'circle'),
                'lean_kind': kind,
                'full_name': full_name,
                'axiom_deps_project': axiom_deps_project_short,
                'axiom_deps_core': axiom_deps_core_short,
                'eliminability': eliminability,
                'eliminability_reason': eliminability_reason,
                'field_constraints': decl.get('structure_fields', []),
                'type_signature': decl.get('type', ''),
            },
        })

    _colliding = sum(1 for v in _LEAN_SHORT_INDEX.values() if len(v) > 1)
    logger.info(
        "Lean extraction: %d decls in, %d nodes out "
        "(%d autogen skipped, %d duplicate-id skipped, "
        "%d unique short names, %d colliding short names)",
        len(declarations), len(nodes),
        _dropped_autogen, _dropped_duplicate,
        len(_LEAN_SHORT_INDEX), _colliding,
    )
    return nodes


def extract_hypothesis_nodes():
    """Extract Hypothesis nodes and ASSUMES edges from HYPOTHESIS_REGISTRY.

    Produces Hypothesis nodes (diamond shape, coral color) and ASSUMES edges
    connecting dependent Lean theorems to their hypotheses.
    """
    from src.core.constants import HYPOTHESIS_REGISTRY

    nodes = []
    edges = []

    for key, hyp in HYPOTHESIS_REGISTRY.items():
        if hyp.get('status') == 'eliminated':
            continue

        node_id = f"hyp:{key}"
        nodes.append({
            'id': node_id,
            'type': 'Hypothesis',
            'label': key.replace('_', ' ').title(),
            'name': key,
            'verification': 'unverified',  # hypotheses are by definition unproved
            'detail': hyp.get('statement', ''),
            'meta': {
                'status': hyp.get('status', 'active'),
                'eliminability': hyp.get('eliminability', 'unknown'),
                'elimination_path': hyp.get('elimination_path', ''),
                'source': hyp.get('source', ''),
                'risk': hyp.get('risk', ''),
                'circularity_note': hyp.get('circularity_note', ''),
                'module': hyp.get('module', ''),
            },
        })

        # Create ASSUMES edges from dependent theorems. HYPOTHESIS_REGISTRY
        # stores fully-qualified names (e.g. `SKEFTHawking.Foo.bar`), which
        # we emit directly as full-name node IDs. Short-name entries (no
        # dot) are resolved via _LEAN_SHORT_INDEX; ambiguity is logged.
        # node_ids filtering happens later in extract_all_edges.
        for thm_name in hyp.get('dependent_theorems', []):
            if '.' in thm_name:
                edges.append({
                    'source': f'lean:{thm_name}',
                    'target': node_id,
                    'type': 'ASSUMES',
                })
                continue
            candidates = _LEAN_SHORT_INDEX.get(thm_name, [])
            if len(candidates) == 1:
                edges.append({
                    'source': candidates[0],
                    'target': node_id,
                    'type': 'ASSUMES',
                })
            elif len(candidates) > 1:
                logger.warning(
                    "ASSUMES edge: short name %r ambiguous (%d candidates) — skipped",
                    thm_name, len(candidates),
                )

    return nodes, edges


# Backward compatibility alias for tests/code that imports the old name
extract_lean_theorem_nodes = extract_lean_declaration_nodes


def extract_aristotle_run_nodes() -> list[dict]:
    """Extract Aristotle run nodes from ARISTOTLE_THEOREMS, deduplicated by run_id."""
    from src.core.constants import ARISTOTLE_THEOREMS

    # Group theorems by run_id, skip 'manual'
    runs: dict[str, list[str]] = {}
    for thm_name, run_id in ARISTOTLE_THEOREMS.items():
        if run_id == 'manual':
            continue
        runs.setdefault(run_id, []).append(thm_name)

    nodes = []
    for run_id, theorems in sorted(runs.items()):
        nodes.append({
            'id': f'aristotle:{run_id}',
            'type': 'AristotleRun',
            'label': run_id,
            'name': run_id,
            'verification': 'verified',
            'detail': f'{len(theorems)} theorems proved',
            'meta': {
                'theorem_count': len(theorems),
                'theorems': sorted(theorems),
            },
        })

    return nodes


def extract_primary_source_nodes() -> list[dict]:
    """Extract primary source nodes from CITATION_REGISTRY in citations.py."""
    from src.core.citations import CITATION_REGISTRY

    nodes = []
    for key, entry in CITATION_REGISTRY.items():
        source_detail = entry.get('notes', '') or entry.get('title', '')
        nodes.append({
            'id': f'source:{key}',
            'type': 'PrimarySource',
            'label': key,
            'name': key,
            'verification': 'verified',
            'detail': source_detail,
            'meta': {
                'authors': entry.get('authors', ''),
                'title': entry.get('title', ''),
                'journal': entry.get('journal'),
                'volume': entry.get('volume'),
                'page': entry.get('page'),
                'year': entry.get('year'),
                'doi': entry.get('doi'),
                'arxiv': entry.get('arxiv'),
                'doi_verified': entry.get('doi_verified'),
                'used_in': entry.get('used_in', []),
                'provides': entry.get('provides', []),
                'notes': entry.get('notes', ''),
            },
        })

    return nodes


def extract_paper_nodes() -> list[dict]:
    """Extract paper nodes from PAPER_DEPENDENCIES in provenance.py."""
    from src.core.provenance import PAPER_DEPENDENCIES

    nodes = []
    for key, entry in PAPER_DEPENDENCIES.items():
        nodes.append({
            'id': f'paper:{key}',
            'type': 'Paper',
            'label': key,
            'name': entry.get('title', key),
            'verification': 'verified',
            'detail': entry.get('topic', ''),
            'meta': {
                'topic': entry.get('topic', ''),
                'formulas': entry.get('formulas', []),
                'lean_modules': entry.get('lean_modules', []),
                'platforms': entry.get('platforms', []),
                'n_claims': len(entry.get('key_claims', [])),
            },
        })

    return nodes


def extract_paper_claim_nodes() -> list[dict]:
    """Extract paper claim nodes from key_claims in PAPER_DEPENDENCIES."""
    from src.core.provenance import PAPER_DEPENDENCIES

    nodes = []
    for paper_key, entry in PAPER_DEPENDENCIES.items():
        for idx, claim_text in enumerate(entry.get('key_claims', [])):
            nodes.append({
                'id': f'claim:{paper_key}:{idx}',
                'type': 'PaperClaim',
                'label': claim_text[:60] + ('...' if len(claim_text) > 60 else ''),
                'name': claim_text,
                'verification': 'verified',
                'detail': claim_text,
                'meta': {
                    'paper': paper_key,
                    'index': idx,
                    'full_text': claim_text,
                },
            })

    return nodes


def extract_figure_nodes() -> list[dict]:
    """Extract figure nodes from FIGURE_REGISTRY in review_figures.py."""
    # Import via importlib to avoid circular deps from review_figures.py's sys.path manipulation
    spec = importlib.util.spec_from_file_location(
        "review_figures",
        str(PROJECT_ROOT / "scripts" / "review_figures.py"),
    )
    mod = importlib.util.module_from_spec(spec)
    # NOTE: This registers review_figures in sys.modules as a side effect.
    # Acceptable for Phase 1; if review_figures gains module-scope side effects,
    # consider extracting FIGURE_REGISTRY to a shared data module.
    sys.modules["review_figures"] = mod
    # Suppress main-level side effects by patching argparse
    _orig_argv = sys.argv
    sys.argv = ['review_figures.py']
    try:
        spec.loader.exec_module(mod)
    finally:
        sys.argv = _orig_argv

    nodes = []
    for fig_spec in mod.FIGURE_REGISTRY:
        nodes.append({
            'id': f'figure:{fig_spec.name}',
            'type': 'Figure',
            'label': fig_spec.name,
            'name': fig_spec.name,
            'verification': 'verified',
            'detail': fig_spec.caption,
            'meta': {
                'function': fig_spec.function,
                'caption': fig_spec.caption,
                'expected_traces': fig_spec.expected_traces,
            },
        })

    return nodes


# ═══════════════════════════════════════════════════════════════════════
# Aggregate node extraction
# ═══════════════════════════════════════════════════════════════════════

def extract_all_nodes() -> list[dict]:
    """Extract all nodes from all extractors."""
    nodes = []
    nodes.extend(extract_parameter_nodes())
    nodes.extend(extract_formula_nodes())
    nodes.extend(extract_lean_declaration_nodes())
    nodes.extend(extract_aristotle_run_nodes())
    nodes.extend(extract_primary_source_nodes())
    nodes.extend(extract_paper_nodes())
    nodes.extend(extract_paper_claim_nodes())
    nodes.extend(extract_figure_nodes())

    # Hypothesis nodes + ASSUMES edges
    hyp_nodes, _hyp_edges = extract_hypothesis_nodes()
    nodes.extend(hyp_nodes)
    # (edges are added separately in build_all_edges)

    # Add shape metadata to all node types that don't already have it
    for node in nodes:
        if 'shape' not in node.get('meta', {}):
            node.setdefault('meta', {})['shape'] = SHAPE_MAP.get(node['type'], 'circle')

    return nodes


# ═══════════════════════════════════════════════════════════════════════
# Edge extractors
# ═══════════════════════════════════════════════════════════════════════

def extract_claims_edges(node_ids: set) -> list[dict]:
    """CLAIMS: Paper -> PaperClaim."""
    from src.core.provenance import PAPER_DEPENDENCIES

    edges = []
    for paper_key, entry in PAPER_DEPENDENCIES.items():
        paper_id = f'paper:{paper_key}'
        if paper_id not in node_ids:
            continue
        for idx in range(len(entry.get('key_claims', []))):
            claim_id = f'claim:{paper_key}:{idx}'
            if claim_id in node_ids:
                edges.append({
                    'source': paper_id,
                    'target': claim_id,
                    'type': 'CLAIMS',
                })

    return edges


def extract_grounded_in_edges(node_ids: set) -> list[dict]:
    """GROUNDED_IN: PaperClaim -> Formula."""
    from src.core.provenance import PAPER_DEPENDENCIES

    # TODO Phase 2: PAPER_DEPENDENCIES doesn't map individual claims to specific formulas.
    # Currently produces Cartesian product (all claims × all formulas per paper).
    # Refine when claim-level formula mapping is available.
    edges = []
    seen = set()
    for paper_key, entry in PAPER_DEPENDENCIES.items():
        formulas = entry.get('formulas', [])
        for idx in range(len(entry.get('key_claims', []))):
            claim_id = f'claim:{paper_key}:{idx}'
            if claim_id not in node_ids:
                continue
            for fname in formulas:
                formula_id = f'formula:{fname}'
                if formula_id in node_ids:
                    edge_key = (claim_id, formula_id)
                    if edge_key not in seen:
                        seen.add(edge_key)
                        edges.append({
                            'source': claim_id,
                            'target': formula_id,
                            'type': 'GROUNDED_IN',
                        })

    return edges


def extract_verified_by_edges(node_ids: set) -> list[dict]:
    """VERIFIED_BY: Formula -> LeanTheorem (from Lean: refs in formulas.py docstrings)."""
    formula_nodes = [n for n in extract_formula_nodes()]

    edges = []
    seen = set()
    for fnode in formula_nodes:
        formula_id = fnode['id']
        if formula_id not in node_ids:
            continue
        lean_refs = fnode.get('meta', {}).get('lean_refs', [])
        for ref in lean_refs:
            # Clean up: ref might be "theorem_name (Module.lean)" or just "theorem_name"
            clean_ref = ref.split('(')[0].strip().split(' ')[0].strip()
            if not clean_ref:
                continue
            lean_id = _resolve_lean_short(clean_ref, node_ids)
            if lean_id is None:
                continue
            edge_key = (formula_id, lean_id)
            if edge_key not in seen:
                seen.add(edge_key)
                edges.append({
                    'source': formula_id,
                    'target': lean_id,
                    'type': 'VERIFIED_BY',
                })

    return edges


def extract_proved_by_edges(node_ids: set) -> list[dict]:
    """PROVED_BY: LeanTheorem -> AristotleRun (skip 'manual')."""
    from src.core.constants import ARISTOTLE_THEOREMS

    edges = []
    seen = set()
    for thm_name, run_id in ARISTOTLE_THEOREMS.items():
        if run_id == 'manual':
            continue
        lean_id = _resolve_lean_short(thm_name, node_ids)
        if lean_id is None:
            continue
        aristotle_id = f'aristotle:{run_id}'
        if aristotle_id not in node_ids:
            continue
        edge_key = (lean_id, aristotle_id)
        if edge_key not in seen:
            seen.add(edge_key)
            edges.append({
                'source': lean_id,
                'target': aristotle_id,
                'type': 'PROVED_BY',
            })

    return edges


def extract_used_by_edges(node_ids: set) -> list[dict]:
    """USED_BY: Parameter -> Formula.

    Inferred: papers list platforms and formulas; a formula belonging to a paper
    using platform X depends on X's params and the corresponding atom's params.
    """
    from src.core.provenance import PAPER_DEPENDENCIES, PARAMETER_PROVENANCE

    edges = []
    seen = set()

    for _paper_key, entry in PAPER_DEPENDENCIES.items():
        platforms = entry.get('platforms', [])
        formulas = entry.get('formulas', [])

        # Collect relevant parameter prefixes for these platforms
        param_prefixes = set()
        for platform in platforms:
            param_prefixes.add(platform)
            atom = PLATFORM_ATOM_MAP.get(platform)
            if atom:
                param_prefixes.add(atom)

        # Also add fundamental constants if any formulas exist
        if formulas:
            param_prefixes.update(['HBAR', 'K_B', 'A_BOHR'])

        for fname in formulas:
            formula_id = f'formula:{fname}'
            if formula_id not in node_ids:
                continue
            for pkey in PARAMETER_PROVENANCE:
                # Check if this parameter matches any relevant prefix
                if any(pkey == prefix or pkey.startswith(f'{prefix}.') for prefix in param_prefixes):
                    param_id = f'param:{pkey}'
                    if param_id in node_ids:
                        edge_key = (param_id, formula_id)
                        if edge_key not in seen:
                            seen.add(edge_key)
                            edges.append({
                                'source': param_id,
                                'target': formula_id,
                                'type': 'USED_BY',
                            })

    return edges


def extract_sourced_from_edges(node_ids: set) -> list[dict]:
    """SOURCED_FROM: Parameter -> PrimarySource (match doi)."""
    from src.core.provenance import PARAMETER_PROVENANCE
    from src.core.citations import CITATION_REGISTRY

    # Build DOI -> citation key map
    doi_to_key: dict[str, str] = {}
    for ckey, centry in CITATION_REGISTRY.items():
        doi = centry.get('doi')
        if doi:
            doi_to_key[doi] = ckey

    edges = []
    seen = set()
    for pkey, pentry in PARAMETER_PROVENANCE.items():
        param_id = f'param:{pkey}'
        if param_id not in node_ids:
            continue
        pdoi = pentry.get('doi')
        if pdoi and pdoi in doi_to_key:
            source_id = f'source:{doi_to_key[pdoi]}'
            if source_id in node_ids:
                edge_key = (param_id, source_id)
                if edge_key not in seen:
                    seen.add(edge_key)
                    edges.append({
                        'source': param_id,
                        'target': source_id,
                        'type': 'SOURCED_FROM',
                    })

    return edges


def extract_depends_on_edges(node_ids: set) -> list[dict]:
    """DEPENDS_ON: Paper -> Parameter (via platforms)."""
    from src.core.provenance import PAPER_DEPENDENCIES, PARAMETER_PROVENANCE

    edges = []
    seen = set()

    for paper_key, entry in PAPER_DEPENDENCIES.items():
        paper_id = f'paper:{paper_key}'
        if paper_id not in node_ids:
            continue

        platforms = entry.get('platforms', [])
        param_prefixes = set()
        for platform in platforms:
            param_prefixes.add(platform)
            atom = PLATFORM_ATOM_MAP.get(platform)
            if atom:
                param_prefixes.add(atom)

        for pkey in PARAMETER_PROVENANCE:
            if any(pkey == prefix or pkey.startswith(f'{prefix}.') for prefix in param_prefixes):
                param_id = f'param:{pkey}'
                if param_id in node_ids:
                    edge_key = (paper_id, param_id)
                    if edge_key not in seen:
                        seen.add(edge_key)
                        edges.append({
                            'source': paper_id,
                            'target': param_id,
                            'type': 'DEPENDS_ON',
                        })

    return edges


def extract_cites_edges(node_ids: set) -> list[dict]:
    """CITES: Formula -> PrimarySource (from Source: refs in docstrings)."""
    from src.core.citations import CITATION_REGISTRY

    formula_nodes = extract_formula_nodes()

    # Build lookup: first author last name -> citation key
    author_to_key: dict[str, list[str]] = {}
    for ckey, centry in CITATION_REGISTRY.items():
        authors = centry.get('authors', '')
        # Extract first author's last name
        first_author = authors.split(',')[0].strip()
        last_name = first_author.split()[-1] if first_author else ''
        if last_name:
            author_to_key.setdefault(last_name, []).append(ckey)

    edges = []
    seen = set()
    for fnode in formula_nodes:
        formula_id = fnode['id']
        if formula_id not in node_ids:
            continue
        source_refs = fnode.get('meta', {}).get('source_refs', [])
        for ref_text in source_refs:
            # Try to match by author last name
            for last_name, ckeys in author_to_key.items():
                if last_name in ref_text:
                    for ckey in ckeys:
                        source_id = f'source:{ckey}'
                        if source_id in node_ids:
                            edge_key = (formula_id, source_id)
                            if edge_key not in seen:
                                seen.add(edge_key)
                                edges.append({
                                    'source': formula_id,
                                    'target': source_id,
                                    'type': 'CITES',
                                })

    return edges


def extract_has_figure_edges(node_ids: set) -> list[dict]:
    """HAS_FIGURE: Paper -> Figure.

    Maps papers to the figures they include, inferred from \\includegraphics
    in paper .tex files.  Since claim-level figure assignments aren't yet
    available, edges go from Paper nodes directly to Figure nodes.
    """
    PAPER_FIGURE_MAP = {
        'paper1_first_order': [
            'fig1_transonic_profiles', 'fig2_correction_hierarchy',
            'fig4_spin_sonic_enhancement',
        ],
        'paper2_second_order': [
            'fig7_cgl_fdr_pattern', 'fig8_even_vs_odd_kernel',
            'fig11_on_shell_vanishing',
        ],
        'paper3_gauge_erasure': [
            'fig20_sm_scorecard', 'fig21_erasure_survey',
        ],
        'paper4_wkb_connection': [
            'fig22_complex_turning_point', 'fig25_hawking_spectrum_exact',
            'fig27_exact_vs_perturbative',
        ],
        'paper5_adw_gap': [
            'fig28_adw_effective_potential', 'fig29_adw_phase_diagram',
            'fig30_adw_ng_modes',
        ],
        'paper6_vestigial': [
            'fig45_vestigial_effective_potential', 'fig42_vestigial_phase_diagram',
            'fig51_vestigial_binder_crossing', 'fig52_vestigial_susceptibility_split',
        ],
        'paper7_chirality_formal': [
            'fig53_gs_condition_formalization', 'fig54_lean_theorem_summary',
            'fig60_tpf_evasion_architecture', 'fig61_fock_exterior_algebra',
        ],
    }

    edges = []
    seen = set()
    for paper_key, figure_names in PAPER_FIGURE_MAP.items():
        paper_id = f'paper:{paper_key}'
        if paper_id not in node_ids:
            continue
        for fig_name in figure_names:
            figure_id = f'figure:{fig_name}'
            if figure_id in node_ids:
                edge_key = (paper_id, figure_id)
                if edge_key not in seen:
                    seen.add(edge_key)
                    edges.append({
                        'source': paper_id,
                        'target': figure_id,
                        'type': 'HAS_FIGURE',
                    })

    return edges


def extract_depends_on_axiom_edges(node_ids: set) -> list[dict]:
    """DEPENDS_ON_AXIOM: LeanTheorem/LeanDef/etc. -> LeanAxiom."""
    lean_nodes = extract_lean_declaration_nodes()

    edges = []
    seen = set()

    for node in lean_nodes:
        src_id = node['id']
        if src_id not in node_ids:
            continue
        short_name = node['name']
        for axiom_short in node.get('meta', {}).get('axiom_deps_project', []):
            target_id = _resolve_lean_short(axiom_short, node_ids)
            if target_id is None:
                continue
            # Skip self-edges
            if src_id == target_id:
                continue
            edge_key = (src_id, target_id)
            if edge_key not in seen:
                seen.add(edge_key)
                edges.append({
                    'source': src_id,
                    'target': target_id,
                    'type': 'DEPENDS_ON_AXIOM',
                })

    return edges


def extract_imports_edges(node_ids: set) -> list[dict]:
    """IMPORTS: Formula -> Formula (if one formula calls another, limited in Phase 1)."""
    # Phase 1: detect direct calls from formulas.py source
    formulas_path = PROJECT_ROOT / "src" / "core" / "formulas.py"
    source = formulas_path.read_text()

    # Get all formula function names
    formula_names = set()
    for match in re.finditer(r'^def\s+([a-z_][a-z0-9_]*)\s*\(', source, re.MULTILINE):
        name = match.group(1)
        if not name.startswith('_'):
            formula_names.add(name)

    # Parse each function body for calls to other formula functions
    func_pattern = re.compile(
        r'^def\s+([a-z_][a-z0-9_]*)\s*\(.*?\n(?=^def\s|\Z)',
        re.MULTILINE | re.DOTALL,
    )

    edges = []
    seen = set()
    for match in func_pattern.finditer(source):
        caller = match.group(1)
        if caller.startswith('_'):
            continue
        body = match.group(0)
        caller_id = f'formula:{caller}'
        if caller_id not in node_ids:
            continue

        # Strip leading docstring so we only search code, not docstring text
        body_code = re.sub(r'""".*?"""', '', body, count=1, flags=re.DOTALL)

        for callee in formula_names:
            if callee == caller:
                continue
            # Look for callee( pattern in code-only text
            if re.search(rf'\b{re.escape(callee)}\s*\(', body_code):
                callee_id = f'formula:{callee}'
                if callee_id in node_ids:
                    edge_key = (caller_id, callee_id)
                    if edge_key not in seen:
                        seen.add(edge_key)
                        edges.append({
                            'source': caller_id,
                            'target': callee_id,
                            'type': 'IMPORTS',
                        })

    return edges


# ═══════════════════════════════════════════════════════════════════════
# Aggregate edge extraction
# ═══════════════════════════════════════════════════════════════════════

def extract_all_edges(node_ids: set) -> list[dict]:
    """Extract all edges from all edge extractors, deduplicated."""
    edges = []
    edges.extend(extract_claims_edges(node_ids))
    edges.extend(extract_grounded_in_edges(node_ids))
    edges.extend(extract_verified_by_edges(node_ids))
    edges.extend(extract_proved_by_edges(node_ids))
    edges.extend(extract_used_by_edges(node_ids))
    edges.extend(extract_sourced_from_edges(node_ids))
    edges.extend(extract_depends_on_edges(node_ids))
    edges.extend(extract_cites_edges(node_ids))
    edges.extend(extract_has_figure_edges(node_ids))
    edges.extend(extract_imports_edges(node_ids))
    edges.extend(extract_depends_on_axiom_edges(node_ids))

    # ASSUMES edges from HYPOTHESIS_REGISTRY
    _hyp_nodes, hyp_edges = extract_hypothesis_nodes()
    for edge in hyp_edges:
        if edge['source'] in node_ids and edge['target'] in node_ids:
            edges.append(edge)

    # Final deduplication (belt-and-suspenders)
    deduped = []
    seen = set()
    for edge in edges:
        key = (edge['source'], edge['target'], edge['type'])
        if key not in seen:
            seen.add(key)
            deduped.append(edge)

    return deduped


# ═══════════════════════════════════════════════════════════════════════
# PG+AGE parallel write
# ═══════════════════════════════════════════════════════════════════════

def _cypher_escape(s) -> str:
    """Escape a string for use in AGE Cypher property values."""
    if s is None:
        return ''
    return str(s).replace("\\", "\\\\").replace("'", "\\'")


def _create_age_labels(conn, node_types: set, edge_types: set) -> None:
    """Create AGE vertex and edge labels using autocommit to avoid transaction pollution.

    Each CREATE label is its own statement; errors (label already exists) are
    ignored individually without affecting the surrounding transaction.
    """
    # Use autocommit so each label creation is its own transaction
    old_autocommit = conn.autocommit
    conn.autocommit = True
    try:
        with conn.cursor() as cur:
            cur.execute("LOAD 'age'")
            cur.execute("SET search_path = ag_catalog, '$user', public")
            for ntype in sorted(node_types):
                try:
                    cur.execute(
                        f"SELECT create_vlabel('sk_eft', '{_cypher_escape(ntype)}')"
                    )
                except Exception:
                    pass  # Label already exists
            for etype in sorted(edge_types):
                try:
                    cur.execute(
                        f"SELECT create_elabel('sk_eft', '{_cypher_escape(etype)}')"
                    )
                except Exception:
                    pass  # Label already exists
    finally:
        conn.autocommit = old_autocommit


def write_graph_to_pg(graph: dict) -> None:
    """Write all nodes and edges to PostgreSQL + Apache AGE (best-effort).

    If psycopg is unavailable or the connection fails, logs a warning and
    returns — never raises.  JSON extraction is unaffected by PG failures.

    Connection: host=localhost port=5433 dbname=sk_eft_provenance
                user=sk_eft password=sk_eft_local  graph=sk_eft
    """
    # --- 1. Import psycopg ---
    try:
        import psycopg  # type: ignore
    except ImportError:
        logger.warning("psycopg not available — skipping PG+AGE write")
        return

    # --- 2. Connect ---
    try:
        conn = psycopg.connect(
            "host=localhost port=5433 dbname=sk_eft_provenance "
            "user=sk_eft password=sk_eft_local"
        )
    except Exception as exc:
        logger.warning("PG+AGE connection failed: %s — skipping write", exc)
        return

    try:
        # --- 4 & 5. Create vertex/edge labels (idempotent, autocommit each) ---
        node_types = {n['type'] for n in graph['nodes']}
        edge_types = {e['type'] for e in graph['links']}
        _create_age_labels(conn, node_types, edge_types)

        # --- 3, 6, 7, 8. Clear + insert all in one transaction ---
        with conn:
            with conn.cursor() as cur:
                cur.execute("LOAD 'age'")
                cur.execute("SET search_path = ag_catalog, '$user', public")

                # --- 3. Clear existing data ---
                cur.execute("""
                    SELECT * FROM cypher('sk_eft', $$
                        MATCH (n) DETACH DELETE n
                    $$) AS (a agtype)
                """)

                # --- 6. Insert all nodes ---
                for node in graph['nodes']:
                    ntype = _cypher_escape(node['type'])
                    nid = _cypher_escape(node['id'])
                    name = _cypher_escape(node.get('name', ''))
                    label = _cypher_escape(node.get('label', ''))
                    verification = _cypher_escape(node.get('verification', ''))
                    detail = _cypher_escape(node.get('detail', ''))
                    shape = _cypher_escape(node.get('meta', {}).get('shape', ''))
                    meta_str = _cypher_escape(json.dumps(node.get('meta', {}), default=str))

                    cur.execute(f"""
                        SELECT * FROM cypher('sk_eft', $$
                            CREATE (:{ntype} {{
                                id: '{nid}',
                                name: '{name}',
                                label: '{label}',
                                verification: '{verification}',
                                detail: '{detail}',
                                shape: '{shape}',
                                meta: '{meta_str}'
                            }})
                        $$) AS (a agtype)
                    """)

                # --- 7. Insert all edges ---
                for edge in graph['links']:
                    etype = _cypher_escape(edge['type'])
                    src = _cypher_escape(edge['source'])
                    tgt = _cypher_escape(edge['target'])

                    cur.execute(f"""
                        SELECT * FROM cypher('sk_eft', $$
                            MATCH (a {{id: '{src}'}}), (b {{id: '{tgt}'}})
                            CREATE (a)-[:{etype}]->(b)
                        $$) AS (a agtype)
                    """)

        # --- 8. Commit (handled by `with conn:` context manager above) ---
        node_count = len(graph['nodes'])
        edge_count = len(graph['links'])
        logger.info(
            "PG+AGE write complete: %d nodes, %d edges",
            node_count,
            edge_count,
        )

    except Exception as exc:
        # --- 9. Rollback on failure ---
        try:
            conn.rollback()
        except Exception:
            pass
        logger.warning("PG+AGE write failed: %s — graph JSON unaffected", exc)
    finally:
        try:
            conn.close()
        except Exception:
            pass


# ═══════════════════════════════════════════════════════════════════════
# Full graph builder
# ═══════════════════════════════════════════════════════════════════════

def build_graph_json() -> dict:
    """Build the complete graph and return as a JSON-serializable dict."""
    nodes = extract_all_nodes()
    node_ids = {n['id'] for n in nodes}
    edges = extract_all_edges(node_ids)

    graph = {
        'nodes': nodes,
        'links': edges,
        'meta': {
            'built_at': datetime.now(timezone.utc).isoformat(),
            'source_hash': compute_source_hash(),
            'node_count': len(nodes),
            'edge_count': len(edges),
        },
    }

    try:
        write_graph_to_pg(graph)
    except Exception as exc:
        logger.warning("PG+AGE write failed: %s", exc)

    return graph


# ═══════════════════════════════════════════════════════════════════════
# CLI
# ═══════════════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(description='Build SK-EFT Hawking knowledge graph.')
    parser.add_argument('--json', action='store_true', help='Dump JSON to stdout')
    parser.add_argument('--out', type=str, default=None, help='Write JSON to file')
    parser.add_argument('--check', action='store_true', help='Print source hash only')
    args = parser.parse_args()

    if args.check:
        print(compute_source_hash())
        return

    graph = build_graph_json()

    if args.out:
        with open(args.out, 'w') as f:
            json.dump(graph, f, indent=2, default=str)
        print(f"Wrote {args.out}: {graph['meta']['node_count']} nodes, "
              f"{graph['meta']['edge_count']} edges, "
              f"hash={graph['meta']['source_hash']}", file=sys.stderr)
    elif args.json:
        print(json.dumps(graph, indent=2, default=str))
    else:
        # Summary
        meta = graph['meta']
        print(f"SK-EFT Knowledge Graph")
        print(f"  Source hash: {meta['source_hash']}")
        print(f"  Nodes: {meta['node_count']}")
        print(f"  Edges: {meta['edge_count']}")
        print()

        # Node breakdown
        from collections import Counter
        node_types = Counter(n['type'] for n in graph['nodes'])
        print("  Node types:")
        for ntype, count in sorted(node_types.items()):
            print(f"    {ntype}: {count}")

        edge_types = Counter(e['type'] for e in graph['links'])
        print("  Edge types:")
        for etype, count in sorted(edge_types.items()):
            print(f"    {etype}: {count}")


if __name__ == '__main__':
    main()
