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

# Shape map for all node types (22 after Phase 5v Wave 2a schema extension).
# Shape vocabulary: diamond = trust boundary (accepted without derivation),
# circle = derived, square = structural, triangle = external.
SHAPE_MAP: dict[str, str] = {
    # Phase 1 base types
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
    # Phase 5v Wave 2a — readiness-system node types.
    # Extractors are stubbed in this wave; populated in Waves 2b–2g.
    'ProseClaim': 'circle',         # Narrative claim not tied to a Formula
    'PythonTest': 'square',         # Test function + test_kind classification
    'ReviewFinding': 'triangle',    # Adversarial review finding (Wave 6)
    'ProductionRun': 'circle',      # MC/RHMC run record + status
    'PlaceholderMarker': 'diamond', # Lean decl with trivial body on non-trivial statement
    'Contradiction': 'triangle',    # Cross-paper inconsistency
    'CountMetric': 'diamond',       # counts.json snapshot
    'ReadinessGate': 'square',      # Per-paper × per-dimension state (Wave 4)
    # Phase 5v Wave 10b — sentence-level prose audit (claims-reviewer-v2)
    'Sentence': 'circle',           # Per-sentence prose unit with chain-of-backing
    'AuditEvent': 'triangle',       # Append-only verification event log entry
    'ClaimCluster': 'square',       # Cross-paper claim equivalence grouping (n-ary; replaces SAME_CLAIM_AS)
    # Phase 6 — Lean module substrate (auto-derived from lean_deps). A claim
    # backed by a whole module resolves to one of these instead of becoming a
    # missing_target dangling edge. Membership is the lazy DECLARES layer.
    'LeanModule': 'square',         # Lean module (file) — container for declarations
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


# Seen-ambiguity dedup: log each unique ambiguous short name at WARNING
# level once per build_graph run. Subsequent occurrences go to DEBUG.
_LEAN_AMBIGUITY_SEEN: set[str] = set()


def _reset_lean_ambiguity_log() -> None:
    _LEAN_AMBIGUITY_SEEN.clear()


def _resolve_lean_short(name: str, node_ids: set) -> str | None:
    """Resolve a Lean declaration reference to its node ID.

    Accepts either a short name (last namespace component) or a full name
    (with dots). Full names resolve directly; short names resolve through
    _LEAN_SHORT_INDEX. Returns None if missing or ambiguous. Each unique
    ambiguous name is logged once per build — repeat occurrences go to
    DEBUG to avoid flooding when a common name (e.g. `cs`, `n`) is
    resolved dozens of times across paper/formula/test extractors.
    """
    if '.' in name:
        direct_id = f'lean:{name}'
        if direct_id in node_ids:
            return direct_id
        short = name.rsplit('.', 1)[-1]
    else:
        short = name

    candidates = _LEAN_SHORT_INDEX.get(short, [])
    in_graph = [c for c in candidates if c in node_ids]
    if not in_graph:
        return None
    if len(in_graph) == 1:
        return in_graph[0]
    if short not in _LEAN_AMBIGUITY_SEEN:
        _LEAN_AMBIGUITY_SEEN.add(short)
        logger.warning(
            "Ambiguous Lean name %r resolves to %d candidates: %s — edges skipped (subsequent hits logged at DEBUG)",
            name, len(in_graph), in_graph,
        )
    else:
        logger.debug(
            "Ambiguous Lean name %r (repeat) — edge skipped",
            name,
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
    from src.core.constants import (
        ARISTOTLE_THEOREMS, AXIOM_METADATA, HYPOTHESIS_REGISTRY,
        MODULE_CHAIN_MAP, CHAIN_MILESTONES,
    )

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
        # Name deps (Phase 5v Wave 9c): direct refs in this decl's body.
        # Kept as full names — the edge extractor resolves them against the
        # node-id index. Empty list when ExtractDeps hasn't been re-run yet
        # with the name_deps_project field.
        name_deps_project_full = decl.get('name_deps_project', [])

        # Chain taxonomy (Phase 5v Wave 9d): derive chain_id from the
        # module's MODULE_CHAIN_MAP entry. Modules not listed get a None
        # chain_id — the dashboard surfaces these in an "unclassified"
        # bucket so we can spot missing taxonomy entries.
        chain_raw = MODULE_CHAIN_MAP.get(module_name)
        if chain_raw is None:
            chain_ids: list[str] = []
        elif isinstance(chain_raw, list):
            chain_ids = list(chain_raw)
        else:
            chain_ids = [chain_raw]

        # Milestone marker: a declaration is a milestone if its short name
        # is registered in CHAIN_MILESTONES or if it's an Axiom (every
        # axiom is always a milestone — trust-boundary clarity).
        is_milestone = short_name in CHAIN_MILESTONES or kind == 'axiom'
        milestone_order = CHAIN_MILESTONES.get(short_name)

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
                'name_deps_project': name_deps_project_full,
                'eliminability': eliminability,
                'eliminability_reason': eliminability_reason,
                'field_constraints': decl.get('structure_fields', []),
                'type_signature': decl.get('type', ''),
                'chain_ids': chain_ids,
                'is_milestone': is_milestone,
                'milestone_order': milestone_order,
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


def _parse_tex_title(tex_path: Path) -> str | None:
    """Pull \\title{...} from a .tex file. Returns None if not found."""
    try:
        text = tex_path.read_text()
    except (OSError, UnicodeDecodeError):
        return None
    # Non-greedy match; allow balanced-ish braces inside
    m = re.search(r'\\title\{([^}]*(?:\\\\[^}]*)*)\}', text)
    if not m:
        return None
    title = m.group(1).replace(r'\\', ' ').strip()
    return title[:200] if title else None


def extract_paper_nodes() -> list[dict]:
    """Extract paper nodes. Auto-discovers every papers/paper*_*/paper_draft.tex
    on the filesystem; enriches with PAPER_DEPENDENCIES metadata when available.

    Previously this extractor was gated on PAPER_DEPENDENCIES, so only 9 of 15
    papers appeared in the graph. Phase 5v Wave 1c switches to filesystem
    discovery so every paper on disk is graph-visible; papers without
    provenance entries get a minimal node with title parsed from \\title{}.
    """
    from src.core.provenance import PAPER_DEPENDENCIES

    papers_dir = PROJECT_ROOT / "papers"
    # Skip registry pseudo-entries that don't correspond to a paper directory
    _NON_PAPER_KEYS = {'experimental_predictions'}

    nodes = []
    seen_keys: set[str] = set()

    # Start from filesystem (ground truth)
    if papers_dir.exists():
        for tex_path in sorted(papers_dir.glob("paper*_*/paper_draft.tex")):
            key = tex_path.parent.name  # e.g. "paper1_first_order"
            entry = PAPER_DEPENDENCIES.get(key, {})
            title = (
                entry.get('title')
                or _parse_tex_title(tex_path)
                or key.replace('_', ' ').title()
            )
            nodes.append({
                'id': f'paper:{key}',
                'type': 'Paper',
                'label': key,
                'name': title,
                'verification': 'verified' if entry else 'unverified',
                'detail': entry.get('topic', '')
                          or f"Filesystem-discovered; no PAPER_DEPENDENCIES entry",
                'meta': {
                    'topic': entry.get('topic', ''),
                    'formulas': entry.get('formulas', []),
                    'lean_modules': entry.get('lean_modules', []),
                    'platforms': entry.get('platforms', []),
                    'n_claims': len(entry.get('key_claims', [])),
                    'tex_path': str(tex_path.relative_to(PROJECT_ROOT)),
                    'has_provenance_entry': bool(entry),
                },
            })
            seen_keys.add(key)

    # Include any PAPER_DEPENDENCIES entries that don't map to a paper
    # directory (e.g. cross-cutting predictions); skip known pseudo-entries
    for key, entry in PAPER_DEPENDENCIES.items():
        if key in seen_keys or key in _NON_PAPER_KEYS:
            continue
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
                'tex_path': None,
                'has_provenance_entry': True,
            },
        })

    logger.info("Paper extraction: %d nodes (of which %d fs-discovered)",
                len(nodes), len(seen_keys))
    return nodes


# Claim-verb triggers for auto-extracting claim sentences from paper .tex
# when no declared key_claims list exists. Targets the same sentence shape
# as the kind of thing a human would put in a bulleted "Results" list:
# "we prove X", "we show Y", "we formalize Z", "first proof of W", etc.
_CLAIM_VERB_RE = re.compile(
    r'\b(we\s+(prove|show|demonstrate|formaliz[es]|verif[yi]|derive|'
    r'construct|establish|give|present|compute|confirm|obtain|extend|'
    r'find|observe|report)|'
    r'(formally\s+verified?|machine[- ]checked|'
    r'(the\s+)?first\s+(formally\s+verified|in\s+any\s+proof\s+assistant|'
    r'complete|computed|explicit)))\b',
    re.IGNORECASE,
)


def _auto_extract_paper_claims(tex: str, limit: int = 12) -> list[str]:
    """Heuristic claim extraction from paper .tex for papers without a
    declared key_claims list. Scans:

      1. Each \\item line in the first bulleted list (usually appears in
         abstract or intro and lists paper contributions)
      2. Each sentence in the abstract that carries a claim-verb marker

    Deduplicates, caps at `limit` items. Used by `extract_paper_claim_nodes`
    when PAPER_DEPENDENCIES.<paper>.key_claims is missing or empty.
    """
    claims: list[str] = []
    seen: set[str] = set()

    # Pass 1: bulleted items. Match the first `\begin{itemize}...\end{itemize}`
    # or `\begin{enumerate}...\end{enumerate}` that appears anywhere.
    list_match = re.search(
        r'\\begin\{(itemize|enumerate)\}(.*?)\\end\{\1\}',
        tex, flags=re.DOTALL,
    )
    if list_match:
        for item_match in re.finditer(r'\\item\s+(.+?)(?=\\item|$)',
                                      list_match.group(2), flags=re.DOTALL):
            text = item_match.group(1).strip()
            # Strip LaTeX formatting for the claim text
            text = re.sub(r'\\cite\{[^}]*\}', '', text)
            text = re.sub(r'\\emph\{([^}]*)\}', r'\1', text)
            text = re.sub(r'\\texttt\{([^}]*)\}', r'\1', text)
            text = re.sub(r'\\text[a-z]*\{([^}]*)\}', r'\1', text)
            text = re.sub(r'\\[a-zA-Z]+\*?', ' ', text)
            text = re.sub(r'[{}]', '', text)
            text = re.sub(r'\s+', ' ', text).strip()
            if len(text) >= 10 and text not in seen:
                seen.add(text)
                claims.append(text)
                if len(claims) >= limit:
                    return claims

    # Pass 2: abstract sentences carrying a claim-verb marker.
    abstract_match = re.search(
        r'\\begin\{abstract\}(.*?)\\end\{abstract\}',
        tex, flags=re.DOTALL,
    )
    if abstract_match:
        abs_text = abstract_match.group(1)
        abs_text = re.sub(r'\\cite\{[^}]*\}', '', abs_text)
        abs_text = re.sub(r'\\emph\{([^}]*)\}', r'\1', abs_text)
        abs_text = re.sub(r'\\texttt\{([^}]*)\}', r'\1', abs_text)
        abs_text = re.sub(r'\\text[a-z]*\{([^}]*)\}', r'\1', abs_text)
        abs_text = re.sub(r'\\[a-zA-Z]+\*?', ' ', abs_text)
        abs_text = re.sub(r'[{}]', '', abs_text)
        abs_text = re.sub(r'\s+', ' ', abs_text).strip()
        # Split on sentence boundaries, respecting e.g./i.e.
        sentences = re.split(
            r'(?<!\be\.g)(?<!\bi\.e)(?<!\bvs)(?<=[.!?])\s+(?=[A-Z])',
            abs_text,
        )
        for sent in sentences:
            sent = sent.strip(' .')
            if len(sent) < 30 or sent in seen:
                continue
            if _CLAIM_VERB_RE.search(sent):
                seen.add(sent)
                claims.append(sent)
                if len(claims) >= limit:
                    break

    return claims


def extract_paper_claim_nodes() -> list[dict]:
    """Extract PaperClaim nodes from every paper on disk.

    Phase 5v Wave 1c+ refinement. Previously gated on
    PAPER_DEPENDENCIES.<paper>.key_claims, so 6 of 15 papers produced
    zero claim nodes (papers 8, 9, 10, 11, 14, 15, 16). Now iterates all
    paper directories:

      - If PAPER_DEPENDENCIES has a declared `key_claims` list, use it
        (curated claims are authoritative).
      - Otherwise auto-extract from the paper's .tex via
        `_auto_extract_paper_claims`, flagging the source as 'tex-auto'
        so the dashboard can surface the distinction.
    """
    from src.core.provenance import PAPER_DEPENDENCIES

    papers_dir = PROJECT_ROOT / "papers"
    nodes = []
    auto_count = 0
    declared_count = 0

    if not papers_dir.exists():
        # Fallback to pre-widening behavior
        for paper_key, entry in PAPER_DEPENDENCIES.items():
            for idx, claim_text in enumerate(entry.get('key_claims', [])):
                nodes.append({
                    'id': f'claim:{paper_key}:{idx}',
                    'type': 'PaperClaim',
                    'label': claim_text[:60] + ('...' if len(claim_text) > 60 else ''),
                    'name': claim_text,
                    'verification': 'verified',
                    'detail': claim_text,
                    'meta': {'paper': paper_key, 'index': idx,
                             'full_text': claim_text, 'source': 'declared'},
                })
        return nodes

    for tex_path in sorted(papers_dir.glob("paper*_*/paper_draft.tex")):
        paper_key = tex_path.parent.name
        entry = PAPER_DEPENDENCIES.get(paper_key, {})
        declared = entry.get('key_claims', [])
        if declared:
            claims = declared
            source = 'declared'
            declared_count += len(claims)
        else:
            try:
                tex = tex_path.read_text()
            except (OSError, UnicodeDecodeError):
                continue
            claims = _auto_extract_paper_claims(tex)
            source = 'tex-auto'
            auto_count += len(claims)

        for idx, claim_text in enumerate(claims):
            nodes.append({
                'id': f'claim:{paper_key}:{idx}',
                'type': 'PaperClaim',
                'label': claim_text[:60] + ('...' if len(claim_text) > 60 else ''),
                'name': claim_text,
                'verification': 'verified' if source == 'declared' else 'unverified',
                'detail': claim_text,
                'meta': {
                    'paper': paper_key,
                    'index': idx,
                    'full_text': claim_text,
                    'source': source,
                },
            })

    logger.info("PaperClaim extraction: %d nodes (%d declared + %d tex-auto)",
                len(nodes), declared_count, auto_count)
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
    seen_ids: set[str] = set()
    registered_functions: set[str] = set()
    for fig_spec in mod.FIGURE_REGISTRY:
        fig_id = f'figure:{fig_spec.name}'
        seen_ids.add(fig_id)
        if fig_spec.function:
            registered_functions.add(fig_spec.function)
        nodes.append({
            'id': fig_id,
            'type': 'Figure',
            'label': fig_spec.name,
            'name': fig_spec.name,
            'verification': 'verified',
            'detail': fig_spec.caption,
            'meta': {
                'function': fig_spec.function,
                'caption': fig_spec.caption,
                'expected_traces': fig_spec.expected_traces,
                'registered': True,
            },
        })

    # Auto-discover fig_* functions in visualizations.py that are NOT already
    # registered (via either name or function field). Previously some figures
    # lived only as functions without review registry entries; this surfaces
    # them with minimal metadata so they appear in the graph.
    # Phase 5v Wave 1c.
    viz_path = PROJECT_ROOT / "src" / "core" / "visualizations.py"
    if viz_path.exists():
        fn_re = re.compile(r'^def\s+(fig_[A-Za-z0-9_]+)\s*\(', re.MULTILINE)
        source = viz_path.read_text()
        extras = 0
        for m in fn_re.finditer(source):
            fn_name = m.group(1)
            # Skip functions already covered by FIGURE_REGISTRY under either
            # their numbered `name` or their `function` field (73 of 76
            # registered figures map to a fig_* function in viz.py).
            if fn_name in registered_functions:
                continue
            fig_id = f'figure:{fn_name}'
            if fig_id in seen_ids:
                continue
            seen_ids.add(fig_id)
            nodes.append({
                'id': fig_id,
                'type': 'Figure',
                'label': fn_name,
                'name': fn_name,
                'verification': 'unverified',
                'detail': 'fs-discovered; not in FIGURE_REGISTRY',
                'meta': {
                    'function': fn_name,
                    'caption': '',
                    'expected_traces': [],
                    'registered': False,
                },
            })
            extras += 1
        logger.info("Figure extraction: %d registered + %d fs-discovered = %d total",
                    len(nodes) - extras, extras, len(nodes))

    return nodes


# ═══════════════════════════════════════════════════════════════════════
# Phase 5v Wave 2a — Readiness system node-type stubs
# ═══════════════════════════════════════════════════════════════════════
# These extractors are registered so downstream aggregators + integrity
# checks see the new node types as first-class, but return empty lists
# until their wiring waves (2b–2g). Each has a module-stable docstring
# describing the contract so wiring can be done independently.


_ABSTRACT_BLOCK_RE = re.compile(
    r'\\begin\{abstract\}(.*?)\\end\{abstract\}',
    re.DOTALL,
)


def _split_sentences(text: str) -> list[str]:
    """Dumb sentence splitter for LaTeX prose. Strips common LaTeX
    commands and splits on periods that aren't part of common
    abbreviations/numbers."""
    t = re.sub(r'\\cite\{[^}]*\}', '', text)
    t = re.sub(r'\\ref\{[^}]*\}', '', t)
    t = re.sub(r'\\label\{[^}]*\}', '', t)
    t = re.sub(r'\\emph\{([^}]*)\}', r'\1', t)
    t = re.sub(r'\\text[a-z]*\{([^}]*)\}', r'\1', t)
    t = re.sub(r'\\[a-zA-Z]+', ' ', t)  # strip remaining commands
    t = re.sub(r'\s+', ' ', t).strip()
    # Period-split respecting abbreviations
    parts = re.split(r'(?<!\be\.g)(?<!\bi\.e)(?<!\bvs)(?<=[.!?])\s+(?=[A-Z])', t)
    return [p.strip(' .') for p in parts if len(p.strip()) > 20]


# Heuristic "interesting claim" triggers — sentences matching any of these
# patterns are flagged as 'interesting: true' in the node meta so the
# NarrativeGrounding readiness gate can prioritize them.
_INTERESTING_PATTERNS = [
    (re.compile(r'\bfirst\b.*\b(proof\s+assistant|formali[sz]ed|verified|computed)\b', re.IGNORECASE), 'first-claim'),
    (re.compile(r'\ball\s+the\s+same\b|\bconverge\b.*\b16\b|\brooted\s+in\b', re.IGNORECASE), 'unification-claim'),
    (re.compile(r'\b(Dedekind|Ramanujan|eta\s+function)\b', re.IGNORECASE), 'attribution-claim'),
    (re.compile(r'\b(programmable|tunable|within\s+reach|feasible)\b', re.IGNORECASE), 'feasibility-claim'),
    (re.compile(r'\b(Monte\s+Carlo\s+evidence|evidence\s+from\s+simulation)\b', re.IGNORECASE), 'simulation-evidence-claim'),
]


def extract_prose_claim_nodes() -> list[dict]:
    """ProseClaim — narrative statements not tied to a Formula.

    Phase 5v Wave 2f (minimal scope). Extracts one ProseClaim per sentence
    of each paper's `\\begin{abstract}...\\end{abstract}` block. The
    abstract is the highest-density region for narrative overclaims —
    "all the same 16", "Ramanujan", "first in any proof assistant", etc.
    all lived there.

    Sentences that match heuristic "interesting-claim" patterns (first-claim,
    unification-claim, attribution-claim, etc.) are tagged in meta for the
    Wave 4 NarrativeGrounding readiness gate to prioritize.

    Broader paper prose (intro, conclusions, body sections) is deferred —
    Stage 13 adversarial review (Wave 6) will catch overclaims in those
    regions without needing a precomputed ProseClaim node per sentence.
    """
    papers_dir = PROJECT_ROOT / "papers"
    if not papers_dir.exists():
        return []

    nodes = []
    seen_ids: set[str] = set()

    for tex_path in sorted(papers_dir.glob("paper*_*/paper_draft.tex")):
        paper_key = tex_path.parent.name
        try:
            text = tex_path.read_text()
        except (OSError, UnicodeDecodeError):
            continue
        abstract_match = _ABSTRACT_BLOCK_RE.search(text)
        if not abstract_match:
            continue
        abstract = abstract_match.group(1).strip()
        sentences = _split_sentences(abstract)

        for idx, sent in enumerate(sentences):
            # Classify against interesting patterns
            tags = []
            for pat, tag in _INTERESTING_PATTERNS:
                if pat.search(sent):
                    tags.append(tag)
            interesting = bool(tags)

            node_id = f'proseclaim:{paper_key}:{idx}'
            if node_id in seen_ids:
                continue
            seen_ids.add(node_id)

            nodes.append({
                'id': node_id,
                'type': 'ProseClaim',
                'label': sent[:70] + ('…' if len(sent) > 70 else ''),
                'name': sent[:250],
                'verification': 'unverified',
                'detail': sent[:400],
                'meta': {
                    'paper': paper_key,
                    'region': 'abstract',
                    'sentence_index': idx,
                    'interesting': interesting,
                    'tags': tags,
                    'full_text': sent,
                },
            })

    if nodes:
        flagged = sum(1 for n in nodes if n['meta']['interesting'])
        logger.info("ProseClaim extraction: %d abstract sentences (%d flagged as interesting)",
                    len(nodes), flagged)
    return nodes


import ast as _ast


def _extract_imports(tree: _ast.AST) -> set[str]:
    """Return the set of top-level names imported at module scope.

    Picks up `from X import a, b` and `import X [as y]`. Used to filter
    referenced-name extraction in PythonTest nodes so bare Python locals
    (e.g. `cs`, `n`, `d` — common one-letter parameters) don't flood the
    VERIFIES-edge resolver with spurious short-name collisions.
    """
    names: set[str] = set()
    for node in _ast.walk(tree):
        if isinstance(node, _ast.ImportFrom):
            for alias in node.names:
                names.add(alias.asname or alias.name)
        elif isinstance(node, _ast.Import):
            for alias in node.names:
                names.add((alias.asname or alias.name).split('.')[0])
    return names


def _classify_assertion(node: _ast.AST) -> str | None:
    """Classify a single assertion AST node by its test_kind.

    Returns one of {golden, bounds, identity, roundtrip, unknown}, or None
    if the node is not an assertion.
    """
    # Assert statements
    if isinstance(node, _ast.Assert):
        test = node.test
        # pytest.approx / math.isclose / np.allclose / np.isclose: golden comparison
        if isinstance(test, _ast.Compare):
            # Walk the comparators to find allclose/isclose/approx calls
            for sub in _ast.walk(test):
                if isinstance(sub, _ast.Call):
                    fn = _ast.unparse(sub.func) if hasattr(_ast, 'unparse') else ''
                    if any(tag in fn for tag in ('allclose', 'isclose', 'approx')):
                        return 'golden'
            # Pure equality between two names: identity
            ops = test.ops
            if len(ops) == 1 and isinstance(ops[0], _ast.Eq):
                return 'identity'
            # Inequalities: bounds check (< <= > >=)
            if all(isinstance(op, (_ast.Lt, _ast.LtE, _ast.Gt, _ast.GtE))
                   for op in ops):
                return 'bounds'
        # Function calls directly as assertion body
        if isinstance(test, _ast.Call):
            fn = _ast.unparse(test.func) if hasattr(_ast, 'unparse') else ''
            if 'allclose' in fn or 'isclose' in fn or 'approx' in fn:
                return 'golden'
        return 'unknown'
    # Method calls: self.assertAlmostEqual, self.assertEqual, etc.
    if isinstance(node, _ast.Expr) and isinstance(node.value, _ast.Call):
        fn = _ast.unparse(node.value.func) if hasattr(_ast, 'unparse') else ''
        if 'assertAlmostEqual' in fn or 'assert_allclose' in fn:
            return 'golden'
        if 'assertEqual' in fn or 'assertIs' in fn:
            return 'identity'
        if 'assertGreater' in fn or 'assertLess' in fn:
            return 'bounds'
    return None


def _classify_test_function(fn: _ast.FunctionDef,
                            imports: set[str]) -> tuple[str, list[str]]:
    """Classify a test function by walking its assertions.

    Priority: golden > identity > roundtrip > bounds > unknown.
    Returns (test_kind, list_of_referenced_names).

    `imports` is the set of names imported at module scope; only these
    names (or attribute chains rooted at these names) are recorded as
    referenced, to avoid false-positive short-name collisions against
    Lean structure-field projections.
    """
    kinds = []
    names: set[str] = set()
    for stmt in _ast.walk(fn):
        kind = _classify_assertion(stmt)
        if kind:
            kinds.append(kind)
        if isinstance(stmt, _ast.Name):
            if stmt.id in imports:
                names.add(stmt.id)
        elif isinstance(stmt, _ast.Attribute):
            # Capture attribute chains rooted at an imported name
            root = stmt
            while isinstance(root, _ast.Attribute):
                root = root.value
            if isinstance(root, _ast.Name) and root.id in imports:
                if hasattr(_ast, 'unparse'):
                    names.add(_ast.unparse(stmt))
    lname = fn.name.lower()
    if any(tag in lname for tag in ('roundtrip', 'inverse', 'forward_backward')):
        kinds.append('roundtrip')
    for preferred in ('roundtrip', 'golden', 'identity', 'bounds', 'unknown'):
        if preferred in kinds:
            return preferred, sorted(names)
    return 'unknown', sorted(names)


def extract_python_test_nodes() -> list[dict]:
    """PythonTest — test functions with test_kind classification.

    Phase 5v Wave 2c. AST-parses every tests/test_*.py file; emits one
    PythonTest node per `def test_*` function. test_kind classification
    priority: roundtrip > golden > identity > bounds > unknown. Bounds-only
    tests are the failure mode that let the k_H² bug through — the
    ComputationCorrectness ReadinessGate (Wave 4) fails any Formula whose
    VERIFIES edges are exclusively `test_kind=bounds`.

    VERIFIES edges (Formula / Parameter / LeanTheorem targets) are
    populated from names referenced in each test function; link-resolution
    uses the existing Formula/Parameter/LeanTheorem node IDs.
    """
    tests_dir = PROJECT_ROOT / "tests"
    if not tests_dir.exists():
        return []

    nodes = []
    seen_ids: set[str] = set()
    for test_file in sorted(tests_dir.glob("test_*.py")):
        try:
            source = test_file.read_text()
            tree = _ast.parse(source, filename=str(test_file))
        except (OSError, UnicodeDecodeError, SyntaxError) as exc:
            logger.debug("PythonTest: skipping %s (%s)", test_file.name, exc)
            continue
        module = test_file.stem  # e.g. "test_formulas"
        imports = _extract_imports(tree)
        for node in _ast.walk(tree):
            if isinstance(node, _ast.FunctionDef) and node.name.startswith('test_'):
                test_kind, refs = _classify_test_function(node, imports)
                test_id = f'test:{module}::{node.name}'
                if test_id in seen_ids:
                    continue
                seen_ids.add(test_id)
                nodes.append({
                    'id': test_id,
                    'type': 'PythonTest',
                    'label': node.name,
                    'name': node.name,
                    'verification': 'verified',
                    'detail': f'{module}.py:{node.lineno} — test_kind={test_kind}',
                    'meta': {
                        'module': module,
                        'file': f'tests/{module}.py',
                        'line': node.lineno,
                        'test_kind': test_kind,
                        'referenced_names': refs[:50],  # cap for readability
                    },
                })

    if nodes:
        from collections import Counter as _C
        kind_counts = _C(n['meta']['test_kind'] for n in nodes)
        logger.info("PythonTest extraction: %d tests across %d files (%s)",
                    len(nodes),
                    len(list(tests_dir.glob("test_*.py"))),
                    ", ".join(f"{k}={v}" for k, v in kind_counts.most_common()))
    return nodes


# Severity marker glyphs used in review docs (including Master Checklist)
_SEV_GLYPHS = {
    '🔴': 'critical',
    '🟡': 'major',
    '🔵': 'minor',
}

# Section heading pattern for Master Checklist / Comprehensive / Citation
# review formats:
#   `### N.N — Paper X — ...`        (Master Checklist)
#   `### N — Paper Y — ...`          (Citation Reviews)
#   `### Class N — ...`              (Citation Verification format, 2026-04-26+)
# also allow plain `### N.N Heading` without em-dashes.
_REVIEW_SECTION_RE = re.compile(
    r'^###\s+(?:Class\s+)?(\d+(?:\.\d+)?)\s*[—\-–]\s*(.+?)$',
    re.MULTILINE,
)
# When the heading uses "Class N" form, prepend "C" to the section number so
# IDs like `review:2026-04-26-...:C2` don't collide with `review:...:2` from
# numeric-N format reports. Detected at extraction time (see header source).
_CLASS_HEADING_RE = re.compile(r'^###\s+Class\s+\d', re.MULTILINE)

# Detect "BLOCKER" / "severity: critical" / "FAIL" markers as severity escalators
_BLOCKER_RE = re.compile(
    r'\*\*?BLOCKER\*\*?|severity:\s*critical|severity:\s*BLOCKER',
    re.IGNORECASE,
)


def _infer_paper_key_from_text(text: str) -> str | None:
    """Best-effort extraction of a paper key (paper1_first_order, etc.)
    from the body text of a finding. Returns None if none found.

    The 2026-05-14 update added optional `\\s+` between "paper" and the
    digit so review-doc headings like "Paper 10 Deep Review — ..." (with
    a literal space) attribute correctly to `paper10`. Previously the
    regex required no space, dropping all "Paper N" review-doc findings
    into the orphan bucket (~5% of the 832-finding corpus, enough to
    drop the test_no_orphaned_findings attach-rate below the 25% floor).
    """
    m = re.search(r'`?paper\s*(\d{1,2}[_A-Za-z0-9]*)`?', text, re.IGNORECASE)
    if m:
        return f'paper{m.group(1).lower()}'
    return None


def _load_supersession_ledger() -> dict[str, dict]:
    """Load `docs/review_finding_supersessions.json` and return a dict
    mapping `finding_id` → entry. Phase 6i Wave 2: lets Wave-N close
    docs flip prior-review findings to `status: fixed` without editing
    the original review .md (which is treated as immutable history).
    Closes the qi-fixpropagation-tracking QI candidate.
    """
    path = PROJECT_ROOT / "docs" / "review_finding_supersessions.json"
    if not path.exists():
        return {}
    try:
        import json as _json
        data = _json.loads(path.read_text(encoding="utf-8"))
    except (OSError, _json.JSONDecodeError) as exc:
        logger.warning("review_finding_supersessions.json unreadable: %s", exc)
        return {}
    out: dict[str, dict] = {}
    for entry in data.get("supersessions", []):
        fid = entry.get("finding_id")
        if fid:
            out[fid] = entry
    return out


def extract_review_finding_nodes() -> list[dict]:
    """ReviewFinding — findings from adversarial reviews.

    Phase 5v Wave 2d. Scans `papers/AutomatedReviews/<date>/*.md` for
    structured findings (numbered `### N.N — ...` headings) with severity
    glyphs (🔴/🟡/🔵). Emits one ReviewFinding node per finding. Status
    defaults to 'open' unless the finding text contains ✅/✓ markers.
    The Master Checklist is the canonical source here; other reviews are
    also scanned.

    Node meta carries: severity, status, review_file, review_date,
    section_index, inferred_paper (if any). FLAGS edges to target
    artifacts (Paper/Formula/LeanTheorem) are emitted in
    extract_flags_edges.

    Phase 6i Wave 2 addition: if `docs/review_finding_supersessions.json`
    contains an entry for a given finding_id, the entry's `status` field
    overrides the parser-inferred status, and `superseded_by`/`evidence`
    are added to the node's meta. This is the project-level analogue of
    the SUPERSEDES edge type — it lets later waves flip prior findings
    to `fixed` without rewriting the original review .md.
    """
    reviews_dir = PROJECT_ROOT / "papers" / "AutomatedReviews"
    if not reviews_dir.exists():
        return []
    supersessions = _load_supersession_ledger()

    nodes = []
    seen_ids: set[str] = set()
    for md_path in sorted(reviews_dir.glob("*/*.md")):
        date_dir = md_path.parent.name        # e.g. "2026-04-12"
        review_name = md_path.stem            # e.g. "CitationReview-01"
        try:
            source = md_path.read_text()
        except (OSError, UnicodeDecodeError):
            continue
        # File-level severity escalation: BLOCKER / severity: critical markers
        # often live in summary tables OR QI Candidate sections (heading level
        # 2: `## QI Candidate`) outside any `### Class N` finding body. If any
        # such marker exists in the whole file, the report is critical-class
        # and findings inherit that severity unless they declare lower locally.
        file_has_critical_marker = bool(_BLOCKER_RE.search(source))

        # Split source into sections by `### N.N` or `### Class N` headings.
        # When the heading uses "Class N" form, prefix the section number with
        # "C" so IDs don't collide across formats.
        matches = list(_REVIEW_SECTION_RE.finditer(source))
        for idx, m in enumerate(matches):
            section_num = m.group(1)
            heading = m.group(2).strip()
            start = m.end()
            end = matches[idx + 1].start() if idx + 1 < len(matches) else len(source)
            body = source[start:end].strip()

            # If the matched heading was "### Class N — ...", tag the section
            # number with a 'C' prefix to avoid ID collisions.
            heading_line = source[m.start():m.end()]
            if _CLASS_HEADING_RE.match(heading_line):
                section_num = f'C{section_num}'

            # Severity from glyphs OR explicit BLOCKER / severity: critical markers
            severity = 'advisory'
            for glyph, sev in _SEV_GLYPHS.items():
                if glyph in heading or glyph in body[:600]:
                    severity = sev
                    break
            # Escalation: explicit BLOCKER / critical markers override glyph-derived severity
            if _BLOCKER_RE.search(heading) or _BLOCKER_RE.search(body[:1000]):
                severity = 'critical'
            # File-level escalation: if any critical marker exists in the report
            # (e.g. summary table, QI Candidate section), all findings inherit
            # critical severity unless they explicitly downgrade in body.
            elif file_has_critical_marker:
                severity = 'critical'

            # Status: fixed if ✅ or "fixed" / "done" / "now closed" markers present
            status = 'open'
            if re.search(r'[✅✓]|\bfixed\b|\bresolved\b|\bdone\b|now\s+closed', heading, re.IGNORECASE):
                status = 'fixed'
            if re.search(r'(now\s+closed|✅\s*\(?(?:now\s+)?closed)', body[:600], re.IGNORECASE):
                status = 'fixed'
            if re.search(r'[❌✗]\s+still', body[:400], re.IGNORECASE):
                status = 'open'

            # Inference text: section heading + body slice + review_name (the
            # filename-derived review identifier). Including review_name lets
            # files like "Paper 10 Deep Review — Modular Generation Constraint.md"
            # attribute every section's findings to paper10 even when the section
            # heading itself doesn't repeat "Paper 10". (2026-05-14: this was
            # the dominant orphan-cause for the Master Checklist + Deep Review
            # corpus; review_name inclusion lifted attach-rate from ~24% to ~30%+.)
            inferred_paper = _infer_paper_key_from_text(
                heading + " " + body[:400] + " " + review_name
            )

            finding_id = f'review:{date_dir}:{review_name}:{section_num}'
            if finding_id in seen_ids:
                continue
            seen_ids.add(finding_id)

            meta = {
                'severity': severity,
                'status': status,
                'review_file': str(md_path.relative_to(PROJECT_ROOT)),
                'review_date': date_dir,
                'review_name': review_name,
                'section': section_num,
                'inferred_paper': inferred_paper,
            }
            ledger = supersessions.get(finding_id)
            if ledger:
                meta['status'] = ledger.get('status', status)
                meta['superseded_by'] = ledger.get('superseded_by')
                meta['supersession_evidence'] = ledger.get('evidence')
                meta['supersession_date'] = ledger.get('date')

            nodes.append({
                'id': finding_id,
                'type': 'ReviewFinding',
                'label': f'{section_num} {heading[:50]}',
                'name': heading[:200],
                'verification': 'verified',
                'detail': body[:400].replace("\n", " "),
                'meta': meta,
            })

    if nodes:
        from collections import Counter as _C
        sev = _C(n['meta']['severity'] for n in nodes)
        st = _C(n['meta']['status'] for n in nodes)
        logger.info("ReviewFinding extraction: %d findings across %d review docs (severity: %s; status: %s)",
                    len(nodes),
                    len(list(reviews_dir.glob("*/*.md"))),
                    dict(sev), dict(st))
    return nodes


def _classify_log_tail(log_tail: str) -> tuple[str, str]:
    """Return (status, reason) from the last ~2KB of a run log.

    Status set: success, crashed, out_of_budget, sign_problem, terminated,
    unknown. Reason is a short human-readable tag.
    """
    t = log_tail.lower()
    if 'brokenpipeerror' in t or 'traceback' in t:
        return 'crashed', 'exception in log'
    if 'sigterm' in t or 'signal 15' in t or 'terminated' in t:
        return 'terminated', 'SIGTERM / cleanup'
    if 'out_of_budget' in t or 'out of budget' in t:
        return 'out_of_budget', 'budget exhausted'
    if '<sign>' in t and '=0' in t:
        return 'sign_problem', 'zero sign average'
    if 'complete' in t or 'successfully' in t or 'finished' in t:
        return 'success', 'log shows completion'
    return 'unknown', 'no terminal marker'


def extract_production_run_nodes() -> list[dict]:
    """ProductionRun — MC/RHMC/other production runs with status.

    Phase 5v Wave 2e. Scans data/**/summary.json and data/**/*.json files
    that carry a run-like schema (timestamps, algorithm fields). For each,
    emit a ProductionRun node with status derived from the paired .log
    (when present) or from JSON content flags. This surfaces Paper 6's
    Monte Carlo failure mode (zero-output runs that were claimed as
    evidence in prose) as graph state the ReadinessGate system can check.

    Status classifications: success, crashed, out_of_budget, sign_problem,
    terminated, unknown.
    """
    data_dir = PROJECT_ROOT / "data"
    if not data_dir.exists():
        return []

    nodes = []
    seen_ids: set[str] = set()

    for json_path in sorted(data_dir.rglob("*.json")):
        # Skip obvious non-run JSON files (small config/schema files)
        try:
            stat = json_path.stat()
        except OSError:
            continue
        if stat.st_size < 32:
            continue
        try:
            import json as _json
            with open(json_path) as f:
                payload = _json.load(f)
        except (OSError, _json.JSONDecodeError, UnicodeDecodeError):
            continue
        # Heuristic: must have a timestamp-ish identifier or an
        # algorithm-name field to count as a run record
        is_run = any(
            k in payload
            for k in ('algorithm', 'timestamp', 'run_id', 'hmc_steps',
                     'binder_crossing', 'n_traj', 'seed')
        )
        if not is_run:
            continue

        # Derive a run ID from path or payload
        stem = json_path.stem
        kind = 'rhmc' if 'rhmc' in stem.lower() else \
               'vestigial_mc' if 'vestigial' in stem.lower() else \
               'mc'
        node_id = f'run:{kind}:{stem}'
        if node_id in seen_ids:
            continue
        seen_ids.add(node_id)

        # Read paired log for status
        log_path = json_path.with_suffix('.log')
        log_tail = ''
        if log_path.exists():
            try:
                with open(log_path) as f:
                    f.seek(max(0, log_path.stat().st_size - 2048))
                    log_tail = f.read()
            except OSError:
                pass
        status, reason = _classify_log_tail(log_tail) if log_tail else ('unknown', 'no paired .log')

        # Sign average from payload if present
        sign_avg = payload.get('sign_average')
        if sign_avg is not None and abs(float(sign_avg)) < 1e-6:
            status = 'sign_problem'
            reason = f'<sign>={sign_avg}'

        nodes.append({
            'id': node_id,
            'type': 'ProductionRun',
            'label': stem[:60],
            'name': stem,
            'verification': 'verified' if status == 'success' else 'unverified',
            'detail': f'{kind} run — status={status} ({reason})',
            'meta': {
                'kind': kind,
                'status': status,
                'reason': reason,
                'data_path': str(json_path.relative_to(PROJECT_ROOT)),
                'log_path': str(log_path.relative_to(PROJECT_ROOT)) if log_path.exists() else None,
                'algorithm': payload.get('algorithm'),
                'timestamp': payload.get('timestamp'),
                'size_bytes': stat.st_size,
            },
        })

    if nodes:
        from collections import Counter as _C
        st = _C(n['meta']['status'] for n in nodes)
        logger.info("ProductionRun extraction: %d runs (status: %s)",
                    len(nodes), dict(st))
    return nodes


# Body patterns that indicate placeholder content. `decide` and
# `native_decide` are deliberately excluded — these are legitimate
# finite-verification techniques used extensively in Phase 5e MTC work
# (IsingBraiding, SU3kFusion, etc.).
_PLACEHOLDER_BODY_PATTERNS = [
    (re.compile(r'^by\s+rfl\s*$'), 'by rfl'),
    (re.compile(r'^rfl\s*$'), 'rfl (term)'),
    (re.compile(r'^by\s+trivial\s*$'), 'by trivial'),
    (re.compile(r'^trivial\s*$'), 'trivial (term)'),
    (re.compile(r'Equiv\.refl'), 'Equiv.refl'),
    (re.compile(r'^by\s+exact\s+rfl\s*$'), 'by exact rfl'),
]


def _scan_lean_theorem_bodies(source: str):
    """Yield (name, line, body_text) for each `theorem NAME ... := BODY` in
    a Lean source file. Handles multi-line declarations with parenthesized
    binders that contain `:`. Body is everything after `:=` up to a blank
    line or the next top-level declaration keyword.
    """
    lines = source.split("\n")
    i = 0
    top_kw_re = re.compile(r'^(theorem|lemma|def|noncomputable\s+def|'
                           r'abbrev|instance|example|axiom|structure|class|'
                           r'inductive|/--|/-|-- |namespace|end|open|import|'
                           r'section|variable|variables|attribute|@\[)\b')
    while i < len(lines):
        line = lines[i]
        m = re.match(r'^theorem\s+([A-Za-z_][A-Za-z0-9_\']*)', line)
        if not m:
            i += 1
            continue
        name = m.group(1)
        line_no = i + 1
        # Accumulate the full declaration until we see `:=`
        decl_lines = []
        assign_offset_in_acc = None
        j = i
        while j < len(lines):
            decl_lines.append(lines[j])
            acc = "\n".join(decl_lines)
            # Find a `:=` that is not inside a string/comment (pragmatic:
            # we treat any `:=` as the assignment)
            idx = acc.find(':=', len("\n".join(decl_lines[:-1])) if len(decl_lines) > 1 else 0)
            if idx >= 0:
                assign_offset_in_acc = idx
                break
            j += 1
        if assign_offset_in_acc is None:
            i = j + 1
            continue
        # Collect body: from after `:=` until blank line / next top-level kw
        body_start_line = j
        body_start_col = assign_offset_in_acc + 2  # skip the `:=`
        # Body on the same line as `:=`
        body_parts = []
        first_line = lines[body_start_line][body_start_col:].strip()
        if first_line:
            body_parts.append(first_line)
        # Continuation lines (indented)
        k = body_start_line + 1
        while k < len(lines):
            ln = lines[k]
            if ln.strip() == '':
                break
            if top_kw_re.match(ln.lstrip()) and not ln.startswith((' ', '\t')):
                break
            # Indented continuation
            body_parts.append(ln.strip())
            k += 1
        body = " ".join(body_parts).strip()
        yield name, line_no, body
        i = k


def extract_placeholder_marker_nodes() -> list[dict]:
    """PlaceholderMarker — Lean decls with trivial body on non-trivial claim.

    Phase 5v Wave 2b. Scans lean/SKEFTHawking/*.lean for theorems whose body
    matches a 'placeholder pattern' (rfl / trivial / Equiv.refl). Excludes
    theorems registered in PLACEHOLDER_THEOREMS (True := trivial — already
    tracked) and excludes decide/native_decide bodies (legitimate finite
    verification, not a placeholder).

    Caveats — this extractor catches the syntactic red flags only. Semantic
    tautologies (e.g., `sixteen_convergence_full` where a conclusion conjunct
    is a hypothesis, body is a non-trivial-looking term construction but
    conveys no content) require LLM inspection and are caught by Stage 13
    adversarial review (Wave 6), not this extractor.
    """
    from src.core.constants import PLACEHOLDER_THEOREMS

    placeholder_short_names = set(PLACEHOLDER_THEOREMS.keys()) if PLACEHOLDER_THEOREMS else set()

    nodes = []
    seen_ids: set[str] = set()

    for lean_file in sorted(LEAN_DIR.glob("*.lean")):
        try:
            source = lean_file.read_text()
        except (OSError, UnicodeDecodeError):
            continue
        module_name = lean_file.stem  # e.g. "RokhlinBridge"
        for thm_name, line_no, body in _scan_lean_theorem_bodies(source):
            if thm_name in placeholder_short_names:
                continue
            pattern_label = None
            for pattern_re, label in _PLACEHOLDER_BODY_PATTERNS:
                if pattern_re.search(body):
                    pattern_label = label
                    break
            if pattern_label is None:
                continue

            full_name = f"SKEFTHawking.{module_name}.{thm_name}"
            node_id = f'placeholder:{full_name}'
            if node_id in seen_ids:
                continue
            seen_ids.add(node_id)

            nodes.append({
                'id': node_id,
                'type': 'PlaceholderMarker',
                'label': thm_name,
                'name': thm_name,
                'verification': 'unverified',
                'detail': f'{module_name}.lean:{line_no} — body matches {pattern_label!r}',
                'meta': {
                    'module': module_name,
                    'lean_full_name': full_name,
                    'lean_file': f'lean/SKEFTHawking/{module_name}.lean',
                    'line': line_no,
                    'body_pattern': pattern_label,
                    'body_preview': body[:200],
                },
            })

    if nodes:
        logger.info("PlaceholderMarker extraction: %d placeholders flagged (rfl/trivial/Equiv.refl bodies)",
                    len(nodes))
    return nodes


def extract_contradiction_nodes() -> list[dict]:
    """Contradiction — concrete cross-paper inconsistency instance.

    Wired in: Wave 2f. Sources: derived from CONTRADICTS edges + ReviewFinding
    pattern clustering. Emits: {id: 'contradiction:{hash}',
    type: 'Contradiction', meta.a_ref, meta.b_ref, meta.detail}.
    """
    return []


def extract_count_metric_nodes() -> list[dict]:
    """CountMetric — snapshot of a counts.json field.

    Phase 5v Wave 2g. Reads docs/counts.json and emits one CountMetric
    node per canonical count field. A single "current snapshot" is
    produced per run (not per-regeneration history — historical snapshots
    can be added later by scanning docs/validation/reports/).

    Each node's detail carries the current value. REPORTS edges from
    Paper nodes (extract_reports_edges) compare this canonical value
    against the count literals that appear in each paper's .tex.
    """
    counts_path = PROJECT_ROOT / "docs" / "counts.json"
    if not counts_path.exists():
        return []
    try:
        import json as _json
        with open(counts_path) as f:
            data = _json.load(f)
    except (OSError, _json.JSONDecodeError):
        return []

    timestamp = data.get('generated', 'unknown')
    lean = data.get('lean', {})
    python = data.get('python', {})
    aristotle = data.get('aristotle', {})

    # Flatten into (metric_name, value) pairs. Only surface metrics that
    # papers actually cite in prose (matches CHECK 17 patterns).
    flat = {
        'total_theorems': lean.get('theorems_total'),
        'substantive_theorems': lean.get('theorems_substantive'),
        'placeholder_theorems': lean.get('theorems_placeholder'),
        'axioms': lean.get('axioms'),
        'sorry': lean.get('sorry_declarations'),
        'lean_modules': lean.get('modules'),
        'lean_definitions': lean.get('definitions'),
        'python_modules': python.get('python_modules'),
        'test_files': python.get('test_files'),
        'figures': python.get('figures'),
        'notebooks': python.get('notebooks'),
        'papers': python.get('papers'),
        'aristotle_proved': aristotle.get('aristotle_proved'),
        'aristotle_runs': aristotle.get('aristotle_runs'),
    }

    nodes = []
    for metric, value in flat.items():
        if value is None:
            continue
        node_id = f'count:{metric}:current'
        nodes.append({
            'id': node_id,
            'type': 'CountMetric',
            'label': metric,
            'name': metric,
            'verification': 'verified',
            'detail': f'canonical value {value} (generated {timestamp})',
            'meta': {
                'metric': metric,
                'value': value,
                'timestamp': timestamp,
                'source': 'docs/counts.json',
            },
        })
    logger.info("CountMetric extraction: %d metrics", len(nodes))
    return nodes


# ═══════════════════════════════════════════════════════════════════════
# Phase 5v Wave 10b — Sentence-level prose audit node extractors
# ═══════════════════════════════════════════════════════════════════════

def _iter_paper_dirs():
    """Yield (paper_key, paper_dir_path) for every papers/paper*_*/ directory."""
    papers_root = PROJECT_ROOT / "papers"
    if not papers_root.is_dir():
        return
    for d in sorted(papers_root.iterdir()):
        if d.is_dir() and d.name.startswith('paper'):
            yield d.name, d


def _load_claims_review(paper_dir: Path) -> dict | None:
    """Load claims_review.json for a paper; return None if missing or v1 schema."""
    cr = paper_dir / "claims_review.json"
    if not cr.exists():
        return None
    try:
        with open(cr) as f:
            data = json.load(f)
    except (json.JSONDecodeError, OSError) as exc:
        logger.warning("Failed to parse %s: %s", cr, exc)
        return None
    # Only consume v2 schema (sentences[] present). v1 files with typed
    # sections are ignored until they're regenerated by claims-reviewer-v2.
    if 'sentences' not in data:
        return None
    return data


def _load_prose_state(paper_dir: Path) -> dict:
    """Load prose_state.json for a paper, or return empty shell."""
    ps = paper_dir / "prose_state.json"
    if not ps.exists():
        return {'sentences': {}}
    try:
        with open(ps) as f:
            return json.load(f)
    except (json.JSONDecodeError, OSError) as exc:
        logger.warning("Failed to parse %s: %s", ps, exc)
        return {'sentences': {}}


def _load_audit_log(paper_dir: Path) -> list[dict]:
    """Load audit_log.jsonl for a paper as list of event dicts."""
    al = paper_dir / "audit_log.jsonl"
    if not al.exists():
        return []
    events = []
    try:
        with open(al) as f:
            for i, line in enumerate(f, 1):
                line = line.strip()
                if not line:
                    continue
                try:
                    events.append(json.loads(line))
                except json.JSONDecodeError as exc:
                    logger.warning("Skipping malformed audit_log line %d in %s: %s",
                                   i, al, exc)
    except OSError as exc:
        logger.warning("Failed to read %s: %s", al, exc)
    return events


def extract_sentence_nodes() -> list[dict]:
    """Sentence — one node per prose unit per paper (Phase 5v Wave 10b).

    Sources claims_review.json (agent-owned) merged with prose_state.json
    (CLI-owned human ratification). A sentence whose id appears in
    prose_state but not in current claims_review is emitted as tombstone.
    """
    nodes: list[dict] = []
    total_tombstones = 0
    papers_seen = 0
    for paper_key, pd in _iter_paper_dirs():
        cr = _load_claims_review(pd)
        if cr is None:
            continue
        papers_seen += 1
        ps = _load_prose_state(pd)
        ps_sentences = ps.get('sentences', {})
        current_ids: set[str] = set()

        for s in cr.get('sentences', []):
            sid = s.get('id')
            if not sid:
                continue
            current_ids.add(sid)
            meta = dict(s.get('meta', {}) or {})
            # Merge top-level fields into meta (claims-reviewer v2 inlines)
            for k in ('section', 'section_ordinal', 'tex_line_start', 'tex_line_end',
                      'quote', 'quote_normalized', 'type', 'agent_verdict',
                      'finding_classes', 'delta_pct', 'agent_notes',
                      'agent_run_id', 'gates_invoked', 'rewrite_of',
                      'tombstone'):
                if k in s:
                    meta.setdefault(k, s[k])
            meta.setdefault('paper_id', paper_key)
            meta.setdefault('sentence_type', s.get('type'))
            # Overlay human ratification state from prose_state.json
            hs = ps_sentences.get(sid, {})
            if hs:
                meta['human_state'] = hs.get('human_state')
                meta['human_ratified_at'] = hs.get('human_ratified_at')
                meta['human_ratified_by'] = hs.get('human_ratified_by')
                meta['human_notes'] = hs.get('human_notes')

            nodes.append({
                'id': sid,
                'type': 'Sentence',
                'name': sid,  # graph_integrity orphan/conflict checks need this
                'label': (s.get('quote') or '')[:80],
                'meta': meta,
            })

        # Tombstones: ids in prose_state but not in current run
        for sid, hs in ps_sentences.items():
            if sid in current_ids:
                continue
            total_tombstones += 1
            nodes.append({
                'id': sid,
                'type': 'Sentence',
                'name': sid,
                'label': '(tombstoned)',
                'meta': {
                    'paper_id': paper_key,
                    'tombstone': True,
                    'human_state': hs.get('human_state'),
                    'human_ratified_at': hs.get('human_ratified_at'),
                    'tombstoned_at': hs.get('tombstoned_at'),
                },
            })

    if nodes:
        logger.info("Sentence extraction: %d nodes across %d papers (%d tombstones)",
                    len(nodes), papers_seen, total_tombstones)
    return nodes


def extract_audit_event_nodes() -> list[dict]:
    """AuditEvent — append-only verification log (Phase 5v Wave 10b).

    Sources audit_log.jsonl per paper. Each line → one node.
    """
    nodes: list[dict] = []
    for paper_key, pd in _iter_paper_dirs():
        events = _load_audit_log(pd)
        for ev in events:
            eid = ev.get('id')
            if not eid:
                continue
            nodes.append({
                'id': eid,
                'type': 'AuditEvent',
                'name': eid,
                'label': ev.get('label', 'audit'),
                'meta': dict(ev.get('meta', {})),
            })
    if nodes:
        logger.info("AuditEvent extraction: %d events", len(nodes))
    return nodes


def extract_claim_cluster_nodes() -> list[dict]:
    """ClaimCluster — cross-paper claim equivalence groups (Phase 5v Wave 10b).

    Sources a project-level `papers/claim_clusters.json` (produced by the
    Wave 10f claims-reviewer-cross-paper pass). Safe no-op if the file
    doesn't exist yet — 10b lands the extractor shape; 10f populates data.
    """
    clusters_file = PROJECT_ROOT / "papers" / "claim_clusters.json"
    if not clusters_file.exists():
        return []
    try:
        with open(clusters_file) as f:
            data = json.load(f)
    except (json.JSONDecodeError, OSError) as exc:
        logger.warning("Failed to parse %s: %s", clusters_file, exc)
        return []
    nodes = []
    for c in data.get('clusters', []):
        cid = c.get('id')
        if not cid:
            continue
        nodes.append({
            'id': cid,
            'type': 'ClaimCluster',
            'name': cid,
            'label': c.get('label', cid),
            'meta': {
                'constructed_by': c.get('constructed_by'),
                'match_kind': c.get('match_kind'),
                'confidence': c.get('confidence'),
                'human_confirmed_at': c.get('human_confirmed_at'),
                'member_count': len(c.get('members', [])),
                'paper_count': len(set(
                    m.split(':')[1] for m in c.get('members', [])
                    if m.startswith('sentence:')
                )),
            },
        })
    if nodes:
        logger.info("ClaimCluster extraction: %d clusters", len(nodes))
    return nodes


def extract_backed_by_edges(node_ids: set) -> list[dict]:
    """BACKED_BY: Sentence → artifact (Phase 5v Wave 10b).

    One edge per chain link in claims_review.json sentences[].chain_proposed.links.
    link_state is derived (link_kind + target node metadata) not stored on edge source.
    """
    edges: list[dict] = []
    # Resolve link targets to existing node ids
    for paper_key, pd in _iter_paper_dirs():
        cr = _load_claims_review(pd)
        if cr is None:
            continue
        for s in cr.get('sentences', []):
            sid = s.get('id')
            if not sid or sid not in node_ids:
                continue
            chain = s.get('chain_proposed') or {}
            for link in chain.get('links', []) or []:
                kind = link.get('kind')
                target = link.get('target')
                if not kind or not target:
                    continue
                # Resolve to node id. Targets are short names / bibkeys etc.;
                # map to graph id conventions:
                #   formula      → formula:<name>
                #   theorem      → lean:<full_name> (via _resolve_lean_short)
                #   axiom        → lean:<full_name> (same resolver)
                #   parameter    → param:<key>
                #   citation     → source:<bibkey>
                #   hypothesis   → hyp:<name>
                #   aristotle    → aristotle:<run_id>
                #   production_run → production:<id>
                candidates = []
                if kind == 'formula':
                    candidates = [f'formula:{target}']
                elif kind in ('theorem', 'axiom'):
                    # Prefer short-name resolution. ``_resolve_lean_short``
                    # also accepts already-qualified names like
                    # ``SKEFTHawking.Module.thm`` and yields ``lean:<full>``.
                    resolved = _resolve_lean_short(target, node_ids)
                    if resolved:
                        candidates = [resolved]
                    else:
                        # Fall back to a whole-module backing reference: a claim
                        # citing module ``X`` resolves to its LeanModule node
                        # instead of becoming a missing_target dangling edge.
                        mod_id = _module_id_for_ref(target, node_ids)
                        candidates = [mod_id] if mod_id else [f'lean:{target}']
                elif kind == 'parameter':
                    candidates = [f'param:{target}']
                elif kind == 'citation':
                    candidates = [f'source:{target}']
                elif kind == 'hypothesis':
                    candidates = [f'hyp:{target}']
                elif kind == 'aristotle':
                    candidates = [f'aristotle:{target}']
                elif kind == 'production_run':
                    candidates = [f'production:{target}']

                target_id = next((c for c in candidates if c in node_ids), None)
                if target_id is None:
                    # Emit with missing_target so integrity check surfaces it
                    edges.append({
                        'source': sid,
                        'target': candidates[0] if candidates else f'unknown:{target}',
                        'type': 'BACKED_BY',
                        'meta': {
                            'link_kind': kind,
                            'link_state': 'missing_target',
                            'computed_value': link.get('computed_value'),
                            'delta_pct': link.get('delta_pct'),
                        },
                    })
                    continue

                edges.append({
                    'source': sid,
                    'target': target_id,
                    'type': 'BACKED_BY',
                    'meta': {
                        'link_kind': kind,
                        'link_state': 'resolved',  # enriched post-hoc by last_modified pass
                        'computed_value': link.get('computed_value'),
                        'delta_pct': link.get('delta_pct'),
                    },
                })
    if edges:
        logger.info("BACKED_BY extraction: %d edges", len(edges))
    return edges


def extract_logged_by_edges(node_ids: set) -> list[dict]:
    """LOGGED_BY: AuditEvent → target (Phase 5v Wave 10b)."""
    edges: list[dict] = []
    for paper_key, pd in _iter_paper_dirs():
        events = _load_audit_log(pd)
        for ev in events:
            eid = ev.get('id')
            meta = ev.get('meta', {})
            target_id = meta.get('target_id')
            if not eid or not target_id:
                continue
            if eid in node_ids and target_id in node_ids:
                edges.append({
                    'source': eid,
                    'target': target_id,
                    'type': 'LOGGED_BY',
                    'meta': {},
                })
    if edges:
        logger.info("LOGGED_BY extraction: %d edges", len(edges))
    return edges


def extract_member_of_edges(node_ids: set) -> list[dict]:
    """MEMBER_OF: Sentence → ClaimCluster (Phase 5v Wave 10b)."""
    clusters_file = PROJECT_ROOT / "papers" / "claim_clusters.json"
    if not clusters_file.exists():
        return []
    try:
        with open(clusters_file) as f:
            data = json.load(f)
    except (json.JSONDecodeError, OSError):
        return []
    edges: list[dict] = []
    for c in data.get('clusters', []):
        cid = c.get('id')
        if not cid or cid not in node_ids:
            continue
        for m in c.get('members', []):
            if m in node_ids:
                edges.append({
                    'source': m,
                    'target': cid,
                    'type': 'MEMBER_OF',
                    'meta': {
                        'member_confidence': c.get('confidence'),
                    },
                })
    if edges:
        logger.info("MEMBER_OF extraction: %d edges", len(edges))
    return edges


def extract_readiness_gate_nodes() -> list[dict]:
    """ReadinessGate — per-paper × per-dimension state (11 gates × 15 papers).

    Phase 5v Wave 4. Aggregates evidence from every other node type to
    produce per-paper per-gate state. Uses `scripts.readiness_gates` for
    the per-gate evaluators; this function is a thin wrapper that runs
    them over the current graph and returns ReadinessGate node payloads.

    Implementation note: to avoid circular graph construction (evaluators
    need a graph; graph extraction produces the nodes), we build a
    graph-without-gates here, run the evaluators, and return the gate
    node list. Edges from gates (IMPACTED_BY) are emitted in Wave 4b.
    """
    # Import here to avoid circular imports; readiness_gates imports
    # only stdlib + logging
    try:
        sys.path.insert(0, str(SCRIPT_DIR))
        from readiness_gates import evaluate_all_gates
    except ImportError as exc:
        logger.warning("readiness_gates not importable (%s); skipping", exc)
        return []

    # Build a pre-gate graph view: all nodes except gates, with edges.
    # We reuse the existing extractors but omit this one to avoid recursion.
    pre_nodes = []
    pre_nodes.extend(extract_parameter_nodes())
    pre_nodes.extend(extract_formula_nodes())
    pre_nodes.extend(extract_lean_declaration_nodes())
    pre_nodes.extend(extract_aristotle_run_nodes())
    pre_nodes.extend(extract_primary_source_nodes())
    pre_nodes.extend(extract_paper_nodes())
    pre_nodes.extend(extract_paper_claim_nodes())
    pre_nodes.extend(extract_figure_nodes())
    hyp_nodes, _ = extract_hypothesis_nodes()
    pre_nodes.extend(hyp_nodes)
    pre_nodes.extend(extract_prose_claim_nodes())
    pre_nodes.extend(extract_python_test_nodes())
    pre_nodes.extend(extract_review_finding_nodes())
    pre_nodes.extend(extract_production_run_nodes())
    pre_nodes.extend(extract_placeholder_marker_nodes())
    pre_nodes.extend(extract_contradiction_nodes())
    pre_nodes.extend(extract_count_metric_nodes())

    node_ids = {n['id'] for n in pre_nodes}
    pre_edges = extract_all_edges_without_gates(node_ids)

    graph_view = {'nodes': pre_nodes, 'links': pre_edges}
    results = evaluate_all_gates(graph_view)
    nodes = [r.to_node_payload() for r in results]

    if nodes:
        from collections import Counter as _C
        states = _C(n['meta']['state'] for n in nodes)
        logger.info("ReadinessGate extraction: %d gates across %d papers (%s)",
                    len(nodes),
                    len(set(n['meta']['paper'] for n in nodes)),
                    dict(states))
    return nodes


def extract_all_edges_without_gates(node_ids: set) -> list[dict]:
    """Extract all edges except gate-derived IMPACTED_BY. Used when
    building the graph-view that readiness evaluators consume, to break
    the recursion (gates need a graph, graph wants gate nodes+edges).
    """
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
    edges.extend(extract_uses_edges(node_ids))
    edges.extend(extract_verifies_edges(node_ids))
    edges.extend(extract_flags_edges(node_ids))
    edges.extend(extract_reports_edges(node_ids))
    edges.extend(extract_cites_source_edges(node_ids))
    edges.extend(extract_cites_theorem_edges(node_ids))
    _hyp_nodes, hyp_edges = extract_hypothesis_nodes()
    for edge in hyp_edges:
        if edge['source'] in node_ids and edge['target'] in node_ids:
            edges.append(edge)
    deduped = []
    seen = set()
    for edge in edges:
        key = (edge['source'], edge['target'], edge['type'])
        if key not in seen:
            seen.add(key)
            deduped.append(edge)
    return deduped


# ═══════════════════════════════════════════════════════════════════════
# Aggregate node extraction
# ═══════════════════════════════════════════════════════════════════════

def _module_id_for_ref(target: str, node_ids: set) -> str | None:
    """Map a 'whole module' backing reference to its LeanModule node id, if one
    exists. Handles the claims-reviewer's surface forms: ``X (module)``,
    ``X_module``, ``SKEFTHawking.X``, bare ``X``, and full nested paths ``A.B``.
    Returns None if the normalized form is not a known module node."""
    base = re.sub(r'\s*\([^)]*\)\s*$', '', target).strip()
    base = re.sub(r'_module$', '', base)
    if not base:
        return None
    cand = base if base.startswith('SKEFTHawking.') else f'SKEFTHawking.{base}'
    mid = f'module:{cand}'
    return mid if mid in node_ids else None


def extract_module_nodes() -> list[dict]:
    """One LeanModule node per Lean module (file), auto-derived from lean_deps.

    This lets the graph 'pick up substrate across all modules' automatically:
    a claim backed by a whole module resolves to its module node with no manual
    registration, instead of becoming a missing_target dangling edge. These are
    container nodes — declaration membership is the lazy DECLARES edge layer
    (loaded on demand like USES), so the default graph stays light.
    """
    from scripts.extract_lean_deps import load_lean_deps

    counts: dict[str, int] = {}
    kinds: dict[str, dict[str, int]] = {}
    for decl in load_lean_deps():
        mod = decl.get('module', '')
        if not mod:
            continue
        kind = decl.get('kind', '')
        if LEAN_KIND_TO_TYPE.get(kind) is None:
            continue
        short = (decl.get('name', '') or '').rsplit('.', 1)[-1]
        if _AUTOGEN_SHORT_RE.match(short):
            continue
        counts[mod] = counts.get(mod, 0) + 1
        kinds.setdefault(mod, {})
        kinds[mod][kind] = kinds[mod].get(kind, 0) + 1

    nodes = []
    for mod, count in sorted(counts.items()):
        label = mod[len('SKEFTHawking.'):] if mod.startswith('SKEFTHawking.') else mod
        nodes.append({
            'id': f'module:{mod}',
            'type': 'LeanModule',
            'label': label,
            'name': label,
            'verification': 'verified',
            'detail': f'{count} declarations',
            'meta': {
                'module_path': mod,
                'declaration_count': count,
                'kinds': kinds.get(mod, {}),
                'shape': SHAPE_MAP['LeanModule'],
            },
        })
    return nodes


def extract_all_nodes() -> list[dict]:
    """Extract all nodes from all extractors."""
    nodes = []
    nodes.extend(extract_parameter_nodes())
    nodes.extend(extract_formula_nodes())
    nodes.extend(extract_lean_declaration_nodes())
    nodes.extend(extract_module_nodes())
    nodes.extend(extract_aristotle_run_nodes())
    nodes.extend(extract_primary_source_nodes())
    nodes.extend(extract_paper_nodes())
    nodes.extend(extract_paper_claim_nodes())
    nodes.extend(extract_figure_nodes())

    # Hypothesis nodes + ASSUMES edges
    hyp_nodes, _hyp_edges = extract_hypothesis_nodes()
    nodes.extend(hyp_nodes)
    # (edges are added separately in build_all_edges)

    # Phase 5v Wave 2a — readiness-system node types (stubs until wired)
    nodes.extend(extract_prose_claim_nodes())
    nodes.extend(extract_python_test_nodes())
    nodes.extend(extract_review_finding_nodes())
    nodes.extend(extract_production_run_nodes())
    nodes.extend(extract_placeholder_marker_nodes())
    nodes.extend(extract_contradiction_nodes())
    nodes.extend(extract_count_metric_nodes())
    nodes.extend(extract_readiness_gate_nodes())

    # Phase 5v Wave 10b — sentence-level prose audit
    nodes.extend(extract_sentence_nodes())
    nodes.extend(extract_audit_event_nodes())
    nodes.extend(extract_claim_cluster_nodes())

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

    Auto-discovers paper -> figure relationships by parsing \\includegraphics
    references in each paper_draft.tex file. Previously this extractor used a
    hand-maintained PAPER_FIGURE_MAP covering only 7 papers (22 edges total);
    Phase 5v Wave 1c switches to filesystem discovery so every included figure
    in every paper surfaces as an edge. Figure node matching is generous:
    tries both the raw basename and fig_-prefixed variants to accommodate
    naming drift between visualizations.py (fig_*) and FIGURE_REGISTRY
    (fig<N>_*).
    """
    papers_dir = PROJECT_ROOT / "papers"
    if not papers_dir.exists():
        return []

    include_re = re.compile(
        r'\\includegraphics(?:\[[^\]]*\])?\{(?:[^{}]*?/)?(?:figures/)?([^{}.]+)(?:\.(?:png|pdf|jpg|jpeg))?\}'
    )

    edges = []
    seen: set[tuple[str, str]] = set()
    unresolved_counter: dict[str, int] = {}

    for tex_path in sorted(papers_dir.glob("paper*_*/paper_draft.tex")):
        paper_key = tex_path.parent.name
        paper_id = f'paper:{paper_key}'
        if paper_id not in node_ids:
            continue
        try:
            text = tex_path.read_text()
        except (OSError, UnicodeDecodeError):
            continue
        for m in include_re.finditer(text):
            raw = m.group(1).strip()
            # Candidates in priority order
            candidates = [raw]
            if not raw.startswith('fig_') and not re.match(r'^fig\d', raw):
                candidates.append(f'fig_{raw}')
            figure_id = None
            for cand in candidates:
                cid = f'figure:{cand}'
                if cid in node_ids:
                    figure_id = cid
                    break
            if figure_id is None:
                unresolved_counter[raw] = unresolved_counter.get(raw, 0) + 1
                continue
            edge_key = (paper_id, figure_id)
            if edge_key not in seen:
                seen.add(edge_key)
                edges.append({
                    'source': paper_id,
                    'target': figure_id,
                    'type': 'HAS_FIGURE',
                })

    if unresolved_counter:
        top = sorted(unresolved_counter.items(), key=lambda x: -x[1])[:5]
        logger.debug(
            "HAS_FIGURE: %d references could not be resolved to Figure nodes; "
            "top unresolved: %s",
            sum(unresolved_counter.values()),
            ", ".join(f"{n} (x{c})" for n, c in top),
        )
    logger.info("HAS_FIGURE: %d edges discovered (%d figure refs unresolved)",
                len(edges), sum(unresolved_counter.values()))
    return edges


def extract_uses_edges(node_ids: set) -> list[dict]:
    """USES: LeanTheorem/LeanDef -> LeanTheorem/LeanDef/LeanStructure/...

    Direct-reference proof-DAG edges derived from the per-declaration
    ``name_deps_project`` field emitted by ``ExtractDeps.lean`` (Phase 5v
    Wave 9c). Each edge means "the source declaration's value (proof body
    / def body) mentions the target declaration by name".

    This is what the dashboard's "Show proof dependencies" toggle uses —
    but because the edge count here can reach ~40k (2800 theorems × ~15
    avg deps), this extractor is **OFF by default** and only runs when
    the env var ``SK_EFT_INCLUDE_USES`` is set to ``1``/``true``. Callers
    that want the proof DAG set the env var and re-request the graph.

    Self-edges and edges to autogen names (already filtered at node
    extraction) are skipped. Duplicate (source, target) pairs collapsed.
    """
    import os
    flag = os.environ.get('SK_EFT_INCLUDE_USES', '').strip().lower()
    if flag not in ('1', 'true', 'yes', 'on'):
        return []

    from scripts.extract_lean_deps import load_lean_deps
    declarations = load_lean_deps()

    edges: list[dict] = []
    seen: set[tuple[str, str]] = set()
    unresolved = 0

    for decl in declarations:
        full_name = decl.get('name', '')
        if not full_name:
            continue
        src_id = f'lean:{full_name}'
        if src_id not in node_ids:
            continue
        for dep in decl.get('name_deps_project', []):
            tgt_id = f'lean:{dep}'
            if tgt_id not in node_ids:
                # Autogen-filtered target or Mathlib straggler — skip.
                unresolved += 1
                continue
            if src_id == tgt_id:
                continue
            key = (src_id, tgt_id)
            if key in seen:
                continue
            seen.add(key)
            edges.append({'source': src_id, 'target': tgt_id, 'type': 'USES'})

    if edges:
        logger.info(
            "USES edges: emitted %d (unresolved/filtered: %d)",
            len(edges), unresolved,
        )
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


# Patterns mapping paper-.tex literal phrases to canonical CountMetric
# node IDs. Each pattern captures (\d+) plus context.
_REPORTS_PATTERNS = [
    (re.compile(r'(\d{2,5})\s+(?:formally[- ]?verified\s+|machine[- ]?checked\s+|Lean\s+)?theorems?\b', re.IGNORECASE),
     'count:total_theorems:current'),
    (re.compile(r'(\d{2,4})\s+(?:Lean\s+)?modules?\b', re.IGNORECASE),
     'count:lean_modules:current'),
    (re.compile(r'(\d{1,4})\s+(?:remaining\s+)?sorry\b', re.IGNORECASE),
     'count:sorry:current'),
    (re.compile(r'(\d{2,4})\s+Aristotle[- ]?proved', re.IGNORECASE),
     'count:aristotle_proved:current'),
    (re.compile(r'(\d{1,3})\s+papers?\b', re.IGNORECASE),
     'count:papers:current'),
    (re.compile(r'(\d{1,4})\s+notebooks?\b', re.IGNORECASE),
     'count:notebooks:current'),
    (re.compile(r'(\d{1,4})\s+figures?\b', re.IGNORECASE),
     'count:figures:current'),
]


def extract_cites_source_edges(node_ids: set) -> list[dict]:
    """CITES_SOURCE: Paper -> PrimarySource.

    Phase 5v coverage-gap fix. For every \\bibitem{key} in each paper's
    .tex, emit an edge to the matching PrimarySource node (if the bibkey
    is in CITATION_REGISTRY). Unregistered bibkeys produce no edge but
    are counted in paper meta as `unregistered_bibkeys` so the
    CitationIntegrity gate can surface the gap.
    """
    papers_dir = PROJECT_ROOT / "papers"
    if not papers_dir.exists():
        return []

    edges = []
    seen: set[tuple[str, str]] = set()
    for tex_path in sorted(papers_dir.glob("paper*_*/paper_draft.tex")):
        paper_key = tex_path.parent.name
        paper_id = f'paper:{paper_key}'
        if paper_id not in node_ids:
            continue
        try:
            text = tex_path.read_text()
        except (OSError, UnicodeDecodeError):
            continue
        for m in re.finditer(r'\\bibitem\{([^}]+)\}', text):
            bibkey = m.group(1).strip()
            target = f'source:{bibkey}'
            if target not in node_ids:
                continue  # unregistered bibkeys are tracked elsewhere
            key = (paper_id, target)
            if key in seen:
                continue
            seen.add(key)
            edges.append({
                'source': paper_id,
                'target': target,
                'type': 'CITES_SOURCE',
                'bibkey': bibkey,
            })
    return edges


def extract_cites_theorem_edges(node_ids: set) -> list[dict]:
    """CITES_THEOREM: Paper -> LeanTheorem.

    Phase 5v coverage-gap fix. Scans each paper's .tex for
    `\\texttt{identifier}` / `\\textsc{identifier}` / `\\verb|identifier|`
    references where `identifier` resolves to exactly one LeanTheorem
    short name. Handles LaTeX-escaped underscores (`\\_` → `_`) which
    papers use routinely inside `\\texttt{}`.

    Filters to LeanTheorem targets only — references that resolve to
    LeanDef / LeanStructure / LeanInstance (typeclass names, structure
    types, etc.) are skipped so the edge carries "this paper cites
    this proved result" semantics, not "this paper names this type".
    """
    papers_dir = PROJECT_ROOT / "papers"
    if not papers_dir.exists():
        return []

    # Build a local type index for LeanTheorem filtering. We can't
    # reuse extract_lean_declaration_nodes (circular in the aggregator
    # sense); instead read _LEAN_SHORT_INDEX which maps short → full IDs,
    # and look up type from the corresponding node by ID via a lazy
    # index built on first need.
    # The cheapest approach: pull the subset of nodes with type
    # 'LeanTheorem' and keep their IDs as an acceptance set.
    theorem_ids = set()
    for node_id in node_ids:
        # Fast path: we only need to know which IDs are LeanTheorem.
        # The node_ids set doesn't carry type info, so we need to
        # reconstruct. Do one pass via extract_lean_declaration_nodes
        # (cached by lru of the lean_deps.json load).
        pass
    # One-shot: get the theorem-only ID set
    _lean_nodes = extract_lean_declaration_nodes()
    theorem_ids = {n['id'] for n in _lean_nodes if n['type'] == 'LeanTheorem'}

    edges = []
    seen: set[tuple[str, str]] = set()
    # Matches \texttt{name}, \textsc{name}, \verb|name|; name may include
    # LaTeX-escaped underscores `\_` which we un-escape before resolving.
    ref_re = re.compile(
        r'\\texttt\{([A-Za-z_][A-Za-z0-9_\\]*?)\}|'
        r'\\textsc\{([A-Za-z_][A-Za-z0-9_\\]*?)\}|'
        r'\\verb\|([A-Za-z_][A-Za-z0-9_\\]*?)\|'
    )
    for tex_path in sorted(papers_dir.glob("paper*_*/paper_draft.tex")):
        paper_key = tex_path.parent.name
        paper_id = f'paper:{paper_key}'
        if paper_id not in node_ids:
            continue
        try:
            text = tex_path.read_text()
        except (OSError, UnicodeDecodeError):
            continue
        for m in ref_re.finditer(text):
            raw = m.group(1) or m.group(2) or m.group(3) or ''
            # Un-escape LaTeX-escaped underscores
            name = raw.replace(r'\_', '_').replace('\\_', '_')
            # Drop anything still containing backslashes or dots — not a
            # clean identifier (catches `LatticeHamiltonian.lean`,
            # `Pi.compactSpace`, stray commands)
            if '\\' in name or '.' in name:
                continue
            # Single-word names without underscores are usually type
            # names (Ring, Algebra, FreeAlgebra, etc.), not theorems
            if '_' not in name:
                continue
            target = _resolve_lean_short(name, node_ids)
            if target is None:
                continue
            if target not in theorem_ids:
                continue  # LeanDef / LeanStructure / LeanInstance — skip
            key = (paper_id, target)
            if key in seen:
                continue
            seen.add(key)
            edges.append({
                'source': paper_id,
                'target': target,
                'type': 'CITES_THEOREM',
                'reference': name,
            })
    return edges


def extract_reports_edges(node_ids: set) -> list[dict]:
    """REPORTS: Paper -> CountMetric.

    Phase 5v Wave 2g. For each paper_draft.tex, scan for count literals
    (same patterns as CHECK 17); for each match, emit a REPORTS edge
    to the corresponding CountMetric node, carrying the paper_value and
    a delta_pct vs the canonical value. The readiness gate
    CountFreshness compares paper_value to canonical value — any paper
    with a REPORTS edge whose delta_pct > 0 is stale.

    Papers that use `\\input{counts.tex}` macros produce no literal
    matches → no REPORTS edges → automatically pass the gate.
    """
    papers_dir = PROJECT_ROOT / "papers"
    if not papers_dir.exists():
        return []

    # Build canonical value lookup from CountMetric nodes
    count_nodes = {n['id']: n for n in extract_count_metric_nodes()}

    edges = []
    seen: set[tuple[str, str, int]] = set()  # (paper_id, target, value) triples
    for tex_path in sorted(papers_dir.glob("paper*_*/paper_draft.tex")):
        paper_key = tex_path.parent.name
        paper_id = f'paper:{paper_key}'
        if paper_id not in node_ids:
            continue
        try:
            text = tex_path.read_text()
        except (OSError, UnicodeDecodeError):
            continue
        for pattern, target_id in _REPORTS_PATTERNS:
            if target_id not in node_ids:
                continue
            canonical = count_nodes.get(target_id, {}).get('meta', {}).get('value')
            for m in pattern.finditer(text):
                try:
                    paper_value = int(m.group(1))
                except ValueError:
                    continue
                # Magnitude filter — only treat this as a project-total
                # claim if the paper value is within 10× of canonical on
                # either side. Sub-10% values are almost always per-module
                # or per-run counts ("24 theorems in Uqsl2Hopf"), not
                # stale project-total claims.
                if canonical and canonical > 0:
                    ratio = paper_value / canonical
                    if ratio < 0.1 or ratio > 10:
                        continue
                # Dedupe by (paper, metric, value)
                key = (paper_id, target_id, paper_value)
                if key in seen:
                    continue
                seen.add(key)
                delta_pct = None
                if canonical and canonical > 0:
                    delta_pct = round(100 * (paper_value - canonical) / canonical, 1)
                stale = bool(delta_pct and abs(delta_pct) > 0.5)
                edges.append({
                    'source': paper_id,
                    'target': target_id,
                    'type': 'REPORTS',
                    'paper_value': paper_value,
                    'canonical_value': canonical,
                    'delta_pct': delta_pct,
                    'stale': stale,
                })
    if edges:
        stale_count = sum(1 for e in edges if e.get('stale'))
        logger.info("REPORTS: %d paper→CountMetric edges (%d stale >0.5%%)",
                    len(edges), stale_count)
    return edges


def extract_flags_edges(node_ids: set) -> list[dict]:
    """FLAGS: ReviewFinding -> Paper / Formula / LeanTheorem / etc.

    Phase 5v Wave 2d. For each ReviewFinding whose meta.inferred_paper
    resolves to a Paper node, emit a FLAGS edge. This is a minimal wiring
    — finer-grained targeting (finding -> specific formula / Lean theorem
    mentioned in the finding text) is deferred; the readiness system
    (Wave 4) will read body text to resolve more targets if needed.

    2026-05-14: added prefix-fallback resolution. The heuristic
    `_infer_paper_key_from_text` returns short keys like `paper10` from
    review-doc body text, but Paper node IDs include a slug suffix
    (`paper:paper10_modular_generation`). When the exact-match lookup
    `paper:<short>` misses, fall back to prefix-match `paper:<short>_*`;
    if exactly one node matches the prefix, treat it as the resolved
    target. If multiple match (e.g., `paper16_graphene_sk_eft` AND
    `paper16_wrt_tqft`), log ambiguity and skip (preserves prior
    behavior for genuinely ambiguous short keys).
    """
    findings = extract_review_finding_nodes()
    paper_ids = {nid for nid in node_ids if nid.startswith('paper:')}
    edges = []
    seen: set[tuple[str, str]] = set()
    ambig_warned: set[str] = set()
    for f in findings:
        paper = f.get('meta', {}).get('inferred_paper')
        if not paper:
            continue
        paper_id = f'paper:{paper}'
        if paper_id not in node_ids:
            # Prefix fallback: paper10 -> paper:paper10_<slug>
            prefix = f'paper:{paper}_'
            candidates = [pid for pid in paper_ids if pid.startswith(prefix)]
            if len(candidates) == 1:
                paper_id = candidates[0]
            elif len(candidates) > 1:
                if paper not in ambig_warned:
                    logger.info(
                        "Ambiguous paper-key resolution: %r matches %d Paper nodes "
                        "(%s) — FLAGS edges skipped for findings inferring this key.",
                        paper, len(candidates), ", ".join(sorted(candidates))
                    )
                    ambig_warned.add(paper)
                continue
            else:
                continue
        if f['id'] not in node_ids:
            continue
        edge_key = (f['id'], paper_id)
        if edge_key in seen:
            continue
        seen.add(edge_key)
        edges.append({
            'source': f['id'],
            'target': paper_id,
            'type': 'FLAGS',
            'severity': f.get('meta', {}).get('severity', 'advisory'),
            'status': f.get('meta', {}).get('status', 'open'),
        })
    return edges


def extract_verifies_edges(node_ids: set) -> list[dict]:
    """VERIFIES: PythonTest -> Formula / Parameter / LeanTheorem.

    Phase 5v Wave 2c. For each PythonTest, inspect its `referenced_names`
    meta; for each name that matches a Formula function name, a Parameter
    short key, or a Lean declaration short name, emit a VERIFIES edge with
    the test_kind attribute. Resolution via _LEAN_SHORT_INDEX for Lean.
    """
    test_nodes = [n for n in extract_python_test_nodes()]
    formula_nodes = [n for n in extract_formula_nodes()]
    param_nodes = [n for n in extract_parameter_nodes()]

    formula_name_to_id = {n['name']: n['id'] for n in formula_nodes}
    # Parameter keys can have dotted forms like 'Steinhauer.omega_perp';
    # also accept the undotted tail
    param_name_to_id: dict[str, str] = {}
    for n in param_nodes:
        param_name_to_id[n['name']] = n['id']
        tail = n['name'].rsplit('.', 1)[-1]
        param_name_to_id.setdefault(tail, n['id'])

    edges = []
    seen: set[tuple[str, str]] = set()
    for test in test_nodes:
        if test['id'] not in node_ids:
            continue
        test_kind = test.get('meta', {}).get('test_kind', 'unknown')
        for raw in test.get('meta', {}).get('referenced_names', []):
            # Try Formula first
            target = formula_name_to_id.get(raw)
            if target is None:
                target = param_name_to_id.get(raw)
            if target is None:
                # Try Lean short-name resolution (returns None if ambiguous/missing)
                lean_id = _resolve_lean_short(raw, node_ids)
                if lean_id is not None:
                    target = lean_id
            if target is None or target not in node_ids:
                continue
            edge_key = (test['id'], target)
            if edge_key in seen:
                continue
            seen.add(edge_key)
            edges.append({
                'source': test['id'],
                'target': target,
                'type': 'VERIFIES',
                'test_kind': test_kind,
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
    edges.extend(extract_uses_edges(node_ids))
    edges.extend(extract_verifies_edges(node_ids))
    edges.extend(extract_flags_edges(node_ids))
    edges.extend(extract_reports_edges(node_ids))
    edges.extend(extract_cites_source_edges(node_ids))
    edges.extend(extract_cites_theorem_edges(node_ids))

    # Phase 5v Wave 10b — sentence-level prose audit edges
    edges.extend(extract_backed_by_edges(node_ids))
    edges.extend(extract_logged_by_edges(node_ids))
    edges.extend(extract_member_of_edges(node_ids))

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
    """Escape a string for use in AGE Cypher property values.

    Order matters:
    - `\\` → `\\\\` first (escape literal backslashes)
    - `'` → `\\'` (escape single quotes that would close the Cypher string)
    - `$$` → `$ $` (PostgreSQL terminates the wrapping dollar-quoted
      string `$$ ... $$` at the first inner `$$`; we cannot use `\\$`
      because Cypher's string-escape grammar only accepts
      `\\", \\', \\/, \\\\, \\b, \\f, \\n, \\r, \\t, \\uXXXX, \\UXXXXXXXX`.
      The cheapest fix is to insert a single space between adjacent
      dollar signs — visually equivalent for LaTeX-rendered labels and
      preserves the SQL-level dollar-quote boundary.)
    """
    if s is None:
        return ''
    return (str(s)
            .replace("\\", "\\\\")
            .replace("'", "\\'")
            .replace("$$", "$ $"))


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

def build_graph_json(*, sync_pg: bool = False) -> dict:
    """Build the complete graph and return as a JSON-serializable dict.

    PG+AGE write is OPT-IN via ``sync_pg=True``. The dashboard serves
    reads from an in-process cache and keeps the Postgres write on a
    separate, debounced path (see ``provenance_dashboard`` cache layer
    and the ``--sync-pg`` CLI flag below). Baking the PG write into
    every ``build_graph_json`` call would block every HTTP request on
    DB connectivity and silently waste seconds per request even when
    the graph is cached upstream.
    """
    _reset_lean_ambiguity_log()  # fresh dedup per build
    nodes = extract_all_nodes()
    node_ids = {n['id'] for n in nodes}
    edges = extract_all_edges(node_ids)

    # Phase 5v Waves 10b/10c — verification change-bus + freshness propagation.
    # Use the canonical {nodes, links} shape (D3 convention; matches
    # build_graph_json's return). Apply verification events FIRST so
    # last_modified_explicit lands before annotate_last_modified walks
    # the dependency edges.
    sys.path.insert(0, str(SCRIPT_DIR))
    _graph_view = {'nodes': nodes, 'links': edges}
    try:
        from verification_state import apply_to_graph as _apply_verif
        _apply_verif(_graph_view)
    except ImportError as _exc:
        logger.warning("verification_state not importable (%s); skipping change-bus apply", _exc)
    except (OSError, ValueError) as _exc:
        # Don't break graph builds on a malformed verification log line.
        logger.warning("verification_state.apply_to_graph failed: %s", _exc)

    try:
        from last_modified import annotate_last_modified
        annotate_last_modified(_graph_view)
    except ImportError as _exc:
        logger.warning("last_modified not importable (%s); skipping freshness annotation", _exc)

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

    if sync_pg:
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
    parser.add_argument('--sync-pg', action='store_true',
                        help='Also write graph to PostgreSQL + AGE '
                             '(off by default; opt-in because HTTP reads '
                             'should never block on DB connectivity).')
    args = parser.parse_args()

    if args.check:
        print(compute_source_hash())
        return

    graph = build_graph_json(sync_pg=args.sync_pg)

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
