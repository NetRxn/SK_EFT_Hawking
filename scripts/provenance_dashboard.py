#!/usr/bin/env python3
"""SK-EFT Provenance Command Center

Interactive Flask+HTMX dashboard for reviewing and verifying parameter
provenance, formula citations, Lean/Aristotle proofs, paper claims, and
the citation registry.

Usage:
    uv run python scripts/provenance_dashboard.py          # start dashboard
    uv run python scripts/provenance_dashboard.py --port 8051  # custom port

Opens at http://localhost:8050 by default.
"""

import argparse
import json
import logging
import os
import re
import sys
import threading
from datetime import datetime, timezone
from pathlib import Path

from flask import Flask, render_template, request, jsonify

# Ensure project root and scripts dir are importable
PROJECT_ROOT = Path(__file__).resolve().parent.parent
SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(PROJECT_ROOT))
sys.path.insert(0, str(SCRIPT_DIR))

app = Flask(__name__, template_folder=str(Path(__file__).parent / "templates"))
app.config['TEMPLATES_AUTO_RELOAD'] = True
app.jinja_env.auto_reload = True

logger = logging.getLogger(__name__)


# ════════════════════════════════════════════════════════════════════
# Graph cache — Phase 5v Wave 9 perf fix
# ════════════════════════════════════════════════════════════════════
#
# Every /api/graph* endpoint used to call build_graph_json() from
# scratch. Hot cost was ~15s per request; cold (stale lean_deps.json)
# triggered a lake subprocess. Paper Focus and Logical Focus fired
# /api/graph/trace and /api/graph/impact, each rebuilding again — so
# a single click chained multiple 15s rebuilds. This cache serves the
# full graph from memory and refreshes lazily when any canonical input
# file changes (mtime-based staleness, cheap — microseconds to check).
#
# PG+AGE sync is now opt-in (build_graph.build_graph_json's sync_pg
# kwarg) and runs on a separate debounced background thread so HTTP
# requests never block on DB connectivity.

_GRAPH_CACHE: dict = {'graph': None, 'fingerprint': None, 'built_at': None,
                      'lean_deps_stale': False}
_GRAPH_CACHE_LOCK = threading.Lock()
_PG_SYNC_LOCK = threading.Lock()
_PG_SYNC_IN_FLIGHT = {'thread': None, 'pending_fingerprint': None}


# Phase 5v Wave 9f: source-of-truth flip. Controlled by env var.
#   json (default) — serve /api/graph* from the in-memory rebuild cache
#   pg             — route trace/impact/subgraph queries to AGE Cypher
# Boot-time validation: if set to `pg`, confirm connectivity at startup;
# fail loudly rather than silently downgrading so setup issues surface.
def _graph_source() -> str:
    return os.environ.get('SK_EFT_GRAPH_SOURCE', 'json').strip().lower()


def _suppress_lake_refresh() -> bool:
    """Prevent the dashboard from ever shelling out to ``lake`` on its own.

    ``extract_lean_deps._run_extraction`` invokes ``lake env lean --run
    SKEFTHawking/ExtractDeps.lean`` as a subprocess. That takes 1-2 min
    on cold toolchain state and was the true cause of the "reload
    hangs" behavior — the prewarm thread held the graph cache lock
    while lake compiled, and concurrent page loads queued behind it.

    Refreshing ``lean_deps.json`` is a heavy, user-intentional action.
    Users re-run ``uv run python scripts/extract_lean_deps.py`` (or
    ``lake build SKEFTHawking.ExtractDeps``) themselves when they've
    changed Lean sources. In the meantime the dashboard serves the
    cached extraction and surfaces a "stale" indicator.

    Gotcha (fixed 2026-04-24): Python imports ``scripts/extract_lean_deps.py``
    via TWO different names — top-level ``extract_lean_deps`` (because
    scripts/ is on sys.path) and package-qualified ``scripts.extract_lean_deps``
    (because build_graph does ``from scripts.extract_lean_deps import ...``).
    Those are **two different module objects** in sys.modules. We must
    patch BOTH, or one call site still shells out and the dashboard hangs.
    """
    def _noop_extraction() -> None:
        logger.warning(
            "lean_deps.json is stale, but the dashboard won't shell out "
            "to lake. Run `uv run python scripts/extract_lean_deps.py` "
            "(or `lake build SKEFTHawking.ExtractDeps`) to refresh. "
            "Serving cached graph data in the meantime."
        )

    needs_refresh = False
    import importlib
    for modname in ('extract_lean_deps', 'scripts.extract_lean_deps'):
        try:
            mod = importlib.import_module(modname)
        except ImportError:
            continue
        # Stamp the stale flag once (they share the same filesystem state).
        if not needs_refresh:
            try:
                needs_refresh = mod._needs_refresh()
            except Exception:
                pass
        mod._run_extraction = _noop_extraction

    _GRAPH_CACHE['lean_deps_stale'] = needs_refresh
    return needs_refresh


def _graph_fingerprint() -> tuple:
    """Cheap staleness signal for the in-memory graph cache.

    Stat the canonical inputs that build_graph_json consumes and
    return (path, mtime_ns) pairs. Any change here invalidates the
    cache on next request. Cost: ~0.5ms — dominated by stat() calls.
    """
    lean_dir = PROJECT_ROOT / "lean" / "SKEFTHawking"
    targets: list[Path] = [
        PROJECT_ROOT / "lean" / "lean_deps.json",
        PROJECT_ROOT / "src" / "core" / "constants.py",
        PROJECT_ROOT / "src" / "core" / "provenance.py",
        PROJECT_ROOT / "src" / "core" / "formulas.py",
        PROJECT_ROOT / "src" / "core" / "visualizations.py",
        PROJECT_ROOT / "src" / "core" / "citations.py",
        PROJECT_ROOT / "src" / "core" / "aristotle_interface.py",
        PROJECT_ROOT / "scripts" / "build_graph.py",
        PROJECT_ROOT / "scripts" / "readiness_gates.py",
        PROJECT_ROOT / "docs" / "counts.json",
    ]
    # Papers + Lean sources are globbed; any file touched trips the cache
    targets.extend(sorted((PROJECT_ROOT / "papers").glob("paper*_*/paper_draft.tex")))
    targets.extend(sorted(lean_dir.glob("*.lean")))
    fp = []
    for p in targets:
        try:
            fp.append((str(p), p.stat().st_mtime_ns))
        except FileNotFoundError:
            fp.append((str(p), 0))
    return tuple(fp)


def _schedule_pg_sync(graph: dict, fingerprint: tuple) -> None:
    """Kick a background thread to write the graph to PG+AGE.

    One writer at a time (tracked by ``_PG_SYNC_LOCK``). If a write is
    already in flight, stash the latest fingerprint so the worker can
    coalesce — no queue, no piling up. PG failures never affect HTTP
    responses.
    """
    from build_graph import write_graph_to_pg

    with _PG_SYNC_LOCK:
        if _PG_SYNC_IN_FLIGHT['thread'] and _PG_SYNC_IN_FLIGHT['thread'].is_alive():
            _PG_SYNC_IN_FLIGHT['pending_fingerprint'] = fingerprint
            return

        def _worker(g, fp):
            try:
                write_graph_to_pg(g)
            except Exception as exc:
                logger.warning("PG+AGE background sync failed: %s", exc)

        t = threading.Thread(
            target=_worker, args=(graph, fingerprint), daemon=True,
            name="pg-age-sync",
        )
        _PG_SYNC_IN_FLIGHT['thread'] = t
        _PG_SYNC_IN_FLIGHT['pending_fingerprint'] = None
        t.start()


def get_cached_graph(*, force_rebuild: bool = False, sync_pg: bool | None = None) -> dict:
    """Return the cached graph, rebuilding if inputs have changed.

    ``force_rebuild`` — ignore cache, rebuild unconditionally (used by
    /api/graph/rebuild).

    ``sync_pg`` — schedule a PG+AGE write after a successful rebuild.
    ``None`` (default) uses the app config ``PG_SYNC_ENABLED`` flag so
    the ``--no-pg-sync`` CLI switch applies everywhere. Pass True/False
    to force the behavior regardless of config (used by the CLI prewarm).
    """
    from build_graph import build_graph_json

    if sync_pg is None:
        sync_pg = app.config.get('PG_SYNC_ENABLED', True)

    fp = _graph_fingerprint()
    with _GRAPH_CACHE_LOCK:
        if (
            not force_rebuild
            and _GRAPH_CACHE['graph'] is not None
            and _GRAPH_CACHE['fingerprint'] == fp
        ):
            return _GRAPH_CACHE['graph']

        # Build outside the critical section would be better, but
        # build_graph_json isn't thread-safe against itself (it mutates
        # module-scoped `_LEAN_AMBIGUITY_SEEN` and `_LEAN_SHORT_INDEX`).
        # Holding the lock across the ~15s rebuild means requests pile
        # up serialized — acceptable because this only happens on
        # staleness, not per request.
        graph = build_graph_json(sync_pg=False)
        _GRAPH_CACHE['graph'] = graph
        _GRAPH_CACHE['fingerprint'] = fp
        _GRAPH_CACHE['built_at'] = datetime.now(timezone.utc).isoformat(timespec='seconds')

    if sync_pg:
        _schedule_pg_sync(graph, fp)
    return graph


# ════════════════════════════════════════════════════════════════════
# Data loading helpers
# ════════════════════════════════════════════════════════════════════

def load_parameters():
    """Load parameter provenance data."""
    from src.core.provenance import PARAMETER_PROVENANCE
    from src.core.constants import EXPERIMENTS, ATOMS, POLARITON_PLATFORMS

    params = []
    for key, entry in sorted(PARAMETER_PROVENANCE.items()):
        # Look up actual code value
        actual = _lookup_actual(key, EXPERIMENTS, ATOMS, POLARITON_PLATFORMS)

        # Determine status
        if entry.get('human_verified_date'):
            status = 'human_verified'
        elif entry.get('llm_verified_date'):
            status = 'llm_verified'
        else:
            status = 'unverified'

        # Detect conflict
        has_conflict = False
        if entry['value'] is None:
            has_conflict = True
        elif actual is not None:
            try:
                rel_err = abs(float(actual) - float(entry['value'])) / max(abs(float(actual)), 1e-30)
                has_conflict = rel_err > 0.001
            except (TypeError, ValueError):
                pass

        # Determine which papers use this parameter
        parts = key.split('.')
        platform = parts[0] if len(parts) > 1 else key
        papers = _papers_using_param(platform)

        params.append({
            'key': key,
            'code_value': actual,
            'provenance_value': entry['value'],
            'unit': entry.get('unit', ''),
            'tier': entry.get('tier', 'UNKNOWN'),
            'source': entry.get('source', ''),
            'detail': entry.get('detail', ''),
            'doi': entry.get('doi'),
            'llm_verified_date': entry.get('llm_verified_date'),
            'llm_verified_notes': entry.get('llm_verified_notes', ''),
            'human_verified_date': entry.get('human_verified_date'),
            'human_verified_notes': entry.get('human_verified_notes', ''),
            'notes': entry.get('notes', ''),
            'status': status,
            'has_conflict': has_conflict,
            'papers': papers,
            'platform': platform,
        })

    return params


def load_formulas():
    """Parse formulas.py docstrings for Lean/Aristotle/Source refs."""
    formulas_path = PROJECT_ROOT / "src" / "core" / "formulas.py"
    if not formulas_path.exists():
        return []

    text = formulas_path.read_text()
    formulas = []

    # Find all function definitions with docstrings
    pattern = re.compile(
        r'^def\s+(\w+)\s*\(.*?\).*?:\s*\n\s*"""(.*?)"""',
        re.MULTILINE | re.DOTALL
    )

    for match in pattern.finditer(text):
        name = match.group(1)
        docstring = match.group(2)
        line_num = text[:match.start()].count('\n') + 1

        lean_ref = _extract_field(docstring, 'Lean')
        aristotle_ref = _extract_field(docstring, 'Aristotle')
        source_ref = _extract_field(docstring, 'Source')

        # First line of docstring as description
        desc_lines = [l.strip() for l in docstring.strip().split('\n') if l.strip()]
        description = desc_lines[0] if desc_lines else ''

        formulas.append({
            'name': name,
            'line': line_num,
            'description': description,
            'lean': lean_ref,
            'aristotle': aristotle_ref,
            'source': source_ref,
            'has_lean': bool(lean_ref),
            'has_aristotle': bool(aristotle_ref),
            'has_source': bool(source_ref),
        })

    return formulas


def load_lean_theorems():
    """Load Lean theorem data from source files and Aristotle registry."""
    from src.core.constants import ARISTOTLE_THEOREMS

    lean_dir = PROJECT_ROOT / "lean" / "SKEFTHawking"
    theorems = []

    if not lean_dir.exists():
        return theorems

    for lean_file in sorted(lean_dir.glob("*.lean")):
        module = lean_file.stem
        for i, line in enumerate(lean_file.read_text().splitlines(), 1):
            if line.startswith("theorem "):
                name = line.split()[1].split("(")[0].split(":")[0].strip()
                run_id = ARISTOTLE_THEOREMS.get(name)

                if run_id and run_id != 'manual':
                    method = 'aristotle'
                elif run_id == 'manual':
                    method = 'manual'
                elif 'sorry' in line:
                    method = 'sorry'
                else:
                    method = 'manual'

                theorems.append({
                    'module': module,
                    'name': name,
                    'line': i,
                    'method': method,
                    'run_id': run_id or '',
                    'statement': line.strip()[:120],
                })
            elif line.startswith("axiom "):
                name = line.split()[1].split("(")[0].split(":")[0].strip()
                theorems.append({
                    'module': module,
                    'name': name,
                    'line': i,
                    'method': 'axiom',
                    'run_id': '',
                    'statement': line.strip()[:120],
                })

    return theorems


def load_paper_claims():
    """Load per-paper claim analysis. For each paper on disk, merges
    declared PAPER_DEPENDENCIES metadata with auto-extracted PaperClaim
    nodes from the graph (covers papers without PAPER_DEPENDENCIES
    entries so every paper surfaces its claims)."""
    from src.core.provenance import PAPER_DEPENDENCIES, PARAMETER_PROVENANCE
    from src.core.constants import ARISTOTLE_THEOREMS

    papers_dir = PROJECT_ROOT / "papers"
    lean_dir = PROJECT_ROOT / "lean" / "SKEFTHawking"
    papers = []

    if not papers_dir.exists():
        return papers

    # Pull PaperClaim nodes + citation edges from the cached graph
    # instead of running the full extractors on every page load. The
    # original code called extract_paper_claim_nodes + extract_all_nodes
    # + extract_cites_*_edges inline, which re-ran all heavy Lean/paper
    # parsing for every request to `/` — the dashboard's "hang on reload"
    # behavior was traced to this path (Phase 5v Wave 9a fix, 2026-04-24).
    graph = get_cached_graph()
    claim_nodes = [n for n in graph['nodes'] if n['type'] == 'PaperClaim']
    claims_by_paper: dict[str, list[dict]] = {}
    for cn in claim_nodes:
        paper = cn.get('meta', {}).get('paper')
        if not paper:
            continue
        claims_by_paper.setdefault(paper, []).append({
            'text': cn.get('name', ''),
            'source': cn.get('meta', {}).get('source', 'declared'),
            'index': cn.get('meta', {}).get('index', 0),
        })

    cites_source_by_paper: dict[str, list[str]] = {}
    cites_theorem_by_paper: dict[str, list[str]] = {}
    for e in graph['links']:
        if e['type'] == 'CITES_SOURCE':
            cites_source_by_paper.setdefault(e['source'], []).append(e.get('bibkey', ''))
        elif e['type'] == 'CITES_THEOREM':
            cites_theorem_by_paper.setdefault(e['source'], []).append(e.get('reference', ''))

    # Build set of all Lean theorem names for cross-referencing
    lean_names = set()
    if lean_dir.exists():
        for lean_file in lean_dir.glob("*.lean"):
            for line in lean_file.read_text().splitlines():
                if line.startswith("theorem "):
                    name = line.split()[1].split("(")[0].split(":")[0].strip()
                    lean_names.add(name)

    for paper_dir in sorted(papers_dir.iterdir()):
        tex_file = paper_dir / "paper_draft.tex"
        if not tex_file.exists():
            continue

        tex = tex_file.read_text()
        tex_lines = tex.splitlines()
        line_count = len(tex_lines)

        # Use declared dependencies (preferred) or fall back to paper name
        meta = PAPER_DEPENDENCIES.get(paper_dir.name, {
            'title': paper_dir.name,
            'topic': '',
            'formulas': [],
            'lean_modules': [],
            'platforms': [],
            'key_claims': [],
        })

        # --- Formula dependencies with Source: status ---
        formula_deps = []
        for fname in meta.get('formulas', []):
            # Check if this formula has a Source: field in formulas.py
            has_source = False
            source_text = ''
            try:
                import src.core.formulas as _f
                func = getattr(_f, fname, None)
                if func and func.__doc__:
                    src_match = re.search(r'Source:\s*(.+)', func.__doc__)
                    if src_match:
                        has_source = True
                        source_text = src_match.group(1).strip()
            except Exception:
                pass
            formula_deps.append({
                'name': fname,
                'has_source': has_source,
                'source': source_text,
            })

        # --- Lean module theorem counts ---
        lean_module_details = []
        for module_name in meta.get('lean_modules', []):
            lean_file = lean_dir / f"{module_name}.lean"
            thm_count = 0
            aristotle_count = 0
            if lean_file.exists():
                for line in lean_file.read_text().splitlines():
                    if line.startswith("theorem "):
                        thm_count += 1
                        name = line.split()[1].split("(")[0].split(":")[0].strip()
                        if name in ARISTOTLE_THEOREMS:
                            aristotle_count += 1
            lean_module_details.append({
                'module': module_name,
                'theorems': thm_count,
                'aristotle': aristotle_count,
            })

        # --- Figures ---
        fig_dir = paper_dir / "figures"
        fig_count = len(list(fig_dir.glob("*.png"))) if fig_dir.exists() else 0
        has_fbox = '\\fbox{\\parbox' in tex

        # --- Bibliography check ---
        has_placeholder_bib = 'xxxxx' in tex.lower() or 'Nature \\textbf{XXX}' in tex
        bibitem_count = tex.count('\\bibitem')

        # --- Parameter readiness ---
        dependent_params = []
        atom_map = {'Steinhauer': 'Rb87', 'Heidelberg': 'K39', 'Trento': 'Na23'}
        seen_keys = set()
        for platform in meta.get('platforms', []):
            for key, entry in PARAMETER_PROVENANCE.items():
                if key.startswith(platform) and key not in seen_keys:
                    seen_keys.add(key)
                    dependent_params.append({
                        'key': key,
                        'human_verified': entry.get('human_verified_date') is not None,
                        'llm_verified': entry.get('llm_verified_date') is not None,
                        'has_conflict': entry['value'] is None,
                    })
            atom = atom_map.get(platform)
            if atom:
                for key, entry in PARAMETER_PROVENANCE.items():
                    if key.startswith(atom) and key not in seen_keys:
                        seen_keys.add(key)
                        dependent_params.append({
                            'key': key,
                            'human_verified': entry.get('human_verified_date') is not None,
                            'llm_verified': entry.get('llm_verified_date') is not None,
                            'has_conflict': entry['value'] is None,
                        })

        params_total = len(dependent_params)
        params_human = sum(1 for p in dependent_params if p['human_verified'])
        params_conflict = sum(1 for p in dependent_params if p['has_conflict'])

        # --- Issues ---
        issues = []
        if has_fbox:
            issues.append('Has \\fbox placeholder figures')
        if has_placeholder_bib:
            issues.append('Has placeholder bibliography entries')
        if params_conflict > 0:
            issues.append(f'{params_conflict} dependent params have unresolved conflicts')
        formulas_without_source = [f for f in formula_deps if not f['has_source']]
        if formulas_without_source:
            issues.append(f'{len(formulas_without_source)} formulas missing Source: field')

        # --- Submission readiness ---
        if params_total == 0:
            param_status = 'no_deps'
        elif params_human == params_total and params_conflict == 0:
            param_status = 'ready'
        elif params_conflict > 0:
            param_status = 'blocked'
        else:
            param_status = 'pending'

        # Merge declared + auto-extracted claims (declared take precedence;
        # if PAPER_DEPENDENCIES has key_claims, PaperClaim nodes mirror
        # them; otherwise PaperClaim nodes are tex-auto and fill the gap).
        graph_claims = sorted(claims_by_paper.get(paper_dir.name, []),
                              key=lambda c: c['index'])
        claim_source = graph_claims[0]['source'] if graph_claims else 'none'

        # Bibliographic coverage: registered bibkeys vs total bibitems in .tex
        paper_id_key = f'paper:{paper_dir.name}'
        all_bibkeys_in_tex = set(re.findall(r'\\bibitem\{([^}]+)\}', tex))
        registered_bibkeys = set(cites_source_by_paper.get(paper_id_key, []))
        unregistered_bibkeys = sorted(all_bibkeys_in_tex - registered_bibkeys)
        bib_coverage_pct = (
            round(100 * len(registered_bibkeys) / len(all_bibkeys_in_tex), 1)
            if all_bibkeys_in_tex else None
        )

        # Theorem-citation coverage: resolved \texttt theorem refs
        resolved_theorem_cites = sorted(set(cites_theorem_by_paper.get(paper_id_key, [])))

        papers.append({
            'name': paper_dir.name,
            'title': meta.get('title', paper_dir.name),
            'topic': meta.get('topic', ''),
            'platforms': meta.get('platforms', []),
            'lean_modules': meta.get('lean_modules', []),
            'lean_module_details': lean_module_details,
            'formula_deps': formula_deps,
            'key_claims': meta.get('key_claims', []),
            'graph_claims': graph_claims,
            'claim_count': len(graph_claims),
            'claim_source': claim_source,
            'registered_bibkeys': sorted(registered_bibkeys),
            'unregistered_bibkeys': unregistered_bibkeys,
            'bib_coverage_pct': bib_coverage_pct,
            'resolved_theorem_cites': resolved_theorem_cites,
            'theorem_cite_count': len(resolved_theorem_cites),
            'lines': line_count,
            'figure_count': fig_count,
            'has_fbox': has_fbox,
            'bibitem_count': bibitem_count,
            'has_placeholder_bib': has_placeholder_bib,
            'dependent_params': dependent_params,
            'params_total': params_total,
            'params_human': params_human,
            'params_conflict': params_conflict,
            'param_status': param_status,
            'issues': issues,
        })

    return papers


def load_proof_architecture():
    """Load data for the Proof Architecture tab.

    Returns a dict with:
      - kind_counts: {type_name: count}
      - total_declarations: int
      - module_count: int
      - sorted_modules: [(module_name, {axioms, theorems, ...})]
      - axiom_cards: [{name, module, eliminability, ...}]
      - struct_fields: [{name, module, fields}]
    """
    from src.core.constants import AXIOM_METADATA, ARISTOTLE_THEOREMS
    from src.core.provenance import PAPER_DEPENDENCIES

    # Phase 5v Wave 9a: pull Lean declaration nodes + axiom edges from
    # the cached graph. Previously this ran extract_lean_declaration_nodes
    # + extract_all_nodes + extract_depends_on_axiom_edges inline, so
    # visiting the Proof Architecture tab triggered a full graph
    # re-extraction (~1.5s) on every page load.
    graph = get_cached_graph()
    lean_types = {'LeanAxiom', 'LeanTheorem', 'LeanDef',
                  'LeanStructure', 'LeanInductive', 'LeanInstance'}
    lean_nodes = [n for n in graph['nodes'] if n['type'] in lean_types]

    # Summary counts by node type
    kind_counts = {}
    for node in lean_nodes:
        kind_counts[node['type']] = kind_counts.get(node['type'], 0) + 1

    # Module breakdown
    modules: dict[str, dict] = {}
    for node in lean_nodes:
        mod = node['meta'].get('module', 'Unknown')
        if mod not in modules:
            modules[mod] = {
                'axioms': 0, 'theorems': 0, 'defs': 0,
                'structures': 0, 'inductives': 0, 'instances': 0, 'total': 0,
            }
        type_key = {
            'LeanAxiom': 'axioms', 'LeanTheorem': 'theorems', 'LeanDef': 'defs',
            'LeanStructure': 'structures', 'LeanInductive': 'inductives',
            'LeanInstance': 'instances',
        }.get(node['type'], 'defs')
        modules[mod][type_key] += 1
        modules[mod]['total'] += 1

    sorted_modules = sorted(modules.items(), key=lambda x: x[1]['total'], reverse=True)

    # Build axiom-to-paper mapping from PAPER_DEPENDENCIES
    axiom_module_to_papers: dict[str, list[str]] = {}
    for paper_key, entry in PAPER_DEPENDENCIES.items():
        for lm in entry.get('lean_modules', []):
            axiom_module_to_papers.setdefault(lm, []).append(
                entry.get('title', paper_key)
            )

    # Axiom cards (from live Lean declarations)
    axiom_nodes = [n for n in lean_nodes if n['type'] == 'LeanAxiom']
    axiom_cards = []
    axiom_edges = [e for e in graph['links'] if e['type'] == 'DEPENDS_ON_AXIOM']

    live_axiom_names = set()
    for ax in axiom_nodes:
        ax_id = ax['id']
        live_axiom_names.add(ax['name'])
        # Downstream: edges where target == this axiom (other decls depend on it)
        downstream = [e for e in axiom_edges if e['target'] == ax_id]
        downstream_names = [e['source'].replace('lean:', '') for e in downstream]

        ax_module = ax['meta'].get('module', '')
        papers_for_axiom = axiom_module_to_papers.get(ax_module, [])

        axiom_cards.append({
            'name': ax['name'],
            'module': ax_module,
            'eliminability': ax['meta'].get('eliminability', 'unknown'),
            'reason': ax['meta'].get('eliminability_reason', ''),
            'statement': ax['meta'].get('type_signature', ''),
            'blast_radius': len(downstream),
            'downstream': downstream_names,
            'core_axioms': ax['meta'].get('axiom_deps_core', []),
            'detail': ax.get('detail', ''),
            'papers': papers_for_axiom,
        })

    # Also include removed axioms from AXIOM_METADATA for historical tracking
    for name, meta in AXIOM_METADATA.items():
        if name not in live_axiom_names:
            ax_module = meta.get('module', '')
            papers_for_axiom = axiom_module_to_papers.get(ax_module, [])
            axiom_cards.append({
                'name': name,
                'module': ax_module,
                'eliminability': meta.get('eliminability', 'unknown'),
                'reason': meta.get('reason', ''),
                'statement': '',
                'blast_radius': 0,
                'downstream': [],
                'core_axioms': [],
                'detail': f'{ax_module}.lean',
                'papers': papers_for_axiom,
            })

    # Structure field assumptions: filter to only Prop-valued fields (constraints)
    prop_indicators = [' < ', ' > ', ' ≤ ', ' ≥ ', ' ≠ ', '.lt ', '.le ',
                       'instLT.lt', 'instLE.le', 'Eq ']
    constraint_name_suffixes = ('_pos', '_nonneg', '_nonpos', '_neg', '_condition',
                                '_decomp', '_eq', '_bound', '_constraint', '_valid',
                                '_compat', '_smooth')

    struct_nodes = [n for n in lean_nodes if n['type'] == 'LeanStructure']
    struct_fields = []
    for s in struct_nodes:
        all_fields = s['meta'].get('field_constraints', [])
        prop_fields = []
        for field in all_fields:
            if isinstance(field, dict):
                fname = field.get('name', '')
                ftype = field.get('type', '')
            else:
                fname = str(field)
                ftype = str(field)
            # Check if this field is Prop-valued
            is_prop = any(ind in ftype for ind in prop_indicators)
            if not is_prop:
                is_prop = any(fname.endswith(s) for s in constraint_name_suffixes)
            if is_prop:
                # Format for display
                if isinstance(field, dict):
                    # Simplify type display
                    display_type = ftype
                    # Remove module prefix for readability
                    display_type = display_type.replace('SKEFTHawking.', '')
                    display_type = display_type.replace('Real.instLT.lt ', '(< ) ')
                    display_type = display_type.replace('Real.instLE.le ', '(≤ ) ')
                    display_type = display_type.replace('instLENat.le ', '(≤ ) ')
                    display_type = display_type.replace('instHAdd.hAdd', '+')
                    display_type = display_type.replace('instHMul.hMul', '*')
                    display_type = display_type.replace('instHMod.hMod', '%')
                    display_type = display_type.replace('instHSMul.hSMul', '•')
                    prop_fields.append(f"{fname} : {display_type}")
                else:
                    prop_fields.append(str(field))

        if prop_fields:
            struct_fields.append({
                'name': s['name'],
                'module': s['meta'].get('module', ''),
                'fields': prop_fields,
            })

    # Fallback: parse Lean source files if no data from JSON
    if not struct_fields:
        struct_fields = _extract_structure_prop_fields()

    return {
        'kind_counts': kind_counts,
        'total_declarations': sum(kind_counts.values()),
        'module_count': len(modules),
        'sorted_modules': sorted_modules,
        'axiom_cards': axiom_cards,
        'struct_fields': struct_fields,
    }


def _extract_structure_prop_fields():
    """Parse Lean source files for structures with Prop-valued fields.

    Identifies fields that are propositions (constraints/conditions), not
    data fields. A field is classified as Prop-valued if its type contains
    comparison operators (< > ≤ ≥ = ≠), quantifiers (∀ ∃), or if the
    field name suggests a constraint (_pos, _nonneg, _condition, etc.)
    AND the type doesn't look like a plain data type (ℝ, ℕ, Matrix, etc.).
    """
    lean_dir = PROJECT_ROOT / "lean" / "SKEFTHawking"
    if not lean_dir.exists():
        return []

    # Patterns that strongly indicate a Prop-valued field type
    prop_patterns = [' < ', ' > ', ' ≤ ', ' ≥ ', ' ≠ ']
    # Equality is prop only if not defining a function
    eq_pattern = ' = '

    # Field names that suggest constraints
    constraint_name_suffixes = (
        '_pos', '_nonneg', '_nonpos', '_neg', '_condition', '_decomp',
        '_eq', '_bound', '_constraint', '_valid', '_compat', '_smooth',
    )

    # Types that indicate data, not propositions
    data_type_indicators = ['ℝ', 'ℕ', 'ℤ', 'ℂ', 'Bool', 'Fin', 'Matrix', 'List', 'Array']

    results = []
    for lean_file in sorted(lean_dir.glob("*.lean")):
        module = lean_file.stem
        lines = lean_file.read_text().splitlines()
        i = 0
        while i < len(lines):
            line = lines[i]
            if line.startswith("structure ") and "where" in line:
                struct_name = line.split()[1].split("(")[0].split("{")[0].strip()
                prop_fields = []
                j = i + 1
                while j < len(lines):
                    raw_line = lines[j]
                    field_line = raw_line.strip()
                    # Skip empty, comments, doc comments
                    if not field_line or field_line.startswith("--") or field_line.startswith("/-"):
                        j += 1
                        continue
                    # End of structure: non-indented line or another definition
                    if raw_line and not raw_line[0].isspace():
                        break
                    # Must have a colon to be a field
                    if ':' in field_line and not field_line.startswith("/"):
                        field_name_part = field_line.split(':')[0].strip()
                        field_type_part = ':'.join(field_line.split(':')[1:]).strip()

                        is_prop = False
                        # Strong prop indicators: comparison operators
                        if any(p in field_type_part for p in prop_patterns):
                            is_prop = True
                        # Equality check (but not if type is just "Type = ...")
                        elif eq_pattern in field_type_part:
                            # Prop equality: things like "a = b" where a,b aren't types
                            if not any(dt in field_type_part.split('=')[0] for dt in data_type_indicators):
                                is_prop = True
                        # Constraint name pattern with non-data type
                        elif any(field_name_part.endswith(s) for s in constraint_name_suffixes):
                            if not any(dt in field_type_part for dt in data_type_indicators):
                                is_prop = True

                        if is_prop:
                            # Clean up: remove doc comment artifacts
                            clean_field = field_line
                            if clean_field.startswith('/--'):
                                clean_field = clean_field.split('-/')[-1].strip() if '-/' in clean_field else clean_field
                            prop_fields.append(clean_field)
                    j += 1
                if prop_fields:
                    results.append({
                        'name': struct_name,
                        'module': module,
                        'fields': prop_fields,
                    })
                i = j
            else:
                i += 1

    return results


def load_citations():
    """Load citation registry data."""
    from src.core.citations import CITATION_REGISTRY

    citations = []
    for key, entry in sorted(CITATION_REGISTRY.items()):
        authors_short = entry['authors'].split(',')[0].strip()
        if ',' in entry['authors']:
            authors_short += ' et al.'

        page = entry.get('page') or '(in press)'
        ref_str = f"{entry['journal']} {entry['volume']}, {page} ({entry['year']})"

        citations.append({
            'key': key,
            'authors': entry['authors'],
            'authors_short': authors_short,
            'title': entry.get('title', ''),
            'ref': ref_str,
            'doi': entry.get('doi'),
            'arxiv': entry.get('arxiv'),
            'doi_verified': entry.get('doi_verified'),
            'used_in': entry.get('used_in', []),
            'provides': entry.get('provides', []),
            'notes': entry.get('notes', ''),
        })

    return citations


def compute_summary(params, formulas, theorems):
    """Compute overall summary statistics."""
    total_params = len(params)
    llm_verified = sum(1 for p in params if p['status'] in ('llm_verified', 'human_verified'))
    human_verified = sum(1 for p in params if p['status'] == 'human_verified')
    conflicts = sum(1 for p in params if p['has_conflict'])

    total_theorems = len(theorems)
    aristotle_proved = sum(1 for t in theorems if t['method'] == 'aristotle')
    manual_proved = sum(1 for t in theorems if t['method'] == 'manual')
    sorry_count = sum(1 for t in theorems if t['method'] == 'sorry')
    axiom_count = sum(1 for t in theorems if t['method'] == 'axiom')

    total_formulas = len(formulas)
    with_lean = sum(1 for f in formulas if f['has_lean'])
    with_source = sum(1 for f in formulas if f['has_source'])

    return {
        'params_total': total_params,
        'params_llm': llm_verified,
        'params_human': human_verified,
        'params_conflicts': conflicts,
        'theorems_total': total_theorems,
        'theorems_aristotle': aristotle_proved,
        'theorems_manual': manual_proved,
        'theorems_sorry': sorry_count,
        'theorems_axioms': axiom_count,
        'formulas_total': total_formulas,
        'formulas_with_lean': with_lean,
        'formulas_with_source': with_source,
    }


# ════════════════════════════════════════════════════════════════════
# Helper functions
# ════════════════════════════════════════════════════════════════════

def _lookup_actual(prov_key, experiments, atoms, polariton_platforms):
    """Look up the actual code value for a provenance key."""
    from src.core.constants import HBAR, K_B, A_BOHR, POLARITON_MASS

    fundamentals = {'HBAR': HBAR, 'K_B': K_B, 'A_BOHR': A_BOHR,
                    'POLARITON_MASS': POLARITON_MASS}
    if prov_key in fundamentals:
        return fundamentals[prov_key]

    parts = prov_key.split('.', 1)
    if len(parts) != 2:
        return None
    group, key = parts

    if group in atoms:
        return atoms[group].get(key)
    if group in experiments:
        return experiments[group].get(key)
    if group in polariton_platforms:
        return polariton_platforms[group].get(key)
    return None


def _extract_field(docstring, field_name):
    """Extract a field value from a docstring (e.g., 'Lean: theorem_name')."""
    pattern = re.compile(rf'{field_name}:\s*(.+?)(?:\n|$)', re.IGNORECASE)
    match = pattern.search(docstring)
    return match.group(1).strip() if match else None


def _papers_using_param(platform):
    """Determine which papers reference a given platform/atom."""
    bec_platforms = {'Steinhauer', 'Heidelberg', 'Trento', 'Rb87', 'K39', 'Na23'}
    polariton_platforms = {'Paris_long', 'Paris_ultralong', 'Paris_standard', 'POLARITON_MASS'}

    if platform in bec_platforms:
        return [1, 2, 3, 4]
    elif platform in polariton_platforms:
        return [1]  # prediction tables
    else:
        return []


def _format_value(val):
    """Format a numerical value for display."""
    if val is None:
        return "NULL (unresolved)"
    try:
        v = float(val)
        if abs(v) < 0.01 or abs(v) > 1e6:
            return f"{v:.4e}"
        return f"{v:.6g}"
    except (TypeError, ValueError):
        return str(val)


# ════════════════════════════════════════════════════════════════════
# Routes
# ════════════════════════════════════════════════════════════════════

@app.route("/")
def index():
    """Main dashboard page."""
    params = load_parameters()
    formulas = load_formulas()
    theorems = load_lean_theorems()
    papers = load_paper_claims()
    citations = load_citations()
    summary = compute_summary(params, formulas, theorems)

    # Load proof architecture data for the lean/proof-arch tab
    proof_arch = None
    tab = request.args.get('tab', 'parameters')
    if tab == 'lean':
        try:
            proof_arch = load_proof_architecture()
        except Exception as e:
            import traceback
            traceback.print_exc()
            proof_arch = {
                'kind_counts': {},
                'total_declarations': 0,
                'module_count': 0,
                'sorted_modules': [],
                'axiom_cards': [],
                'struct_fields': [],
                'error': str(e),
            }
    status_filter = request.args.get('status', 'all')
    tier_filter = request.args.get('tier', 'all')
    paper_filter = request.args.get('paper', 'all')

    filtered_params = params
    if status_filter != 'all':
        if status_filter == 'conflict':
            filtered_params = [p for p in params if p['has_conflict']]
        else:
            filtered_params = [p for p in params if p['status'] == status_filter]
    if tier_filter != 'all':
        filtered_params = [p for p in filtered_params if p['tier'] == tier_filter]
    if paper_filter != 'all':
        paper_num = int(paper_filter)
        filtered_params = [p for p in filtered_params if paper_num in p['papers']]

    # Sort: conflicts first, then unverified, then LLM-only, then verified
    status_order = {'unverified': 0, 'llm_verified': 1, 'human_verified': 2}
    filtered_params.sort(key=lambda p: (
        0 if p['has_conflict'] else 1,
        status_order.get(p['status'], 3),
        p['key']
    ))

    return render_template("dashboard.html",
                           params=filtered_params,
                           formulas=formulas,
                           theorems=theorems,
                           papers=papers,
                           citations=citations,
                           summary=summary,
                           proof_arch=proof_arch,
                           tab=tab,
                           status_filter=status_filter,
                           tier_filter=tier_filter,
                           paper_filter=paper_filter,
                           format_value=_format_value)


@app.route("/verify", methods=["POST"])
def verify_param():
    """HTMX endpoint: mark a parameter as human-verified."""
    key = request.form.get('key')
    action = request.form.get('action')  # 'confirm', 'reject', 'flag'
    notes = request.form.get('notes', '')

    if not key:
        return "Missing key", 400

    # Update provenance.py in memory and prepare for batch save
    from src.core.provenance import PARAMETER_PROVENANCE
    if key not in PARAMETER_PROVENANCE:
        return f"Unknown key: {key}", 404

    entry = PARAMETER_PROVENANCE[key]
    now = datetime.now(timezone.utc).strftime('%Y-%m-%d')

    if action == 'confirm':
        entry['human_verified_date'] = now
        entry['human_verified_notes'] = notes or 'Confirmed via dashboard'
        status_class = 'status-human'
        status_text = 'HUMAN VERIFIED'
    elif action == 'reject':
        entry['human_verified_date'] = None
        entry['human_verified_notes'] = f'REJECTED: {notes}'
        status_class = 'status-conflict'
        status_text = f'REJECTED: {notes}'
    elif action == 'flag':
        entry['human_verified_notes'] = f'FLAGGED: {notes}'
        status_class = 'status-unverified'
        status_text = f'FLAGGED: {notes}'
    else:
        return f"Unknown action: {action}", 400

    # Return updated card fragment via HTMX
    return f'''<span class="status-badge {status_class}">{status_text}</span>
    <small class="verify-date">{now}</small>'''


@app.route("/save", methods=["POST"])
def save_all():
    """Write current PARAMETER_PROVENANCE state back to provenance.py."""
    from src.core.provenance import PARAMETER_PROVENANCE

    provenance_path = PROJECT_ROOT / "src" / "core" / "provenance.py"
    text = provenance_path.read_text()

    # Update human_verified_date and human_verified_notes for each modified entry
    changes = 0
    for key, entry in PARAMETER_PROVENANCE.items():
        if entry.get('human_verified_date'):
            # Find and update in file
            old_pattern = f"'{key}'"
            if old_pattern in text:
                # Update human_verified_date
                old_hvd = "'human_verified_date': None,"
                new_hvd = f"'human_verified_date': '{entry['human_verified_date']}',"
                # This is a simplified approach — for production, use AST rewriting
                # For now, we track changes and report them
                changes += 1

    return f'''<div class="save-status">
        <strong>{changes} parameters updated in memory.</strong>
        <p>Run <code>uv run python scripts/provenance_dashboard.py --write</code> to persist to disk.</p>
    </div>'''


# ════════════════════════════════════════════════════════════════════
# Knowledge Graph API endpoints
# ════════════════════════════════════════════════════════════════════

@app.route("/api/graph")
def api_graph():
    """Return the full provenance graph as JSON for D3 visualization.

    Served from an in-memory cache (see :func:`get_cached_graph`). The
    cache invalidates when any canonical input file changes, so fresh
    data shows up automatically on the next request — no manual poke.
    """
    graph = get_cached_graph()
    return jsonify(graph)


@app.route("/api/graph/rebuild", methods=["POST", "GET"])
def api_graph_rebuild():
    """Force a graph rebuild, bypassing the mtime-based staleness check.

    Use when an input changed in a way stat() can't see (e.g., you
    edited a docstring that re-parses differently but didn't touch any
    file mtime within the watched set).
    """
    graph = get_cached_graph(force_rebuild=True)
    return jsonify({
        "rebuilt": True,
        "node_count": graph['meta']['node_count'],
        "edge_count": graph['meta']['edge_count'],
        "built_at": _GRAPH_CACHE['built_at'],
        "lean_deps_stale": _GRAPH_CACHE['lean_deps_stale'],
    })


@app.route("/api/graph/status")
def api_graph_status():
    """Return lightweight cache state — used by the UI to render a
    "graph is rebuilding" or "Lean deps stale" indicator without pulling
    the full 5 MB payload.
    """
    import extract_lean_deps as eld
    try:
        lean_stale = eld._needs_refresh()
    except Exception:
        lean_stale = False
    _GRAPH_CACHE['lean_deps_stale'] = lean_stale
    return jsonify({
        "built_at": _GRAPH_CACHE['built_at'],
        "node_count": (
            _GRAPH_CACHE['graph']['meta']['node_count']
            if _GRAPH_CACHE['graph'] else 0
        ),
        "edge_count": (
            _GRAPH_CACHE['graph']['meta']['edge_count']
            if _GRAPH_CACHE['graph'] else 0
        ),
        "lean_deps_stale": lean_stale,
        "ready": _GRAPH_CACHE['graph'] is not None,
    })


@app.route("/api/graph/refresh_lean_deps", methods=["POST"])
def api_refresh_lean_deps():
    """Explicit opt-in endpoint to run ``lake env lean --run
    SKEFTHawking/ExtractDeps.lean`` from within the dashboard.

    Users normally run this from the CLI. The endpoint exists so the
    dashboard can wire a button to it (future work). **This blocks for
    1-2 minutes** and monopolizes the Flask worker that serves it —
    do NOT invoke from the UI without a loading indicator.
    """
    import extract_lean_deps as eld
    # Temporarily un-suppress lake invocation, run once, re-suppress.
    _suppressed = eld._run_extraction
    try:
        # The module's own `_run_extraction` (pre-suppression) shells
        # out to lake. We need to reach that original. We captured it
        # by making _suppress_lake_refresh replace the name — the
        # original is bound to `_suppressed` above. To run it we must
        # re-import the module fresh because ``_run_extraction``
        # internally uses module globals (logger, subprocess). Easiest:
        # call through load_lean_deps with a hash mismatch.
        import importlib
        importlib.reload(eld)
        eld.load_lean_deps()
        # Reapply our suppression guard for subsequent calls.
        _suppress_lake_refresh()
        # Invalidate graph cache so next /api/graph rebuilds with fresh deps.
        with _GRAPH_CACHE_LOCK:
            _GRAPH_CACHE['graph'] = None
            _GRAPH_CACHE['fingerprint'] = None
        return jsonify({"refreshed": True,
                        "hint": "Next /api/graph call will rebuild with fresh Lean deps."})
    except Exception as exc:
        return jsonify({"refreshed": False, "error": str(exc)}), 500


@app.route("/api/graph/trace/<path:node_id>")
def api_trace(node_id):
    """Return the provenance chain for a node (bidirectional BFS).

    Walks forward through outgoing edges (source->target) AND backward
    through incoming edges (target->source) to find the full chain.
    """
    graph = get_cached_graph()
    nodes = graph['nodes']
    links = graph['links']

    # Validate node exists
    node_ids = {n['id'] for n in nodes}
    if node_id not in node_ids:
        return jsonify({'error': f'Unknown node: {node_id}'}), 404

    # Build adjacency indexes once per request — O(E) rather than
    # scanning the full edge list inside each recursive step.
    out_idx: dict[str, list[int]] = {}
    in_idx: dict[str, list[int]] = {}
    for i, link in enumerate(links):
        out_idx.setdefault(link['source'], []).append(i)
        in_idx.setdefault(link['target'], []).append(i)

    traced_node_ids: set[str] = set()
    traced_edge_indices: set[int] = set()

    def walk(nid: str, idx: dict[str, list[int]], link_end: str) -> None:
        stack = [nid]
        while stack:
            cur = stack.pop()
            if cur in traced_node_ids:
                continue
            traced_node_ids.add(cur)
            for i in idx.get(cur, ()):
                traced_edge_indices.add(i)
                stack.append(links[i][link_end])

    walk(node_id, out_idx, 'target')  # forward
    walk(node_id, in_idx, 'source')   # backward

    return jsonify({
        'traced_node_ids': sorted(traced_node_ids),
        'traced_edge_indices': sorted(traced_edge_indices),
    })


@app.route("/api/graph/impact/<path:node_id>")
def api_impact(node_id):
    """Return all nodes that depend on the given node (upstream walk).

    Walks upstream: find edges where target == current, follow source.
    Also walks downstream: find edges where source == current, follow target.
    """
    graph = get_cached_graph()
    nodes = graph['nodes']
    links = graph['links']

    node_ids = {n['id'] for n in nodes}
    if node_id not in node_ids:
        return jsonify({'error': f'Unknown node: {node_id}'}), 404

    # One-time adjacency build; O(E) vs re-scanning per recursion step.
    out_idx: dict[str, list[int]] = {}
    in_idx: dict[str, list[int]] = {}
    for i, link in enumerate(links):
        out_idx.setdefault(link['source'], []).append(i)
        in_idx.setdefault(link['target'], []).append(i)

    impacted_node_ids: set[str] = {node_id}
    impacted_edge_indices: set[int] = set()

    # Upstream: who depends on me (follow incoming edges backward).
    stack = [node_id]
    while stack:
        cur = stack.pop()
        for i in in_idx.get(cur, ()):
            src = links[i]['source']
            if src not in impacted_node_ids:
                impacted_node_ids.add(src)
                impacted_edge_indices.add(i)
                stack.append(src)

    # Downstream: one hop from the seed (matches the prior semantics —
    # the original downstream() didn't recurse, just flagged direct
    # targets. Keeping that contract to avoid surprising the UI.)
    for i in out_idx.get(node_id, ()):
        tgt = links[i]['target']
        if tgt not in impacted_node_ids:
            impacted_node_ids.add(tgt)
            impacted_edge_indices.add(i)

    return jsonify({
        'impacted_node_ids': sorted(impacted_node_ids),
        'impacted_edge_indices': sorted(impacted_edge_indices),
    })


@app.route("/api/graph/integrity")
def api_integrity():
    """Return the graph integrity report."""
    from graph_integrity import run_integrity_checks
    return jsonify(run_integrity_checks())


# ──────────────────────────────────────────────────────────────
# Read-only Cypher endpoint (Phase 5v Wave 9f)
# ──────────────────────────────────────────────────────────────
#
# Exposes parameterised Cypher queries against the AGE-backed graph
# (database: sk_eft_provenance, graph: sk_eft). Dashboard subgraph
# endpoints route through this when SK_EFT_GRAPH_SOURCE=pg; scripts
# and notebooks can use it directly via HTTP.
#
# Safety guards (MANDATORY — do not relax without discussion):
#   - Only SELECT/MATCH/RETURN allowed. CREATE / DELETE / MERGE / SET /
#     REMOVE / DROP all rejected with 400. Keeps this endpoint read-only
#     even if an authenticated client goes rogue.
#   - Query length capped at 4000 chars. AGE doesn't do automatic timeout
#     per-query, so big queries are the main DoS vector.
#   - Parameters passed as a dict; values are escaped through psycopg's
#     parameter binding for the outer SELECT, not inlined into the
#     Cypher body. The Cypher body itself is a literal — callers must
#     validate their own query strings.

_CYPHER_READ_ONLY_RX = re.compile(
    r'\b(CREATE|DELETE|MERGE|SET|REMOVE|DROP|DETACH|CALL\s+db\.)\b',
    re.IGNORECASE,
)


@app.route("/api/graph/cypher", methods=["POST"])
def api_cypher():
    """Execute a read-only Cypher query against AGE.

    POST body (JSON): ``{"query": "MATCH (n:LeanTheorem) WHERE ... RETURN n LIMIT 50"}``

    Response: ``{"rows": [[...], ...], "columns": ["n"], "ms": 42.3, "count": N}``
    or ``{"error": "...", "hint": "..."}`` with HTTP 400/500.
    """
    body = request.get_json(silent=True) or {}
    query = (body.get('query') or '').strip()

    if not query:
        return jsonify({"error": "missing 'query' field in POST body"}), 400
    if len(query) > 4000:
        return jsonify({"error": "query too long (4000 char cap)"}), 400
    if _CYPHER_READ_ONLY_RX.search(query):
        return jsonify({
            "error": "write clauses are not permitted on /api/graph/cypher",
            "hint": "CREATE / DELETE / MERGE / SET / REMOVE / DROP are blocked; "
                    "use scripts/sync_graph_to_pg.py for writes.",
        }), 400

    try:
        import psycopg  # type: ignore
    except ImportError:
        return jsonify({"error": "psycopg not installed in the dashboard venv"}), 500

    t0 = __import__('time').monotonic()
    try:
        with psycopg.connect(
            "host=localhost port=5433 dbname=sk_eft_provenance "
            "user=sk_eft password=sk_eft_local",
            connect_timeout=5,
        ) as conn, conn.cursor() as cur:
            cur.execute("LOAD 'age'")
            cur.execute("SET search_path = ag_catalog, '$user', public")

            # AGE's Cypher wrapper requires us to declare each returned
            # column's label as `agtype` in the outer SELECT. We can't
            # introspect the return shape from Python, so we ask AGE to
            # wrap the whole result in a single agtype column — the
            # caller gets stringified agtype values back and parses them
            # themselves. That's the simplest reliable path.
            escaped = query.replace("$$", "\\$\\$")
            wrapped = (
                f"SELECT agtype_out(r) FROM cypher('sk_eft', $$ "
                f"{escaped} "
                f"$$) AS (r agtype)"
            )
            cur.execute(wrapped)
            rows = cur.fetchall()
    except psycopg.OperationalError as exc:
        return jsonify({
            "error": f"PG unreachable: {exc}",
            "hint": "Confirm docker container is running "
                    "(port 5433, sk_eft_provenance DB).",
        }), 503
    except Exception as exc:
        return jsonify({"error": f"cypher execution failed: {exc}"}), 500

    t1 = __import__('time').monotonic()

    # Rows are tuples with a single stringified agtype value; flatten.
    # Callers that want structured values can parse the agtype string.
    flat_rows = [r[0] if isinstance(r, tuple) and len(r) == 1 else r for r in rows]

    return jsonify({
        "rows": flat_rows,
        "count": len(flat_rows),
        "ms": round((t1 - t0) * 1000, 2),
        "query": query,
    })


# ──────────────────────────────────────────────────────────────
# Proof-dependency subgraph (Phase 5v Wave 9c)
# ──────────────────────────────────────────────────────────────
#
# The default /api/graph response omits USES (direct proof-reference)
# edges because emitting all ~40k of them on every request would inflate
# the payload ~15x. Instead they're fetched on demand through this
# endpoint, which re-extracts USES edges once, caches them separately,
# and returns only the edges themselves (the nodes are already in the
# base graph). The UI merges these into its D3 data lazily when the
# "Show proof dependencies" toggle flips on.

_USES_CACHE: dict = {'edges': None, 'fingerprint': None, 'built_at': None}
_USES_CACHE_LOCK = threading.Lock()


def _get_uses_edges() -> list[dict]:
    """Return the cached USES edges (proof-dep DAG), rebuilding lazily."""
    import os
    fp = _graph_fingerprint()
    with _USES_CACHE_LOCK:
        if _USES_CACHE['edges'] is not None and _USES_CACHE['fingerprint'] == fp:
            return _USES_CACHE['edges']
        # Temporarily flip the env var and re-run the USES extractor only.
        # We can't reuse the main graph cache here because its fingerprint
        # coincides and its extraction runs under SK_EFT_INCLUDE_USES=0.
        prev = os.environ.get('SK_EFT_INCLUDE_USES')
        os.environ['SK_EFT_INCLUDE_USES'] = '1'
        try:
            graph = get_cached_graph()
            from build_graph import extract_uses_edges
            node_ids = {n['id'] for n in graph['nodes']}
            edges = extract_uses_edges(node_ids)
        finally:
            if prev is None:
                os.environ.pop('SK_EFT_INCLUDE_USES', None)
            else:
                os.environ['SK_EFT_INCLUDE_USES'] = prev
        _USES_CACHE['edges'] = edges
        _USES_CACHE['fingerprint'] = fp
        _USES_CACHE['built_at'] = datetime.now(timezone.utc).isoformat(timespec='seconds')
        return edges


# ──────────────────────────────────────────────────────────────
# Chain / Proof-Chain-Viz endpoints (Phase 5v Wave 9d)
# ──────────────────────────────────────────────────────────────
#
# Three zoom levels per the design contract
# (Lit-Search/Phase-5v/Designs/Proof-Chein-Viz-Dashboard/docs/SUBGRAPH_CONTRACT.md):
#   L0 — /api/chain/{id}/summary    — verdict strip
#   L1 — /api/chain/{id}/milestones — milestone DAG (deterministic layout)
#   L2 — /api/chain/{id}/subgraph   — full chain subgraph + 1-hop externals
#
# Chains are DISCOVERED, not hardcoded. Any node whose meta.chain_ids
# includes a value materialises that chain. See src/core/constants.py
# MODULE_CHAIN_MAP for the module-to-chain mapping; adding a new entry
# there (or adding a node-level chain_id override) creates a new chain
# in the dashboard with no registry plumbing.

def _chain_nodes(graph: dict, chain_id: str) -> list[dict]:
    """Return all nodes belonging to the given chain."""
    return [n for n in graph['nodes']
            if chain_id in (n.get('meta', {}).get('chain_ids') or [])]


@app.route("/api/chain/list")
def api_chain_list():
    """Return the set of chain_ids present in the current graph, with
    per-chain node counts and a rough verdict (from summary counts)."""
    graph = get_cached_graph()
    from collections import Counter
    chain_counter: Counter = Counter()
    unclassified = 0
    for n in graph['nodes']:
        ids = n.get('meta', {}).get('chain_ids')
        if not ids:
            # Only count Lean nodes as unclassified (Paper / Formula etc.
            # may legitimately lack a chain tag).
            if n['type'] in (
                'LeanTheorem', 'LeanAxiom', 'LeanDef',
                'LeanStructure', 'LeanInductive', 'LeanInstance',
            ):
                unclassified += 1
            continue
        for cid in ids:
            chain_counter[cid] += 1
    chains = [
        {
            'chain_id': cid,
            'node_count': count,
        }
        for cid, count in sorted(chain_counter.items(), key=lambda x: -x[1])
    ]
    return jsonify({
        'chains': chains,
        'unclassified_lean_nodes': unclassified,
        'built_at': _GRAPH_CACHE['built_at'],
    })


@app.route("/api/chain/<chain_id>/summary")
def api_chain_summary(chain_id: str):
    """L0 — verdict strip: aggregate counts + state for a chain."""
    graph = get_cached_graph()
    chain_ns = _chain_nodes(graph, chain_id)
    if not chain_ns:
        return jsonify({'error': f'Unknown chain: {chain_id}'}), 404

    def count_by(pred):
        return sum(1 for n in chain_ns if pred(n))

    counts = {
        'axioms': {
            'total': count_by(lambda n: n['type'] == 'LeanAxiom'),
            'verified': count_by(lambda n: n['type'] == 'LeanAxiom'
                                 and n.get('verification') == 'verified'),
        },
        'theorems': {
            'total': count_by(lambda n: n['type'] == 'LeanTheorem'),
            'verified': count_by(lambda n: n['type'] == 'LeanTheorem'
                                 and n.get('verification') == 'verified'),
        },
        'defs': count_by(lambda n: n['type'] == 'LeanDef'),
        'structures': count_by(lambda n: n['type'] == 'LeanStructure'),
        'placeholders': count_by(
            lambda n: n.get('meta', {}).get('method') == 'manual'
            and any(tag in (n.get('label', '').lower()) for tag in ('placeholder', 'stub'))
        ),
        'milestones': count_by(lambda n: n.get('meta', {}).get('is_milestone')),
    }

    # Verdict heuristic. Needs tuning once ReadinessGate -> chain_id rollups exist.
    if counts['theorems']['verified'] == counts['theorems']['total'] and counts['placeholders'] == 0:
        verdict = 'solid'
    elif counts['placeholders']:
        verdict = 'solid-gaps'
    else:
        verdict = 'mixed'

    return jsonify({
        'chain_id': chain_id,
        'verdict': verdict,
        'counts': counts,
        'built_at': _GRAPH_CACHE['built_at'],
    })


@app.route("/api/chain/<chain_id>/milestones")
def api_chain_milestones(chain_id: str):
    """L1 — milestone DAG: 6–12 pillar nodes + proved-edges between them.

    Edges between milestones are computed as graph reachability through
    non-milestone intermediates (hop_count = shortest path length).
    """
    graph = get_cached_graph()
    chain_ns = _chain_nodes(graph, chain_id)
    if not chain_ns:
        return jsonify({'error': f'Unknown chain: {chain_id}'}), 404

    milestones = [n for n in chain_ns if n.get('meta', {}).get('is_milestone')]
    milestone_ids = {n['id'] for n in milestones}

    # Build adjacency for the chain's subgraph (+ 1-hop externals for
    # traversal fidelity). Use project-meaningful edges only: PROVED_BY,
    # USES, USED_BY, DEPENDS_ON_AXIOM, IMPORTS, GROUNDED_IN.
    trav_types = {'PROVED_BY', 'USES', 'USED_BY', 'DEPENDS_ON_AXIOM',
                  'GROUNDED_IN', 'CLAIMS'}
    chain_set = {n['id'] for n in chain_ns}
    adj: dict[str, set[str]] = {}
    for e in graph['links']:
        if e['type'] not in trav_types:
            continue
        src, tgt = e['source'], e['target']
        if src in chain_set or tgt in chain_set:
            adj.setdefault(src, set()).add(tgt)

    # For each pair (milestone, milestone), compute shortest path length
    # through non-milestone intermediates. Capped at depth 5 to stay cheap.
    from collections import deque
    edges: list[dict] = []
    for m in milestones:
        seen = {m['id']: 0}
        q: deque[tuple[str, int]] = deque([(m['id'], 0)])
        MAX_DEPTH = 5
        while q:
            cur, depth = q.popleft()
            if depth >= MAX_DEPTH:
                continue
            for nxt in adj.get(cur, ()):
                if nxt in seen:
                    continue
                seen[nxt] = depth + 1
                if nxt in milestone_ids and nxt != m['id']:
                    edges.append({
                        'from': m['id'],
                        'to': nxt,
                        'kind': 'USED_BY',
                        'hop_count': depth + 1,
                        'confidence': 'proved',
                    })
                    # Don't traverse beyond another milestone
                    continue
                q.append((nxt, depth + 1))

    # Shape output per SUBGRAPH_CONTRACT.md section 3
    nodes_out = [
        {
            'id': m['id'],
            'label': m.get('label', m['id'].split(':')[-1]),
            'type': m['type'],
            'node_shape': m.get('meta', {}).get('shape', 'circle'),
            'verification': m.get('verification', 'verified'),
            'is_external_axiom': m['type'] == 'LeanAxiom',
            'milestone_order': m.get('meta', {}).get('milestone_order'),
        }
        for m in milestones
    ]
    nodes_out.sort(key=lambda n: (
        n.get('milestone_order') if n.get('milestone_order') is not None else 99,
        n['label']
    ))

    return jsonify({
        'chain_id': chain_id,
        'nodes': nodes_out,
        'edges': edges,
        'built_at': _GRAPH_CACHE['built_at'],
    })


@app.route("/api/chain/<chain_id>/subgraph")
def api_chain_subgraph(chain_id: str):
    """L2 — full subgraph for a chain, same node/link shape as /api/graph."""
    graph = get_cached_graph()
    chain_ns = _chain_nodes(graph, chain_id)
    if not chain_ns:
        return jsonify({'error': f'Unknown chain: {chain_id}'}), 404

    # Chain node set + 1-hop externals
    chain_set = {n['id'] for n in chain_ns}
    external: set[str] = set()
    edges_out: list[dict] = []
    for e in graph['links']:
        if e['source'] in chain_set and e['target'] in chain_set:
            edges_out.append(e)
        elif e['source'] in chain_set and e['target'] not in chain_set:
            external.add(e['target'])
            edges_out.append(e)
        elif e['target'] in chain_set and e['source'] not in chain_set:
            external.add(e['source'])
            edges_out.append(e)

    nodes_out = list(chain_ns)
    for nid in external:
        n = next((nn for nn in graph['nodes'] if nn['id'] == nid), None)
        if n:
            nodes_out.append({**n, '_external': True})

    return jsonify({
        'chain_id': chain_id,
        'nodes': nodes_out,
        'links': edges_out,
        'meta': {
            'internal_count': len(chain_ns),
            'external_count': len(external),
            'built_at': _GRAPH_CACHE['built_at'],
        },
    })


@app.route("/api/graph/uses_edges")
def api_uses_edges():
    """Return the proof-dependency (USES) edges.

    These are direct references in each Lean theorem/def's body — "this
    proof invokes that lemma". Excluded from /api/graph by default
    because there are ~40k of them (every theorem pulls in ~15 lemmas).
    Enabled via the "Show proof dependencies" dashboard toggle.

    If ``lean_deps.json`` predates the Wave 9c ExtractDeps upgrade (no
    ``name_deps_project`` field on declarations), this returns an empty
    list and a ``reason`` hint so the UI can prompt to re-extract.
    """
    edges = _get_uses_edges()
    hint = None
    if not edges:
        # Probe lean_deps.json to distinguish "genuinely zero" from
        # "extraction hasn't emitted the field yet"
        try:
            from extract_lean_deps import load_lean_deps
            decls = load_lean_deps()
            has_field = any('name_deps_project' in d for d in decls[:20])
            if not has_field:
                hint = ("lean_deps.json predates the Wave 9c ExtractDeps "
                        "upgrade. Run `uv run python scripts/extract_lean_deps.py` "
                        "after the next successful `lake build SKEFTHawking.ExtractDeps` "
                        "to populate name_deps_project, then reload.")
        except Exception:
            pass
    return jsonify({
        'edges': edges,
        'count': len(edges),
        'built_at': _USES_CACHE['built_at'],
        'hint': hint,
    })


# ──────────────────────────────────────────────────────────────
# Paper Provenance (Phase 5v Wave 9g)
# ──────────────────────────────────────────────────────────────
#
# Per-paper 8-layer dossier — the interactive-tab deliverable from
# `Lit-Search/Phase-5v/Designs/Proof-Chein-Viz-Dashboard-v2/`.
# Consumes `papers/<paper>/claims_review.json` (generated by the
# physics-qa:claims-reviewer agent) + `papers/<paper>/figures/
# figure_review_report.json` (figure-reviewer) + live registries
# (PARAMETER_PROVENANCE, CITATION_REGISTRY, etc.). Returns the exact
# shape the v2 `paper-review.js` + `paper-provenance.js` consume so
# the tab can be a straight port of the design.
#
# The 8 layers (matches LAYERS in the v2 design):
#   NUM · THM · AX · HYP · CIT · PAR · FIG · QUA
#
# Claim IDs: for papers without inline `\claim{id}{...}` macros
# (Wave 9g-3 follow-up), we auto-generate stable IDs from
# `(layer, location)` so reruns hit the same keys.

_PP_LAYERS_SPEC = [
    ("NUM", "Numeric", "Recomputed against canonical constants + formulas"),
    ("THM", "Theorem", "Named Lean theorem exists, no sorry, axiom-deps known"),
    ("AX",  "Axiom", "Axiom-risk scan — which project axioms (if any) this claim depends on"),
    ("HYP", "Hypothesis", "Explicit + implicit hypothesis registry cross-check"),
    ("CIT", "Citation", "Bibkey in CITATION_REGISTRY; \\cite in-text present"),
    ("PAR", "Parameter", "Parameter provenance — tier, llm-verified date, human-verified date"),
    ("FIG", "Figure", "Figure regeneration review — data, physics, style, caption match"),
    ("QUA", "Qualitative", "Non-numeric assertions evaluated against cited literature"),
]

# Map claims_review.json section name → (layer code, label-extractor fn).
# Label-extractor pulls a human-readable quote from the entry.
_CR_SECTION_MAP: dict[str, tuple[str, str]] = {
    'numerical_claims':    ('NUM', 'paper_value'),
    'theorem_refs':        ('THM', 'name'),
    'axiom_risk':          ('AX',  'finding'),
    'hypothesis_risk':     ('HYP', 'finding'),
    'citation_integrity':  ('CIT', 'bibkey'),
    'parameter_provenance':('PAR', 'key'),
    'qualitative_claims':  ('QUA', 'claim'),
}


def _pp_claim_id(section: str, entry: dict, idx: int) -> str:
    """Stable auto-generated claim ID for an entry without an explicit
    `\\claim{id}` anchor. Prefers meaningful fields (bibkey, param key,
    theorem name) and falls back to `section-{idx}` so IDs stay stable
    run-over-run even if the entry order shifts."""
    for key in ('bibkey', 'key', 'name'):
        if key in entry and isinstance(entry[key], str):
            return f"{section}:{entry[key]}"
    # Numerical / qualitative / axiom-risk — use location or stable index
    loc = (entry.get('location') or '').strip()
    if loc:
        safe = re.sub(r'[^A-Za-z0-9._-]+', '-', loc).strip('-').lower()[:60]
        if safe:
            return f"{section}:{safe}"
    return f"{section}:{idx}"


def _pp_finding_for_entry(layer: str, entry: dict) -> dict:
    """Convert a claims_review.json entry into a finding dict matching
    the v2 design's `{layer, status, delta?, note}` schema."""
    finding: dict = {
        'layer': layer,
        'status': entry.get('status', 'INFO'),
    }
    # Numeric claims carry a delta_pct — promote to top-level `delta`
    if 'delta_pct' in entry and entry['delta_pct'] is not None:
        try:
            finding['delta'] = f"{float(entry['delta_pct']):.2f}%"
        except (TypeError, ValueError):
            pass
    note_parts = []
    for key in ('notes', 'finding', 'computed_value', 'support'):
        if key in entry and entry[key]:
            note_parts.append(str(entry[key]))
    # Show paper_value for numeric claims if no notes
    if not note_parts and 'paper_value' in entry:
        note_parts.append(f"paper: {entry['paper_value']}")
    finding['note'] = ' · '.join(note_parts) if note_parts else '(no notes)'
    return finding


def _pp_load_claims_review(paper_id: str) -> dict | None:
    """Load `papers/<paper>/claims_review.json` if present."""
    path = PROJECT_ROOT / 'papers' / paper_id / 'claims_review.json'
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text())
    except Exception as exc:
        logger.warning("Failed to parse claims_review for %s: %s", paper_id, exc)
        return None


def _pp_load_figure_review(paper_id: str) -> dict | None:
    """Load `papers/<paper>/figures/figure_review_report.json` if present."""
    path = PROJECT_ROOT / 'papers' / paper_id / 'figures' / 'figure_review_report.json'
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text())
    except Exception as exc:
        logger.warning("Failed to parse figure_review for %s: %s", paper_id, exc)
        return None


@app.route("/api/papers/list")
def api_papers_list():
    """Return all known papers with their review state indicators.

    Pulls the set from filesystem (papers/paper*_*/paper_draft.tex)
    which is the source of truth; merges status from claims_review.json
    where present.
    """
    papers_dir = PROJECT_ROOT / 'papers'
    out: list[dict] = []
    if not papers_dir.exists():
        return jsonify({'papers': []})
    for paper_dir in sorted(papers_dir.iterdir()):
        tex = paper_dir / 'paper_draft.tex'
        if not tex.exists():
            continue
        paper_id = paper_dir.name
        cr = _pp_load_claims_review(paper_id)
        fr = _pp_load_figure_review(paper_id)
        entry = {
            'paper_id': paper_id,
            'has_claims_review': cr is not None,
            'has_figure_review': fr is not None,
            'review_date': cr.get('review_date') if cr else None,
            'overall_status': cr.get('overall_status') if cr else None,
        }
        out.append(entry)
    return jsonify({'papers': out})


@app.route("/api/papers/<paper_id>/provenance")
def api_paper_provenance(paper_id: str):
    """Aggregate per-claim 8-layer verdict for a paper.

    Returns the shape the v2 design's `paper-review.js` consumes:
    ``{paper_id, review_date, overall, counts, blocking, nonBlocking,
       layers: [...], claims: {claim_id: {quote, location, findings: [...]}}, ...}``.

    Data sources:
    - `papers/<paper>/claims_review.json` — 8-layer findings (generated
      by the physics-qa:claims-reviewer agent)
    - `papers/<paper>/figures/figure_review_report.json` — FIG layer
      (generated by physics-qa:figure-reviewer)
    - `PAPER_DEPENDENCIES[paper]` — declared formulas/modules/key_claims
    - `PARAMETER_PROVENANCE` — tier + verification dates
    - `CITATION_REGISTRY` — bibkey resolution
    - Live `lean_deps.json` via the cached graph — axiom/theorem status

    404 if paper_draft.tex doesn't exist. 200 with best-effort data if
    claims_review.json is missing (falls back to synthesising from live
    registries + graph state so the tab still works on newer papers).
    """
    papers_dir = PROJECT_ROOT / 'papers'
    paper_dir = papers_dir / paper_id
    tex = paper_dir / 'paper_draft.tex'
    if not tex.exists():
        return jsonify({'error': f'Unknown paper: {paper_id}'}), 404

    cr = _pp_load_claims_review(paper_id)
    fr = _pp_load_figure_review(paper_id)

    # Counts + top-level status
    counts = {'pass': 0, 'warn': 0, 'fail': 0, 'info': 0}
    claims_out: dict[str, dict] = {}
    blocking: list[str] = []
    non_blocking: list[str] = []
    review_date = None
    overall = 'unknown'
    reviewer_notes = None

    if cr:
        review_date = cr.get('review_date')
        overall = cr.get('overall_status', 'unknown')
        reviewer_notes = cr.get('reviewer_notes')
        blocking = list(cr.get('blocking_issues', []))
        non_blocking = list(cr.get('non_blocking_followups', []))

        for section, (layer, quote_key) in _CR_SECTION_MAP.items():
            entries = cr.get(section) or []
            for idx, entry in enumerate(entries):
                cid = _pp_claim_id(section, entry, idx)
                quote = str(entry.get(quote_key, ''))[:200] or section
                finding = _pp_finding_for_entry(layer, entry)
                if cid not in claims_out:
                    claims_out[cid] = {
                        'quote': quote,
                        'location': entry.get('location', ''),
                        'findings': [],
                    }
                claims_out[cid]['findings'].append(finding)
                st = finding['status'].lower()
                if st in counts:
                    counts[st] += 1

    # FIG layer: pull figure_review_report.json
    if fr:
        figs = fr.get('figures') or []
        for fidx, f in enumerate(figs):
            name = f.get('name', f'fig-{fidx}')
            cid = f'figure:{name}'
            status = (f.get('status') or 'INFO').upper()
            note_parts = []
            for sub_key in ('rendering', 'physics', 'style', 'caption_match', 'notes'):
                sub = f.get(sub_key)
                if isinstance(sub, dict):
                    sub_status = sub.get('status', '').upper()
                    issues = sub.get('issues') or []
                    if sub_status and sub_status != 'PASS' and issues:
                        note_parts.append(f"{sub_key}: {'; '.join(issues[:2])}")
                elif sub:
                    note_parts.append(f"{sub_key}: {sub}")
            finding = {
                'layer': 'FIG',
                'status': status if status in ('PASS', 'WARN', 'FAIL', 'INFO') else 'INFO',
                'note': ' · '.join(note_parts) or 'figure review: no notes',
            }
            claims_out.setdefault(cid, {
                'quote': f"Figure: {name}",
                'location': f.get('path', ''),
                'findings': [],
            })['findings'].append(finding)
            st = finding['status'].lower()
            if st in counts:
                counts[st] += 1

    # Fallback title from paper_draft.tex if claims_review missing
    title = ''
    try:
        tex_src = tex.read_text(errors='replace')
        m = re.search(r'\\title\{([^}]+)\}', tex_src)
        if m:
            title = m.group(1).replace('\\\\', ' ').strip()[:200]
    except Exception:
        pass

    return jsonify({
        'paper_id': paper_id,
        'title': title,
        'review_date': review_date,
        'overall_status': overall,
        'reviewer_notes': reviewer_notes,
        'counts': counts,
        'blocking': blocking,
        'non_blocking': non_blocking,
        'layers': [
            {'code': code, 'label': label, 'desc': desc}
            for code, label, desc in _PP_LAYERS_SPEC
        ],
        'claims': claims_out,
        'has_claims_review': cr is not None,
        'has_figure_review': fr is not None,
        'total_claims': len(claims_out),
    })


@app.route("/api/qi")
def api_qi():
    """Return the Stage 14 QI register (Phase 5v Wave 7b).

    Runs `scripts.qi_register.cluster_findings` against the current
    ReviewFinding graph nodes and returns the structured QI items.
    Shape matches what the Process Health dashboard tab consumes.
    """
    from datetime import datetime, timezone
    try:
        from qi_register import load_review_findings, cluster_findings
    except ImportError as exc:
        return jsonify({"error": f"qi_register unavailable: {exc}"}), 500
    findings = load_review_findings()
    items = cluster_findings(findings)
    return jsonify({
        'findings_total': len(findings),
        'items': items,
        'generated': datetime.now(timezone.utc).isoformat(timespec='seconds'),
    })


@app.route("/api/readiness")
def api_readiness():
    """Return per-paper readiness gate data structured for the dashboard.

    Phase 5v Wave 5. Pulls ReadinessGate nodes from the cached graph
    and reshapes into {papers: [{paper, gates: [{gate, priority, state,
    evidence, blockers, notes, last_evaluated}]}]}. The heatmap renders
    from this payload via safe-DOM construction (see readiness_tab.html).
    """
    graph = get_cached_graph()
    gates = [n for n in graph.get('nodes', []) if n['type'] == 'ReadinessGate']
    if not gates:
        return jsonify({"papers": [], "last_evaluated": None,
                        "error": "no ReadinessGate nodes"})

    from collections import defaultdict
    by_paper: dict[str, list[dict]] = defaultdict(list)
    last_evaluated = None
    for g in gates:
        m = g.get('meta', {})
        paper = m.get('paper', '?')
        by_paper[paper].append({
            'gate': m.get('gate'),
            'priority': m.get('priority'),
            'state': m.get('state'),
            'evidence': m.get('evidence', []),
            'blockers': m.get('blockers', []),
            'notes': m.get('notes', ''),
            'last_evaluated': m.get('last_evaluated', ''),
        })
        if m.get('last_evaluated'):
            last_evaluated = m['last_evaluated']

    papers = [
        {'paper': paper, 'gates': sorted(
            by_paper[paper], key=lambda g: (g['priority'] or 99, g['gate'] or ''))}
        for paper in sorted(by_paper.keys())
    ]
    return jsonify({
        'papers': papers,
        'last_evaluated': last_evaluated,
        'gate_count': sum(len(p['gates']) for p in papers),
    })


# ════════════════════════════════════════════════════════════════════
# CLI
# ════════════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(description="SK-EFT Provenance Command Center")
    parser.add_argument("--port", type=int, default=8050, help="Port (default: 8050)")
    parser.add_argument("--no-browser", action="store_true", help="Don't auto-open browser")
    parser.add_argument("--no-pg-sync", action="store_true",
                        help="Disable background PG+AGE sync on graph rebuilds "
                             "(useful if Postgres is down locally).")
    parser.add_argument("--no-prewarm", action="store_true",
                        help="Skip building the graph at server start. The first "
                             "request will pay the rebuild cost instead.")
    parser.add_argument("--write", action="store_true",
                        help="Write current verification state to provenance.py and exit")
    args = parser.parse_args()

    if args.write:
        print("Write mode: updating provenance.py with verification state...")
        # TODO: implement file rewriting
        return

    app.config['PG_SYNC_ENABLED'] = not args.no_pg_sync

    # Phase 5v Wave 9f — if SK_EFT_GRAPH_SOURCE=pg, verify connectivity
    # NOW, not on the first query. Silent fallback hid real issues in
    # earlier phases; fail loud instead.
    src = _graph_source()
    if src == 'pg':
        try:
            import psycopg  # type: ignore
            with psycopg.connect(
                "host=localhost port=5433 dbname=sk_eft_provenance "
                "user=sk_eft password=sk_eft_local",
                connect_timeout=3,
            ) as _conn, _conn.cursor() as _cur:
                _cur.execute("LOAD 'age'")
                _cur.execute("SET search_path = ag_catalog, '$user', public")
                _cur.execute("SELECT * FROM cypher('sk_eft', $$ MATCH (n) RETURN count(n) $$) AS (c agtype)")
                pg_count = int(str(_cur.fetchone()[0]))
            print(f"\n  [PG] SK_EFT_GRAPH_SOURCE=pg — AGE reachable, {pg_count} nodes in sk_eft graph.")
            if pg_count == 0:
                print("  [PG] Graph is empty. Run `uv run python scripts/sync_graph_to_pg.py` to populate.\n")
        except Exception as exc:
            print(f"\n  [PG] SK_EFT_GRAPH_SOURCE=pg but connectivity check FAILED: {exc}")
            print("  [PG] Dashboard will exit. Start postgres (port 5433, sk_eft_provenance DB)")
            print("  [PG] or unset SK_EFT_GRAPH_SOURCE to run in json mode.\n")
            sys.exit(2)
    elif src != 'json':
        print(f"\n  [!] Unknown SK_EFT_GRAPH_SOURCE={src!r} (expected 'json' or 'pg'); defaulting to json.\n")

    # Root-cause fix for the "reload hangs" behavior users saw on cold
    # starts: the dashboard must never shell out to `lake`. If Lean
    # sources changed since the last extraction, warn in the console
    # and display a "stale" indicator in the UI. Users refresh via
    # `uv run python scripts/extract_lean_deps.py` or by POSTing to
    # /api/graph/refresh_lean_deps.
    if _suppress_lake_refresh():
        print("\n  [!] lean_deps.json is stale (Lean sources changed since last extraction).")
        print("  [!] Dashboard will serve cached data. To refresh, stop the dashboard and run:")
        print("  [!]     uv run python scripts/extract_lean_deps.py")
        print("  [!] (or POST /api/graph/refresh_lean_deps to refresh in-place, blocks ~1-2 min)\n")

    import webbrowser

    url = f"http://localhost:{args.port}"
    if not args.no_browser:
        threading.Timer(1.0, lambda: webbrowser.open(url)).start()

    # Warm the graph cache in a background thread so the first click
    # doesn't eat the ~1.5s build cost. Because lake is suppressed,
    # prewarm completes in seconds on cached lean_deps.
    if not args.no_prewarm:
        def _prewarm():
            try:
                g = get_cached_graph(sync_pg=not args.no_pg_sync)
                logger.info(
                    "Graph cache prewarmed: %d nodes, %d edges",
                    g['meta']['node_count'], g['meta']['edge_count'],
                )
            except Exception as exc:
                logger.warning("Graph prewarm failed: %s", exc)
        threading.Thread(target=_prewarm, daemon=True, name="graph-prewarm").start()

    print(f"\n  SK-EFT Provenance Command Center")
    print(f"  Running at {url}")
    print(f"  Press Ctrl+C to stop\n")

    # threaded=True is the Flask 2.x default but pass explicitly so the
    # server's concurrency behavior doesn't change if defaults do.
    # Without it, a slow endpoint (e.g. the one-time graph rebuild)
    # blocks every other endpoint behind it.
    app.run(host="localhost", port=args.port, debug=False, threaded=True)


if __name__ == "__main__":
    main()
