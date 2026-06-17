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

# Datastar SDK glue (Phase 5v Wave 9h). See docs/references/Datastar_Dashboard_Reference.md
from datastar_helpers import SSE, is_datastar_request, read_signals, sse_response, esc

app = Flask(__name__, template_folder=str(Path(__file__).parent / "templates"))
app.config['TEMPLATES_AUTO_RELOAD'] = True
app.jinja_env.auto_reload = True

# Expose shared constants to Jinja templates (GATE_DEFS is defined below
# the routes; wire it at registration time via a context_processor so the
# forward reference resolves cleanly).
@app.context_processor
def _inject_readiness_constants():
    return {"GATE_DEFS": GATE_DEFS, "PP_PAPERS_LIST": _pp_list_papers}


def _pp_list_papers() -> list[dict]:
    """Walk papers/paper*_*/ and return the list the provenance dropdown
    needs. Called from Jinja via PP_PAPERS_LIST() — inlined at render time
    so the tab needs no separate /api/papers/list round-trip."""
    papers_dir = PROJECT_ROOT / 'papers'
    out: list[dict] = []
    if not papers_dir.exists():
        return out
    for paper_dir in sorted(papers_dir.iterdir()):
        tex = paper_dir / 'paper_draft.tex'
        if not tex.exists():
            continue
        paper_id = paper_dir.name
        cr = _pp_load_claims_review(paper_id)
        out.append({
            'paper_id': paper_id,
            'has_claims_review': cr is not None,
            'overall_status': cr.get('overall_status') if cr else None,
        })
    return out

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


def _invalidate_graph_cache() -> None:
    """Force the next ``get_cached_graph`` call to rebuild.

    Phase 5v Wave 10c — used by verification endpoints so a confirm /
    reject ripples to dependent claims on the next request without
    waiting for a file-mtime change to trip the fingerprint.
    """
    with _GRAPH_CACHE_LOCK:
        _GRAPH_CACHE['graph'] = None
        _GRAPH_CACHE['fingerprint'] = None


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
        PROJECT_ROOT / "scripts" / "verification_state.py",
        PROJECT_ROOT / "scripts" / "last_modified.py",
        PROJECT_ROOT / "docs" / "counts.json",
        # Wave 10c — any verification event flips the cache so next
        # request re-applies the change-bus + freshness propagation.
        PROJECT_ROOT / "docs" / "verification_log.jsonl",
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
    # Wave 10g — retire Paper Contributions tab. ``?tab=papers`` redirects
    # to ``?tab=paper`` (Paper Provenance), preserving any ``paper=<id>``
    # selector. Old bookmarks keep working.
    if request.args.get('tab') == 'papers':
        from flask import redirect
        paper_arg = request.args.get('paper', '')
        target = '/?tab=paper' + (f'&paper={paper_arg}' if paper_arg else '')
        return redirect(target, code=302)

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
    # Phase 5v Wave 9g: the Paper Provenance tab uses `?paper=<paper_id>`
    # (string). This Parameters-tab handler only wants the numeric paper
    # number; guard against str vs int collision so a non-numeric value
    # (from the other tab) doesn't 500 out the whole dashboard.
    if paper_filter != 'all' and tab == 'parameters':
        try:
            paper_num = int(paper_filter)
            filtered_params = [p for p in filtered_params if paper_num in p['papers']]
        except ValueError:
            pass  # Other tabs own this param; ignore here.

    # Sort: conflicts first, then unverified, then LLM-only, then verified
    status_order = {'unverified': 0, 'llm_verified': 1, 'human_verified': 2}
    filtered_params.sort(key=lambda p: (
        0 if p['has_conflict'] else 1,
        status_order.get(p['status'], 3),
        p['key']
    ))

    # Phase 6i Wave 7.5: load bundle summary lazily (only when the
    # Bundles tab is rendered) to keep other-tab requests fast.
    bundles_summary = None
    if tab == 'bundles':
        try:
            from datastar_bundles import load_bundles_summary
            bundles_summary = load_bundles_summary()
        except Exception as exc:
            import traceback
            traceback.print_exc()
            bundles_summary = {
                'total_bundles': 0,
                'bundles': [],
                'cross_bundle_count': 0,
                'cross_bundle_clusters': [],
                'submission_events': [],
                'error': str(exc),
            }

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
                           bundles_summary=bundles_summary,
                           format_value=_format_value)


# ─────────────────────────────────────────────────────────────────
# Phase 6i Wave 7.5 — Bundles tab supporting endpoints
# ─────────────────────────────────────────────────────────────────

@app.route("/api/bundles/<bundle>/review")
def bundle_review_doc(bundle):
    """Serve a per-bundle review document (read-only). Returns 404 if
    no review doc exists yet."""
    from flask import abort, send_file
    from pathlib import Path
    PROJECT = Path(__file__).resolve().parent.parent
    REVIEWS = PROJECT / "papers" / "AutomatedReviews"
    if not REVIEWS.exists():
        abort(404)
    candidates = sorted(
        d for d in REVIEWS.iterdir()
        if d.is_dir() and d.name.endswith("-bundle-stage13")
    )
    if not candidates:
        abort(404)
    latest = candidates[-1]
    doc = latest / f"{bundle}.md"
    if not doc.exists():
        abort(404)
    return send_file(doc, mimetype="text/markdown")


@app.route("/api/bundles/<bundle>/submission_event", methods=["POST"])
def bundle_submission_event(bundle):
    """Record a bundle submission state event (drafted, stage13_pass,
    submitted, accepted, published). Append-only log."""
    from datastar_bundles import append_submission_event
    payload = request.get_json(silent=True) or {}
    action = payload.get("action", "")
    evidence = payload.get("evidence", "")
    valid_actions = {"drafted", "stage13_pass", "submitted", "accepted",
                     "published"}
    if action not in valid_actions:
        return jsonify({
            "ok": False,
            "error": f"action must be one of {sorted(valid_actions)}",
        }), 400
    event = append_submission_event(bundle, action, evidence)
    return jsonify({"ok": True, "event": event})


@app.route("/bundles/submission_event", methods=["POST"])
def bundle_submission_event_form():
    """Form-encoded sibling of /api/bundles/<b>/submission_event for the Bundles
    tab's inline UI. Records the event, then redirects back to the tab (so the log
    re-renders) with a success/error flash in the query string. Plain form POST —
    no client-side JS — so it can never break the way a two-way Datastar binding
    can (see memory `feedback-test-client-never-runs-js`)."""
    from flask import redirect
    from datastar_bundles import append_submission_event, _TIER_OF
    bundle = (request.form.get("bundle") or "").strip()
    action = (request.form.get("action") or "").strip()
    evidence = (request.form.get("evidence") or "").strip()
    valid_actions = {"drafted", "stage13_pass", "submitted", "accepted", "published"}
    if bundle not in _TIER_OF or action not in valid_actions:
        return redirect("/?tab=bundles&submit_error=1")
    append_submission_event(bundle, action, evidence)
    return redirect(f"/?tab=bundles&submitted={bundle}")


@app.route("/verify", methods=["POST"])
def verify_param():
    """Legacy Parameters-tab endpoint: mark a parameter human-verified.

    Returns an HTML fragment consumed by ``verifyParam`` in
    ``dashboard.html`` (vanilla ``fetch`` + ``safeSetHTML`` — HTMX was
    removed at an earlier checkpoint, and a Datastar port of this tab
    is a deferred Wave 9h-followup item; the four newer tabs
    (readiness/qi/chains/paper-provenance) are already on Datastar).

    Wave 10c: every action also lands on the cross-tab change-bus via
    ``verification_state.record_event``. The verification timestamp
    propagates to dependent Sentence / ProseClaim nodes on the next
    graph rebuild, surfacing as a stale (purple-stripe) indicator on
    Paper Provenance.
    """
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

    # Wave 10c — change-bus event. Failure to record a verification
    # event must not break the in-memory PARAMETER_PROVENANCE update
    # that the user just applied; log + continue.
    try:
        from verification_state import record_event
        actor = request.form.get('actor') or 'user:dashboard'
        record_event(
            artifact_type='Parameter',
            artifact_id=key,
            action=action,
            actor=actor,
            notes=notes or None,
        )
        _invalidate_graph_cache()
    except Exception as exc:  # noqa: BLE001 — defensive on dashboard request path
        logger.warning("verification_state.record_event failed: %s", exc)

    # Return updated card fragment via HTMX
    return f'''<span class="status-badge {status_class}">{status_text}</span>
    <small class="verify-date">{now}</small>'''


# ════════════════════════════════════════════════════════════════════
# Cross-tab verification change-bus (Phase 5v Wave 10c)
# ════════════════════════════════════════════════════════════════════
#
# /verify (above) is the legacy Parameters-tab vanilla-fetch endpoint
# (will become Datastar in a future Wave 9h-followup port). The
# generic /api/verification/event endpoint is the entry point for any
# Datastar tab (current Paper Provenance, future Citations + axiom
# eliminability, …) that wants to bump an artifact's last_modified
# through the change-bus. Returns JSON, consumable both from Datastar
# `@post(...)` actions and vanilla fetch.
#
# Both endpoints record into the same docs/verification_log.jsonl via
# verification_state.record_event, both invalidate the graph cache so
# the next /api/graph* request observes the bumped timestamp.

@app.route("/api/verification/event", methods=["POST"])
def api_verification_event():
    """Record one cross-tab verification event.

    Accepts JSON or form-encoded body with fields:
      artifact_type, artifact_id, action, actor, notes (optional),
      node_id (optional override)

    Returns the recorded event with normalized timestamp + auto-derived
    node_id (when not supplied).
    """
    payload = request.get_json(silent=True) or request.form
    artifact_type = payload.get('artifact_type')
    artifact_id = payload.get('artifact_id')
    action = payload.get('action')
    actor = payload.get('actor') or 'user:dashboard'
    notes = payload.get('notes') or None
    node_id = payload.get('node_id') or None
    # Wave 10 cross-tab provenance: when the event was triggered from a
    # sentence's per-link verify UI, the client passes ``triggered_by``
    # carrying the source sentence_id. Null for Parameters-tab events.
    triggered_by = payload.get('triggered_by') or None

    if not (artifact_type and artifact_id and action):
        return jsonify({
            "error": "missing required field(s); expected "
                     "artifact_type, artifact_id, action"
        }), 400

    try:
        from verification_state import record_event
        ev = record_event(
            artifact_type=artifact_type,
            artifact_id=artifact_id,
            action=action,
            actor=actor,
            notes=notes,
            node_id=node_id,
            triggered_by=triggered_by,
        )
    except ValueError as exc:
        return jsonify({"error": str(exc)}), 400
    except Exception as exc:  # noqa: BLE001
        logger.exception("record_event unexpected failure")
        return jsonify({"error": f"unexpected: {exc}"}), 500

    _invalidate_graph_cache()
    return jsonify({"event": ev}), 200


@app.route("/api/verification/state", methods=["GET"])
def api_verification_state():
    """Return the latest verification event per node (or full history).

    Query params:
      node_id          — return only events for this node id
      artifact_type    — filter by artifact type
      artifact_id      — filter by source-of-truth key
      latest_only=1    — return one event per node (most recent)
      limit=N          — cap the event list at N (most recent first)
    """
    try:
        from verification_state import read_events, latest_per_node
    except ImportError as exc:
        return jsonify({"error": f"verification_state not importable: {exc}"}), 500

    node_id = request.args.get('node_id')
    artifact_type = request.args.get('artifact_type')
    artifact_id = request.args.get('artifact_id')
    latest_only = request.args.get('latest_only') in ('1', 'true', 'yes')

    try:
        limit = int(request.args.get('limit', '0'))
    except ValueError:
        limit = 0

    def _matches(ev: dict) -> bool:
        if node_id and ev.get('node_id') != node_id:
            return False
        if artifact_type and ev.get('artifact_type') != artifact_type:
            return False
        if artifact_id and ev.get('artifact_id') != artifact_id:
            return False
        return True

    if latest_only:
        items = [ev for ev in latest_per_node().values() if _matches(ev)]
        items.sort(key=lambda e: e.get('timestamp', ''), reverse=True)
    else:
        items = [ev for ev in read_events() if _matches(ev)]
        items.sort(key=lambda e: e.get('timestamp', ''), reverse=True)

    if limit > 0:
        items = items[:limit]

    return jsonify({"events": items, "count": len(items)})


# NOTE: the former POST /save ("Save All") route was removed. It was a no-op that
# claimed "{N} parameters updated" and told the user to run `--write` to persist,
# but it wrote nothing to disk (and `--write` is itself an unimplemented stub).
# Verification actions already persist immediately, per-action, via
# /verify -> verification_state.record_event (docs/verification_log.jsonl), so
# there is nothing to batch-save. The Parameters-tab save-bar now states this.


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


CHAIN_TITLES = {
    'hawking':          'Dissipative Hawking Radiation',
    'graphene':         'Graphene Dirac Fluid (2+1D)',
    'generations':      'Generation Constraint + ℤ₁₆ Convergence',
    'gauge-emergence':  'Gauge Emergence & Drinfeld Center',
    'chirality-wall':   'Chirality Wall (GS / TPF / GT)',
    'fracton':          'Fracton Gravity & Hydrodynamics',
    'vestigial':        'Vestigial Gravity (Dim. Reduction)',
    'dark-sector':      'Dark Sector (SFDM / fracton-DM / FG / hidden sectors)',
    'gate-engineering': 'Geometric Quantum Gate (Fermi-Hubbard Dimer)',
}
CHAIN_VERDICT_LABELS = {
    'solid': 'Machine-verified',
    'solid-gaps': 'Structural, known gaps',
    'mixed': 'Mixed results',
    'contested': 'Contested gaps',
    'in-progress': 'Work in progress',
}


def _chain_list_build() -> dict:
    """Compute chain list + per-chain summary once so all renderers share it."""
    from collections import Counter
    graph = get_cached_graph()
    chain_counter: Counter = Counter()
    unclassified = 0
    for n in graph['nodes']:
        ids = n.get('meta', {}).get('chain_ids')
        if not ids:
            if n['type'] in (
                'LeanTheorem', 'LeanAxiom', 'LeanDef',
                'LeanStructure', 'LeanInductive', 'LeanInstance',
            ):
                unclassified += 1
            continue
        for cid in ids:
            chain_counter[cid] += 1
    chains = []
    for cid, count in sorted(chain_counter.items(), key=lambda x: -x[1]):
        chain_ns = _chain_nodes(graph, cid)
        thm_total = sum(1 for n in chain_ns if n['type'] == 'LeanTheorem')
        thm_verified = sum(1 for n in chain_ns if n['type'] == 'LeanTheorem'
                           and n.get('verification') == 'verified')
        ax_total = sum(1 for n in chain_ns if n['type'] == 'LeanAxiom')
        ms_count = sum(1 for n in chain_ns if n.get('meta', {}).get('is_milestone'))
        placeholders = sum(
            1 for n in chain_ns
            if n.get('meta', {}).get('method') == 'manual'
            and any(t in (n.get('label', '').lower()) for t in ('placeholder', 'stub'))
        )
        if thm_verified == thm_total and placeholders == 0:
            verdict = 'solid'
        elif placeholders:
            verdict = 'solid-gaps'
        else:
            verdict = 'mixed'
        chains.append({
            'chain_id': cid, 'node_count': count, 'verdict': verdict,
            'thm_total': thm_total, 'thm_verified': thm_verified,
            'ax_total': ax_total, 'ms_count': ms_count,
        })
    return {'chains': chains, 'unclassified_lean_nodes': unclassified,
            'built_at': _GRAPH_CACHE['built_at']}


def _chain_milestone_svg(chain_id: str, W: int = 900, H: int = 380,
                         margin: int = 50) -> str:
    """Server-side port of layoutDAG + SVG render from the old chains_tab JS.
    Produces a deterministic topo-layered milestone DAG — no D3, no client
    geometry. Edges are smooth quadratic curves; hop_count > 1 emits an
    inline label. Node click still bubbles up to the document for deep-link
    navigation."""
    data = _chain_milestones_data(chain_id) or {}
    nodes = data.get('nodes', [])
    edges = data.get('edges', [])
    if not nodes:
        return ('<div class="rs-empty">No milestones registered for this chain yet. '
                'Add short names to CHAIN_MILESTONES in src/core/constants.py.</div>')

    # --- Topo-layered layout, ported from scripts/templates/partials/chains_tab.html::layoutDAG
    outgoing: dict[str, list[str]] = {n['id']: [] for n in nodes}
    incoming: dict[str, list[str]] = {n['id']: [] for n in nodes}
    by_id = {n['id']: n for n in nodes}
    for e in edges:
        if e['from'] in by_id and e['to'] in by_id:
            outgoing[e['from']].append(e['to'])
            incoming[e['to']].append(e['from'])
    layer: dict[str, int] = {}

    def visit(nid: str, depth: int) -> None:
        if nid in layer and layer[nid] >= depth:
            return
        layer[nid] = depth
        for s in outgoing[nid]:
            visit(s, depth + 1)

    sources = [n for n in nodes if not incoming[n['id']]]
    if not sources:
        for n in nodes:
            layer[n['id']] = 0
    else:
        for s in sources:
            visit(s['id'], 0)
        for n in nodes:
            layer.setdefault(n['id'], 0)
    max_layer = max(layer.values()) if layer else 0
    by_layer: dict[int, list[dict]] = {i: [] for i in range(max_layer + 1)}
    for n in nodes:
        by_layer[layer[n['id']]].append(n)
    for ln in by_layer.values():
        ln.sort(key=lambda n: (
            n.get('milestone_order') if n.get('milestone_order') is not None else 99,
            n.get('label', ''),
        ))

    col_count = max_layer + 1
    col_w = (W - margin * 2) / max(col_count, 1)
    positions: dict[str, tuple[float, float]] = {}
    for L in range(max_layer + 1):
        layer_ns = by_layer[L]
        row_h = (H - margin * 2) / max(len(layer_ns), 1)
        for i, n in enumerate(layer_ns):
            positions[n['id']] = (
                margin + col_w * L + col_w / 2,
                margin + row_h * i + row_h / 2,
            )

    # --- SVG rendering (edges first so nodes layer on top)
    svg_parts = [f'<svg class="rs-dag-svg" viewBox="0 0 {W} {H}">']
    for e in edges:
        if e['from'] not in positions or e['to'] not in positions:
            continue
        p1x, p1y = positions[e['from']]
        p2x, p2y = positions[e['to']]
        mid_x = (p1x + p2x) / 2
        mid_y = (p1y + p2y) / 2
        d = f'M {p1x} {p1y} Q {mid_x} {p1y}, {mid_x} {mid_y} T {p2x} {p2y}'
        dash = ' stroke-dasharray="4 3"' if e.get('confidence') == 'conjectured' else ''
        svg_parts.append(f'<path class="rs-dag-edge" d="{d}"{dash}/>')
        if (e.get('hop_count') or 0) > 1:
            svg_parts.append(
                f'<text class="rs-dag-edge-hop-label" x="{mid_x}" y="{mid_y - 6}">'
                f'{e["hop_count"]}↷</text>'
            )
    for n in nodes:
        if n['id'] not in positions:
            continue
        px, py = positions[n['id']]
        is_axiom = n.get('node_shape') == 'diamond' or n.get('is_external_axiom')
        fill = '#fde68a' if is_axiom else '#86c9a8'
        stroke = '#b45309' if is_axiom else '#166534'
        label = (n.get('label') or n['id'].split(':')[-1])[:22]
        label_w = max(len(label) * 6.6 + 16, 70)
        # Click navigates to graph tab traced at this node.
        nav = f"window.location.href='?tab=graph#trace=' + encodeURIComponent('{esc(n['id'])}')"
        svg_parts.append(
            f'<g transform="translate({px} {py})" style="cursor:pointer" '
            f'data-on:click="{esc(nav)}" data-node-id="{esc(n["id"])}">'
            f'<rect class="rs-dag-node-rect" x="{-label_w/2}" y="-14" '
            f'width="{label_w}" height="28" rx="3" fill="{fill}" stroke="{stroke}" '
            f'fill-opacity="0.22"/>'
            f'<text class="rs-dag-node-label" y="4">{esc(label)}</text>'
            f'</g>'
        )
    svg_parts.append('</svg>')
    return ''.join(svg_parts)


def _chain_card_html(entry: dict, expanded_chain: str) -> str:
    cid = entry['chain_id']
    expanded = (expanded_chain == cid)
    title = CHAIN_TITLES.get(cid, cid)
    verdict = entry.get('verdict', 'mixed')
    verdict_label = CHAIN_VERDICT_LABELS.get(verdict, verdict)
    toggle_expr = f"$expandedChain = $expandedChain === '{esc(cid)}' ? '' : '{esc(cid)}'; @get('/api/chain/list')"

    strip = (
        f'<div class="rs-chain-strip{" expanded" if expanded else ""}" '
        f'data-on:click="{esc(toggle_expr)}">'
        f'<span class="rs-verdict-dot {esc(verdict)}"></span>'
        f'<div class="rs-chain-name">{esc(title)}</div>'
        f'<div class="rs-chain-stats">'
        f'<span><span class="val">{entry["thm_verified"]}</span>/'
        f'<span class="val">{entry["thm_total"]}</span> thms</span>'
        f'<span><span class="val">{entry["ax_total"]}</span> ax</span>'
        f'<span><span class="val">{entry["ms_count"]}</span> milestones</span>'
        f'</div>'
        f'<span class="rs-chain-verdict">{esc(verdict_label)}</span>'
        f'<span class="rs-chain-expand">›</span>'
        f'</div>'
    )
    body_inner = _chain_milestone_svg(cid) if expanded else ''
    # When expanded, also show a link to the full L2 subgraph.
    body_actions = ''
    if expanded:
        l2_nav = f"window.open('?tab=graph#chain=' + encodeURIComponent('{esc(cid)}'),'_self')"
        body_actions = (
            '<div class="rs-chain-actions">'
            f'<button data-on:click="{esc(l2_nav)}">Open full subgraph (L2) →</button>'
            '</div>'
        )
    body = (
        f'<div class="rs-chain-body{" expanded" if expanded else ""}">'
        + body_inner + body_actions +
        '</div>'
    )
    return f'<div class="rs-chain-card" data-chain-id="{esc(cid)}">{strip}{body}</div>'


def _chain_list_sse_events(data: dict, signals: dict):
    expanded = signals.get('expandedChain') or ''
    chains = data.get('chains', [])
    if not chains:
        html_body = ('<div class="rs-empty">No chains discovered yet. '
                     'Add entries to MODULE_CHAIN_MAP in src/core/constants.py '
                     'to register chains.</div>')
    else:
        html_body = ''.join(_chain_card_html(c, expanded) for c in chains)
    yield SSE.patch_elements(f'<div id="rs-chains-list">{html_body}</div>')
    unclass = data.get('unclassified_lean_nodes', 0)
    unclass_html = (f'{unclass} Lean decls unclassified' if unclass else '')
    yield SSE.patch_elements(f'<div class="rs-unclassified" id="rs-unclassified">{esc(unclass_html)}</div>')


@app.route("/api/chain/list")
def api_chain_list():
    """Chain taxonomy + per-chain summary (Wave 9d; Datastar port Wave 9h).

    JSON shape unchanged for backward compat (omits verdict/counts only in
    the JSON path to keep callers stable; SSE path computes them inline).
    """
    data = _chain_list_build()
    if is_datastar_request():
        signals = read_signals()
        return sse_response(lambda: _chain_list_sse_events(data, signals))
    # Legacy JSON shape — kept identical to the Wave 9d contract.
    chains_legacy = [
        {'chain_id': c['chain_id'], 'node_count': c['node_count']}
        for c in data['chains']
    ]
    return jsonify({
        'chains': chains_legacy,
        'unclassified_lean_nodes': data['unclassified_lean_nodes'],
        'built_at': data['built_at'],
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


def _chain_milestones_data(chain_id: str) -> dict | None:
    """Compute milestone nodes + edges for a chain. Extracted so both the
    JSON endpoint and the SSE SVG renderer consume the same shape without
    re-entering the Flask request context."""
    graph = get_cached_graph()
    chain_ns = _chain_nodes(graph, chain_id)
    if not chain_ns:
        return None

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

    return {
        'chain_id': chain_id,
        'nodes': nodes_out,
        'edges': edges,
        'built_at': _GRAPH_CACHE['built_at'],
    }


@app.route("/api/chain/<chain_id>/milestones")
def api_chain_milestones(chain_id: str):
    """L1 — milestone DAG data. Returned as JSON; SSE consumers use
    _chain_milestones_data directly to avoid re-entering the request path."""
    data = _chain_milestones_data(chain_id)
    if data is None:
        return jsonify({'error': f'Unknown chain: {chain_id}'}), 404
    return jsonify(data)


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
# skeft-qa:claims-reviewer agent) + `papers/<paper>/figures/
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


# ── Wave 10c — staleness check for paper-provenance findings ──
#
# Maps `(layer, claim_entry)` → KG node id, then compares the node's
# verification timestamp from docs/verification_log.jsonl to the paper's
# `review_date`. If a verification landed AFTER the review was generated,
# the claim is "stale" — the prose-level surface needs a re-review.
# Section keys (e.g. parameter_provenance, citation_integrity) embed the
# source-of-truth artifact key by convention from `_pp_claim_id`.

def _pp_review_iso(review_date: str | None) -> str:
    """Normalize a claims_review.json `review_date` to a sortable ISO-Z
    timestamp. Returns '' if missing or unparseable."""
    if not review_date:
        return ''
    s = str(review_date).strip()
    # Plain date → start of day UTC.
    if re.fullmatch(r'\d{4}-\d{2}-\d{2}', s):
        return f"{s}T00:00:00Z"
    if s.endswith('+00:00'):
        return s[:-6] + 'Z'
    if 'T' in s and not s.endswith('Z'):
        return s.split('+')[0].rstrip() + ('Z' if 'Z' not in s else '')
    return s


def _pp_artifact_id_for_section(section: str, entry: dict) -> tuple[str, str] | None:
    """Return (artifact_type, source-of-truth key) for a claims_review entry,
    or None if the entry doesn't reference a verifiable artifact.

    Mirrors the `_pp_claim_id` field-priority so the (layer, key) we use
    for staleness lookup matches the cid format the dashboard renders.
    """
    if section == 'parameter_provenance':
        key = entry.get('key') or entry.get('name')
        return ('Parameter', str(key)) if key else None
    if section == 'citation_integrity':
        key = entry.get('bibkey') or entry.get('key')
        return ('Citation', str(key)) if key else None
    if section == 'theorem_status':
        # theorem entries carry 'name' (full Lean decl)
        key = entry.get('name') or entry.get('theorem')
        return ('LeanTheorem', str(key)) if key else None
    if section == 'axiom_risk':
        key = entry.get('axiom') or entry.get('name')
        return ('LeanAxiom', str(key)) if key else None
    return None


def _pp_compute_stale_findings(
    cr_data: dict | None,
    claims_out: dict,
) -> tuple[int, dict[str, str]]:
    """Mark findings whose underlying artifact has been verified AFTER the
    claims_review was generated. Returns (count_marked, per-cid event-actor map).

    Mutates claims_out in place: each affected `finding` gets
    `finding['stale'] = True` plus `finding['stale_since']` (timestamp) and
    `finding['stale_actor']` (who verified). The caller bubbles up a
    `claim['is_stale']` flag in `_pp_build_data` after this returns.
    """
    if not cr_data:
        return (0, {})
    review_iso = _pp_review_iso(cr_data.get('review_date'))
    if not review_iso:
        return (0, {})

    try:
        from verification_state import latest_per_node, node_id_for
    except ImportError:
        return (0, {})

    latest = latest_per_node()
    if not latest:
        return (0, {})

    n_marked = 0
    cid_to_actor: dict[str, str] = {}

    for section, (layer, _quote_key) in _CR_SECTION_MAP.items():
        entries = cr_data.get(section) or []
        for idx, entry in enumerate(entries):
            cid = _pp_claim_id(section, entry, idx)
            claim = claims_out.get(cid)
            if not claim:
                continue
            mapping = _pp_artifact_id_for_section(section, entry)
            if not mapping:
                continue
            artifact_type, key = mapping
            nid = node_id_for(artifact_type, key)
            if not nid:
                continue
            ev = latest.get(nid)
            if not ev:
                continue
            ev_iso = ev.get('timestamp', '')
            if ev_iso <= review_iso:
                continue
            # Mark every finding on this claim that matches the layer.
            for finding in claim.get('findings', []):
                if finding.get('layer') != layer:
                    continue
                finding['stale'] = True
                finding['stale_since'] = ev_iso
                finding['stale_actor'] = ev.get('actor', '')
                finding['stale_action'] = ev.get('action', '')
                n_marked += 1
            cid_to_actor[cid] = ev.get('actor', '')

    return (n_marked, cid_to_actor)


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


# ── Wave 10d — v2 sentence-keyed data layer ──
#
# When ``papers/<paper>/claims_review.json`` carries a ``sentences[]``
# list (v2 schema), the Paper Provenance tab switches to the sentence-
# level UI: 3-column layout, per-sentence state machine, per-link
# verification, audit log pane. v1 schemas (the curated 8-layer dossier)
# continue to work as before.
#
# State storage (Wave 10b CLI is the sole writer):
#   prose_state.json — human ratification state per sentence
#   audit_log.jsonl  — append-only event stream

def _pp_is_v2_schema(cr: dict | None) -> bool:
    return bool(cr) and isinstance(cr.get('sentences'), list)


def _pp_load_prose_state(paper_id: str) -> dict:
    """Load `papers/<paper>/prose_state.json` if present, else empty.

    Schema (managed by sentence_state.py):
      {"version": 1, "paper": <id>,
       "sentences": {<sentence_id>: {"human_state", "human_ratified_at",
                                     "human_ratified_by", "human_notes"}}}
    """
    path = PROJECT_ROOT / 'papers' / paper_id / 'prose_state.json'
    if not path.exists():
        return {'version': 1, 'paper': paper_id, 'sentences': {}}
    try:
        data = json.loads(path.read_text())
    except Exception as exc:
        logger.warning("Failed to parse prose_state for %s: %s", paper_id, exc)
        return {'version': 1, 'paper': paper_id, 'sentences': {}}
    data.setdefault('sentences', {})
    return data


def _pp_load_audit_log(paper_id: str, *, limit: int = 0) -> list[dict]:
    """Load `papers/<paper>/audit_log.jsonl` event stream in file order.

    ``limit`` — if > 0, return only the most recent N events.
    Skips malformed lines with a warning rather than failing the whole load.
    """
    path = PROJECT_ROOT / 'papers' / paper_id / 'audit_log.jsonl'
    if not path.exists():
        return []
    events: list[dict] = []
    try:
        with open(path, 'r', encoding='utf-8') as f:
            for lineno, raw in enumerate(f, 1):
                line = raw.rstrip('\n')
                if not line.strip():
                    continue
                try:
                    events.append(json.loads(line))
                except json.JSONDecodeError as exc:
                    logger.warning(
                        "audit_log %s line %d malformed: %s", paper_id, lineno, exc
                    )
    except Exception as exc:
        logger.warning("Failed to read audit_log for %s: %s", paper_id, exc)
        return []
    if limit > 0 and len(events) > limit:
        events = events[-limit:]
    return events


def _pp_load_claim_clusters() -> dict:
    """Load ``papers/claim_clusters.json`` produced by cluster_detect.py.

    Wave 10f. Returns ``{}`` if the file is missing or malformed.
    """
    path = PROJECT_ROOT / 'papers' / 'claim_clusters.json'
    if not path.exists():
        return {}
    try:
        return json.loads(path.read_text())
    except Exception as exc:
        logger.warning("Failed to load claim_clusters.json: %s", exc)
        return {}


def _pp_clusters_by_sentence() -> dict[str, list[dict]]:
    """Index ClaimCluster records by member sentence id.

    Returns ``{sentence_id: [{cluster_id, match_kind, confidence,
    other_members, member_papers, label}, ...]}``. Multiple clusters per
    sentence are possible (e.g. exact + normalized hits collapse to one
    sentence appearing in two cluster types).
    """
    data = _pp_load_claim_clusters()
    out: dict[str, list[dict]] = {}
    for c in data.get('clusters') or []:
        cid = c.get('id')
        members = c.get('members') or []
        if not cid or len(members) < 2:
            continue
        for sid in members:
            entry = {
                'cluster_id': cid,
                'match_kind': c.get('match_kind'),
                'confidence': c.get('confidence'),
                'other_members': [m for m in members if m != sid],
                'member_papers': c.get('member_papers') or [],
                'label': c.get('label'),
                'human_confirmed_at': c.get('human_confirmed_at'),
            }
            out.setdefault(sid, []).append(entry)
    return out


def _pp_audit_events_by_sentence(events: list[dict]) -> dict[str, list[dict]]:
    """Group audit events by their target sentence_id.

    sentence_state.py nests target_id/target_type under ``meta``; older
    events may carry them at the top level. Tolerate both.
    """
    out: dict[str, list[dict]] = {}
    for ev in events:
        meta = ev.get('meta') or {}
        target = (
            meta.get('target_id') or ev.get('target_id')
            or ev.get('target', {}).get('id')
        )
        ttype = (
            meta.get('target_type') or ev.get('target_type')
            or ev.get('target', {}).get('type')
        )
        if ttype and ttype != 'Sentence':
            continue
        if not target:
            continue
        out.setdefault(target, []).append(ev)
    return out


# Mapping from short state token → palette key for the UI.
_PP_SENTENCE_STATE_PALETTE = {
    'human_verified':       'verified',     # green
    'human_interpretive':   'interpretive', # blue
    'human_ungrounded':     'ungrounded',   # amber
    'human_needs_fix':      'needs_fix',    # red
    'human_needs_recheck':  'needs_recheck',  # purple-stripe
    None:                   'agent_proposed',  # grey
}

_PP_VERDICT_TO_DEFAULT_PALETTE = {
    'PASS': 'agent_proposed',
    'WARN': 'agent_proposed_warn',
    'FAIL': 'agent_proposed_fail',
    'INFO': 'agent_proposed_info',
    'UNGROUNDED': 'ungrounded_unclaimed',
    'TRANSITION': 'transition',
}


def _pp_sentence_chain_link_states(
    sentence: dict,
    verification_latest: dict[str, dict],
) -> list[dict]:
    """Annotate each chain link with derived state.

    For each link in ``sentence.chain_proposed.links`` produce:
        kind, target, link_state, last_verification (event or None),
        node_id, computed_value, delta_pct (when present).

    ``link_state`` derivation (matches schema delta §3.3):
      human_verified  — link target has a human-confirm verification event
      llm_verified_only  — parameter target has llm_verified_date but no human
      stale  — last_modified > sentence.human_ratified_at (set by caller)
      missing_target  — node_id_for() returns None
      resolved  — default
    """
    try:
        from verification_state import node_id_for as _node_id_for
    except ImportError:
        def _node_id_for(t, k):  # noqa: ARG001
            return None

    chain = sentence.get('chain_proposed') or {}
    links_in = chain.get('links') or []
    out: list[dict] = []
    for raw in links_in:
        kind = raw.get('kind')
        target = raw.get('target')
        # Map link kind → node id type
        if kind == 'parameter':
            nid = _node_id_for('Parameter', target)
        elif kind == 'citation':
            nid = _node_id_for('Citation', target)
        elif kind == 'axiom':
            nid = _node_id_for('LeanAxiom', target)
        elif kind in ('theorem', 'formula'):
            # Lean theorems use lean: prefix; formulas use formula:
            if kind == 'theorem':
                nid = _node_id_for('LeanTheorem', target)
            else:
                nid = _node_id_for('Formula', target)
        else:
            nid = None

        ev = verification_latest.get(nid) if nid else None
        explicit_state = raw.get('link_state')
        if explicit_state in ('llm_verified_only', 'human_verified',
                              'stale', 'missing_target', 'resolved'):
            link_state = explicit_state
        elif nid is None:
            link_state = 'missing_target'
        elif ev and ev.get('action') == 'confirm':
            link_state = 'human_verified'
        else:
            link_state = 'resolved'

        out.append({
            'kind': kind,
            'target': target,
            'node_id': nid,
            'link_state': link_state,
            'last_verification': ev,
            'computed_value': raw.get('computed_value'),
            'delta_pct': raw.get('delta_pct'),
        })
    return out


def _pp_sentence_palette_key(
    sentence: dict, prose_record: dict | None, is_stale: bool,
) -> str:
    """Pick the visual palette key for a sentence.

    Priority: stale > human_state > agent_verdict-based default.
    """
    if is_stale:
        return 'needs_recheck'
    human = (prose_record or {}).get('human_state')
    if human in _PP_SENTENCE_STATE_PALETTE:
        return _PP_SENTENCE_STATE_PALETTE[human]
    verdict = sentence.get('agent_verdict', 'PASS')
    return _PP_VERDICT_TO_DEFAULT_PALETTE.get(verdict, 'agent_proposed')


def _pp_parse_ts(ts: str | None) -> datetime | None:
    """Parse an ISO-8601 timestamp into a datetime. Tolerates both Zulu
    suffix and ``+00:00`` form, both second and microsecond precision.
    Returns None on failure.

    Wave 10d-8: necessary because verification_state writes second-precision
    timestamps (`...23Z`) and sentence_state writes microsecond-precision
    (`...23.456789Z`); raw string compare orders the shorter form GREATER
    when seconds match (because 'Z' > '.'), inverting reality.
    """
    if not ts:
        return None
    s = str(ts).strip()
    if not s:
        return None
    # datetime.fromisoformat accepts +00:00 but not Z prior to 3.11
    # — normalize to +00:00 first.
    if s.endswith('Z'):
        s = s[:-1] + '+00:00'
    try:
        return datetime.fromisoformat(s)
    except ValueError:
        return None


def _pp_compute_sentence_stale(
    sentence: dict,
    prose_record: dict | None,
    chain_links: list[dict],
) -> bool:
    """Return True iff any chain link target's last verification post-dates
    the sentence's human_ratified_at."""
    if (prose_record or {}).get('human_state') is None:
        return False
    rat_dt = _pp_parse_ts((prose_record or {}).get('human_ratified_at'))
    if rat_dt is None:
        return False
    for link in chain_links:
        ev = link.get('last_verification')
        if not ev:
            continue
        ev_dt = _pp_parse_ts(ev.get('timestamp', ''))
        if ev_dt is not None and ev_dt > rat_dt:
            return True
    return False


def _pp_build_data_v2(paper_id: str, cr: dict, fr: dict | None,
                     tex_path) -> dict:
    """Build sentence-keyed dashboard data for v2 schemas.

    Returns the same top-level fields as ``_pp_build_data`` plus:
      sentences[]  — each enriched with `human_state`, `palette`,
                     `chain_links` (annotated), `is_stale`, `audit_events`
      coverage     — counts of sentence states + stale + ungrounded
      audit_events_by_sentence — preserved for the audit-log pane
    """
    # Verification log → latest event per node (used by chain link states +
    # stale derivation across all sentences)
    try:
        from verification_state import latest_per_node
        v_latest = latest_per_node()
    except ImportError:
        v_latest = {}

    prose_state = _pp_load_prose_state(paper_id)
    audit_events = _pp_load_audit_log(paper_id)
    audit_by_sentence = _pp_audit_events_by_sentence(audit_events)
    # Wave 10f — index cross-paper clusters keyed by sentence id
    clusters_by_sentence = _pp_clusters_by_sentence()

    sentences_in = cr.get('sentences', [])
    sentences_out: list[dict] = []

    coverage = {
        'verified': 0, 'interpretive': 0, 'ungrounded_human': 0,
        'needs_fix': 0, 'needs_recheck': 0, 'agent_proposed': 0,
        'transition': 0, 'tombstone': 0, 'total': 0, 'stale': 0,
        'ungrounded_agent': 0,
    }

    for s in sentences_in:
        sid = s.get('id')
        if not sid:
            continue
        if s.get('tombstone'):
            coverage['tombstone'] += 1
            # Tombstones do NOT count toward total / coverage.
            continue
        coverage['total'] += 1
        prose_rec = prose_state['sentences'].get(sid)
        chain_links = _pp_sentence_chain_link_states(s, v_latest)
        stale = _pp_compute_sentence_stale(s, prose_rec, chain_links)
        if stale:
            coverage['stale'] += 1
        palette = _pp_sentence_palette_key(s, prose_rec, stale)

        # Coverage bookkeeping
        human_state = (prose_rec or {}).get('human_state')
        if human_state == 'human_verified':
            coverage['verified'] += 1
        elif human_state == 'human_interpretive':
            coverage['interpretive'] += 1
        elif human_state == 'human_needs_fix':
            coverage['needs_fix'] += 1
        elif human_state == 'human_needs_recheck':
            coverage['needs_recheck'] += 1
        else:
            verdict = s.get('agent_verdict', 'PASS')
            if verdict == 'TRANSITION':
                coverage['transition'] += 1
            elif verdict == 'UNGROUNDED':
                coverage['ungrounded_agent'] += 1
            else:
                coverage['agent_proposed'] += 1

        sentences_out.append({
            'id': sid,
            'section': s.get('section', ''),
            'section_ordinal': s.get('section_ordinal'),
            'tex_line_start': s.get('tex_line_start'),
            'tex_line_end': s.get('tex_line_end'),
            'quote': s.get('quote', ''),
            'type': s.get('type', ''),
            'finding_classes': s.get('finding_classes') or [],
            'agent_verdict': s.get('agent_verdict', 'PASS'),
            'agent_notes': s.get('agent_notes', ''),
            'gates_invoked': s.get('gates_invoked') or [],
            'rewrite_of': s.get('rewrite_of'),
            'delta_pct': s.get('delta_pct'),
            'chain_links': chain_links,
            'human_state': human_state,
            'human_ratified_at': (prose_rec or {}).get('human_ratified_at'),
            'human_ratified_by': (prose_rec or {}).get('human_ratified_by'),
            'human_notes': (prose_rec or {}).get('human_notes', ''),
            'is_stale': stale,
            'palette': palette,
            'audit_event_count': len(audit_by_sentence.get(sid, [])),
            # Wave 10f — cross-paper cluster memberships (zero-or-more)
            'clusters': clusters_by_sentence.get(sid, []),
        })

    # Title parse — share with v1 path below
    title = ''
    try:
        tex_src = tex_path.read_text(errors='replace')
        m = re.search(r'\\title\s*\{', tex_src)
        if m:
            depth = 1
            i = m.end()
            while i < len(tex_src) and depth > 0:
                if tex_src[i] == '{':
                    depth += 1
                elif tex_src[i] == '}':
                    depth -= 1
                    if depth == 0:
                        break
                i += 1
            title = tex_src[m.end():i].replace('\\\\', ' ').strip()[:300]
    except Exception:
        pass

    # Aggregate verdicts to seed the overall_status banner
    n_fail = sum(1 for s in sentences_out if s['agent_verdict'] == 'FAIL')
    n_warn = sum(1 for s in sentences_out if s['agent_verdict'] == 'WARN')
    overall = 'pass' if (n_fail + n_warn) == 0 else 'issues_found'

    return {
        'paper_id': paper_id,
        'title': title,
        'review_date': cr.get('review_date'),
        'reviewer_version': cr.get('reviewer_version'),
        'reviewer_run_id': cr.get('reviewer_run_id'),
        'overall_status': overall,
        'reviewer_notes': cr.get('summary') or cr.get('reviewer_notes'),
        'counts': {
            'fail': n_fail, 'warn': n_warn,
            'pass': sum(1 for s in sentences_out if s['agent_verdict'] == 'PASS'),
            'info': sum(1 for s in sentences_out if s['agent_verdict'] == 'INFO'),
        },
        'stale_count': coverage['stale'],
        'coverage': coverage,
        'blocking': list(cr.get('blocking_issues', [])),
        'non_blocking': list(cr.get('non_blocking_followups', [])),
        'sentences': sentences_out,
        'audit_events_by_sentence': audit_by_sentence,
        'has_claims_review': True,
        'has_figure_review': fr is not None,
        'schema_version': 'v2',
    }


@app.route("/api/papers/<paper_id>/sentences/<path:sentence_id>/verify",
           methods=["POST"])
def api_paper_sentence_verify(paper_id: str, sentence_id: str):
    """Wave 10d sentence-level verification endpoint.

    Body (JSON or form):
      state  — verified | interpretive | needs_fix | needs_recheck
      notes  — free-form
      actor  — user:<id> | agent:<name>:<ts>  (default user:dashboard)

    Routes through ``sentence_state.cmd_mark`` (sole writer to
    ``prose_state.json`` + ``audit_log.jsonl``). Invalidates the graph
    cache so dependent reads pick up the new ratification timestamp.
    """
    payload = request.get_json(silent=True) or request.form
    state = payload.get('state')
    notes = payload.get('notes') or ''
    actor = payload.get('actor') or 'user:dashboard'

    if state not in ('verified', 'interpretive', 'needs_fix', 'needs_recheck'):
        return jsonify({
            "error": "state must be one of: "
                     "verified | interpretive | needs_fix | needs_recheck"
        }), 400

    # sentence_id arrives URL-decoded but path: matcher leaves the colons
    # intact (they're path-safe). Sanity check.
    if not sentence_id.startswith('sentence:'):
        return jsonify({
            "error": "sentence_id must be of the form sentence:<paper>:<slug>:<hash>"
        }), 400
    if not sentence_id.split(':')[1] == paper_id:
        return jsonify({
            "error": f"sentence_id paper mismatch: expected {paper_id}, "
                     f"got {sentence_id.split(':')[1]}"
        }), 400

    # Call CLI in-process (sole-writer pattern; mirrors verification_state).
    try:
        from sentence_state import cmd_mark
    except ImportError as exc:
        return jsonify({"error": f"sentence_state not importable: {exc}"}), 500

    import argparse as _ap
    args = _ap.Namespace(
        sentence_id=sentence_id,
        state=state,
        actor=actor,
        notes=notes,
    )
    # cmd_mark writes prose_state.json + audit_log.jsonl, prints {ok, event_id}
    # to stdout, returns 0 on success / 1 on failure. Capture stdout to relay.
    import io as _io
    import contextlib as _ctx
    out_buf = _io.StringIO()
    err_buf = _io.StringIO()
    rc = -1
    try:
        with _ctx.redirect_stdout(out_buf), _ctx.redirect_stderr(err_buf):
            rc = cmd_mark(args)
    except SystemExit as exc:
        # _paper_from_sentence_id raises SystemExit on malformed ids.
        rc = int(exc.code or 1)
        err_buf.write(str(exc) + "\n")
    except Exception as exc:  # noqa: BLE001
        logger.exception("cmd_mark unexpected failure")
        return jsonify({
            "error": f"cmd_mark unexpected: {exc}",
            "stderr": err_buf.getvalue(),
        }), 500

    if rc != 0:
        return jsonify({
            "error": f"cmd_mark failed (rc={rc})",
            "stderr": err_buf.getvalue().strip(),
        }), 400

    # Parse the {ok, event_id} JSON cmd_mark printed.
    try:
        result = json.loads(out_buf.getvalue().strip().splitlines()[-1])
    except Exception:
        result = {'ok': True}

    # Wave 10c — verification ripple.
    _invalidate_graph_cache()

    # Re-build paper data so the caller can patch sentence state without
    # a separate fetch. Used by Datastar SSE handler downstream.
    data = _pp_build_data(paper_id)
    return jsonify({
        'ok': bool(result.get('ok', True)),
        'event_id': result.get('event_id'),
        'sentence': next(
            (s for s in (data.get('sentences') or []) if s.get('id') == sentence_id),
            None,
        ),
    }), 200


@app.route("/api/papers/<paper_id>/clusters/<path:cluster_id>/propagate",
           methods=["POST"])
def api_cluster_propagate(paper_id: str, cluster_id: str):
    """Wave 10f: propagate a human verification state to all members of a
    cross-paper ClaimCluster.

    Body (JSON or form):
      state            — verified | interpretive | needs_fix | needs_recheck
      source_sentence  — the sentence_id the user is propagating FROM (annotated
                          in audit log as ``propagated_from``)
      actor            — user:<id> | agent:<name>:<ts> (default user:dashboard)

    Iterates ``sentence_state.cmd_mark`` over each cluster member that
    isn't the source sentence. Returns a summary listing per-member rc.
    """
    payload = request.get_json(silent=True) or request.form
    state = payload.get('state')
    source_sentence = payload.get('source_sentence', '')
    actor = payload.get('actor') or 'user:dashboard'
    notes = payload.get('notes', '')

    if state not in ('verified', 'interpretive', 'needs_fix', 'needs_recheck'):
        return jsonify({"error": "state must be one of: "
                                  "verified | interpretive | needs_fix | needs_recheck"}), 400

    clusters = _pp_load_claim_clusters().get('clusters') or []
    cluster = next((c for c in clusters if c.get('id') == cluster_id), None)
    if cluster is None:
        return jsonify({"error": f"unknown cluster_id: {cluster_id}"}), 404

    members = cluster.get('members') or []
    if not members:
        return jsonify({"error": "cluster has no members"}), 400

    try:
        from sentence_state import cmd_mark
    except ImportError as exc:
        return jsonify({"error": f"sentence_state not importable: {exc}"}), 500

    # Append `(propagated from sentence_id)` to notes so the audit trail is
    # readable. cmd_mark's argparse Namespace doesn't take propagated_from
    # natively; we encode it in notes.
    propagation_tag = (
        f' (propagated from {source_sentence})' if source_sentence else ''
    )
    full_notes = (notes + propagation_tag).strip()

    import argparse as _ap
    import io as _io
    import contextlib as _ctx

    results: list[dict] = []
    for sid in members:
        if sid == source_sentence:
            continue  # Don't re-mark the source sentence
        if not sid.startswith(f'sentence:{paper_id.split("_")[0]}'):
            # Cluster spans papers — propagation hits sentences in OTHER
            # papers too. The endpoint URL pins paper_id to the source
            # paper, but that's just for routing; cmd_mark figures out
            # the target paper from the sentence_id.
            pass
        args = _ap.Namespace(
            sentence_id=sid, state=state, actor=actor, notes=full_notes,
        )
        out_buf = _io.StringIO()
        err_buf = _io.StringIO()
        rc = -1
        try:
            with _ctx.redirect_stdout(out_buf), _ctx.redirect_stderr(err_buf):
                rc = cmd_mark(args)
        except SystemExit as exc:
            rc = int(exc.code or 1)
            err_buf.write(str(exc) + '\n')
        except Exception as exc:  # noqa: BLE001
            logger.exception("cmd_mark unexpected failure for %s", sid)
            rc = -1
            err_buf.write(str(exc))
        try:
            evj = json.loads(out_buf.getvalue().strip().splitlines()[-1])
        except Exception:
            evj = {}
        results.append({
            'sentence': sid,
            'rc': rc,
            'event_id': evj.get('event_id'),
            'stderr': err_buf.getvalue().strip() if rc != 0 else None,
        })

    _invalidate_graph_cache()
    return jsonify({
        'cluster_id': cluster_id,
        'state_applied': state,
        'source_sentence': source_sentence,
        'propagated_count': sum(1 for r in results if r['rc'] == 0),
        'failed_count': sum(1 for r in results if r['rc'] != 0),
        'results': results,
    }), 200


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


def _pp_build_data(paper_id: str) -> dict | None:
    """Extract of the original api_paper_provenance body so both JSON and
    SSE consumers share the same computation. Returns None if the paper
    dir is missing (caller emits the appropriate 404 or error event).

    Wave 10d: when ``claims_review.json`` carries the v2 sentence-keyed
    schema (``sentences[]``), routes to :func:`_pp_build_data_v2` for
    the 3-column UI. Legacy 8-layer dossier flow stays for v1 papers.
    """
    papers_dir = PROJECT_ROOT / 'papers'
    paper_dir = papers_dir / paper_id
    tex = paper_dir / 'paper_draft.tex'
    if not tex.exists():
        return None

    cr = _pp_load_claims_review(paper_id)
    fr = _pp_load_figure_review(paper_id)

    # Wave 10d v2 path
    if _pp_is_v2_schema(cr):
        return _pp_build_data_v2(paper_id, cr, fr, tex)

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

    title = ''
    try:
        tex_src = tex.read_text(errors='replace')
        # Balanced-brace extractor — `[^}]+` regex breaks on nested
        # `{...}` like `\pmod{3}` inside the title.
        m = re.search(r'\\title\s*\{', tex_src)
        if m:
            depth = 1
            i = m.end()
            while i < len(tex_src) and depth > 0:
                if tex_src[i] == '{':
                    depth += 1
                elif tex_src[i] == '}':
                    depth -= 1
                    if depth == 0:
                        break
                i += 1
            title = tex_src[m.end():i].replace('\\\\', ' ').strip()[:300]
    except Exception:
        pass

    # Wave 10c — staleness pass. Mark findings whose artifact has been
    # verified after the claims_review was generated; bubble a `is_stale`
    # flag onto the claim for the renderer.
    stale_count, _stale_actors = _pp_compute_stale_findings(cr, claims_out)
    for cid, claim in claims_out.items():
        claim['is_stale'] = any(
            f.get('stale') for f in claim.get('findings', [])
        )

    return {
        'paper_id': paper_id,
        'title': title,
        'review_date': review_date,
        'overall_status': overall,
        'reviewer_notes': reviewer_notes,
        'counts': counts,
        'stale_count': stale_count,
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
        'schema_version': 'v1',
    }


# Worst-status ordering for `worstStatus(claim)` — matches the original JS.
_PP_STATUS_ORDER = {'FAIL': 4, 'WARN': 3, 'INFO': 2, 'PASS': 1}


def _pp_worst_status(claim: dict) -> str:
    best = 'PASS'
    best_n = 0
    for f in claim.get('findings', []):
        n = _PP_STATUS_ORDER.get(f.get('status', 'INFO'), 0)
        if n > best_n:
            best_n = n
            best = f['status']
    return best


def _pp_filtered_claims(data: dict, filter_layers: list[str]) -> list[tuple[str, dict]]:
    """Return (claim_id, claim) pairs visible under the current layer filter."""
    filt = set(filter_layers or [])
    pairs = []
    for cid, claim in (data.get('claims') or {}).items():
        if not filt:
            pairs.append((cid, claim))
            continue
        if any(f.get('layer') in filt for f in claim.get('findings', [])):
            pairs.append((cid, claim))
    # Sort: by layer-of-first-finding, then by worst-status, then by cid
    # Matches the original paper-provenance.js ordering.
    return sorted(pairs, key=lambda kv: (
        kv[1]['findings'][0].get('layer', 'ZZZ') if kv[1].get('findings') else 'ZZZ',
        -_PP_STATUS_ORDER.get(_pp_worst_status(kv[1]), 0),
        kv[0],
    ))


# ── LaTeX → HTML renderer for abstract bodies (Wave 9h final pass) ──
#
# Full pandoc pipeline is Wave 9g-2 (paper.tex → claim-anchored HTML via a
# `\claim{}` macro). Meanwhile, we render a best-effort HTML view of the
# abstract using a minimal LaTeX subset: enough physics commands for
# paper-grade math inlines (Greek letters, sub/superscripts, ≈, ×, ∈, …).
# Anything we don't understand passes through unchanged rather than
# 500-ing.

_LATEX_SYMBOLS = {
    r'\alpha': 'α', r'\beta': 'β', r'\gamma': 'γ', r'\delta': 'δ',
    r'\epsilon': 'ε', r'\varepsilon': 'ε', r'\zeta': 'ζ', r'\eta': 'η',
    r'\theta': 'θ', r'\vartheta': 'ϑ', r'\iota': 'ι', r'\kappa': 'κ',
    r'\lambda': 'λ', r'\mu': 'μ', r'\nu': 'ν', r'\xi': 'ξ', r'\pi': 'π',
    r'\rho': 'ρ', r'\sigma': 'σ', r'\tau': 'τ', r'\upsilon': 'υ',
    r'\phi': 'φ', r'\varphi': 'φ', r'\chi': 'χ', r'\psi': 'ψ', r'\omega': 'ω',
    r'\Gamma': 'Γ', r'\Delta': 'Δ', r'\Theta': 'Θ', r'\Lambda': 'Λ',
    r'\Xi': 'Ξ', r'\Pi': 'Π', r'\Sigma': 'Σ', r'\Phi': 'Φ', r'\Psi': 'Ψ',
    r'\Omega': 'Ω',
    r'\approx': '≈', r'\pm': '±', r'\mp': '∓', r'\sim': '∼',
    r'\times': '×', r'\cdot': '·', r'\in': '∈', r'\notin': '∉',
    r'\subset': '⊂', r'\subseteq': '⊆', r'\supset': '⊃',
    r'\leq': '≤', r'\geq': '≥', r'\ne': '≠', r'\neq': '≠',
    r'\ll': '≪', r'\gg': '≫', r'\to': '→', r'\rightarrow': '→',
    r'\leftarrow': '←', r'\Leftarrow': '⇐', r'\Rightarrow': '⇒',
    r'\mapsto': '↦', r'\infty': '∞', r'\partial': '∂', r'\nabla': '∇',
    r'\int': '∫', r'\sum': '∑', r'\prod': '∏', r'\hbar': 'ℏ',
    r'\ell': 'ℓ', r'\langle': '⟨', r'\rangle': '⟩', r'\cup': '∪',
    r'\cap': '∩', r'\ldots': '…', r'\dots': '…', r'\cdots': '⋯',
}

_SUP_MAP = str.maketrans('0123456789+-=()', '⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻⁼⁽⁾')
_SUB_MAP = str.maketrans('0123456789+-=()aeioruvxhklmnpst',
                          '₀₁₂₃₄₅₆₇₈₉₊₋₌₍₎ₐₑᵢₒᵣᵤᵥₓₕₖₗₘₙₚₛₜ')


def _unicode_script(s: str, which: str) -> str | None:
    """Try to convert an entire substring to Unicode sub/superscript;
    return None if any char has no mapping (caller will use HTML <sub>/<sup>)."""
    table = _SUP_MAP if which == 'sup' else _SUB_MAP
    out = s.translate(table)
    # If every char was translated the length is same and no untranslated
    # alphabetic chars remain.
    if all(c in table.values() or c in (' ',) for c in out):
        return out
    return None


# Math-mode named operators (LaTeX renders these upright + small spaces).
# Inline math doesn't carry full typography, so we just emit the name.
_MATH_OPERATORS = {
    r'\ln': 'ln', r'\log': 'log', r'\exp': 'exp',
    r'\sin': 'sin', r'\cos': 'cos', r'\tan': 'tan',
    r'\arcsin': 'arcsin', r'\arccos': 'arccos', r'\arctan': 'arctan',
    r'\sinh': 'sinh', r'\cosh': 'cosh', r'\tanh': 'tanh',
    r'\det': 'det', r'\dim': 'dim', r'\ker': 'ker',
    r'\inf': 'inf', r'\sup': 'sup', r'\max': 'max', r'\min': 'min',
    r'\arg': 'arg', r'\Re': 'Re', r'\Im': 'Im', r'\mod': 'mod',
}


def _render_math_inline(expr: str) -> str:
    """Render a single `$...$` block to HTML. Conservative subset.

    Order of operations matters:
      1. Symbol commands (`\\mu`, `\\pi`, …) FIRST with word-boundary
         regex so `\\pm` doesn't eat the start of `\\pmod`. Doing
         symbols before `\\text{...}` collapse is critical: `\\mu\\text{m}`
         must NOT first become `\\mum` (which then can't match `\\mu`
         because `m` is a letter). Symbol-first preserves the boundary
         since `\\mu` is followed by `\\` (not a letter).
      2. Special argument-taking commands (`\\frac`, `\\sqrt`, `\\pmod`).
      3. Named operators (`\\ln`, `\\sin`, `\\equiv`, …).
      4. Text-mode collapse (`\\text{...}`, `\\mathrm{...}`).
      5. Backslash escapes (`\\_`, `\\&`, …).
      6. Sub/superscripts.
    """
    s = expr
    # Step 1: Greek + operator symbols with word boundary.
    for k in sorted(_LATEX_SYMBOLS, key=len, reverse=True):
        s = re.sub(re.escape(k) + r'(?![a-zA-Z])', _LATEX_SYMBOLS[k], s)

    # Step 2: Argument-taking special forms.
    # \frac{a}{b} → a/b (flat horizontal form fine for inline)
    s = re.sub(r'\\frac\{([^{}]*)\}\{([^{}]*)\}', r'\1/\2', s)
    # \sqrt{x} → √x
    s = re.sub(r'\\sqrt\{([^{}]*)\}', r'√\1', s)
    # \pmod{x} → (mod x)
    s = re.sub(r'\\pmod\{([^{}]*)\}', r' (mod \1)', s)

    # Step 3: Named operators (multi-letter, can't be in symbol table).
    for k, v in _MATH_OPERATORS.items():
        s = re.sub(re.escape(k) + r'(?![a-zA-Z])', v, s)
    # \bmod and \equiv are also operators-ish.
    s = re.sub(r'\\bmod(?![a-zA-Z])', 'mod', s)
    s = re.sub(r'\\equiv(?![a-zA-Z])', '≡', s)

    # Step 4: Text-mode commands → just the inner text. Must come AFTER
    # symbol replacement so `\mu\text{m}` first becomes `μ\text{m}`,
    # then `μm` rather than the buggy `\mum` order.
    s = re.sub(r'\\text\{([^{}]*)\}', r'\1', s)
    s = re.sub(r'\\mathrm\{([^{}]*)\}', r'\1', s)
    s = re.sub(r'\\mathbf\{([^{}]*)\}', r'<strong>\1</strong>', s)

    # Step 5: Backslash escapes for special characters.
    s = re.sub(r'\\([_&$%#{}])', r'\1', s)
    # ~ is a non-breaking space in math
    s = s.replace('~', ' ')
    # \\ → break (rare in inline math, just treat as space)
    s = s.replace('\\\\', ' ')
    # \, \: \; \! → thin spaces / no space — collapse to space
    s = re.sub(r'\\[,;: ]', ' ', s)
    s = s.replace(r'\!', '')

    # Superscripts / subscripts: prefer Unicode (⁻¹, ₀, …); HTML <sup>/<sub> fallback.
    def _sup(m):
        inner = m.group(1)
        u = _unicode_script(inner, 'sup')
        return u if u else f'<sup>{inner}</sup>'

    def _sub(m):
        inner = m.group(1)
        u = _unicode_script(inner, 'sub')
        return u if u else f'<sub>{inner}</sub>'

    s = re.sub(r'\^\{([^{}]*)\}', _sup, s)
    s = re.sub(r'_\{([^{}]*)\}', _sub, s)
    s = re.sub(r'\^(\S)', lambda m: _unicode_script(m.group(1), 'sup') or f'<sup>{m.group(1)}</sup>', s)
    s = re.sub(r'_(\S)', lambda m: _unicode_script(m.group(1), 'sub') or f'<sub>{m.group(1)}</sub>', s)
    # `{-}` / `{+}` / `{=}` → just the operator
    s = re.sub(r'\{([+\-=])\}', r'\1', s)
    # Drop any remaining bare braces
    s = s.replace('{', '').replace('}', '')
    return s


_LATEX_BLOCK_ENV_RE = re.compile(
    r'\\begin\{(equation|align|gather|multline|itemize|enumerate|figure|table|abstract)\*?\}'
    r'(.*?)'
    r'\\end\{\1\*?\}',
    re.DOTALL,
)


def _latex_block_envs_extract(tex: str) -> tuple[str, dict[str, str]]:
    """Pre-extract LaTeX block envs into HTML placeholders.

    Wave 10d-7: returns (tex_with_markers, marker_to_html). Per-env
    HTML is computed once; the inline renderer's per-char walker sees
    only opaque markers (no LaTeX commands or HTML tags) so the markers
    pass through unchanged + we sub them back at the end.
    """
    blocks: dict[str, str] = {}

    def repl(m: re.Match) -> str:
        env = m.group(1)
        body = m.group(2)
        if env in ('equation', 'align', 'gather', 'multline'):
            inner = re.sub(r'\\label\{[^{}]*\}', '', body).strip()
            inner = re.sub(r'\s+', ' ', inner)
            if len(inner) > 240:
                inner = inner[:240] + '…'
            html = f'<div class="pp-displayed-math">[{esc(env)}] {esc(inner)}</div>'
        elif env == 'itemize':
            items = re.split(r'\\item\b\s*', body)
            items = [it.strip() for it in items if it.strip()]
            lis = ''.join(f'<li>{esc(it[:300])}</li>' for it in items)
            html = f'<ul class="pp-itemize">{lis}</ul>'
        elif env == 'enumerate':
            items = re.split(r'\\item\b\s*', body)
            items = [it.strip() for it in items if it.strip()]
            lis = ''.join(f'<li>{esc(it[:300])}</li>' for it in items)
            html = f'<ol class="pp-enumerate">{lis}</ol>'
        elif env in ('figure', 'table'):
            cap_m = re.search(r'\\caption\{(.+?)\}', body, re.DOTALL)
            cap = cap_m.group(1).strip() if cap_m else '(no caption)'
            cap = re.sub(r'\s+', ' ', cap)[:240]
            html = f'<div class="pp-figure-stub">[{esc(env.title())}: {esc(cap)}]</div>'
        else:
            # abstract / unknown — reserve marker but emit body unchanged
            html = esc(body)
        marker = f'PPBLOCKMARKER{len(blocks):04d}END'
        blocks[marker] = html
        return marker

    rewritten = _LATEX_BLOCK_ENV_RE.sub(repl, tex)
    return rewritten, blocks


def _latex_to_html(tex: str, citation_claims: dict[str, str] | None = None,
                   active_claim: str = '') -> str:
    """Render a paragraph of LaTeX to HTML. Conservative: passes unknown
    commands through unchanged. HTML-escapes text segments; math `$...$`
    goes through `_render_math_inline` which emits safe HTML.

    Wave 10d-7: pre-runs ``_latex_block_envs_to_html`` so top-level
    block environments (equation/align/itemize/enumerate/figure) are
    folded into placeholder HTML before the per-character walker sees
    them — otherwise they degenerate into raw `\\begin{...}` output.

    ``citation_claims`` maps bibkey → claim_id for the CIT layer — when
    present, `\\cite{Bibkey}` is rendered as an inline claim span so it
    visibly highlights citation issues in the abstract. This is the
    partial-heuristic fallback until Wave 9g-3 (`\\claim{id}{text}`
    authoring in the TeX source) gives every claim a canonical anchor.
    """
    # Pre-process: fold block envs into opaque markers + an html lookup.
    # Markers (alphanumeric only) pass cleanly through the per-char
    # walker; we restore the rendered HTML in a single substitution at
    # the end. No-op when the input is sentence-level (no envs).
    tex, _ppblock_lookup = _latex_block_envs_extract(tex)
    citation_claims = citation_claims or {}
    out_parts: list[str] = []
    i = 0
    n = len(tex)
    while i < n:
        c = tex[i]
        if c == '$':
            # Inline math: find closing $
            j = i + 1
            while j < n and tex[j] != '$':
                if tex[j] == '\\' and j + 1 < n:
                    j += 2
                else:
                    j += 1
            math_raw = tex[i + 1:j]
            out_parts.append(f'<span class="pp-math">{_render_math_inline(math_raw)}</span>')
            i = j + 1
        elif c == '\\':
            # Backslash-escape FIRST (`\_`, `\&`, `\$`, `\%`, `\#`, `\{`,
            # `\}`) — these aren't command names; they're literal char
            # escapes. Must be checked before the `\name` regex or
            # `\\_` falls through and becomes literal `\_` in HTML.
            if i + 1 < n and tex[i + 1] in '_&$%#{}':
                out_parts.append(esc(tex[i + 1]))
                i += 2
                continue
            # `\\` → line break in text mode
            if i + 1 < n and tex[i + 1] == '\\':
                out_parts.append('<br>')
                i += 2
                continue
            # Command: \name{...} or \name
            m = re.match(r'\\([a-zA-Z]+)\*?(\{([^{}]*)\})?', tex[i:])
            if not m:
                # Lone backslash with no token — drop it.
                i += 1
                continue
            cmd = m.group(1)
            arg = m.group(3) or ''
            consumed = m.end()
            if cmd in ('textit', 'emph'):
                out_parts.append(f'<em>{esc(arg)}</em>')
            elif cmd == 'textbf':
                out_parts.append(f'<strong>{esc(arg)}</strong>')
            elif cmd == 'texttt':
                out_parts.append(f'<code>{esc(arg)}</code>')
            elif cmd == 'cite':
                # Split multi-key cites (`\cite{A,B,C}`) and wrap each
                # with a claim span if the bibkey has a CIT finding.
                keys = [k.strip() for k in arg.split(',') if k.strip()]
                rendered_keys: list[str] = []
                for k in keys:
                    cid = citation_claims.get(k)
                    if cid:
                        cls = 'pp-claim-span pp-claim-span--warn'
                        # Any citation-integrity FAIL dominates
                        if citation_claims.get(k + ':fail'):
                            cls = 'pp-claim-span pp-claim-span--fail'
                        if cid == active_claim:
                            cls += ' pp-claim-span--active'
                        on_click = (
                            f"$activeClaim = '{esc(cid)}'; "
                            f"@get(`/api/papers/${{$activePaper}}/provenance`)"
                        )
                        rendered_keys.append(
                            f'<span class="{cls}" data-claim-id="{esc(cid)}" '
                            f'data-on:click="{esc(on_click)}" '
                            f'title="{esc(cid)}">{esc(k)}</span>'
                        )
                    else:
                        rendered_keys.append(esc(k))
                if rendered_keys:
                    out_parts.append(' [' + ', '.join(rendered_keys) + ']')
            elif cmd == 'ref' or cmd == 'eqref':
                out_parts.append('')
            elif cmd == 'label':
                out_parts.append('')
            elif cmd in ('begin', 'end'):
                # Skip the rest of the begin{env}/end{env} — the abstract
                # extractor already trimmed these; if one slips through,
                # drop it.
                out_parts.append('')
            elif cmd == 'maketitle' or cmd == 'today':
                out_parts.append('')
            else:
                # Unknown command — look up symbol table first; pass
                # raw LaTeX through so physicists can spot missing
                # symbols instead of silently eating content.
                if '\\' + cmd in _LATEX_SYMBOLS:
                    out_parts.append(_LATEX_SYMBOLS['\\' + cmd])
                else:
                    out_parts.append(esc(m.group(0)))
            i += consumed
        elif c == '~':
            out_parts.append(' ')
            i += 1
        elif c == '-' and tex[i:i + 3] == '---':
            out_parts.append('—')
            i += 3
        elif c == '-' and tex[i:i + 2] == '--':
            out_parts.append('–')
            i += 2
        elif c == '\n':
            # Treat two newlines as paragraph break; single newline as space
            if tex[i:i + 2] == '\n\n':
                out_parts.append('</p><p>')
                i += 2
            else:
                out_parts.append(' ')
                i += 1
        elif c == '%':
            # LaTeX comment — skip to end of line
            j = tex.find('\n', i)
            i = n if j < 0 else j
        else:
            out_parts.append(esc(c))
            i += 1
    html = ''.join(out_parts)
    # Collapse whitespace runs
    html = re.sub(r' {2,}', ' ', html).strip()
    # Wave 10d-7: substitute block-env placeholders back. Markers are
    # alphanumeric-only so they survived the per-char escape pass intact.
    if _ppblock_lookup:
        for marker, block_html in _ppblock_lookup.items():
            html = html.replace(marker, block_html)
    return f'<p>{html}</p>'


def _pp_extract_abstract(tex_path: Path) -> str:
    """Pull `\\begin{abstract}...\\end{abstract}` from a paper .tex. Returns
    an empty string if not found or the file can't be read."""
    try:
        src = tex_path.read_text(errors='replace')
    except Exception:
        return ''
    m = re.search(r'\\begin\{abstract\}(.*?)\\end\{abstract\}', src, re.DOTALL)
    return m.group(1).strip() if m else ''


def _pp_claim_span_class(claim: dict) -> str:
    """Pick a highlight style for an inline claim span based on the
    worst-status finding. Matches the v2 design cream theme: FAIL = solid
    red underline, WARN = amber wavy, INFO = blue dotted, PASS = no style
    (unannotated). Wave 10c: claims with any stale finding pick up the
    ``pp-claim-span--stale`` modifier (purple-stripe, dashboard CSS)."""
    w = _pp_worst_status(claim)
    cls = {
        'FAIL': 'pp-claim-span pp-claim-span--fail',
        'WARN': 'pp-claim-span pp-claim-span--warn',
        'INFO': 'pp-claim-span pp-claim-span--info',
        'PASS': 'pp-claim-span pp-claim-span--pass',
    }.get(w, 'pp-claim-span')
    if claim.get('is_stale'):
        cls += ' pp-claim-span--stale'
    return cls


def _pp_wrap_claim_spans(html_body: str, claims: dict[str, dict],
                         active_claim: str) -> str:
    """Best-effort wrap of claim-quote substrings inside the rendered
    abstract with `<span class="pp-claim-span" ...>` so the v2 design's
    inline highlight works without a `\\claim{}` macro in the TeX source.

    Heuristic — will miss claims whose quotes don't appear verbatim
    (most numerics that get math-rendered). Covered today:
      1. Exact quote substring match (rare — English-language claims)
      2. Citation bibkey author-name (e.g. `Falque2025` → highlight
         any bare mention of "Falque" in the abstract text)

    Everything else surfaces in the right-pane dossier list. The real
    fix is Wave 9g-3: author `\\claim{id}{text}` anchors in the TeX
    source so every claim has a canonical span.
    """
    def make_span(cid: str, claim: dict, visible: str) -> str:
        cls = _pp_claim_span_class(claim)
        if cid == active_claim:
            cls += ' pp-claim-span--active'
        on_click = (
            f"$activeClaim = '{esc(cid)}'; "
            f"@get(`/api/papers/${{$activePaper}}/provenance`)"
        )
        return (
            f'<span class="{cls}" data-claim-id="{esc(cid)}" '
            f'data-on:click="{esc(on_click)}" '
            f'title="{esc(cid)}">{visible}</span>'
        )

    # Sort claims by quote length DESC so the longest substring wins.
    items = [(cid, c) for cid, c in claims.items() if c.get('quote')]
    items.sort(key=lambda kv: -len(kv[1]['quote']))

    # Pass 1: exact substring match on the rendered HTML.
    for cid, claim in items:
        quote = claim['quote'].strip()
        if not quote or len(quote) < 3:
            continue
        esc_quote = esc(quote)
        if esc_quote not in html_body:
            continue
        html_body = html_body.replace(esc_quote, make_span(cid, claim, esc_quote), 1)

    # Pass 2: citation bibkeys → author-name mentions.
    # `Falque2025` → match bare "Falque" (outside existing tags). Only
    # wrap the first occurrence per bibkey so each author mention
    # resolves to its primary citation claim.
    cite_ids = [(cid, c) for cid, c in claims.items()
                if cid.startswith('citation_integrity:')]
    for cid, claim in cite_ids:
        bibkey = cid.split(':', 1)[1]
        # Strip trailing digits to derive author surname (Falque2025 → Falque).
        author = re.sub(r'\d+$', '', bibkey)
        if len(author) < 4:
            continue
        # Word-boundary match, avoid matching inside existing spans/tags.
        pattern = re.compile(
            r'(?<![A-Za-z<>])' + re.escape(author) + r'(?![A-Za-z])'
        )
        # Split by tags so we don't replace inside attributes.
        out_parts: list[str] = []
        pos = 0
        done = False
        for tag in re.finditer(r'<[^>]+>', html_body):
            segment = html_body[pos:tag.start()]
            if not done:
                new_seg, n = pattern.subn(make_span(cid, claim, author), segment, count=1)
                if n:
                    done = True
                    out_parts.append(new_seg)
                else:
                    out_parts.append(segment)
            else:
                out_parts.append(segment)
            out_parts.append(tag.group(0))
            pos = tag.end()
        # Tail
        tail = html_body[pos:]
        if not done:
            tail, _ = pattern.subn(make_span(cid, claim, author), tail, count=1)
        out_parts.append(tail)
        html_body = ''.join(out_parts)

    return html_body


def _pp_paper_body_html(data: dict, active_claim: str) -> str:
    """Render the paper body — title + subtitle + abstract — as HTML with
    inline claim spans. Served as the morph target ``#pp-paper-body``."""
    paper_id = data.get('paper_id', '')
    full_title = data.get('title') or paper_id
    # Split on `:` to get subtitle. Run BOTH halves through `_latex_to_html`
    # so embedded math (e.g. paper10's `$N_f \equiv 0 \pmod{3}$`) renders
    # rather than appearing as raw LaTeX.
    title_main, _, subtitle = full_title.partition(':')
    title_inner = _latex_to_html(title_main.strip()).removeprefix('<p>').removesuffix('</p>')
    title_html = f'{title_inner}:' if subtitle else title_inner
    subtitle_html = ''
    if subtitle:
        sub_inner = _latex_to_html(subtitle.strip()).removeprefix('<p>').removesuffix('</p>')
        subtitle_html = f'<div class="pp-paper__subtitle">{sub_inner}</div>'

    # Render abstract; fall back to a placeholder if none available
    tex_path = PROJECT_ROOT / 'papers' / paper_id / 'paper_draft.tex'
    abstract_raw = _pp_extract_abstract(tex_path) if paper_id else ''
    if abstract_raw:
        # Build a {bibkey: claim_id} lookup so \cite{Bibkey} renders
        # inline as a highlighted claim span. Wave 9g-3 (\claim{}
        # macro authoring) will extend this to numeric + qualitative
        # layers; today only the CIT layer has a canonical anchor.
        citation_claims: dict[str, str] = {}
        for cid, claim in (data.get('claims') or {}).items():
            if not cid.startswith('citation_integrity:'):
                continue
            bibkey = cid.split(':', 1)[1]
            citation_claims[bibkey] = cid
            worst = _pp_worst_status(claim)
            if worst == 'FAIL':
                citation_claims[bibkey + ':fail'] = cid
        abstract_html = _latex_to_html(abstract_raw, citation_claims, active_claim)
        # Also run the plain-substring heuristic for any claim whose
        # quote happens to appear verbatim in the rendered HTML (rare
        # but occasionally hits English-language qualitative claims).
        abstract_html = _pp_wrap_claim_spans(
            abstract_html, data.get('claims') or {}, active_claim
        )
    else:
        abstract_html = (
            '<p class="pp-paper__placeholder">No abstract could be extracted '
            'from paper_draft.tex. Render requires a '
            r'<code>\begin{abstract}…\end{abstract}</code> block.</p>'
        )

    return (
        '<article id="pp-paper-body" class="pp-paper">'
        '<div class="pp-paper__kicker">ARXIV PREPRINT · SUBMITTED TO PRD</div>'
        f'<h1 class="pp-paper__title">{title_html}</h1>'
        + subtitle_html +
        '<div class="pp-paper__byline">SK-EFT Hawking Research Program</div>'
        '<hr class="pp-paper__rule"/>'
        '<div class="pp-paper__section-label">ABSTRACT</div>'
        f'<div class="pp-paper__abstract">{abstract_html}</div>'
        '</article>'
    )


def _pp_default_dossier_html(data: dict) -> str:
    """Right-pane default view: PROVENANCE DOSSIER header + blocking
    issues + non-blocking follow-ups. Replaces the keyboard-hint empty
    state once a paper is loaded. Morphed into ``#pp-detail``."""
    blocking = data.get('blocking') or []
    non_blocking = data.get('non_blocking') or []
    parts = [
        '<div id="pp-detail" class="pp-dossier">',
        '<div class="pp-dossier__section-label">PROVENANCE DOSSIER</div>',
        '<p class="pp-dossier__intro"><em>Hover or click any highlighted span '
        'in the paper to see every layer&rsquo;s verdict for that claim.</em></p>',
    ]
    if blocking:
        parts.append(
            f'<div class="pp-dossier__section-label">BLOCKING ISSUES '
            f'<span class="pp-dossier__count pp-dossier__count--fail">{len(blocking)}</span></div>'
        )
        parts.append('<ul class="pp-dossier__list pp-dossier__list--fail">')
        for b in blocking:
            text = b if isinstance(b, str) else json.dumps(b)
            parts.append(f'<li>{esc(text)}</li>')
        parts.append('</ul>')
    if non_blocking:
        parts.append(
            f'<div class="pp-dossier__section-label">NON-BLOCKING FOLLOW-UPS '
            f'<span class="pp-dossier__count pp-dossier__count--warn">{len(non_blocking)}</span></div>'
        )
        parts.append('<ul class="pp-dossier__list pp-dossier__list--warn">')
        for b in non_blocking:
            text = b if isinstance(b, str) else json.dumps(b)
            parts.append(f'<li>{esc(text)}</li>')
        parts.append('</ul>')
    if not blocking and not non_blocking:
        parts.append(
            '<p class="pp-dossier__empty">No blocking issues or follow-ups recorded '
            'in <code>claims_review.json</code> for this paper.</p>'
        )
    parts.append('</div>')
    return ''.join(parts)


def _pp_banner_html(data: dict) -> str:
    """Emit the four banner morph targets as a single SSE payload string.

    The four ids — pp-banner-title-block / pp-banner-meter / pp-banner-review
    / pp-banner-verdict — sit in separate grid columns of .pp-banner, so they
    each need to be top-level elements in the patched fragment rather than
    wrapped. Datastar's morph applies them by id independently."""
    paper_id = data.get('paper_id') or ''
    full_title = data.get('title') or paper_id
    title_main, _, subtitle = full_title.partition(':')
    title_line = esc(title_main.strip())
    rd = data.get('review_date')
    review_s = f'REVIEW {esc(rd[:10])}' if rd else 'NO REVIEW'
    counts = data.get('counts') or {}
    stale_count = data.get('stale_count') or 0
    overall = data.get('overall_status') or 'unknown'
    if stale_count > 0:
        overall_label = 'NEEDS RECHECK'
        verdict_cls = 'stale'
    elif overall == 'issues_found':
        overall_label = 'ISSUES FOUND'
        verdict_cls = 'issues_found'
    elif overall == 'pass':
        overall_label = 'PASS'
        verdict_cls = 'pass'
    else:
        overall_label = 'UNKNOWN'
        verdict_cls = 'unknown'

    def meter(key: str, label: str) -> str:
        return (f'<div class="pp-meter" data-s="{key}">'
                f'<span class="pp-meter__n">{counts.get(key, 0)}</span>'
                f'<span class="pp-meter__l">{label}</span>'
                f'</div>')

    title_block = (
        f'<div class="pp-banner__title-block" id="pp-banner-title-block">'
        f'<div class="pp-banner__pid">{esc(paper_id)}</div>'
        f'<div class="pp-banner__title">{title_line}</div>'
        f'</div>'
    )
    meter_block = (
        '<div class="pp-banner__meter" id="pp-banner-meter">'
        + meter('fail', 'FAIL') + meter('warn', 'WARN')
        + meter('pass', 'PASS') + meter('info', 'INFO')
        + '</div>'
    )
    review_block = (
        f'<div class="pp-banner__review" id="pp-banner-review">{review_s}</div>'
    )
    verdict_block = (
        f'<div class="pp-verdict" id="pp-banner-verdict" data-v="{esc(verdict_cls)}">'
        f'{esc(overall_label)}</div>'
    )
    return title_block + meter_block + review_block + verdict_block


def _pp_filter_chips_html(data: dict, filter_layers: list[str]) -> str:
    # Count claims per layer (unique per layer per claim)
    layer_counts: dict[str, int] = {l['code']: 0 for l in data.get('layers', [])}
    for claim in (data.get('claims') or {}).values():
        seen: set[str] = set()
        for f in claim.get('findings', []):
            lay = f.get('layer')
            if lay and lay not in seen:
                seen.add(lay)
                layer_counts[lay] = layer_counts.get(lay, 0) + 1
    parts = ['<div id="pp-filter-chips" style="display:contents">']
    active = set(filter_layers or [])
    for l in data.get('layers', []):
        code = l['code']
        n = layer_counts.get(code, 0)
        if n == 0:
            continue
        cls = 'pp-chip' + (' pp-chip--on' if code in active else '')
        # Toggle membership in the $filterLayers array signal. Uses
        # Datastar's JS expression runtime: array push/filter idiom.
        toggle = (
            f"$filterLayers = ($filterLayers || []).includes('{code}') "
            f"? ($filterLayers || []).filter(x => x !== '{code}') "
            f": [...($filterLayers || []), '{code}']; "
            f"$activeClaim = ''; "
            f"@get(`/api/papers/${{$activePaper}}/provenance`)"
        )
        parts.append(
            f'<button class="{cls}" title="{esc(l["desc"])}" '
            f'data-on:click="{esc(toggle)}">'
            f'<span>{esc(l["label"])}</span>'
            f'<span class="pp-chip__n">{n}</span>'
            f'</button>'
        )
    parts.append('</div>')
    return ''.join(parts)


def _pp_nav_html(data: dict, filter_layers: list[str], active_claim: str) -> str:
    filtered = _pp_filtered_claims(data, filter_layers)
    visible = bool(filter_layers)
    if not visible:
        return '<div class="pp-nav" id="pp-nav" style="display:none"></div>'
    if not filtered:
        cnt = '0 of 0'
    else:
        ids = [cid for cid, _ in filtered]
        if active_claim in ids:
            cnt = f'{ids.index(active_claim) + 1} of {len(ids)}'
        else:
            cnt = f'— of {len(ids)}'
    # URL-param `?nav=...` rather than `{payload: {nav: ...}}` so the
    # server reads it via `request.args.get('nav')` consistently with
    # the keyboard shortcuts (which embed in URL). Datastar puts the
    # signal snapshot in `?datastar=...` — `?nav=` is independent.
    prev_expr = "@get(`/api/papers/${$activePaper}/provenance?nav=prev`)"
    next_expr = "@get(`/api/papers/${$activePaper}/provenance?nav=next`)"
    clear_expr = ("$filterLayers = []; "
                  "@get(`/api/papers/${$activePaper}/provenance`)")
    return (
        '<div class="pp-nav" id="pp-nav">'
        f'<button data-on:click="{esc(prev_expr)}" title="Previous (←)">◀</button>'
        f'<span id="pp-nav-count">{esc(cnt)}</span>'
        f'<button data-on:click="{esc(next_expr)}" title="Next (→)">▶</button>'
        f'<button data-on:click="{esc(clear_expr)}" title="Clear filters (Esc)">clear</button>'
        '</div>'
    )


def _pp_claim_list_html(data: dict, filter_layers: list[str], active_claim: str) -> str:
    filtered = _pp_filtered_claims(data, filter_layers)
    total = len(data.get('claims') or {})
    header = f'Claims · {len(filtered)}' + (f' of {total}' if filter_layers else '')
    parts = [
        f'<div class="pp-left__title" id="pp-left-title">{esc(header)}</div>',
        '<div class="pp-left__hint" id="pp-left-hint">',
        'Interactive paper-body with inline claim anchoring lands in Wave 9g-2 '
        '(pandoc + <code>\\claim{}</code> LaTeX macro). Meanwhile, every claim '
        'from <code>claims_review.json</code> + <code>figure_review_report.json</code> '
        'is listed here.',
        '</div>',
        '<div class="pp-claim-list" id="pp-claim-list">',
    ]
    for cid, claim in filtered:
        worst = _pp_worst_status(claim)
        active_cls = ' is-active' if cid == active_claim else ''
        quote = esc(claim.get('quote') or '(no quote)')
        loc = claim.get('location') or ''
        id_line = esc(cid + (f' · {loc}' if loc else ''))
        # Build per-layer dots (dedup by layer)
        seen: set[str] = set()
        dots = []
        for f in claim.get('findings', []):
            lay = f.get('layer')
            if lay in seen or not lay:
                continue
            seen.add(lay)
            st = esc(f.get('status', 'INFO'))
            dots.append(
                f'<span class="pp-claim__layer-dot" data-s="{st}" title="{esc(lay)}: {st}"></span>'
            )
        click_expr = (
            f"$activeClaim = '{esc(cid)}'; "
            f"@get(`/api/papers/${{$activePaper}}/provenance`)"
        )
        parts.append(
            f'<div class="pp-claim{active_cls}" tabindex="0" '
            f'data-on:click="{esc(click_expr)}">'
            f'<div class="pp-claim__badge" data-s="{esc(worst)}">{esc(worst)}</div>'
            f'<div>'
            f'<div class="pp-claim__quote">{quote}</div>'
            f'<div class="pp-claim__id">{id_line}</div>'
            f'</div>'
            f'<div class="pp-claim__layers">{"".join(dots)}</div>'
            f'</div>'
        )
    parts.append('</div>')
    return '<div id="pp-left-pane-inner" style="display:contents">' + ''.join(parts) + '</div>'


def _pp_dossier_html(data: dict, active_claim: str) -> str:
    if not active_claim or active_claim not in (data.get('claims') or {}):
        # Empty state with blocking/non-blocking lists
        parts = [
            '<div id="pp-detail">'
            '<div class="pp-empty">'
            '<div class="pp-empty__hint">'
            'Click any claim on the left to see its 8-layer verdict matrix.<br/>'
            '<kbd>←</kbd> <kbd>→</kbd> cycle claims<br/>'
            '<kbd>F</kbd> next FAIL · <kbd>W</kbd> next WARN · <kbd>Esc</kbd> clear'
            '</div>'
            '<div class="pp-issues" id="pp-issues">'
        ]
        blocking = data.get('blocking') or []
        non_blocking = data.get('non_blocking') or []
        if blocking:
            parts.append(f'<div class="pp-issues__title">Blocking ({len(blocking)})</div><ul>')
            for b in blocking:
                text = b if isinstance(b, str) else json.dumps(b)
                parts.append(f'<li data-b="true">{esc(text)}</li>')
            parts.append('</ul>')
        if non_blocking:
            parts.append(
                f'<div class="pp-issues__title" style="margin-top:16px">Non-blocking ({len(non_blocking)})</div><ul>'
            )
            for b in non_blocking:
                text = b if isinstance(b, str) else json.dumps(b)
                parts.append(f'<li>{esc(text)}</li>')
            parts.append('</ul>')
        parts.append('</div></div></div>')
        return ''.join(parts)

    c = data['claims'][active_claim]
    layers = data.get('layers', [])
    by_layer: dict[str, list[dict]] = {}
    for f in c.get('findings', []):
        by_layer.setdefault(f.get('layer'), []).append(f)

    back_expr = (
        "$activeClaim = ''; "
        "@get(`/api/papers/${$activePaper}/provenance`)"
    )
    parts = [
        '<div id="pp-detail" class="pp-dossier">',
        f'<button class="pp-dossier__back" data-on:click="{esc(back_expr)}">← back to dossier</button>',
        '<div class="pp-dossier__section-label">Claim</div>',
        f'<div class="pp-dossier__claim-quote">{esc(c.get("quote", ""))}</div>',
    ]
    if c.get('location'):
        parts.append(f'<div class="pp-dossier__loc">{esc(c["location"])}</div>')
    parts.append('<div class="pp-dossier__section-label">Vetting layers</div>')
    parts.append('<div class="pp-matrix">')
    for l in layers:
        code = l['code']
        fs = by_layer.get(code)
        if not fs:
            parts.append(
                '<div class="pp-matrix__row" data-na="true">'
                f'<div class="pp-matrix__layer">{esc(l["label"])}</div>'
                '<div class="pp-matrix__status" data-s="NA">—</div>'
                '<div class="pp-matrix__note">not applicable</div>'
                '</div>'
            )
            continue
        for i, f in enumerate(fs):
            layer_cell = esc(l['label']) if i == 0 else ''
            note = ''
            if f.get('delta'):
                note += f'<span class="pp-delta">Δ {esc(f["delta"])}</span>'
            # Wave 10c — stale flag adds a "needs recheck" annotation in
            # the matrix note column so the dossier reader can see WHY
            # the claim span shows a purple stripe.
            if f.get('stale'):
                actor = f.get('stale_actor', '')
                action = f.get('stale_action', '')
                since = (f.get('stale_since', '') or '')[:10]
                stale_label = (
                    f'NEEDS RECHECK · {esc(action)} {esc(since)}'
                    + (f' by {esc(actor)}' if actor else '')
                )
                note += f'<span class="pp-stale-badge">{stale_label}</span> '
            note += esc(f.get('note', ''))
            row_attrs = ' data-stale="true"' if f.get('stale') else ''
            parts.append(
                f'<div class="pp-matrix__row"{row_attrs}>'
                f'<div class="pp-matrix__layer">{layer_cell}</div>'
                f'<div class="pp-matrix__status" data-s="{esc(f.get("status", "INFO"))}">{esc(f.get("status", "INFO"))}</div>'
                f'<div class="pp-matrix__note">{note}</div>'
                '</div>'
            )
    parts.append('</div></div>')
    return ''.join(parts)


def _pp_apply_nav(data: dict, signals: dict, payload_nav: str | None) -> str:
    """If a keyboard/button nav hint was sent, compute the new activeClaim."""
    active = signals.get('activeClaim') or ''
    filter_layers = list(signals.get('filterLayers') or [])
    filtered = _pp_filtered_claims(data, filter_layers)
    if not filtered:
        return active
    ids = [cid for cid, _ in filtered]
    if payload_nav == 'next' or payload_nav == 'prev':
        if active not in ids:
            return ids[0] if payload_nav == 'next' else ids[-1]
        idx = ids.index(active)
        delta = 1 if payload_nav == 'next' else -1
        return ids[(idx + delta) % len(ids)]
    if payload_nav in ('FAIL', 'WARN'):
        target = payload_nav
        # Find next claim whose worstStatus == target after current position
        if active in ids:
            order = ids[ids.index(active) + 1:] + ids[:ids.index(active) + 1]
        else:
            order = ids
        for cid in order:
            if _pp_worst_status(data['claims'][cid]) == target:
                return cid
        return active
    return active


# ──────────────────────────────────────────────────────────────────────
# Wave 10d — v2 sentence-keyed UI renderers
# ──────────────────────────────────────────────────────────────────────

# State-button presets: (label, short token, hint)
_PP_V2_STATE_BUTTONS = (
    ('verified', 'Verified', 'V', 'Sentence is fully verified — chain holds.'),
    ('interpretive', 'Interpretive', 'I', 'Sentence is informal interpretation; flag for downstream readers.'),
    ('needs_fix', 'Needs Fix', 'F', 'A finding requires editorial change to the sentence or chain.'),
    ('needs_recheck', 'Needs Recheck', 'R', 'Verification is uncertain; flag for re-examination.'),
)

_PP_V2_PALETTE_LABEL = {
    'verified': ('Human verified', 'verified'),
    'interpretive': ('Human interpretive', 'interpretive'),
    'ungrounded': ('Human ungrounded', 'ungrounded'),
    'needs_fix': ('Human needs fix', 'needs_fix'),
    'needs_recheck': ('Needs recheck', 'needs_recheck'),
    'agent_proposed': ('Agent proposed', 'agent_proposed'),
    'agent_proposed_warn': ('Agent WARN', 'agent_proposed_warn'),
    'agent_proposed_fail': ('Agent FAIL', 'agent_proposed_fail'),
    'agent_proposed_info': ('Agent INFO', 'agent_proposed_info'),
    'ungrounded_unclaimed': ('Ungrounded', 'ungrounded_unclaimed'),
    'transition': ('Transition', 'transition'),
}


def _pp_v2_apply_nav(data: dict, signals: dict, payload_nav: str | None) -> tuple[str, int]:
    """Update active sentence id from nav hint. Returns (new_active, link_idx).

    Nav hints: prev | next | first-fail | first-warn | first-needs |
                v|i|f|r (state shortcuts handled by client; not here).
    """
    sentences = data.get('sentences') or []
    ids = [s['id'] for s in sentences]
    active = signals.get('activeSentence') or ''
    # NB: ``or -1`` fallback would coerce an explicit 0 to -1 (because
    # 0 is falsy in Python). Use a None-aware coercion instead.
    raw_link = signals.get('activeLinkIdx', -1)
    link_idx = int(raw_link) if raw_link is not None and raw_link != '' else -1

    if not ids:
        return ('', -1)

    if payload_nav in ('next', 'prev'):
        if active not in ids:
            return (ids[0] if payload_nav == 'next' else ids[-1], -1)
        idx = ids.index(active)
        if payload_nav == 'next':
            return (ids[(idx + 1) % len(ids)], -1)
        return (ids[(idx - 1) % len(ids)], -1)

    if payload_nav in ('first-fail', 'first-warn', 'first-needs'):
        verdict = {'first-fail': 'FAIL', 'first-warn': 'WARN'}.get(payload_nav)
        if verdict:
            for s in sentences:
                if s.get('agent_verdict') == verdict:
                    return (s['id'], -1)
        else:  # first-needs
            for s in sentences:
                if s.get('is_stale') or s.get('agent_verdict') == 'UNGROUNDED':
                    return (s['id'], -1)
        return (active, link_idx)

    if payload_nav == 'link-next' or payload_nav == 'link-prev':
        s = next((s for s in sentences if s['id'] == active), None)
        if not s:
            return (active, -1)
        n_links = len(s.get('chain_links') or [])
        if n_links == 0:
            return (active, -1)
        if link_idx < 0:
            return (active, 0 if payload_nav == 'link-next' else n_links - 1)
        if payload_nav == 'link-next':
            return (active, (link_idx + 1) % n_links)
        return (active, (link_idx - 1) % n_links)

    return (active, link_idx)


def _pp_v2_coverage_ribbon_html(data: dict) -> str:
    """Render the coverage ribbon: % verified / proposed / unclaimed /
    stale / ungrounded. Morph target: ``#pp-coverage-ribbon``.
    """
    cov = data.get('coverage') or {}
    total = cov.get('total', 0) or 1  # avoid div by zero
    cells = [
        ('Verified', cov.get('verified', 0), 'verified'),
        ('Interpretive', cov.get('interpretive', 0), 'interpretive'),
        ('Needs Fix', cov.get('needs_fix', 0), 'needs_fix'),
        ('Needs Recheck', cov.get('needs_recheck', 0), 'needs_recheck'),
        ('Stale (any link)', cov.get('stale', 0), 'stale'),
        ('Agent only', cov.get('agent_proposed', 0), 'agent_proposed'),
        ('Ungrounded', cov.get('ungrounded_agent', 0), 'ungrounded_unclaimed'),
        ('Transition', cov.get('transition', 0), 'transition'),
    ]
    total_meaningful = sum(n for _, n, _ in cells)
    parts: list[str] = [
        '<div id="pp-coverage-ribbon" class="pp-coverage">',
        f'<div class="pp-coverage__total">{cov.get("total", 0)} sentences</div>',
        '<div class="pp-coverage__bar">',
    ]
    if total_meaningful > 0:
        for label, n, key in cells:
            if n == 0:
                continue
            pct = (n / total) * 100.0
            parts.append(
                f'<div class="pp-coverage__seg" data-pal="{esc(key)}" '
                f'style="flex: {n};" title="{esc(label)}: {n}"></div>'
            )
    else:
        parts.append('<div class="pp-coverage__empty">no sentences</div>')
    parts.append('</div>')
    parts.append('<div class="pp-coverage__legend">')
    for label, n, key in cells:
        if n == 0:
            continue
        parts.append(
            f'<span class="pp-coverage__chip" data-pal="{esc(key)}">'
            f'<span class="pp-coverage__dot" data-pal="{esc(key)}"></span>'
            f'{esc(label)}: <strong>{n}</strong></span>'
        )
    parts.append('</div></div>')
    return ''.join(parts)


def _pp_filter_sentences_by_gate(
    sentences: list[dict], gate_filter: str,
) -> tuple[list[dict], int]:
    """Wave 10g: when ``$gateFilter`` is set (e.g. ``gate:CitationIntegrity``
    from a Readiness/Process-Health deep-link), keep only sentences whose
    ``gates_invoked`` list includes the named gate. Returns (filtered, dropped).

    Filter syntax: ``gate:<gate_name>`` (case-insensitive, partial-match).
    Empty/missing filter returns all sentences. Falls through gracefully
    (no filtering) when the syntax doesn't match.
    """
    if not gate_filter:
        return (sentences, 0)
    if not gate_filter.startswith('gate:'):
        return (sentences, 0)
    needle = gate_filter[5:].strip().lower()
    if not needle:
        return (sentences, 0)
    kept: list[dict] = []
    for s in sentences:
        gates = [str(g).lower() for g in (s.get('gates_invoked') or [])]
        if any(needle in g for g in gates):
            kept.append(s)
    return (kept, len(sentences) - len(kept))


def _pp_v2_paper_body_html(data: dict, active_sentence: str,
                           gate_filter: str = '') -> str:
    """Render the abstract with each sentence wrapped in an interactive
    span. Sentences in section "abstract" are rendered inline; other
    sections appear in collapsed group headers (until Wave 10d-7 lands
    full-body render).

    Wave 10g: when ``gate_filter`` is set, only sentences whose
    ``gates_invoked`` list includes the named gate are rendered, plus
    a banner indicating the filter is active.
    """
    paper_id = data.get('paper_id', '')
    full_title = data.get('title') or paper_id
    title_main, _, subtitle = full_title.partition(':')
    title_inner = _latex_to_html(title_main.strip()).removeprefix('<p>').removesuffix('</p>')
    title_html = f'{title_inner}:' if subtitle else title_inner
    subtitle_html = ''
    if subtitle:
        sub_inner = _latex_to_html(subtitle.strip()).removeprefix('<p>').removesuffix('</p>')
        subtitle_html = f'<div class="pp-paper__subtitle">{sub_inner}</div>'

    all_sentences = data.get('sentences') or []
    sentences, dropped = _pp_filter_sentences_by_gate(all_sentences, gate_filter)

    # Group sentences by section so each section header lists its sentences
    by_section: dict[str, list[dict]] = {}
    section_order: list[str] = []
    for s in sentences:
        sec = s.get('section') or 'untitled'
        if sec not in by_section:
            by_section[sec] = []
            section_order.append(sec)
        by_section[sec].append(s)

    parts: list[str] = [
        '<article id="pp-paper-body" class="pp-paper">',
        '<div class="pp-paper__kicker">SK-EFT HAWKING · SENTENCE-LEVEL PROVENANCE</div>',
        f'<h1 class="pp-paper__title">{title_html}</h1>',
        subtitle_html,
        '<div class="pp-paper__byline">SK-EFT Hawking Research Program</div>',
        '<hr class="pp-paper__rule"/>',
    ]
    # Wave 10g — surface active gate filter so the user knows the body
    # isn't showing every sentence. Cleared by Esc (also clears
    # $gateFilter via the existing keyboard binding).
    if gate_filter and dropped > 0:
        clear_expr = (
            "$gateFilter = ''; window.history.replaceState({}, '', "
            "'?tab=paper&paper=' + encodeURIComponent($activePaper)); "
            "@get(`/api/papers/${$activePaper}/provenance`)"
        )
        parts.append(
            '<div class="pp-paper__filter-banner">'
            f'Filter: <strong>{esc(gate_filter)}</strong> · showing '
            f'{len(sentences)} of {len(all_sentences)} sentences '
            f'<button class="pp-paper__filter-clear" '
            f'data-on:click="{esc(clear_expr)}">clear (Esc)</button>'
            '</div>'
        )
    elif gate_filter and dropped == 0 and not sentences:
        parts.append(
            '<div class="pp-paper__filter-banner">'
            f'Filter <strong>{esc(gate_filter)}</strong> matched zero '
            'sentences in this paper.'
            '</div>'
        )

    for sec in section_order:
        sec_sents = by_section[sec]
        # Sort by section_ordinal if available, else preserve order
        sec_sents = sorted(sec_sents, key=lambda s: s.get('section_ordinal') or 0)
        sec_label = sec.replace('-', ' ').upper()
        parts.append(f'<div class="pp-paper__section-label">{esc(sec_label)}</div>')
        parts.append('<div class="pp-paper__abstract">')
        for s in sec_sents:
            sid = s['id']
            quote_inner = _latex_to_html(s.get('quote', ''))
            quote_inner = quote_inner.removeprefix('<p>').removesuffix('</p>')
            palette_key = s.get('palette') or 'agent_proposed'
            classes = ['pp-sentence', f'pp-sentence--{palette_key}']
            if sid == active_sentence:
                classes.append('pp-sentence--active')
            if s.get('is_stale'):
                classes.append('pp-sentence--stale')
            click_expr = (
                f"$activeSentence = '{esc(sid)}'; "
                f"$activeLinkIdx = -1; "
                f"@get(`/api/papers/${{$activePaper}}/provenance`)"
            )
            verdict = esc(s.get('agent_verdict', ''))
            parts.append(
                f'<span class="{ " ".join(classes) }" '
                f'data-sentence-id="{esc(sid)}" '
                f'data-on:click="{esc(click_expr)}" '
                f'title="{verdict} · {esc(palette_key)}">'
                f'{quote_inner} </span>'
            )
        parts.append('</div>')
    parts.append('</article>')
    return ''.join(parts)


def _pp_v2_sentence_inspector_html(data: dict, active_sentence: str) -> str:
    """Middle column: per-sentence verdict + state machine + chain summary.

    Morph target: ``#pp-sentence-inspector``.
    """
    sentences = data.get('sentences') or []
    s = next((s for s in sentences if s['id'] == active_sentence), None)
    if not s:
        return (
            '<aside id="pp-sentence-inspector" class="pp-inspector">'
            '<div class="pp-inspector__empty">'
            '<div class="pp-inspector__hint">Click any sentence in the paper '
            '(or use <kbd>↑↓</kbd>) to inspect its chain + state.</div>'
            '<div class="pp-inspector__hint">Keyboard: <kbd>v</kbd> verify · '
            '<kbd>i</kbd> interpretive · <kbd>r</kbd> recheck · '
            '<kbd>f</kbd> needs fix · <kbd>→</kbd> chain inspector · '
            '<kbd>Esc</kbd> clear</div></div></aside>'
        )

    sid = s['id']
    palette_key = s.get('palette') or 'agent_proposed'
    palette_label = _PP_V2_PALETTE_LABEL.get(palette_key, (palette_key, palette_key))[0]
    verdict = s.get('agent_verdict', '')
    notes = s.get('agent_notes', '')

    # State buttons — each posts to the verify endpoint, then refreshes panel
    btn_html_parts: list[str] = []
    for short, label, key, hint in _PP_V2_STATE_BUTTONS:
        post_expr = (
            f"@post(`/api/papers/${{$activePaper}}/sentences/{esc(sid)}/verify`, "
            f"{{contentType:'json', body: JSON.stringify({{state:'{short}', "
            f"actor:'user:dashboard'}})}}); "
            f"@get(`/api/papers/${{$activePaper}}/provenance`)"
        )
        btn_html_parts.append(
            f'<button class="pp-state-btn pp-state-btn--{esc(short)}" '
            f'data-on:click="{esc(post_expr)}" '
            f'title="{esc(hint)}">'
            f'<kbd>{esc(key)}</kbd> {esc(label)}</button>'
        )

    chain_links = s.get('chain_links') or []
    chain_link_html_parts: list[str] = []
    for idx, link in enumerate(chain_links):
        link_state = link.get('link_state', 'resolved')
        link_kind = link.get('kind', '')
        target = link.get('target', '')
        click_expr = (
            f"$activeLinkIdx = {idx}; "
            f"@get(`/api/papers/${{$activePaper}}/provenance`)"
        )
        chain_link_html_parts.append(
            f'<li class="pp-chain-link" data-link-state="{esc(link_state)}" '
            f'data-on:click="{esc(click_expr)}">'
            f'<span class="pp-chain-link__kind">{esc(link_kind)}</span>'
            f'<span class="pp-chain-link__target">{esc(target)}</span>'
            f'<span class="pp-chain-link__state">{esc(link_state)}</span>'
            f'</li>'
        )
    if not chain_link_html_parts:
        chain_html = (
            '<div class="pp-inspector__empty-chain">'
            'No chain links proposed (UNGROUNDED or TRANSITION sentence).'
            '</div>'
        )
    else:
        chain_html = (
            f'<ul class="pp-chain-links">{ "".join(chain_link_html_parts) }</ul>'
        )

    finding_classes = s.get('finding_classes') or []
    fc_html = ''
    if finding_classes:
        chips = ' '.join(
            f'<span class="pp-finding-chip">{esc(c)}</span>' for c in finding_classes
        )
        fc_html = f'<div class="pp-inspector__row"><span class="pp-inspector__lbl">Finding classes:</span> {chips}</div>'

    # Audit log summary (full pane in 10d-6; here just a count + link)
    n_audit = s.get('audit_event_count', 0)
    ratified_at = s.get('human_ratified_at')
    ratified_by = s.get('human_ratified_by')
    rat_html = ''
    if ratified_at:
        rat_html = (
            f'<div class="pp-inspector__row"><span class="pp-inspector__lbl">Last ratified:</span> '
            f'<code>{esc(ratified_at[:19])}</code> by <code>{esc(ratified_by or "")}</code></div>'
        )

    audit_toggle_expr = (
        f"$showAudit = !$showAudit; "
        f"@get(`/api/papers/${{$activePaper}}/provenance`)"
    )

    # Wave 10f — cluster banner. If this sentence is a member of one or
    # more cross-paper ClaimClusters, render a banner per cluster with
    # a "propagate" button that fires the propagation endpoint.
    cluster_html = ''
    clusters_for_sid = s.get('clusters') or []
    s_human_state = s.get('human_state')
    cur_short_state = (
        s_human_state.replace('human_', '') if s_human_state else 'verified'
    )
    for cluster in clusters_for_sid:
        cid = cluster.get('cluster_id', '')
        n_other = len(cluster.get('other_members') or [])
        match_kind = cluster.get('match_kind', 'exact')
        confidence = cluster.get('confidence', 1.0)
        member_papers = cluster.get('member_papers') or []
        # Prompt for the state (verified/interpretive/needs_fix/needs_recheck);
        # default to the active sentence's current state. Advanced
        # one-click UX with state pre-pick is a 10f-followup.
        propagate_expr = (
            "let st = prompt('Propagate which state to other "
            "{n_other} member(s)?\\n\\nverified | interpretive | needs_fix | needs_recheck', "
            "'{cur_state}'); "
            "if (st && ['verified','interpretive','needs_fix','needs_recheck'].includes(st)) {{ "
            "@post(`/api/papers/${{$activePaper}}/clusters/{cid}/propagate`, "
            "{{contentType:'json', body: JSON.stringify({{state: st, "
            "source_sentence: $activeSentence, actor: 'user:dashboard'}})}}); "
            "@get(`/api/papers/${{$activePaper}}/provenance`); "
            "}}"
        ).format(
            n_other=n_other,
            cur_state=cur_short_state,
            cid=cid,
        )
        # The active sentence belongs to the displayed paper, which is
        # the data['paper_id']; show only the OTHER member papers.
        active_paper_id = (s.get('id') or '').split(':')[1] if (s.get('id') or '').count(':') >= 1 else ''
        member_papers_str = ', '.join(p for p in member_papers if p != active_paper_id) or '—'
        cluster_html += (
            '<div class="pp-cluster-banner" '
            f'data-match-kind="{esc(match_kind)}">'
            f'<div class="pp-cluster-banner__head">CROSS-PAPER CLAIM CLUSTER · '
            f'{esc(match_kind)} ({confidence:.2f})</div>'
            f'<div class="pp-cluster-banner__body">'
            f'Same factual claim appears in <strong>{n_other}</strong> other paper'
            f'{"s" if n_other != 1 else ""} '
            f'(<code>{esc(member_papers_str)}</code>).</div>'
            f'<button class="pp-cluster-banner__btn" '
            f'data-on:click="{esc(propagate_expr)}" '
            f'title="Apply current verification state to all other members">'
            f'Propagate to {n_other} other member{"s" if n_other != 1 else ""}'
            '</button>'
            '</div>'
        )

    return (
        '<aside id="pp-sentence-inspector" class="pp-inspector">'
        '<div class="pp-inspector__head">'
        f'<div class="pp-inspector__verdict pp-inspector__verdict--{esc(verdict.lower())}">{esc(verdict)}</div>'
        f'<div class="pp-inspector__palette" data-pal="{esc(palette_key)}">{esc(palette_label)}</div>'
        '</div>'
        f'<div class="pp-inspector__quote">{ _latex_to_html(s.get("quote", "")).removeprefix("<p>").removesuffix("</p>") }</div>'
        f'<div class="pp-inspector__id"><code>{esc(sid)}</code></div>'
        f'{fc_html}'
        f'<div class="pp-inspector__row"><span class="pp-inspector__lbl">Type:</span> {esc(s.get("type", ""))}</div>'
        f'{rat_html}'
        f'<div class="pp-inspector__notes">{esc(notes)}</div>'
        f'{cluster_html}'
        '<div class="pp-inspector__section-label">Verify</div>'
        f'<div class="pp-state-btns">{ "".join(btn_html_parts) }</div>'
        '<div class="pp-inspector__section-label">Chain '
        f'({len(chain_links)} link{"s" if len(chain_links)!=1 else ""})</div>'
        f'{chain_html}'
        f'<button class="pp-inspector__audit-toggle" data-on:click="{esc(audit_toggle_expr)}">'
        f'Audit log ({n_audit})</button>'
        '</aside>'
    )


def _pp_v2_chain_inspector_html(data: dict, active_sentence: str,
                                active_link_idx: int) -> str:
    """Right column: per-link verification UI + in-place artifact preview.

    Morph target: ``#pp-chain-inspector``.
    """
    sentences = data.get('sentences') or []
    s = next((s for s in sentences if s['id'] == active_sentence), None)
    if not s:
        return (
            '<aside id="pp-chain-inspector" class="pp-inspector pp-inspector--right">'
            '<div class="pp-inspector__empty">'
            '<div class="pp-inspector__hint">Select a sentence to expose '
            'its chain. Click any link there (or use <kbd>↑↓</kbd>) to '
            'preview the artifact in place.</div></div></aside>'
        )

    chain_links = s.get('chain_links') or []
    if active_link_idx < 0 or active_link_idx >= len(chain_links):
        return (
            '<aside id="pp-chain-inspector" class="pp-inspector pp-inspector--right">'
            '<div class="pp-inspector__empty">'
            f'<div class="pp-inspector__hint">{len(chain_links)} chain '
            f'link{"s" if len(chain_links)!=1 else ""} on this sentence. '
            'Click one (or press <kbd>→</kbd>) to expand its artifact.</div>'
            '</div></aside>'
        )

    link = chain_links[active_link_idx]
    kind = link.get('kind', '')
    target = link.get('target', '')
    nid = link.get('node_id') or ''
    link_state = link.get('link_state', '')
    last_v = link.get('last_verification') or {}

    # Per-link verify UI: three-state buttons. They post to the generic
    # /api/verification/event endpoint so each tab type can land changes
    # consistently.
    artifact_type = {
        'parameter': 'Parameter',
        'citation': 'Citation',
        'axiom': 'LeanAxiom',
        'theorem': 'LeanTheorem',
    }.get(kind, '')

    verify_btns_html = ''
    if artifact_type:
        for short, color, label in (
            ('confirm', 'verified', '✓ Confirm'),
            ('reject', 'needs_fix', '✗ Wrong'),
            ('flag', 'needs_recheck', '⚠ Uncertain'),
        ):
            # Wave 10 strengthening: forward $activeSentence as
            # ``triggered_by`` so the audit trail surfaces "this
            # verification was fired from sentence <id>'s per-link UI".
            post_expr = (
                f"@post('/api/verification/event', "
                f"{{contentType:'json', body: JSON.stringify({{"
                f"artifact_type:'{esc(artifact_type)}', "
                f"artifact_id:'{esc(target)}', "
                f"action:'{short}', actor:'user:dashboard', "
                f"triggered_by: $activeSentence}})}}); "
                f"@get(`/api/papers/${{$activePaper}}/provenance`)"
            )
            verify_btns_html += (
                f'<button class="pp-link-verify pp-link-verify--{esc(color)}" '
                f'data-on:click="{esc(post_expr)}">{esc(label)}</button>'
            )

    # Artifact preview body — defer to in-place expander
    preview_html = _pp_v2_artifact_preview_html(kind, target, link)

    last_v_html = ''
    if last_v:
        last_v_html = (
            '<div class="pp-inspector__row"><span class="pp-inspector__lbl">Last verification:</span> '
            f'<code>{esc((last_v.get("timestamp") or "")[:19])}</code> · '
            f'{esc(last_v.get("action", ""))} by <code>{esc(last_v.get("actor", ""))}</code></div>'
        )

    return (
        '<aside id="pp-chain-inspector" class="pp-inspector pp-inspector--right">'
        '<div class="pp-inspector__head">'
        f'<div class="pp-inspector__kind">{esc(kind.upper())}</div>'
        f'<div class="pp-link-state pp-link-state--{esc(link_state)}">{esc(link_state)}</div>'
        '</div>'
        f'<div class="pp-inspector__target"><code>{esc(target)}</code></div>'
        f'<div class="pp-inspector__row"><span class="pp-inspector__lbl">Node:</span> '
        f'<code>{esc(nid or "—")}</code></div>'
        f'{last_v_html}'
        f'<div class="pp-inspector__section-label">Artifact</div>'
        f'<div class="pp-link-preview">{preview_html}</div>'
        f'<div class="pp-inspector__section-label">Per-link verification</div>'
        f'<div class="pp-link-verify-row">{verify_btns_html or "<em>No verify path for this link kind.</em>"}</div>'
        '</aside>'
    )


def _pp_v2_artifact_preview_html(kind: str, target: str, link: dict) -> str:
    """In-place artifact preview for the chain inspector. Pulls minimal
    data from live registries (PARAMETER_PROVENANCE, CITATION_REGISTRY,
    lean_deps.json). Best-effort — falls back to "(unable to load)".
    """
    try:
        if kind == 'parameter':
            from src.core.provenance import PARAMETER_PROVENANCE
            entry = PARAMETER_PROVENANCE.get(target)
            if not entry:
                return f'<em>Parameter <code>{esc(target)}</code> not in PARAMETER_PROVENANCE.</em>'
            value = entry.get('value')
            unit = entry.get('unit', '')
            tier = entry.get('tier', '')
            source = entry.get('source', '')
            llm_v = entry.get('llm_verified_date')
            human_v = entry.get('human_verified_date')
            return (
                f'<div class="pp-art__hdr">{esc(target)}</div>'
                f'<div class="pp-art__row"><span class="pp-art__lbl">value:</span> '
                f'<code>{esc(str(value))}</code> {esc(unit or "")}</div>'
                f'<div class="pp-art__row"><span class="pp-art__lbl">tier:</span> {esc(tier)}</div>'
                f'<div class="pp-art__row"><span class="pp-art__lbl">source:</span> {esc(source[:200])}</div>'
                f'<div class="pp-art__row"><span class="pp-art__lbl">llm verified:</span> {esc(str(llm_v))}</div>'
                f'<div class="pp-art__row"><span class="pp-art__lbl">human verified:</span> {esc(str(human_v))}</div>'
            )
        if kind == 'citation':
            from src.core.citations import CITATION_REGISTRY
            entry = CITATION_REGISTRY.get(target)
            if not entry:
                return f'<em>Citation <code>{esc(target)}</code> not in CITATION_REGISTRY.</em>'
            return (
                f'<div class="pp-art__hdr">{esc(target)}</div>'
                f'<div class="pp-art__row"><span class="pp-art__lbl">title:</span> {esc(entry.get("title", "")[:200])}</div>'
                f'<div class="pp-art__row"><span class="pp-art__lbl">authors:</span> {esc(entry.get("authors", "")[:200])}</div>'
                f'<div class="pp-art__row"><span class="pp-art__lbl">journal/year:</span> {esc(entry.get("journal", ""))} {esc(str(entry.get("year", "")))}</div>'
                f'<div class="pp-art__row"><span class="pp-art__lbl">doi:</span> <code>{esc(entry.get("doi", "—") or "—")}</code></div>'
                f'<div class="pp-art__row"><span class="pp-art__lbl">arxiv:</span> <code>{esc(entry.get("arxiv", "—") or "—")}</code></div>'
                f'<div class="pp-art__row"><span class="pp-art__lbl">doi verified:</span> {esc(str(entry.get("doi_verified")))}</div>'
            )
        if kind in ('theorem', 'axiom', 'formula'):
            return (
                f'<div class="pp-art__hdr">{esc(target)}</div>'
                f'<div class="pp-art__row"><em>Lean source preview is a Wave 10d-6 follow-up '
                f'(reads ``lean_deps.json`` / declaration source for the named identifier).</em></div>'
            )
        return f'<em>Unknown link kind: {esc(kind)}</em>'
    except Exception as exc:  # noqa: BLE001
        logger.warning("artifact preview failed for %s/%s: %s", kind, target, exc)
        return f'<em>(unable to load preview: {esc(str(exc))})</em>'


def _pp_v2_audit_log_html(data: dict, active_sentence: str) -> str:
    """Bottom drawer audit log + diff-since-last-verified.

    Morph target: ``#pp-audit-pane``. Visibility controlled by the
    ``$showAudit`` signal in the template (data-show binding). We
    always emit the content so toggling is instant — no extra fetch.
    """
    if not active_sentence:
        return (
            '<div id="pp-audit-pane" class="pp-audit">'
            '<div class="pp-audit__head">AUDIT LOG</div>'
            '<div class="pp-audit__empty">'
            'Select a sentence to see its verification history.'
            '</div></div>'
        )

    sentences = data.get('sentences') or []
    s = next((x for x in sentences if x['id'] == active_sentence), None)
    if not s:
        return (
            '<div id="pp-audit-pane" class="pp-audit">'
            '<div class="pp-audit__head">AUDIT LOG</div>'
            '<div class="pp-audit__empty">Active sentence not found.</div></div>'
        )

    audit_by = data.get('audit_events_by_sentence') or {}
    events = audit_by.get(active_sentence) or []

    # Diff-since-last-verified: walk chain_links, find any whose
    # last_verification.timestamp > sentence.human_ratified_at.
    # Use datetime parsing to avoid the cross-precision string-compare
    # bug (verification_state second-precision vs sentence_state
    # microsecond-precision; see _pp_parse_ts comment).
    rat_raw = s.get('human_ratified_at') or ''
    rat_dt = _pp_parse_ts(rat_raw)
    diff_rows: list[str] = []
    for link in s.get('chain_links') or []:
        ev = link.get('last_verification') or {}
        ts = ev.get('timestamp', '')
        ev_dt = _pp_parse_ts(ts)
        if rat_dt and ev_dt and ev_dt > rat_dt:
            # Wave 10 strengthening — surface triggered_by so the user
            # sees if a per-link verify came from THIS sentence's chain
            # inspector vs from another sentence (cross-tab).
            tb = ev.get('triggered_by') or ''
            same_sentence = tb == s.get('id')
            tb_html = ''
            if tb:
                marker = '⚲' if same_sentence else '↗'
                title = ('triggered from this sentence'
                         if same_sentence else
                         f'triggered from {tb}')
                tb_html = (
                    f' <span class="pp-audit__triggered-by" '
                    f'title="{esc(title)}">{esc(marker)} {esc(tb if not same_sentence else "self")}</span>'
                )
            diff_rows.append(
                '<tr>'
                f'<td>{esc(link.get("kind", ""))}</td>'
                f'<td><code>{esc(link.get("target", ""))}</code></td>'
                f'<td><code>{esc(ts[:19])}</code></td>'
                f'<td>{esc(ev.get("action", ""))}{tb_html}</td>'
                f'<td><code>{esc(ev.get("actor", ""))}</code></td>'
                '</tr>'
            )

    diff_html = ''
    if rat_dt and diff_rows:
        diff_html = (
            '<div class="pp-audit__section-label">DIFF SINCE LAST VERIFIED · '
            f'<code>{esc(rat_raw[:19])}</code></div>'
            '<table class="pp-audit__diff">'
            '<thead><tr><th>kind</th><th>target</th><th>updated</th>'
            '<th>action</th><th>by</th></tr></thead>'
            f'<tbody>{ "".join(diff_rows) }</tbody>'
            '</table>'
        )
    elif rat_dt:
        diff_html = (
            '<div class="pp-audit__section-label">DIFF SINCE LAST VERIFIED · '
            f'<code>{esc(rat_raw[:19])}</code></div>'
            '<div class="pp-audit__nodiff">No backing artifacts have been '
            're-verified since this sentence was ratified.</div>'
        )

    # Event log — newest first.
    # sentence_state.py nests fields under `meta`; tolerate flat events too.
    rev_events = list(reversed(events))
    log_rows: list[str] = []
    for ev in rev_events:
        meta = ev.get('meta') or {}
        ts = meta.get('timestamp') or ev.get('timestamp', '')
        actor = meta.get('actor') or ev.get('actor', '')
        action = meta.get('action') or ev.get('action', '')
        new_state = meta.get('new_state') or ev.get('new_state') or ''
        prior_state = meta.get('prior_state', ev.get('prior_state'))
        notes = meta.get('notes') or ev.get('notes', '') or ''
        log_rows.append(
            '<tr>'
            f'<td><code>{esc(str(ts)[:19])}</code></td>'
            f'<td>{esc(action)}</td>'
            f'<td>{esc(str(prior_state) if prior_state is not None else "—")}</td>'
            f'<td>{esc(new_state)}</td>'
            f'<td><code>{esc(actor)}</code></td>'
            f'<td>{esc(notes[:120])}</td>'
            '</tr>'
        )
    log_html = ''
    if log_rows:
        log_html = (
            '<div class="pp-audit__section-label">'
            f'EVENTS ({len(events)})</div>'
            '<table class="pp-audit__log">'
            '<thead><tr><th>timestamp</th><th>action</th><th>prior</th>'
            '<th>new</th><th>actor</th><th>notes</th></tr></thead>'
            f'<tbody>{ "".join(log_rows) }</tbody>'
            '</table>'
        )
    else:
        log_html = '<div class="pp-audit__empty">No audit events recorded for this sentence yet.</div>'

    return (
        '<div id="pp-audit-pane" class="pp-audit">'
        '<div class="pp-audit__head">AUDIT LOG · '
        f'<code>{esc(active_sentence)}</code></div>'
        f'{diff_html}'
        f'{log_html}'
        '</div>'
    )


def _pp_v2_sse_events(data: dict, signals: dict, payload_nav: str | None):
    """Wave 10d v2 SSE handler — emits banner + coverage + 3-column body."""
    # Tell the template we're in v2 mode so it adds ``pp-split--v2`` to
    # the body grid (3-column layout).
    if (signals.get('schemaMode') or 'v1') != 'v2':
        yield SSE.patch_signals({'schemaMode': 'v2'})

    new_active, new_link_idx = _pp_v2_apply_nav(data, signals, payload_nav)
    if new_active != (signals.get('activeSentence') or ''):
        yield SSE.patch_signals({'activeSentence': new_active})
    raw_link = signals.get('activeLinkIdx', -1)
    cur_link_idx = int(raw_link) if raw_link is not None and raw_link != '' else -1
    if new_link_idx != cur_link_idx:
        yield SSE.patch_signals({'activeLinkIdx': new_link_idx})

    gate_filter = signals.get('gateFilter') or ''

    yield SSE.patch_elements(_pp_banner_html(data))
    yield SSE.patch_elements(_pp_v2_coverage_ribbon_html(data))
    yield SSE.patch_elements(_pp_v2_paper_body_html(data, new_active, gate_filter))
    yield SSE.patch_elements(_pp_v2_sentence_inspector_html(data, new_active))
    yield SSE.patch_elements(_pp_v2_chain_inspector_html(data, new_active, new_link_idx))
    yield SSE.patch_elements(_pp_v2_audit_log_html(data, new_active))


def _pp_sse_events(data: dict, signals: dict, payload_nav: str | None):
    # Wave 10d v2 — sentence-keyed schema gets the 3-column layout
    if data.get('schema_version') == 'v2':
        yield from _pp_v2_sse_events(data, signals, payload_nav)
        return

    # v1 (legacy 8-layer dossier) flow.
    # Reset schemaMode so the template flips back to 2-column when the
    # user switches from a v2 paper to a v1 paper.
    if (signals.get('schemaMode') or 'v1') != 'v1':
        yield SSE.patch_signals({'schemaMode': 'v1'})

    new_active = _pp_apply_nav(data, signals, payload_nav)
    filter_layers = list(signals.get('filterLayers') or [])

    # Patch signals: sync activeClaim if server changed it via a nav hint
    if new_active != (signals.get('activeClaim') or ''):
        yield SSE.patch_signals({'activeClaim': new_active})

    yield SSE.patch_elements(_pp_banner_html(data))
    yield SSE.patch_elements(_pp_filter_chips_html(data, filter_layers))
    yield SSE.patch_elements(_pp_nav_html(data, filter_layers, new_active))
    # Paper body with inline claim spans (v2 design, Wave 9h final pass).
    yield SSE.patch_elements(_pp_paper_body_html(data, new_active))
    # Right pane: dossier matrix if a claim is active, else the default
    # PROVENANCE DOSSIER view with blocking + non-blocking lists.
    if new_active and new_active in (data.get('claims') or {}):
        yield SSE.patch_elements(_pp_dossier_html(data, new_active))
    else:
        yield SSE.patch_elements(_pp_default_dossier_html(data))


@app.route("/api/papers/<paper_id>/provenance", methods=["GET", "POST"])
def api_paper_provenance(paper_id: str):
    """Per-claim 8-layer provenance dossier (Wave 9g; Datastar port Wave 9h).

    Auto-negotiates SSE vs JSON. SSE consumers drive the Paper Provenance
    tab via four signals: ``$activePaper``, ``$activeClaim``,
    ``$filterLayers`` (array of layer codes), and an optional ``nav``
    payload on the request (``'next' | 'prev' | 'FAIL' | 'WARN'``) that
    moves the active claim without the client needing the full claim
    list. JSON path unchanged from Wave 9g for backward compat.

    404 if paper_draft.tex doesn't exist. 200 with best-effort data if
    claims_review.json is missing (falls back to synthesising from live
    registries + graph state so the tab still works on newer papers).
    """
    data = _pp_build_data(paper_id)
    if data is None:
        return jsonify({'error': f'Unknown paper: {paper_id}'}), 404
    if is_datastar_request():
        signals = read_signals()
        # `nav` is passed as a URL query param (`?nav=next`) by both the
        # keyboard shortcuts and the prev/next/F/W buttons — uniform.
        payload_nav = request.args.get('nav')
        return sse_response(lambda: _pp_sse_events(data, signals, payload_nav))
    return jsonify(data)


def _qi_derive_severity(mix: dict | None) -> str:
    if not mix:
        return 'advisory'
    if mix.get('critical'):
        return 'critical'
    if mix.get('major'):
        return 'major'
    if mix.get('minor'):
        return 'minor'
    return 'advisory'


def _qi_summary_html(data: dict) -> str:
    items = data.get('items', [])
    open_n = sum(1 for i in items if i.get('status') == 'open')
    closed_n = len(items) - open_n
    by_gate = {}
    for it in items:
        g = it.get('gate_affected')
        by_gate[g] = by_gate.get(g, 0) + 1
    gate_count = len(by_gate)
    generated = esc(data.get('generated') or 'unknown')

    def fig(n: int, label: str, color: str) -> str:
        return (f'<div><div class="count" style="color:{color}">{n}</div>'
                f'<div>{esc(label)}</div></div>')

    return (
        '<div id="qi-summary" class="qi-summary">'
        + fig(len(items), 'QI items', '#3730a3')
        + fig(open_n, 'open', '#b45309')
        + fig(closed_n, 'closed', '#166534')
        + fig(gate_count, 'gates affected', '#475569')
        + fig(data.get('findings_total', 0), 'ReviewFindings source', '#6b7280')
        + f'<div style="margin-left:auto;color:var(--grey);font-size:0.8rem">Generator run: {generated}</div>'
        + '</div>'
    )


def _qi_items_html(data: dict, signals: dict) -> str:
    items = data.get('items', [])
    show_open_only = bool(signals.get('qiShowOpenOnly'))
    if not items:
        return ('<div id="qi-items" class="qi-items">'
                '<div class="qi-empty">No QI items yet — no cross-paper failure patterns detected.</div>'
                '</div>')
    filtered = [i for i in items if not show_open_only or i.get('status') == 'open']
    if not filtered:
        return ('<div id="qi-items" class="qi-items">'
                '<div class="qi-empty">No open items.</div>'
                '</div>')

    parts = ['<div id="qi-items" class="qi-items">']
    for item in filtered:
        sev = _qi_derive_severity(item.get('severity_mix'))
        status = esc(item.get('status') or 'open')
        status_color = '#166534' if item.get('status') == 'closed' else '#b45309'
        parts.append(f'<div class="qi-item severity-{esc(sev)}">')
        parts.append(
            '<h4><span>' + esc(item.get('pattern_summary', '?')) + '</span>'
            '<span class="qi-id">' + esc(item.get('id', '')) + '</span></h4>'
        )
        meta = [
            '<span class="qi-gate-pill">' + esc(item.get('gate_affected', '?')) + '</span>',
            f' <span>{item.get("occurrences", 0)} findings</span>',
            f'<span style="font-weight:600;color:{status_color}">status: {status}</span>',
            f'<span>first seen: {esc(item.get("first_observed") or "?")}</span>',
            f'<span>last seen: {esc(item.get("last_observed") or "?")}</span>',
        ]
        if item.get('owner'):
            meta.append(f'<span>owner: {esc(item["owner"])}</span>')
        if item.get('target_date'):
            meta.append(f'<span>target: {esc(item["target_date"])}</span>')
        parts.append('<div class="qi-meta">' + ''.join(meta) + '</div>')
        papers = item.get('affected_papers') or []
        if papers:
            # Wave 10g — each paper chip deep-links into Paper Provenance
            # with a gate filter so the user lands on the offending sentences.
            gate = item.get('gate_affected', '')
            chips = []
            for p in papers:
                href = f'/?tab=paper&paper={esc(p)}'
                if gate:
                    href += f'&filter=gate:{esc(gate)}'
                chips.append(
                    f'<a class="paper-chip qi-paper-link" '
                    f'href="{href}" '
                    f'title="Open {esc(p)} in Paper Provenance"'
                    f'>{esc(p)}</a>'
                )
            parts.append('<div class="qi-papers">' + ''.join(chips) + '</div>')
        rfs = item.get('representative_findings') or []
        if rfs:
            parts.append('<ul class="qi-findings">')
            for rf in rfs:
                label = esc(rf.get('label') or rf.get('id') or '?')
                file_s = rf.get('file')
                suffix = (f'<span style="color:#9ca3af"> ({esc(file_s)})</span>'
                          if file_s else '')
                parts.append(f'<li><span>{label}</span>{suffix}</li>')
            parts.append('</ul>')
        parts.append('</div>')
    parts.append('</div>')
    return ''.join(parts)


def _qi_build_data() -> dict:
    from datetime import datetime, timezone as _tz
    try:
        from qi_register import load_review_findings, cluster_findings
    except ImportError as exc:
        return {'error': f'qi_register unavailable: {exc}'}
    findings = load_review_findings()
    items = cluster_findings(findings)
    return {
        'findings_total': len(findings),
        'items': items,
        'generated': datetime.now(_tz.utc).isoformat(timespec='seconds'),
    }


def _qi_sse_events(data: dict, signals: dict):
    yield SSE.patch_elements(_qi_summary_html(data))
    yield SSE.patch_elements(_qi_items_html(data, signals))


@app.route("/api/qi")
def api_qi():
    """Stage 14 QI register (Phase 5v Wave 7b; Datastar port Wave 9h).

    Auto-negotiates SSE (Datastar) vs JSON (tests/scripts). Signals
    consumed: `qiShowOpenOnly` — boolean to filter closed items out.
    """
    data = _qi_build_data()
    if 'error' in data:
        return jsonify(data), 500
    if is_datastar_request():
        signals = read_signals()
        return sse_response(lambda: _qi_sse_events(data, signals))
    return jsonify(data)


# ── Readiness tab — shared metadata + SSE render helpers (Wave 9h) ──
#
# GATE_DEFS is the canonical list of the 11 readiness gates in display
# order. The Datastar-driven tab reads this from the server rather than
# duplicating it in JS (the previous port carried two parallel copies).

GATE_DEFS: list[tuple[str, int, str]] = [
    ('CitationIntegrity',       1, 'Cit'),
    ('CrossPaperConsistency',   1, 'XPaper'),
    ('ParameterProvenance',     1, 'Param'),
    ('ComputationCorrectness',  1, 'Comp'),
    ('LeanProofSubstance',      1, 'LeanP'),
    ('AssumptionDisclosure',    1, 'Assum'),
    ('NarrativeGrounding',      1, 'Narr'),
    ('ProductionRunHealth',     1, 'ProdRun'),
    ('NumericalFreshness',      2, 'Num'),
    ('FirstClaimVerification',  2, '1st'),
    ('FixPropagation',          2, 'Fix'),
]


def _readiness_build_data() -> dict:
    """Pull ReadinessGate nodes from the cached graph and shape into the
    {papers: [{paper, gates: [...]}], last_evaluated, ...} payload both
    SSE and JSON paths consume. Extracted so _readiness_sse_events can
    share it with the legacy JSON response."""
    from collections import defaultdict
    graph = get_cached_graph()
    gates = [n for n in graph.get('nodes', []) if n['type'] == 'ReadinessGate']
    if not gates:
        return {"papers": [], "last_evaluated": None,
                "error": "no ReadinessGate nodes"}
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
    return {
        'papers': papers,
        'last_evaluated': last_evaluated,
        'gate_count': sum(len(p['gates']) for p in papers),
    }


def _classify_paper(gate_states: list[str]) -> str:
    if any(s == 'blocked' for s in gate_states):
        return 'RED'
    if any(s != 'passed' for s in gate_states):
        return 'YELLOW'
    return 'GREEN'


def _paper_gate_list(paper: dict) -> list[dict]:
    """Normalize each paper to a 11-entry gate list in GATE_DEFS order."""
    by_gate = {g['gate']: g for g in paper['gates']}
    out = []
    for name, prio, _abbrev in GATE_DEFS:
        g = by_gate.get(name) or {
            'gate': name, 'priority': prio, 'state': 'open',
            'evidence': [], 'blockers': [], 'notes': '', 'last_evaluated': '',
        }
        out.append(g)
    return out


def _readiness_summary_html(data: dict) -> str:
    if 'error' in data:
        return (
            '<div id="readiness-summary-row" class="readiness-summary">'
            f'<div style="color:#721c24">Failed to load: {esc(data["error"])}</div>'
            '</div>'
        )
    counts = {'RED': 0, 'YELLOW': 0, 'GREEN': 0}
    for paper in data['papers']:
        states = [g['state'] for g in _paper_gate_list(paper)]
        counts[_classify_paper(states)] += 1
    last = esc(data.get('last_evaluated') or 'unknown')
    n = len(data['papers'])
    return (
        '<div id="readiness-summary-row" class="readiness-summary">'
        f'<div><div class="count" style="color:#155724">{counts["GREEN"]}</div><div>green</div></div>'
        f'<div><div class="count" style="color:#856404">{counts["YELLOW"]}</div><div>yellow</div></div>'
        f'<div><div class="count" style="color:#721c24">{counts["RED"]}</div><div>red</div></div>'
        f'<div style="margin-left:auto;color:var(--grey);font-size:0.8rem">{n} papers · last evaluated {last}</div>'
        '</div>'
    )


def _should_show_paper(paper: dict, state_filter: str | None, gate_filter: str | None) -> bool:
    gate_list = _paper_gate_list(paper)
    states = [g['state'] for g in gate_list]
    pstate = _classify_paper(states)
    if state_filter and pstate != state_filter:
        return False
    if gate_filter:
        g = next((gg for gg in gate_list if gg['gate'] == gate_filter), None)
        if not g or g['state'] == 'passed':
            return False
    return True


def _readiness_heatmap_html(data: dict, signals: dict) -> str:
    """Full heatmap table with header + priority row + body, filtered by signals.
    Morph target is <table id="readiness-heatmap">; we return the complete
    table so Datastar's morph preserves scroll state and cell outlines."""
    state_f = (signals.get('paperStateFilter') or '').upper() or None
    gate_f = signals.get('gateFilter') or None
    active_paper = signals.get('activePaper') or None
    active_gate = signals.get('activeGate') or None

    # Header row
    thead = ['<tr>',
             '<th class="paper-col">Paper</th>',
             '<th>State</th>']
    for name, prio, abbrev in GATE_DEFS:
        cls = 'gate-head' + (' filtered' if gate_f == name else '')
        expr = (
            f"$gateFilter=$gateFilter==='{name}'?'':'{name}'; "
            f"@get('/api/readiness')"
        )
        thead.append(
            f'<th class="{cls}" '
            f'title="{esc(name)} (P{prio}) — click to filter to papers failing this gate" '
            f'data-on:click="{esc(expr)}">{esc(abbrev)}</th>'
        )
    thead.append('</tr>')
    # Priority row
    thead.append('<tr><th class="paper-col"></th><th></th>')
    for _name, prio, _abbrev in GATE_DEFS:
        thead.append(f'<th class="priority-label">P{prio}</th>')
    thead.append('</tr>')

    # Body rows
    rows = []
    if 'papers' in data:
        visible = [p for p in data['papers'] if _should_show_paper(p, state_f, gate_f)]
        for paper in visible:
            gate_list = _paper_gate_list(paper)
            states = [g['state'] for g in gate_list]
            pstate = _classify_paper(states)
            passed = sum(1 for s in states if s == 'passed')
            paper_id = paper['paper']
            focused_cls = ' focused' if active_paper == paper_id else ''
            focus_expr = (
                f"$activePaper='{esc(paper_id)}'; $activeGate=''; @get('/api/readiness')"
            )
            rows.append(
                f'<tr><th class="paper-col{focused_cls}" '
                f'data-on:click="{esc(focus_expr)}">{esc(paper_id)}</th>'
                f'<td><span class="paper-state-{pstate}">{pstate}</span> '
                f'<span style="color:var(--grey);font-size:0.72rem">{passed}/11</span></td>'
            )
            for g in gate_list:
                is_focus_cell = (active_paper == paper_id and active_gate == g['gate'])
                cell_cls = 'gate-cell ' + g['state'] + (' active-focus' if is_focus_cell else '')
                cell_expr = (
                    f"$activePaper='{esc(paper_id)}'; "
                    f"$activeGate='{esc(g['gate'])}'; @get('/api/readiness')"
                )
                letter = g['state'][0].upper() if g['state'] else '?'
                title = f"{g['gate']} — {g['state']}"
                rows.append(
                    f'<td class="{cell_cls}" title="{esc(title)}" '
                    f'data-on:click="{esc(cell_expr)}">{esc(letter)}</td>'
                )
            rows.append('</tr>')

    return (
        '<table id="readiness-heatmap" class="readiness-heatmap">'
        '<thead>' + ''.join(thead) + '</thead>'
        '<tbody>' + ''.join(rows) + '</tbody>'
        '</table>'
    )


def _readiness_focus_html(data: dict, signals: dict) -> str:
    active_paper = signals.get('activePaper') or None
    active_gate = signals.get('activeGate') or None
    if not active_paper or 'papers' not in data:
        return (
            '<aside id="readiness-focus" class="focus-pane">'
            '<div class="placeholder">Click a paper name or a gate cell to see details.</div>'
            '</aside>'
        )
    paper = next((p for p in data['papers'] if p['paper'] == active_paper), None)
    if not paper:
        return (
            '<aside id="readiness-focus" class="focus-pane">'
            '<div class="placeholder">Paper not found.</div>'
            '</aside>'
        )
    gate_list = _paper_gate_list(paper)
    states = [g['state'] for g in gate_list]
    pstate = _classify_paper(states)
    passed = sum(1 for s in states if s == 'passed')

    # Wave 10g — deep link from readiness focus pane to Paper Provenance,
    # carrying the active gate as a filter so the Paper Provenance UI can
    # surface only the sentences that invoke the failed gate.
    pp_href = f'/?tab=paper&paper={active_paper}'
    if active_gate:
        pp_href += f'&filter=gate:{active_gate}'

    parts = [
        '<aside id="readiness-focus" class="focus-pane">',
        f'<h3>{esc(active_paper)}</h3>',
        '<div class="paper-meta">',
        f'<span class="paper-state-{pstate}">{pstate}</span> ',
        f'{passed}/11 gates passed',
        '</div>',
        f'<a class="readiness-pp-link" href="{esc(pp_href)}">'
        '→ Open in Paper Provenance'
        f'{(" · filter " + esc(active_gate)) if active_gate else ""}'
        '</a>',
    ]
    for g in gate_list:
        expanded = (g['state'] != 'passed') or (active_gate == g['gate'])
        row_cls = 'gate-row' + (' expanded' if expanded else '')
        toggle = (
            f"$activeGate=$activeGate==='{esc(g['gate'])}'?'':'{esc(g['gate'])}'; "
            f"@get('/api/readiness')"
        )
        chip = ('GREEN' if g['state'] == 'passed'
                else 'RED' if g['state'] == 'blocked' else 'YELLOW')
        parts.append(
            f'<div class="{row_cls}" data-on:click="{esc(toggle)}">'
            '<div class="gate-title">'
            f'<span style="font-size:0.85rem">P{g["priority"]} · {esc(g["gate"])}</span>'
            f'<span class="gate-chip paper-state-{chip}">{esc(g["state"])}</span>'
            '</div>'
        )
        if expanded:
            if g.get('notes'):
                parts.append(f'<div class="gate-notes">{esc(g["notes"])}</div>')
            if g.get('evidence'):
                parts.append('<div><strong style="font-size:0.75rem">Evidence</strong>'
                             '<ul class="evidence">')
                for e in g['evidence']:
                    parts.append(f'<li>{esc(e)}</li>')
                parts.append('</ul></div>')
            if g.get('blockers'):
                parts.append('<div><strong style="font-size:0.75rem">Blockers</strong>'
                             '<ul class="blockers">')
                for b in g['blockers']:
                    parts.append(f'<li>{esc(b)}</li>')
                parts.append('</ul></div>')
            if g.get('last_evaluated'):
                parts.append(
                    f'<div class="gate-notes">Last evaluated: {esc(g["last_evaluated"])}</div>'
                )
        parts.append('</div>')
    parts.append('</aside>')
    return ''.join(parts)


def _readiness_sse_events(data: dict, signals: dict):
    """Emit three morph targets in order: summary, heatmap, focus.
    Filter row is static HTML with Datastar attrs — no server emit needed.
    Datastar's morph is by id, so re-emitting idempotent fragments is cheap."""
    yield SSE.patch_elements(_readiness_summary_html(data))
    yield SSE.patch_elements(_readiness_heatmap_html(data, signals))
    yield SSE.patch_elements(_readiness_focus_html(data, signals))


@app.route("/api/readiness")
def api_readiness():
    """Per-paper readiness gate data. Auto-negotiates SSE (Datastar) vs JSON.

    SSE path (Accept: text/event-stream): streams patch_elements for the
    four morph targets — summary, filters, heatmap, focus — with filter
    state taken from client-provided Datastar signals. See Wave 9h.

    JSON path: unchanged from Wave 5a — preserved for tests + scripts.
    """
    data = _readiness_build_data()
    if is_datastar_request():
        signals = read_signals()
        return sse_response(lambda: _readiness_sse_events(data, signals))
    return jsonify(data)


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
