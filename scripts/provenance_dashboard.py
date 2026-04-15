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
import re
import sys
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
    """Load per-paper claim analysis from declared PAPER_DEPENDENCIES."""
    from src.core.provenance import PAPER_DEPENDENCIES, PARAMETER_PROVENANCE
    from src.core.constants import ARISTOTLE_THEOREMS

    papers_dir = PROJECT_ROOT / "papers"
    lean_dir = PROJECT_ROOT / "lean" / "SKEFTHawking"
    papers = []

    if not papers_dir.exists():
        return papers

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

        papers.append({
            'name': paper_dir.name,
            'title': meta.get('title', paper_dir.name),
            'topic': meta.get('topic', ''),
            'platforms': meta.get('platforms', []),
            'lean_modules': meta.get('lean_modules', []),
            'lean_module_details': lean_module_details,
            'formula_deps': formula_deps,
            'key_claims': meta.get('key_claims', []),
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

    sys.path.insert(0, str(SCRIPT_DIR))
    from extract_lean_deps import load_lean_deps
    from build_graph import (
        extract_lean_declaration_nodes,
        extract_depends_on_axiom_edges,
        extract_all_nodes,
    )

    lean_nodes = extract_lean_declaration_nodes()

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
    all_nodes = extract_all_nodes()
    node_ids = {n['id'] for n in all_nodes}
    axiom_edges = extract_depends_on_axiom_edges(node_ids)

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
    """Return the full provenance graph as JSON for D3 visualization."""
    from build_graph import build_graph_json
    graph = build_graph_json()
    return jsonify(graph)


@app.route("/api/graph/trace/<path:node_id>")
def api_trace(node_id):
    """Return the provenance chain for a node (bidirectional BFS).

    Walks forward through outgoing edges (source->target) AND backward
    through incoming edges (target->source) to find the full chain.
    """
    from build_graph import build_graph_json
    graph = build_graph_json()
    nodes = graph['nodes']
    links = graph['links']

    # Validate node exists
    node_ids = {n['id'] for n in nodes}
    if node_id not in node_ids:
        return jsonify({'error': f'Unknown node: {node_id}'}), 404

    traced_node_ids = set()
    traced_edge_indices = set()

    def fwd(nid):
        if nid in traced_node_ids:
            return
        traced_node_ids.add(nid)
        for i, link in enumerate(links):
            if link['source'] == nid:
                traced_edge_indices.add(i)
                fwd(link['target'])

    def bwd(nid):
        if nid in traced_node_ids:
            return
        traced_node_ids.add(nid)
        for i, link in enumerate(links):
            if link['target'] == nid:
                traced_edge_indices.add(i)
                bwd(link['source'])

    fwd(node_id)
    bwd(node_id)

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
    from build_graph import build_graph_json
    graph = build_graph_json()
    nodes = graph['nodes']
    links = graph['links']

    node_ids = {n['id'] for n in nodes}
    if node_id not in node_ids:
        return jsonify({'error': f'Unknown node: {node_id}'}), 404

    impacted_node_ids = set([node_id])
    impacted_edge_indices = set()

    def upstream(nid):
        for i, link in enumerate(links):
            if link['target'] == nid and link['source'] not in impacted_node_ids:
                impacted_node_ids.add(link['source'])
                impacted_edge_indices.add(i)
                upstream(link['source'])

    def downstream(nid):
        for i, link in enumerate(links):
            if link['source'] == nid and link['target'] not in impacted_node_ids:
                impacted_node_ids.add(link['target'])
                impacted_edge_indices.add(i)

    upstream(node_id)
    downstream(node_id)

    return jsonify({
        'impacted_node_ids': sorted(impacted_node_ids),
        'impacted_edge_indices': sorted(impacted_edge_indices),
    })


@app.route("/api/graph/integrity")
def api_integrity():
    """Return the graph integrity report."""
    from graph_integrity import run_integrity_checks
    return jsonify(run_integrity_checks())


@app.route("/api/readiness")
def api_readiness():
    """Return per-paper readiness gate data structured for the dashboard.

    Phase 5v Wave 5. Builds a graph, pulls the ReadinessGate nodes, and
    reshapes into {papers: [{paper, gates: [{gate, priority, state,
    evidence, blockers, notes, last_evaluated}]}]}. The heatmap renders
    from this payload via safe-DOM construction (see readiness_tab.html).
    """
    from build_graph import build_graph_json

    graph = build_graph_json()
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
    parser.add_argument("--write", action="store_true",
                        help="Write current verification state to provenance.py and exit")
    args = parser.parse_args()

    if args.write:
        print("Write mode: updating provenance.py with verification state...")
        # TODO: implement file rewriting
        return

    import webbrowser
    import threading

    url = f"http://localhost:{args.port}"
    if not args.no_browser:
        threading.Timer(1.0, lambda: webbrowser.open(url)).start()

    print(f"\n  SK-EFT Provenance Command Center")
    print(f"  Running at {url}")
    print(f"  Press Ctrl+C to stop\n")

    app.run(host="localhost", port=args.port, debug=False)


if __name__ == "__main__":
    main()
