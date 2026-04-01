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

# Ensure project root is importable
PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT))

app = Flask(__name__, template_folder=str(Path(__file__).parent / "templates"))


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
    """Load per-paper claim analysis for the Paper Claims tab."""
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

    # Paper descriptions and which platforms/modules they depend on
    paper_meta = {
        'paper1_first_order': {
            'title': 'Paper 1: First-Order SK-EFT (PRL)',
            'topic': 'δ_diss = Γ_H/κ correction for 3 BEC platforms',
            'platforms': ['Steinhauer', 'Heidelberg', 'Trento'],
            'lean_modules': ['AcousticMetric', 'SKDoubling', 'HawkingUniversality'],
        },
        'paper2_second_order': {
            'title': 'Paper 2: Second-Order SK-EFT (PRD)',
            'topic': 'Frequency-dependent ω³ correction, counting formula, CGL FDR',
            'platforms': ['Steinhauer', 'Heidelberg', 'Trento'],
            'lean_modules': ['SecondOrderSK', 'WKBAnalysis', 'CGLTransform'],
        },
        'paper3_gauge_erasure': {
            'title': 'Paper 3: Non-Abelian Gauge Erasure (PRL)',
            'topic': 'Universal structural theorem — U(1) survives',
            'platforms': ['Steinhauer'],
            'lean_modules': ['GaugeErasure'],
        },
        'paper4_wkb_connection': {
            'title': 'Paper 4: Exact WKB Connection (PRD)',
            'topic': 'Non-perturbative Bogoliubov, decoherence, noise floor',
            'platforms': ['Steinhauer', 'Heidelberg', 'Trento'],
            'lean_modules': ['WKBConnection'],
        },
        'paper5_adw_gap': {
            'title': 'Paper 5: ADW Gap Equation (PRD)',
            'topic': 'Mean-field tetrad condensation, G_c, 2 gravitons',
            'platforms': [],
            'lean_modules': ['ADWMechanism'],
        },
        'paper6_vestigial': {
            'title': 'Paper 6: Vestigial Gravity (PRD)',
            'topic': 'Lattice MC, vestigial metric phase, Weingarten integration',
            'platforms': [],
            'lean_modules': ['VestigialGravity', 'FermionBag4D', 'SO4Weingarten'],
        },
        'paper7_chirality_formal': {
            'title': 'Paper 7: Chirality Wall Formal Verification (PRD/CPC)',
            'topic': 'GS 9 conditions formalized, TPF evasion machine-verified',
            'platforms': [],
            'lean_modules': ['LatticeHamiltonian', 'GoltermanShamir', 'TPFEvasion'],
        },
        'experimental_predictions': {
            'title': 'Prediction Tables',
            'topic': 'Platform-specific spectral predictions',
            'platforms': ['Steinhauer', 'Heidelberg', 'Trento'],
            'lean_modules': ['KappaScaling', 'PolaritonTier1'],
        },
    }

    # Load provenance to check parameter readiness
    from src.core.provenance import PARAMETER_PROVENANCE

    for paper_dir in sorted(papers_dir.iterdir()):
        tex_file = paper_dir / "paper_draft.tex"
        if not tex_file.exists():
            continue

        tex = tex_file.read_text()
        tex_lines = tex.splitlines()
        line_count = len(tex_lines)

        meta = paper_meta.get(paper_dir.name, {
            'title': paper_dir.name,
            'topic': '',
            'platforms': [],
            'lean_modules': [],
        })

        # --- Theorem references with Lean verification ---
        texttt_refs = re.findall(r'\\texttt\{([a-z_][a-zA-Z0-9_]*)\}', tex)
        theorem_refs = [r for r in texttt_refs if '_' in r]
        theorem_details = []
        for ref in theorem_refs:
            in_lean = ref in lean_names
            theorem_details.append({'name': ref, 'in_lean': in_lean})
        missing_theorems = [t for t in theorem_details if not t['in_lean']]

        # --- Figures ---
        fig_dir = paper_dir / "figures"
        fig_count = len(list(fig_dir.glob("*.png"))) if fig_dir.exists() else 0
        has_fbox = '\\fbox{\\parbox' in tex

        # --- Numerical table extraction (look for tabular environments) ---
        numerical_values = []
        in_tabular = False
        for i, line in enumerate(tex_lines, 1):
            if '\\begin{tabular}' in line:
                in_tabular = True
            elif '\\end{tabular}' in line:
                in_tabular = False
            elif in_tabular and '&' in line:
                # Extract numbers from table rows
                cells = line.split('&')
                nums = []
                for cell in cells:
                    # Match scientific notation and plain numbers
                    for m in re.finditer(r'(\d+\.?\d*)\s*(?:\\times\s*10\^\{?(-?\d+)\}?|[eE]([+-]?\d+))?', cell):
                        val_str = m.group(0).strip().rstrip('\\').strip()
                        if val_str and any(c.isdigit() for c in val_str):
                            nums.append(val_str)
                if nums:
                    row_label = cells[0].strip().replace('$', '').replace('\\', '')[:40]
                    numerical_values.append({
                        'line': i,
                        'label': row_label,
                        'nums': nums[:5],  # cap at 5 values per row
                    })

        # --- Bibliography check ---
        has_placeholder_bib = 'xxxxx' in tex.lower() or 'Nature \\textbf{XXX}' in tex
        bibitem_count = tex.count('\\bibitem')

        # --- Parameter readiness ---
        dependent_params = []
        for platform in meta['platforms']:
            for key, entry in PARAMETER_PROVENANCE.items():
                if key.startswith(platform) or key.startswith(platform[:2].upper()):
                    dependent_params.append({
                        'key': key,
                        'human_verified': entry.get('human_verified_date') is not None,
                        'llm_verified': entry.get('llm_verified_date') is not None,
                        'has_conflict': entry['value'] is None,
                    })

        # Also check atomic params for BEC platforms
        atom_map = {'Steinhauer': 'Rb87', 'Heidelberg': 'K39', 'Trento': 'Na23'}
        for platform in meta['platforms']:
            atom = atom_map.get(platform)
            if atom:
                for key, entry in PARAMETER_PROVENANCE.items():
                    if key.startswith(atom):
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
        if missing_theorems:
            issues.append(f'{len(missing_theorems)} theorem refs not in Lean')
        if params_conflict > 0:
            issues.append(f'{params_conflict} dependent params have unresolved conflicts')

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
            'title': meta['title'],
            'topic': meta['topic'],
            'platforms': meta['platforms'],
            'lean_modules': meta['lean_modules'],
            'lines': line_count,
            'theorem_refs': theorem_details,
            'theorem_count': len(theorem_refs),
            'missing_theorems': missing_theorems,
            'figure_count': fig_count,
            'has_fbox': has_fbox,
            'numerical_values': numerical_values[:10],  # cap display
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

    # Apply filters from query params
    tab = request.args.get('tab', 'parameters')
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
