"""Row-generator functions for paper table autogen (Phase 5v).

Each source function returns a list of dicts ready for render. Values in
the dicts are pre-formatted strings (each physics quantity chooses its
natural precision); the rendering engine just handles column layout.

Sources grow as new data shapes are needed. Papers reference these from
their `tables.py` specs:

    from scripts.paper_tables.sources import platform_rows
    TABLES = {'tab1': {'rows': lambda: platform_rows(['Steinhauer', 'Heidelberg']), ...}}
"""

from __future__ import annotations

from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent


# Platform → BECParameters factory. Defined at module scope so papers
# can discover available platforms without importing all physics code.
_PLATFORM_FACTORIES = {
    'Steinhauer': 'steinhauer_Rb87',
    'Heidelberg': 'heidelberg_K39',
    'Trento':     'trento_spin_sonic',
}


def _format_sci(x: float, precision: int = 1) -> str:
    """LaTeX-friendly scientific notation for small values."""
    if x == 0:
        return '0'
    mantissa_exp = f'{x:.{precision}e}'
    mantissa, exp = mantissa_exp.split('e')
    exp_int = int(exp)
    return f'${mantissa} \\times 10^{{{exp_int}}}$'


def lean_module_summary(modules: list[str],
                        columns: tuple[str, ...] = ('theorems', 'aristotle', 'sorry')) -> list[dict]:
    """Per-Lean-module theorem/axiom/sorry counts for paper formalization
    summary tables.

    `modules` is a list of short module names (without the `SKEFTHawking.`
    prefix) that the paper wants to surface. `columns` selects which
    count fields to include in each row.

    Rows returned: one dict per module with these available fields:
        module        — short module name
        long_name     — 'SKEFTHawking.<module>'
        theorems      — count of theorem declarations in the module
        aristotle     — count registered in ARISTOTLE_THEOREMS
        sorry         — count of declarations with sorry axiom deps
        axioms        — count of axiom declarations
        definitions   — count of def declarations
        summary       — human-readable "Name.lean (N thms [, status])"

    Plus a terminal 'Total' row summing across the selected modules.
    """
    import json as _json
    from src.core.constants import ARISTOTLE_THEOREMS

    lean_deps_path = PROJECT_ROOT / "lean" / "lean_deps.json"
    data = []
    if lean_deps_path.exists():
        try:
            data = _json.loads(lean_deps_path.read_text())
        except Exception:
            data = []

    # Build per-module index
    by_module: dict[str, list[dict]] = {}
    for decl in data:
        mod = decl.get('module', '')
        short_mod = mod.replace('SKEFTHawking.', '', 1)
        by_module.setdefault(short_mod, []).append(decl)

    rows = []
    totals = {'theorems': 0, 'aristotle': 0, 'sorry': 0, 'axioms': 0, 'definitions': 0}
    for short_name in modules:
        decls = by_module.get(short_name, [])
        theorems = sum(1 for d in decls if d.get('kind') == 'theorem')
        axioms = sum(1 for d in decls if d.get('kind') == 'axiom')
        definitions = sum(1 for d in decls if d.get('kind') == 'def')
        sorry_count = sum(
            1 for d in decls
            if any('sorry' in str(a).lower() for a in d.get('axiom_deps_core', []))
        )
        aristotle_count = sum(
            1 for d in decls
            if d.get('kind') == 'theorem'
            and d.get('name', '').rsplit('.', 1)[-1] in ARISTOTLE_THEOREMS
        )
        totals['theorems'] += theorems
        totals['aristotle'] += aristotle_count
        totals['sorry'] += sorry_count
        totals['axioms'] += axioms
        totals['definitions'] += definitions

        summary_parts = [f'{theorems} thms']
        if aristotle_count:
            summary_parts.append(f'{aristotle_count} Aristotle')
        if sorry_count == 0:
            summary_parts.append('0 sorry')
        elif sorry_count > 0:
            summary_parts.append(f'{sorry_count} sorry')

        rows.append({
            'module':      short_name,
            'long_name':   f'SKEFTHawking.{short_name}',
            'file':        f'{short_name}.lean',
            'theorems':    str(theorems),
            'aristotle':   str(aristotle_count),
            'sorry':       str(sorry_count),
            'axioms':      str(axioms),
            'definitions': str(definitions),
            'summary':     f'{short_name}.lean ({", ".join(summary_parts)})',
        })

    # Total row
    rows.append({
        'module':      'Total',
        'long_name':   '',
        'file':        '',
        'theorems':    str(totals['theorems']),
        'aristotle':   str(totals['aristotle']),
        'sorry':       str(totals['sorry']),
        'axioms':      str(totals['axioms']),
        'definitions': str(totals['definitions']),
        'summary':     f'{len(modules)} modules, {totals["theorems"]} theorems, '
                       f'{totals["aristotle"]} Aristotle, {totals["sorry"]} sorry',
    })
    return rows


def pipeline_stages() -> list[dict]:
    """The 12 pipeline stages + their gates, parsed from
    `docs/WAVE_EXECUTION_PIPELINE.md`. Used by Paper 15 Table 1.

    Returns rows with: stage (number), name (stage name), gate (gate
    description text).
    """
    import re as _re
    pipeline_md = PROJECT_ROOT / "docs" / "WAVE_EXECUTION_PIPELINE.md"
    if not pipeline_md.exists():
        return []

    text = pipeline_md.read_text()
    # Parse the summary block "Stage N: NAME → Gate: ..."
    rows = []
    summary_re = _re.compile(
        r'Stage\s+(\d+[a-z]?)[:\s]+([A-Z][A-Z &—\-]+?)\s+→\s+Gate:\s+(.+)',
        _re.MULTILINE,
    )
    for m in summary_re.finditer(text):
        stage_num = m.group(1)
        name = m.group(2).strip().title().replace('Sk', 'SK')
        gate = m.group(3).strip()
        rows.append({
            'stage': stage_num,
            'name': name,
            'gate': gate,
        })
    return rows


def validation_checks() -> list[dict]:
    """The registered validate.py checks, parsed from
    `scripts/validate.py` `@register_check(name, description)` calls.
    Used by Paper 15 Table 2.

    Returns rows with: number, name, description.
    """
    import re as _re
    validate_py = PROJECT_ROOT / "scripts" / "validate.py"
    if not validate_py.exists():
        return []

    text = validate_py.read_text()
    # Match only DECORATOR usages (line starts with @register_check),
    # never examples inside docstrings or comments.
    pattern = _re.compile(
        r'^@register_check\(\s*"([^"]+)"\s*,\s*("(?:[^"\\]|\\.)*")\s*\)',
        _re.MULTILINE | _re.DOTALL,
    )
    rows = []
    for idx, m in enumerate(pattern.finditer(text), start=1):
        name = m.group(1)
        desc = m.group(2)[1:-1].replace('\\"', '"')
        rows.append({
            'number': str(idx),
            'name': f'\\texttt{{{name}}}',
            'description': desc,
        })
    return rows


def platform_rows(platforms: list[str]) -> list[dict]:
    """Per-parameter rows × per-platform columns for BEC analog Hawking
    experiments. One row per physics quantity; cells are formatted
    strings ready for LaTeX.

    Rows: c_s, ξ, κ, T_H, δ_diss
    Columns: (parameter, unit, <platform>, ...)

    Example: platform_rows(['Steinhauer', 'Heidelberg', 'Trento']) →
        [
          {'parameter': 'Speed of sound $c_s$', 'unit': 'mm/s',
           'Steinhauer': '0.55', 'Heidelberg': '3.92', 'Trento': '2.18'},
          {'parameter': 'Healing length $\\xi$', 'unit': '$\\mu$m',
           'Steinhauer': '1.33', 'Heidelberg': '0.42', 'Trento': '1.26'},
          ...
        ]
    """
    import src.core.transonic_background as tb
    from src.core.formulas import beliaev_transport_coefficients

    # Build per-platform BECParameters + TransonicBackground
    backgrounds: dict[str, tuple] = {}
    for p in platforms:
        factory_name = _PLATFORM_FACTORIES.get(p)
        if factory_name is None:
            raise ValueError(
                f"Unknown platform {p!r}. Known: "
                f"{sorted(_PLATFORM_FACTORIES)}. Register in "
                f"scripts/paper_tables/sources.py._PLATFORM_FACTORIES."
            )
        factory = getattr(tb, factory_name)
        params = factory()
        bg = tb.solve_transonic_background(params)
        backgrounds[p] = (params, bg)

    rows: list[dict] = []

    # c_s (mm/s)
    row = {'parameter': 'Speed of sound $c_s$', 'unit': 'mm/s'}
    for p in platforms:
        params, _bg = backgrounds[p]
        row[p] = f'{params.sound_speed_upstream * 1000:.2f}'
    rows.append(row)

    # ξ (μm)
    row = {'parameter': 'Healing length $\\xi$', 'unit': '$\\mu$m'}
    for p in platforms:
        params, _bg = backgrounds[p]
        row[p] = f'{params.healing_length * 1e6:.2f}'
    rows.append(row)

    # κ (s⁻¹)
    row = {'parameter': 'Surface gravity $\\kappa$', 'unit': 's$^{-1}$'}
    for p in platforms:
        _params, bg = backgrounds[p]
        row[p] = f'{bg.surface_gravity:.1f}'
    rows.append(row)

    # T_H (nK)
    row = {'parameter': 'Hawking temperature $T_H$', 'unit': 'nK'}
    for p in platforms:
        _params, bg = backgrounds[p]
        row[p] = f'{bg.hawking_temp * 1e9:.3f}'
    rows.append(row)

    # δ_diss (dimensionless, scientific notation)
    row = {'parameter': 'Dissipative correction $\\delta_{\\mathrm{diss}}$ (Beliaev, $T{=}0$)',
           'unit': '(dimensionless)'}
    for p in platforms:
        params, bg = backgrounds[p]
        xi = params.healing_length
        tc = beliaev_transport_coefficients(
            n_1D=params.density_upstream,
            a_s=params.scattering_length,
            kappa=bg.surface_gravity,
            c_s=params.sound_speed_upstream,
            xi=xi,
        )
        delta_diss = tb.compute_dissipative_correction(
            bg, params, tc['gamma_1'], tc['gamma_2'],
        )['delta_diss']
        row[p] = _format_sci(delta_diss, precision=1)
    rows.append(row)

    return rows
