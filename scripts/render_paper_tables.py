#!/usr/bin/env python3
"""Render paper tables from per-paper `tables.py` specs (Phase 5v).

Discovers every `papers/<paper_key>/tables.py` file, loads its `TABLES`
dict, renders each spec to a LaTeX tabular block, writes output to
`papers/<paper_key>/tables/<spec_id>.tex` (paper-readable `\\input{}`
target).

Usage:
    # Regenerate every paper's tables
    uv run python scripts/render_paper_tables.py

    # Regenerate a single paper
    uv run python scripts/render_paper_tables.py --paper paper1_first_order

    # List discovered specs
    uv run python scripts/render_paper_tables.py --list
"""

from __future__ import annotations

import argparse
import importlib.util
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
PAPERS_DIR = PROJECT_ROOT / 'papers'
SCRIPT_DIR = Path(__file__).resolve().parent

# Standardize on `scripts.paper_tables` as the canonical import path so
# paper specs and this renderer see the same `Span` / `Col` class
# objects. Earlier versions added SCRIPT_DIR to sys.path which allowed
# `from paper_tables import ...` — that created a second module copy
# and broke `isinstance(value, Span)` checks in `render_table`.
sys.path.insert(0, str(PROJECT_ROOT))

from scripts.paper_tables import render_table  # noqa: E402


def iter_spec_paths(papers_dir: Path | None = None) -> list[Path]:
    """Every ``papers/<key>/tables.py`` that exists, in render order.

    ⚠️ Bundle directories are named by CODE (I1, D3, L2, E1, D12), not
    `paperNN_*`, so globbing `paper*_*` alone made them undiscoverable — while
    `validate.py --check bundle_tables_use_pipeline` tells those very bundles to
    "add a papers/<X>/tables.py spec and render with render_paper_tables.py".
    The check demanded a remedy this discovery could not perform. Both shapes
    now resolve; discovery is by the PRESENCE of tables.py, not by the
    directory's naming convention.

    ⚠️ **This is the SINGLE OWNER of the spec population.** `tables_fresh`
    imports it rather than re-globbing, because a freshness guard that computes
    its own population can share a blind spot with the generator it watches and
    then report "fresh" over files neither one reads. That is exactly what
    happened for D12: this function resolved bundle specs, the check's private
    `paper*_*` glob did not, so a bundle spec would have been rendered and never
    guarded.
    """
    root = PAPERS_DIR if papers_dir is None else papers_dir
    if not root.exists():
        return []
    return sorted(root.glob('paper*_*/tables.py')) + sorted(
        d / 'tables.py' for d in root.iterdir()
        if d.is_dir() and not d.name.startswith('paper') and (d / 'tables.py').exists())


def spec_output_paths(tables_py: Path) -> list[Path]:
    """The `.tex` files ``tables_py`` is responsible for producing.

    ⚠️ This is deliberately **not** ``(dir/'tables').glob('*.tex')``. A
    `tables/` directory can hold an ORPHAN output whose spec entry no longer
    exists (`papers/I1/tables/table1_stages.tex` is one today). An orphan can
    never be regenerated, so a freshness comparison that includes it is
    permanently and unfixably stale — it reports a defect no regeneration run
    can clear. The freshness relation is spec → output; a file with no spec is
    outside it. Consumers wanting orphan detection should diff this against the
    directory listing, which is a different question from staleness.

    ⚠️ FAIL-CLOSED FALLBACK: when the spec will not load we cannot know what it
    owns, so we return the whole output directory rather than nothing. Returning
    nothing would report "a spec with no outputs" and mask a genuinely stale
    set; returning everything can only over-report staleness, which is the safe
    direction for a freshness guard.
    """
    out_dir = tables_py.parent / 'tables'
    ids = _spec_ids(tables_py)
    if ids is None:
        return sorted(out_dir.glob('*.tex'))
    return [out_dir / f'{i}.tex' for i in ids]


def _spec_ids(tables_py: Path) -> list[str] | None:
    """Declared TABLES + SCALARS ids of one spec, or None if it will not load."""
    loaded = _load_spec(tables_py, strict=False)
    if loaded is None:
        return None
    return list(loaded['tables']) + list(loaded['scalars'])


def _load_spec(tables_py: Path, *, strict: bool = True) -> dict | None:
    """Exec one ``tables.py`` and return ``{'tables': ..., 'scalars': ...}``.

    ``strict`` controls what a spec that RAISES does. The renderer wants the
    traceback (a broken spec must not be silently skipped, or the paper keeps
    typesetting a stale table). Read-only callers that only want to know which
    files a spec owns want a `None` they can fall back from, because crashing
    `validate.py` on someone else's broken spec turns one paper's defect into a
    whole-suite outage.
    """
    paper_key = tables_py.parent.name
    module_name = f'_paper_tables_{paper_key}'
    spec = importlib.util.spec_from_file_location(module_name, tables_py)
    if spec is None or spec.loader is None:
        print(f'Warning: could not load {tables_py}', file=sys.stderr)
        return None
    module = importlib.util.module_from_spec(spec)
    try:
        spec.loader.exec_module(module)
    except Exception as exc:
        if strict:
            raise
        print(f'Warning: {tables_py} raised on import: {exc!r}', file=sys.stderr)
        return None
    tables = getattr(module, 'TABLES', None) or {}
    scalars = getattr(module, 'SCALARS', None) or {}
    if not isinstance(tables, dict) or not isinstance(scalars, dict):
        print(f'Warning: {tables_py} TABLES/SCALARS not dicts', file=sys.stderr)
        return None
    if not tables and not scalars:
        print(f'Warning: {tables_py} has no TABLES or SCALARS dict', file=sys.stderr)
        return None
    return {'tables': tables, 'scalars': scalars}


def discover_specs() -> dict[str, dict]:
    """Discover every papers/<paper_key>/tables.py + load TABLES + SCALARS.

    Returns: ``{paper_key: {'tables': {id: spec}, 'scalars': {id: spec}}}``.
    """
    specs: dict[str, dict] = {}
    if not PAPERS_DIR.exists():
        return specs
    for tables_py in iter_spec_paths():
        loaded = _load_spec(tables_py)
        if loaded is None:
            continue
        specs[tables_py.parent.name] = loaded
    return specs


def _render_scalar(spec: dict) -> str:
    """Render a SCALARS spec to a single-line `.tex` snippet (no envelope).

    Suitable for in-equation `\\input{}` substitution. Header lines are
    LaTeX comments so the rendered file remains a drop-in replacement
    for an inline literal.
    """
    desc = spec.get('description', '')
    value_fn = spec['value']
    rendered = value_fn() if callable(value_fn) else str(value_fn)
    lines = []
    lines.append('% AUTOGENERATED by scripts/render_paper_tables.py — do not edit by hand.')
    lines.append('% Regenerate via `uv run python scripts/render_paper_tables.py` after')
    lines.append('% changing any source data or the paper\'s tables.py SCALARS spec.')
    if desc:
        lines.append(f'% Description: {desc}')
    lines.append(rendered)
    return '\n'.join(lines) + '\n'


def render_paper(paper_key: str, paper_specs: dict) -> list[Path]:
    """Render every spec in `paper_specs` and return the paths written."""
    out_dir = PAPERS_DIR / paper_key / 'tables'
    out_dir.mkdir(parents=True, exist_ok=True)
    written: list[Path] = []
    tables = paper_specs.get('tables', {})
    scalars = paper_specs.get('scalars', {})
    for table_id, spec in tables.items():
        try:
            content = render_table(spec)
        except Exception as exc:
            print(f'ERROR: {paper_key}:{table_id} failed: {exc}', file=sys.stderr)
            continue
        out_path = out_dir / f'{table_id}.tex'
        out_path.write_text(content)
        written.append(out_path)
    for scalar_id, spec in scalars.items():
        try:
            content = _render_scalar(spec)
        except Exception as exc:
            print(f'ERROR: {paper_key}:{scalar_id} (scalar) failed: {exc}',
                  file=sys.stderr)
            continue
        out_path = out_dir / f'{scalar_id}.tex'
        out_path.write_text(content)
        written.append(out_path)
    return written


def main() -> int:
    ap = argparse.ArgumentParser(description='Render paper tables from specs.')
    ap.add_argument('--paper', metavar='KEY',
                    help='Render only this paper (e.g. paper1_first_order)')
    ap.add_argument('--list', action='store_true',
                    help='List discovered specs without rendering')
    args = ap.parse_args()

    specs = discover_specs()

    if args.list:
        if not specs:
            print('No tables.py specs found under papers/')
            return 0
        for paper_key in sorted(specs):
            print(f'{paper_key}:')
            for table_id, spec in specs[paper_key].get('tables', {}).items():
                desc = spec.get('description', '')
                print(f'  [table]  {table_id}' + (f'  — {desc}' if desc else ''))
            for scalar_id, spec in specs[paper_key].get('scalars', {}).items():
                desc = spec.get('description', '')
                print(f'  [scalar] {scalar_id}' + (f'  — {desc}' if desc else ''))
        return 0

    if args.paper:
        if args.paper not in specs:
            print(f'ERROR: no tables.py found for {args.paper}', file=sys.stderr)
            return 1
        written = render_paper(args.paper, specs[args.paper])
        for p in written:
            print(f'  wrote {p.relative_to(PROJECT_ROOT)}')
        print(f'{len(written)} table(s) rendered for {args.paper}')
        return 0

    total = 0
    for paper_key in sorted(specs):
        written = render_paper(paper_key, specs[paper_key])
        for p in written:
            print(f'  wrote {p.relative_to(PROJECT_ROOT)}')
        total += len(written)
    print(f'{total} table(s) rendered across {len(specs)} paper(s)')
    return 0


if __name__ == '__main__':
    sys.exit(main())
