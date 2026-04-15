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

sys.path.insert(0, str(PROJECT_ROOT))
sys.path.insert(0, str(SCRIPT_DIR))

from paper_tables import render_table  # noqa: E402


def discover_specs() -> dict[str, dict]:
    """Discover every papers/<paper_key>/tables.py + load its TABLES dict.

    Returns: {paper_key: {table_id: spec}}.
    """
    specs: dict[str, dict] = {}
    if not PAPERS_DIR.exists():
        return specs
    for tables_py in sorted(PAPERS_DIR.glob('paper*_*/tables.py')):
        paper_key = tables_py.parent.name
        module_name = f'_paper_tables_{paper_key}'
        spec = importlib.util.spec_from_file_location(module_name, tables_py)
        if spec is None or spec.loader is None:
            print(f'Warning: could not load {tables_py}', file=sys.stderr)
            continue
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        tables = getattr(module, 'TABLES', None)
        if not isinstance(tables, dict):
            print(f'Warning: {tables_py} has no TABLES dict', file=sys.stderr)
            continue
        specs[paper_key] = tables
    return specs


def render_paper(paper_key: str, paper_specs: dict) -> list[Path]:
    """Render every spec in `paper_specs` and return the paths written."""
    out_dir = PAPERS_DIR / paper_key / 'tables'
    out_dir.mkdir(parents=True, exist_ok=True)
    written: list[Path] = []
    for table_id, spec in paper_specs.items():
        try:
            content = render_table(spec)
        except Exception as exc:
            print(f'ERROR: {paper_key}:{table_id} failed: {exc}', file=sys.stderr)
            continue
        out_path = out_dir / f'{table_id}.tex'
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
            for table_id, spec in specs[paper_key].items():
                desc = spec.get('description', '')
                print(f'  - {table_id}' + (f'  — {desc}' if desc else ''))
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
