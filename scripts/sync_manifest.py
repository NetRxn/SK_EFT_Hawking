#!/usr/bin/env python3
"""L0 — the sync manifest: the single declarative table of mechanical
(input → output, regen-cmd, staleness) edges. Generalizes the three
staleness detectors that already exist (counts_fresh, the extract_lean_deps
hash, tables_fresh, inventory_index_autogen_fresh) so nothing hard-codes a
dependency edge twice. Read by sync.py (L3) and pre-commit-sync.sh (L2).

Stdlib only. `--check` prints stale outputs and exits 1 if any are stale.
"""
from __future__ import annotations
import argparse
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

SCRIPT_DIR = Path(__file__).resolve().parent
ROOT = SCRIPT_DIR.parent
LEAN = ROOT / "lean"


@dataclass(frozen=True)
class Edge:
    output: str                 # human label / path of the derived artifact
    inputs_glob: str            # what it derives from (doc only; staleness is is_stale)
    regen_cmd: list[str]        # argv to regenerate (run from ROOT)
    is_stale: Callable[[], bool]
    cost: str                   # "cheap" (ms–s) or "heavy" (clean build / ExtractDeps / network)


def _lean_deps_stale() -> bool:
    """True if the .lean hash differs from the cached lean_deps.json.hash."""
    sys.path.insert(0, str(SCRIPT_DIR))
    try:
        import extract_lean_deps as eld
        hp = LEAN / "lean_deps.json.hash"
        if not (LEAN / "lean_deps.json").exists() or not hp.exists():
            return True
        return eld.compute_lean_hash() != hp.read_text().strip()
    except Exception:
        return True  # fail-stale (safe): a broken detector flags for regen, never silently passes


def _counts_stale() -> bool:
    sys.path.insert(0, str(SCRIPT_DIR))
    try:
        import validate
        stale, _ = validate._counts_is_stale()
        return bool(stale)
    except Exception:
        return True


def _tables_stale() -> bool:
    sys.path.insert(0, str(SCRIPT_DIR))
    try:
        import validate
        # tables_fresh exposes a staleness helper analogous to _counts_is_stale;
        # if the symbol name differs, adapt here (single point of truth).
        return bool(validate._tables_is_stale()[0])
    except Exception:
        return True


def _index_autogen_stale() -> bool:
    sys.path.insert(0, str(SCRIPT_DIR))
    try:
        from update_inventory_index import compute_stale
        return bool(compute_stale()[0])
    except Exception:
        return True


def _atlas_view_stale() -> bool:
    """True if lean/atlas_view.json differs from a fresh build (ADR-005). Content-compare against the
    serialization `--write` would emit, so it catches ANY input change (lean_deps.json OR the
    HYPOTHESIS_REGISTRY) — the atlas is a derived VIEW, kept consistent with the committed
    lean_deps.json (read directly; no extraction)."""
    sys.path.insert(0, str(SCRIPT_DIR))
    try:
        import json as _json
        import atlas_view
        p = LEAN / "atlas_view.json"
        if not p.exists():
            return True
        fresh = _json.dumps(atlas_view.build_atlas(atlas_view.load_lean_deps_file()), indent=2)
        return fresh != p.read_text()
    except Exception:
        return True  # fail-stale (safe)


def _atlas_heatmap_stale() -> bool:
    """True if docs/ATLAS_HEATMAP.md differs from a fresh render (ADR-005 Phase 3). Same content-compare
    contract as `_atlas_view_stale`."""
    sys.path.insert(0, str(SCRIPT_DIR))
    try:
        import atlas_heatmap
        import atlas_view
        p = ROOT / "docs" / "ATLAS_HEATMAP.md"
        if not p.exists():
            return True
        fresh = atlas_heatmap.render(atlas_view.build_atlas(atlas_view.load_lean_deps_file()))
        return fresh != p.read_text()
    except Exception:
        return True


UV = ["uv", "run", "python"]

EDGES: list[Edge] = [
    Edge("lean/lean_deps.json", "lean/**/*.lean",
         UV + ["scripts/extract_lean_deps.py"], _lean_deps_stale, "heavy"),
    Edge("docs/counts.json + docs/counts.tex", "lean/**/*.lean, src/**",
         UV + ["scripts/update_counts.py"], _counts_stale, "heavy"),
    Edge("papers/*/tables/*.tex", "papers/*/tables.py, lean/lean_deps.json",
         UV + ["scripts/render_paper_tables.py"], _tables_stale, "cheap"),
    Edge("SK_EFT_Hawking_Inventory_Index.md (autogen blocks)", "docs/counts.json",
         UV + ["scripts/update_inventory_index.py"], _index_autogen_stale, "cheap"),
    # ADR-005 atlas surfaces — derived from lean_deps.json ∪ HYPOTHESIS_REGISTRY; cheap (no extraction).
    Edge("lean/atlas_view.json", "lean/lean_deps.json, src/core/constants.py (HYPOTHESIS_REGISTRY)",
         UV + ["scripts/atlas_view.py", "--write"], _atlas_view_stale, "cheap"),
    Edge("docs/ATLAS_HEATMAP.md", "lean/lean_deps.json, src/core/constants.py (HYPOTHESIS_REGISTRY)",
         UV + ["scripts/atlas_heatmap.py", "--write"], _atlas_heatmap_stale, "cheap"),
]


def stale_artifacts(cheap_only: bool = False) -> list[str]:
    return [e.output for e in EDGES
            if (not cheap_only or e.cost == "cheap") and e.is_stale()]


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="L0 sync manifest staleness report.")
    ap.add_argument("--check", action="store_true", help="exit 1 if any artifact is stale")
    ap.add_argument("--cheap-only", action="store_true", help="restrict to cheap edges")
    a = ap.parse_args(argv)
    stale = stale_artifacts(cheap_only=a.cheap_only)
    if stale:
        print("STALE: " + ", ".join(stale))
        return 1 if a.check else 0
    print("FRESH: all mechanical artifacts up-to-date")
    return 0


if __name__ == "__main__":
    sys.exit(main())
