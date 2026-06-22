#!/usr/bin/env python3
"""Atlas heatmap — a glanceable Markdown surface of the derived proof-atlas (ADR-005 Phase 3).

Renders ``atlas_view.build_atlas()`` into ``docs/ATLAS_HEATMAP.md``: the proof landscape
(TRUE / OBSTRUCTION / open), the open frontier grouped by TRACK ("separate areas"), the headline
apexes, and the most-gating open assumptions. Dependency-free — no DB, no dashboard server — so it
is a committed, diff-able surface regenerated on demand (``--write``) or via ``/sync``. The atlas is
a VIEW (``scripts/atlas_view.py``); this is purely its presentation, adds no state, and reads
``lean_deps.json`` directly (never triggers re-extraction).
"""

from __future__ import annotations

import pathlib
import sys

PROJECT_ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "scripts"))
sys.path.insert(0, str(PROJECT_ROOT))
import atlas_view  # noqa: E402

HEATMAP_PATH = PROJECT_ROOT / "docs" / "ATLAS_HEATMAP.md"
_TOP_FRONTIER = 15


def render(atlas: dict) -> str:
    """Pure: derived-atlas dict → Markdown string. Deterministic (atlas is sorted)."""
    s = atlas["summary"]
    bks = s["by_kind_status"]
    proved = bks.get("TRUE:PROVED", 0)
    obstruction = bks.get("OBSTRUCTION:OBSTRUCTION", 0)
    out: list[str] = []
    out.append("# Atlas Heatmap — derived proof-landscape surface (ADR-005 Phase 3)")
    out.append("")
    out.append("> **Auto-generated** by `scripts/atlas_heatmap.py` from `atlas_view.build_atlas()` — a "
               "VIEW over `lean_deps.json` ∪ `HYPOTHESIS_REGISTRY`. Do not hand-edit; regenerate with "
               "`uv run python scripts/atlas_heatmap.py --write`.")
    out.append("")
    out.append(f"_Source: {s['theorem_nodes']} theorem nodes, {s['unknown_nodes']} tracked open "
               f"assumptions, {s['implies_edges']} IMPLIES edges._")
    out.append("")

    out.append("## Landscape")
    out.append("")
    out.append("| | count |")
    out.append("|---|---:|")
    out.append(f"| ✅ TRUE (proved) | {proved} |")
    out.append(f"| ⛔ OBSTRUCTION (no-go) | {obstruction} |")
    out.append(f"| ❓ open (tracked assumptions) | {s['unknown_nodes']} |")
    out.append(f"| ★ apex (headline open targets) | {s['apex_nodes']} |")
    out.append("")

    out.append('## Open frontier by track ("separate areas")')
    out.append("")
    out.append("Each open assumption belongs to a TRACK (`tier`); `gating` is the Σ of how many decls "
               "each node in the track immediately gates (reverse proof-dep edges).")
    out.append("")
    out.append("| track | open | gating (Σ impact) | apex |")
    out.append("|---|---:|---:|---:|")
    for t, tr in atlas["tracks"].items():
        out.append(f"| `{t}` | {tr['open_count']} | {tr['total_impact']} | {tr['apex_count'] or ''} |")
    out.append("")

    out.append("## Apex (headline) targets")
    out.append("")
    apex_rows = [f for f in atlas["frontier"] if f["is_apex"]]
    if apex_rows:
        out.append("| target | eliminability | gating |")
        out.append("|---|---|---:|")
        for f in apex_rows:
            out.append(f"| `{f['id']}` | {f['eliminability']} | {f['frontier_impact']} |")
    else:
        out.append("_(none)_")
    out.append("")

    out.append(f"## Most-gating open assumptions (top {_TOP_FRONTIER})")
    out.append("")
    out.append('"Which open node, if discharged, unlocks the most." Swarm schedulers read this '
               "frontier (from `lean/atlas_view.json`, DB-free) to fan out provable work — ADR-005 D-I.")
    out.append("")
    out.append("| gating | open node | track | eliminability | status |")
    out.append("|---:|---|---|---|---|")
    for f in atlas["frontier"][:_TOP_FRONTIER]:
        star = " ★" if f["is_apex"] else ""
        out.append(f"| {f['frontier_impact']} | `{f['id']}`{star} | {f['tier']} | "
                   f"{f['eliminability']} | {f['status']} |")
    out.append("")
    return "\n".join(out) + "\n"


def main(argv: list[str] | None = None) -> int:
    import argparse
    ap = argparse.ArgumentParser(description="Atlas heatmap surface (ADR-005 Phase 3).")
    ap.add_argument("--write", action="store_true", help=f"write {HEATMAP_PATH}")
    a = ap.parse_args(argv)
    md = render(atlas_view.build_atlas(atlas_view.load_lean_deps_file()))
    if a.write:
        HEATMAP_PATH.write_text(md)
        print(f"wrote {HEATMAP_PATH}")
    else:
        sys.stdout.write(md)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
