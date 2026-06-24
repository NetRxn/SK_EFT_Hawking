#!/usr/bin/env python3
"""Derived Proof Atlas — the classification/frontier VIEW over the dependency graph (ADR-005).

Phase 1a (derive-only, zero attributes). The atlas is NOT a separate store: it is a projection
computed from artifacts the project already produces —
  * ``lean/lean_deps.json``     (declarations, kinds, axiom closures, proof-dep edges)
  * ``HYPOTHESIS_REGISTRY``     (tracked open assumptions — the UNKNOWN/open nodes)
  * ``AXIOM_METADATA``          (axiom ledger — feeds the AXIOM_TAINTED check)
  * the no-go naming convention (OBSTRUCTION nodes)

Node kinds (ADR-005 D-B), all DERIVED in this phase (no ``@[atlas_node]`` attribute yet):
  * TRUE        — a kernel-clean proved theorem (positive front)
  * OBSTRUCTION — a proved no-go / negation (negative front), by name/module/``¬``-head
  * UNKNOWN     — a tracked open assumption (from HYPOTHESIS_REGISTRY) / live axiom
  (EDGE — implication wiring — is deferred to Phase 2; it needs the attribute or type parsing.)

Status lattice (ADR-005 D-C), derived from the already-emitted axiom closure + sorry signal:
  PROVED · OBSTRUCTION · CONDITIONALLY_PROVED (rests on a ``sorry`` stub) ·
  AXIOM_TAINTED (rests on a project-local axiom — needs sign-off) · PLANNED/STATED (open).

This module is import-safe (``build_atlas`` is pure given its inputs) and has a CLI that writes
``lean/atlas_view.json`` + prints a summary. ``build_graph.py`` overlays the result onto the graph;
``validate.py --check atlas_integrity`` gates it.
"""
from __future__ import annotations

import collections
import json
import re
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
LEAN_DEPS_PATH = PROJECT_ROOT / "lean" / "lean_deps.json"
ATLAS_VIEW_PATH = PROJECT_ROOT / "lean" / "atlas_view.json"
# Boundary atlas: the GITIGNORED post-compaction freshness artifact (Live-Anchor Move 3). Written by
# `--write-boundary` so a hook/agent NEVER dirties the git-tracked ATLAS_VIEW_PATH (harness QI
# invariant: a hook MUST NOT write a tracked path). The live-anchor probe prefers it when fresher.
BOUNDARY_ATLAS_PATH = PROJECT_ROOT / ".claude" / "dev-harness" / "atlas_view.boundary.json"

# Kernel-trust baseline (ADR-002). A decl is kernel-pure iff its core axiom closure is a subset of
# these AND it carries no project-local axiom and no `sorryAx`.
KERNEL_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
_SORRY_AX = "sorryAx"

# OBSTRUCTION (no-go) detection by the project's naming convention (decl name or module) — the same
# suffixes validate.py's substance scan recognizes — plus a proved-negation type head.
_NOGO_RE = re.compile(
    r"(_no_go|_nogo|_refuted|_falsified|_obstruction|_forbidden|nogo|NoGo|Obstruction)"
)


# `native_decide` introduces a per-call-site compiler axiom `<decl>._native.native_decide.ax_*` in
# the SKEFTHawking package. These are ADR-002's policy-tolerated COMPILER-trust surface (tracked by
# `axiom_closure_allowlist`), NOT project axioms needing sign-off — they must NOT count as AXIOM_TAINTED.
_NATIVE_DECIDE_RE = re.compile(r"\._native\.native_decide")


def _has_sorry(rec: dict) -> bool:
    return any(_SORRY_AX in a for a in rec.get("axiom_deps_core", []))


def _genuine_project_axioms(rec: dict) -> list[str]:
    """Project-local axioms in the closure EXCLUDING native_decide compiler artifacts —
    i.e. genuine `axiom` declarations that need sign-off (ADR-005 D-F / Inv #15)."""
    return [a for a in rec.get("axiom_deps_project", []) if not _NATIVE_DECIDE_RE.search(a)]


def _uses_native_decide(rec: dict) -> bool:
    return any(_NATIVE_DECIDE_RE.search(a) for a in rec.get("axiom_deps_project", []))


def _is_kernel_pure(rec: dict) -> bool:
    """Strict kernel purity: core ⊆ {propext, Classical.choice, Quot.sound}, no genuine project
    axiom, no sorry, and no native_decide (native_decide is policy-OK but not strictly kernel-pure)."""
    core = set(rec.get("axiom_deps_core", []))
    return (not _genuine_project_axioms(rec) and not _uses_native_decide(rec)
            and core.issubset(KERNEL_AXIOMS) and not _has_sorry(rec))


def _is_obstruction(rec: dict) -> bool:
    if _NOGO_RE.search(rec.get("name", "")) or _NOGO_RE.search(rec.get("module", "")):
        return True
    t = (rec.get("type") or "").lstrip()
    return t.startswith("¬") or t.startswith("Not ") or t.startswith("Not(")


def classify_theorem(rec: dict) -> tuple[str, str]:
    """Return ``(atlas_kind, atlas_status)`` for a theorem record."""
    kind = "OBSTRUCTION" if _is_obstruction(rec) else "TRUE"
    if _genuine_project_axioms(rec):
        status = "AXIOM_TAINTED"   # genuine project axiom — atlas_integrity cross-refs AXIOM_METADATA
    elif _has_sorry(rec):
        status = "CONDITIONALLY_PROVED"
    elif kind == "OBSTRUCTION":
        status = "OBSTRUCTION"
    else:
        status = "PROVED"          # PROVED (modulo native_decide where the native_decide flag is set)
    return kind, status


def _hyp_status(h: dict) -> str:
    tier = (h.get("tier") or "").lower()
    status = (h.get("status") or "").lower()
    if "discharge_future" in tier or status.startswith("proposed"):
        return "PLANNED"
    return "STATED"


def build_atlas(lean_deps: list[dict], hyp_registry: dict | None = None,
                axiom_metadata: dict | None = None) -> dict:
    """Compute the derived atlas view. Pure given its inputs (registries default to the project's)."""
    if hyp_registry is None or axiom_metadata is None:
        sys.path.insert(0, str(PROJECT_ROOT))
        from src.core.constants import HYPOTHESIS_REGISTRY, AXIOM_METADATA  # noqa: E402
        hyp_registry = HYPOTHESIS_REGISTRY if hyp_registry is None else hyp_registry
        axiom_metadata = AXIOM_METADATA if axiom_metadata is None else axiom_metadata

    # frontier_impact = how many decls immediately depend on this one (reverse proof-dep edges).
    downstream: collections.Counter = collections.Counter()
    for r in lean_deps:
        for dep in r.get("name_deps_project", []):
            downstream[dep] += 1

    nodes: list[dict] = []
    counts: collections.Counter = collections.Counter()
    edges: list[dict] = []  # IMPLIES (assumption -> dependent theorem) edges; proof-dep USES edges
    # already live in build_graph from name_deps. Phase-1a IMPLIES edges = the hypothesis links.

    registered_fqns: set[str] = set()

    for r in lean_deps:
        if r.get("kind") != "theorem":
            continue  # defs/structures/instances are graph nodes but not atlas RESULT nodes in 1a
        ak, status = classify_theorem(r)
        fqn = r["name"]
        registered_fqns.add(fqn)
        nodes.append({
            "fqn": fqn,
            "module": r.get("module"),
            "atlas_kind": ak,
            "atlas_status": status,
            "kernel_pure": _is_kernel_pure(r),
            "native_decide": _uses_native_decide(r),
            "frontier_impact": int(downstream.get(fqn, 0)),
        })
        counts[f"{ak}:{status}"] += 1

    # UNKNOWN / open nodes from the tracked-hypothesis ledger (the open frontier).
    unknowns: list[dict] = []
    for key, h in hyp_registry.items():
        deps = list(h.get("dependent_theorems", []) or [])
        st = _hyp_status(h)
        node_id = f"hyp:{key}"
        tier = h.get("tier")
        unknowns.append({
            "id": node_id,
            "atlas_kind": "UNKNOWN",
            "atlas_status": st,
            "tier": tier,
            "eliminability": h.get("eliminability"),
            "module": h.get("module"),
            # is_apex: a HEADLINE-tier open target — the bit the D-E `@[atlas_node apex]` attribute was
            # to carry, but it is already structured in HYPOTHESIS_REGISTRY for open nodes (ADR-005 D-H).
            "is_apex": (tier == "headline"),
            "frontier_impact": len(deps),
            "dependent_theorems": deps,
        })
        counts[f"UNKNOWN:{st}"] += 1
        for d in deps:
            edges.append({"source": node_id, "type": "ASSUMED_BY", "target": d})

    # Frontier (Phase-1a sense): open assumptions ranked by how much they gate, highest first —
    # "which open node, if discharged, unlocks the most." Each entry carries its TRACK (`tier`) +
    # `eliminability` + `is_apex` so the frontier is navigable by workstream, not just a flat list
    # (ADR-005 D-H: the atlas serves "many open phases/waves working separate areas").
    frontier = sorted(
        ({"id": u["id"], "frontier_impact": u["frontier_impact"], "status": u["atlas_status"],
          "tier": u["tier"], "eliminability": u["eliminability"], "is_apex": u["is_apex"]}
         for u in unknowns),
        key=lambda x: (-x["frontier_impact"], x["id"]),
    )

    # Per-TRACK rollup (the "separate areas" view): one bucket per `tier`, soft "unclassified" for any
    # node lacking one (ADR-005 D-H — unclassified degrades softly, never a hard failure).
    tracks: dict[str, dict] = {}
    for u in unknowns:
        t = u["tier"] or "unclassified"
        tr = tracks.setdefault(t, {"open_count": 0, "total_impact": 0, "apex_count": 0, "node_ids": []})
        tr["open_count"] += 1
        tr["total_impact"] += u["frontier_impact"]
        tr["apex_count"] += 1 if u["is_apex"] else 0
        tr["node_ids"].append(u["id"])
    for tr in tracks.values():
        tr["node_ids"].sort()
    apex_ids = sorted(u["id"] for u in unknowns if u["is_apex"])

    return {
        "nodes": nodes,
        "unknowns": unknowns,
        "edges": edges,
        "frontier": frontier,
        "tracks": {t: tracks[t] for t in sorted(tracks)},
        "summary": {
            "theorem_nodes": len(nodes),
            "unknown_nodes": len(unknowns),
            "implies_edges": len(edges),
            "apex_nodes": len(apex_ids),
            "apex_ids": apex_ids,
            "by_kind_status": dict(sorted(counts.items())),
            "by_tier": {t: tracks[t]["open_count"] for t in sorted(tracks)},
        },
    }


def load_lean_deps_file() -> list[dict]:
    """Read lean_deps.json directly (does NOT trigger re-extraction)."""
    if not LEAN_DEPS_PATH.exists():
        raise SystemExit(f"lean_deps.json not found at {LEAN_DEPS_PATH} — run extraction first.")
    with open(LEAN_DEPS_PATH) as f:
        return json.load(f)


def main(argv: list[str] | None = None) -> int:
    import argparse
    ap = argparse.ArgumentParser(description="Derived proof-atlas view (ADR-005 Phase 1a).")
    ap.add_argument("--write", action="store_true", help=f"write {ATLAS_VIEW_PATH} (tracked)")
    ap.add_argument("--write-boundary", action="store_true",
                    help="write the GITIGNORED boundary atlas (.claude/dev-harness/"
                         "atlas_view.boundary.json) — post-compaction freshness; NEVER the tracked file")
    a = ap.parse_args(argv)

    atlas = build_atlas(load_lean_deps_file())
    s = atlas["summary"]
    print("Derived Proof Atlas (Phase 2: tracks + apexes)")
    print(f"  theorem nodes : {s['theorem_nodes']}")
    print(f"  unknown nodes : {s['unknown_nodes']}  (tracked open assumptions)")
    print(f"  IMPLIES edges : {s['implies_edges']}")
    print(f"  apex (headline) open targets : {s['apex_nodes']}")
    print("  by kind:status:")
    for k, v in s["by_kind_status"].items():
        print(f"    {k:32s} {v}")
    print("  open frontier by TRACK (separate areas — ADR-005 D-H):")
    for t, tr in atlas["tracks"].items():
        apex = f", {tr['apex_count']} apex" if tr["apex_count"] else ""
        print(f"    {t:20s} {tr['open_count']:2d} open, gating {tr['total_impact']:4d} decls{apex}")
    print("  apex (headline) targets:")
    for fr in (f for f in atlas["frontier"] if f["is_apex"]):
        print(f"    {fr['frontier_impact']:4d}  {fr['id']}  [{fr['eliminability']}]")
    print("  top frontier overall (most-gating open assumptions):")
    for fr in atlas["frontier"][:5]:
        tag = " ★apex" if fr["is_apex"] else ""
        print(f"    {fr['frontier_impact']:4d}  {fr['id']}  [{fr['tier']}/{fr['eliminability']}]{tag}")

    if a.write:
        ATLAS_VIEW_PATH.write_text(json.dumps(atlas, indent=2))
        print(f"wrote {ATLAS_VIEW_PATH}")
    if a.write_boundary:
        BOUNDARY_ATLAS_PATH.parent.mkdir(parents=True, exist_ok=True)
        BOUNDARY_ATLAS_PATH.write_text(json.dumps(atlas, indent=2))
        print(f"wrote {BOUNDARY_ATLAS_PATH}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
