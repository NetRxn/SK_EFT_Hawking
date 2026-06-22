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
        unknowns.append({
            "id": node_id,
            "atlas_kind": "UNKNOWN",
            "atlas_status": st,
            "tier": h.get("tier"),
            "eliminability": h.get("eliminability"),
            "module": h.get("module"),
            "frontier_impact": len(deps),
            "dependent_theorems": deps,
        })
        counts[f"UNKNOWN:{st}"] += 1
        for d in deps:
            edges.append({"source": node_id, "type": "ASSUMED_BY", "target": d})

    # Frontier (Phase-1a sense): open assumptions ranked by how much they gate, highest first —
    # "which open node, if discharged, unlocks the most." (The provable-theorem frontier becomes
    # meaningful once STATED-but-unproven targets exist — Phase 2/3.)
    frontier = sorted(
        ({"id": u["id"], "frontier_impact": u["frontier_impact"], "status": u["atlas_status"]}
         for u in unknowns),
        key=lambda x: (-x["frontier_impact"], x["id"]),
    )

    return {
        "nodes": nodes,
        "unknowns": unknowns,
        "edges": edges,
        "frontier": frontier,
        "summary": {
            "theorem_nodes": len(nodes),
            "unknown_nodes": len(unknowns),
            "implies_edges": len(edges),
            "by_kind_status": dict(sorted(counts.items())),
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
    ap.add_argument("--write", action="store_true", help=f"write {ATLAS_VIEW_PATH}")
    a = ap.parse_args(argv)

    atlas = build_atlas(load_lean_deps_file())
    s = atlas["summary"]
    print("Derived Proof Atlas (Phase 1a)")
    print(f"  theorem nodes : {s['theorem_nodes']}")
    print(f"  unknown nodes : {s['unknown_nodes']}  (tracked open assumptions)")
    print(f"  IMPLIES edges : {s['implies_edges']}")
    print("  by kind:status:")
    for k, v in s["by_kind_status"].items():
        print(f"    {k:32s} {v}")
    print("  top frontier (most-gating open assumptions):")
    for fr in atlas["frontier"][:5]:
        print(f"    {fr['frontier_impact']:4d}  {fr['id']}  [{fr['status']}]")

    if a.write:
        ATLAS_VIEW_PATH.write_text(json.dumps(atlas, indent=2))
        print(f"wrote {ATLAS_VIEW_PATH}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
