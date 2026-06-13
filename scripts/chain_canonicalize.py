"""chain_canonicalize.py — deterministic canonicalization of the claims-reviewer's
`chain_proposed.links` targets.

Each link is `{kind, target}` where `target` is free-text from claims-reviewer-v2.
build_graph resolves it to a BACKED_BY node id by string convention; ~26% don't
match (root cause: docs/KNOWLEDGE_GRAPH.md restricts BACKED_BY targets to a closed
declaration-level artifact set, and the reviewer often cites modules/constants/prose).

This module resolves each `{kind, target}` against the live graph to ONE of:
  - resolved     : a canonical node id (auto-fixable)
  - suggested    : best-guess node id(s) for a human to confirm
  - unresolvable : with a human-readable reason (genuine residue)

It is SCHEMA-ALIGNED: it never invents new node types — it only maps to the
existing closed BACKED_BY target set. The pure core `canonicalize_link(kind,
target, index)` is unit-testable against a small fake index; the CLI `--report`
builds a real index and is read-only (no writes).

CLI:
    uv run python scripts/chain_canonicalize.py --report        # read-only breakdown
    uv run python scripts/chain_canonicalize.py --report --paper paper11_quantum_group
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Protocol

PROJECT_ROOT = Path(__file__).resolve().parent.parent

# The closed BACKED_BY link-kind set (mirrors sentence_state._VALID_LINK_KINDS /
# KNOWLEDGE_GRAPH.md:159). Anything else is a schema error, not a resolution miss.
VALID_KINDS = {"formula", "theorem", "axiom", "parameter", "citation",
               "hypothesis", "aristotle", "production_run"}

RESOLVED = "resolved"
SUGGESTED = "suggested"
UNRESOLVABLE = "unresolvable"


@dataclass
class Resolution:
    status: str                       # resolved | suggested | unresolvable
    kind: str
    target: str
    target_id: str | None = None      # canonical node id (resolved)
    suggestions: list[str] = field(default_factory=list)
    reason: str = ""
    category: str = ""                # root-cause bucket for reporting


class Index(Protocol):
    """The lookups canonicalize_link needs. Real impl is GraphIndex below; tests
    use a small fake."""
    node_ids: set[str]
    def resolve_lean_short(self, name: str) -> str | None: ...
    def lean_short_candidates(self, name: str) -> list[str]: ...
    def module_id_for_ref(self, target: str) -> str | None: ...
    def constant_param_alias(self, target: str) -> str | None: ...
    def is_constant_ref(self, target: str) -> bool: ...
    def closest_formula(self, target: str) -> str | None: ...
    def normalize_bibkey(self, target: str) -> str | None: ...


# Forms the reviewer uses to mean "the whole module": "X (module)", "X_module",
# "SKEFTHawking.X", trailing "(...)" annotations.
_ANNOT_RE = re.compile(r"\s*\([^)]*\)\s*$")


def _strip_module_surface(target: str) -> str:
    base = _ANNOT_RE.sub("", target).strip()
    base = re.sub(r"_module$", "", base)
    if base.startswith("SKEFTHawking."):
        base = base[len("SKEFTHawking."):]
    return base


def canonicalize_link(kind: str, target: str, idx: Index) -> Resolution:
    """Resolve one chain link to a canonical BACKED_BY target id, a suggestion,
    or an unresolvable-with-reason. Pure: all I/O is via `idx`."""
    kind = (kind or "").strip()
    t = (target or "").strip()

    def R(status, **kw):
        return Resolution(status=status, kind=kind, target=target, **kw)

    if kind not in VALID_KINDS:
        return R(UNRESOLVABLE, reason=f"invalid link kind {kind!r}", category="invalid-kind")
    if not t:
        return R(UNRESOLVABLE, reason="empty target", category="empty")

    if kind == "formula":
        if f"formula:{t}" in idx.node_ids:
            return R(RESOLVED, target_id=f"formula:{t}", category="formula-ok")
        cand = idx.closest_formula(t)
        if cand:
            return R(SUGGESTED, suggestions=[f"formula:{cand}"],
                     reason="formula name not found; closest existing def", category="formula-renamed")
        return R(UNRESOLVABLE, reason="no formula by that name (expression/renamed/absent)",
                 category="formula-absent")

    if kind in ("theorem", "axiom"):
        r = idx.resolve_lean_short(t)
        if r:
            return R(RESOLVED, target_id=r, category="theorem-ok")
        mod_id = idx.module_id_for_ref(t)
        if mod_id:
            # Whole-module backing reference -> its auto-derived LeanModule node.
            return R(RESOLVED, target_id=mod_id, category="module-resolved")
        cands = idx.lean_short_candidates(t)
        if len(cands) > 1:
            return R(SUGGESTED, suggestions=cands, reason="ambiguous short name", category="theorem-ambiguous")
        return R(UNRESOLVABLE, reason="no Lean declaration or module resolves (renamed/absent)",
                 category="theorem-absent")

    if kind == "parameter":
        if f"param:{t}" in idx.node_ids:
            return R(RESOLVED, target_id=f"param:{t}", category="param-ok")
        alias = idx.constant_param_alias(t)
        if alias:
            return R(SUGGESTED, suggestions=[f"param:{alias}"],
                     reason="constants.py constant; PROVENANCE parameter is the same quantity",
                     category="param-constant-aliased")
        if idx.is_constant_ref(t):
            return R(UNRESOLVABLE, reason="constants.py constant (not a PARAMETER_PROVENANCE entry)",
                     category="param-constant")
        return R(UNRESOLVABLE, reason="no parameter by that name (expression/absent)", category="param-absent")

    if kind == "citation":
        if f"source:{t}" in idx.node_ids:
            return R(RESOLVED, target_id=f"source:{t}", category="citation-ok")
        norm = idx.normalize_bibkey(t)
        if norm and f"source:{norm}" in idx.node_ids:
            return R(SUGGESTED, suggestions=[f"source:{norm}"], reason="bibkey format mismatch",
                     category="citation-format")
        return R(UNRESOLVABLE, reason="citation not in CITATION_REGISTRY", category="citation-absent")

    if kind == "hypothesis":
        if f"hyp:{t}" in idx.node_ids:
            return R(RESOLVED, target_id=f"hyp:{t}", category="hyp-ok")
        short = t.split(".")[-1]
        if short != t and f"hyp:{short}" in idx.node_ids:
            return R(SUGGESTED, suggestions=[f"hyp:{short}"], reason="module-qualified; short form registered",
                     category="hyp-qualified")
        return R(UNRESOLVABLE, reason="hypothesis not in HYPOTHESIS_REGISTRY", category="hyp-absent")

    if kind == "aristotle":
        if f"aristotle:{t}" in idx.node_ids:
            return R(RESOLVED, target_id=f"aristotle:{t}", category="aristotle-ok")
        base = re.split(r"[ (]", t, 1)[0].strip()
        if base != t and f"aristotle:{base}" in idx.node_ids:
            return R(SUGGESTED, suggestions=[f"aristotle:{base}"], reason="annotation stripped",
                     category="aristotle-format")
        return R(UNRESOLVABLE, reason="aristotle run not found", category="aristotle-absent")

    if kind == "production_run":
        if f"production:{t}" in idx.node_ids:
            return R(RESOLVED, target_id=f"production:{t}", category="production-ok")
        return R(UNRESOLVABLE, reason="production run not found", category="production-absent")

    return R(UNRESOLVABLE, reason=f"unhandled kind {kind!r}", category="invalid-kind")


# ─────────────────────────────────────────────────────────────────────────────
# Real index (CLI). Kept out of the pure core so tests don't need the graph.
# ─────────────────────────────────────────────────────────────────────────────

class GraphIndex:
    """Live index built from build_graph's node extractors + the source files.
    Read-only; ~node-build cost (no edges, no PG)."""

    def __init__(self) -> None:
        sys.path.insert(0, str(PROJECT_ROOT / "scripts"))
        sys.path.insert(0, str(PROJECT_ROOT))
        import build_graph as bg
        self._bg = bg
        nodes = bg.extract_all_nodes()          # also populates _LEAN_SHORT_INDEX
        self.node_ids = {n["id"] for n in nodes}
        # formula def names
        self.formula_names = {i.split(":", 1)[1] for i in self.node_ids if i.startswith("formula:")}
        # constants.py UPPER_SNAKE dict/const names (rough) for is_constant_ref
        csrc = (PROJECT_ROOT / "src" / "core" / "constants.py").read_text()
        self.const_roots = set(re.findall(r"^([A-Z][A-Z0-9_]+)\s*[:=]", csrc, re.M))

    def resolve_lean_short(self, name: str) -> str | None:
        return self._bg._resolve_lean_short(name, self.node_ids)

    def lean_short_candidates(self, name: str) -> list[str]:
        short = name.rsplit(".", 1)[-1]
        return list(self._bg._LEAN_SHORT_INDEX.get(short, []))

    def module_id_for_ref(self, target: str) -> str | None:
        # Delegate to build_graph's resolver so the report mirrors the graph.
        return self._bg._module_id_for_ref(target, self.node_ids)

    def constant_param_alias(self, target: str) -> str | None:
        # Intentionally empty in v1: the report surfaces which constants are
        # referenced so we can build an explicit, reviewed alias table (Tier-2
        # step 3) rather than guessing equivalences.
        return None

    def is_constant_ref(self, target: str) -> bool:
        root = target.split(".")[0].strip()
        return root in self.const_roots or target in self.const_roots

    def closest_formula(self, target: str) -> str | None:
        import difflib
        m = difflib.get_close_matches(target, self.formula_names, n=1, cutoff=0.8)
        return m[0] if m else None

    def normalize_bibkey(self, target: str) -> str | None:
        # Try inserting a colon before a 4-digit year: Hatsuda2008 -> Hatsuda:2008
        m = re.match(r"^([A-Za-z]+)(\d{4})$", target.strip())
        return f"{m.group(1)}:{m.group(2)}" if m else None


def _iter_links():
    for p in sorted((PROJECT_ROOT / "papers").glob("*/claims_review.json")):
        paper = p.parent.name
        cr = json.loads(p.read_text())
        for s in cr.get("sentences", []):
            for l in ((s.get("chain_proposed") or {}).get("links") or []):
                yield paper, s.get("id"), l.get("kind"), l.get("target")


def cmd_report(args: argparse.Namespace) -> int:
    from collections import Counter
    idx = GraphIndex()
    by_status = Counter()
    by_category = Counter()
    by_status_paper = Counter()
    examples: dict[str, list[str]] = {}
    total = 0
    for paper, sid, kind, target in _iter_links():
        if args.paper and paper != args.paper:
            continue
        if not kind or not target:
            continue
        total += 1
        res = canonicalize_link(kind, target, idx)
        by_status[res.status] += 1
        by_category[(res.status, res.category)] += 1
        by_status_paper[(res.status, paper)] += 1
        examples.setdefault(res.category, [])
        if len(examples[res.category]) < 4:
            examples[res.category].append(f"[{kind}] {target!r}")

    print(f"\nchain-link canonicalization report — {total} links"
          + (f" (paper={args.paper})" if args.paper else " (all 46 files)"))
    print("=" * 64)
    for st in (RESOLVED, SUGGESTED, UNRESOLVABLE):
        print(f"  {st:13} {by_status[st]:5}  ({100*by_status[st]//max(total,1)}%)")
    print("\nby category:")
    for (st, cat), n in by_category.most_common():
        print(f"  {n:5}  {st:12} {cat}")
        for ex in examples.get(cat, [])[:3]:
            print(f"         e.g. {ex}")
    return 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--report", action="store_true", help="read-only breakdown (default)")
    ap.add_argument("--paper", help="limit to one paper dir name")
    args = ap.parse_args(argv)
    return cmd_report(args)


if __name__ == "__main__":
    raise SystemExit(main())
