#!/usr/bin/env python3
"""Parked work — authorized work waiting on an external release condition (ADR-012 D19).

The pattern already exists across the roadmap corpus, in several prose dialects, and is
machine-readable by nothing:

    **Status: ⏸ PARKED / HOLDING (2026-06-30).** Gated on `5q.G` … until L2 clears
    ⏳ **PARKED as landmark** — eliminability: very_hard … NOT queued for spare capacity
    If the paper has not yet been published, Track 1 is on hold pending publication

**Every one of them names a release condition**, and that is the whole design: a parked item
is structurally a finding whose blocker is external to the finding graph. It has a target, a
lane, an owner and a condition; the only difference from an ordinary `blocked_by` is what
the blocker points at.

⚠️ **Roadmaps are NOT converted into finding streams.** The declaration is one opt-in HTML
comment block; the roadmap corpus is untouched until something is parked deliberately.
Converting the layer wholesale would be a far larger change, and roadmaps are where *scope*
is declared — a different job from where *work* is tracked.

⚠️ **This narrows a pre-existing hole; it does not close it.** `docs/architecture/
END_TO_END_MAP.md` §2 records that the roadmap layer is entirely unmechanized — no check
reads `docs/roadmaps/`, and no `*_close.md` files exist — and calls it the single largest
ungated seam in the map. That remains true.

⚠️ **There is no `operator:` scheme.** An operator decision that gates work is itself a queue
item with a node id (ADR-012 D12/D21), so parking behind it is the plain `blocked_by: <id>`
case. A separate token would be a second decision-record channel beside the queue, with its
own store and its own staleness.

Block shape
-----------
    <!-- PARKED
    id: mlx-rhmc-campaign
    lane: pyrust
    target: docs/RHMC_CAMPAIGN_SEQUENCE.md
    blocked_by: run:mlx-rhmc-2026-08
    reason: campaign staged; the operator launches it, results gate the analysis wave
    -->

`id`, `lane` and `blocked_by` are required. A parked item with no release condition is not
parked, it is abandoned — and the whole point is that the queue can tell those apart.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent
sys.path.insert(0, str(SCRIPT_DIR))
sys.path.insert(0, str(PROJECT_ROOT))

_BLOCK_RE = re.compile(r"<!--\s*PARKED\s*\n(.*?)-->", re.S)
_REQUIRED = ("id", "lane", "blocked_by")

#: Release-condition schemes, shared with `build_graph._RELEASE_SCHEMES`. Imported rather
#: than restated — two declarations of one vocabulary is how they drift.
try:
    from build_graph import _RELEASE_SCHEMES as RELEASE_SCHEMES
except ImportError:                                       # pragma: no cover
    RELEASE_SCHEMES = ("run:", "phase:", "pub:", "research:")


def parse_parked_blocks(text: str, source: str) -> list[dict]:
    """Every `<!-- PARKED … -->` block in one document, as queue-item nodes.

    Shaped like a `ReviewFinding` node (`{'id', 'type', 'meta'}`) on purpose, so the same
    consumers work on both without a second code path.
    """
    items: list[dict] = []
    for m in _BLOCK_RE.finditer(text or ""):
        fields: dict[str, str] = {}
        for line in m.group(1).splitlines():
            if ":" not in line:
                continue
            k, _, v = line.partition(":")
            k, v = k.strip().lower(), v.strip()
            if k:
                fields[k] = v
        missing = [k for k in _REQUIRED if not fields.get(k)]
        if missing:
            raise ValueError(
                f"{source}: PARKED block is missing {missing}. A parked item with no "
                f"`blocked_by` release condition is not parked, it is abandoned — and the "
                f"queue must be able to tell those apart.")
        deps = [d.strip().strip("`") for d in fields["blocked_by"].split(",") if d.strip()]
        items.append({
            "id": f"parked:{fields['id']}",
            "type": "ParkedItem",
            "meta": {
                "lane": fields["lane"].strip().strip("`").lower(),
                "target": fields.get("target"),
                "reason": fields.get("reason"),
                "blocked_by": deps,
                "source": source,
                "status": "open",
            },
        })
    return items


def release_condition_met(token: str) -> bool | None:
    """`True` / `False` / **`None` — cannot determine.**

    ⚠️ `None` IS NOT `False`, and the distinction is the one this whole suite exists to
    preserve. An unresolvable condition is *unknown*, not *unmet*: reporting it as unmet
    makes a released item look parked forever, and reporting it as met would release work on
    no evidence. Callers must handle three values.
    """
    if not token.startswith(RELEASE_SCHEMES):
        return None
    scheme, _, value = token.partition(":")
    value = value.strip()
    if not value:
        return None

    if scheme == "pub":
        try:
            from src.core.citations import CITATION_REGISTRY
        except ImportError:
            return None
        entry = CITATION_REGISTRY.get(value)
        if entry is None:
            return None
        return not entry.get("inprep", False)

    if scheme == "research":
        try:
            from src.core.workspace import find_workspace
            done = Path(find_workspace()) / "Lit-Search" / "Tasks" / "complete"
        except Exception:
            return None
        if not done.is_dir():
            return None
        return any(p.stem == value or p.name == value for p in done.iterdir())

    if scheme == "phase":
        roadmaps = PROJECT_ROOT / "docs" / "roadmaps"
        if not roadmaps.is_dir():
            return None
        hits = [p for p in roadmaps.glob("*.md") if value.lower() in p.stem.lower()]
        if not hits:
            return None
        closed = re.compile(r"^\*\*Status:.*\b(COMPLETE|CLOSED|DONE)\b", re.M | re.I)
        return any(closed.search(p.read_text(encoding="utf-8", errors="replace"))
                   for p in hits)

    if scheme == "run":
        # ⚠️ Deliberately UNKNOWN until a run registry exists. Returning False would render
        # every staged campaign as permanently parked; returning True would release work on
        # no evidence. The honest answer is that we cannot tell.
        return None

    return None


def collect(roadmaps_dir: Path | None = None) -> list[dict]:
    """Every parked item declared across the roadmap corpus."""
    d = roadmaps_dir or (PROJECT_ROOT / "docs" / "roadmaps")
    out: list[dict] = []
    if not d.is_dir():
        return out
    for p in sorted(d.glob("*.md")):
        try:
            src = str(p.relative_to(PROJECT_ROOT))
        except ValueError:
            src = str(p)        # a directory outside the repo (tests, or a sibling repo)
        out.extend(parse_parked_blocks(
            p.read_text(encoding="utf-8", errors="replace"), src))
    return out


if __name__ == "__main__":
    for it in collect():
        conds = {t: release_condition_met(t) for t in it["meta"]["blocked_by"]}
        state = ("RELEASED" if conds and all(v is True for v in conds.values())
                 else "UNKNOWN" if any(v is None for v in conds.values()) else "PARKED")
        print(f"{state:9} {it['id']:32} {it['meta']['lane']:10} {conds}")
