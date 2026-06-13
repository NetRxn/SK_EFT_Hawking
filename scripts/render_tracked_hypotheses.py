#!/usr/bin/env python3
"""Render docs/PERMANENT_TRACKED_HYPOTHESES.md from HYPOTHESIS_REGISTRY.

Substrate Integrity Gates W3 (ADR-004): HYPOTHESIS_REGISTRY (src/core/constants.py)
is the SINGLE source of truth for the project's tracked-hypothesis surface.
The markdown doc is an auto-generated, publication-facing VIEW of it — it can no
longer drift from the registry (the prior failure: two hand-maintained ledgers
with disjoint contents). Freshness is enforced by
`validate.py --check tracked_hypotheses_fresh` at Stage 12.

Usage:
    uv run python scripts/render_tracked_hypotheses.py          # write the md
    uv run python scripts/render_tracked_hypotheses.py --check  # nonzero exit if stale
"""
from __future__ import annotations
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
DOC_PATH = PROJECT_ROOT / "docs" / "PERMANENT_TRACKED_HYPOTHESES.md"

_TIER_ORDER = ["headline", "external_boundary", "discharge_future", "local"]
_TIER_TITLE = {
    "headline": "Headline-gating (a published-paper headline rides on it)",
    "external_boundary": "External boundary / KEEP_AS_TRACKED (research-grade or project-scope)",
    "discharge_future": "Discharge-future (in-principle derivable; scheduled)",
    "local": "Local / intermediate (module-scoped algebraic hypothesis)",
    "_other": "Other / untiered",
}


def _esc(s: str) -> str:
    return str(s).replace("\n", " ").strip()


def render() -> str:
    sys.path.insert(0, str(PROJECT_ROOT))
    from src.core.constants import HYPOTHESIS_REGISTRY

    lines: list[str] = []
    lines.append("# Permanent Tracked Hypotheses")
    lines.append("")
    lines.append("> **AUTO-GENERATED — DO NOT EDIT BY HAND.** This document is rendered from "
                 "`HYPOTHESIS_REGISTRY` in `src/core/constants.py` by "
                 "`scripts/render_tracked_hypotheses.py` (Substrate Integrity Gates W3, ADR-004). "
                 "The registry is the single source of truth; edit it, then regenerate. "
                 "Freshness enforced by `validate.py --check tracked_hypotheses_fresh`.")
    lines.append("")
    lines.append("**Purpose.** Catalogue the project's load-bearing tracked-hypothesis Props — "
                 "Lean predicates consumed by substantive theorems but NOT independently derived. "
                 "Each is a *constructive* alternative to a global `axiom`: the claim is packaged "
                 "as a `def … : Prop` and taken as an explicit hypothesis, making the project's "
                 "assumption surface visible at the type-signature level (Pipeline Invariant #15/#16).")
    lines.append("")
    reg = HYPOTHESIS_REGISTRY
    by_tier: dict[str, list[str]] = {}
    for k, v in reg.items():
        by_tier.setdefault(v.get("tier", "_other"), []).append(k)
    lines.append(f"**Count.** {len(reg)} tracked hypotheses "
                 + ", ".join(f"{len(by_tier.get(t, []))} {t}" for t in _TIER_ORDER
                             if by_tier.get(t)) + ".")
    lines.append("")
    lines.append("---")
    lines.append("")

    for tier in _TIER_ORDER + ["_other"]:
        keys = sorted(by_tier.get(tier, []))
        if not keys:
            continue
        lines.append(f"## {_TIER_TITLE[tier]}")
        lines.append("")
        for key in keys:
            v = reg[key]
            lines.append(f"### `{key}`")
            lines.append("")
            if v.get("statement"):
                lines.append(f"**Statement.** {_esc(v['statement'])}")
                lines.append("")
            meta = []
            if v.get("status"):
                meta.append(f"status `{v['status']}`")
            if v.get("eliminability"):
                meta.append(f"eliminability `{v['eliminability']}`")
            if v.get("module"):
                meta.append(f"module `{v['module']}`")
            if meta:
                lines.append("- " + " · ".join(meta))
            if v.get("prose"):
                lines.append(f"- **Posture.** {_esc(v['prose'])}")
            if v.get("elimination_path"):
                lines.append(f"- **Discharge path.** {_esc(v['elimination_path'])}")
            if v.get("source"):
                lines.append(f"- **Source.** {_esc(v['source'])}")
            if v.get("risk"):
                lines.append(f"- **Risk.** {_esc(v['risk'])}")
            if v.get("circularity_note") and v["circularity_note"] != "None.":
                lines.append(f"- **Circularity.** {_esc(v['circularity_note'])}")
            dts = v.get("dependent_theorems") or []
            if dts:
                lines.append(f"- **Consumers.** {', '.join('`' + d + '`' for d in dts)}")
            lines.append("")
        lines.append("---")
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def main(argv: list[str]) -> int:
    new = render()
    if "--check" in argv:
        old = DOC_PATH.read_text() if DOC_PATH.exists() else ""
        if old != new:
            print("STALE: docs/PERMANENT_TRACKED_HYPOTHESES.md differs from the registry render.")
            return 1
        print("FRESH")
        return 0
    DOC_PATH.write_text(new)
    print(f"Wrote {DOC_PATH} ({new.count('### ')} entries).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
