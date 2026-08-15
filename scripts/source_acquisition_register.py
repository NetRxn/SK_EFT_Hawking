#!/usr/bin/env python3
"""Regenerate `docs/SOURCE_ACQUISITION_REGISTER.md` — what we cite but do not hold.

WHY THIS EXISTS. Submission-grade prose may not disclose that we cite a source we
have not read; that disclosure is a non-starter in a manuscript. But deleting the
disclosure while leaving the citation is strictly worse -- it converts a visible gap
into an invisible one. The repair is to ACQUIRE the source, which costs money we
have a limited budget for. So the gap has to be measured and ranked, not narrated.

WHAT IS MEASURED (all at HEAD, never quoted from a prior run):
  * holding   -- CITATION_REGISTRY[k]['primary_source_path'], resolved on disk.
                 `abstract` when the cached filename says so; a cached abstract is
                 NOT the source, and the Mather1982 convention question is the
                 measured proof that treating it as one produces a false claim.
  * usage     -- \\cite keys in the 21 bundle drafts, LaTeX comments stripped.
                 Legacy paperNN drafts are excluded: they are not the submission
                 surface, so a gap there is not a budget item.
  * bearing   -- the source supplies a registered PARAMETER_PROVENANCE value, or is
                 named in formulas.py.

⚠️ THE BEARING SIGNAL IS A FLOOR, NOT A CENSUS, and the register says so in its own
   output. A source supplying a CLOSED FORM, a theorem or a convention -- rather
   than a numeral -- is invisible to it. IrwinHilton2005 is the measured example:
   it is the attributed source of D12's gradient-factor closed form and neither
   signal fires on it. That is what `docs/source_acquisition_overlay.json` is for;
   curated verdicts there override, and survive regeneration.

⚠️ AN UNCHECKED PAYWALL IS A GUESS, NOT A COST. `route: paywalled` is only honest
   once the free routes in `route_note` have actually been tried. The overlay's
   README carries that rule; this script surfaces unchecked ones separately so a
   provisional label cannot masquerade as a priced one.

Usage:  uv run python scripts/source_acquisition_register.py [--check]
        --check exits 1 if the register on disk differs from a fresh measurement,
        so a stale register fails rather than misleads.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
WORKSPACE = PROJECT_ROOT.parent
sys.path.insert(0, str(PROJECT_ROOT))

OVERLAY = PROJECT_ROOT / "docs" / "source_acquisition_overlay.json"
REGISTER = PROJECT_ROOT / "docs" / "SOURCE_ACQUISITION_REGISTER.md"

_CITE = re.compile(r"\\cite[a-zA-Z]*\*?(?:\[[^\]]*\])*\{([^}]*)\}")
_COMMENT = re.compile(r"(?<!\\)%.*$")

#: Routes that cost nothing. A source on one of these is a FETCH task and must
#: never appear in a budget total, however load-bearing it is.
_FREE_ROUTES = {"open", "arxiv", "repository", "internal"}


def _holding(key: str, registry: dict) -> str:
    path = (registry.get(key) or {}).get("primary_source_path")
    if not path:
        return "none"
    fp = WORKSPACE / path
    if not fp.exists():
        return "missing"
    return "abstract" if "abstract" in fp.name.lower() else "full"


def _bundle_usage() -> dict[str, set[str]]:
    """`{bibkey: {bundle, ...}}` over the submission bundles only."""
    usage: dict[str, set[str]] = {}
    for d in sorted((PROJECT_ROOT / "papers").iterdir()):
        if not (d.is_dir() and (d / "bundle_metadata.json").exists()):
            continue
        tex = d / "paper_draft.tex"
        if not tex.is_file():
            continue
        body = "\n".join(_COMMENT.sub("", ln)
                         for ln in tex.read_text(errors="replace").splitlines())
        for m in _CITE.finditer(body):
            for key in (x.strip() for x in m.group(1).split(",")):
                if key:
                    usage.setdefault(key, set()).add(d.name)
    return usage


def _bearing(keys, registry, provenance) -> dict[str, list[str]]:
    """Automated load-bearing signal. A FLOOR — see the module docstring."""
    formulas = (PROJECT_ROOT / "src" / "core" / "formulas.py").read_text(errors="replace")
    out: dict[str, list[str]] = {}
    for pkey, pval in provenance.items():
        blob = " ".join(str(pval.get(f, "")) for f in ("source", "doi", "detail")).lower()
        for key in keys:
            doi = ((registry.get(key) or {}).get("doi") or "").lower()
            if (doi and doi in blob) or re.search(rf"\b{re.escape(key.lower())}\b", blob):
                out.setdefault(key, []).append(f"param:{pkey}")
    for key in keys:
        if re.search(rf"\b{re.escape(key)}\b", formulas):
            out.setdefault(key, []).append("formulas.py")
    return out


def _rows():
    from src.core.citations import CITATION_REGISTRY as REG
    from src.core.provenance import PARAMETER_PROVENANCE as PROV

    overlay = {k: v for k, v in json.loads(OVERLAY.read_text()).items()
               if not k.startswith("_")}
    usage = _bundle_usage()
    gaps = {k: v for k, v in usage.items() if _holding(k, REG) != "full"}
    bearing = _bearing(gaps, REG, PROV)

    rows = []
    for key, bundles in gaps.items():
        ov = overlay.get(key, {})
        signals = bearing.get(key, [])
        # Curated verdict wins over the signal, in BOTH directions: it promotes a
        # formula-supplying source the signal cannot see, and it demotes a textbook
        # the signal would never have flagged anyway.
        if "load_bearing" in ov:
            bears, why = bool(ov["load_bearing"]), "curated"
        else:
            bears, why = bool(signals), ("signal" if signals else "-")
        route = ov.get("route") or ("internal" if key.startswith("Roehm2026") else "unassessed")
        if route == "internal":
            priority = "—"           # our own companion papers: never a budget item
        elif bears:
            priority = "P0"
        elif len(bundles) > 1:
            priority = "P1"
        else:
            priority = "P2"
        rows.append({
            "key": key, "holding": _holding(key, REG), "bundles": sorted(bundles),
            "bears": bears, "why": why, "signals": signals, "route": route,
            "priority": priority, "reason": ov.get("reason", ""),
            "route_note": ov.get("route_note", ""),
            "doi": (REG.get(key) or {}).get("doi") or "",
        })
    rows.sort(key=lambda r: ({"P0": 0, "P1": 1, "P2": 2, "—": 3}[r["priority"]],
                             -len(r["bundles"]), r["key"]))
    return rows


def render() -> str:
    rows = _rows()
    p0 = [r for r in rows if r["priority"] == "P0"]
    buy = [r for r in p0 if r["route"] not in _FREE_ROUTES]
    unassessed = [r for r in p0 if r["route"] == "unassessed"]

    out = [
        "# Source Acquisition Register",
        "",
        "**Auto-generated** by `scripts/source_acquisition_register.py`. Do not hand-edit —",
        "curated verdicts belong in `docs/source_acquisition_overlay.json`, which survives",
        "regeneration.",
        "",
        "Sources cited in the **21 submission bundles** that we do not hold in full text.",
        "Legacy `paperNN` drafts are excluded: they are not the submission surface.",
        "",
        "## Priority",
        "",
        "| | meaning | budget |",
        "|---|---|---|",
        "| **P0** | load-bearing — a claim, parameter or formula depends on it | buy only if `route` is not free |",
        "| **P1** | cited by 2+ bundles, not load-bearing | do not buy; verify the citation earns its place |",
        "| **P2** | single bundle, not load-bearing | do not buy; likely droppable |",
        "| **—** | our own companion papers | never a budget item |",
        "",
        "⚠️ **The load-bearing signal is a FLOOR, not a census.** It fires on sources that",
        "supply a registered parameter value or are named in `formulas.py`. A source",
        "supplying a *closed form*, theorem or convention is invisible to it —",
        "`IrwinHilton2005` is the measured example. Curate those in the overlay; a P1/P2",
        "row is 'not detected as load-bearing', never 'confirmed decorative'.",
        "",
        "⚠️ **An unchecked paywall is a guess, not a cost.** `route: paywalled` is honest",
        "only once the free routes named in `route_note` have actually been tried.",
        "",
        "## Spend list — P0, not free",
        "",
    ]
    if buy:
        out += ["| source | held | bundles | route | free routes to exhaust first |",
                "|---|---|---|---|---|"]
        for r in buy:
            out.append(f"| `{r['key']}` | {r['holding']} | {', '.join(r['bundles'])} | "
                       f"{r['route']} | {r['route_note'] or '⚠️ none recorded'} |")
    else:
        out.append("_None._")
    out += ["", f"**Candidate spend: {len(buy)} source(s).**", ""]
    if unassessed:
        out += ["⚠️ **Route not yet assessed** (cannot be priced, may well be free): "
                + ", ".join(f"`{r['key']}`" for r in unassessed), ""]

    out += ["## P0 — load-bearing", "",
            "| source | held | bundles | route | why it is load-bearing |",
            "|---|---|---|---|---|"]
    for r in p0:
        why = r["reason"] or ("; ".join(r["signals"]) if r["signals"] else "—")
        out.append(f"| `{r['key']}` | {r['holding']} | {', '.join(r['bundles'])} | "
                   f"{r['route']} | {why} |")

    for tier, label in (("P1", "P1 — cross-cutting, not detected as load-bearing"),
                        ("P2", "P2 — single bundle, not detected as load-bearing")):
        sel = [r for r in rows if r["priority"] == tier]
        out += ["", f"## {label} ({len(sel)})", ""]
        out.append(", ".join(f"`{r['key']}`" for r in sel) or "_None._")

    own = [r for r in rows if r["priority"] == "—"]
    out += ["", f"## Our own companion papers ({len(own)}) — not purchasable", "",
            ", ".join(f"`{r['key']}`" for r in own) or "_None._", "",
            "---", "",
            f"*{len(rows)} bundle-cited sources not held in full text: "
            f"{len(p0)} P0, {len([r for r in rows if r['priority']=='P1'])} P1, "
            f"{len([r for r in rows if r['priority']=='P2'])} P2, {len(own)} internal.*", ""]
    return "\n".join(out)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true",
                    help="exit 1 if the register on disk is stale")
    args = ap.parse_args()
    fresh = render()
    if args.check:
        current = REGISTER.read_text() if REGISTER.exists() else ""
        if current != fresh:
            print("STALE: docs/SOURCE_ACQUISITION_REGISTER.md differs from a fresh "
                  "measurement. Regenerate with "
                  "`uv run python scripts/source_acquisition_register.py`.")
            return 1
        print("Register is current.")
        return 0
    REGISTER.write_text(fresh)
    print(f"Wrote {REGISTER.relative_to(PROJECT_ROOT)} ({len(fresh.splitlines())} lines)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
