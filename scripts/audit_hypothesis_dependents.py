#!/usr/bin/env python3
"""Audit the HAND-WRITTEN ``dependent_theorems`` lists that drive the atlas POSITIVE frontier.

Why this exists (2026-07-21 atlas-integrity repair)
---------------------------------------------------
``SK_EFT_Hawking/CLAUDE.md`` describes the atlas as "derived from ``lean_deps.json`` — **cannot
drift**". That is true for *declaration* nodes (``atlas_view.py:156`` takes
``frontier_impact`` from reverse ``name_deps_project`` edges, genuinely derived) but **false for
exactly the nodes the positive frontier ranks**: for every open assumption node ``hyp:*``,
``atlas_view.py:163-182`` reads a hand-authored ``dependent_theorems`` list out of
``HYPOTHESIS_REGISTRY`` and sets ``frontier_impact = len(deps)``, emitting one ``ASSUMED_BY`` edge
per listed name. Nothing checks that those names exist, that they are Prop-consuming, or that they
mention the hypothesis at all. So the ranking that steers fan-out is **asserted, not derived**.

This script makes the gap **measurable rather than asserted**. It is READ-ONLY: it never rewrites
the registry or the atlas, and it deliberately does NOT change how the frontier ranks (that is an
operator-visible decision).

What it checks, per open hypothesis node
----------------------------------------
1. **ROT** — listed dependents that do not exist in ``lean_deps.json`` at all. Every such name
   inflates ``frontier_impact`` by one while gating nothing. This is the hard signal.
2. **UNMENTIONED** — listed dependents that DO exist but whose elaborated type never mentions the
   hypothesis's Lean carrier (when the registry names one via ``lean_carrier``, else inferred from
   the key). A softer signal: the theorem may legitimately depend transitively, so this is
   reported as advisory, never as failure.

Exit status: 0 always in ``--report-only`` (default); ``--strict`` exits 1 if any ROT is found.

Caveat the output repeats: a stale ``lean_deps.json`` makes freshly-added declarations look absent.
Check ``lean/lean_deps.json.hash`` against ``compute_lean_hash()`` before treating ROT as final.

Usage:  ``python scripts/audit_hypothesis_dependents.py [--strict]``
Stdlib only (plus the in-repo ``src.core.constants``).
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

LEAN_DEPS = ROOT / "lean" / "lean_deps.json"

#: Hypothesis ledger states that are CLOSED — mirrors ``atlas_view._CLOSED_HYP_STATUSES``. A closed
#: node is excluded from the open frontier, so its list cannot inflate any ranking.
_CLOSED_PREFIXES = ("proven", "discharged", "superseded")


def _stale_warning() -> str:
    """Best-effort staleness note so ROT is never over-read (see the module docstring caveat)."""
    try:
        from scripts.extract_lean_deps import compute_lean_hash, HASH_PATH  # type: ignore
        stored = HASH_PATH.read_text().strip() if HASH_PATH.exists() else ""
        if stored and stored != compute_lean_hash():
            return ("  ⚠ lean_deps.json is STALE (source hash differs) — declarations added since the\n"
                    "    last extraction will show as ROT. Refresh extraction before acting on ROT.\n")
    except Exception:
        pass
    return ""


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--strict", action="store_true",
                    help="exit 1 if any listed dependent is absent from lean_deps.json")
    args = ap.parse_args(argv)

    from src.core.constants import HYPOTHESIS_REGISTRY

    if not LEAN_DEPS.exists():
        print(f"lean_deps.json not found at {LEAN_DEPS} — run extraction first.")
        return 0

    deps_records = json.loads(LEAN_DEPS.read_text())
    by_name = {r.get("name", ""): r for r in deps_records}

    rows = []
    for key, h in HYPOTHESIS_REGISTRY.items():
        status = (h.get("status") or "").lower()
        if status.startswith(_CLOSED_PREFIXES):
            continue
        listed = list(h.get("dependent_theorems") or [])
        if not listed:
            continue
        rot = [n for n in listed if n not in by_name]
        carrier = h.get("lean_carrier") or ""
        unmentioned = []
        if carrier:
            for n in listed:
                rec = by_name.get(n)
                if rec is not None and carrier not in (rec.get("type") or ""):
                    unmentioned.append(n)
        rows.append({"key": key, "advertised": len(listed), "rot": rot,
                     "unmentioned": unmentioned, "carrier": carrier})

    rows.sort(key=lambda r: (-r["advertised"], r["key"]))

    print("Atlas POSITIVE-frontier hand-list audit (read-only)")
    print("  frontier_impact for every `hyp:` node = len(dependent_theorems), a HAND-WRITTEN list.")
    print("  This audit measures how far those lists have drifted from the Lean.\n")
    sw = _stale_warning()
    if sw:
        print(sw)
    print(f"  {'advert':>6} {'rot':>5} {'real':>5}  key")
    tot_adv = tot_rot = 0
    for r in rows:
        tot_adv += r["advertised"]
        tot_rot += len(r["rot"])
        real = r["advertised"] - len(r["rot"])
        flag = "  <-- ROT" if r["rot"] else ""
        print(f"  {r['advertised']:>6} {len(r['rot']):>5} {real:>5}  {r['key']}{flag}")
        for n in r["rot"]:
            print(f"{'':>21}absent from lean_deps.json: {n}")
        for n in r["unmentioned"]:
            print(f"{'':>21}advisory — type never mentions `{r['carrier']}`: {n}")

    print(f"\n  TOTAL advertised open-frontier impact: {tot_adv}")
    print(f"  Of which names ABSENT from Lean:       {tot_rot}"
          f"  ({(100.0 * tot_rot / tot_adv):.0f}% of the ranking is backed by nothing)"
          if tot_adv else "")
    print("\n  This is an integrity signal, not a gate. Fixing a list changes the frontier ranking,")
    print("  which is operator-visible — surface it, do not silently re-rank.")

    return 1 if (args.strict and tot_rot) else 0


if __name__ == "__main__":
    raise SystemExit(main())
