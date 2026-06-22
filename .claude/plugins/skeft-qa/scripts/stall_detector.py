#!/usr/bin/env python3
"""Convergence/stall detector (GAP-A: docs/dev-loops/proposals/stall-detector.md) — the harvest
consolidator's OFF-LOOP signal that the load-bearing residual is NOT converging, so the next
compaction's COACHING BLOCK tells the loop to climb the PD-1 ladder instead of grinding the same
residual. INFORMATIONAL ONLY — never a Stop signal, never a /goal gate, never a hook.

Built to the LIVE derived-atlas interface (``lean/atlas_view.json``: ``frontier[]`` / ``unknowns[]`` /
``nodes[]`` / ``summary.apex_ids`` — richer than the Phase-1a spec assumed, which is exactly why we read
the real file). The load-bearing residual is the goal's curated apex if one is given, else the
highest-``frontier_impact`` open node. NO judgment about the work's correctness — just the convergence
signal + the matched PD-1 rung.

DECOUPLED from git for testability: the PURE ``compute_stall_signal`` takes ``commits_by_module`` as
data; the consolidator runs ``git log`` and passes it, so this module's core has no IO. Stdlib only.
"""
import argparse
import json
import sys
from pathlib import Path

_OPEN_UNKNOWN = ("STATED", "PLANNED")


def _residual_module(atlas, rid):
    for u in atlas.get("unknowns", []):
        if u.get("id") == rid:
            return u.get("module")
    return None


def _module_stem(module):
    """The atlas `module` field is often human-annotated ("SpinRokhlinInterface (Phase 5q.B...); ...").
    Reduce it to its leading module-path token so it matches a commits map keyed by the same stem (the
    consolidator keys each git-changed lean file by its dotted module path, e.g.
    lean/SKEFTHawking/FKLW/CartanSubstrate.lean -> FKLW.CartanSubstrate)."""
    if not module:
        return ""
    head = str(module).split("(", 1)[0].strip()
    toks = head.split()
    return toks[0] if toks else ""


def _open_modules(atlas, exclude_id):
    """STEMS of modules carrying an OTHER open residual: a STATED/PLANNED tracked-hypothesis UNKNOWN, or
    a CONDITIONALLY_PROVED theorem node (0 right now, but handle them for a future sorry-bearing
    keystone). Stemmed so they match the consolidator's stem-keyed commits map."""
    mods = set()
    for u in atlas.get("unknowns", []):
        if u.get("id") != exclude_id and u.get("atlas_status") in _OPEN_UNKNOWN:
            s = _module_stem(u.get("module"))
            if s:
                mods.add(s)
    for nd in atlas.get("nodes", []):
        if nd.get("atlas_status") == "CONDITIONALLY_PROVED":
            s = _module_stem(nd.get("module"))
            if s:
                mods.add(s)
    return mods


def compute_stall_signal(atlas, history, commits_by_module, k=3, n=2, goal_apex=None):
    """Decide whether the load-bearing residual is NOT converging. PURE (no IO). Returns a signal dict.

    atlas               parsed atlas_view.json (frontier[]/unknowns[]/nodes[]/summary).
    history             [{compact_event_id, residual_id, status}], oldest..newest (per-goal).
    commits_by_module   {module: commit_count_in_window} (the consolidator runs git).
    k                   no-advance threshold in DISTINCT compact-events (default 3 = GAP-A threshold).
    n                   untouched-frontier threshold (default 2).
    goal_apex           optional residual id to focus (the goal's curated apex); else top frontier.
    """
    frontier = atlas.get("frontier", []) or []
    if not frontier:
        return {"stall": False, "reason": "no open frontier (nothing tracked to converge on)"}

    # (1) load-bearing residual: the goal's apex if given+open, else the highest-frontier_impact node
    #     (the frontier is pre-sorted by frontier_impact desc in atlas_view.build_atlas).
    residual = None
    if goal_apex:
        residual = next((f for f in frontier if f.get("id") == goal_apex), None)
    if residual is None:
        residual = frontier[0]
    rid = residual.get("id")
    rstatus = residual.get("status")

    # (2) no-advance: the residual's status is unchanged across the last K DISTINCT compact-events.
    seen, streak = set(), 0
    for h in reversed([h for h in history if h.get("residual_id") == rid]):  # newest first
        ce = h.get("compact_event_id")
        if ce in seen:
            continue
        seen.add(ce)
        if h.get("status") == rstatus:
            streak += 1
        else:
            break
    no_advance = streak >= k

    # (3) available-but-untouched: OTHER open residuals whose module saw NO commits in the window.
    open_mods = _open_modules(atlas, rid)
    untouched = sorted(m for m in open_mods if commits_by_module.get(m, 0) == 0)
    untouched_count = len(untouched)

    # (4) route-proliferation (corroborating): sibling attempt-modules sharing the residual's module
    #     stem (the "23 *ConnSquare* files" smell). Best-effort from module paths.
    rstem = _module_stem(_residual_module(atlas, rid))
    proliferation = sorted(
        {m for m in open_mods if rstem and len(rstem) >= 4 and rstem in m}) if rstem else []

    stall = bool(rid) and no_advance and untouched_count >= n
    # matched PD-1 rung: a long no-advance -> E (forensic arc-trace); else an available sweep -> B;
    # else decompose -> D. (B/D/E map to PD-1's rungs in PRE_DECISIONS.md.)
    if streak >= 2 * k:
        rung = "E (forensic arc-trace) — the residual has resisted long enough that an audit precedes the next attempt"
    elif untouched_count >= n:
        rung = "B (toehold-sweep) — provable-frontier nodes sit available untouched; sweep the substrate"
    else:
        rung = "D (decompose) — break the residual into provable sub-steps and bank what works"

    return {
        "stall": stall,
        "residual_id": rid,
        "residual_status": rstatus,
        "frontier_impact": residual.get("frontier_impact"),
        "is_apex": bool(residual.get("is_apex", False)),
        "no_advance_events": streak,
        "k": k,
        "untouched_count": untouched_count,
        "untouched_modules": untouched[:10],
        "route_proliferation": len(proliferation),
        "matched_rung": rung,
    }


def append_history(history, compact_event_id, residual_id, status, cap=50):
    """Append this pass's observation (idempotent by (compact_event_id, residual_id)); cap length so
    the per-goal history file can't grow unbounded. Returns the new list."""
    if compact_event_id is None or not residual_id:
        return history
    out = [h for h in history
           if not (h.get("compact_event_id") == compact_event_id and h.get("residual_id") == residual_id)]
    out.append({"compact_event_id": compact_event_id, "residual_id": residual_id, "status": status})
    return out[-cap:]


def main(argv=None):
    ap = argparse.ArgumentParser(description="Convergence/stall detector over the derived proof-atlas.")
    ap.add_argument("--atlas", required=True, help="path to atlas_view.json")
    ap.add_argument("--history", default=None, help="per-goal stall-history JSON (read + append-on-write)")
    ap.add_argument("--commits", default=None, help="{module: count} JSON the consolidator computes from git (default {})")
    ap.add_argument("--apex", default=None, help="the goal's curated apex residual id (else the top frontier node)")
    ap.add_argument("--compact-event", default=None, help="this pass's compact_event_id (to append to --history)")
    ap.add_argument("-k", type=int, default=3)
    ap.add_argument("-n", type=int, default=2)
    a = ap.parse_args(argv)
    atlas = json.loads(Path(a.atlas).read_text())
    history = json.loads(Path(a.history).read_text()) if a.history and Path(a.history).exists() else []
    commits = json.loads(Path(a.commits).read_text()) if a.commits and Path(a.commits).exists() else {}
    sig = compute_stall_signal(atlas, history, commits, k=a.k, n=a.n, goal_apex=a.apex)
    # Append this pass's observation so FUTURE passes can detect no-advance (the consolidator supplies
    # the compact_event_id; without it we read-only).
    if a.history and a.compact_event and sig.get("residual_id"):
        history = append_history(history, a.compact_event, sig["residual_id"], sig.get("residual_status"))
        Path(a.history).write_text(json.dumps(history, indent=2))
    print(json.dumps(sig, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
