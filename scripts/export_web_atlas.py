#!/usr/bin/env python3
"""
Export compact, web-weight JSON distillations of the proof atlas for
external visualization surfaces (dashboards, static sites).

Reads from:
  - lean/atlas_view.json   (derived Proof Atlas — ADR-005 / ADR-007)
  - docs/counts.json       (single source of truth for counts)
  - git history of docs/counts.json (velocity time series)

Writes to build/web_export/ (gitignored):
  - site_atlas.json      compact atlas: summary, ranked frontier, registered
                         and unregistered obstructions with false-statement
                         glosses, per-module-family province aggregates
  - velocity.json        daily time series of declaration/theorem/module
                         counts reconstructed from counts.json git history
  - counts_summary.json  the headline trust numbers
  - manifest.json        schema_version, generated_at, sha256 per file

Design constraints:
  - site_atlas.json target size <= 300 KB (source atlas is ~4.3 MB)
  - every number is derived, none hand-typed
  - consumers treat these as a versioned snapshot (schema_version below)

Usage:
    uv run python scripts/export_web_atlas.py
    uv run python scripts/export_web_atlas.py --out build/web_export
"""

import argparse
import hashlib
import json
import subprocess
import sys
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path

SCHEMA_VERSION = "0.2.0"
ROOT = Path(__file__).resolve().parent.parent


def load_atlas() -> dict:
    with open(ROOT / "lean" / "atlas_view.json") as f:
        return json.load(f)


def load_counts() -> dict:
    with open(ROOT / "docs" / "counts.json") as f:
        return json.load(f)


def load_deps() -> list:
    """lean_deps.json is expensive to regenerate — tolerate its absence
    (family_edges just ships empty) rather than failing the export."""
    path = ROOT / "lean" / "lean_deps.json"
    if not path.exists():
        print("WARN: lean/lean_deps.json missing — family_edges will be empty",
              file=sys.stderr)
        return []
    with open(path) as f:
        return json.load(f)


MIN_FAMILY_SIZE = 10  # smaller top-level modules roll into "(other)"


def family_of(module: str) -> str:
    """SKEFTHawking.Family.Rest -> Family; SKEFTHawking.TopLevel -> TopLevel."""
    parts = (module or "").split(".")
    if parts and parts[0] == "SKEFTHawking" and len(parts) >= 2:
        return parts[1]
    return parts[0] if parts and parts[0] else "(unknown)"


MIN_EDGE_WEIGHT = 2  # single stray crossings are noise; keeps the export lean


def build_family_edges(deps: list) -> list:
    """Cross-family dependency edges from lean_deps.json — real proof-graph
    structure aggregated to family level (no declaration names shipped).
    Undirected: keys sorted lexicographically, weight = crossing dep count.
    Edges below MIN_EDGE_WEIGHT are dropped (disclosed cap, not silent)."""
    fam_of_name = {d["name"]: family_of(d.get("module", ""))
                   for d in deps if d.get("name")}
    counts: Counter = Counter()
    for d in deps:
        fa = fam_of_name.get(d.get("name"))
        if not fa:
            continue
        for dep in d.get("name_deps_project", []):
            fb = fam_of_name.get(dep)
            if fb and fb != fa:
                counts[(min(fa, fb), max(fa, fb))] += 1
    return [{"a": a, "b": b, "weight": w}
            for (a, b), w in sorted(counts.items(),
                                    key=lambda kv: (-kv[1], kv[0]))
            if w >= MIN_EDGE_WEIGHT]


def build_site_atlas(atlas: dict) -> dict:
    provinces: dict[str, dict] = defaultdict(lambda: defaultdict(int))
    for node in atlas.get("nodes", []):
        fam = family_of(node.get("module", ""))
        provinces[fam]["total"] += 1
        provinces[fam][node.get("atlas_status", "UNKNOWN")] += 1

    major, other = [], defaultdict(int)
    for fam, counts in provinces.items():
        if counts["total"] >= MIN_FAMILY_SIZE:
            major.append({"family": fam, **counts})
        else:
            for k, v in counts.items():
                other[k] += v
            other["families"] += 1
    major.sort(key=lambda p: -p["total"])
    if other:
        major.append({"family": "(other)", **other})
    province_list = major

    # fqn -> family via the nodes list (unknowns[].module is FREE TEXT prose —
    # never parse it; families come from the dependent theorems instead).
    # Fallback for FQNs absent from the node list: the namespace itself
    # (SKEFTHawking.Family.decl) still encodes real family structure;
    # top-level declarations (2 parts) carry no family evidence.
    fqn_family = {n["fqn"]: family_of(n.get("module", ""))
                  for n in atlas.get("nodes", [])}

    def family_of_fqn(fqn: str) -> str | None:
        if fqn in fqn_family:
            return fqn_family[fqn]
        parts = (fqn or "").split(".")
        if parts[0] == "SKEFTHawking" and len(parts) >= 3:
            return parts[1]
        return None

    hyp_meta: dict[str, tuple[str | None, list[dict]]] = {}
    for u in atlas.get("unknowns", []):
        fams = sorted(f for f in (family_of_fqn(t)
                                  for t in u.get("dependent_theorems", []))
                      if f is not None)
        if fams:
            counts = Counter(fams)
            best = sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))[0][0]
            links = [{"id": u["id"], "family": fam, "weight": n}
                     for fam, n in sorted(counts.items())]
        else:
            best, links = None, []
        hyp_meta[u["id"]] = (best, links)

    frontier = [
        {
            "id": e.get("id"),
            "frontier_impact": e.get("frontier_impact"),
            "status": e.get("status"),
            "tier": e.get("tier"),
            "eliminability": e.get("eliminability"),
            "is_apex": e.get("is_apex", False),
            "family": hyp_meta.get(e.get("id"), (None, []))[0],
        }
        for e in atlas.get("frontier", [])
    ]
    frontier_links = [l for e in atlas.get("frontier", [])
                      for l in hyp_meta.get(e.get("id"), (None, []))[1]]

    obstructions = [
        {
            "id": o.get("id"),
            "fork_id": o.get("fork_id"),
            "nogo_kind": o.get("nogo_kind"),
            "false_statement": o.get("false_statement"),
            "backing_theorems": o.get("backing_theorems", []),
            "kernel_pure": o.get("kernel_pure"),
            "registered": o.get("registered", False),
            "family": (family_of_fqn(o.get("backing_theorems", [None])[0])
                       if o.get("backing_theorems") else None),
        }
        for o in atlas.get("obstructions", [])
    ]

    return {
        "schema_version": SCHEMA_VERSION,
        "summary": atlas.get("summary", {}),
        "provinces": province_list,
        "frontier": frontier,
        "frontier_links": frontier_links,
        "obstructions": obstructions,
    }


def counts_at_revision(rev: str) -> dict | None:
    """Parse docs/counts.json at a git revision, tolerating schema drift."""
    try:
        raw = subprocess.run(
            ["git", "show", f"{rev}:docs/counts.json"],
            capture_output=True, text=True, cwd=ROOT, check=True,
        ).stdout
        c = json.loads(raw)
    except (subprocess.CalledProcessError, json.JSONDecodeError):
        return None
    lean = c.get("lean", c)  # older schemas were flat
    out = {}
    for key, aliases in {
        "declarations": ("total_declarations",),
        "theorems": ("theorems_total", "theorems"),
        "modules": ("modules",),
        "definitions": ("definitions",),
    }.items():
        for a in aliases:
            if a in lean:
                out[key] = lean[a]
                break
    return out or None


def build_velocity() -> dict:
    log = subprocess.run(
        ["git", "log", "--format=%H %aI", "--follow", "--", "docs/counts.json"],
        capture_output=True, text=True, cwd=ROOT, check=True,
    ).stdout.strip().splitlines()
    # oldest first; keep the last sample of each calendar day
    entries = [line.split() for line in reversed(log) if line.strip()]
    by_day: dict[str, dict] = {}
    for rev, iso in entries:
        day = iso[:10]
        counts = counts_at_revision(rev)
        if counts:
            by_day[day] = {"date": day, **counts}
    series = [by_day[d] for d in sorted(by_day)]
    return {
        "schema_version": SCHEMA_VERSION,
        "source": "git history of docs/counts.json (last sample per day)",
        "series": series,
    }


def build_counts_summary(counts: dict) -> dict:
    lean = counts.get("lean", {})
    return {
        "schema_version": SCHEMA_VERSION,
        "counts_generated": counts.get("generated"),
        "declarations": lean.get("total_declarations"),
        "theorems": lean.get("theorems_total"),
        "theorems_substantive": lean.get("theorems_substantive"),
        "modules": lean.get("modules"),
        "axioms": lean.get("axioms"),
        "sorries": lean.get("sorry_declarations"),
        "aristotle_proved": counts.get("aristotle", {}).get("aristotle_proved"),
        "aristotle_runs": counts.get("aristotle", {}).get("aristotle_runs"),
        "pytest_cases": counts.get("python", {}).get("pytest_cases"),
        "figures": counts.get("python", {}).get("figures"),
        "notebooks": counts.get("python", {}).get("notebooks"),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", default="build/web_export",
                        help="output directory (default: build/web_export)")
    args = parser.parse_args()

    out = ROOT / args.out
    out.mkdir(parents=True, exist_ok=True)

    atlas = load_atlas()
    counts = load_counts()
    generated_at = datetime.now(timezone.utc).isoformat(timespec="seconds")

    site_atlas = build_site_atlas(atlas)
    site_atlas["family_edges"] = build_family_edges(load_deps())

    payloads = {
        "site_atlas.json": site_atlas,
        "velocity.json": build_velocity(),
        "counts_summary.json": build_counts_summary(counts),
    }

    manifest = {
        "schema_version": SCHEMA_VERSION,
        "generated_at": generated_at,
        "files": {},
    }
    for name, payload in payloads.items():
        payload["generated_at"] = generated_at
        blob = json.dumps(payload, separators=(",", ":"), sort_keys=True)
        (out / name).write_text(blob)
        manifest["files"][name] = {
            "sha256": hashlib.sha256(blob.encode()).hexdigest(),
            "bytes": len(blob),
        }
        print(f"  {name}: {len(blob)/1024:.0f} KB")
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2))
    print(f"wrote {out}/manifest.json")

    site_kb = manifest["files"]["site_atlas.json"]["bytes"] / 1024
    if site_kb > 300:
        print(f"WARNING: site_atlas.json {site_kb:.0f} KB exceeds 300 KB budget",
              file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
