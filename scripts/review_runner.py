#!/usr/bin/env python3
"""
review_runner.py — Phase 6i Wave 7.2 bundle-aware review orchestrator
=====================================================================

Orchestrates a bundle-level Stage-13 review by walking the lifted
source material (per `docs/PAPER_DRAFT_MAPPING.md` §2 + the per-bundle
anchor list at `docs/agents/claims-reviewer-bundle-prompts.md`) and
producing a per-bundle review document at
`papers/AutomatedReviews/<DATE>-bundle-stage13/<bundle>.md`.

The actual Stage-13 LLM-driven review work is performed by the
`skeft-qa:claims-reviewer` and `skeft-qa:figure-reviewer` agents,
which accept a `bundle_target` argument. This script is the thin
orchestration layer that:

  1. Resolves a bundle's lifted source set from `PAPER_DRAFT_MAPPING.md`.
  2. Looks up the bundle's anchor list from
     `docs/agents/claims-reviewer-bundle-prompts.md`.
  3. Emits a per-bundle review-prep brief that the agent consumes.
  4. After the agent runs, validates the produced review document
     against the bundle anchor list (anchor coverage check).

Usage
-----
    uv run python scripts/review_runner.py --list-bundles
    uv run python scripts/review_runner.py --bundle L1 --prep-brief
    uv run python scripts/review_runner.py --bundle L1 --review-doc <path>
                                              # validates anchor coverage
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
PAPERS_DIR = PROJECT_ROOT / "papers"
MAPPING_DOC = PROJECT_ROOT / "docs" / "PAPER_DRAFT_MAPPING.md"
ANCHOR_DOC = PROJECT_ROOT / "docs" / "agents" / "claims-reviewer-bundle-prompts.md"

sys.path.insert(0, str(PROJECT_ROOT / "scripts"))
from bundle_migration import parse_mapping  # noqa: E402
from bundle_registry import TIER_OF  # noqa: E402
from sentence_state import _VALID_BUNDLE_TARGETS  # noqa: E402


def list_bundles() -> dict[str, dict]:
    """Build per-bundle index: {bundle: {sources: [paper_keys],
    tier: int, anchor_section_present: bool}}."""
    mapping_text = MAPPING_DOC.read_text()
    assignments = parse_mapping(mapping_text)
    anchor_text = ANCHOR_DOC.read_text() if ANCHOR_DOC.exists() else ""

    by_bundle: dict[str, list[str]] = {b: [] for b in _VALID_BUNDLE_TARGETS}
    for paper, a in assignments.items():
        for b in a["bundle_destinations"]:
            by_bundle[b].append(paper)

    # Tier map from THE roster source of truth (scripts/bundle_registry.py).
    # This used to be a local literal that stopped at D9, so it raised
    # KeyError('D10') for every bundle authorized since 2026-06-29. Because
    # this function builds the WHOLE listing in one pass, that single unmapped
    # code took down the documented Stage-13 prep-brief entry point for every
    # bundle — from D10's first lift until 98660389.
    # `.get(b, 1)` is belt-and-braces: an unregistered code degrades to the
    # deep-paper tier instead of crashing the listing again.
    tiers = TIER_OF

    out: dict[str, dict] = {}
    for b in sorted(_VALID_BUNDLE_TARGETS):
        anchor_section = bool(re.search(rf"### {re.escape(b)}\.\s", anchor_text))
        out[b] = {
            "tier": tiers.get(b, 1),
            "sources": sorted(by_bundle[b]),
            "source_count": len(by_bundle[b]),
            "anchor_section_present": anchor_section,
        }
    return out


def emit_prep_brief(bundle: str) -> str:
    """Emit a markdown review-prep brief for the given bundle: tier,
    sources, anchor list pointer, scope guidance."""
    if bundle not in _VALID_BUNDLE_TARGETS:
        raise ValueError(
            f"unknown bundle {bundle!r}; must be one of "
            f"{sorted(_VALID_BUNDLE_TARGETS)}"
        )
    info = list_bundles()[bundle]

    profile_per_tier = {
        0: ("Tier 0 — Flagship (review-paper style)",
            "Independent reviewer-anchored against ARCHITECTURE_SCOPE.md, "
            "RESEARCH_STATUS_OVERVIEW.md, and shipped Tier 1 bundle "
            "published versions."),
        1: ("Tier 1 — Deep paper (bundle-level review)",
            "Intra-bundle consistency across lifted sections + "
            "cross-bundle consistency for cross-bridge claims + "
            "architectural-scope sidebar correctly slice-restricted."),
        2: ("Tier 2 — PRL splash (single-paper depth, stand-alone)",
            "Stand-alone review; reviewer does NOT penalize the absence "
            "of broader-scope content. Carry the bundle-specific "
            "Stage-13 anchor."),
        3: ("Tier 3 — Infrastructure (software / methodology paper)",
            "Software-paper review pattern; reproducibility checks; "
            "each worked case traces to a reproducible Aristotle run ID "
            "or commit-pinned counterexample."),
        4: ("Tier 4 — Experimental letter (lightweight + device audit)",
            "Letter review + device-parameter audit pass against the "
            "experimental team's published device specs."),
    }
    profile_label, profile_desc = profile_per_tier[info["tier"]]

    lines = [
        f"# Bundle {bundle} — Stage-13 review prep brief",
        "",
        f"**Tier:** {info['tier']}",
        f"**Profile:** {profile_label}",
        "",
        profile_desc,
        "",
        f"**Sources ({info['source_count']}):**",
        "",
    ]
    for src in info["sources"]:
        lines.append(f"- `papers/{src}/paper_draft.tex`")
    lines.extend([
        "",
        "**Anchor list:** see `docs/agents/claims-reviewer-bundle-prompts.md`"
        f" §`{bundle}`.",
        "",
        "**Required reads (in order):**",
        "1. `CLAUDE.md` — project conventions",
        "2. `docs/PAPER_STRATEGY.md` — bundle architecture",
        "3. `docs/PAPER_DRAFT_MAPPING.md` — per-draft → per-bundle assignment",
        "4. `docs/agents/claims-reviewer-bundle-prompts.md` — per-bundle "
        "anchor list",
        "5. `docs/WAVE_EXECUTION_PIPELINE.md` Stage 13 — adversarial review",
        "",
        "**Cross-bundle consistency:** for any anchor cited as a"
        " cross-bridge in `claims-reviewer-bundle-prompts.md`, run"
        " `validate.py --check bundle_consistency` (Wave 7.3) to confirm"
        " the cross-bridge claim agrees across bundle boundaries.",
        "",
        "**Output:** write the review document to "
        f"`papers/AutomatedReviews/<DATE>-bundle-stage13/{bundle}.md`.",
    ])
    return "\n".join(lines)


def validate_review_doc(bundle: str, doc_path: Path) -> tuple[bool, list[str]]:
    """Validate that a bundle review document exists and references all
    of the bundle's anchor list items at least once. Returns (ok,
    issues)."""
    if not doc_path.exists():
        return (False, [f"review document not found: {doc_path}"])
    text = doc_path.read_text()
    issues: list[str] = []

    # Cheap heuristic: check that every source paper is at least
    # *mentioned* by name in the review document.
    info = list_bundles()[bundle]
    for src in info["sources"]:
        if src not in text:
            issues.append(f"source paper '{src}' not mentioned in review")

    # Bundle code itself should appear at least once.
    if bundle not in text:
        issues.append(f"bundle code '{bundle}' not mentioned in review")

    return (not issues, issues)


#: Roots a `- **Location:**` value may be written against, in resolution order.
#: ⚠️ The review corpus writes targets **`papers/`-relative** (`D10_initial_draft/
#: paper_draft.tex:88`), not repo-relative. Resolving only from the repo root made most
#: targets miss, and the brief then told the worker the finding was STALE — a false
#: staleness claim on a live file, in the one artifact the brief asks a worker to trust.
_TARGET_ROOTS: tuple[str, ...] = ("", "papers")


def _workspace_root() -> Path | None:
    """The multi-repo workspace this repo sits in, or `None` outside one.

    ⚠️ Via `find_workspace`, never a hardcoded parent-walk — that is the repo convention,
    and a parent-walk breaks in a worktree.
    """
    try:
        from src.core.workspace import find_workspace
        return Path(find_workspace())
    except Exception:
        return None


def _resolve_target(target: str) -> tuple[Path | None, list[str]]:
    """`(path, tried)` — the file a `Location:` names, and every root attempted.

    Returning the attempts is what makes the unresolved branch actionable: "does not
    resolve" plus the paths tried is a measurement; "does not resolve" alone is a verdict
    the reader cannot check.

    ⚠️ Some targets are WORKSPACE-relative, not repo-relative — `temporary/working-docs/...`
    resolves in the workspace that holds this repo, not inside it. Those are live files, and
    resolving only from the repo root reported them as stale, which is the same false-
    staleness defect the `papers/` root was added to fix, one directory further out.
    """
    head = target.split(":")[0].strip()
    tried: list[str] = []
    roots: list[Path] = [PROJECT_ROOT / r if r else PROJECT_ROOT for r in _TARGET_ROOTS]
    ws = _workspace_root()
    if ws is not None and ws != PROJECT_ROOT:
        roots.append(ws)
    for base in roots:
        cand = base / head
        try:
            shown = str(cand.relative_to(PROJECT_ROOT))
        except ValueError:                       # outside the repo — show it absolute
            shown = str(cand)
        tried.append(shown)
        if cand.is_file():
            return cand, tried
    return None, tried


def emit_finding_brief(finding_id: str) -> str:
    """Generated orientation for ONE finding (ADR-012 D17).

    ⚠️ Orientation is GENERATED, not gathered. Re-deriving it per finding from cold context
    is the expensive way, and it is what the operator's step 1 was reacting to: the finding
    carries its own pointers, so the worker does not go looking. This is also what makes the
    decision package affordable — four of its five elements are generated rather than
    researched.

    RAISES on an unknown id. An empty brief is worse than an error: it reads as "nothing to
    orient on" when the truth is "the finding was not found".
    """
    import subprocess
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from build_graph import extract_review_finding_nodes, finding_is_dispatchable

    nodes = extract_review_finding_nodes()
    node = next((n for n in nodes if n["id"] == finding_id), None)
    if node is None:
        raise KeyError(
            f"{finding_id} names no minted finding. An empty brief would read as 'nothing "
            f"to orient on' when the truth is 'not found'.")

    # THE production consumer of BLOCKED_BY. A dependency edge whose only caller is a test
    # is an edge nothing observes working — `PRODUCES` sat expired for a full wave that way.
    _ids = {n["id"] for n in nodes}
    _closed = {n["id"] for n in nodes
               if (n.get("meta") or {}).get("status") in ("fixed", "accepted")}
    dispatchable = finding_is_dispatchable(node, _ids, _closed)

    m = node["meta"]
    target = (m.get("target") or "").strip("`") or None
    out = [f"# Orientation — {finding_id}", "",
           f"**{node.get('name', '')[:160]}**", "",
           f"- SEVERITY: {m.get('severity')}   STATUS: {m.get('status')}",
           f"- LANE: {m.get('lane')}",
           f"- BLOCKS: {m.get('blocks') or '(none declared)'}",
           f"- VERIFY: {m.get('verify') or '(none declared)'}",
           f"- BLOCKED-BY: {', '.join(m.get('blocked_by') or []) or '(nothing)'}",
           f"- DISPATCHABLE: {'yes' if dispatchable else 'NO — every blocker above must '
                                                        'close or release first'}",
           f"- NEEDS-OPERATOR: {m.get('needs_operator') or 'no'}",
           f"- REVIEW: {m.get('review_file')}", ""]

    out += ["## TARGET", ""]
    if not target:
        out += ["⚠️ No `- **Location:**` line on this finding, so there is nothing to point",
                "at. It is not dispatchable until one is added.", ""]
    else:
        out += [f"`{target}`", ""]
        path, tried = _resolve_target(target)
        if path is not None:
            try:
                rel = str(path.relative_to(PROJECT_ROOT))
                outside = ""
            except ValueError:
                # A workspace-level target. Say so — a worker who assumes repo-relative
                # will not find it, and `git log` below covers only this repo.
                rel, outside = str(path), "  ⚠️ OUTSIDE this repo (workspace-level path)"
            out += [f"Exists at `{rel}`.{outside} {path.stat().st_size} bytes.", ""]
            out += ["## GIT HISTORY", ""]
            try:
                log = subprocess.run(
                    ["git", "log", "-5", "--oneline", "--", str(path)],
                    cwd=str(PROJECT_ROOT), capture_output=True, text=True, timeout=20)
                out += ["```", log.stdout.strip() or "(no history)", "```", ""]
            except Exception as exc:
                out += [f"(git log unavailable: {exc})", ""]
        else:
            out += ["⚠️ The target does not resolve to a file on disk. Re-measure before",
                    "acting: a finding pointing at a moved or renamed path is stale.",
                    "", "Tried:"] + [f"- `{t}`" for t in tried] + [""]

    out += ["## ROADMAP", ""]
    hits, unread = [], []
    rm = PROJECT_ROOT / "docs" / "roadmaps"
    if target and rm.is_dir():
        stem = Path(target.split(":")[0]).stem
        for r in sorted(rm.glob("*.md")):
            try:
                if stem and stem in r.read_text(encoding="utf-8", errors="replace"):
                    hits.append(r.name)
            except OSError as exc:
                # ⚠️ NAME the unread files. Swallowing this makes an unreadable corpus
                # print the same reassuring "no roadmap mentions this target" as a genuine
                # absence — absence of measurement rendered as a measurement.
                unread.append(f"{r.name} ({exc.__class__.__name__})")
    out += ([f"- {h}" for h in hits[:5]] if hits else
            ["(no roadmap mentions this target — it may predate the roadmap corpus)"])
    if unread:
        out += ["", f"⚠️ {len(unread)} roadmap(s) could not be read, so this list is "
                    f"INCOMPLETE, not empty: " + ", ".join(unread[:5])]
    out += ["", "## SUBSTRATE DELTA", "",
            "⚠️ Answer explicitly, including 'no': has anything moved since this finding was",
            "filed that should change the target? A finding's scope is a CLAIM, not a",
            "measurement — re-derive it before acting.", ""]
    return "\n".join(out)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description="Phase 6i Wave 7.2 bundle-aware review orchestrator",
    )
    parser.add_argument(
        "--list-bundles", action="store_true",
        help="list all 18 bundles + source paper counts",
    )
    parser.add_argument(
        "--bundle", help="bundle code (one of F, D1-D9, L1-L3, I1-I3, E1-E2)",
    )
    parser.add_argument(
        "--prep-brief", action="store_true",
        help="emit a markdown review-prep brief for the bundle",
    )
    parser.add_argument(
        "--review-doc",
        help="path to a completed review document; validate anchor coverage",
    )
    parser.add_argument(
        "--json", action="store_true",
        help="emit JSON instead of human-readable output",
    )
    parser.add_argument(
        "--finding",
        help="emit generated orientation for ONE finding id (ADR-012 D17)",
    )
    args = parser.parse_args(argv)

    # ⚠️ BEFORE the `--bundle` gate below, which returns 1 on anything without a bundle.
    if args.finding:
        try:
            print(emit_finding_brief(args.finding))
        except KeyError as exc:
            print(f"✗ {exc}", file=sys.stderr)
            return 1
        return 0

    if args.list_bundles:
        info = list_bundles()
        if args.json:
            print(json.dumps(info, indent=2))
        else:
            print(f"{'BUNDLE':6s} {'TIER':4s} {'SRCS':5s}  ANCHOR  SOURCES")
            for b, d in info.items():
                ok = "✓" if d["anchor_section_present"] else "✗"
                srcs = ",".join(d["sources"][:3])
                if d["source_count"] > 3:
                    srcs += f", +{d['source_count'] - 3} more"
                print(f"{b:6s} {d['tier']:4d} {d['source_count']:5d}    {ok}    {srcs}")
        return 0

    if not args.bundle:
        parser.print_help()
        return 1

    if args.review_doc:
        ok, issues = validate_review_doc(args.bundle, Path(args.review_doc))
        if ok:
            print(f"OK — {args.bundle} review at {args.review_doc} covers all "
                  f"sources and anchors.")
            return 0
        else:
            print(f"FAIL — {args.bundle} review at {args.review_doc}:")
            for issue in issues:
                print(f"  - {issue}")
            return 1

    if args.prep_brief:
        print(emit_prep_brief(args.bundle))
        return 0

    parser.print_help()
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
