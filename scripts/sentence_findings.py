"""Resolve manuscript sentences to the open findings that land on them (ADR-012 D15 S4).

THE QUESTION THIS ANSWERS
-------------------------
*"I am reading §4 — is anything under it broken?"*

⚠️ **THAT IS A QUESTION ABOUT WHERE THE READER IS, NOT ABOUT THE PROVENANCE CHAIN BENEATH
THEM**, and getting that distinction wrong is what made the original specification
unbuildable. D15 S4 said to *"ask the graph whether any open `ReviewFinding` FLAGS it"*.
Measured at HEAD: **all 4,895 `FLAGS` edges point at `paper:` nodes.** A finding is attached
to the paper it was filed against — never to a formula, a theorem or a parameter. Built as
specified, the marker would have rendered on **no sentence, ever**, and its emptiness would
have been indistinguishable from a clean corpus: this repository's signature defect,
installed inside the surface built to surface defects.

What findings *do* carry is `target`, parsed from the reviewer's `- **Location:**` line —
typically `papers/D12/paper_draft.tex:666` or `paper26_bh_entropy/paper_draft.tex:311-329`.
Sentences carry `tex_line_start` / `tex_line_end`. **Overlapping line ranges in the same
draft is a real relation, and it is the one the operator's question is actually about.**

WHAT THIS MODULE REFUSES TO DO
------------------------------
It refuses to report a marker population without also reporting the population it **cannot**
see. `coverage()` returns both, and the caller is expected to surface them together. A marker
layer that is silent about what it cannot mark is the same failure one level down: a sentence
with no marker would otherwise read as "nothing is wrong here" when the truth is "no finding
in this corpus carries a location precise enough to say".
"""
from __future__ import annotations

import re
from collections import defaultdict
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent

#: `[papers/]<draft-dir>/paper_draft.tex:<line>[-<line>]`, the shapes actually on disk.
#:
#: ⚠️ THE `papers/` PREFIX IS OPTIONAL, and that is measured rather than defensive. A first
#: version of this pattern required it and silently dropped every target written as
#: `paper26_bh_entropy/paper_draft.tex:311-329` — 3 findings' worth in the live corpus, and a
#: shape a reviewer will keep producing because it reads naturally. Both dash characters are
#: accepted for the same reason: reviewers type an en-dash.
_TARGET_RE = re.compile(
    r"(?:papers/)?([A-Za-z0-9_.+-]+)/(?:paper_draft\.tex):(\d+)(?:\s*[-–]\s*(\d+))?")


def parse_target(target: str | None) -> tuple[str, int, int] | None:
    """`(draft_dir, first_line, last_line)` or `None` when it is not a draft location.

    `None` is a legitimate, common answer — a target naming `lean/…`, `scripts/…` or a `.tex`
    with no line number is a real finding that simply cannot be placed on a sentence. The
    caller must COUNT those, never discard them.
    """
    if not target:
        return None
    m = _TARGET_RE.search(target)
    if not m:
        return None
    lo = int(m.group(2))
    hi = int(m.group(3) or m.group(2))
    return (m.group(1), min(lo, hi), max(lo, hi))


def _open_findings(nodes: list[dict] | None = None) -> list[dict]:
    if nodes is None:
        import sys
        sys.path.insert(0, str(PROJECT_ROOT / "scripts"))
        from build_graph import extract_review_finding_nodes
        nodes = extract_review_finding_nodes()
    return [n for n in nodes if (n.get("meta") or {}).get("status") == "open"]


def index_by_draft(nodes: list[dict] | None = None) -> dict[str, list[dict]]:
    """`{draft_dir: [{id, first, last, severity, lane, label}, …]}` for OPEN findings only.

    Closed findings are excluded deliberately: a marker exists to say *this is broken now*.
    """
    out: dict[str, list[dict]] = defaultdict(list)
    for n in _open_findings(nodes):
        m = n.get("meta") or {}
        loc = parse_target(m.get("target"))
        if not loc:
            continue
        draft, first, last = loc
        out[draft].append({
            "id": n["id"],
            "first": first,
            "last": last,
            "severity": str(m.get("severity", "")),
            "lane": str(m.get("lane") or "unclassified"),
            "label": str(n.get("label", ""))[:120],
        })
    return dict(out)


def findings_for_sentences(draft: str, sentences: list[dict],
                           nodes: list[dict] | None = None) -> dict[str, list[dict]]:
    """`{sentence_id: [finding, …]}` — the open findings whose lines overlap the sentence.

    ⚠️ A sentence missing `tex_line_start` gets **no entry at all**, rather than an empty
    list. The two are different answers — "no finding lands here" versus "this sentence has
    no location, so the question was never asked" — and the renderer must be able to tell
    them apart. `coverage()` counts the second population.
    """
    by_draft = index_by_draft(nodes).get(draft, [])
    out: dict[str, list[dict]] = {}
    for s in sentences:
        start, end = s.get("tex_line_start"), s.get("tex_line_end")
        if not isinstance(start, int):
            continue
        last = end if isinstance(end, int) else start
        lo, hi = min(start, last), max(start, last)
        hits = [f for f in by_draft if f["first"] <= hi and f["last"] >= lo]
        out[str(s.get("id"))] = sorted(
            hits, key=lambda f: (f["first"], f["id"]))
    return out


def coverage(nodes: list[dict] | None = None) -> dict:
    """What the marker layer CAN and CANNOT see. Both, always, in one call.

    Every open finding lands in exactly one bucket, and the buckets sum to the population —
    the same complement discipline the readiness ratchets use, for the same reason: a
    partition asserted in prose is one that drifts.
    """
    findings = _open_findings(nodes)
    placeable = no_target = elsewhere = 0
    for n in findings:
        m = n.get("meta") or {}
        target = m.get("target")
        if not target:
            no_target += 1
        elif parse_target(target):
            placeable += 1
        else:
            elsewhere += 1
    assert placeable + no_target + elsewhere == len(findings), (
        "the coverage buckets do not partition the open population")
    return {
        "open_findings": len(findings),
        "placeable_on_a_sentence": placeable,
        "carry_no_target": no_target,
        "target_is_not_a_draft_location": elsewhere,
        "drafts_covered": len(index_by_draft(nodes)),
    }


def coverage_caveat(cov: dict) -> str:
    """One sentence the pane must render beside the markers. Not optional.

    A reader who sees an unmarked sentence will conclude nothing is wrong with it. That
    conclusion is only warranted for the fraction of findings this layer can actually place.
    """
    return (
        f"Markers cover {cov['placeable_on_a_sentence']} of {cov['open_findings']} open "
        f"findings — those whose Location names a draft line. "
        f"{cov['carry_no_target']} carry no location at all and "
        f"{cov['target_is_not_a_draft_location']} point outside the manuscripts "
        f"(Lean, scripts, docs). An unmarked sentence is NOT evidence of a clean sentence.")


if __name__ == "__main__":  # pragma: no cover — operator convenience
    import json
    print(json.dumps(coverage(), indent=2))
    print(coverage_caveat(coverage()))
