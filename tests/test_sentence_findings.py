"""Reading-while-blocked: sentences resolve to the findings that land on them (ADR-012 S4).

WHY THIS RESOLVER EXISTS AT ALL, AND WHY IT IS NOT `FLAGS`
----------------------------------------------------------
D15 S4 specified *"ask the graph whether any open `ReviewFinding` FLAGS it"*. Measured before
building: **all 4,895 `FLAGS` edges point at `paper:` nodes.** Findings attach to papers,
never to formulas or theorems, so that query returns nothing for every artifact — a marker
rendering on **no sentence, ever**, indistinguishable from a clean corpus.

The relation that exists is the finding's `Location:` line versus the sentence's
`tex_line_start` / `tex_line_end`. `test_flags_edges_cannot_answer_this_question` pins the
measurement, so if `FLAGS` ever gains artifact targets somebody is told to revisit the design
rather than discovering it by accident.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

import sentence_findings as sf  # noqa: E402


def _f(fid, target, severity="major", status="open"):
    return {"id": fid, "label": f"label {fid}",
            "meta": {"status": status, "severity": severity, "target": target,
                     "lane": "prose"}}


# ── The parser ────────────────────────────────────────────────────────────────────────

@pytest.mark.parametrize("raw,expect", [
    ("`papers/D12/paper_draft.tex:666`", ("D12", 666, 666)),
    ("`papers/D12/paper_draft.tex:635-669`", ("D12", 635, 669)),
    # ⚠️ NO `papers/` PREFIX — a real on-disk shape. A first version of the pattern required
    # the prefix and silently dropped these.
    ("`paper26_bh_entropy/paper_draft.tex:311-329`", ("paper26_bh_entropy", 311, 329)),
    # An en-dash: reviewers type them.
    ("`papers/I1/paper_draft.tex:10–20`", ("I1", 10, 20)),
    # Trailing prose after the location must not defeat it.
    ("`papers/D3/paper_draft.tex:12-14` vs the registry", ("D3", 12, 14)),
])
def test_the_shapes_that_are_actually_on_disk_all_parse(raw, expect):
    assert sf.parse_target(raw) == expect


@pytest.mark.parametrize("raw", [
    None, "", "`lean/SKEFTHawking/BHEntropyMicroscopic.lean:604-606`",
    "`scripts/validate.py` — no check verifies this", "`papers/D1/paper_draft.tex`",
])
def test_a_non_draft_location_returns_None_rather_than_a_guess(raw):
    """`None` is a legitimate answer with a large population behind it, not an error. A
    parser that guessed here would place findings on sentences they say nothing about."""
    assert sf.parse_target(raw) is None


def test_a_reversed_range_is_normalised_not_dropped():
    assert sf.parse_target("`papers/D1/paper_draft.tex:900-100`") == ("D1", 100, 900)


# ── The overlap ───────────────────────────────────────────────────────────────────────

_SENTS = [
    {"id": "s:before", "tex_line_start": 10, "tex_line_end": 20},
    {"id": "s:overlap-start", "tex_line_start": 95, "tex_line_end": 105},
    {"id": "s:inside", "tex_line_start": 110, "tex_line_end": 120},
    {"id": "s:overlap-end", "tex_line_start": 195, "tex_line_end": 205},
    {"id": "s:after", "tex_line_start": 300, "tex_line_end": 310},
    {"id": "s:no-location"},
]
_NODES = [_f("review:x:D1:1", "`papers/D1/paper_draft.tex:100-200`")]


def test_only_the_overlapping_sentences_are_marked():
    got = sf.findings_for_sentences("D1", _SENTS, _NODES)
    marked = sorted(k for k, v in got.items() if v)
    assert marked == ["s:inside", "s:overlap-end", "s:overlap-start"]


def test_a_sentence_with_no_location_is_ABSENT_not_empty():
    """⚠️ THREE STATES. `[]` means asked-and-clean; a missing key means the question was
    never asked. Collapsing them renders 'unknown' and 'fine' identically, which is the
    defect this whole surface exists to make impossible."""
    got = sf.findings_for_sentences("D1", _SENTS, _NODES)
    assert got["s:after"] == []
    assert "s:no-location" not in got


def test_a_finding_in_a_DIFFERENT_draft_never_marks():
    got = sf.findings_for_sentences("D2", _SENTS, _NODES)
    assert all(v == [] for v in got.values())


def test_closed_findings_do_not_mark():
    """A marker says 'this is broken NOW'."""
    nodes = [_f("review:x:D1:9", "`papers/D1/paper_draft.tex:100-200`", status="fixed")]
    assert all(v == [] for v in sf.findings_for_sentences("D1", _SENTS, nodes).values())


def test_a_single_line_target_marks_the_sentence_containing_it():
    nodes = [_f("review:x:D1:2", "`papers/D1/paper_draft.tex:115`")]
    got = sf.findings_for_sentences("D1", _SENTS, nodes)
    assert [k for k, v in got.items() if v] == ["s:inside"]


# ── Coverage — what the layer CANNOT see ──────────────────────────────────────────────

def test_the_coverage_buckets_PARTITION_the_open_population():
    """The same complement discipline the readiness ratchets use, for the same reason: a
    partition asserted in prose drifts. Here it is asserted in the function itself."""
    nodes = [
        _f("a", "`papers/D1/paper_draft.tex:1`"),
        _f("b", "`lean/SKEFTHawking/X.lean:5`"),
        _f("c", None),
        _f("d", "`papers/D1/paper_draft.tex:9`", status="fixed"),   # closed: not counted
    ]
    cov = sf.coverage(nodes)
    assert cov["open_findings"] == 3
    assert cov["placeable_on_a_sentence"] == 1
    assert cov["target_is_not_a_draft_location"] == 1
    assert cov["carry_no_target"] == 1


def test_the_caveat_names_the_population_it_CANNOT_mark():
    """⚠️ A reader who sees an unmarked sentence concludes nothing is wrong with it. That
    conclusion is only warranted for the fraction of findings this layer can place, so the
    caveat is not decoration — it is the thing that keeps the marker honest."""
    cov = sf.coverage([_f("a", "`papers/D1/paper_draft.tex:1`"), _f("c", None)])
    text = sf.coverage_caveat(cov)
    assert "carry no location" in text
    assert "NOT evidence" in text


# ── The measurement the design rests on ───────────────────────────────────────────────

@pytest.mark.slow
def test_flags_edges_cannot_answer_this_question():
    """⚠️ PINS THE MEASUREMENT THAT KILLED THE ORIGINAL DESIGN. Every `FLAGS` edge targets a
    `paper:` node. If that ever changes, this test fails and whoever changed it is told to
    revisit S4 — rather than discovering by accident that a better relation existed."""
    from build_graph import build_graph_json
    flags = [e for e in build_graph_json()["links"] if e.get("type") == "FLAGS"]
    assert flags, "no FLAGS edges at all — this assertion would pass over nothing"
    non_paper = {e["target"].split(":")[0] for e in flags} - {"paper"}
    assert not non_paper, (
        f"FLAGS now targets {sorted(non_paper)} as well as papers — S4 resolves findings to "
        f"sentences by LOCATION precisely because it could not resolve them by FLAGS. "
        f"Re-read `scripts/sentence_findings.py`'s header before extending it")


@pytest.mark.slow
def test_the_live_corpus_actually_produces_markers():
    """Non-vacuity against production data: a resolver that marks nothing is
    indistinguishable from a clean corpus, which is the failure being prevented."""
    cov = sf.coverage()
    assert cov["placeable_on_a_sentence"] > 0
    assert cov["drafts_covered"] > 1
    assert cov["carry_no_target"] > 0, (
        "no open finding lacks a target — then the caveat is describing an empty "
        "population and should be re-derived rather than displayed")
