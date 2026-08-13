"""The Flow board — where every bundle is, and what is holding it (ADR-012 D15, S2).

THE QUESTION THIS ANSWERS
-------------------------
*"Where is everything, and what is the bottleneck?"*

The second half is the part that makes this a routing instrument rather than a status
board. A stage matrix says **D3 is yellow**. The lane overlay says **D3 is held by six
substrate findings** — which names the queue, the agent profile and the gate set that
will close it (D2's lane table). Without the overlay this surface is a prettier
`BUNDLE_READINESS_HEATMAP.md`; with it, it is the thing the operator reads before
deciding where the next worker goes.

WHAT THIS MODULE REFUSES TO DO
------------------------------
**It refuses to render a stage as passed, failed or fine when the truth is that nobody
measured it.** Five separate states in this corpus are *not* a verdict, and every one of
them has previously been rendered as one somewhere in this repository:

1. **A stage with no field at all.** §7.5's read-through is performed by `prose-reviewer`,
   which by design mints no machine state (ADR-012 C3). It renders `not-tracked` — never
   `passed`, never `failed`. A green §7.5 column would be a claim about work no field
   records.
2. **A status value outside the declared enum.** `Phase7a_Roadmap.md` declares
   `pending | green | red`; the live corpus carries five values, three of them undeclared.
   An unrecognised value **renders as itself**, tagged `undeclared`, and is counted in
   `status_census()`. Coercing `pending-redo` to "pending" would erase the fact that a
   completed stage was invalidated by a later append.
3. **A missing artifact.** No `claims_review.json` means Stage 10 never ran (ADR-011
   Phase 2d). That is its own state — not a failure, and emphatically not a pass.
4. **A signal that could not be computed.** The P1-gate roll-up, the freshness legs and
   the manuscript sizing can each fail to measure. Each reports `unmeasured` with its
   reason, and `unmeasured` never rolls up into `green`.
5. **A finding the board cannot attribute to any row.** `coverage()` counts those, and
   the buckets are asserted to partition the open population — the same complement
   discipline `sentence_findings.coverage()` and the readiness ratchets use, for the same
   reason: a partition asserted in prose is one that drifts.

TWO SIGNALS THIS BOARD RENDERS AND DOES NOT VOUCH FOR
-----------------------------------------------------
D15 requires S2 to render a bundle's registered Lean module list and its manuscript
length, and ADR-012 §Overlap requires it to say what guards each, because neither is
sound today and neither is this surface's to fix:

- **TODO-D50** — a registered module can name substrate that was planned and never built,
  so the list is not evidence the modules exist. The count of unresolved registrations is
  measured per row rather than asserted, through `_resolve_module` — the resolver that
  ladder-matches dotted / path-style / bare registrations. Exact matching calls 182 of 444
  registrations nonexistent and would put a fabricated number on this board.
- **TODO-D51** — the length signal decides a PDF is trustworthy by comparing mtimes
  against the draft's input closure. Every bundle `\\input`s `docs/counts.tex`, so one
  byte-identical rewrite of that file blanks the sizing for the entire roster at once.
  An empty length column therefore means *"nobody can size these right now"*, which is not
  the same fact as *"these are the wrong length"*.

Both appear verbatim in `flow_board()['caveats']`, with their live magnitudes.

WIRING
------
`flow_board()` is pure data — no HTML, no Flask, no template. The renderer owns
presentation; this module owns truth. Every expensive input is injectable so a caller that
already holds the graph pays for it once:

    board = flow_board(gate_nodes=[n for n in graph["nodes"]
                                   if n["type"] == "ReadinessGate"])
"""
from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "scripts"))

# ⚠️ THE ROSTER IS IMPORTED, NEVER WRITTEN DOWN. `bundle_registry_consistency` Leg C is an
# AST walk over `scripts/**/*.py` for exactly the literal this module would otherwise
# contain, and it exists because the roster was hardcoded in seven places and every
# omission failed differently and silently. See `scripts/bundle_registry.py`'s docstring.
from bundle_registry import (  # noqa: E402
    BUNDLE_CODES,
    BUNDLE_TITLES,
    TIER_OF,
    bundle_sort_key,
)

PAPERS_DIR = PROJECT_ROOT / "papers"


# ── Vocabulary ────────────────────────────────────────────────────────────────────────

#: The enum `Phase7a_Roadmap.md` declares for every `stage*_status` field.
#:
#: ⚠️ This is the DECLARED set, not the live one, and the gap between them is a finding
#: this board surfaces rather than absorbs. `bundle_readiness._STAGE_STATUS_ENUM` is the
#: measured live vocabulary; a value in the live set but not this one renders verbatim and
#: is reported by `status_census()` under `undeclared_by_roadmap`.
ROADMAP_DECLARED_STATUSES: frozenset[str] = frozenset({"pending", "green", "red"})

#: Every kind a cell may carry. Asserted on emission — a typo'd kind would otherwise reach
#: the renderer, which would fall through to its default styling and paint an unknown state
#: in a known state's colour.
CELL_KINDS: frozenset[str] = frozenset({
    "green",        # affirmatively done, by this column's own bar
    "red",          # affirmatively failed
    "pending",      # declared, in the declared enum, not yet done
    "warning",      # advisory: measured, not clean, not blocking
    "absent",       # the artifact or field does not exist — a state, not a verdict
    "not-tracked",  # no field exists for this stage BY DESIGN (§7.5)
    "unmeasured",   # the signal exists but could not be computed here and now
    "undeclared",   # a value outside the roadmap enum, rendered verbatim
})


class Column:
    """One board column: its key, its label, and the fields it actually reads.

    `source` is the field list rather than a prose description so a reader can check the
    column against the metadata without leaving this file.
    """

    __slots__ = ("key", "label", "source", "note")

    def __init__(self, key: str, label: str, source: str, note: str = "") -> None:
        self.key, self.label, self.source, self.note = key, label, source, note

    def as_dict(self) -> dict:
        return {"key": self.key, "label": self.label,
                "source": self.source, "note": self.note}


#: The columns D15 specifies, in render order. Restricted to stages carrying real machine
#: state — a column over a stage with no field is either `not-tracked` (§7.5, which is
#: listed because the reader must be told it is untracked) or absent from this tuple.
COLUMNS: tuple[Column, ...] = (
    Column("draft_exists", "draft",
           "papers/<B>/paper_draft.tex + paper_draft.pdf"),
    Column("read_through", "§7.5 read-through", "(no field exists)",
           "the `prose-reviewer` mints no machine state by design (ADR-012 C3), so this "
           "column can only ever say NOT TRACKED. It is rendered rather than dropped "
           "because a missing column reads as a stage nobody runs."),
    Column("stage9_figure", "S9 figure", "stage9_status"),
    Column("stage10_claims", "S10 claims",
           "stage10_status + papers/<B>/claims_review.json",
           "artifact absence is its own state (ADR-011 Phase 2d): GREEN is withheld, not "
           "granted, when Stage 10 left nothing behind."),
    Column("stage12_sync", "S12 sync",
           "scripts/check_bundle_source_freshness.check()"),
    Column("stage13_adversarial", "S13 adversarial",
           "stage13_status + stage13_review_kind + stage13_redo_required",
           "only a `full-adversarial` review kind earns green."),
    Column("submission", "submission",
           "readiness_submission_gate (ReadinessGate nodes) + blockers_open"),
)


def _cell(kind: str, value: str, **extra) -> dict:
    """One cell. `kind` is validated here so an unknown kind cannot reach a renderer."""
    if kind not in CELL_KINDS:
        raise ValueError(f"unknown cell kind {kind!r}; known kinds are "
                         f"{sorted(CELL_KINDS)}")
    return {"kind": kind, "value": value, **extra}


def _status_cell(raw, *, green_ok: bool = True, green_withheld: str = "") -> dict:
    """A `stage*_status` value as a cell, WITHOUT coercing anything it does not know.

    ⚠️ The one rule that matters here: an unrecognised value renders as **itself**. The
    tempting shape is `kind = "green" if raw == "green" else "pending"`, which silently
    maps `pending-redo`, `skeleton` and `not_started` onto the nearest declared state and
    destroys the drift D15 says this board must not hide.

    `green_ok=False` means the value says green but a second condition this column also
    requires was not met — the cell keeps the raw value and reports `green_withheld`,
    because "it says green and I do not believe it" and "it does not say green" are
    different facts.
    """
    text = "" if raw is None else str(raw)
    if not text:
        return _cell("absent", "(no value)")
    if text == "green":
        if green_ok:
            return _cell("green", text)
        return _cell("unmeasured", text, green_withheld=green_withheld)
    if text in ROADMAP_DECLARED_STATUSES:
        return _cell("red" if text == "red" else "pending", text)
    return _cell("undeclared", text,
                 detail="outside the roadmap's declared `pending|green|red` enum; "
                        "rendered verbatim, never coerced")


# ── Inputs ────────────────────────────────────────────────────────────────────────────

def _read_metadata(code: str) -> dict | None:
    """`papers/<code>/bundle_metadata.json`, or `None` when absent/unparseable.

    `None` means UNKNOWN. It must never be replaced by `{}`: an empty blob makes every
    field read absent-and-therefore-fine, which is the conflation this whole module is
    written against.
    """
    path = PAPERS_DIR / code / "bundle_metadata.json"
    try:
        return json.loads(path.read_text())
    except (OSError, json.JSONDecodeError):
        return None


def load_finding_nodes() -> list[dict]:
    """Every `ReviewFinding` node. Raises if the population is empty."""
    from build_graph import extract_review_finding_nodes
    nodes = extract_review_finding_nodes()
    if not nodes:
        raise RuntimeError(
            "extract_review_finding_nodes() returned NOTHING. An empty finding "
            "population is a failure of the extractor, not a clean corpus — the overlay "
            "would render every bundle unblocked. Refusing to build the board.")
    return nodes


def load_gate_nodes() -> list[dict]:
    """`ReadinessGate` nodes from a full graph build (~13 s).

    A caller that already holds the graph should pass `gate_nodes=` to `flow_board`
    instead; this is the fallback for a standalone run.
    """
    from build_graph import build_graph_json
    return [n for n in build_graph_json().get("nodes", [])
            if n.get("type") == "ReadinessGate"]


def load_aggregate() -> dict:
    """`bundle_readiness.aggregate_by_bundle` over the live tree.

    ⚠️ Read-only: `resolve_stage13_reviews(backfill=False)` inside it writes no metadata.
    A board that backfilled the artifact it reports on would be its own upstream.
    """
    import bundle_readiness as br
    from bundle_migration import parse_mapping, MAPPING_DOC
    assignments = parse_mapping(MAPPING_DOC.read_text())
    return br.aggregate_by_bundle(assignments, br.load_findings_by_paper())


def load_freshness() -> list[dict]:
    """The S12 freshness findings. Pure — `write_metadata=False` touches no file."""
    import check_bundle_source_freshness as fresh
    return fresh.check(write_metadata=False)


def lane_index(finding_nodes: list[dict]) -> dict[str, str]:
    """`{finding_id: lane}`.

    A finding with no declared lane reads `unclassified`, which `build_graph._parse_lane`
    already supplies — and which is a real answer, not a default: it means the routing
    decision has not been made yet, and `coverage()` counts it so the lane breakdown is
    never mistaken for a complete routing picture.
    """
    return {n["id"]: str((n.get("meta") or {}).get("lane") or "unclassified")
            for n in finding_nodes}


# ── The overlay: the bottleneck signal ────────────────────────────────────────────────

def lane_overlay(open_finding_ids: list[str], lanes: dict[str, str]) -> dict:
    """Open findings on this bundle, broken down by lane. **The point of the board.**

    ⚠️ `open_finding_ids` comes from `aggregate_by_bundle`, whose list is COMPLETE rather
    than a sample (the cap was deliberately moved to the render site there). The overlay
    therefore covers exactly the population the row's counts describe, by construction,
    rather than by two code paths agreeing — and an id the lane index has never seen is
    reported under `unresolved_ids` rather than dropped or defaulted into a lane.
    """
    by_lane: Counter[str] = Counter()
    unresolved: list[str] = []
    for fid in open_finding_ids:
        lane = lanes.get(fid)
        if lane is None:
            unresolved.append(fid)
            continue
        by_lane[lane] += 1
    return {
        "open_total": len(open_finding_ids),
        "by_lane": dict(sorted(by_lane.items(), key=lambda kv: (-kv[1], kv[0]))),
        "unresolved_ids": sorted(unresolved),
        "unclassified": by_lane.get("unclassified", 0),
    }


# ── The soft signals D15 requires rendered, and §Overlap requires guarded ─────────────

def registered_lean_modules(code: str) -> dict:
    """The bundle's registered Lean module list, with its unbuilt registrations named.

    ⚠️ **TODO-D50.** A registration can name substrate that was planned and never built,
    so this list is not evidence the modules exist — which is why `unresolved` is measured
    and rendered beside the count instead of the count standing alone.

    Resolution goes through `_resolve_module`, never exact matching: registrations are
    written dotted, path-style and bare, and `SKEFTHawking.<name>` alone calls 182 of 444
    registrations nonexistent (`reference-measurement-traps-false-absence`).
    """
    from check_bundle_source_freshness import _registered_lean_modules
    from validation.checks.bundles_readiness import _resolve_module

    mods = _registered_lean_modules(code)
    if mods is None:
        return {"measured": False, "count": None, "unresolved": None,
                "note": "append_log.json unreadable — the registration list is "
                        "UNMEASURED, which is not the same as 'registers nothing'"}
    unresolved = sorted(m for m in mods if _resolve_module(m) is None)
    return {
        "measured": True,
        "count": len(mods),
        "modules": sorted(mods),
        "unresolved": unresolved,
        "note": ("this list is hand-typed at lift time and is NOT evidence the modules "
                 "exist in the build (TODO-D50)"),
    }


def manuscript_length(code: str, metadata: dict | None) -> dict:
    """The manuscript-length signal, with the reason it is blank when it is blank.

    ⚠️ **TODO-D51.** Sizing is withheld when the PDF is older than the draft's input
    closure, judged by mtime. Every bundle `\\input`s `docs/counts.tex`, so one
    byte-identical rewrite of that file takes the whole roster to `unmeasured` at once —
    observed 2026-08-11, going from *passed, 4 sized* to *UNVERIFIED, 21 unmeasured* with
    nothing about any manuscript changed. A blank cell here means nobody can size this
    right now; it does not mean the manuscript is the wrong length.

    The measurement itself is `_measure_manuscript`, the same instrument
    `bundle_manuscript_length` uses — deliberately not a second sizer, and deliberately
    not the stored `compiled_pages`, which cannot be told apart from a stale one.
    """
    from validation.checks.bundles_readiness import _measure_manuscript

    target = (metadata or {}).get("length_target") or None
    value, unit, note = _measure_manuscript(code)
    return {
        "measured": value is not None,
        "value": value,
        "unit": unit,
        "target": target,
        "unmeasured_reason": None if value is not None else (note or "unknown"),
        "note": ("staleness is judged by mtime against the draft's input closure, so this "
                 "can blank for the whole roster on one rewrite of a shared input "
                 "(TODO-D51)"),
    }


# ── Columns ───────────────────────────────────────────────────────────────────────────

def _draft_cell(code: str) -> dict:
    tex = (PAPERS_DIR / code / "paper_draft.tex").is_file()
    pdf = (PAPERS_DIR / code / "paper_draft.pdf").is_file()
    if tex and pdf:
        return _cell("green", "tex+pdf")
    if tex:
        return _cell("warning", "tex only",
                     detail="no compiled PDF — `scripts/compile_bundle_pdf.py "
                            f"{code}`")
    if pdf:
        return _cell("warning", "pdf only",
                     detail="a compiled PDF with no source draft beside it")
    return _cell("absent", "no draft")


def _read_through_cell() -> dict:
    """§7.5. **There is no field, and there is not supposed to be one.**

    This is the column most likely to be 'helpfully' wired to something adjacent — the
    Stage-9 status, the prose gates, a review doc's existence. Every one of those would
    report a different stage's state under this heading. The correct value is that the
    question is not tracked.
    """
    return _cell("not-tracked", "not tracked",
                 detail="`prose-reviewer` emits a restructuring instruction, not a "
                        "finding or a status field (ADR-012 C3). Nothing on disk records "
                        "whether §7.5 ran, so this is neither passed nor failed.")


def _stage10_cell(metadata: dict | None, code: str) -> dict:
    claims = (PAPERS_DIR / code / "claims_review.json").is_file()
    raw = (metadata or {}).get("stage10_status")
    cell = _status_cell(
        raw,
        green_ok=claims,
        green_withheld="stage10_status says green but there is no claims_review.json — "
                       "Stage 10 left no artifact, so the claim is unverifiable here")
    cell["claims_review"] = "present" if claims else "absent"
    if not claims:
        cell.setdefault(
            "detail",
            "no claims_review.json: Stage 10 never ran. That is its own state "
            "(ADR-011 Phase 2d) — not a failure and not a pass.")
    return cell


def _stage13_cell(metadata: dict | None) -> dict:
    """S13. Only `full-adversarial` earns green, and the redo flag overrides everything.

    ⚠️ Measured 2026-08-12, `stage13_review_kind` was absent from **every** bundle's
    metadata, so no row could reach green here at all. That was a RECORDING gap, not 21
    failed reviews, and it was filed and repaired on 2026-08-13: `resolve_stage13_reviews`
    now reads a kind an evidence document DECLARES about itself, the same evidence-based
    path the review date already had. Two bundles resolve one that way; the rest are
    `reviewed-kind-unrecorded`, which is a distinct state from `unreviewed` and still does
    not earn green. **A directory name is deliberately not treated as a kind** — inferring
    one from the path would manufacture, for eighteen bundles at once, exactly the evidence
    this gate exists to demand.
    """
    from bundle_readiness import _KINDS_SUFFICIENT_FOR_GREEN

    md = metadata or {}
    kind = md.get("stage13_review_kind")
    redo = bool(md.get("stage13_redo_required"))
    sufficient = str(kind or "") in _KINDS_SUFFICIENT_FOR_GREEN
    withheld = []
    if not sufficient:
        withheld.append(
            f"review kind is {kind!r}; only "
            f"{'/'.join(sorted(_KINDS_SUFFICIENT_FOR_GREEN))} earns green")
    if redo:
        withheld.append("stage13_redo_required is set — a later append invalidated the "
                        "recorded review")
    cell = _status_cell(md.get("stage13_status"),
                        green_ok=not withheld,
                        green_withheld="; ".join(withheld))
    cell["review_kind"] = kind
    cell["redo_required"] = redo
    return cell


def _freshness_cell(code: str, findings: list[dict]) -> dict:
    """S12. Rolled up from the freshness check's own per-bundle findings.

    A bundle with **no** findings has no `bundle_metadata.json` for the check to key on —
    it was skipped, not cleared, so the cell is `absent` rather than green.
    """
    mine = [f for f in findings if f.get("bundle") == code]
    if not mine:
        return _cell("absent", "not checked",
                     detail="the freshness check found no bundle_metadata.json to key "
                            "on, so this bundle was skipped — not cleared")
    failed = [f for f in mine if not f.get("passed")]
    warned = [f for f in mine if f.get("passed") and f.get("warning")]
    unmeasured = [f for f in mine if not f.get("measured", True)]
    detail = {"messages": [f.get("message", "") for f in mine],
              "unmeasured_legs": [f.get("message", "") for f in unmeasured]}
    if failed:
        return _cell("red", f"{len(failed)} stale", **detail)
    if unmeasured and not warned:
        return _cell("unmeasured", "legs unmeasured", **detail)
    if warned:
        return _cell("warning", f"{len(warned)} advisory", **detail)
    return _cell("green", "fresh", **detail)


def _submission_cell(code: str, readiness: dict | None, metadata: dict | None,
                     *, gates_present: bool) -> dict:
    """The submission column: the `readiness_submission_gate` verdict + `blockers_open`.

    ⚠️ **Two different ways to have no verdict, and neither is green.**
    `readiness_submission_gate`'s own history is the argument: it classified papers
    correctly and returned `passed=True` unconditionally, so the only state in which it
    could fail was *"zero gate nodes"* — it failed when it could not measure and passed
    when it measured RED (61 of 64 papers RED, verdict True). Both no-verdict states are
    therefore reported by name, and both render `unmeasured`.

    ⚠️ There was a third branch here — `state is None` — and it was **unreachable**:
    `readiness_by_bundle` never emits an entry without a state, so a mutation replacing
    that branch with `green` survived the suite. Dead code in a surface like this is worse
    than useless; it reads as a handled case and cannot be tested.
    """
    md = metadata or {}
    blockers = md.get("blockers_open")
    if not gates_present:
        return _cell("unmeasured", "no gate nodes exist",
                     blockers_open=blockers,
                     detail="NO ReadinessGate nodes exist at all — the submission gate "
                            "has nothing to evaluate, so its verdict is vacuous. That is "
                            "the one state in which every bundle trivially satisfies it")
    if readiness is None:
        return _cell("unmeasured", "not evaluated for this bundle",
                     blockers_open=blockers,
                     detail="the gate system produced gates, but none of them names this "
                            "bundle — UNVERIFIED, not passing")
    state = readiness["state"]
    blocked = readiness.get("blocked_gates") or []
    kind = {"green": "green", "yellow": "warning", "red": "red"}[state]
    return _cell(kind, state, blockers_open=blockers, blocked_gates=blocked,
                 detail=(f"{len(blocked)} blocked gate(s): {', '.join(blocked)}"
                         if blocked else "no blocked gate"))


def readiness_by_bundle(gate_nodes: list[dict]) -> dict[str, dict]:
    """`{bundle: {state, blocked_gates, advisory_gates}}` from `ReadinessGate` nodes.

    Uses `classify_readiness` / `partition_readiness` — the pure functions
    `readiness_submission_gate` itself calls — rather than a second verdict. A bundle the
    gates never mention is simply absent from this map, and `_submission_cell` renders
    that as unmeasured.
    """
    from validation.checks.bundles_readiness import (
        classify_readiness, partition_readiness)

    per_paper = classify_readiness(gate_nodes)
    green, yellow, red = partition_readiness(per_paper)
    state_of = {**{p: "green" for p in green}, **{p: "yellow" for p in yellow},
                **{p: "red" for p in red}}
    out: dict[str, dict] = {}
    for code in BUNDLE_CODES:
        if code not in per_paper:
            continue
        s = per_paper[code]
        out[code] = {
            "state": state_of[code],
            "blocked_gates": sorted(g for g, _, _ in s["p1_blocked"] + s["p2_blocked"]),
            "advisory_gates": sorted(g for g, _, _ in s["p2_advisory"] + s["open"]),
        }
    return out


# ── Census, coverage, caveats ─────────────────────────────────────────────────────────

def status_census(rows: list[dict]) -> dict:
    """The live `stage*_status` value set, and which values the roadmap never declared.

    D15: *"the status enum has drifted and the board must not hide it."* Hiding it would
    not require coercing anything — merely never counting would do it, because a board
    that renders `pending-redo` in one cell and says nothing else leaves the drift as an
    anecdote rather than a measurement.
    """
    fields = ("stage9_status", "stage10_status", "stage13_status")
    per_field: dict[str, dict[str, int]] = {}
    all_values: Counter[str] = Counter()
    for field in fields:
        counter: Counter[str] = Counter()
        for row in rows:
            raw = (row.get("metadata_present") and row["raw_status"].get(field))
            counter[str(raw) if raw else "(absent)"] += 1
        per_field[field] = dict(sorted(counter.items()))
        all_values.update(counter)
    undeclared = sorted(v for v in all_values
                        if v not in ROADMAP_DECLARED_STATUSES and v != "(absent)")
    return {
        "declared_by_roadmap": sorted(ROADMAP_DECLARED_STATUSES),
        "live_values": dict(sorted(all_values.items())),
        "undeclared_by_roadmap": undeclared,
        "per_field": per_field,
    }


def coverage(rows: list[dict], finding_nodes: list[dict]) -> dict:
    """What the overlay CAN and CANNOT see. Both, always, in one call.

    Every open finding lands in exactly one bucket and the buckets are asserted to sum to
    the population. The bucket that matters is `carry_no_bundle_or_paper_key`: those
    findings are dropped before `aggregate_by_bundle` ever sees them (silent-drop point 1
    in `QA_QI_INFRASTRUCTURE_MAP.md` §3), so a board that reported only what it could
    place would let a bundle read unblocked because its findings LOST their attribution.
    """
    open_nodes = [n for n in finding_nodes
                  if (n.get("meta") or {}).get("status") == "open"]
    attributed_ids: set[str] = set()
    for row in rows:
        attributed_ids.update(row["overlay_ids"])

    attributed = keyed_off_roster = no_key = 0
    for n in open_nodes:
        m = n.get("meta") or {}
        if n["id"] in attributed_ids:
            attributed += 1
        elif m.get("inferred_bundle") or m.get("inferred_paper"):
            keyed_off_roster += 1
        else:
            no_key += 1
    assert attributed + keyed_off_roster + no_key == len(open_nodes), (
        "the coverage buckets do not partition the open finding population")

    lanes = lane_index(finding_nodes)
    unclassified = sum(1 for fid in attributed_ids
                       if lanes.get(fid, "unclassified") == "unclassified")
    return {
        "open_findings": len(open_nodes),
        "attributed_to_a_row": attributed,
        "keyed_to_something_off_the_roster": keyed_off_roster,
        "carry_no_bundle_or_paper_key": no_key,
        "attributed_with_no_declared_lane": unclassified,
        "rows": len(rows),
        "rows_without_metadata": sum(1 for r in rows if not r["metadata_present"]),
        "submission_gates_evaluated": sum(
            1 for r in rows if r["cells"]["submission"]["kind"] != "unmeasured"),
        "manuscripts_sized": sum(
            1 for r in rows if r["soft_signals"]["manuscript_length"]["measured"]),
        "lean_registrations_unmeasured": sum(
            1 for r in rows if not r["soft_signals"]["registered_lean_modules"]["measured"]),
    }


def caveats(rows: list[dict], cov: dict, census: dict) -> list[str]:
    """Every sentence the board must render beside itself. Not optional, and measured.

    A caveat carrying no number is a disclaimer; one carrying the live magnitude is a
    measurement the reader can act on. Each of these is computed from the rows above.
    """
    out: list[str] = []

    out.append(
        "§7.5 read-through is NOT TRACKED for any bundle: `prose-reviewer` mints no "
        "machine state by design (ADR-012 C3). An empty §7.5 column is not evidence the "
        "read-through was skipped, and it is never evidence that it passed.")

    if census["undeclared_by_roadmap"]:
        out.append(
            "The stage-status enum has drifted. `Phase7a_Roadmap.md` declares "
            f"{'|'.join(census['declared_by_roadmap'])}; the live corpus also carries "
            f"{', '.join(repr(v) for v in census['undeclared_by_roadmap'])}. Undeclared "
            "values render VERBATIM here and are never coerced to the nearest declared "
            "state — `pending-redo` in particular means a completed stage was invalidated "
            "by a later append, which is not 'pending'.")

    kinds = {r["bundle"]: r["cells"]["stage13_adversarial"].get("review_kind")
             for r in rows}
    missing_kind = sorted(b for b, k in kinds.items() if not k)
    if missing_kind:
        out.append(
            f"{len(missing_kind)} of {len(rows)} bundles resolve NO `stage13_review_kind` "
            "— not from metadata, and not from a kind their evidence document declares — so "
            "those rows cannot reach green at S13 whatever `stage13_status` says, since only "
            "`full-adversarial` earns it. ⚠️ For most of them this is a RECORDING gap rather "
            "than a failed review: the evidence exists on disk and does not say what kind of "
            "pass it was. A kind is never inferred from a directory name.")

    unbuilt = {r["bundle"]: r["soft_signals"]["registered_lean_modules"]["unresolved"]
               for r in rows
               if r["soft_signals"]["registered_lean_modules"]["measured"]}
    n_unbuilt = sum(len(v) for v in unbuilt.values())
    n_bundles = sum(1 for v in unbuilt.values() if v)
    out.append(
        f"The registered Lean module list is HAND-TYPED at lift time and is not evidence "
        f"the modules exist: {n_unbuilt} registration(s) across {n_bundles} bundle(s) "
        f"resolve to no module in the Lean build (TODO-D50). They are registrations of "
        f"substrate that was planned and not built, and they can only be repaid by "
        f"removing the registration. Nothing on this board guards that field."
        + (f" {cov['lean_registrations_unmeasured']} bundle(s) could not be measured at "
           f"all (unreadable append_log.json)."
           if cov["lean_registrations_unmeasured"] else ""))

    sized = cov["manuscripts_sized"]
    out.append(
        f"The manuscript-length signal is sized for {sized} of {len(rows)} bundles. It "
        f"keys on mtime against each draft's input closure, and every draft `\\input`s "
        f"`docs/counts.tex` — so ONE byte-identical rewrite of that file blanks the whole "
        f"roster at once (TODO-D51, observed 2026-08-11). A blank length means nobody can "
        f"size the manuscript right now; it does not mean the manuscript is mis-sized, "
        f"and it must not be repaired by recompiling all the PDFs.")

    if cov["carry_no_bundle_or_paper_key"] or cov["keyed_to_something_off_the_roster"]:
        out.append(
            f"The lane overlay reaches {cov['attributed_to_a_row']} of "
            f"{cov['open_findings']} open findings. "
            f"{cov['carry_no_bundle_or_paper_key']} carry neither a bundle nor a paper "
            f"key and are dropped before any per-bundle aggregation can see them; "
            f"{cov['keyed_to_something_off_the_roster']} are keyed to something that maps "
            f"to no bundle on the roster. A row's overlay is a floor on what holds it, "
            f"never a total.")

    if cov["attributed_with_no_declared_lane"]:
        out.append(
            f"{cov['attributed_with_no_declared_lane']} of {cov['attributed_to_a_row']} "
            f"attributed findings carry no declared lane and count as `unclassified`. "
            f"Every named lane on this board is therefore an UNDERCOUNT: routing 'six "
            f"substrate findings' is a lower bound until "
            f"`scripts/backfill_lanes.py --propose` has been worked through.")

    if cov["rows_without_metadata"]:
        out.append(
            f"{cov['rows_without_metadata']} row(s) have no readable "
            f"`bundle_metadata.json`; every metadata-sourced cell on those rows reads "
            f"ABSENT rather than defaulting to a state.")

    if cov["submission_gates_evaluated"] < len(rows):
        out.append(
            f"The submission verdict was computable for "
            f"{cov['submission_gates_evaluated']} of {len(rows)} rows. The rest read "
            f"UNMEASURED — which is the state `readiness_submission_gate` used to render "
            f"as a pass, and the reason it is rendered as its own kind here.")

    return out


# ── The board ─────────────────────────────────────────────────────────────────────────

def flow_board(*, by_bundle: dict | None = None,
               finding_nodes: list[dict] | None = None,
               gate_nodes: list[dict] | None = None,
               freshness_findings: list[dict] | None = None) -> dict:
    """`{'rows': [...], 'coverage': {...}, 'caveats': [...], 'columns': [...],
    'status_census': {...}}` — the Flow board as data.

    Every argument is an injection point for an input that is otherwise loaded live, so a
    caller holding the graph pays for it once and a test can drive the whole board from
    synthetic inputs. Passing `gate_nodes=[]` is NOT the same as omitting it: an empty gate
    population means no bundle has a submission verdict, and every submission cell reads
    `unmeasured`.

    **Raises** rather than returning an empty board when the roster or the finding
    population is empty. An empty board is indistinguishable from a portfolio with nothing
    in it, which is precisely the failure this surface exists to make visible.
    """
    roster = tuple(sorted(BUNDLE_CODES, key=bundle_sort_key))
    if not roster:
        raise RuntimeError(
            "bundle_registry.BUNDLE_CODES is EMPTY. A board with no rows is not a clean "
            "portfolio; it is a broken roster. Refusing to render.")

    findings = finding_nodes if finding_nodes is not None else load_finding_nodes()
    if not findings:
        raise RuntimeError(
            "the ReviewFinding population is EMPTY. The overlay would show every bundle "
            "unblocked, which is the one reading this board must never produce by "
            "accident. Refusing to render.")

    aggregate = by_bundle if by_bundle is not None else load_aggregate()
    fresh = (freshness_findings if freshness_findings is not None
             else load_freshness())
    gates = gate_nodes if gate_nodes is not None else load_gate_nodes()
    readiness = readiness_by_bundle(gates)
    lanes = lane_index(findings)

    rows: list[dict] = []
    for code in roster:
        md = _read_metadata(code)
        agg = aggregate.get(code) or {}
        # ⚠️ `.get(code)` returning nothing is a REAL possibility and is rendered, not
        # papered over: a bundle the aggregation never reached has no finding list, which
        # is not the same as an empty one.
        reached = code in aggregate
        open_ids = list(agg.get("open_finding_ids") or [])

        cells = {
            "draft_exists": _draft_cell(code),
            "read_through": _read_through_cell(),
            "stage9_figure": _status_cell((md or {}).get("stage9_status")),
            "stage10_claims": _stage10_cell(md, code),
            "stage12_sync": _freshness_cell(code, fresh),
            "stage13_adversarial": _stage13_cell(md),
            "submission": _submission_cell(code, readiness.get(code), md,
                                           gates_present=bool(gates)),
        }
        assert set(cells) == {c.key for c in COLUMNS}, (
            "the emitted cells and the declared COLUMNS have drifted apart")

        overlay = lane_overlay(open_ids, lanes)
        if not reached:
            overlay["note"] = (
                "this bundle was not reached by the per-bundle aggregation at all — the "
                "overlay is UNMEASURED, not zero")
            overlay["measured"] = False
        else:
            overlay["measured"] = True

        rows.append({
            "bundle": code,
            "tier": TIER_OF.get(code),
            "title": BUNDLE_TITLES.get(code, ""),
            "metadata_present": md is not None,
            "raw_status": {k: (md or {}).get(k) for k in
                           ("stage9_status", "stage10_status", "stage13_status")},
            "cells": cells,
            "overlay": overlay,
            "overlay_ids": open_ids,
            "blockers_open": (md or {}).get("blockers_open"),
            "readiness_verdict": agg.get("readiness_display") or agg.get("readiness"),
            "soft_signals": {
                "registered_lean_modules": registered_lean_modules(code),
                "manuscript_length": manuscript_length(code, md),
            },
        })

    census = status_census(rows)
    cov = coverage(rows, findings)
    return {
        "columns": [c.as_dict() for c in COLUMNS],
        "rows": rows,
        "coverage": cov,
        "status_census": census,
        "caveats": caveats(rows, cov, census),
    }


if __name__ == "__main__":  # pragma: no cover — operator convenience
    board = flow_board()
    print(json.dumps({"coverage": board["coverage"],
                      "status_census": board["status_census"],
                      "caveats": board["caveats"]}, indent=2))
    for r in board["rows"]:
        cells = " | ".join(
            f"{c.key}={r['cells'][c.key]['kind']}:{r['cells'][c.key]['value']}"
            for c in COLUMNS)
        print(f"{r['bundle']:>3}  {cells}")
        print(f"      overlay {r['overlay']['open_total']} open "
              f"{r['overlay']['by_lane']}")
