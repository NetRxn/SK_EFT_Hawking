"""Bundle-metadata, readiness-gate and roster checks — ADR-009 Phase 2.

`bundle_figure_integrity`, `bundle_metadata_matches_graph`,
`readiness_verdicts_agree`, `readiness_submission_gate`, `bundle_consistency`,
`bundle_registry_consistency`.

✅ **`readiness_submission_gate` HARD-FAILS. Repaired 2026-08-03 (ADR-009 §Deferred
item 2).** It is one of the two checks `validate.py` is deliberately RED on, and
that is the instrument working.

⚠️ This header asserted the OPPOSITE — *"IS INVERTED AND CANNOT BLOCK … do not 'fix'
it during a mechanical phase"* — for a day after the repair landed, because the
header was written during Phase 2 and the Phase-3 fix did not come back to it
(audit finding QI-12). A module header that tells a reader a working guard is
broken is the same defect class as a guard that cannot fire: both leave the
reader's model wrong in the direction of false confidence. It also cited the wrong
ordinal — the inversion is §Deferred item **2**; item 1 is the `native_decide`
ratchet (QI-16).

For the record, what was wrong before the repair: it failed only when ZERO
`ReadinessGate` nodes existed and PASSED when it measured RED, marked solely by an
inline `# WARN not FAIL during rollout`, with a `--strict` path its docstring
promised and its body never referenced. Measured at repair: **61 of 64 papers RED,
verdict `True`** — which is why 14 bundles sat at `stage13_status: green` with open
blockers.

`readiness_verdicts_agree` is the cross-check that exists BECAUSE of that: two
subsystems compute a per-bundle verdict from different inputs, and nothing compared
them, so the reassuring one could be quoted. It asserts both directions — RED at the
heatmap must not be green at the gate, and GREEN at the heatmap must survive every
P1 gate.

`bundle_registry_consistency` gates the roster's single source of truth in three
legs, one of which (leg C, an AST walk for re-hardcoded roster literals) is what
stops the NEXT authorized bundle from regressing the seven-places problem. It reads
`BUNDLE_CODES` from `validate` via `_ROSTER_CONSUMERS`, which is why that name stays
re-exported there (H2) rather than moving here.

Import rules as elsewhere. No check here reads a runtime flag.
"""
from __future__ import annotations

import ast
import hashlib
import importlib
import json
import tempfile
from pathlib import Path
from typing import List

import validate_helpers as _H
from validation._registry import CheckResult, Detail, register_check

# ⚠️ `import re` and `from bundle_registry import BUNDLE_CODES` stood here and were
# NEVER referenced (removed 2026-08-04, audit QI-11). The roster gate below reads
# `registry.BUNDLE_CODES` off its own `import bundle_registry as registry`, so the
# module-level name was dead — and its `# the roster's owner (H2)` comment implied
# an H2 obligation that this import was not in fact carrying. H2's actual
# requirement is that **`validate`** expose `BUNDLE_CODES`, which `validate.py`
# satisfies directly; `_ROSTER_CONSUMERS` below still asserts it.


# ═══════════════════════════════════════════════════════════════════════
# CHECK 10: Notebook visualization consistency (warnings only)
# ═══════════════════════════════════════════════════════════════════════

@register_check("bundle_figure_integrity",
                "Bundle figures match a fresh render and are legible at typeset size")
def check_bundle_figure_integrity() -> CheckResult:
    """Two guarantees the printed paper actually depends on, both of which were
    violated in the D11/D12 first lift and caught only by a human-in-the-loop
    reviewer rasterising the PDF:

    1. **No source/artefact drift.** Every ``papers/<bundle>/figures/<name>.png``
       must be byte-identical to a fresh render from ``src/core/visualizations``.
       ``review_figures.py`` writes to ``_H.PROJECT_ROOT/figures``, not into the
       bundle directories, so nothing otherwise stops a shipped figure from
       silently diverging from the code that is supposed to produce it.

    2. **Legible in print.** ``bundle_figure_typeset_pt`` reports the SMALLEST
       printed text size, over every text-bearing field, at ``figure*``
       ``\textwidth``. Stage-9 round 3 found figures printing at 2-3 pt against
       10 pt body text while looking fine as PNGs. Round 5 then found that the
       checker itself had **zero consumers repo-wide** — it was honest but not
       binding. This is the binding.

    Floor is 8.0 pt. Skips cleanly when kaleido is unavailable.
    """
    # (`import importlib` stood here, shadowing the module-level import — audit QI-11.)
    details: List[Detail] = []
    try:
        viz = importlib.import_module("src.core.visualizations")
    except Exception as exc:  # pragma: no cover - import guard
        return CheckResult(passed=True, measured=False, details=[Detail(
            "skipped", True, f"visualizations import failed ({exc}) — skipped",
            warning=True)])

    if not hasattr(viz, "bundle_figure_typeset_pt"):
        return CheckResult(passed=True, measured=False, details=[Detail(
            "skipped", True, "bundle_figure_typeset_pt absent — skipped",
            warning=True)])

    FLOOR_PT = 8.0
    # Derived from FIGURE_REGISTRY rather than hand-maintained: a hand-listed
    # roster means the NEXT bundle figure ships unguarded, which is the same
    # silent-omission class as the four hardcoded bundle registries this lift
    # had to patch. The literal below is the fallback if the registry is
    # unreadable.
    try:
        import importlib.util as _ilu
        import sys as _sys
        _spec = _ilu.spec_from_file_location(
            "_review_figures", _H.SCRIPT_DIR / "review_figures.py")
        _rf = _ilu.module_from_spec(_spec)
        # ⚠️ REGISTER BEFORE EXEC (fixed 2026-08-05, PR-review R4-MAJ3). Without
        # this the block raised `AttributeError: 'NoneType' object has no attribute
        # '__dict__'` on EVERY run, so the `except` below always fired and the
        # "derived from FIGURE_REGISTRY rather than hand-maintained" guarantee was
        # dead — production always used the hardcoded 7-figure literal, i.e. the
        # very hand-maintained list this block exists to replace.
        #
        # Cause: `module_from_spec` does NOT put the module in `sys.modules`, and
        # Python 3.12+ `@dataclass` dereferences `sys.modules.get(cls.__module__)`
        # while probing for `KW_ONLY`. `review_figures.py` defines `FigureSpec` as a
        # dataclass, so executing it out-of-band could never succeed.
        #
        # Reproduced directly before fixing, not inferred from the fallback firing.
        _sys.modules[_spec.name] = _rf
        _spec.loader.exec_module(_rf)
        _derived: dict[str, list] = {}
        for fs in _rf.FIGURE_REGISTRY:
            if not fs.name.startswith(("d11_", "d12_")):
                continue
            _derived.setdefault(fs.name.split("_")[0].upper(), []).append(
                (fs.name, fs.function))
        if _derived:
            SPECS = _derived
        else:
            raise RuntimeError("no d11_/d12_ specs found")
    except Exception:
        SPECS = {
        "D11": [("d11_fig1_phononic_band_gap", "fig_d11_phononic_band_gap"),
                ("d11_fig2_pt_exceptional_point", "fig_d11_pt_exceptional_point"),
                ("d11_fig3_haldane_chern", "fig_d11_haldane_chern"),
                ("d11_fig4_effective_medium", "fig_d11_effective_medium")],
        "D12": [("d12_fig1_poisson_floor_vs_folklore", "fig_d12_poisson_floor_vs_folklore"),
                ("d12_fig2_enbw_matched_filter", "fig_d12_enbw_matched_filter"),
                ("d12_fig3_etf_stability", "fig_d12_etf_stability")],
    }

    n_ok = n_fail = 0
    for bundle, figs in SPECS.items():
        for png_name, func_name in figs:
            png = _H.PAPERS_DIR / bundle / "figures" / f"{png_name}.png"
            fn = getattr(viz, func_name, None)
            if fn is None:
                details.append(Detail(f"missing_fn:{bundle}:{func_name}", False,
                                      f"{func_name} not found in visualizations"))
                n_fail += 1
                continue
            if not png.exists():
                details.append(Detail(f"missing_png:{bundle}:{png_name}", False,
                                      f"papers/{bundle}/figures/{png_name}.png absent"))
                n_fail += 1
                continue
            try:
                fig = fn()
            except Exception as exc:
                details.append(Detail(f"render_error:{bundle}:{png_name}", False,
                                      f"{func_name}() raised {exc!r}"))
                n_fail += 1
                continue

            pt = viz.bundle_figure_typeset_pt(fig)
            if pt < FLOOR_PT:
                details.append(Detail(
                    f"illegible:{bundle}:{png_name}", False,
                    f"smallest printed text {pt:.2f}pt < {FLOOR_PT}pt floor "
                    f"(against 10pt body) — widen the canvas or raise the font"))
                n_fail += 1
            else:
                n_ok += 1
                details.append(Detail(f"legible:{bundle}:{png_name}", True,
                                      f"smallest printed text {pt:.2f}pt", warning=False))

            # Drift check is advisory: kaleido may be unavailable, and a
            # byte-compare is sensitive to renderer version. A mismatch is worth
            # surfacing, not worth blocking a whole validation run on.
            try:
                import os as _os   # hashlib/tempfile are module-level (audit QI-11)
                with tempfile.NamedTemporaryFile(suffix=".png", delete=False) as tmp:
                    tmp_path = tmp.name
                fig.write_image(tmp_path, scale=3)
                fresh = hashlib.sha256(Path(tmp_path).read_bytes()).hexdigest()
                shipped = hashlib.sha256(png.read_bytes()).hexdigest()
                _os.unlink(tmp_path)
                if fresh != shipped:
                    details.append(Detail(
                        f"drift:{bundle}:{png_name}", True,
                        f"shipped PNG differs from a fresh render "
                        f"({shipped[:12]} vs {fresh[:12]}) — re-render before review",
                        warning=True))
            except ImportError:
                pass  # kaleido genuinely unavailable — advisory only
            except Exception as exc:
                # A bare `except: pass` here previously swallowed a NameError
                # for a whole review round, making "zero drift" indistinguishable
                # from "never ran". Surface anything that is not a missing
                # renderer, as a warning rather than a hard failure.
                details.append(Detail(
                    f"drift_check_error:{bundle}:{png_name}", True,
                    f"drift comparison could not run: {type(exc).__name__}: {exc}",
                    warning=True))

    details.insert(0, Detail(
        "summary", n_fail == 0,
        f"{n_ok + n_fail} bundle figures checked — {n_ok} legible / {n_fail} below "
        f"the {FLOOR_PT}pt floor"))
    return CheckResult(passed=n_fail == 0, details=details)


@register_check("bundle_metadata_matches_graph",
                "bundle_metadata.json finding counts equal the live graph's")
def check_bundle_metadata_matches_graph() -> CheckResult:
    """CHECK: the per-bundle metadata blob must not assert stale finding counts.

    Added 2026-07-31 (D12 Stage-13 round-7 findings 7.2 + 8.3 and D11 4.2 — three
    findings, one root cause). `bundle_source_manifest.py` initialises
    `blockers_open` / `advisories_open` to 0 when a bundle is created and nothing
    updated them afterwards, so ALL 21 bundles asserted `blockers_open: 0` while
    carrying up to 36 open blockers each — and `freshness_stale: false` rested on
    that zero. `bundle_readiness.py` now writes the live numbers back
    (`write_metadata_counts`); this check is the guard that they stay written.

    It compares against the same aggregation the heatmap uses, so a bundle whose
    metadata was hand-edited, or whose readiness run was skipped after new findings
    landed, fails here rather than being quoted as evidence of readiness.
    """
    try:
        from bundle_readiness import (MAPPING_DOC, parse_mapping,
                                      load_findings_by_paper,
                                      resolve_stage13_reviews,
                                      aggregate_by_bundle,
                                      _bundle_metadata_path)
    except ImportError as exc:
        # FAIL, not pass (D12 Stage-13 round-8 BLOCKER 8.2). A readiness guard that cannot
        # load its own dependency reports "no disagreement found" — indistinguishable from
        # agreement. Demonstrated end-to-end by the round-8 reviewer: renaming
        # `evaluate_all_gates` makes build_graph emit ZERO ReadinessGate nodes, at which
        # point every readiness check passed green with nothing to check.
        return CheckResult(passed=False, details=[
            Detail("import", False,
                   f"could not import the readiness machinery ({exc}) — this check is "
                   f"UNVERIFIED, not passing")])

    try:
        by_bundle = aggregate_by_bundle(
            parse_mapping(MAPPING_DOC.read_text()),
            load_findings_by_paper(),
            resolve_stage13_reviews(backfill=False))
    except Exception as exc:
        # FAIL, not pass: an uncomputable live verdict is not agreement.
        return CheckResult(passed=False, details=[
            Detail("aggregate", False,
                   f"live counts could not be computed ({type(exc).__name__}: {exc}) "
                   f"— metadata is therefore UNVERIFIED, not matching")])

    details: list[Detail] = []
    drift = 0
    checked = 0
    for bundle, agg in sorted(by_bundle.items()):
        mp = _bundle_metadata_path(bundle)
        if not mp.is_file():
            # FAIL, not skip (D12 round-8): a bundle with no metadata blob has nothing to
            # disagree with the graph, which is not the same as agreeing with it.
            drift += 1
            details.append(Detail(
                bundle, False,
                f"no bundle_metadata.json at {mp} — the readiness assertions for this "
                f"bundle do not exist, so they are unverified rather than consistent"))
            continue
        try:
            meta = json.loads(mp.read_text())
        except (json.JSONDecodeError, OSError) as exc:
            drift += 1
            details.append(Detail(bundle, False, f"metadata unreadable: {exc}"))
            continue
        checked += 1
        live_blockers = agg.get("blocker_count", 0)
        live_adv = sum(v for k, v in (agg.get("severity_mix") or {}).items()
                       if k in ("minor", "advisory"))
        bad = []
        if meta.get("blockers_open") != live_blockers:
            bad.append(f"blockers_open={meta.get('blockers_open')} live={live_blockers}")
        if meta.get("advisories_open") != live_adv:
            bad.append(f"advisories_open={meta.get('advisories_open')} live={live_adv}")
        if meta.get("readiness") != agg.get("readiness"):
            bad.append(f"readiness={meta.get('readiness')!r} live={agg.get('readiness')!r}")
        # ── `stage13_status: green` is illegal while blockers are open ──────────────
        # Added 2026-08-03 (publication-readiness audit). The three comparisons above
        # assert that metadata AGREES WITH the graph. They cannot catch the state 14 of
        # 21 bundles are in right now, because that state is internally CONSISTENT: the
        # metadata says `blockers_open: 37` and the graph says 37, so they agree — while
        # the same file also says `stage13_status: "green"`.
        #
        # `stage13_status` is asserted by an agent hand-editing JSON (the only automated
        # write is `bundle_append.py`'s green->pending DEMOTION on lift); no code path
        # promotes it, and until now nothing in this repo read it. So the one direction
        # that matters for publication safety was unguarded.
        #
        # The remedy is quoted verbatim from this project's own reviewer,
        # `papers/AutomatedReviews/2026-07-31-1652-internal-adversarial/D11.md:227`:
        # "a bundle with `blockers_open > 0` must not carry `stage13_status: 'green'`".
        # A mutation test proving the hole was already committed at
        # `2026-08-01-0009-internal-adversarial/D11.md:179` (flip pending->green =>
        # "PASS <-- missed"). The test existed; the guard did not.
        #
        # Compared against the LIVE count, not `meta["blockers_open"]`: hand-editing the
        # count to 0 to make this pass would trip the `blockers_open` comparison above,
        # so both legs have to be defeated rather than one.
        if str(meta.get("stage13_status", "")).strip().lower() == "green" \
                and live_blockers > 0:
            bad.append(
                f"stage13_status='green' while {live_blockers} blocker(s) are open — "
                f"Stage 13 is GREEN only when no blocking finding remains "
                f"(BUNDLE_LIFT_PROCEDURE.md §12)")
        # NOT asserted here: `stage13_redo_required`. The same reviewer paired it with the
        # rule above, but the two are independent: `redo_required` means "new content was
        # appended since the last review" (written by `bundle_append.py`), NOT "blockers
        # are open". A bundle can correctly carry blockers with `redo_required: false` when
        # the blockers came from the review itself rather than from a later lift. Asserting
        # it would repeat the `freshness_stale` mistake recorded immediately below —
        # inferring a field's meaning from the workflow step that mentions it.
        # NOT asserted here: `freshness_stale`. D12 Stage-13 round-8 reported that seven
        # bundles set it false with blockers open, citing
        # LATE_PHASE6_ABSORPTION_PROTOCOL.md. I implemented that assertion and it was
        # wrong — the field is owned by `scripts/check_bundle_source_freshness.py` and
        # means "a source paper is newer than last_lift", which is independent of blocker
        # count. The protocol line quoted is a workflow step, not the field's definition.
        # Asserting it here made two writers fight and `validate.py` non-idempotent.
        if bad:
            drift += 1
            details.append(Detail(
                bundle, False,
                f"metadata disagrees with the live graph: {'; '.join(bad)}. "
                + ("⚠️ `stage13_status` is NOT written by `bundle_readiness.py` — that "
                   "script owns blockers_open / advisories_open / open_findings / "
                   "blocked_p1_gates / readiness only. `stage13_status` is set by the "
                   "Stage-13 review cycle (BUNDLE_LIFT_PROCEDURE.md §§8–10), so a green "
                   "value here is a claim about a PAST review that newly-minted blockers "
                   "have since contradicted. Re-run Stage 13 for this bundle (or set "
                   "`stage13_redo_required`) — re-running the counts writer will NOT "
                   "clear it."
                   if any("stage13_status" in b for b in bad) else
                   "Re-run `uv run python scripts/bundle_readiness.py`, which writes "
                   "these fields; do not hand-edit them.")))

    details.insert(0, Detail(
        "summary", drift == 0,
        f"{checked} bundle metadata blob(s) compared against the live graph, "
        f"{drift} with drift"))
    return CheckResult(passed=drift == 0, details=details)


@register_check("readiness_verdicts_agree",
                "The heatmap and the submission gate return the same per-bundle verdict")
def check_readiness_verdicts_agree() -> CheckResult:
    """CHECK: cross-validate the two independent readiness verdicts.

    Added 2026-07-31 (D12 Stage-13 round-6 BLOCKER 8.1). Two subsystems compute
    a per-bundle readiness verdict from different inputs and had no consistency
    obligation between them:

      * `scripts/bundle_readiness.py` counts findings straight off the review
        files, per bundle, and rendered D11/D12 RED with unclosed blockers;
      * `readiness_submission_gate` aggregates ReadinessGate node states off the
        graph, and rendered the same bundles as "all P1 passed".

    Both were reporting honestly about their own inputs; nothing compared them,
    so the reassuring one could be quoted as the verdict. This check asserts the
    direction that matters: a bundle the heatmap calls RED (open blocking
    findings) must NOT be green or yellow at the submission gate.
    """
    try:
        from build_graph import build_graph_json
        from bundle_readiness import (MAPPING_DOC, parse_mapping,
                                      load_findings_by_paper,
                                      resolve_stage13_reviews,
                                      aggregate_by_bundle)
    except ImportError as exc:
        # FAIL, not pass (D12 Stage-13 round-8 BLOCKER 8.2). A readiness guard that cannot
        # load its own dependency reports "no disagreement found" — indistinguishable from
        # agreement. Demonstrated end-to-end by the round-8 reviewer: renaming
        # `evaluate_all_gates` makes build_graph emit ZERO ReadinessGate nodes, at which
        # point every readiness check passed green with nothing to check.
        return CheckResult(passed=False, details=[
            Detail("import", False,
                   f"could not import the readiness machinery ({exc}) — this check is "
                   f"UNVERIFIED, not passing")])

    try:
        assignments = parse_mapping(MAPPING_DOC.read_text())
        findings_by_paper = load_findings_by_paper()
        # Read-only: never backfill review metadata from inside a validation check.
        review_info = resolve_stage13_reviews(backfill=False)
        by_bundle = aggregate_by_bundle(assignments, findings_by_paper, review_info)
    except Exception as exc:  # pragma: no cover - defensive
        # FAIL, not pass (D12 round-7 finding 8.3). This guard exists to make a
        # false-green verdict impossible; an exception inside the heatmap computation
        # must not be indistinguishable from "the two verdicts agree". Same reasoning
        # as the orphan-scan handler at :3366.
        return CheckResult(passed=False, details=[
            Detail("heatmap", False,
                   f"heatmap verdict could not be computed ({type(exc).__name__}: "
                   f"{exc}) — the two verdicts are therefore UNVERIFIED, not agreed")])

    graph = build_graph_json()
    gates = [n for n in graph.get('nodes', []) if n.get('type') == 'ReadinessGate']
    if not gates:
        return CheckResult(passed=False, details=[
            Detail("gates", False,
                   "NO ReadinessGate nodes exist — nothing to cross-check, so the two "
                   "verdicts are unverified rather than in agreement (round-8 8.2)")])

    blocked_at_gate: dict[str, list[str]] = {}
    seen_papers: set[str] = set()
    for g in gates:
        m = g['meta']
        seen_papers.add(m['paper'])
        if m['state'] == 'blocked':
            blocked_at_gate.setdefault(m['paper'], []).append(m['gate'])

    details: list[Detail] = []
    disagreements = 0
    checked = 0

    # ── Reverse direction (self-audit 2026-07-31; also raised as D12 round-7 8.2) ──
    # The first version of this check opened with `if readiness != 'RED': continue`,
    # so it asserted only heatmap-RED ⇒ some gate blocked and was blind BY
    # CONSTRUCTION to the mirror image: a bundle the heatmap renders GREEN while a P1
    # gate is blocked. That is the same false-green shape as the defect the check was
    # written for, one layer over, and it was live — D6 rendered GREEN in
    # BUNDLE_READINESS_HEATMAP.md with NarrativeGrounding blocked. GREEN is what a
    # reader takes as "ready", so it must survive every P1 gate, including the ones
    # the heatmap does not model (it counts findings only).
    # ⚠️ THE LEG RUNS; ITS *DISAGREEMENT BRANCH* IS WHAT CANNOT FIRE
    # (2026-08-05, PR-review pass 2, R4-I8).
    #
    # R4 filed this as "dead by construction" and I restated that before measuring.
    # Both wrong: `reverse_coverage` reports **1 GREEN bundle cross-checked** on the
    # live tree — the loop executes and correctly finds no disagreement. What is
    # unreachable is only the `if bundle in blocked_at_gate` branch, and only while
    # the producer keeps demoting GREEN.
    #
    # (Third time this session a "dead code" claim resolved to "runs, but one branch
    # is unreachable". The two are not the same finding and do not have the same fix.)
    #
    # The chronology decides whether to delete it:
    #
    #   2026-07-31  this leg added, because `aggregate_by_bundle` was GATE-BLIND —
    #               D6 rendered GREEN in the heatmap with NarrativeGrounding blocked.
    #   2026-08-04  `5228ed6d` made the producer gate-AWARE
    #               (`bundle_readiness._blocked_p1_gates_by_paper`), so GREEN is now
    #               demoted whenever a P1 gate blocks.
    #
    # So: **a later fix to the producer silently made a consumer's guard unable to
    # fire**, and nobody noticed. It is kept because it guards a regression the
    # codebase has demonstrably occupied — remove the gate-awareness from the
    # producer and this branch fires again. Deleting it would trade a live safety net
    # for tidiness.
    #
    # What was wrong was the SILENCE. `checked` did not distinguish the two
    # directions, so the summary read "17 heatmap-RED bundles cross-checked, 0
    # disagreements" and a reader concluded both directions had been exercised. The
    # reverse coverage is now reported explicitly, and
    # `tests/test_d5_bundles_readiness.py` asserts the producer invariant that makes
    # this leg inert — so a regression there fails fast at unit level instead of
    # waiting for this slow cross-check to notice.
    reverse_checked = 0
    for bundle, agg in sorted(by_bundle.items()):
        if str(agg.get('readiness', '')).upper() != 'GREEN':
            continue
        reverse_checked += 1
        if bundle in blocked_at_gate:
            disagreements += 1
            details.append(Detail(
                bundle, False,
                f"DISAGREE (reverse): heatmap renders this bundle GREEN while P1 "
                f"gate(s) {', '.join(sorted(blocked_at_gate[bundle]))} are blocked. The "
                f"heatmap models findings only and cannot see these gates; GREEN must "
                f"not be issued while any P1 gate is blocked"))
        else:
            checked += 1

    details.append(Detail(
        "reverse_coverage", True,
        f"reverse direction (GREEN heatmap ⇒ no blocked P1 gate): {reverse_checked} "
        f"GREEN bundle(s) cross-checked"
        + ("" if reverse_checked else
           " — NONE, so this direction asserted nothing this run")
        + ". Its disagreement branch cannot fire while `aggregate_by_bundle` itself "
          "demotes GREEN on a blocked P1 gate; retained as the regression guard for "
          "that producer behaviour",
        warning=not reverse_checked))

    for bundle, agg in sorted(by_bundle.items()):
        if str(agg.get('readiness', '')).upper() != 'RED':
            continue
        if bundle not in seen_papers:
            # FAIL, not warn (D12 round-7 finding 8.2). A heatmap-RED bundle with NO
            # gate nodes is the strongest possible form of the defect this check
            # exists for: the submission gate cannot report it as blocked because it
            # has nothing to report at all. Warning-and-passing here reproduced the
            # original 8.1 failure exactly.
            disagreements += 1
            details.append(Detail(
                bundle, False,
                f"heatmap RED ({agg.get('blocker_count', 0)} blockers) but NO "
                f"ReadinessGate nodes exist for paper:{bundle} — the submission gate "
                f"is structurally unable to report this bundle as blocked"))
            continue
        checked += 1
        if bundle in blocked_at_gate:
            details.append(Detail(
                bundle, True,
                f"agree: heatmap RED ({agg.get('blocker_count', 0)} blockers), "
                f"gate blocked on {', '.join(sorted(blocked_at_gate[bundle]))}"))
        else:
            disagreements += 1
            details.append(Detail(
                bundle, False,
                f"DISAGREE: heatmap RED with {agg.get('blocker_count', 0)} open "
                f"blockers, but no ReadinessGate is blocked — the submission gate "
                f"would report this bundle as passing"))

    if not checked and not details:
        details.append(Detail("summary", True,
                              "no bundle is heatmap-RED; nothing to cross-check"))
    else:
        details.insert(0, Detail(
            "summary", disagreements == 0,
            f"{checked} heatmap-RED bundles cross-checked, "
            f"{disagreements} disagreement(s)"))
    return CheckResult(passed=disagreements == 0, details=details)


# ── Pure core, extracted for testability (ADR-009 D5) ────────────────────────
#: Gate states that count as a hard blocker for submission.
_READY_BLOCKED = "blocked"


def classify_readiness(gates: List[dict]) -> dict:
    """Group ReadinessGate nodes per paper. Pure: no graph build, no I/O.

    Extracted in Phase 3 so the submission verdict can be mutation-tested against
    synthetic gates instead of a 15-second graph build over the live tree. Same
    precedent as `_tp_scan_lines`.

    A paper is submission-ready iff every P1 gate is `passed` and no P2 gate is
    `blocked`. P2 `needs-recheck`/`open` are advisory.
    """
    from collections import defaultdict
    per_paper: dict = defaultdict(lambda: {
        'p1_blocked': [], 'p2_blocked': [], 'p2_advisory': [],
        'passed': [], 'open': [],
    })
    for g in gates:
        m = g['meta']
        entry = (m['gate'], m['state'], m.get('notes', ''))
        bucket = per_paper[m['paper']]
        if m['state'] == 'passed':
            bucket['passed'].append(entry)
        elif m['priority'] == 1 and m['state'] == _READY_BLOCKED:
            bucket['p1_blocked'].append(entry)
        elif m['priority'] == 2 and m['state'] == _READY_BLOCKED:
            bucket['p2_blocked'].append(entry)
        elif m['priority'] == 2 and m['state'] in ('needs-recheck', 'open'):
            bucket['p2_advisory'].append(entry)
        else:
            bucket['open'].append(entry)
    return dict(per_paper)


def partition_readiness(per_paper: dict) -> tuple[list, list, list]:
    """(green, yellow, red). RED = any blocked gate, P1 or P2 — the blocking set."""
    green, yellow, red = [], [], []
    for paper, s in sorted(per_paper.items()):
        if s['p1_blocked'] or s['p2_blocked']:
            red.append(paper)
        elif s['p2_advisory'] or s['open']:
            yellow.append(paper)
        else:
            green.append(paper)
    return green, yellow, red


@register_check("readiness_submission_gate",
                "Every paper has all P1 readiness gates passed (Phase 5v Wave 4)")
def check_readiness_submission_gate() -> CheckResult:
    """Aggregate per-paper readiness state, and FAIL when a paper is not ready.

    A paper is submission-ready iff ALL priority-1 gates are `passed` and no
    priority-2 gate is `blocked`. Priority-2 `needs-recheck`/`open` are advisory
    warnings and do not fail the check.

    ⚠️ **THIS CHECK WAS INVERTED UNTIL 2026-08-03 (ADR-009 §Deferred item 2).** It
    classified papers into green/yellow/red exactly as it does now, emitted a
    per-paper detail saying "N blocked: ...", and then returned `passed=True`
    unconditionally — with `# WARN not FAIL during rollout` as the only marker. So
    the only state in which it could fail was **zero gate nodes**, i.e. it failed
    when it could not measure and passed when it measured RED. Measured at the
    moment of the fix: **61 of 64 papers RED, verdict `True`.**

    Its docstring also promised that `validate.py --strict` would block submission.
    `STRICT_MODE` was never referenced in the body. That promise is now obsolete
    rather than unbuilt: the check hard-fails by default, which is what its own name
    and registered description have always claimed. (⚠️ this parenthetical read "`--strict`
    remains unreachable in practice anyway — no automated caller passes it" until
    2026-08-05. It is FALSE: `scripts/gate_precheck.py submission` runs
    `validate.py --strict --force-latex`. §Deferred item 6's disposition stands; its
    no-caller sub-clause does not.)

    The rollout the comment deferred to is over: `stage13_status` is now guarded,
    the bundles are in active remediation, and the operator's standing expectation
    is that gates go red as remediation applies. A gate that cannot go red is not a
    gate.
    """
    try:
        from build_graph import build_graph_json
    except ImportError as exc:
        # FAIL, not skip. Matches the reasoning already written into this module's
        # sibling `readiness_verdicts_agree`: a readiness guard that cannot load its
        # own dependency reports "no problem found", which is indistinguishable from
        # agreement. This branch returned passed=True until 2026-08-03.
        return CheckResult(passed=False, details=[
            Detail("import", False,
                   f"build_graph unavailable ({exc}) — the submission gate could not "
                   f"be evaluated, so its verdict is UNVERIFIED, not passing"),
        ])

    graph = build_graph_json()
    gates = [n for n in graph.get('nodes', []) if n['type'] == 'ReadinessGate']
    if not gates:
        # Zero gate nodes is not "no problems found" — it is the gate system being
        # absent, the only state in which every bundle trivially satisfies it.
        return CheckResult(passed=False, details=[
            Detail("gates", False,
                   "NO ReadinessGate nodes exist. The submission gate has nothing to "
                   "evaluate, so its verdict is vacuous — treat as unverified, not passing."),
        ])

    per_paper = classify_readiness(gates)
    green, yellow, red = partition_readiness(per_paper)
    ok = not red

    details = [
        Detail("summary", ok,
               f"{len(green)} green / {len(yellow)} yellow / {len(red)} red "
               f"across {len(per_paper)} papers"),
    ]
    for paper in green:
        details.append(Detail(paper, True, "all 11 gates passed"))
    for paper in yellow:
        s = per_paper[paper]
        details.append(Detail(
            paper, True,
            f"all P1 passed; advisory on: "
            f"{', '.join(g for g,_,_ in s['p2_advisory'] + s['open'])}",
            warning=True))
    for paper in red:
        s = per_paper[paper]
        blockers = s['p1_blocked'] + s['p2_blocked']
        details.append(Detail(
            paper, False,
            f"{len(blockers)} blocked: "
            f"{', '.join(g for g,_,_ in blockers[:5])}"
            + (f" (+{len(blockers)-5} more)" if len(blockers) > 5 else "")))

    return CheckResult(passed=ok, details=details)


# ═══════════════════════════════════════════════════════════════════════
# Phase 6i Wave 7.3 — bundle-level cross-paper consistency
# ═══════════════════════════════════════════════════════════════════════

@register_check("bundle_consistency",
                "Cross-bundle clusters' member sentences agree on numerical "
                "content across bundle boundaries")
def check_bundle_consistency() -> CheckResult:
    """For every cluster in `papers/cluster_bundle_index.json` whose
    `cross_bundle: true` flag is set, verify that the cluster's member
    sentences carry the same numerical content across all member
    bundles.

    The cluster index is built by `scripts/bundle_clusters.py` and
    projects each cluster's `member_papers` through
    `docs/PAPER_DRAFT_MAPPING.md` to determine which bundle codes the
    cluster spans. A cross-bundle cluster's member sentences must agree
    on:

    - Same primary source citation (bibkey).
    - Same numerical value (within ±2σ of the citation's reported
      uncertainty, or within 1% relative tolerance if no uncertainty
      is published).
    - Same Lean theorem reference (or no Lean reference if the cluster
      is qualitative).

    Mismatches are flagged at WARN level (advisory; not yet a blocker
    pending Wave 7.4 per-bundle Stage-13 sweep). The check exits
    cleanly when no cross-bundle clusters disagree.

    Phase 6i Wave 7.3 deliverable. Builds on the cluster-bundle index
    from Wave 7.1 + the per-bundle anchor list from Wave 7.2.
    """
    # Layout-independent (works from the main checkout AND a worktree slot):
    # _H.PAPERS_DIR = _H.PROJECT_ROOT / "papers", where _H.PROJECT_ROOT is this
    # checkout's repo root. The old `__file__.parent×3 / "SK_EFT_Hawking" /
    # "papers"` walk resolved to `.claude/worktrees/SK_EFT_Hawking/papers`
    # from a worktree. Per CLAUDE.md: never hardcode parent-walks.
    INDEX_PATH = _H.PAPERS_DIR / "cluster_bundle_index.json"

    details: List[Detail] = []
    if not INDEX_PATH.exists():
        return CheckResult(
            passed=False,
            error=(
                f"missing cluster bundle index at {INDEX_PATH}; "
                f"run `uv run python scripts/bundle_clusters.py` first"
            ),
        )

    try:
        idx = json.loads(INDEX_PATH.read_text())
    except (json.JSONDecodeError, OSError) as exc:
        return CheckResult(passed=False, error=f"failed to read index: {exc}")

    cross_bundle_clusters = [c for c in idx.get("clusters", [])
                             if c.get("cross_bundle")]
    n_total = idx.get("cluster_count", 0)
    n_cross = len(cross_bundle_clusters)

    details.append(Detail(
        "summary",
        True,
        f"{n_total} clusters indexed / {n_cross} cross-bundle clusters",
    ))

    if not cross_bundle_clusters:
        details.append(Detail(
            "no_cross_bundle_clusters",
            True,
            "No cross-bundle clusters present; nothing to verify.",
        ))
        return CheckResult(passed=True, details=details)

    # For each cross-bundle cluster, the cluster_detect.py exact-match
    # algorithm guarantees same `normalized_hash`. So if the cluster
    # was constructed by `match_kind: exact`, all member sentences
    # share the same normalized prose content by construction — the
    # only consistency risk is post-hoc drift via direct prose_state
    # edit. For `match_kind: normalized`, fuzzy matches may differ in
    # numerical content; flag those for manual review.
    n_passing = 0
    n_warning = 0
    for c in cross_bundle_clusters:
        match_kind = c.get("match_kind", "unknown")
        bundles = ",".join(c.get(
            "bundle_destinations_excluding_flagship", []
        ))
        if match_kind == "exact":
            details.append(Detail(
                f"exact_cluster:{c['id']}",
                True,
                f"exact-match cluster spans {bundles}; "
                f"normalized_hash guarantees identical content "
                f"({len(c.get('member_papers', []))} member papers).",
            ))
            n_passing += 1
        elif match_kind == "normalized":
            details.append(Detail(
                f"normalized_cluster:{c['id']}",
                True,  # advisory only
                f"normalized-match cluster spans {bundles}; "
                f"fuzzy match — manual numerical-consistency review "
                f"recommended at Stage 13 sweep.",
            ))
            n_warning += 1
        else:
            details.append(Detail(
                f"unknown_match_kind:{c['id']}",
                False,
                f"unknown match_kind {match_kind!r}; cluster index may "
                f"be stale — re-run scripts/bundle_clusters.py",
            ))

    details.append(Detail(
        "verdict",
        all(d.passed for d in details),
        f"{n_passing} exact-match clusters guaranteed consistent; "
        f"{n_warning} normalized-match clusters flagged for Stage-13 "
        f"manual review.",
    ))

    return CheckResult(
        passed=all(d.passed for d in details),
        details=details,
    )


#: Modules that must derive their bundle roster from `bundle_registry`, and the
#: bundle-keyed attribute names to compare against it. Adding a consumer here
#: is how you put it under the gate.
_ROSTER_CONSUMERS: tuple[tuple[str, tuple[str, ...]], ...] = (
    ("sentence_state", ("_VALID_BUNDLE_TARGETS",)),
    ("validate", ("BUNDLE_CODES",)),
    ("bundle_readiness", ("_BUNDLE_ORDER", "_TIER_OF")),
    ("review_runner", ("TIER_OF",)),
    ("bundle_source_manifest", ("_TIER_OF", "_BUNDLE_TITLES",
                               "_BUNDLE_TARGET_JOURNAL", "_BUNDLE_SUBPHASE")),
    ("datastar_bundles", ("_TIER_OF", "_BUNDLE_TITLES")),
    ("aristotle_usage_by_bundle", ("ALL_BUNDLES",)),
)

#: Files allowed to contain a literal bundle roster: the registry itself (the
#: one legitimate home) and the migration shim that reads historical rosters.
_ROSTER_LITERAL_ALLOWLIST = frozenset({"bundle_registry.py"})

#: A literal collection holding at least this many distinct bundle codes is a
#: roster, not a coincidence. The smallest real roster slice that could appear
#: innocently is a tier (Tier 1 has 12 members); 6 is comfortably below every
#: hand-rolled roster seen on 2026-07-30 and above any incidental grouping.
_ROSTER_LITERAL_THRESHOLD = 6


@register_check(
    "bundle_registry_consistency",
    "Publication-bundle roster has ONE source of truth "
    "(scripts/bundle_registry.py) that every consumer derives from")
def check_bundle_registry_consistency() -> CheckResult:
    """Gate the publication-bundle roster against re-fragmentation.

    Before 2026-07-30 the roster was hardcoded in **seven** places. The D11/D12
    first lift patched each by hand, and every omission had failed *silently
    and differently* — `validate.py` skipped D10 in the one check that catches
    Lean theorem-name drift in prose; `bundle_readiness.py` rendered 19 of 21
    bundles while looking complete; `aristotle_usage_by_bundle.py` reported a
    complete-looking `n/len(ALL_BUNDLES)` over a roster that stopped at D9. Only
    `review_runner.py` failed loudly (`KeyError('D10')`), and that one crash
    took down the Stage-13 prep-brief entry point for every bundle at once.

    Three independent legs, because "they all import the registry" is only
    true until someone writes a new dict:

    A. **Documentary agreement** — the registry's codes and tiers must match
       `docs/PAPER_STRATEGY.md` §6, the human-authoritative roster. This is the
       leg with teeth for the actual failure mode: a bundle authorized in the
       strategy doc but never registered. (Only code and tier are compared —
       the table's titles are abbreviated for width and its target column
       collapses the registry's ``|``-separated journal alternatives, since a
       literal ``|`` would break the markdown cell.)

    B. **Consumer agreement** — every module in `_ROSTER_CONSUMERS` exposes
       bundle-keyed attributes whose key sets equal the registry's exactly.
       Catches a consumer that drifts by filtering or extending the roster.

    C. **No re-hardcoding** — an AST walk over `scripts/*.py` flags any literal
       dict/list/tuple/set holding ≥6 distinct bundle codes outside the
       registry. This is the leg that stops the *next* authorized bundle from
       regressing this: leg B only sees maps that already exist, but leg C sees
       a brand-new hand-rolled roster the moment it is written. AST-based, so
       prose in comments and docstrings never trips it.
    """
    details: List[Detail] = []
    all_pass = True

    def check(name: str, passed: bool, msg: str, warning: bool = False) -> None:
        nonlocal all_pass
        details.append(Detail(name, passed, msg, warning=warning))
        if not passed and not warning:
            all_pass = False

    import bundle_registry as registry

    ref_codes = set(registry.BUNDLE_CODES)

    # ── Leg A: registry ↔ PAPER_STRATEGY.md §6 ──────────────────────────
    try:
        strategy = registry.parse_strategy_roster()
    except (OSError, ValueError) as exc:
        check("strategy_doc_parses", False, f"PAPER_STRATEGY.md §6: {exc}")
        strategy = None

    if strategy is not None:
        unregistered = sorted(set(strategy) - ref_codes)   # authorized, not registered
        unauthorized = sorted(ref_codes - set(strategy))   # registered, not in the doc
        check(
            "strategy_roster_matches", not unregistered and not unauthorized,
            "registry codes == PAPER_STRATEGY.md §6 "
            f"({len(ref_codes)} bundles)"
            if not unregistered and not unauthorized else
            "; ".join(filter(None, [
                f"authorized in PAPER_STRATEGY.md §6 but MISSING from "
                f"scripts/bundle_registry.py: {unregistered}"
                if unregistered else "",
                f"in scripts/bundle_registry.py but absent from "
                f"PAPER_STRATEGY.md §6: {unauthorized}" if unauthorized else "",
            ])),
        )
        tier_drift = {
            c: (t, registry.TIER_OF[c])
            for c, t in strategy.items()
            if c in registry.TIER_OF and registry.TIER_OF[c] != t
        }
        check(
            "strategy_tiers_match", not tier_drift,
            f"all {len(strategy)} tiers agree with PAPER_STRATEGY.md §6"
            if not tier_drift else
            f"tier drift (doc, registry): {tier_drift}",
        )

    # ── Leg B: every consumer's key set == the registry's ────────────────

    n_attrs = 0
    leg_b_ok = True
    for mod_name, attrs in _ROSTER_CONSUMERS:
        try:
            mod = importlib.import_module(mod_name)
        except Exception as exc:  # noqa: BLE001 — any import failure is a fail
            leg_b_ok = False
            check(f"consumer_imports:{mod_name}", False,
                  f"cannot import scripts/{mod_name}.py: {exc}")
            continue
        for attr in attrs:
            obj = getattr(mod, attr, None)
            if obj is None:
                leg_b_ok = False
                check(f"consumer_attr:{mod_name}.{attr}", False,
                      f"{mod_name}.{attr} is gone — update _ROSTER_CONSUMERS "
                      f"if it was intentionally renamed")
                continue
            keys = set(obj)
            n_attrs += 1
            if keys != ref_codes:
                leg_b_ok = False
                check(
                    f"consumer_roster:{mod_name}.{attr}", False,
                    f"{mod_name}.{attr} disagrees with bundle_registry — "
                    f"missing {sorted(ref_codes - keys)}, "
                    f"extra {sorted(keys - ref_codes)}",
                )
    if leg_b_ok:
        check("consumer_rosters_agree", True,
              f"{n_attrs} bundle-keyed attributes across "
              f"{len(_ROSTER_CONSUMERS)} modules all match the registry "
              f"({len(ref_codes)} bundles)")

    # ── Leg C: no re-hardcoded roster literals under scripts/ ────────────
    offenders: List[str] = []
    n_scanned = 0
    # ⚠️ rglob (fixed 2026-08-04). `glob("*.py")` stopped at `scripts/`, so the 12
    # check modules ADR-009 Phase 2 created under `scripts/validation/checks/` were
    # OUTSIDE the scan — a re-hardcoded roster written in a check module was invisible
    # to the very gate whose purpose is stopping the roster being hardcoded again.
    # Same class as QI-01 and as the `paper_tables` consumer: a scan scoped to a
    # directory the code has since moved out of.
    for py in sorted(_H.SCRIPT_DIR.rglob("*.py")):
        if py.name in _ROSTER_LITERAL_ALLOWLIST:
            continue
        try:
            tree = ast.parse(py.read_text(encoding="utf-8"), filename=str(py))
        except (OSError, SyntaxError) as exc:
            check(f"scan_parses:{py.name}", True, f"unparsed: {exc}",
                  warning=True)
            continue
        n_scanned += 1
        for node in ast.walk(tree):
            if isinstance(node, ast.Dict):
                elements = node.keys
            elif isinstance(node, (ast.List, ast.Tuple, ast.Set)):
                elements = node.elts
            else:
                continue
            found = {
                e.value for e in elements
                if isinstance(e, ast.Constant) and e.value in ref_codes
            }
            if len(found) >= _ROSTER_LITERAL_THRESHOLD:
                offenders.append(
                    f"{py.name}:{node.lineno} ({len(found)} bundle codes)")

    check(
        "no_rehardcoded_rosters", not offenders,
        f"{n_scanned} scripts/*.py scanned — no literal bundle roster outside "
        f"scripts/bundle_registry.py"
        if not offenders else
        "literal bundle rosters found outside scripts/bundle_registry.py "
        f"(import from it instead): {offenders}",
    )

    return CheckResult(passed=all_pass, details=details)




#: How many bundles may still declare NO apex theorems. **A RATCHET — it only goes down,
#: and 0 is the target.** Every bundle retrofitted under ADR-010 §D5a lowers it by one, in
#: the same commit.
#:
#: ⚠️ This is the instrument that keeps `bundle_apex_resolves` from being vacuous. Its
#: substantive predicate is "every declared apex resolves to a live theorem", a universal
#: over a set the bundles supply — so with nothing declared it is true of nothing, which
#: is the monotone-in-emptiness shape that made a whole family of content-facing checks on
#: this branch unable to fail (PR-review pass 2, H1). Counting the empty ones and refusing
#: to let that count RISE is what gives the check teeth on day one.
#:
#: 21 = every bundle on disk, measured 2026-08-06, when the closure machinery shipped and
#: no apexes had yet been declared. Declaration is gated on the operator's per-bundle
#: full-context-review condition (ADR-010 §D5a), so this started at the maximum by design.
#: 21 -> 20: D6 retrofitted 2026-08-06 (11 apexes; docs/audits/2026-08-06-d6-retrofit/).
#: 20 -> 19: D9 retrofitted 2026-08-06 (25 apexes, one per claim of its five-layer abstract).
#: 19 -> 18: L2 retrofitted 2026-08-06 (8 apexes).
#: 18 -> 17: D12 retrofitted 2026-08-06 (11 apexes, one per claim of its abstract;
#:           docs/audits/2026-08-06-d12-retrofit/FINDINGS.md). Chosen because ADR-010
#:           §What-remains item 2 lists the D6+D9+D12 merge as UNTESTED — with D6 and D9
#:           already declared, D12 makes the three-way overlap computable.
#: 17 -> 16: D11 retrofitted 2026-08-07 (73 apexes; docs/audits/2026-08-07-d11-retrofit/
#:           FINDINGS.md). The apex count is high because the draft is written as a
#:           theorem catalogue — 73 statements are presented as results across five
#:           independent layers. Its closure reaches NOTHING outside its own modules,
#:           so D11 borrows from no other bundle.
#: 16 -> 15: D10 retrofitted 2026-08-07 (33 apexes; docs/audits/2026-08-07-d10-retrofit/
#:           FINDINGS.md). Chosen to close ADR-010's second untested merge, and it does:
#:           D10 ∩ D11 = 0, while D10 ∩ D9 = 50. The pairing was adjacency, not content.
#: 15 -> 14: D1 retrofitted 2026-08-07 (41 apexes; docs/audits/2026-08-07-d1-retrofit/
#:           FINDINGS.md). Supplies the honest denominator for TODO-D9's
#:           \substantivetheorems{} overclaim: D1's measured closure is 249 declarations.
#: 14 -> 13: F retrofitted 2026-08-07 (29 apexes; docs/audits/2026-08-07-f-retrofit/
#:           FINDINGS.md) — the first Tier-0. The flagship enumerates a 17-bundle roster
#:           and does not know D9-D12 exist; F ∩ D1 = 27 and F ∩ each of D6/D9/D10/D11/
#:           D12/L2 = 0.
#: 13 -> 12: D3 retrofitted 2026-08-07 (89 apexes; docs/audits/2026-08-07-d3-retrofit/
#:           FINDINGS.md) — the heaviest bundle. D3 ∩ F = 126 (F's substrate is largely
#:           D3's) but D3 ∩ D1 = 0: the program's "the substrate is one object"
#:           synthesis claim has no Lean witness.
#: 12 -> 11: D2 retrofitted 2026-08-07 (47 apexes; docs/audits/2026-08-07-d2-retrofit/
#:           FINDINGS.md). Narrowed TODO-D16 — a Witt-invariant bridge D3<->D2 DOES
#:           exist (3 shared GenerationConstraint declarations); it is the Sakharov
#:           N_f identity specifically that has no witness. Also L2 ∩ D2 = 391 of
#:           L2's 430.
UNDECLARED_APEX_CEILING = 11


@register_check(
    "bundle_apex_resolves",
    "Every apex theorem a bundle declares names a live Lean theorem, and the "
    "undeclared-bundle count does not rise (publication-intake closure)")
def check_bundle_apex_resolves() -> CheckResult:
    """Gate the ONE hand-maintained input to the bundle substrate closure.

    A bundle declares its apex theorems in `papers/<bundle>/bundle_metadata.json`; its
    substrate is the derived transitive closure of those apexes and therefore cannot
    drift. That puts the whole drift risk in a handful of names per bundle — which is
    exactly what this check reads.

    Three hard failures:

    * an apex naming **no live declaration** (a rename, a deletion, a typo). The closure
      silently shrinks and the bundle looks smaller rather than broken.
    * an apex resolving to something **other than a theorem**. A bundle claims results; a
      `def` or `structure` is machinery the results are stated over, and seeding a closure
      from one pulls in the definition's dependencies while claiming nothing.
    * the **undeclared-bundle count rising** above `UNDECLARED_APEX_CEILING`.

    ⚠️ The third is not decoration, it is what makes the other two non-vacuous. "Every
    declared apex resolves" is a universal over a bundle-supplied set, so today — with
    nothing declared anywhere — it holds of nothing. A check in that shape reports a clean
    pass over an absence, which is the exact defect this branch exists to remove. The
    ratchet measures the absence directly and refuses to let it grow, and the per-bundle
    detail says UNKNOWN rather than summing the missing substrate to zero.
    """
    import bundle_closure

    details: List[Detail] = []
    all_pass = True

    def check(name: str, passed: bool, msg: str, warning: bool = False) -> None:
        nonlocal all_pass
        details.append(Detail(name, passed, msg, warning=warning))
        if not passed and not warning:
            all_pass = False

    papers_root = _H.PROJECT_ROOT / "papers"
    declarations = bundle_closure.load_apex_declarations(papers_root)
    if not declarations:
        # No bundle metadata at all — the input is ABSENT, not empty. This is the one
        # branch that genuinely cannot measure.
        return CheckResult(
            passed=True, measured=False,
            details=[Detail("papers_present", True,
                            f"no bundle metadata under {papers_root} — nothing to measure",
                            warning=True)])

    unreadable = sorted(b for b, d in declarations.items() if d.get("unreadable"))
    check("metadata_readable", not unreadable,
          f"{len(declarations)} bundle metadata files parse"
          if not unreadable else
          "unreadable bundle_metadata.json (an undeclared bundle, not an absent one): "
          f"{unreadable}")

    declared = {b: d for b, d in declarations.items() if d["declared"] and d["apexes"]}
    undeclared = sorted(set(declarations) - set(declared))

    check("undeclared_does_not_rise", len(undeclared) <= UNDECLARED_APEX_CEILING,
          f"{len(undeclared)} of {len(declarations)} bundle(s) declare no apexes "
          f"(ceiling {UNDECLARED_APEX_CEILING}; substrate UNKNOWN, not empty)"
          + (f": {', '.join(undeclared)}" if undeclared else "")
          if len(undeclared) <= UNDECLARED_APEX_CEILING else
          f"undeclared bundles rose to {len(undeclared)}, above the ratchet's "
          f"{UNDECLARED_APEX_CEILING}: {', '.join(undeclared)}",
          warning=bool(undeclared) and len(undeclared) <= UNDECLARED_APEX_CEILING)

    if not declared:
        # Nothing to resolve — say so, rather than reporting a vacuous pass on the
        # substantive predicate. The ratchet above is what carries this check today.
        details.append(Detail(
            "apexes_resolve", True,
            f"UNMEASURABLE — no bundle declares `{bundle_closure.APEX_KEY}`, so there is "
            "no apex to resolve; the undeclared-count ratchet is this check's only live "
            "assertion until the first bundle is retrofitted",
            warning=True))
        return CheckResult(passed=all_pass, details=details)

    records = bundle_closure.load_records()
    closures = bundle_closure.build_closures(records, declarations)

    unresolved = {b: c.unresolved_apexes for b, c in closures.items()
                  if c.unresolved_apexes}
    check("apexes_resolve", not unresolved,
          f"{sum(len(d['apexes']) for d in declared.values())} declared apexes across "
          f"{len(declared)} bundle(s) all name live declarations"
          if not unresolved else
          f"declared apexes naming no live declaration: {unresolved}")

    non_theorem = {b: c.non_theorem_apexes for b, c in closures.items()
                   if c.non_theorem_apexes}
    check("apexes_are_theorems", not non_theorem,
          "every declared apex is a theorem"
          if not non_theorem else
          "declared apexes that are not theorems (a bundle claims results, not "
          f"definitions): {non_theorem}")

    # Closure shape, always WITH its truncation — a size published alone reads complete.
    for b, c in sorted(closures.items()):
        if not c.measurable:
            continue
        details.append(Detail(
            f"closure_{b}", True,
            f"{len(c.apexes)} apex(es) → {len(c.closure)} declarations across "
            f"{len(c.modules)} modules, depth {c.max_depth}"
            + (f" ⚠ {c.truncated_private} walk(s) stopped at a private declaration"
               if c.truncated_private else ""),
            warning=bool(c.truncated_private)))

    return CheckResult(passed=all_pass, details=details)
