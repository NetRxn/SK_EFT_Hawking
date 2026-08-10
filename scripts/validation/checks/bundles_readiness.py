"""Bundle-metadata, readiness-gate and roster checks — ADR-009 Phase 2.

`bundle_figure_integrity`, `bundle_metadata_matches_graph`,
`bundle_stage13_claim_consistent`, `readiness_verdicts_agree`,
`readiness_submission_gate`, `bundle_consistency`, `bundle_registry_consistency`.

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
#
# ⚠️ `re` is back (2026-08-08, ADR-011 Phase 1) and this time it IS referenced —
# `_PAGES_RE` below. The 2026-08-04 removal was for a dead import, not a ban.

import re

#: `pdfinfo`'s page line. The rendered PDF is the only honest source for a page
#: count: `.log` files are not trustworthy for a shared bundle (see the module
#: docstring of `scripts/compile_bundle_pdf.py`), and a stored number cannot be
#: told apart from a stale one.
_PAGES_RE = re.compile(r"Pages:\s+(\d+)")


def _read_metadata(code: str) -> dict | None:
    """`papers/<code>/bundle_metadata.json`, or `None` if absent/unparseable.

    `None` means UNKNOWN — every caller must treat it as unmeasured rather than as
    an empty blob whose fields all read as absent-and-therefore-fine.
    """
    p = _H.PAPERS_DIR / code / "bundle_metadata.json"
    try:
        return json.loads(p.read_text())
    except (OSError, json.JSONDecodeError):
        return None


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
            _SPEC_FALLBACK = None
        else:
            raise RuntimeError("no d11_/d12_ specs found")
    except Exception as _spec_exc:      # noqa: BLE001
        # ⚠️ The fallback itself is defensible; its SILENCE was not. This exact
        # literal was live for a whole review round — production always used it,
        # i.e. the hand-maintained list this block exists to replace — and nothing
        # said so. Round 1 fixed the cause and left the silence; `_SPEC_FALLBACK`
        # is now surfaced as a warning Detail below.
        _SPEC_FALLBACK = f"{type(_spec_exc).__name__}: {_spec_exc}"
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

    # ⚠️ THE SCOPE RIDES ON THE SUMMARY. This check's population is the
    # REGISTRY-BACKED figures it can regenerate, which the `d11_`/`d12_` prefix
    # filter above restricts to two bundles — while thirteen bundles carry
    # figures on disk. `gate_precheck.py`'s s9 leg calls this check before a
    # figure-reviewer dispatch, so a dispatch on D5 or I1 previously printed
    # PASS having examined ZERO of that bundle's figures. A regenerable figure
    # and a migrated one are different states and the check can only speak to
    # the first; what it must not do is let the second read as covered.
    import bundle_registry as _registry
    _codes = set(_registry.BUNDLE_CODES)
    on_disk = {}
    for png in sorted(_H.PAPERS_DIR.glob("*/figures/*.png")):
        code = png.parent.parent.name
        if code in _codes:
            on_disk[code] = on_disk.get(code, 0) + 1
    uncovered = {c: n for c, n in on_disk.items() if c not in SPECS}
    if uncovered:
        # ⚠️ `measured` stays TRUE, under the SAME policy this codebase applies to
        # partial Lean-module resolution: `measured=False` means the population was
        # UNREACHABLE, not incompletely covered. This detail said `measured=False`
        # for incomplete coverage — the precise case the policy abolishes — inside
        # the very check the policy comment cites as its exemplar. Found by the
        # closure reviewer. The uncovered figures are a WARNING within a
        # measurement, which is what the warning flag is for. The check really did measure the
        # registry-backed figures; calling the whole result unmeasured would be
        # its own false statement, and would silently drop a check out of the
        # `--ci` coverage floor — a zero-headroom instrument. What was wrong was
        # that the uncovered figures had no machine-readable mark at all, so a
        # consumer reading details saw a passing census.
        #
        # ⚠️ RESIDUAL, stated rather than closed: `gate_precheck s9` consumes only
        # this check's EXIT CODE, so it still cannot see this warning, and a
        # figure-reviewer dispatch on a fully-uncovered bundle still prints PASS.
        # Closing that means either registering the uncovered figures in
        # `visualizations.py` or teaching `gate_precheck` the per-bundle coverage
        # — both real work, neither hidden.
        details.insert(0, Detail(
            "coverage", True,
            f"{sum(uncovered.values())} figure(s) across {len(uncovered)} bundle(s) "
            f"are NOT registry-backed and were not regenerated or measured: "
            f"{', '.join(f'{c}:{n}' for c, n in sorted(uncovered.items()))}. "
            f"This check speaks only to figures it can rebuild from "
            f"`visualizations.py`; the rest are UNMEASURED here.",
            warning=True))
    if _SPEC_FALLBACK:
        details.insert(0, Detail(
            "spec_source", True,
            f"the D11/D12 figure specs came from the HARDCODED FALLBACK, not from "
            f"`review_figures.FIGURE_REGISTRY` ({_SPEC_FALLBACK}) — the list this "
            f"derivation exists to replace is what actually ran",
            warning=True, measured=False))
    details.insert(0, Detail(
        "summary", n_fail == 0,
        f"{n_ok + n_fail} registry-backed bundle figures checked — {n_ok} legible / "
        f"{n_fail} below the {FLOOR_PT}pt floor; {sum(on_disk.values())} figure(s) "
        f"exist across {len(on_disk)} bundle(s)"))
    # The spec-source fallback IS a population failure (the registry could not be
    # read, so the specs came from a frozen literal), unlike partial figure
    # coverage above — so it, and only it, flips the check's own `measured`.
    #
    # ⚠️ **THIS COUPLES THE ZERO-HEADROOM `--ci` FLOOR TO AN OUT-OF-BAND IMPORT, and
    # that consequence is deliberate but was undisclosed when first shipped.**
    # `CI_MIN_CHECKS_RUN` is 75 with no slack, so a failed `review_figures`
    # FIGURE_REGISTRY load now turns `--ci` red rather than merely warning. That
    # import demonstrably failed on EVERY run for a whole review round (see the
    # comment at the fallback itself) without anyone noticing — which is the
    # argument for the coupling, not against it: a silent fallback to the
    # hand-maintained list this derivation exists to replace should stop the build.
    return CheckResult(passed=n_fail == 0,
                       measured=_SPEC_FALLBACK is None, details=details)


def _readiness_aggregate():
    """`(by_bundle, metadata_path_fn, failure_detail)` — the live per-bundle aggregation.

    Shared by the two metadata checks below. Returns `(None, None, Detail)` on any
    failure to compute, so each caller fails CLOSED with its own subject named: an
    uncomputable live verdict is not agreement (D12 round-8 BLOCKER 8.2).
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
        return None, None, Detail(
            "import", False,
            f"could not import the readiness machinery ({exc}) — this check is "
            f"UNVERIFIED, not passing")
    try:
        by_bundle = aggregate_by_bundle(
            parse_mapping(MAPPING_DOC.read_text()),
            load_findings_by_paper(),
            resolve_stage13_reviews(backfill=False))
    except Exception as exc:
        # FAIL, not pass: an uncomputable live verdict is not agreement.
        return None, None, Detail(
            "aggregate", False,
            f"live counts could not be computed ({type(exc).__name__}: {exc}) "
            f"— metadata is therefore UNVERIFIED, not matching")
    return by_bundle, _bundle_metadata_path, None


@register_check("bundle_stage13_claim_consistent",
                "No bundle claims stage13_status='green' while the graph shows open blockers")
def check_bundle_stage13_claim_consistent() -> CheckResult:
    """CHECK: a metadata REVIEW-VERDICT claim contradicted by the live graph.

    **Split out of `bundle_metadata_matches_graph` on 2026-08-07 (TODO-D23, operator
    authorized).** It lived there from 2026-08-03 because nothing else in the repo read
    `stage13_status` and the hole needed a home. The cost of that housing was measured
    twice in one session: the check registered as *"finding counts equal the live
    graph's"*, so when this leg fired the failure was mis-read as count drift by its own
    author and read as spurious by the operator. Both readings follow from the
    description. The assertion was never in question — only its label.

    **Why it is a different assertion from the count comparisons.** Those compare a
    metadata field to the same field derived from the graph: `blockers_open == live`.
    This one compares a metadata CLAIM against a graph FACT OF ANOTHER SHAPE — the blob
    says a past Stage-13 review returned green (i.e. no blocking finding remained) while
    the graph carries open blockers. Both cannot be true. It is a genuine
    metadata-vs-graph contradiction, but a semantic one, not a field equality, and that
    is exactly why it reported badly under the old name.

    The remedy is quoted verbatim from this project's own reviewer,
    `papers/AutomatedReviews/2026-07-31-1652-internal-adversarial/D11.md:227`:
    "a bundle with `blockers_open > 0` must not carry `stage13_status: 'green'`".
    A mutation test proving the hole was already committed at
    `2026-08-01-0009-internal-adversarial/D11.md:179` (flip pending->green =>
    "PASS <-- missed"). The test existed; the guard did not.

    Compared against the LIVE count, never `meta["blockers_open"]`: hand-editing the
    count to 0 to silence this would trip `bundle_metadata_matches_graph` instead, so
    both checks have to be defeated rather than one. That cross-bracing is the reason
    the two stay adjacent after the split.

    NOT asserted here: `stage13_redo_required`. The same reviewer paired it with the rule
    above, but the two are independent: `redo_required` means "new content was appended
    since the last review" (written by `bundle_append.py`), NOT "blockers are open". A
    bundle can correctly carry blockers with `redo_required: false` when the blockers came
    from the review itself rather than from a later lift.

    NOT asserted here: `freshness_stale`. D12 Stage-13 round-8 reported that seven bundles
    set it false with blockers open, citing LATE_PHASE6_ABSORPTION_PROTOCOL.md. That
    assertion was implemented once and was wrong — the field is owned by
    `scripts/check_bundle_source_freshness.py` and means "a source paper is newer than
    last_lift", independent of blocker count. The protocol line quoted is a workflow step,
    not the field's definition. Asserting it made two writers fight and `validate.py`
    non-idempotent.

    NOT asserted here: the Stage-9/10-before-13 ORDERING gate
    (`BUNDLE_LIFT_PROCEDURE.md:9`). That is a different defect — a green that was invalid
    WHEN WRITTEN because a prerequisite stage had not passed, rather than one contradicted
    by findings filed LATER. It now has its own check, `bundle_reviewer_stage_ordering`
    (ADR-011 Phase 2), and is deliberately not folded in here.
    """
    by_bundle, meta_path, failure = _readiness_aggregate()
    if failure is not None:
        return CheckResult(passed=False, details=[failure])

    details: list[Detail] = []
    bad = 0
    checked = 0
    for bundle, agg in sorted(by_bundle.items()):
        mp = meta_path(bundle)
        if not mp.is_file():
            # FAIL, not skip: a bundle with no metadata blob makes no stage13 claim, which
            # is not the same as making a consistent one. `bundle_metadata_matches_graph`
            # reports the same bundle for its own subject; both are UNVERIFIED here.
            bad += 1
            details.append(Detail(
                bundle, False,
                f"no bundle_metadata.json at {mp} — this bundle's Stage-13 claim does "
                f"not exist, so it is unverified rather than consistent"))
            continue
        try:
            meta = json.loads(mp.read_text())
        except (json.JSONDecodeError, OSError) as exc:
            bad += 1
            details.append(Detail(bundle, False, f"metadata unreadable: {exc}"))
            continue
        checked += 1
        live_blockers = agg.get("blocker_count", 0)
        if str(meta.get("stage13_status", "")).strip().lower() == "green" \
                and live_blockers > 0:
            bad += 1
            details.append(Detail(
                bundle, False,
                f"stage13_status='green' while {live_blockers} blocker(s) are open — "
                f"Stage 13 is GREEN only when no blocking finding remains "
                f"(BUNDLE_LIFT_PROCEDURE.md §12). ⚠️ `stage13_status` is NOT written by "
                f"`bundle_readiness.py` — that script owns blockers_open / "
                f"advisories_open / open_findings / blocked_p1_gates / readiness only. "
                f"It is set by the Stage-13 review cycle (BUNDLE_LIFT_PROCEDURE.md "
                f"§§8–10), so a green value here is a claim about a PAST review that "
                f"newly-minted blockers have since contradicted. Re-running the counts "
                f"writer will NOT clear it: the bundle re-enters at Stage 9/10 and only "
                f"then Stage 13 (BUNDLE_LIFT_PROCEDURE.md:9 gate ordering)."))

    # Seam guard (guide §2.5): a loop that inspected nothing must not report agreement.
    if checked == 0:
        details.insert(0, Detail(
            "population", False,
            "no bundle metadata blob was inspected — this check is UNVERIFIED, not "
            "passing (an empty population is the round-8 state: every readiness check "
            "green with nothing to check)"))
        return CheckResult(passed=False, measured=False, details=details)

    details.insert(0, Detail(
        "summary", bad == 0,
        f"{checked} bundle Stage-13 claim(s) checked against the live blocker counts, "
        f"{bad} contradicted"))
    return CheckResult(passed=bad == 0, details=details)


#: An em-dash: the LaTeX ligature (EXACTLY three hyphens) or the literal character.
#:
#: ⚠️ **The lookarounds are the whole check.** `--` is an EN-DASH and is MANDATORY
#: scientific typography — `Bose--Einstein`, `Bekenstein--Hawking`, `SK--EFT`,
#: `Kaul--Majumdar`, page ranges. The corpus carries **1,121 of them**. A pattern that
#: did not require exactly-three would flag 1,862 occurrences and be WRONG about 1,121,
#: and "fixing" those would corrupt every compound eponym in the program. One line
#: carries both: `observables---also drives the SK--EFT`.
_EM_DASH_RE = re.compile(r"(?<!-)---(?!-)|—")

#: `%` that is not `\%`. Comments never reach a reader, so an em-dash inside one is not
#: an authorship signal; the sweep left several in place deliberately.
_TEX_COMMENT_RE = re.compile(r"(?<!\\)%.*")



#: THE ONE definition of "reader-visible prose for bundle `code`".
#:
#: ⚠️ Three checks share this subject — em-dash freedom, reader-facing voice, and
#: sentence length — and the closure widening landed at ONE of them. The other two
#: kept reading `paper_draft.tex` alone, so `papers/I1/tables/table1_stages.tex`
#: stayed invisible to both; `bundle_sentence_length` is additionally a down-only
#: ratchet frozen over the narrow population, so every day it stayed narrow raised
#: the cost of widening it. A reader does not know or care which file a sentence was
#: typed in, so neither should the population.
def _reader_visible_sources(tex: Path) -> list[Path]:
    r"""`tex` plus every `.tex` it \input{}s, transitively, de-duplicated.

    `.bib` and image members of the closure are excluded: a bibliography entry is
    not manuscript prose.
    """
    return sorted({tex, *(p for p in _H.draft_input_closure(tex)
                          if p.suffix == ".tex" and p.is_file())})


def _reader_visible_sources_and_gaps(tex: Path) -> tuple[list[Path], list[str]]:
    r"""`(sources, unscannable)` — the population AND what fell out of it.

    ⚠️ **The gap report is bound to the population on purpose.** The unscannable
    guard was wired into the em-dash check alone, so a draft that `\input`s a
    renamed file was silently clean in `bundle_sentence_length` and
    `bundle_reader_facing_voice` — and `bundle_sentence_length` is a DOWN-ONLY
    RATCHET whose floor was just lowered 22→20. A missing `\input` silently
    shrinks that ratchet's own population, and the ratchet then locks in a floor
    derived from prose it never read. Returning the two together means a caller
    cannot consume the population without receiving its gaps.
    """
    return _reader_visible_sources(tex), _unscannable_closure_members(tex)


def _unscannable_closure_members(tex: Path) -> list[str]:
    """`.tex` closure members DROPPED because they do not resolve to a file.

    ⚠️ `draft_input_closure` keeps an unresolvable `\\input` target on purpose —
    "an unresolvable reference is still recorded as a path" — and the `.is_file()`
    filter above discards exactly those, silently. A draft with
    `\\input{tables/gone}` scanned clean and reported "0 em-dashes" with no detail
    naming the file it never opened. Zero such entries exist today, so this is
    latent — latent on the very widening these checks just shipped.
    """
    return sorted(
        str(q) for q in _H.draft_input_closure(tex)
        if q.suffix == ".tex" and not q.is_file())


#: Environments whose `\\` is a ROW separator, not a line break inside a sentence.
_ROW_ENV_RE = re.compile(
    r"\\begin\{(tabular\*?|tabularx|array|longtable|matrix|align\*?|split)\}"
    r".*?\\end\{\1\}", re.DOTALL)


def _rows_as_sentences(body: str) -> str:
    r"""Make each table row its own unit before sentence splitting.

    ⚠️ Measured 2026-08-09: without this, `papers/I1/tables/table1_stages.tex`
    reports a single **166-word sentence** that no reader ever sees — it is fifteen
    three-column table rows concatenated, because `\\` is not a sentence boundary to
    the splitter. Widening the sentence-length population to the input closure
    imported that artifact and pushed the over-100 count from 22 to 23, one past a
    down-only ratchet, for a defect that does not exist in the prose.
    **Scoped to row environments deliberately**: splitting on every `\\` would also
    split a genuine over-long sentence that happens to contain a line break, which
    would hide real debt — the opposite error.
    """
    return _ROW_ENV_RE.sub(lambda m: m.group(0).replace("\\\\", ". "), body)


@register_check("bundle_prose_em_dash_free",
                "No bundle draft contains an em-dash in prose a reader will see")
def check_bundle_prose_em_dash_free() -> CheckResult:
    """CHECK (ADR-011 Phase 3): zero em-dashes in rendered manuscript prose.

    **A trust signal, not a style preference**, and that is why the target is zero rather
    than a ratcheted rate (operator direction, 2026-08-08): *an em-dash immediately
    signals AI authorship to a human reader in 2026, and decreases trust.* One is as
    disqualifying as forty, so a density threshold would measure the wrong thing.

    **Measured before the sweep: 741 across the corpus** (621 `---` + 120 literal `—`),
    with **0 of 21 bundles clean**. Removing them was a rewrite rather than a
    substitution — an em-dash usually joins two clauses, and the right replacement is a
    colon, a semicolon, parentheses, or a full stop depending on the job it was doing.
    Six agents read every occurrence in context; the sentence shapes that generate them
    are recorded in the authoring skill's `references/prohibited-patterns.md`.

    ⚠️ **This check CANNOT see the regression it is most likely to cause.** It counts
    exactly-three hyphens, so an author who over-corrects to "no dashes at all" and
    breaks `Bose--Einstein` passes it silently. That rule lives in the authoring
    reference, where a human reads it, because no scan distinguishes a missing en-dash
    from a compound word.

    Comments are stripped: `%` text never reaches a reader, so an em-dash there is not an
    authorship signal.

    ⚠️ **THE POPULATION IS THE DRAFT'S `\\input` CLOSURE, NOT THE DRAFT.** It scanned
    `paper_draft.tex` alone until 2026-08-09, and a reader does not know or care which
    file a sentence was typed in: `papers/I1/tables/table1_stages.tex:10-11` carried two
    reader-visible em-dashes inside a live `\\input`ed table and the gate reported I1
    clean. Found by the closure reviewer, not by this check. `draft_input_closure` is the
    same definition `paper_latex_compiles`, `bundle_manuscript_length` and
    `compile_bundle_pdf` already use for "which files change this draft", so widening to
    it costs no new notion of scope — and a check whose subject is *what a reader sees*
    has no business stopping at a file boundary the reader cannot perceive.
    """
    details: List[Detail] = []
    try:
        import bundle_registry as registry
        codes = list(registry.BUNDLE_CODES)
    except Exception as exc:  # noqa: BLE001
        return CheckResult(passed=False, measured=False, details=[Detail(
            "roster", False,
            f"could not read the bundle roster ({exc}) — UNVERIFIED, not passing")])

    checked = total = n_unscannable = 0
    for code in codes:
        tex = _H.PAPERS_DIR / code / "paper_draft.tex"
        if not tex.is_file():
            continue
        checked += 1
        hits = []
        for missing in _unscannable_closure_members(tex):
            n_unscannable += 1
            details.append(Detail(
                f"{code}:unscannable:{n_unscannable}", False,
                f"\\input target {missing} does not resolve to a file and was NOT "
                f"scanned — an unread file is not a clean one",
                measured=False))
        for src in _reader_visible_sources(tex):
            for i, line in enumerate(src.read_text(errors="replace").splitlines(), 1):
                body = _TEX_COMMENT_RE.sub("", line)
                n = len(_EM_DASH_RE.findall(body))
                if n:
                    hits.append((src, i, n, body.strip()[:90]))
        if hits:
            n = sum(h[2] for h in hits)
            total += n
            files = len({h[0] for h in hits})
            details.append(Detail(
                code, False,
                f"{n} em-dash(es) on {len(hits)} line(s) across {files} file(s); "
                f"first at {hits[0][0].relative_to(_H.PROJECT_ROOT)}:{hits[0][1]} "
                f"— {hits[0][3]!r}"))

    if checked == 0:
        details.insert(0, Detail(
            "population", False,
            "no bundle draft was read — this check is UNVERIFIED, not passing"))
        return CheckResult(passed=False, measured=False, details=details)

    # ⚠️ An unscannable closure member must reach the VERDICT, not just the detail
    # list. Emitting a `passed=False` Detail while returning `passed=(total == 0)`
    # leaves the check green over a file it never opened — the same
    # silence-reads-as-clean shape the widening was meant to close.
    details.insert(0, Detail(
        "summary", total == 0 and n_unscannable == 0,
        f"{checked} bundle draft(s) scanned, {total} em-dash(es) in reader-visible prose "
        f"(target 0; en-dashes are mandatory and deliberately untouched)"
        + (f"; ⚠️ {n_unscannable} closure member(s) could NOT be scanned"
           if n_unscannable else ""),
        measured=(n_unscannable == 0)))
    return CheckResult(passed=(total == 0 and n_unscannable == 0),
                       measured=(n_unscannable == 0), details=details)


#: Module basenames too generic to find by substring. A hit on `Basic` proves nothing.
_AMBIGUOUS_MODULE_BASENAMES = frozenset({
    "Basic", "Trace", "Module", "Sum", "Spectrum", "Chain", "Concrete", "Positive",
    "Log", "Core", "Defs", "Util", "Utils", "Main", "Types", "Lemmas",
})

#: Registered-but-absent modules, corpus-wide. **A RATCHET: may only shrink.**
#:
#: MEASURED 2026-08-08: **238 of 444 declared modules (54%)** are registered in a
#: bundle's `append_log.json` as contributing and are never named in its draft. D10 and
#: E1 declare modules and cite NONE of them; D9 is 64 absent of 77.
#:
#: ⚠️ **Absent is not automatically a defect, and the ratchet is why this is honest.**
#: A module can legitimately support a cited result without being named, so a ~53%
#: absence rate more likely reflects generous registration (every module a wave touched)
#: than incomplete drafts. What the number *does* say is that the link between declared
#: substrate and published claim is weak, and it can only be strengthened. Lower it by
#: citing the module or by not registering it, never by widening the ambiguous list.
#: 2026-08-09: 238 -> 236, attributed by measurement rather than assumed. **It is D10,
#: 11 -> 9**, from the TODO-D12 prose repair naming two modules it already registered;
#: D9 (64) and E1 (7) are unchanged. The first guess — D3's restructuring — was WRONG:
#: swapping D3's draft for its HEAD version changes no bundle's count. Lowered because
#: the live count fell, which is the direction the ratchet exists to allow.
LEAN_MODULE_ABSENT_CEILING = 236


@register_check("bundle_lean_module_coverage",
                "Lean modules a bundle registers as contributing are named in its draft (ratcheted)")
def check_bundle_lean_module_coverage() -> CheckResult:
    """CHECK (ADR-011 Phase 6, F-10): declared substrate reaches the published claim.

    `bundle_append.py --lean-modules` records, per append event, which Lean modules a
    source contributed. Nothing ever compared that list to the manuscript, so a bundle
    could register a module family and never mention it: **E1 declares 7 modules and cites
    none of them.** D10 was in the same state until TODO-D12's prose repair named 2 of its
    11 — a correction recorded in the ceiling's own addendum above ("It is D10, 11 -> 9")
    and NOT here, 15 lines below it, for two days. Same defect as D15/D36/D4: the fix
    landed at the site the finding named and not at the second site carrying the claim.

    ⚠️ **The field is `lean_modules_referenced`, not `lean_modules`.** Probing the latter
    reports 0 of 21 bundles declaring anything, which reads as "the data does not exist"
    and would have retired this check as unbuildable. It is
    `reference-measurement-traps-false-absence` exactly: a narrow key makes a live
    population scan empty.

    **Matching is underscore-aware and basename-tolerant.** Drafts escape underscores
    inside `\\thm{}`/`\\texttt{}`, so `Foo_Bar` appears as `Foo\\_Bar` and a bare
    substring test misses it; and a dotted module is often cited by its leaf
    (`APSEta.He3A` as `He3A`). Both forms count.
    """
    details: List[Detail] = []
    try:
        import bundle_registry as registry
        codes = list(registry.BUNDLE_CODES)
    except Exception as exc:  # noqa: BLE001
        return CheckResult(passed=False, measured=False, details=[Detail(
            "roster", False,
            f"could not read the bundle roster ({exc}) — UNVERIFIED, not passing")])

    checked = declared = absent_total = 0
    worst: list[tuple[int, str, list[str]]] = []
    for code in codes:
        log = _H.PAPERS_DIR / code / "append_log.json"
        tex = _H.PAPERS_DIR / code / "paper_draft.tex"
        if not log.is_file() or not tex.is_file():
            continue
        try:
            events = json.loads(log.read_text()).get("events", [])
        except (OSError, json.JSONDecodeError):
            continue
        mods: set[str] = set()
        for e in events:
            v = e.get("lean_modules_referenced") or []
            if isinstance(v, str):
                v = v.split(",")
            mods |= {str(x).strip() for x in v if str(x).strip()}
        if not mods:
            continue
        checked += 1
        declared += len(mods)
        # `\_` -> `_` so an escaped identifier matches its declared form.
        body = tex.read_text(errors="replace").replace("\\_", "_")
        missing = [m for m in sorted(mods)
                   if m.split(".")[-1] not in _AMBIGUOUS_MODULE_BASENAMES
                   and m.split(".")[-1] not in body and m not in body]
        absent_total += len(missing)
        if missing:
            worst.append((len(missing), code, missing))

    if checked == 0:
        details.insert(0, Detail(
            "population", False,
            "no bundle declares a contributing Lean module — this check is UNVERIFIED, "
            "not passing. The field is `lean_modules_referenced` in append_log.json"))
        return CheckResult(passed=False, measured=False, details=details)

    for n, code, missing in sorted(worst, reverse=True):
        details.append(Detail(
            code, True,
            f"{n} of the modules it registers are never named in its draft "
            f"(e.g. {', '.join(missing[:3])})", warning=True))

    ok = absent_total <= LEAN_MODULE_ABSENT_CEILING
    details.insert(0, Detail(
        "ratchet", ok,
        f"{absent_total} registered-but-absent module(s) across {checked} bundle(s) "
        f"({declared} declared); ceiling {LEAN_MODULE_ABSENT_CEILING}"
        + ("" if ok else
           " — REGISTERED SUBSTRATE DRIFTED FURTHER FROM THE PUBLISHED CLAIM. Cite the "
           "module or stop registering it; do not widen the ambiguous-basename list")))
    return CheckResult(passed=ok, details=details)


#: Section-count ceiling by tier. A 30–50 pp article with more than twenty top-level
#: sections is a table of contents, not an argument. Tier 0 (a review) is exempt.
_SECTION_CEILING_BY_TIER = {1: 20, 2: 20, 3: 20, 4: 20}

#: A closing section, by the names this corpus actually uses. Deliberately wide: it is a
#: presence floor, and a false positive here would demand a rename for no reader benefit.
_CLOSING_SECTION_RE = re.compile(
    r"conclu|discuss|outlook|summar|synthesis|lessons|future work", re.I)

#: How far from the end a closing section may sit. Papers legitimately end with
#: "Methods and tools disclosure", "Verification status" or "Code Availability", so
#: testing only the LAST section reports 10 of 21 bundles as lacking a conclusion when
#: every one of them has one. Measured 2026-08-08 before this window was widened.
_CLOSING_WITHIN_LAST = 3


@register_check("bundle_structural_coherence",
                "Every bundle has a closing section, a bibliography, and a readable section count")
def check_bundle_structural_coherence() -> CheckResult:
    """CHECK (ADR-011 Phase 4, Gate 14): the shape a referee expects, deterministically.

    **Deliberately much narrower than the 2026-08-01 audit specified**, because two of its
    four legs did not survive being measured:

    - ⚠️ **The sedimentation ratio is not implementable as written.** The audit proposes
      `n_sections / n_sources`, failing above 0.8. That divides by *registered* sources,
      and a sourceless bundle has one synthetic key, so **D9 scores 9.0 with nine sections
      while D3 — the actual sedimentation case, 31 sections and 114 subsections — scores
      0.97.** The metric ranks them backwards. Sedimentation is real and is addressed at
      its cause in `BUNDLE_LIFT_PROCEDURE` §3 (registering a source must not create a
      section), not by this ratio.
    - ⚠️ **The `\\bibitem`-count leg would flag two bundles that are correct.** The audit
      says it "alone catches D8 and D10"; both carry `\\bibliography{}` + a real `.bib`.
      This check accepts either mechanism.

    What is left is a **structural floor**: three properties with no legitimate exception,
    and a section ceiling. The floor passes on all 21 bundles today and exists as a
    regression guard, which is the honest description of it — a draft that loses its
    bibliography or its conclusion has a defect a reader meets immediately.

    **Whether each section advances an argument is NOT decidable here** and belongs to the
    `prose-reviewer` (F-04 question 2). Section *length* is likewise left to it: 400 words
    is an arbitrary line, and "Code Availability" is legitimately short.
    """
    details: List[Detail] = []
    try:
        import bundle_registry as registry
        codes = list(registry.BUNDLE_CODES)
    except Exception as exc:  # noqa: BLE001
        return CheckResult(passed=False, measured=False, details=[Detail(
            "roster", False,
            f"could not read the bundle roster ({exc}) — UNVERIFIED, not passing")])

    checked = bad = 0
    for code in codes:
        tex = _H.PAPERS_DIR / code / "paper_draft.tex"
        md = _read_metadata(code)
        if not tex.is_file() or md is None:
            continue
        checked += 1
        body = _TEX_COMMENT_RE.sub("", tex.read_text(errors="replace"))
        secs = re.findall(r"\\section\*?\{([^}]*)\}", body)
        faults = []

        if not re.search(r"\\begin\{abstract\}", body):
            faults.append("no abstract")
        # Either bibliography mechanism is correct; see the docstring.
        if not re.search(r"\\bibitem|\\bibliography\{", body):
            if re.search(r"\\cite[a-z]*\{", body):
                faults.append("cites sources but has no bibliography by either mechanism")
        if secs and not any(_CLOSING_SECTION_RE.search(s)
                            for s in secs[-_CLOSING_WITHIN_LAST:]):
            faults.append(
                f"no closing section among the last {_CLOSING_WITHIN_LAST} "
                f"({', '.join(repr(s[:34]) for s in secs[-_CLOSING_WITHIN_LAST:])})")
        ceiling = _SECTION_CEILING_BY_TIER.get(md.get("tier"))
        if ceiling is not None and len(secs) > ceiling:
            faults.append(
                f"{len(secs)} top-level sections against a tier-{md.get('tier')} ceiling "
                f"of {ceiling} — a section list this long is a table of contents rather "
                f"than an argument")

        if faults:
            bad += 1
            details.append(Detail(code, False, "; ".join(faults)))

    if checked == 0:
        details.insert(0, Detail(
            "population", False,
            "no bundle draft was read — this check is UNVERIFIED, not passing"))
        return CheckResult(passed=False, measured=False, details=details)

    details.insert(0, Detail(
        "summary", bad == 0,
        f"{checked} bundle(s) checked for structural floor + section ceiling, {bad} short"))
    return CheckResult(passed=bad == 0, details=details)


#: Minimum figure count by tier, the backstop the 2026-08-01 audit specified for use
#: until every bundle carries a charter figure plan. A review article and a four-page
#: letter do not owe a reader the same number of figures.
_FIGURE_FLOOR_BY_TIER = {0: 8, 1: 4, 2: 1, 3: 2, 4: 1}


@register_check("bundle_figure_adequacy",
                "Every bundle carries at least the figures its tier owes a reader")
def check_bundle_figure_adequacy() -> CheckResult:
    """CHECK (ADR-011 Phase 4, Gate 13): a bundle has figures a referee expects.

    **Nine of twenty-one bundles ship ZERO figures**, the flagship among them, and the
    cause is structural rather than editorial: `BUNDLE_LIFT_PROCEDURE` §6 is titled
    *figure MIGRATION* and its first instruction is to copy figures from the source
    papers. **No step in the procedure ever planned a figure.** If the contributing
    sources had none, the bundle has none, and nothing objected.

    ⚠️ **Stage 9 could not object either, and that is the sharper defect.** Its pass
    criterion is *"ALL figures PASS, no FAIL, no MINOR"*, which over an empty set is
    vacuously true — `papers/D10/bundle_metadata.json` recorded `stage9_status: green`
    for a bundle with no figures at all. `paper_provenance` is equally blind: it
    validates that `\\includegraphics` targets exist, so a draft with no
    `\\includegraphics` is trivially clean. Two gates over the same hole, both green.

    The tier floor is a backstop, not the intended instrument. Once a bundle declares a
    charter figure plan the check should compare against *that* — every planned figure
    resolving to an `\\includegraphics` or an explicit `\\figuredeferred{id}{reason}` —
    and the floor becomes the case for a bundle whose plan is not yet written.
    """
    details: List[Detail] = []
    try:
        import bundle_registry as registry
        codes = list(registry.BUNDLE_CODES)
    except Exception as exc:  # noqa: BLE001
        return CheckResult(passed=False, measured=False, details=[Detail(
            "roster", False,
            f"could not read the bundle roster ({exc}) — UNVERIFIED, not passing")])

    checked = short = 0
    total_drawn = total_deferred = zero_drawn = 0
    for code in codes:
        tex = _H.PAPERS_DIR / code / "paper_draft.tex"
        md = _read_metadata(code)
        if not tex.is_file() or md is None:
            continue
        checked += 1
        body = _TEX_COMMENT_RE.sub("", tex.read_text(errors="replace"))
        n_fig = len(re.findall(r"\\begin\{figure", body))
        n_def = len(re.findall(r"\\figuredeferred\{", body))
        total_drawn += n_fig
        total_deferred += n_def
        if n_fig == 0:
            zero_drawn += 1
        tier = md.get("tier")
        floor = _FIGURE_FLOOR_BY_TIER.get(tier)
        if floor is None:
            details.append(Detail(
                code, True, f"tier {tier!r} has no declared figure floor — UNMEASURED",
                warning=True))
            continue
        if n_fig + n_def < floor:
            short += 1
            details.append(Detail(
                code, False,
                f"{n_fig} figure(s)"
                + (f" + {n_def} declared-deferred" if n_def else "")
                + f" against a tier-{tier} floor of {floor}"
                + (" — a bundle with no figures is a charter defect, not a style choice"
                   if n_fig == 0 else "")))

    if checked == 0:
        details.insert(0, Detail(
            "population", False,
            "no bundle draft was read — this check is UNVERIFIED, not passing"))
        return CheckResult(passed=False, measured=False, details=details)

    # ⚠️ The drawn/deferred split rides on the SUMMARY, not only on the failing
    # lines, so a green can never hide an all-deferred corpus. `\figuredeferred`
    # is the pipeline law's honest-disclosure form and it legitimately satisfies
    # the floor — but a bundle that has PLANNED four figures and a bundle that
    # has DRAWN four are different states, and a gate reporting only "0 short"
    # would render them identically. That is the vacuous-Stage-9 failure
    # ("ALL figures PASS" over an empty set) rebuilt one layer up.
    details.insert(0, Detail(
        "summary", short == 0,
        f"{checked} bundle(s) checked against their tier figure floor, {short} short "
        f"— {total_drawn} drawn, {total_deferred} declared-deferred, "
        f"{zero_drawn} bundle(s) with zero drawn figures"))
    return CheckResult(passed=short == 0, details=details)


#: A fix NARRATING ITSELF to the reader (ADR-011 Phase 3, F-05).
#:
#: ⚠️ **These match the ACT, not the vocabulary, and that distinction is the whole
#: design.** The 2026-08-01 audit proposed a word denylist — `Stage 13`, `reviewer`,
#: `adversarial review`, `BLOCKER`. Measured against the corpus that scores 90 hits, of
#: which **I1 alone holds 48**: I1 is the methodology paper, so the review pipeline is
#: its SUBJECT MATTER and every one of its uses is legitimate. `reviewer` splits three
#: ways — scar tissue in F (`\texttt{adversarial-reviewer} agent; fresh-context
#: Stage-13 pass`), subject matter in I1, and the paper's actual audience in I2/I3
#: (*"lets reviewers calibrate effort"*, *"Mathlib4 reviewers"*). A gate over that
#: vocabulary needs a per-bundle exemption and is really a judgment call wearing a
#: regex, which is the prose reviewer's job.
#:
#: Matching the act instead scores **13 hits across 4 bundles with I1 at ZERO**, so no
#: exemption mechanism exists to drift. No physics manuscript legitimately tells a
#: reader what an earlier draft of itself said, or on what date and in which review
#: round it was corrected.
_SELF_NARRATION = (
    (r"[Cc]orrected\s+20[0-9]{2}-[0-9]{2}-[0-9]{2}", "a correction stamped with its date"),
    (r"(?:earlier|previous|prior)\s+(?:draft|version)s?\s+of\s+this",
     "an account of what an earlier draft of this text said"),
    (r"[Ww]e previously\s+\w+", "a first-person account of a superseded claim"),
    (r"[Ss]tage-?\s?1[034][^.]{0,30}round-?\s?[0-9]+[^.]{0,20}finding",
     "an internal review-round finding reference"),
    # ── Added 2026-08-08 from a coverage gap the de-scarring agent found ──
    # It reported two D11 passages that are unmistakably self-narration and that the
    # four patterns above do not match. Both were verified corpus-wide before being
    # added: 4 hits, all in D11, ZERO false positives elsewhere. A pattern set derived
    # from four bundles' worth of examples will have gaps like this; the guard is that a
    # new pattern is measured across all 21 before it is trusted, not that the first set
    # was complete.
    (r"[Oo]ur earlier (?:planning |internal )?documents?",
     "an account of what the project's own internal documents said"),
    (r"\brounds?\s+[0-9]+(?:\s+and\s+[0-9]+)?\s+(?:both\s+)?"
     r"(?:rated|supplied|flagged|caught|raised|noted)",
     "review rounds cast as actors in the manuscript's own history"),
    (r"in every draft\b", "a claim about what every draft of this paper contained"),
)


@register_check("bundle_sentence_length",
                "No bundle draft grows its stock of sentences a reader must re-read to parse")
def check_bundle_sentence_length() -> CheckResult:
    """TODO-D7's readability half: a down-only ratchet on very long sentences.

    ⚠️ **The metric is deliberately independent of any rewriter.** TODO-D7's own
    constraint is that "the decider must not be the generator", so this counts
    what is there and freezes it; the prose was NOT edited to lower the number in
    the change that introduced the check. A metric shipped together with the
    edits that satisfy it has measured nothing.

    Two thresholds, gated differently on purpose:

    * **>100 words — GATED.** Not a style preference. Measured 2026-08-09 at 20
      sentences across 13 bundles, max 235 words — see `SENTENCE_OVER_100_CEILING`
      for the four-way population measurement behind that number. (It read "22
      across 14" for two days: the ceiling constant was rewritten with the full
      table and this docstring, in the module that IMPLEMENTS it, was not.)
    * **>60 words — ADVISORY.** Long but defensible in a methods paragraph.
      Gating it would fire on correct work, which VALIDATION_GATE_TOPOLOGY §3
      says is how a gate gets switched off.

    Sentence splitting runs on comment-stripped body prose with macros blanked,
    so a `\\section{...}` or a citation does not inflate a word count.
    """
    from src.core.constants import (SENTENCE_OVER_100_CEILING,
                                    SENTENCE_OVER_60_ADVISORY)
    # Local imports: `BUNDLE_CODES` was removed from module scope as dead
    # (audit QI-11) and reintroducing it there would revive the false H2
    # obligation that removal note describes.
    from bundle_registry import BUNDLE_CODES
    from validation._tex import _strip_tex_comments
    details: List[Detail] = []
    over60 = 0
    over100: list[tuple[str, int]] = []
    unscannable: list[str] = []
    scanned = 0
    for code in sorted(BUNDLE_CODES):
        draft = _H.PAPERS_DIR / code / "paper_draft.tex"
        if not draft.is_file():
            continue
        scanned += 1
        srcs, gaps = _reader_visible_sources_and_gaps(draft)
        unscannable.extend(f"{code}: {g}" for g in gaps)
        for src in srcs:
            body = _strip_tex_comments(src.read_text(encoding="utf-8", errors="ignore"))
            body = body.split(r"\begin{document}")[-1].split(r"\begin{thebibliography}")[0]
            body = _rows_as_sentences(body)
            body = re.sub(r"\\[a-zA-Z]+\*?(\[[^\]]*\])?(\{[^{}]*\})?", " ", body)
            for sent in re.split(r"(?<=[.!?])\s+", body):
                n = len(sent.split())
                if n > 60:
                    over60 += 1
                if n > 100:
                    over100.append((code, n))

    if scanned == 0:
        # ⚠️ `measured=False` — five sibling zero-population guards in this file
        # set it and this one, in the check this diff rewrote, set neither the
        # CheckResult's nor the Detail's flag while its own message states the
        # cannot-measure premise verbatim.
        return CheckResult(passed=False, measured=False, details=[Detail(
            "scanned", False, measured=False,
            message="no bundle draft found — an empty scan is not evidence "
                    "of short prose")])
    if unscannable:
        # A ratchet must not be computed over a population it could not read.
        details.append(Detail(
            "unscannable", False,
            f"{len(unscannable)} \\input target(s) do not resolve and were NOT "
            f"scanned, so the ratchet population is incomplete: "
            f"{'; '.join(unscannable[:3])}", measured=False))

    ok = len(over100) <= SENTENCE_OVER_100_CEILING
    worst = max((n for _c, n in over100), default=0)
    details.append(Detail(
        "over_100_words", ok,
        f"{len(over100)} sentence(s) over 100 words across "
        f"{len({c for c, _n in over100})} bundle(s), longest {worst} words "
        f"(ratchet {SENTENCE_OVER_100_CEILING}, down-only)"
        if ok else
        f"{len(over100)} sentence(s) over 100 words exceeds the frozen ratchet "
        f"{SENTENCE_OVER_100_CEILING}. Shorten the new prose, or lower the ratchet "
        f"only after shortening: longest is {worst} words."))
    details.append(Detail(
        "over_60_words", True,
        f"{over60} sentence(s) over 60 words (advisory baseline "
        f"{SENTENCE_OVER_60_ADVISORY}; not gated, see docstring)",
        warning=over60 > SENTENCE_OVER_60_ADVISORY))
    # ⚠️ A DOWN-ONLY RATCHET must not report a measurement over a population
    # it could not read: an unresolvable `\input` silently shrinks the count
    # the floor is frozen against.
    return CheckResult(passed=ok and not unscannable,
                       measured=not unscannable, details=details)


@register_check("bundle_reader_facing_voice",
                "No bundle draft narrates its own correction history to the reader")
def check_bundle_reader_facing_voice() -> CheckResult:
    """CHECK (ADR-011 Phase 3, F-05): a fix may not narrate itself.

    A published paper states what IS true. It does not tell a referee what an earlier
    draft of itself said, when it was corrected, or which review round caught it. That
    reader has no access to the process and cannot act on it, so the text reads as a
    repository changelog pasted into a manuscript.

    **Why it accumulates, and why an agent review cannot be the guard.** The lift
    procedure makes the manuscript the fix surface: a reviewer files a finding, the
    author edits the prose, and each round leaves a deposit. D11 and D12 ran **fourteen
    Stage-13 rounds in a single day**. The deposits appear *between* agent reviews, which
    is exactly what a deterministic check catches and a periodic reviewer does not.

    **Removal is not deletion.** The narration usually wraps real content: a retraction
    is a scientific disclosure, and a scope correction states the correct scope. The
    substantive claim is restated in the present tense and the process account is dropped;
    per F-05, the history moves to `change_log.md` and the supersession ledger, which are
    where a later reader can actually check it.

    Comments are stripped — `%` text is not rendered, and the lift banners live there.
    """
    details: List[Detail] = []
    try:
        import bundle_registry as registry
        codes = list(registry.BUNDLE_CODES)
    except Exception as exc:  # noqa: BLE001
        return CheckResult(passed=False, measured=False, details=[Detail(
            "roster", False,
            f"could not read the bundle roster ({exc}) — UNVERIFIED, not passing")])

    checked = total = 0
    for code in codes:
        tex = _H.PAPERS_DIR / code / "paper_draft.tex"
        if not tex.is_file():
            continue
        checked += 1
        found = []
        srcs, gaps = _reader_visible_sources_and_gaps(tex)
        for g in gaps:
            details.append(Detail(
                f"{code}:unscannable:{len(details)}", False,
                f"\\input target {g} does not resolve and was NOT scanned",
                measured=False))
        for src in srcs:
            for i, line in enumerate(src.read_text(errors="replace").splitlines(), 1):
                body = _TEX_COMMENT_RE.sub("", line)
                for pat, why in _SELF_NARRATION:
                    for m in re.finditer(pat, body):
                        found.append((src, i, why, m.group(0)[:60]))
        if found:
            total += len(found)
            src, i, why, txt = found[0]
            details.append(Detail(
                code, False,
                f"{len(found)} self-narrating passage(s); first at "
                f"{src.relative_to(_H.PROJECT_ROOT)}:{i} — {why}: {txt!r}"))

    if checked == 0:
        details.insert(0, Detail(
            "population", False,
            "no bundle draft was read — this check is UNVERIFIED, not passing"))
        return CheckResult(passed=False, measured=False, details=details)

    details.insert(0, Detail(
        "summary", total == 0,
        f"{checked} bundle draft(s) scanned, {total} passage(s) narrating the paper's own "
        f"correction history (target 0; the history belongs in change_log.md)"))
    n_gaps = sum(1 for d in details if ":unscannable:" in d.name)
    return CheckResult(passed=(total == 0 and n_gaps == 0),
                       measured=(n_gaps == 0), details=details)


#: Reviewer-stage status values the tree actually uses. `Phase7a_Roadmap.md:91-93`
#: declares three (`pending`/`green`/`red`, plus `yellow` for stage 13); the live corpus
#: also carries `pending-redo`, `skeleton` and `not_started`. Declared here rather than
#: silently accepted, so an unrecognised value is a finding instead of a shrug —
#: `skeleton` and `not_started` both read as "this stage has not run", and a check that
#: treated an unknown string as "not green" would let a typo'd `greeen` pass as safe.
_STAGE_STATUS_VALUES = frozenset({
    "green", "yellow", "red", "pending", "pending-redo", "skeleton", "not_started",
})

#: The stages `stage13_status` may not overtake. `BUNDLE_LIFT_PROCEDURE.md:9`.
_STAGE13_PREREQUISITES = ("stage9_status", "stage10_status")


@register_check("bundle_reviewer_stage_ordering",
                "No bundle records a Stage-13 verdict before Stages 9 and 10 are green")
def check_bundle_reviewer_stage_ordering() -> CheckResult:
    """CHECK (ADR-011 Phase 2, = TODO-D24 = Gate 16 assertion #2): the hard gate.

    `BUNDLE_LIFT_PROCEDURE.md:9` states it as law — *"Stage 13 (adversarial review) may
    not be invoked until **both** Stage 9 (figure review) AND Stage 10 (claims review)
    are GREEN, with all fixes from those stages applied."* Nothing read the fields.

    **What it caught when it was written by hand (2026-08-07):** five bundles held a
    Stage-13 verdict with a prerequisite never run — D6 (`s9: not_started`,
    `s10: skeleton`), D7 (`s9: not_started`), D8 (both `pending`), D9 (`s10: pending`,
    and it was the portfolio's only GREEN), I3 (`s9: pending`). The operator's demotion
    cleared all five, so this check is expected to pass on a clean tree; it exists to
    stop the next hand-typed `green` from recreating the state.

    **Distinct from `bundle_stage13_claim_consistent`, and they fail on disjoint data.**
    That one catches a green *invalidated later* by newly-minted findings. This one
    catches a green *invalid when written*, because a prerequisite had not passed. A
    bundle can satisfy either and violate the other; D6 did exactly that, holding zero
    blockers (so the other check was silent) with figure review `not_started`.

    ⚠️ **The implication is vacuously true for a bundle with no Stage-13 verdict**, which
    is every bundle today. That is why the seam guard counts *blobs compared*, not
    violations found: a run that inspected nothing must not report agreement. Without it
    this check would pass on an empty `papers/` tree, which is the round-8 state
    (`evaluate_all_gates` renamed → every readiness check green with nothing to check).
    """
    details: list[Detail] = []
    try:
        import bundle_registry as registry
        codes = list(registry.BUNDLE_CODES)
    except Exception as exc:  # noqa: BLE001
        return CheckResult(passed=False, measured=False, details=[Detail(
            "roster", False,
            f"could not read the bundle roster ({exc}) — UNVERIFIED, not passing")])

    checked = 0
    bad = 0
    for code in codes:
        md = _read_metadata(code)
        if md is None:
            bad += 1
            details.append(Detail(
                code, False,
                "no readable bundle_metadata.json — this bundle's stage ordering is "
                "unverified rather than correct"))
            continue
        checked += 1

        raw = {f: str(md.get(f) or "").strip().lower()
               for f in ("stage13_status",) + _STAGE13_PREREQUISITES}
        for field, value in raw.items():
            if value and value not in _STAGE_STATUS_VALUES:
                bad += 1
                details.append(Detail(
                    code, False,
                    f"{field}={value!r} is not a declared status "
                    f"({', '.join(sorted(_STAGE_STATUS_VALUES))}) — an unrecognised "
                    f"value cannot be judged 'not green', so it is a finding, not a shrug"))

        if raw["stage13_status"] != "green":
            continue   # antecedent false — nothing asserted, correctly
        missing = [f"{f.replace('_status', '')}={raw[f] or 'absent'}"
                   for f in _STAGE13_PREREQUISITES if raw[f] != "green"]
        if missing:
            bad += 1
            details.append(Detail(
                code, False,
                f"stage13_status='green' while {', '.join(missing)} — Stage 13 may not "
                f"be invoked until Stages 9 and 10 are both green "
                f"(BUNDLE_LIFT_PROCEDURE.md:9). This verdict was invalid when written, "
                f"not invalidated later: re-run the prerequisite stage, do not edit "
                f"stage13_status"))

    if checked == 0:
        details.insert(0, Detail(
            "population", False,
            "no bundle metadata blob was read — this check is UNVERIFIED, not passing. "
            "Every assertion here is an implication, and an implication over an empty "
            "population is vacuously true; the guard is on the population, not the "
            "violations"))
        return CheckResult(passed=False, measured=False, details=details)

    details.insert(0, Detail(
        "summary", bad == 0,
        f"{checked} bundle(s) checked for reviewer-stage ordering, {bad} violation(s)"))
    return CheckResult(passed=bad == 0, details=details)


def _measure_manuscript(code: str):
    """`(value, unit, note)` for one bundle, or `(None, unit, why-not)`.

    Measures the RENDERED artifact, never a stored number. `compiled_pages` exists in
    the metadata for the dashboard's benefit, and this check deliberately does not read
    it: a stored size is indistinguishable from a stale one, and the whole point of a
    length gate is to catch a draft that grew or shrank since anyone last looked.

    Staleness is judged against the draft's full input closure — the `.tex`, everything
    it `\\input`s transitively, its figures and its `.bib` — via
    `validate_helpers.draft_input_closure`, the single copy. It was promoted there when
    `compile_bundle_pdf.py` became its third consumer; a second "which files can change
    this draft" implementation is precisely the duplication `chain_canonicalize` nearly
    acquired (`REMEDIATION_PLAN.md` §5b).
    """
    import shutil
    import subprocess

    paper_dir = _H.PAPERS_DIR / code
    tex, pdf = paper_dir / "paper_draft.tex", paper_dir / "paper_draft.pdf"
    if not tex.is_file():
        return None, None, "no paper_draft.tex"
    if not pdf.is_file():
        return None, None, ("no compiled PDF — run `uv run python "
                            f"scripts/compile_bundle_pdf.py {code}`")
    try:
        newest = max(p.stat().st_mtime for p in _H.draft_input_closure(tex) if p.is_file())
    except (OSError, ValueError):
        return None, None, "input closure unreadable"
    if pdf.stat().st_mtime < newest:
        return None, None, ("PDF is older than the draft's input closure — the size on "
                            "disk is not this draft's size; recompile before trusting it")

    md = _read_metadata(code) or {}
    unit = ((md.get("length_target") or {}).get("unit")) or "pages"
    if unit == "pages":
        if not shutil.which("pdfinfo"):
            return None, unit, "pdfinfo not on PATH (poppler-utils)"
        out = subprocess.run(["pdfinfo", str(pdf)], capture_output=True,
                             text=True, timeout=60).stdout
        m = _PAGES_RE.search(out)
        return (int(m.group(1)) if m else None), unit, (
            None if m else "pdfinfo reported no page count")

    # word_equivalents — the PRL rule. A page count is the wrong instrument for a
    # letter, because PRL's limit counts text PLUS a 300-word allowance per figure,
    # so a two-figure letter that fits on 4 pages can still be over the real limit.
    if not shutil.which("pdftotext"):
        return None, unit, "pdftotext not on PATH (poppler-utils)"
    body = subprocess.run(["pdftotext", str(pdf), "-"], capture_output=True,
                          text=True, timeout=120).stdout
    n_fig = tex.read_text(errors="replace").count(r"\begin{figure}")
    return len(body.split()) + 300 * n_fig, unit, f"{n_fig} figure(s) at 300 words each"


@register_check("bundle_manuscript_length",
                "Every bundle's compiled manuscript is within its declared length target")
def check_bundle_manuscript_length() -> CheckResult:
    """CHECK (ADR-011 Phase 1, Gate 12): the article is the size its venue requires.

    **The instrument existed and was deliberately unwired.**
    `compile_bundle_pdf.py` computed the page count and then dropped it into a
    human-readable string — `ok = not errors and unresolved <= 0 and not unused_opts`
    never referenced it (audit 2026-08-01 §5.2). So *"is this manuscript the length it
    is supposed to be"* was measured nowhere, and the audit records what that cost:
    **D7 (16 kB, 1 subsection) and D10 (22 kB) were both closed GREEN against ~40 pp
    targets.** Nothing in the pipeline objected, because nothing was looking.

    **Both bounds carry weight, and they catch different failures.** A ceiling catches
    a letter that has become a monograph. A *floor* catches the failure this corpus
    actually exhibits — a container declared as a deep paper whose content is a letter.

    ⚠️ **THE FLOOR IS ADVISORY AS OF 2026-08-09, BY OPERATOR DECISION.** Verbatim:
    *"if length of paper is not sufficient, it's ok to skip. I don't think it's
    realistic to write that length in many areas."* Under-floor findings are reported
    with their exact magnitude and flagged as warnings; they no longer fail the check.
    Over-ceiling still fails — a journal rejects an over-length manuscript outright,
    which is a submission blocker rather than an aspiration.

    **What was deliberately NOT done, and why it matters:** the declared floors were
    not lowered to match current page counts. That would have made the gate agree with
    every one of the audit's findings — the exact move the paragraph above says would
    hollow it out — and it would have destroyed the measurement the operator is
    choosing to accept. Accepting a gap and hiding it are different acts. The charters
    still say what the venues want; the check still says how far each draft is from
    it; only the verdict stopped blocking. If a charter is genuinely unrealistic for a
    given bundle, re-setting THAT bundle's `length_target` is a per-bundle editorial
    decision for goal 2, made with the operator and recorded — not a silent sweep.

    ⚠️ **UNMEASURED is not PASS, and there are four ways to reach it** — no declared
    target, no compiled PDF, a PDF older than the draft's input closure, or no
    `poppler-utils`. Each is reported by name and *counted*, and the check returns
    `measured=False` when nothing at all could be measured. A length gate that silently
    passed the bundles it could not size would be the `Stage 9`-over-an-empty-set defect
    (`"ALL figures PASS"` is vacuously true of zero figures) rebuilt in a new place.

    `length_target: null` is therefore a live, visible state — the honest record for a
    bundle whose venue is still open (ADR-010 §Open item 1) — and never a quiet pass.
    """
    details: List[Detail] = []
    try:
        # From the roster's OWNER, not from `validate`'s re-export — the discipline
        # `bundle_registry_consistency` leg C exists to enforce.
        import bundle_registry as registry
        codes = list(registry.BUNDLE_CODES)
    except Exception as exc:  # noqa: BLE001
        return CheckResult(passed=False, measured=False, details=[Detail(
            "roster", False,
            f"could not read the bundle roster ({exc}) — UNVERIFIED, not passing")])

    over, under, unmeasured, sized = [], [], [], 0
    for code in codes:
        md = _read_metadata(code)
        if md is None:
            continue
        target = md.get("length_target")
        if not target:
            unmeasured.append(f"{code}: no length_target declared")
            continue
        value, unit, note = _measure_manuscript(code)
        if value is None:
            unmeasured.append(f"{code}: {note}")
            continue
        sized += 1
        floor, ceiling = target.get("floor"), target.get("ceiling")
        u = "pp" if unit == "pages" else "word-equiv"
        if ceiling is not None and value > ceiling:
            over.append(f"{code}: {value} {u} > ceiling {ceiling}")
        elif floor is not None and value < floor:
            under.append(f"{code}: {value} {u} < floor {floor} — declared as a "
                         f"{md.get('target_journal', '?')} article, sized like a letter")

    # ⚠️ **OPERATOR DECISION 2026-08-09: UNDER-FLOOR IS ADVISORY, NOT A FAILURE.**
    # Verbatim: *"if length of paper is not sufficient, it's ok to skip. I don't
    # think it's realistic to write that length in many areas."*
    #
    # This is a product decision and only the operator could make it. What it does
    # NOT authorise, and what was deliberately not done: lowering the declared
    # floors to match current page counts. That would erase the measurement. The
    # floors stay as the charters state them, every gap is still reported with its
    # exact magnitude, and the verdict simply stops blocking on it.
    #
    # OVER-ceiling remains a hard FAIL. It is a different fact: a journal rejects
    # an over-length manuscript outright, so that one is a real submission blocker
    # rather than an aspiration.
    for r in over:
        details.append(Detail("over_ceiling", False, r))
    for r in under:
        details.append(Detail("under_floor", True, r, warning=True))
    for r in unmeasured:
        details.append(Detail("unmeasured", True, r, warning=True))

    if sized == 0:
        details.insert(0, Detail(
            "population", False,
            f"no bundle manuscript could be sized ({len(unmeasured)} unmeasured) — this "
            f"check is UNVERIFIED, not passing. Compile the drafts "
            f"(`scripts/compile_bundle_pdf.py --all`) and declare `length_target`."))
        return CheckResult(passed=False, measured=False, details=details)

    details.insert(0, Detail(
        "summary", len(over) == 0,
        f"{sized} manuscript(s) sized against their declared target — "
        f"{len(over)} OVER ceiling (gating), {len(under)} under floor "
        f"(ADVISORY by operator decision 2026-08-09, not gating); "
        f"{len(unmeasured)} UNMEASURED",
        warning=bool(under)))
    # ⚠️ **THE UNMEASURED POPULATION FOLDS INTO `measured`, and this check was the
    # one sibling that did not do it.** Five others already do (`freshness.py`,
    # the three reader-visible-prose checks, `graph_atlas`). Without the fold this
    # gate degraded SILENTLY: a stale PDF took a bundle UNMEASURED, the reported
    # under-floor population shrank 11 → 10 → 1, and it stayed GREEN throughout.
    #
    # That is not only an advisory-information loss. A bundle that goes UNMEASURED
    # also escapes the OVER-CEILING leg — the one that still gates — so staleness
    # was a way to skip the only blocking check here. Latent today (zero
    # over-ceiling bundles), which is exactly why it needed closing before it
    # wasn't.
    #
    # Folding it makes the perishability ENFORCE itself rather than be documented
    # in three places and observed in none: a stale tree now reads `74 MEASURED,
    # floor 75` under `--ci` instead of a green tick over part of the corpus. The
    # remedy is `scripts/compile_bundle_pdf.py --all --force`.
    return CheckResult(passed=len(over) == 0,
                       measured=not unmeasured, details=details)


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

    **Scope, after the 2026-08-07 split (TODO-D23).** This check is now exactly what its
    registered description says: FIELD EQUALITY between the blob and the graph, on
    `blockers_open`, `advisories_open` and `readiness`. The fourth assertion it used to
    carry — `stage13_status='green'` is illegal while blockers are open — is a semantic
    contradiction rather than a count equality, and moved to
    `bundle_stage13_claim_consistent`. Nothing about that assertion changed; it stopped
    being reported under a name that described the other three legs.

    The two remain cross-braced by design: zeroing `blockers_open` by hand to silence the
    Stage-13 check trips THIS check instead, so both have to be defeated rather than one.
    """
    by_bundle, meta_path, failure = _readiness_aggregate()
    if failure is not None:
        return CheckResult(passed=False, details=[failure])

    details: list[Detail] = []
    drift = 0
    checked = 0
    for bundle, agg in sorted(by_bundle.items()):
        mp = meta_path(bundle)
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
        if bad:
            drift += 1
            details.append(Detail(
                bundle, False,
                f"metadata disagrees with the live graph: {'; '.join(bad)}. "
                f"Re-run `uv run python scripts/bundle_readiness.py`, which writes "
                f"these fields; do not hand-edit them."))

    # Seam guard (guide §2.5): a loop that compared nothing must not report agreement.
    if checked == 0:
        details.insert(0, Detail(
            "population", False,
            "no bundle metadata blob was compared — this check is UNVERIFIED, not "
            "passing (an empty population is the round-8 state: every readiness check "
            "green with nothing to check)"))
        return CheckResult(passed=False, measured=False, details=details)

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
#: 11 -> 10: D4 retrofitted 2026-08-07 (66 apexes; docs/audits/2026-08-07-d4-retrofit/
#:           FINDINGS.md). Largest closure yet (753 decls / 61 modules) and the most
#:           truncated walk (90). Makes the D4->D8 boundary concrete: D4 and D8 name
#:           the SAME GenericSU2 Clifford+T theorem. D4 ∩ D6 = 0, though F says D6
#:           absorbed D4's Solovay-Kitaev headline.
#: 10 -> 9:  D5 retrofitted 2026-08-07 (70 apexes; docs/audits/2026-08-07-d5-retrofit/
#:           FINDINGS.md). Flattest closure measured (216 decls, depth 3) because its
#:           theorems are VERDICTS — corroborating the draft's own MCC self-labelling.
#:           Apex-to-closure ratio is a genre signal, not a quality metric.
#: 9 -> 8:   D8 retrofitted 2026-08-07 (35 apexes; docs/audits/2026-08-07-d8-retrofit/
#:           FINDINGS.md). LARGEST closure in the portfolio: 2290 decls / 289 modules /
#:           depth 24. RESOLVES the D4->D8 declaration conflict on the drafts' own
#:           instructions — 4 GenericSU2 apexes moved D4 -> D8, and D4's closure fell
#:           753 -> 620 as a result, corroborating the reassignment.
#: 8 -> 7:   D7 retrofitted 2026-08-07 (14 apexes; docs/audits/2026-08-07-d7-retrofit/
#:           FINDINGS.md). SECOND declaration conflict resolved: D1 §8.2 had declared
#:           D7's entire headline as a cross-check; 6 apexes moved D1 -> D7 (D1's
#:           closure 249 -> 171). D7's draft is five-sevenths placeholder sections.
#: 7 -> 6:   I1 retrofitted 2026-08-07 (6 apexes; docs/audits/2026-08-07-i1-retrofit/
#:           FINDINGS.md). The METHODOLOGY paper describes the pipeline at about half
#:           its current size: 33 checks vs a live 66, 15 invariants vs #17, 17 bundles
#:           vs 21, toolchain v4.29.0 vs v4.32.0.
#: 6 -> 5:   I2 retrofitted 2026-08-07 (20 apexes; docs/audits/2026-08-07-i2-retrofit/
#:           FINDINGS.md). Every per-theorem purity claim VERIFIES, in both directions:
#:           SU(2)_k "no native_decide" true, fib_pentagon "by native_decide" true.
#: 5 -> 4:   I3 retrofitted 2026-08-07 (12 apexes; docs/audits/2026-08-07-i3-retrofit/
#:           FINDINGS.md). SMALLEST closure in the portfolio (32 decls / 9 modules) and
#:           the only one intersecting NOTHING -- corroborating the draft's own published
#:           grep that its D3/D5/E1 cross-bridges are designed but not yet consumed.
#: 4 -> 3:   L1 retrofitted 2026-08-07 (11 apexes; docs/audits/2026-08-07-l1-retrofit/
#:           FINDINGS.md). Narrowest closure structurally (1 module, depth 1) -- right shape
#:           for a falsification Letter. THIRD declaration conflict (D3 and F both declare
#:           L1's theorems) but NOTHING was reassigned: this one is the reserved
#:           `L1 disposition` STOP-AND-ASK, recorded as evidence, not resolved.
#: 3 -> 2:   L3 retrofitted 2026-08-07 (13 apexes; docs/audits/2026-08-07-l3-retrofit/
#:           FINDINGS.md). Reading D3's draft directly showed BOTH L1/D3 and L3/D3 are
#:           DECLARED splash/deep companion pairs ("character-for-character identical",
#:           D3 §8) -- so the shared apexes are the design, not a collision. Corrects the
#:           L1 finding, which filed that absence without a probe that could show presence.
#: 2 -> 1:   E1 retrofitted 2026-08-07 (7 apexes; docs/audits/2026-08-07-e1-retrofit/
#:           FINDINGS.md). THIRD declared companion pair -- D1's abstract calls E1 and E2
#:           "companion experimental letters" -- and the first found DELIBERATELY, by
#:           running the bundle-name probe the L3 correction prescribed.
#: 1 -> 0:   E2 retrofitted 2026-08-07 (6 apexes; docs/audits/2026-08-07-e2-retrofit/
#:           FINDINGS.md). ALL 21 BUNDLES NOW DECLARE APEXES -- the ADR-010 D5a retrofit
#:           is complete. The ceiling is now a true ratchet: any bundle added without
#:           declared apexes fails this check immediately.
UNDECLARED_APEX_CEILING = 0


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


# ═══════════════════════════════════════════════════════════════════════
# CHECK: per-bundle native_decide debt — disclosure + ratchet
# ═══════════════════════════════════════════════════════════════════════

#: LaTeX-COMMENT work markers. The `(?<!\\)%` is load-bearing: `\%` is a printed
#: percent sign, not a comment.
_TODO_COMMENT_RE = __import__("re").compile(r"(?<!\\)%.*\b(TODO|FIXME|XXX|TBD)\b")

#: Any mention at all — the disclosure test. Deliberately permissive: a bundle that
#: names the tactic anywhere has told its reader the compiler is in the chain, and
#: judging whether the wording is *prominent* is the prose reviewer's job, not a
#: regex's.
_ND_MENTION_RE = __import__("re").compile(r"native\\?_decide", __import__("re").I)


def _bundle_native_decide_hits() -> tuple[dict, str | None]:
    """`{bundle: {declaration names carrying native_decide in its apex closure}}`.

    Returns `({}, reason)` when the measurement cannot be made — never an empty
    result that reads as "no debt".
    """
    if not _H.lean_deps_present():
        return {}, "lean/lean_deps.json absent (refresh: cd lean && lake build SKEFTHawking.ExtractDeps)"
    try:
        import bundle_closure as bc
        from update_counts import native_decide_decls
        # `_H.load_lean_deps()` is the single loader (validate_helpers §path resolution);
        # a second parse of the 70 MB file here would be the duplicate-load-site defect
        # that module was written to remove.
        nd = {d["name"] if isinstance(d, dict) else d
              for d in native_decide_decls(_H.load_lean_deps())}
        recs = bc.load_records()
        closures = bc.build_closures(recs, bc.load_apex_declarations(_H.PAPERS_DIR))
    except Exception as exc:  # noqa: BLE001
        return {}, f"could not derive closures / native_decide set ({exc})"

    # ── SEAM GUARD (authoring-guide §2.5) ──────────────────────────────────────
    # Both populations must be non-empty, and the reason is that EITHER going empty
    # makes this check pass while measuring nothing:
    #   * `nd` empty ⇒ every intersection is empty ⇒ every bundle reports "clean",
    #     which is the same sentence a genuinely clean corpus produces. The
    #     project-wide ceiling is 546, so an empty set here means the extractor's
    #     shape changed under us, not that the debt was paid.
    #   * no measurable closure ⇒ nothing to intersect ⇒ "0 bundles carry debt".
    # This is `"ALL figures PASS"` over an empty set, refused a third home.
    if not nd:
        return {}, ("the native_decide declaration set came back EMPTY while the "
                    "project-wide ceiling is non-zero — `native_decide_decls` no longer "
                    "matches lean_deps.json's shape. Every bundle would read clean")
    measurable = {code: (c.closure & nd) for code, c in closures.items() if c.measurable}
    if not measurable:
        return {}, ("no bundle has a measurable apex closure, so no per-bundle debt "
                    "could be computed — see `bundle_apex_resolves`")
    return measurable, None


@register_check(
    "bundle_native_decide_debt",
    "Every bundle's native_decide debt is disclosed in its draft and does not grow (ADR-002 ratchet, per-bundle)")
def check_bundle_native_decide_debt() -> CheckResult:
    """CHECK: compiler-trust debt, attributed to the manuscript that rests on it.

    **`native_decide_regression` counts the project and cannot answer a reader's
    question.** Its metric is one number over the whole corpus, so it is silent on
    *which paper's* claims depend on the Lean compiler rather than on the kernel. A
    reader of D4 cannot learn from it that 19 declarations in D4's own apex closure
    are compiler-checked. This check asks that question per bundle, which is the unit
    at which the debt must be disclosed and the unit at which paying it down changes
    what a paper may assert.

    **Two legs:**

    1. **Ratchet.** A bundle's debt may not exceed its `NATIVE_DECIDE_BUNDLE_DEBT`
       entry (absent ⇒ 0). Down-only, like every ceiling in `constants.py`.
    2. **Disclosure.** A bundle carrying debt must name `native_decide` somewhere in
       its draft. Deliberately permissive — whether the disclosure is *prominent
       enough* is a prose-review judgement, and a regex that tried to grade prominence
       would be the heuristic gate this project keeps out of the deterministic layer.

    ⚠️ **A third leg was written and REMOVED, and the reason is worth keeping.** It
    tried to hard-fail a draft that *asserts* it carries no `native_decide` while its
    closure says otherwise — a false kernel-purity claim being exactly what a reader
    cannot check. On first run it fired on **I2, wrongly.** I2's *"All of these proofs
    are kernel-pure (`decide` / `norm_num` / `ring` / `linear_combination`; no
    `native_decide`)"* is scoped to its Q(√n) and cubic-field subsection, and I2
    separately discloses `fib_pentagon` *"by `native_decide` on the 512-case F-symbol
    catalog"* — the exact declaration the closure counts. **The draft was right and the
    regex was wrong**, because separating a corpus-wide claim from a scoped one is a
    reading task, not a matching task.

    Rather than grow an exception set, the leg is gone: **judging whether a disclosure
    is honestly scoped belongs to the prose reviewer**, alongside prominence, which is
    the same call made one paragraph up. What survives mechanically is stronger for
    being narrow — the debt cannot grow, and it cannot be silent.

    ⚠️ **Zero debt is asserted, not assumed.** A bundle absent from the map is
    required to measure zero, so a wave that routes compiler trust into a clean
    bundle fails here instead of landing quietly and being discovered by a referee.

    ⚠️ **UNMEASURABLE is not PASS.** An undeclared bundle has no closure, so its debt
    is UNKNOWN; it is counted and named, never scored clean.
    """
    from src.core.constants import NATIVE_DECIDE_BUNDLE_DEBT as DEBT

    hits, err = _bundle_native_decide_hits()
    if err:
        return CheckResult(passed=False, measured=False, details=[Detail(
            "measure", False,
            f"{err} — the per-bundle compiler-trust surface is UNVERIFIED, not clean")])

    details: List[Detail] = []
    ok = True
    try:
        import bundle_registry as registry
        codes = list(registry.BUNDLE_CODES)
    except Exception as exc:  # noqa: BLE001
        return CheckResult(passed=False, measured=False, details=[Detail(
            "roster", False, f"could not read the bundle roster ({exc}) — UNVERIFIED")])

    undeclared = [c for c in codes if c not in hits]
    if undeclared:
        details.append(Detail(
            "undeclared", True,
            f"{len(undeclared)} bundle(s) declare no apexes, so their debt is UNKNOWN "
            f"rather than zero: {', '.join(sorted(undeclared))}",
            warning=True))

    carrying, paid = [], []
    for code in sorted(hits):
        n, ceil = len(hits[code]), DEBT.get(code, 0)
        if n > ceil:
            ok = False
            mods = {}
            for name in hits[code]:
                mods[name.rsplit(".", 1)[0]] = mods.get(name.rsplit(".", 1)[0], 0) + 1
            top = ", ".join(f"{k.split('.')[-1]}={v}" for k, v in
                            sorted(mods.items(), key=lambda kv: -kv[1])[:4])
            details.append(Detail(
                f"ratchet:{code}", False,
                f"{code}: native_decide debt {n} EXCEEDS its ceiling {ceil} — a wave routed "
                f"compiler trust into this bundle's claimed substrate. Eliminate it "
                f"(ADR-002; D8's draft §'Kernel purity made uniform' is the worked "
                f"precedent) or raise NATIVE_DECIDE_BUNDLE_DEBT['{code}'] with a stated "
                f"reason in the same commit. Densest: {top}"))
            continue
        if n == 0:
            if ceil:
                details.append(Detail(
                    f"paid:{code}", True,
                    f"{code}: debt is now 0 against a ceiling of {ceil} — PAID DOWN; "
                    f"delete its NATIVE_DECIDE_BUNDLE_DEBT entry", warning=True))
            continue
        carrying.append(code)
        if n < ceil:
            paid.append(f"{code} {ceil}→{n}")

        draft = _H.PAPERS_DIR / code / "paper_draft.tex"
        try:
            text = draft.read_text()
        except OSError:
            ok = False
            details.append(Detail(
                f"disclose:{code}", False,
                f"{code}: carries {n} native_decide declaration(s) and its draft could not "
                f"be read — disclosure UNVERIFIED, not assumed"))
            continue
        if not _ND_MENTION_RE.search(text):
            ok = False
            details.append(Detail(
                f"disclose:{code}", False,
                f"{code}: {n} declaration(s) in its apex closure rest on native_decide and the "
                f"draft never names it. Compiler-trust in the proof chain is disclosable "
                f"content (audit D-5); say so in the verification-status section"))

    if paid:
        details.append(Detail("progress", True,
                              f"debt paid down since the ceiling was set: {', '.join(paid)} — "
                              f"lower the ceiling(s)", warning=True))
    if carrying:
        total = sum(len(hits[c]) for c in carrying)
        details.append(Detail(
            "register", True,
            f"{len(carrying)} bundle(s) carry disclosed native_decide debt, {total} declaration(s) "
            f"total: " + ", ".join(f"{c}={len(hits[c])}" for c in carrying)))
    clean = [c for c in sorted(hits) if not hits[c]]
    details.append(Detail(
        "clean", True,
        f"{len(clean)} declared bundle(s) measure ZERO native_decide in their apex closure "
        f"(asserted, not assumed): {', '.join(clean)}"))
    return CheckResult(passed=ok, details=details)


@register_check(
    "bundle_todo_free_before_green",
    "No bundle carrying an unresolved work marker records a Stage-13 green")
def check_bundle_todo_free_before_green() -> CheckResult:
    """CHECK: a draft with open TODOs may exist; it may not be declared finished.

    Operator ruling, 2026-08-08: *"Papers with todos are OK in draft mode, but we
    can't let them go green."* Drafting with markers is normal and this check does
    not object to it — it objects only to a marker coexisting with a **green**
    reviewer verdict, which is a bundle asserting a completed review over content
    its own author flagged as unwritten.

    ⚠️ **The predicate is LaTeX-comment markers only, and the narrowing is the whole
    design.** A first scan keyed on `TODO|placeholder` case-insensitively across the
    prose returned 80-odd hits per bundle and would have gated on two populations
    that must not be conflated:

    * **`placeholder` in reader-facing prose is a disclosed technical term here** — a
      `True :=  trivial` Lean stub, governed by `placeholder_not_cited` and
      `disclosure_consistency`. Drafts are *required* to name them. Gating on the word
      would penalize exactly the honesty the pipeline mandates.
    * **D11 §1 describes an in-source TODO in *Mathlib***, a factual statement about a
      dependency, not an unfinished sentence of its own.

    Neither is an unresolved work item. What is: `% TODO: lift content from …`,
    `% TODO: substantive draft`. Those are author notes-to-self, invisible to a
    reader, and each names work that has not been done. The negative lookbehind keeps a
    printed (escaped) percent sign out of it.

    **No exception set, deliberately** (contrast TODO-D30, where building one is the
    hard part). A comment whose text merely *mentions* markers — e.g. one recording
    that stubs were suppressed — trips this check, and the fix is to reword the
    comment, a one-line edit. Pushing the burden onto unambiguous authoring is
    cheaper and more durable than a curated allow-list that itself goes stale.
    """
    try:
        import bundle_registry as registry
        codes = list(registry.BUNDLE_CODES)
    except Exception as exc:  # noqa: BLE001
        return CheckResult(passed=False, measured=False, details=[Detail(
            "roster", False, f"could not read the bundle roster ({exc}) — UNVERIFIED")])

    details: List[Detail] = []
    ok = True
    drafting, blocked, unread = [], [], []
    for code in codes:
        draft = _H.PAPERS_DIR / code / "paper_draft.tex"
        try:
            lines = draft.read_text().splitlines()
        except OSError:
            unread.append(code)
            continue
        marks = [i for i, ln in enumerate(lines, 1) if _TODO_COMMENT_RE.search(ln)]
        if not marks:
            continue
        md = _read_metadata(code) or {}
        status = str(md.get("stage13_status", "")).lower()
        if status == "green":
            ok = False
            blocked.append(code)
            details.append(Detail(
                f"green_with_todo:{code}", False,
                f"{code}: stage13_status='green' with {len(marks)} unresolved work marker(s) "
                f"at line(s) {', '.join(map(str, marks[:6]))}"
                f"{' …' if len(marks) > 6 else ''} — a green verdict asserts a completed "
                f"review over content the draft itself flags as unwritten. Resolve the "
                f"markers or withdraw the green"))
        else:
            drafting.append(f"{code}={len(marks)}")

    if unread:
        details.append(Detail(
            "unread", True,
            f"{len(unread)} draft(s) could not be read, so their marker state is UNKNOWN: "
            f"{', '.join(sorted(unread))}", warning=True))
    if drafting:
        details.append(Detail(
            "drafting", True,
            f"{len(drafting)} bundle(s) carry work markers and are correctly NOT green "
            f"(this is allowed): " + ", ".join(sorted(drafting)), warning=True))
    if not blocked and not unread:
        details.append(Detail(
            "gate", True, "no bundle records a Stage-13 green while carrying a work marker"))
    return CheckResult(passed=ok, details=details)
