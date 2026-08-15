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
import bisect
import hashlib
import importlib
import json
import tempfile
from functools import lru_cache
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
        # ⚠️ The prefix set is DERIVED from the bundle roster, not typed.
        # It was hardcoded to ("d11_", "d12_") until 2026-08-11, which meant the
        # gate examined two bundles' figures and silently examined ZERO of every
        # other bundle's -- while still reporting PASS for them. FIGURE_REGISTRY
        # already carried the entries (I1 six, I2 five); only this filter hid
        # them. Deriving the prefixes from BUNDLE_CODES makes a newly-registered
        # bundle figure guarded on arrival, which is the property the surrounding
        # comment already claimed.
        from bundle_registry import BUNDLE_CODES        # single owner of the roster
        _prefixes = tuple(f"{code.lower()}_" for code in BUNDLE_CODES)
        _derived: dict[str, list] = {}
        for fs in _rf.FIGURE_REGISTRY:
            if not fs.name.startswith(_prefixes):
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
                # ⚠️ Must match scripts/review_figures.py's render rule EXACTLY, or
                # drift is unclearable by construction. This was `scale=3`
                # unconditionally while the renderer uses scale=2 for any figure
                # whose declared canvas is >= 1000px wide, so every wide figure
                # reported permanent drift that no regeneration could clear —
                # a warning that cannot be acted on trains readers to ignore it.
                _fw = fig.layout.width or 1200
                _fh = fig.layout.height or 800
                fig.write_image(tmp_path, width=_fw, height=_fh,
                                scale=2 if _fw >= 1000 else 3)
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
    # `CI_MIN_CHECKS_RUN` is 76 with no slack, so a failed `review_figures`
    # FIGURE_REGISTRY load now turns `--ci` red rather than merely warning. That
    # import demonstrably failed on EVERY run for a whole review round (see the
    # comment at the fallback itself) without anyone noticing — which is the
    # argument for the coupling, not against it: a silent fallback to the
    # hand-maintained list this derivation exists to replace should stop the build.
    return CheckResult(passed=n_fail == 0,
                       measured=_SPEC_FALLBACK is None, details=details)


#: Open `major` (REQUIRED) findings per bundle. **A RATCHET: may only shrink.**
#:
#: ⚠️ THIS IS NOT A NEW SEVERITY TIER, and any commit message saying REQUIRED "now blocks"
#: is describing a state that has not existed since 2026-07-31. `readiness_gates.py`'s
#: `BLOCKING_SEVERITIES` already contains `major`; `bundle_readiness.py` already counts it
#: into `n_blockers`; the leg above already forbids a green Stage-13 against that count.
#: REQUIRED already blocks the gate, the readiness verdict AND the green claim.
#:
#: What nothing asserted is that the population cannot GROW — and the consistency leg above
#: fires on zero rows today, because no bundle currently claims `stage13_status: green`. It
#: is a correct guard over an empty population. This ratchet is the growth guard, and it
#: mechanizes PD-5 ("BLOCKER/MAJOR/IMPORTANT are never deferred", operator-set 2026-07-29),
#: which has bound the autonomous loop for two weeks and bound no gate.
#:
#: PD-5 governs the finding you just found: fix it in-session. This governs the population:
#: a new major takes its bundle above ceiling and fails — PD-5 firing mechanically.
#:
#: MEASURED 2026-08-12 through `_readiness_aggregate()`, which is what this check reads.
#: ⚠️ NOT through `meta['inferred_bundle']`: the aggregation attributes via
#: `inferred_paper or inferred_bundle` plus the paper→bundle mapping, so the two populations
#: differ materially (D3 3 vs 6, D5 6 vs 10, F 5 vs 15). Measuring the wrong one makes this
#: leg red on arrival.
def _required_open_ceilings() -> dict[str, int]:
    """Load the frozen per-bundle ceilings (ADR-012 D9).

    ⚠️ DATA, NOT A PYTHON LITERAL, and the reason is a guard firing on my first attempt.
    A 15-code dict in this module tripped `bundle_registry_consistency` Leg C — a
    hand-maintained roster parallel to `scripts/bundle_registry.py`. The per-file
    allowlist would have blinded that gate to this entire module, which is the file most
    likely to re-hardcode a roster, so the ceilings moved to data instead.

    An ABSENT bundle reads 0 — the strictest default. A newly-registered bundle starts
    clean and any open major fails it, so this file cannot go stale by omission.
    """
    path = _H.DOCS_DIR / "required_open_ceilings.json"
    if not path.is_file():
        return {}
    try:
        return dict(json.loads(path.read_text(encoding="utf-8")).get("ceilings", {}))
    except (OSError, json.JSONDecodeError):
        return {}


#: Open blocking-severity findings that the per-bundle aggregation DOES NOT REACH.
#: **A RATCHET: may only shrink.**
#:
#: ⚠️ THIS IS WHAT MAKES THE PER-BUNDLE RATCHET HONEST. A per-bundle ceiling can only see
#: findings that reach the aggregation, and `bundle_readiness.py` drops those carrying
#: neither key before it — silent-drop point 1 in `QA_QI_INFRASTRUCTURE_MAP.md` §3. With
#: only the first ratchet, a finding that LOSES its attribution silently leaves the ratchet,
#: and "no bundle carries an open major" becomes reachable by degrading attribution rather
#: than by fixing anything. That is absence rendered as success, one level up from where
#: this suite usually catches it.
#:
#: MEASURED 2026-08-12: **47** carry neither key. 71 lack `inferred_bundle`, but 24 of those
#: carry `inferred_paper` and DO reach the aggregation, so counting 71 here would
#: double-count what ratchet 1 already covers — a guard that lies about what the other one
#: misses.
#: 2026-08-12: 47 -> 39 after the pilot batch closed 99 findings. Lowered in the same
#: commit that lowered the population, per the ratchet rule.
#:
#: ⚠️ **39 -> 47, and this is a RE-DERIVATION, not a raise.** The predicate changed from
#: "carries neither key" to "the aggregation did not reach it", because the first was a
#: PROXY for the second and was wrong for 8 findings: a finding keyed to a pre-bundle-era
#: paper (ADR-012 D7) has an `inferred_paper`, so the old predicate skipped it, and maps to
#: no bundle, so leg 1 never counted it. Both legs reported green over it.
#:
#: A measurement is scoped by its predicate, and widening the predicate VOIDS the baseline
#: — the same rule that governed leg 1's `major` -> `BLOCKING_SEVERITIES` widening earlier
#: the same day. The new baseline is frozen at the live count under the new predicate and
#: shrinks from there. That 47 equals the pre-pilot figure is a coincidence of two
#: different populations, not a reversion.
#:
#: ⚠️ **47 -> 52, and this one is a RAISE. Operator-authorized 2026-08-12; read the argument
#: before ever reusing it.** ADR-012 P8 re-filed the D45-D49 block out of
#: `ARCHITECTURE_TODOs.MD` — a file with no machine reader — into the queue. Five of the eight
#: minted findings are blocking, and all five are unattributed because a defect in
#: `formulas.py`, `LeviCivita.lean` or `update_counts.py` reaches no bundle. Leg 2 therefore
#: rose by exactly five.
#:
#: The claim is that this is previously-INVISIBLE debt becoming visible, not new debt: every
#: item was written down on **2026-08-11**, before this baseline was frozen on 2026-08-12, and
#: the re-file document re-measures each one at HEAD.
#:
#: ⚠️ **CORRECTED — this justification miscounted its own source.** It read "four of the nine
#: were already fixed and are NOT filed", which is unsatisfiable: eight findings were minted,
#: and 8 + 4 = 12, not 9. Measured against the re-file document: **eleven** sub-items
#: (D45-a..d, D46-a..d, D47, D48, D49), of which **three** are marked fixed-and-not-filed
#: (D45-c, D47, D49) and **eight** were filed. The "four of the nine" phrasing came from the
#: re-file document's own prose, which says "four" and then names three — so the error
#: propagated from there rather than originating here, and both are fixed.
#:
#: The raise itself reproduces exactly and is unaffected: the eight findings carry 1 critical
#: + 4 major = **5 blocking**, and 47 + 5 = 52. A reviewer re-deriving this raise can now
#: reconcile every number in it, which is the entire point of an auditable ceiling change.
#:
#: ⚠️ **THERE IS NO MECHANICAL DISCRIMINATOR BEHIND THAT CLAIM, and pretending otherwise would
#: be worse than the raise.** To this check, five findings recorded a day earlier and five
#: invented this morning are identical — `review_date` is the FILING date, not the discovery
#: date. The only safeguard is the dated record in `ARCHITECTURE_TODOs.MD` and the operator's
#: sign-off on this specific raise. **A future raise justified by pointing at this one is
#: exactly the abuse this note exists to make visible.** The ceiling records a distance that
#: must shrink; ADR-012 P10 is what shrinks it.
#:
#: ⚠️ **52 -> 45, AND THIS IS A RE-DERIVATION FROM AN IMPROVED INSTRUMENT, NOT A RAISE —
#: the number went DOWN and the sibling leg went UP, which is what a displacement looks
#: like.** Until 2026-08-15 the aggregation read a finding's bundle from two regexes over
#: text and never opened the frontmatter, so a document declaring `paper:
#: note_rt_ch_bounds` or `bundle_target: D11` was parsed by neither and its findings
#: reached no bundle. `bundle_readiness.resolve_attribution` now reads the declaration.
#: **Twelve** open blocking findings moved out of this leg and into leg 1, where their own
#: bundles carry them: 57 - 12 = 45, and the 12 fan out to **27** bundle occurrences, so
#: leg 1 goes 12 -> 39. Every number reconciles, because nothing was found and nothing was
#: forgiven — the same findings are now counted where they belong.
#:
#: (The leg-1 endpoints include L3's concurrent redraft, which landed 6 of its 7 blockers
#: visibly to the OLD instrument as well; `docs/required_open_ceilings.json` records why
#: that growth is deliberately NOT absorbed into the frozen per-bundle set. This leg is
#: unaffected by the distinction: it only ever SHRANK.)
#:
#: The test is which of the two changed, the POPULATION or the INSTRUMENT. Here the
#: instrument did: these findings have existed all along and the aggregation could not see
#: them. A ratchet may never be raised to accommodate a population that GREW; it MUST be
#: re-derived when a wider predicate reveals what was always there — the precedent this
#: file already carries twice (`major` -> `BLOCKING_SEVERITIES`, and the neither-key proxy
#: -> what the aggregation actually reached), and the pattern `count_literals` prescribes
#: in its own Fix section: widen the predicate, MEASURE the new population, then sweep it
#: or freeze at the measured value with the jump stated in the same commit. Never widen and
#: quietly raise.
#:
#: ⚠️ **23 of the 45 carry a declaration that does NOT resolve, and they are NOT a residue
#: of the fix — they are what the fix made visible.** Eight are `bundle_target: infra` /
#: `paper: infra` and are correctly unattributable: a defect in `formulas.py` or
#: `update_counts.py` belongs to no publication bundle, and this leg is what bounds them.
#: Narrowing the predicate to exclude them would be reclassification standing in for
#: remediation. The other sixteen — `phase6EE_control` (11) and `phase6EA_substrate` (5,
#: plus 3 in round 2) — declare `paper: phase6EA_substrate` / `paper: phase6EE_control`,
#: which are not `PAPER_DRAFT_MAPPING` keys and not bundle codes, so they resolve to
#: nothing BY CONSTRUCTION. `phase6EA_substrate` names D12 only inside a free-prose
#: `scope:` sentence, and `phase6EE_control` names no bundle at all; reading either would
#: be a regex over prose, which is the channel this fix exists to remove. The remedy is for
#: those documents to DECLARE `bundle_target: D12`, at which point this leg drops by 19
#: without a line of code changing — which is the point of asserting the decider.
#:
#: ⚠️ **45 -> 44: the closure of the attribution finding itself.** `infra:1.1` of
#: `2026-08-15-declared-attribution-unread-by-the-aggregation` was one of the 45 — it
#: declares `bundle_target: infra` and so belongs to this leg by construction — and it
#: is fixed by the change it describes. Lowered in the commit that records the closure,
#: per the ratchet rule; a ceiling left standing above a corpus that improved is
#: headroom, and headroom makes a ratchet unfireable.
UNATTRIBUTED_OPEN_BLOCKING_CEILING: int = 44


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
            "import", False, measured=False,
            message=f"could not import the readiness machinery ({exc}) — this check is "
                    f"UNVERIFIED, not passing")
    try:
        by_bundle = aggregate_by_bundle(
            parse_mapping(MAPPING_DOC.read_text()),
            load_findings_by_paper(),
            resolve_stage13_reviews(backfill=False))
    except Exception as exc:
        # FAIL, not pass: an uncomputable live verdict is not agreement.
        return None, None, Detail(
            "aggregate", False, measured=False,
            message=f"live counts could not be computed ({type(exc).__name__}: {exc}) "
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

    # ── The finding population both ratchets measure ──────────────────────────────
    # ⚠️ SEAM GUARD FIRST (guide §2.5). `checked` counts metadata BLOBS, not findings, so
    # it stays at 21 while the finding corpus reads zero — and both ratchets then report
    # "0, none above ceiling" over nothing. That is the round-8 state exactly: every
    # readiness check green with nothing to check. Both sit at zero headroom, so the
    # vacuous path is the ONLY way they can silently go green.
    try:
        import sys as _sys
        _sys.path.insert(0, str(_H.PROJECT_ROOT / "scripts"))
        from build_graph import extract_review_finding_nodes as _erfn
        _all_findings = _erfn()
    except Exception as exc:        # cannot-measure is not success
        details.append(Detail(
            "finding_population", False, measured=False,
            message=f"could not read the ReviewFinding population ({exc}); neither "
                    f"open-REQUIRED ratchet ran, so their silence is not evidence"))
        return CheckResult(passed=False, measured=False, details=details)
    if not _all_findings:
        details.append(Detail(
            "finding_population", False, measured=False,
            message="the ReviewFinding population is EMPTY — every open-REQUIRED ratchet "
                    "below would read 0 and pass over nothing, so this check is "
                    "UNVERIFIED, not passing. An empty population is the round-8 state "
                    "(rename `evaluate_all_gates` and every readiness check goes green), "
                    "not a clean corpus"))
        return CheckResult(passed=False, measured=False, details=details)

    # ── Ratchet 1: the open-REQUIRED population, per bundle (ADR-012 D9) ──────────
    # ⚠️ EVERY BLOCKING SEVERITY, not just `major`. Keying on `severity_mix['major']` left
    # the attributed open CRITICALS ratcheted by nothing — leg 2 covers only the
    # *unattributed* ones — so the population this leg claims to bound had a hole the exact
    # size of the corpus's criticals. `BLOCKING_SEVERITIES` is imported, never restated.
    from readiness_gates import BLOCKING_SEVERITIES as _BLOCKING
    _ceilings = _required_open_ceilings()
    # A renamed aggregate key would make every bundle read 0 and pass — the
    # `lean_modules` vs `lean_modules_referenced` trap, one file over.
    if not any("severity_mix" in (d or {}) for d in (by_bundle or {}).values()):
        details.append(Detail(
            "required_population", False, measured=False,
            message="no bundle aggregate carries a `severity_mix` key — the field this "
                    "ratchet counts has been renamed or dropped, and counting a missing "
                    "key yields 0 for every bundle, which passes"))
        bad += 1
        _live_total = None
    else:
        over = []
        _live_total = 0
        for bundle, data in sorted((by_bundle or {}).items()):
            mix = data.get("severity_mix") or {}
            live = sum(v for k, v in mix.items() if k in _BLOCKING)
            _live_total += live
            ceiling = _ceilings.get(bundle, 0)
            if live > ceiling:
                over.append(f"{bundle} {live}>{ceiling}")
        details.append(Detail(
            "required_population", not over,
            f"open REQUIRED ({'/'.join(sorted(_BLOCKING))}) findings per bundle, against "
            f"frozen ceilings; "
            + (f"ABOVE CEILING: {', '.join(over)}. These severities are ALREADY blocking — "
               f"what this ratchet adds is that the population may not GROW (PD-5). Fix "
               f"the finding; do not raise the ceiling."
               if over else
               f"{_live_total} across {len(by_bundle or {})} bundle(s) "
               f"({len(_ceilings)} carry a non-zero ceiling), none above ceiling")))
        if over:
            bad += 1

    # ── Ratchet 2: the population ratchet 1 structurally cannot see ───────────────
    # ⚠️ THE COMPLEMENT OF LEG 1'S COVERAGE, not a proxy for it. This counted findings
    # carrying NEITHER `inferred_paper` NOR `inferred_bundle` — a guess at which findings
    # fail to reach the aggregation. The guess was wrong for a whole class: a finding
    # carrying `inferred_paper` for a paper that maps to NO bundle (the pre-bundle-era
    # corpus, ADR-012 D7) has a key, so this leg skipped it, and reaches no bundle, so
    # leg 1 never saw it. Measured 2026-08-12: EIGHT open blocking findings sat in that
    # gap, and `END_TO_END_MAP`'s claim that the two legs cover the population between
    # them was false as written.
    #
    # Keying on what the aggregation ACTUALLY reached makes the coverage true by
    # construction rather than by argument: leg 1 counts the ids in `open_finding_ids`,
    # leg 2 counts every open blocking finding whose id is not among them. Neither leg
    # can be satisfied by moving a finding out of its scope, because the scopes are
    # defined as complements. `test_the_two_ratchet_legs_cover_the_population` pins it.
    _covered: set[str] = set()
    for _d in (by_bundle or {}).values():
        _covered.update(_d.get("open_finding_ids") or ())
    _open_blocking = [
        n for n in _all_findings
        if (n["meta"].get("status") == "open"
            and n["meta"].get("severity") in _BLOCKING)]
    _uncovered = [n for n in _open_blocking if n["id"] not in _covered]
    _covered_blocking = [n for n in _open_blocking if n["id"] in _covered]
    unattributed = len(_uncovered)
    ok_un = unattributed <= UNATTRIBUTED_OPEN_BLOCKING_CEILING
    # ⚠️ THE SEAM, REPORTED (2026-08-15). "Declared a target that does not resolve" and
    # "declared nothing" are different facts about a document and must not share a
    # rendering: the first is a convention with a typo or a missing mapping entry, and it
    # keeps reading as attribution to every human who opens the file, while no consumer
    # can act on it. A silent merge into the undeclared population is how the whole
    # defect this leg is measuring stayed invisible for months.
    _unresolved = 0
    for _n in _uncovered:
        _m = _n["meta"]
        if _m.get("declared_paper") or _m.get("declared_bundle"):
            _unresolved += 1
    details.append(Detail(
        "unattributed_population", ok_un,
        f"{unattributed} open {'/'.join(sorted(_BLOCKING))} finding(s) are NOT reached by "
        f"the per-bundle aggregation, so no bundle ceiling bounds them; "
        f"limit {UNATTRIBUTED_OPEN_BLOCKING_CEILING}. "
        f"Of those, {_unresolved} DECLARE a target that resolves to no bundle "
        f"(an `infra`/`process` lane, or a key outside PAPER_DRAFT_MAPPING) and "
        f"{unattributed - _unresolved} declare nothing — a declaration that cannot be "
        f"resolved is reported here rather than merged into the undeclared population, "
        f"because it still reads as attribution to anyone opening the file. "
        f"The two legs are complements over one id set, so every open blocking finding reaches exactly one of them: "
        f"{len(_covered_blocking)} reached by the aggregation, {unattributed} not. "
        f"⚠️ Leg 1 ratchets bundle-OCCURRENCES of those {len(_covered_blocking)} findings, not the findings — a finding attributed to two bundles counts against both ceilings, which is correct for a per-bundle guard and is why leg 1's total exceeds this one"
        + ("" if ok_un else
           " — a finding that LOSES its attribution leaves the per-bundle ratchet. "
           "Re-attribute it or fix it; never raise this limit.")))
    if not ok_un:
        bad += 1

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


def _prose_with_line_index(src: Path) -> tuple[str, list[int]]:
    r"""Comment-stripped prose as ONE string, plus each line's start offset in it.

    ⚠️ **A per-LINE scan of a soft-wrapped manuscript measures the line breaks, not the
    prose.** LaTeX source wraps at ~95 columns wherever the word happens to fall, so
    whether a phrase is visible to a line-oriented pattern is decided by the wrap. It is
    not hypothetical: D12 `:405-406` reads *"…and have / not inspected its text"*, and a
    line scan sees `have` and `not inspected its text` as different subjects. That
    passage was caught only because a SECOND pattern happened to fall inside one line —
    reflow the paragraph and the gate goes green on unchanged prose.

    A **blank line is a paragraph break** and is rendered as a full stop, so no pattern
    can span two paragraphs; a comment-only line is not a break (a `%` note inside a
    paragraph does not interrupt the sentence) and joins as a space. Blankness is read
    off the RAW line, before comment stripping, so the two cases stay distinguishable.

    Returns `(prose, starts)` where `starts[i]` is the offset of source line `i+1`;
    `_line_at` maps a match offset back to a 1-indexed line, so widening the scan
    window costs nothing in the precision of what the report names.
    """
    out: list[str] = []
    starts: list[int] = []
    pos = 0
    for raw in src.read_text(errors="replace").splitlines():
        piece = "." if not raw.strip() else _TEX_COMMENT_RE.sub("", raw)
        starts.append(pos)
        out.append(piece)
        pos += len(piece) + 1
    return " ".join(out), starts


def _line_at(starts: list[int], offset: int) -> int:
    """1-indexed source line containing `offset` in `_prose_with_line_index`'s string."""
    return bisect.bisect_right(starts, offset)



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
    codes, _roster_err = _H.bundle_codes_or_unmeasured()
    if codes is None:
        return CheckResult(passed=False, measured=False, details=[Detail(
            "roster", False, _roster_err)])

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


def _strip_tex_comments(text: str) -> str:
    """Drop each line's LaTeX comment, honouring the `\\%` escape.

    A module named only inside a commented-out block is not cited by the manuscript.
    Counting it silently credited drafts for substrate the reader never sees.
    """
    return "\n".join(re.sub(r"(?<!\\)%.*$", "", line) for line in text.splitlines())


@lru_cache(maxsize=1)
def _declarations_by_module() -> dict[str, frozenset[str]]:
    """Module -> the distinctive declaration names it alone owns, from `lean_deps.json`.

    A draft that names `schwarzschild_area_monotone` has reached the module proving it,
    whether or not it also spells the filename. Three filters keep a match meaningful:
    autogenerated declarations are skipped (they are Mathlib spillover, not this
    project's claims); a name must be at least 8 characters and contain `_`, so common
    identifiers cannot match incidental prose; and a short name owned by more than one
    module credits neither, since it cannot say which one the draft meant.

    Returns `{}` when the extract is missing or unreadable — the check then falls back
    to filename matching alone, which over-reports absence rather than under-reporting it.
    """
    path = _H.PROJECT_ROOT / "lean" / "lean_deps.json"
    try:
        decls = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError):
        return {}
    owners: dict[str, set[str]] = {}
    for d in decls:
        if not isinstance(d, dict) or d.get("autogen"):
            continue
        mod, name = d.get("module"), str(d.get("name", ""))
        short = name.split(".")[-1]
        if not mod or len(short) < 8 or "_" not in short:
            continue
        owners.setdefault(short, set()).add(mod)
    by_mod: dict[str, set[str]] = {}
    for short, mods in owners.items():
        if len(mods) == 1:
            by_mod.setdefault(next(iter(mods)), set()).add(short)
    return {m: frozenset(v) for m, v in by_mod.items()}


@lru_cache(maxsize=1)
def _build_modules() -> frozenset[str]:
    """Every module name present in the Lean build, per `lean_deps.json`."""
    try:
        decls = json.loads((_H.PROJECT_ROOT / "lean" / "lean_deps.json").read_text())
    except (OSError, json.JSONDecodeError):
        return frozenset()
    return frozenset(d["module"] for d in decls
                     if isinstance(d, dict) and d.get("module"))


@lru_cache(maxsize=None)
def _resolve_module(registered: str) -> str | None:
    """Registered short name -> its module in the build, or None if it has none.

    ⚠️ Registrations are NOT written in build-module form. They are recorded as a
    bundle's wave saw them: dotted (`APSEta.He3A`), path-style (`RossSelinger/BridgeParity`),
    or bare (`CliffordCCZSU8Density`, which actually lives at `SKEFTHawking.FKLW.`+that).
    Resolving on `SKEFTHawking.<registered>` alone calls 182 of 444 registrations
    nonexistent; resolving through nesting and leaf brings that to 52, and the difference
    is entirely naming convention. Anything reported as unresolved must survive this
    ladder first — see `reference-measurement-traps-false-absence`.
    """
    name = registered.replace("/", ".")
    mods = _build_modules()
    if f"SKEFTHawking.{name}" in mods:
        return f"SKEFTHawking.{name}"
    nested = [m for m in mods if m.endswith(f".{name}")]
    if nested:
        return sorted(nested)[0]
    leaf = name.split(".")[-1]
    by_leaf = [m for m in mods if m.split(".")[-1] == leaf]
    return sorted(by_leaf)[0] if len(by_leaf) == 1 else None


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
#:
#: 2026-08-11: 236 -> 149 by a PREDICATE CORRECTION, not by repayment. The old predicate
#: was wrong in three ways, and the errors had been partly cancelling:
#:   * it read the raw `.tex`, so a module named only inside a `%`-commented block
#:     counted as cited (15 modules corpus-wide, 4 of them I1's — false credit);
#:   * it looked for the module's *filename*, so a draft that cites that module's
#:     theorems by name scanned as never reaching it (false debt; D11 19 -> 0 and
#:     D10 9 -> 0 once declarations count); and
#:   * registrations are not written in build-module form, so crediting declarations
#:     had to resolve `CliffordCCZSU8Density` to `SKEFTHawking.FKLW.CliffordCCZSU8Density`
#:     and `RossSelinger/BridgeParity` to its dotted form (a further 219 -> 149).
#: Citing a theorem is stronger evidence that declared substrate reached the published
#: claim than naming a file, which is what this check is for. Because 149 < 236 this is
#: an ordinary down-ratchet — the honest number was always below the recorded one.
#: The count is now COMPARABLE ONLY TO ITSELF: do not diff it against a pre-08-11 figure.
LEAN_MODULE_ABSENT_CEILING = 149


def _deregistered_detail(dropped: dict[str, list[str]]) -> Detail:
    """The always-printed ledger of what each bundle stopped resting on.

    ⚠️ It NAMES the modules, and both exit paths of the coverage check use this one
    formatter. A summary that reports only a count is not the visibility half of the
    deregistration design — "1 module deregistered" and "the module this Letter is
    about was deregistered" have to look different to a reader, and the second is the
    one worth seeing.
    """
    n = sum(len(v) for v in dropped.values())
    return Detail(
        "deregistered", True,
        f"{n} module(s) across {len(dropped)} bundle(s) are recorded as DEREGISTERED — "
        f"a draft that stopped resting on them, declared through `bundle_append.py "
        f"--deregister-lean-modules` with a rationale, and excluded from the absence "
        f"ledger ({'; '.join(f'{c}: {", ".join(v)}' for c, v in sorted(dropped.items()))})",
        warning=True)


@register_check("bundle_lean_module_coverage",
                "Lean modules a bundle registers as contributing are reached by its draft, "
                "by module name or by citing their theorems (ratcheted)")
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

    **A module counts as reached three ways, and never from a comment.** Drafts escape
    underscores inside `\\thm{}`/`\\texttt{}`, so `Foo_Bar` appears as `Foo\\_Bar` and a
    bare substring test misses it; a dotted module is often cited by its leaf
    (`APSEta.He3A` as `He3A`); and a draft may cite a module's *theorems* without ever
    naming the file, which is the stronger form of reaching it — see
    `_declarations_by_module`. Commented-out LaTeX is excluded, so a module surviving
    only in a `%` block reads as absent, which it is.

    ## Deregistration — a bundle MAY drop a module, visibly and deliberately

    ⚠️ **This ratchet used to punish a legitimate redraft, and the cost was measured
    in manuscript quality, not in gate noise.** Frozen at its corpus-wide ceiling, it
    made any drafting pass that stopped depending on a module raise the count and turn
    the corpus red — so the cheap path was to keep naming the module. The 2026-08-15
    L3 Stage-10 redraft took exactly that path: it **retained two theorem citations in
    its Discussion purely to hold this ratchet green**, and the `prose-reviewer`
    independently flagged those same two as belonging to a different paper's argument
    (`papers/AutomatedReviews/2026-08-15-l3-stage10-redraft/L3.md` §5.2). The check's
    own guidance already said *"repay by removing the registration"* for unbuilt
    modules; there was no mechanism to do it for built ones.

    There is now. `bundle_append.py --deregister-lean-modules … --deregistration-rationale
    …` appends a deregistration event, and the score is taken over the **net**
    registration set (`bundle_append.net_registered_modules`, the single walk — a
    second copy of it here is the duplication `CLAUDE.md` rule 1 names).

    **The ceiling was NOT raised and must not be.** Deregistration lowers the live
    count, which is a down-ratchet — the direction this ratchet already permits.
    Raising the ceiling would buy the same relief while destroying the measurement,
    which is the move `bundle_manuscript_length`'s docstring calls *"accepting a gap
    and hiding it are different acts"*.

    **Three things stop this being an escape hatch**, and only the third is load-bearing:

    * the CLI requires a rationale, and this check re-asserts the same floor, so a
      hand-edited `append_log.json` cannot smuggle a bare deregistration past it;
    * every deregistration is REPORTED on every run, so a bundle that drops substrate
      says so in the gate's own output rather than only in a log nobody opens;
    * **a deregistration is falsifiable against the manuscript.** Claiming the draft no
      longer rests on a module it still reaches — by name or by citing its theorems —
      is a FAILURE, and deliberately not a ratcheted one. That leg is what makes this a
      declaration rather than a mute. Its population is legitimately zero today, which
      is what a regression guard looks like; the mutation test seeds it into production
      to prove it can fire.
    """
    from bundle_append import (DEREGISTRATION_RATIONALE_MIN,
                               net_registered_modules)

    details: List[Detail] = []
    codes, _roster_err = _H.bundle_codes_or_unmeasured()
    if codes is None:
        return CheckResult(passed=False, measured=False, details=[Detail(
            "roster", False, _roster_err)])

    checked = declared = absent_total = 0
    worst: list[tuple[int, str, list[str]]] = []
    unbuilt: dict[str, list[str]] = {}
    dropped: dict[str, list[str]] = {}
    contradicted: list[str] = []
    unjustified: list[str] = []
    for code in codes:
        log = _H.PAPERS_DIR / code / "append_log.json"
        tex = _H.PAPERS_DIR / code / "paper_draft.tex"
        if not log.is_file() or not tex.is_file():
            continue
        try:
            events = json.loads(log.read_text()).get("events", [])
        except (OSError, json.JSONDecodeError):
            continue
        mods, deregistered = net_registered_modules(events)

        # ⚠️ The rationale floor is asserted HERE as well as in the writer, because the
        # writer is not the only way an event reaches this file — a hand edit is. A
        # gate that trusts its own CLI to have been used is not a gate.
        for e in events:
            drop = e.get("lean_modules_deregistered") or []
            if isinstance(drop, str):
                drop = drop.split(",")
            drop = [str(x).strip() for x in drop if str(x).strip()]
            if not drop:
                continue
            why = str(e.get("deregistration_rationale") or "").strip()
            if len(why) < DEREGISTRATION_RATIONALE_MIN:
                unjustified.append(
                    f"{code}: deregistration of {', '.join(drop)} dated "
                    f"{e.get('date', '?')} carries a rationale of {len(why)} "
                    f"character(s), below the floor of "
                    f"{DEREGISTRATION_RATIONALE_MIN}")

        if deregistered:
            dropped[code] = sorted(deregistered)
        if not mods and not deregistered:
            continue
        # `\_` -> `_` so an escaped identifier matches its declared form; then drop
        # commented-out LaTeX, which is not part of the published claim.
        body = _strip_tex_comments(tex.read_text(errors="replace").replace("\\_", "_"))
        owned = _declarations_by_module()

        def _reached(m: str) -> bool:
            if m.split(".")[-1] in body or m in body:
                return True
            resolved = _resolve_module(m)
            return bool(resolved) and any(d in body for d in owned.get(resolved, ()))

        # ⚠️ THE FALSIFIABILITY LEG. A deregistration says "this draft no longer rests
        # on that module". `_reached` is the same predicate the absence ledger uses, so
        # a module the draft still names, or whose theorems it still cites, contradicts
        # the record. Scored for EVERY deregistering bundle, including one that has
        # deregistered everything it ever registered — which is why this sits above the
        # `not mods` guard rather than inside the registered-module accounting.
        contradicted += [
            f"{code}: `{m}` was deregistered, but the draft still reaches it "
            f"(by name or by citing its theorems) — the record and the manuscript "
            f"disagree; re-register it, or stop reaching it"
            for m in sorted(deregistered)
            if m.split(".")[-1] not in _AMBIGUOUS_MODULE_BASENAMES and _reached(m)]

        if not mods:
            continue
        checked += 1
        declared += len(mods)

        missing = [m for m in sorted(mods)
                   if m.split(".")[-1] not in _AMBIGUOUS_MODULE_BASENAMES
                   and not _reached(m)]
        absent_total += len(missing)
        if missing:
            worst.append((len(missing), code, missing))
        ghosts = sorted(m for m in missing if _resolve_module(m) is None)
        if ghosts:
            unbuilt[code] = ghosts

    if checked == 0 and not dropped:
        details.insert(0, Detail(
            "population", False,
            "no bundle declares a contributing Lean module — this check is UNVERIFIED, "
            "not passing. The field is `lean_modules_referenced` in append_log.json"))
        return CheckResult(passed=False, measured=False, details=details)

    if checked == 0:
        # ⚠️ Every registration in the corpus has been deregistered. The ABSENCE LEDGER
        # is then unmeasurable — zero absent modules out of zero registered is not a
        # clean bill — but the deregistration legs below DID measure, and a corpus in
        # this state is exactly where a false deregistration would hide. So the ratchet
        # leg reports UNMEASURED and the falsifiability legs still return their verdict,
        # rather than the whole check going quiet over the one shape it must not.
        details.append(Detail(
            "ratchet", True,
            "UNMEASURABLE — every registered module in the corpus has been "
            "deregistered, so the absence ledger has no population. The "
            "deregistration legs below are this check's only live assertion in that "
            "state.", warning=True, measured=False))
        ok = not contradicted and not unjustified
        for r in contradicted:
            details.append(Detail("deregistration_contradicted", False, r))
        for r in unjustified:
            details.append(Detail("deregistration_unjustified", False, r))
        details.insert(0, _deregistered_detail(dropped))
        return CheckResult(passed=ok, measured=True, details=details)

    for n, code, missing in sorted(worst, reverse=True):
        details.append(Detail(
            code, True,
            f"{n} of the modules it registers are reached by its draft neither by name "
            f"nor by citing their theorems (e.g. {', '.join(missing[:3])})", warning=True))

    if unbuilt:
        n_ghost = sum(len(v) for v in unbuilt.values())
        details.append(Detail(
            "unbuilt", True,
            f"{n_ghost} of those, across {len(unbuilt)} bundle(s), resolve to NO module "
            f"in the Lean build and so can never be repaid by citing them — they are "
            f"registrations of substrate that was planned and not built "
            f"({'; '.join(f'{c}: {len(v)}' for c, v in sorted(unbuilt.items()))}). "
            f"Repay by removing the registration, not by writing prose about them "
            f"(TODO-D50)", warning=True))

    # ⚠️ **DEREGISTRATIONS ARE REPORTED ON EVERY RUN, INCLUDING A GREEN ONE.** That is
    # half of what makes dropping a dependency *visible* rather than silent: the ledger
    # of what each bundle stopped resting on is in the gate's output, not only in a log
    # nobody opens. It is a warning-level detail because a legitimate drop is not a
    # defect — the two legs below are what fail.
    if dropped:
        details.append(_deregistered_detail(dropped))

    # Both legs below are HARD, unratcheted failures. A ratchet on either would let a
    # bundle buy absence-ledger relief with an unjustified or false deregistration,
    # which is precisely the escape hatch this mechanism must not be.
    for r in contradicted:
        details.append(Detail("deregistration_contradicted", False, r))
    for r in unjustified:
        details.append(Detail("deregistration_unjustified", False, r))

    ok = (absent_total <= LEAN_MODULE_ABSENT_CEILING
          and not contradicted and not unjustified)
    details.insert(0, Detail(
        "ratchet", absent_total <= LEAN_MODULE_ABSENT_CEILING,
        f"{absent_total} registered-but-absent module(s) across {checked} bundle(s) "
        f"({declared} net-declared after {sum(len(v) for v in dropped.values())} "
        f"deregistration(s)); ceiling {LEAN_MODULE_ABSENT_CEILING}"
        + ("" if absent_total <= LEAN_MODULE_ABSENT_CEILING else
           " — REGISTERED SUBSTRATE DRIFTED FURTHER FROM THE PUBLISHED CLAIM. Cite the "
           "module, or DEREGISTER it with a rationale "
           "(`bundle_append.py --deregister-lean-modules`) if the draft genuinely no "
           "longer rests on it; do not widen the ambiguous-basename list, and do not "
           "keep a citation alive only to hold this number down")))
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
    codes, _roster_err = _H.bundle_codes_or_unmeasured()
    if codes is None:
        return CheckResult(passed=False, measured=False, details=[Detail(
            "roster", False, _roster_err)])

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
    codes, _roster_err = _H.bundle_codes_or_unmeasured()
    if codes is None:
        return CheckResult(passed=False, measured=False, details=[Detail(
            "roster", False, _roster_err)])

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
    # ── Added 2026-08-15: the SECOND shape, disclosed INCOMPLETE DILIGENCE ──
    # The seven patterns above all match one act — the manuscript narrating its own
    # EDITING history. A manuscript telling a referee that it did not read a source it
    # cites is a different act with the same disqualifying property: it is an account of
    # the authors' process, the reader cannot act on it, and here it is also a submission
    # non-starter, because the citation is left standing as support for a claim while the
    # text says nobody read it. See ADR-014: the repair is ACQUISITION, and deleting the
    # disclosure while keeping the citation converts a visible gap into an invisible one.
    #
    # ⚠️ **THREE SHAPES LOOK ALIKE AND ONLY ONE IS THE DEFECT.** This is why the patterns
    # below key on *the text of a cited source*, never on "we did not"/"not read":
    #
    #   ✗ "we did not read a source we cite as support"     → the defect; must fire
    #   ✓ "the cited source ITSELF reports partial progress" → scholarly hedging
    #   ✓ "our novelty search covered X and not Y"          → REQUIRED on a novelty claim
    #
    # All three are live in D12 within 300 lines of each other, and the near-misses are
    # measured, not imagined: `:673` *"…which presents itself as an ongoing project…so we
    # do not read it as establishing how much of that layer is finished"* (shape 2),
    # `:674` *"HOL Light was not among the ecosystems we assessed and we do not assert
    # absence there"* (shape 3), and — one word from firing — `:288` *"We have not been
    # able to inspect that development directly"* and `:792` *"We did not inspect this
    # development"*, both of which bound a PRIOR-ART sweep rather than excusing a
    # citation, and both of which stay green. **The discriminator is the noun**: not
    # reading *its text* is the defect; not having surveyed *that development* is the
    # scope statement a priority claim owes its reader.
    #
    # Measured before shipping, per the 2026-08-08 bar: 21 bundle drafts + their full
    # `\input` closure (85 reader-visible files), and all 64 `paper_draft.tex` in the
    # tree. **5 matches, all in D12, at `:405`, `:474`, `:475`, `:498`; zero elsewhere.**
    # The existing seven patterns are unchanged at 0 in both scan modes.
    (r"(?:have|has|had|having)\s+not\s+(?:yet\s+)?"
     r"(?:read|inspected|examined|consulted|obtained|accessed)\s+"
     r"(?:its|their|the|this)\s+(?:full[-\s]text|text|contents?|body|manuscript)\b",
     "a disclosure that the text of a cited source was never read"),
    (r"only\s+as\s+an?\s+(?:resolved\s+)?"
     r"(?:DOI|bibliographic|catalogue|catalog|metadata|index)\s+(?:record|entry)\b",
     "a cited source held only as a metadata record, disclosed to the reader"),
    (r"\b[Ww]e\s+(?:have\s+|had\s+)?read\s+(?:"
     r"[^.]{0,80}?\bin\s+(?:the\s+)?abstracts?\s+(?:only|alone)\b"
     r"|only\s+(?:its|the|this)\s+abstracts?\b"
     r"|(?:its|the|this)\s+abstracts?\s+(?:only|alone)\b)",
     "a disclosure that a cited source was read in abstract only"),
)

# ── What the diligence half deliberately does NOT cover, and why (2026-08-15) ──
# Two further phrasings of the same act were drafted and DROPPED before shipping:
# "without having read it" and "could not obtain the full text". Both score ZERO on the
# corpus, so neither could be validated by measurement — and each sits one word from
# live, legitimate prose: I1 `:2543` "can be classified without reading the prose that
# surrounds it" and `:775` "without reading a proof"; D11 `:560` "the two results we
# could not obtain are recorded as deferred". Shipping an unmeasured pattern whose
# nearest neighbour is correct prose in the methodology paper is exactly the mistake the
# vocabulary denylist made. Those two phrasings are therefore UNCOVERED: the prose
# reviewer catches them, and a pattern is added THEN, with a measurement behind it.


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


@register_check(
    "bundle_reader_facing_voice",
    "No bundle draft narrates its own process to the reader — neither its correction "
    "history nor its unfinished diligence")
def check_bundle_reader_facing_voice() -> CheckResult:
    """CHECK (ADR-011 Phase 3, F-05): a fix may not narrate itself.

    A published paper states what IS true. It does not tell a referee what an earlier
    draft of itself said, when it was corrected, or which review round caught it. That
    reader has no access to the process and cannot act on it, so the text reads as a
    repository changelog pasted into a manuscript.

    **Two shapes, one rule.** The first is the manuscript's own EDITING history (seven
    patterns, 2026-08-01/08-08). The second, added 2026-08-15, is disclosed **incomplete
    diligence** — the manuscript telling a referee that it never read the text of a
    source it cites. Same disqualifying property, and additionally a submission
    non-starter: the citation stands as support while the prose says nobody read it. The
    repair is ACQUISITION (ADR-014), not deletion — dropping the disclosure and keeping
    the citation turns a visible gap into an invisible one, so this check going RED on
    the sites that are blocked on acquisition is the correct state, not a bug.

    ⚠️ The diligence patterns key on *the text of a cited source*, never on "we did
    not" — a source that ITSELF reports partial progress, and a novelty search that
    states which ecosystems it covered, are legitimate and stay green. The constant's
    comment carries the measured near-misses that fix that line.

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

    Comments are stripped — `%` text is not rendered, and the lift banners live there —
    and the scan runs over paragraph-joined prose, so a soft wrap cannot hide a passage
    (`_prose_with_line_index`).
    """
    details: List[Detail] = []
    codes, _roster_err = _H.bundle_codes_or_unmeasured()
    if codes is None:
        return CheckResult(passed=False, measured=False, details=[Detail(
            "roster", False, _roster_err)])

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
            prose, starts = _prose_with_line_index(src)
            for pat, why in _SELF_NARRATION:
                for m in re.finditer(pat, prose):
                    found.append((src, _line_at(starts, m.start()), why,
                                  m.group(0)[:60]))
        if found:
            total += len(found)
            # Sorted, because the patterns are now scanned pattern-major over the whole
            # file: "first" must mean earliest in the DOCUMENT, which is the only sense
            # in which it is a place to start reading.
            src, i, why, txt = min(found, key=lambda f: (str(f[0]), f[1]))
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
        f"process to the reader — its correction history, or a source it cites without "
        f"having read (target 0; a correction belongs in change_log.md, and an unread "
        f"source is repaired by acquiring it, not by dropping the disclosure — ADR-014)"))
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
    codes, _roster_err = _H.bundle_codes_or_unmeasured()
    if codes is None:
        return CheckResult(passed=False, measured=False, details=[Detail(
            "roster", False, _roster_err)])

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
    codes, _roster_err = _H.bundle_codes_or_unmeasured()
    if codes is None:
        return CheckResult(passed=False, measured=False, details=[Detail(
            "roster", False, _roster_err)])

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
        details.append(Detail("unmeasured", True, r, warning=True, measured=False))

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
    # under-floor population fell 11 → 3 on a stale tree (ACCURACY_LEDGER V75/V79
  # row 1; ADR-011 §C4) and 11 → 10 on a test-seeded one (V80 row 1), and it stayed
  # GREEN throughout. (An earlier draft of this comment wrote "11 → 10 → 1",
  # asserting a third degradation that is recorded nowhere.)
    #
    # That is not only an advisory-information loss. A bundle that goes UNMEASURED
    # also escapes the OVER-CEILING leg — the one that still gates — so staleness
    # was a way to skip the only blocking check here. Latent today (zero
    # over-ceiling bundles), which is exactly why it needed closing before it
    # wasn't.
    #
    # Folding it makes the perishability ENFORCE itself rather than be documented
    # in three places and observed in none: a stale tree now reads `75 MEASURED,
    # floor 76` under `--ci` instead of a green tick over part of the corpus. The
    # remedy is `scripts/compile_bundle_pdf.py --all --force`.
    # `measured=True` whenever ANY bundle was sized. THE ONE POLICY: `measured=False`
    # means the population was UNREACHABLE, not that coverage of it was INCOMPLETE.
    # Sizing 10 of 21 is incomplete coverage of a reachable population, so the check
    # IS measured; the 11 it could not size are carried on their own details, each
    # `measured=False`, which is where the granular signal belongs. The wholly
    # unreachable case (`sized == 0`) returns `measured=False` at the guard above.
    #
    # The previous `measured=not unmeasured` conflated the two and broke `--ci`: the
    # coverage floor counts MEASURED checks with zero headroom, so one stale PDF
    # anywhere took the whole suite under the floor. It also contradicted this
    # module's own policy note in `_registry.py`.
    #
    # ⚠️ What that fold was reaching for is REAL and is NOT solved by this line: a
    # bundle that goes UNMEASURED escapes the OVER-CEILING leg, the only one that
    # still gates, so staleness remains a way to skip it. That is contained by
    # keeping it LOUD rather than by lying about `measured` — the summary always
    # prints the UNMEASURED count, every skipped bundle is named, and
    # `bundle_source_freshness` gates staleness directly. Recompiling
    # (`scripts/compile_bundle_pdf.py --all --force`) is the remedy; see
    # VALIDATION_ARCHITECTURE.md §5.1 for the regeneration ORDER.
    return CheckResult(passed=len(over) == 0,
                       measured=sized > 0, details=details)


#: LaTeX control sequences that contribute NOTHING to the rendered abstract: pure
#: markup, cross-referencing and spacing. Their ARGUMENT still counts — `\textit{foo}`
#: renders as `foo` — so only the command token is removed.
_ABSTRACT_INVISIBLE_MACROS = frozenset({
    "textit", "textbf", "texttt", "textrm", "textsf", "textsc", "emph", "mbox",
    "text", "mathrm", "mathbf", "mathit", "mathcal", "mathbb", "operatorname",
    "label", "noindent", "protect", "ensuremath", "left", "right", "big", "Big",
    "bigl", "bigr", "Bigl", "Bigr", "displaystyle", "textstyle", "vspace", "hspace",
    "small", "footnotesize", "normalsize", "par", "linebreak", "newline",
})

#: LaTeX escapes for characters that ARE one rendered character.
_ABSTRACT_LITERAL_ESCAPES = {
    r"\%": "%", r"\&": "&", r"\_": "_", r"\$": "$", r"\#": "#",
    r"\{": "{", r"\}": "}", r"\~": "~", r"\^": "^",
}

_ABSTRACT_ENV_RE = re.compile(r"\\begin\{abstract\}(.*?)\\end\{abstract\}", re.S)
_MACRO_RE = re.compile(r"\\([A-Za-z]+)\*?")


def abstract_plain_text(tex_body: str) -> str | None:
    """The `abstract` environment reduced to a RENDERED-LENGTH PROXY, or `None`.

    ⚠️ **This is a proxy, and saying so is part of the check's contract.** The only
    authoritative count is the one the publisher's own submission form performs on the
    typeset abstract. What this does:

    * takes the `abstract` environment, minus LaTeX comments;
    * drops pure-markup control sequences (`\\textit`, `\\label`, sizing, `\\left`)
      while KEEPING their arguments, because `\\textit{foo}` renders as `foo`;
    * collapses every OTHER control sequence to a single character, because a macro
      like `\\alpha`, `\\kappa` or a project shorthand like `\\Thawk` typesets as
      roughly one glyph — counting `\\Thawk` as six characters would inflate a
      symbol-dense abstract past a limit it actually meets;
    * unescapes `\\%`, `\\_`, … to the one character each renders as;
    * removes braces and math delimiters, and collapses whitespace runs to one space.

    **The proxy's error is bounded and small relative to the verdicts it drives.** The
    corpus measurement on 2026-08-15 found the letter abstracts at 2.1–4.7× their
    declared ceiling; no plausible per-macro error changes those verdicts. A bundle
    landing within a few percent of its ceiling should be confirmed by hand — the
    detail line prints the measured value so that is possible without re-deriving it.
    """
    m = _ABSTRACT_ENV_RE.search(_strip_tex_comments(tex_body))
    if not m:
        return None
    s = m.group(1)
    for esc, lit in _ABSTRACT_LITERAL_ESCAPES.items():
        s = s.replace(esc, "\x00" + lit + "\x00")   # park it out of macro reach
    s = _MACRO_RE.sub(
        lambda mo: "" if mo.group(1) in _ABSTRACT_INVISIBLE_MACROS else "x", s)
    s = s.replace("\x00", "")
    s = re.sub(r"[{}$]|\\[()\[\]]|\\\\", " ", s)
    return re.sub(r"\s+", " ", s).strip()


#: Down-only floor on how many bundles declare an `abstract_ceiling`.
#:
#: MEASURED 2026-08-15: **5 of 21** — the letter bundles L1, L2, L3, E1, E2.
#:
#: ⚠️ **THIS IS THE POPULATION FLOOR, NOT A VIOLATION CEILING, and it is the leg
#: `CHECK_AUTHORING_GUIDE` §2.5 exists for.** Non-empty is not enough: if four of the
#: five declarations were dropped, the check would size one abstract, find it within its
#: ceiling and report a clean pass — a narrowed population reporting health over the
#: bundles it stopped reading. `theorem_census_agrees` lost 13 matched sites to 5 and
#: stayed green on exactly that shape. RAISE this as venues are declared; lower it only
#: with a stated reason (a bundle retired, or a venue confirmed to publish no limit).
ABSTRACT_CEILING_DECLARED_FLOOR = 5


@register_check(
    "bundle_abstract_length",
    "Every bundle's abstract is within the abstract ceiling its declared venue imposes")
def check_bundle_abstract_length() -> CheckResult:
    """CHECK: the abstract is the size the venue accepts, which no other gate asked.

    **The gap this closes, measured.** `bundle_manuscript_length` sizes the whole
    compiled manuscript and nothing sized the abstract, so PRL's abstract limit was
    enforced nowhere. The 2026-08-15 L3 Stage-10 redraft found the superseded L3
    abstract at roughly 1900 characters against PRL's ~600 — **over three times the
    limit, and every gate in the suite passed it.** A real submission would have been
    desk-returned before review
    (`papers/AutomatedReviews/2026-08-15-l3-stage10-redraft/L3.md` §5.1). Five bundles
    are letters (L1, L2, L3, E1, E2), so this is not a single-bundle accident.

    ## The ceiling is DECLARED, never known by this check

    ⛔ **This check hardcodes no venue's limit, and must not start.** It reads
    `length_target.abstract_ceiling` from each bundle's `bundle_metadata.json`:

    ```json
    "abstract_ceiling": {
      "unit": "characters",          // or "words"
      "ceiling": 600,
      "source": "<the author guide that states it>",
      "source_verified": false,      // has a human confirmed it against the primary?
      "source_note": "<why not, if not>"
    }
    ```

    A hardcoded table would be the `CHECK_AUTHORING_GUIDE` §6 failure *"a
    hand-maintained list parallel to a registry"*: the venue already lives in the
    bundle's own metadata, beside the `length_target` this parallels exactly.

    ⚠️ **`source_verified` is reported in the detail line, and it is not decoration.**
    A 2026-08-15 `research-scout` pass could not confirm a single one of fourteen
    venues' abstract limits against its primary author guide: APS
    (`journals.aps.org/robots.txt` disallows automated agents), Elsevier and AIP return
    403 to every request including `robots.txt`, and Springer redirects to a login
    wall. The one figure it DID verify — JOSS — is that JOSS states no separate
    abstract limit at all. So the PRL ~600 in the letter bundles is **the pilot
    finding's number, not a primary-sourced one**, and the check says so on every run
    rather than letting a green be read as *"confirmed venue-conformant"*. Confirming
    these against the actual author guides is filed as a finding, not silently assumed.

    ## What UNMEASURED means here

    A bundle with no `abstract_ceiling`, or with no `abstract` environment in its
    draft, is reported BY NAME as UNMEASURED with `measured=False` on that detail — it
    is never a quiet pass. The wholly-unreachable case returns `measured=False` for the
    check. This mirrors `bundle_manuscript_length`, deliberately: an absent declaration
    is a live, visible state and the honest record for a bundle whose venue is open.

    **What this does NOT verify:** that the abstract is *good*, that it states the
    paper's result, or that the count matches the publisher's own tool to the
    character. The first two belong to `prose-reviewer`; the third is bounded by
    `abstract_plain_text`'s documented proxy error.
    """
    details: List[Detail] = []
    codes, _roster_err = _H.bundle_codes_or_unmeasured()
    if codes is None:
        return CheckResult(passed=False, measured=False, details=[Detail(
            "roster", False, _roster_err)])

    over: list[str] = []
    within: list[str] = []
    unmeasured: list[str] = []
    notes: set[str] = set()
    unverified_source = 0
    for code in codes:
        md = _read_metadata(code)
        tex = _H.PAPERS_DIR / code / "paper_draft.tex"
        if md is None or not tex.is_file():
            continue
        spec = (md.get("length_target") or {}).get("abstract_ceiling")
        if not spec or spec.get("ceiling") is None:
            unmeasured.append(
                f"{code}: no `length_target.abstract_ceiling` declared "
                f"(target_journal: {md.get('target_journal', '?')})")
            continue
        plain = abstract_plain_text(tex.read_text(errors="replace"))
        if plain is None:
            unmeasured.append(f"{code}: no `abstract` environment in paper_draft.tex")
            continue

        unit = spec.get("unit") or "characters"
        value = len(plain.split()) if unit == "words" else len(plain)
        ceiling = spec["ceiling"]
        u = "word(s)" if unit == "words" else "character(s)"
        # ⚠️ The provenance NOTE is printed ONCE, in its own detail below, not on every
        # row. Repeating a 400-character caveat 21 times is how a caveat stops being
        # read — the per-row marker points at the note, the note carries the reason.
        prov = "" if spec.get("source_verified") else " [ceiling UNVERIFIED — see `ceiling_provenance`]"
        if not spec.get("source_verified"):
            unverified_source += 1
            notes.add(f"{spec.get('source') or 'no source recorded'} — "
                      f"{spec.get('source_note') or 'no reason recorded'}")
        if value > ceiling:
            over.append(
                f"{code}: abstract is {value} {u} against a declared ceiling of "
                f"{ceiling} ({value / ceiling:.1f}x) — {md.get('target_journal', '?')} "
                f"would desk-return this before review{prov}")
        else:
            within.append(f"{code}: {value} of {ceiling} {u}{prov}")

    for r in over:
        details.append(Detail("over_ceiling", False, r))
    for r in within:
        details.append(Detail("within_ceiling", True, r))
    for r in unmeasured:
        details.append(Detail("unmeasured", True, r, warning=True, measured=False))
    for r in sorted(notes):
        details.append(Detail("ceiling_provenance", True, r, warning=True))

    sized = len(over) + len(within)
    if sized == 0:
        details.insert(0, Detail(
            "population", False,
            f"no bundle abstract could be sized ({len(unmeasured)} unmeasured) — this "
            f"check is UNVERIFIED, not passing. Declare "
            f"`length_target.abstract_ceiling` with the venue's limit and its source."))
        return CheckResult(passed=False, measured=False, details=details)

    population_ok = sized >= ABSTRACT_CEILING_DECLARED_FLOOR
    if not population_ok:
        details.insert(0, Detail(
            "population_floor", False,
            f"only {sized} bundle(s) declare an `abstract_ceiling`, below the floor of "
            f"{ABSTRACT_CEILING_DECLARED_FLOOR} — the population this check reads has "
            f"SHRUNK. A narrowed population reports health over the bundles it stopped "
            f"reading, which is the defect this suite exists to prevent. Restore the "
            f"declaration, or lower the floor with a stated reason.", measured=False))

    details.insert(0, Detail(
        "summary", not over and population_ok,
        f"{sized} abstract(s) sized against a declared venue ceiling (floor "
        f"{ABSTRACT_CEILING_DECLARED_FLOOR}) — {len(over)} OVER (gating), "
        f"{len(unmeasured)} UNMEASURED; {unverified_source} of the {sized} ceilings are "
        f"NOT confirmed against their primary author guide",
        warning=bool(unverified_source)))
    return CheckResult(passed=not over and population_ok,
                       measured=population_ok, details=details)


#: Down-only floor on how many bundle metadata blobs carry the `critical_open` field
#: (D11 Stage-13 round-9 finding 4.4). 21 of 21 as of 2026-08-14, the run of
#: `scripts/bundle_readiness.py` that introduced it. **May be LOWERED only with a stated
#: reason** — a bundle legitimately retired is one; the writer quietly dropping the field
#: is the defect this floor exists to catch.
_CRITICAL_OPEN_FLOOR = 21


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
    n_with_critical = 0
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
        # `critical_open` — the 🔴-only count, split out 2026-08-14 (D11 Stage-13
        # round-9 finding 4.4) because `blockers_open` is critical+major and its name
        # says otherwise, so a bundle with one 🔴 read as carrying eighteen blockers.
        # POPULATION-RATCHETED below rather than merely "compared when present": a
        # field that quietly stops being written would otherwise make this leg vacuous.
        live_crit = (agg.get("severity_mix") or {}).get("critical", 0)
        if "critical_open" in meta:
            n_with_critical += 1
            if meta.get("critical_open") != live_crit:
                bad.append(f"critical_open={meta.get('critical_open')} "
                           f"live={live_crit}")
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

    # POPULATION RATCHET for the `critical_open` leg. Non-empty is not enough: the leg
    # is skipped per-blob when the field is absent, so a writer that stopped emitting it
    # would silently reduce this to zero comparisons while the check stayed green.
    # Floor scaled to what was actually compared: the ratchet must bite on the live
    # 21-bundle corpus without failing a fixture that legitimately compares fewer blobs.
    # Every blob compared must carry the field either way, so the leg can never be
    # skipped for a bundle in silence.
    _floor = min(_CRITICAL_OPEN_FLOOR, checked)
    if n_with_critical < _floor:
        drift += 1
        details.append(Detail(
            "critical_open_population", False,
            f"only {n_with_critical} of {checked} bundle blob(s) carry "
            f"`critical_open`, below the floor of {_floor} (corpus ratchet "
            f"{_CRITICAL_OPEN_FLOOR}). The 🔴-only count stopped being written "
            f"for some bundles, so that leg compares nothing for them. Re-run "
            f"`uv run python scripts/bundle_readiness.py`; lower the floor only with a "
            f"stated reason."))
    else:
        details.append(Detail(
            "critical_open_population", True,
            f"{n_with_critical} of {checked} bundle blob(s) carry `critical_open` "
            f"(floor {_floor}; corpus ratchet {_CRITICAL_OPEN_FLOOR})"))

    details.insert(0, Detail(
        "summary", drift == 0,
        f"{checked} bundle metadata blob(s) compared against the live graph, "
        f"{drift} with drift"))
    return CheckResult(passed=drift == 0, details=details)


@register_check("readiness_verdicts_agree",
                "The heatmap and the submission gate return the same per-bundle verdict")
def check_readiness_verdicts_agree() -> CheckResult:
    """CHECK: cross-validate the two readiness verdicts. They are NOT independent.

    Added 2026-07-31 (D12 Stage-13 round-6 BLOCKER 8.1). Two subsystems compute
    a per-bundle readiness verdict and had no consistency obligation between them:

      * `scripts/bundle_readiness.py` counts findings straight off the review
        files, per bundle, and rendered D11/D12 RED with unclosed blockers;
      * `readiness_submission_gate` aggregates ReadinessGate node states off the
        graph, and rendered the same bundles as "all P1 passed".

    Both were reporting honestly about their own inputs; nothing compared them,
    so the reassuring one could be quoted as the verdict. This check asserts the
    direction that matters: a bundle the heatmap calls RED (open blocking
    findings) must NOT be green or yellow at the submission gate.

    ⚠️ **THIS IS NOT AN INDEPENDENCE ARGUMENT, and the docstring used to claim it was**
    ("from different inputs" — corrected 2026-08-15, D12 round-6 8.2). Both sides call
    `build_graph.extract_review_finding_nodes()` and both attribute a finding through
    `meta['inferred_bundle']`, derived from the review filename stem. **Every failure in
    that shared layer moves both verdicts the same way**, so this check cannot see it: a
    review filed as `D12-round7.md` infers no bundle, the heatmap drops it AND no FLAGS
    edge is emitted, giving heatmap-GREEN and gate-passed together — and the RED loop's
    `continue` means the guard never even runs. Cross-validating two consumers of one
    input detects disagreement between the consumers, nothing about the input.

    The floor on that shared layer is therefore a SEPARATE check, not this one: the
    `findings_reach_the_graph` leg of `graph_integrity` (`checks/graph_atlas.py`)
    asserts both that a finding resolving to bundle X flags `paper:X`, and that every
    review file named after a roster bundle yields at least one finding resolving to
    it. Read them as a pair — this check is worthless without that one. (Note it is a
    Detail inside `graph_integrity`, not a registered check in its own right, so
    `validate.py --check findings_reach_the_graph` does not resolve.)
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

    papers_root = _H.PAPERS_DIR   # H1: the anchor owns this path, never re-derive it
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
# CHECK: the apex `claims` STRING — the half `bundle_apex_resolves` never reads
# ═══════════════════════════════════════════════════════════════════════

#: Markers that a `claims` string was never written. Anchored: a claim may legitimately
#: contain the word "see" mid-sentence, but one that OPENS with it is a pointer, not a
#: claim.
_CLAIM_PLACEHOLDER_RE = re.compile(
    r"^\s*(todo|tbd|t\.b\.d|n/?a|none|placeholder|xxx|fixme|\.\.\.|see\b|as above\b)",
    re.I)

#: Shortest string that can describe a theorem. Below this it is a label, not a claim.
_CLAIM_MIN_CHARS = 12

#: Numerals to ignore before asking whether a claim's numbers are in the statement.
#: Each is a POINTER to somewhere else in the corpus, not a quantity the theorem
#: asserts, so requiring it in the type would guarantee a false positive.
_CLAIM_NUMERAL_NOISE = (
    re.compile(r"§+\s*\d+(?:\.\d+)*"),                            # §7.3, §§4.2
    re.compile(r"\b(?:19|20)\d\d\b"),                             # citation years
    re.compile(r"\b[Ww]ave[-\s]?\d+[A-Za-z.]*"),                  # Wave 6v.4
    re.compile(r"\b[Pp]hase[-\s]?\d+[A-Za-z.]*"),                 # Phase 6a
    re.compile(r"\b(?:Lemma|Thm|Theorem|Eq|Prop|Proposition|Cor|Corollary|Def|"
               r"Definition|Sec|Section|Fig|Figure|Table|Ch|Chapter|App|Appendix|"
               r"Tier|Route|Step|Item|Gate|Closure|TODO-D)\.?\s*\d+(?:\.\d+)*",
               re.I),
)

#: A numeral worth asking about: a decimal, or two or more digits. Single digits 0-9
#: are excluded DELIBERATELY and the exclusion is measured, not guessed — an elaborated
#: Lean type writes small literals through `OfNat`/`One`/`Zero` and prose uses them as
#: enumeration ("EFFECT 1", "2+1D", "|beta|^2"). Including them took the population
#: from 31 to 159 on 2026-08-15, essentially all noise.
_CLAIM_NUMERAL_RE = re.compile(r"(?<![\w.^])(\d+\.\d+|\d{2,})(?![\w])")

#: Apex claims whose numerals are not found in the statement they describe.
#: **A RATCHET: may only shrink.**
#:
#: MEASURED 2026-08-15: **31 of 639 declared apex claims** across 12 bundles. The
#: measurement is one-hop: a numeral counts as present if it appears in the theorem's
#: own elaborated type OR in the type of any declaration that type references.
#:
#: ⚠️ **AN ENTRY HERE IS A POINTER TO CHECK, NOT A PROVEN DEFECT, and the ratchet is
#: why that is honest.** `lean_deps.json` carries types, not definition BODIES, so a
#: numeral that lives inside a `def`'s value — `G_N_sakharov = 12π/(N_f Λ²)` — is
#: invisible to any depth of type walk, and its claim lands here while being perfectly
#: correct. What the number DOES say is how many published claims assert a quantity
#: that no machine-readable statement in their chain carries, and that can only be
#: strengthened. Lower it by restating the claim over what the theorem proves, or by
#: proving the quantity; never by widening the noise list above.
APEX_CLAIM_NUMERAL_CEILING = 31

#: Down-only floor on how many apex claims this check actually SCORES.
#:
#: MEASURED 2026-08-15: **639**, every declared apex across all 21 bundles, all of which
#: resolve.
#:
#: ⚠️ **THE POPULATION FLOOR (§2.5).** The three legs above are universals over a
#: bundle-supplied set, so anything that quietly shrinks that set — a metadata key
#: renamed, `lean_deps.json` regenerated without a module, the resolution skip widening —
#: makes them hold over fewer and fewer rows while still reporting a clean pass. The
#: violations were ratcheted from the start; the POPULATION was not, and that is the half
#: that rots silently. Lower it only with a stated reason.
APEX_CLAIMS_SCORED_FLOOR = 639


@register_check(
    "apex_theorem_claims_grounded",
    "Every declared apex theorem's `claims` prose is present, is not a restatement of "
    "the theorem's own name, and its numerals appear in the statement (ratcheted)")
def check_apex_theorem_claims_grounded() -> CheckResult:
    """CHECK: `bundle_metadata.json.apex_theorems[*].claims` was read by NOTHING.

    ## Scope — and what already owns the rest

    ⛔ **This check does NOT resolve apex names and does not judge their kind.**
    `bundle_apex_resolves` owns both, hard-failing on an apex that names no live
    declaration and on one that resolves to something other than a theorem. Re-asserting
    either here would be the second-resolver duplication `CLAUDE.md` rule 1 names. The
    residue genuinely uncovered — measured 2026-08-15, and the reason this exists — is
    the **`claims` STRING**: 639 of them across the corpus, read by no check, no test
    and no reviewer agent. The L3 Stage-10 redraft found one of thirteen describing a
    theorem that does not exist in the form claimed
    (`papers/AutomatedReviews/2026-08-15-l3-stage10-redraft/L3.md` §2.3: the metadata
    said `falsifier_alpha_ADW_dependence` establishes that δ_ADW must depend on α_ADW
    rather than being free; the theorem is `1 < α_ADW → 0 < (α_ADW - 1) * Λ_UV`, which
    mentions neither the bundle nor δ).

    ## ⚠️ WHAT THIS CHECK CANNOT VERIFY — read this before quoting its silence

    **Claim-to-type equivalence is not decidable, and this check does not approximate
    it.** A green verdict here means the three properties below hold. It does NOT mean:

    * that the claim DESCRIBES the theorem. Prose and a dependent type are different
      languages; nothing mechanical adjudicates between them.
    * that the claim is TRUE of the theorem, or that it is not the *converse* of it, or
      that it is not a strictly stronger statement than the theorem supports. **The
      exact L3 §2.3 defect that motivated this check would NOT be caught by it** — that
      claim carries no numerals and is not a name-restatement, so it passes all three
      legs. Catching it needed a human reading the type beside the prose, and still does.
    * that the claim's *hypotheses* match the theorem's. A claim silently dropping a
      hypothesis is invisible here; `atlas_hypothesis_discipline` and the
      `claims-reviewer` agent's HD class are where that lives.
    * that the theorem is SUBSTANTIVE. `vacuous_statement_audit` owns that.

    So: this check's silence is evidence about three narrow properties and about
    nothing else. It exists because those three are cheap, decidable and were
    previously unmeasured — not because they add up to verification.

    ## The three legs

    1. **Present and non-placeholder** (hard fail; live population 0). A claim shorter
       than `_CLAIM_MIN_CHARS`, or opening with TODO / TBD / N/A / "see …", is a field
       nobody filled.
    2. **Not a restatement of the theorem's own name** (hard fail; live population 0).
       `claims: "critical_coupling_pos"` against `theorem critical_coupling_pos` tells a
       reader nothing they did not have. Compared on alphanumerics only, so
       `"Critical coupling pos."` is caught too.
    3. **Numerals appear in the statement** (RATCHETED at
       `APEX_CLAIM_NUMERAL_CEILING`; live population 31). See that constant for what an
       entry does and does not prove.

    Legs 1 and 2 are hard rather than ratcheted precisely BECAUSE their live population
    is zero: that is what a regression guard looks like, and a ratchet at zero is the
    same thing with a worse name. The mutation test seeds each into production metadata.
    """
    details: List[Detail] = []
    codes, _roster_err = _H.bundle_codes_or_unmeasured()
    if codes is None:
        return CheckResult(passed=False, measured=False, details=[Detail(
            "roster", False, _roster_err)])

    try:
        records = json.loads(
            (_H.PROJECT_ROOT / "lean" / "lean_deps.json").read_text())
    except (OSError, json.JSONDecodeError) as exc:
        return CheckResult(passed=False, measured=False, details=[Detail(
            "lean_deps", False,
            f"lean/lean_deps.json unreadable ({exc}) — the statements this check "
            f"compares claims against are UNAVAILABLE, so this is UNVERIFIED, not "
            f"passing. Rebuild with `lake build SKEFTHawking.ExtractDeps`.")])
    by_name = {r["name"]: r for r in records if isinstance(r, dict) and r.get("name")}

    def _statement_haystack(rec: dict) -> str:
        """The theorem's type, plus the types of the declarations it references.

        One hop, not a full closure: a numeral in the statement of something the
        statement mentions is still *in the chain a reader follows*. Deeper walks were
        measured and moved the population 34 -> 31, which does not pay for the cost or
        for the weaker meaning of a hit.
        """
        parts = [rec.get("type") or ""]
        for dep in (rec.get("type_deps_project") or []):
            d = by_name.get(dep)
            if d:
                parts.append(d.get("type") or "")
        return " ".join(parts)

    scored = 0
    placeholders: list[str] = []
    restatements: list[str] = []
    numeral_gaps: list[tuple[str, str, list[str]]] = []
    for code in codes:
        md = _read_metadata(code)
        if md is None:
            continue
        for apex in (md.get("apex_theorems") or []):
            if not isinstance(apex, dict):
                continue
            name = str(apex.get("name") or "")
            rec = by_name.get(name)
            if rec is None:
                # `bundle_apex_resolves` owns this and hard-fails on it. Skipping
                # rather than double-reporting keeps one defect to one gate — but it
                # is skipped from the SCORED population too, so this check never
                # claims coverage of an apex it could not read.
                continue
            claim = str(apex.get("claims") or "").strip()
            short = name.split(".")[-1]
            scored += 1

            if len(claim) < _CLAIM_MIN_CHARS or _CLAIM_PLACEHOLDER_RE.match(claim):
                placeholders.append(
                    f"{code}: `{short}` has claims={claim!r} — a declared apex with no "
                    f"claim is a published assertion nobody wrote")
                continue
            if (re.sub(r"[^a-z0-9]", "", claim.lower())
                    == re.sub(r"[^a-z0-9]", "", short.lower())):
                restatements.append(
                    f"{code}: `{short}` claims only its own name — the field is meant "
                    f"to say what the theorem establishes, in words a referee reads")
                continue

            probe = claim
            for noise in _CLAIM_NUMERAL_NOISE:
                probe = noise.sub(" ", probe)
            hay = _statement_haystack(rec)
            hay_compact = hay.replace(" ", "")
            missing = sorted({n for n in _CLAIM_NUMERAL_RE.findall(probe)
                              if n not in hay and n.replace(".", "") not in hay_compact})
            if missing:
                numeral_gaps.append((code, short, missing))

    if scored == 0:
        details.insert(0, Detail(
            "population", False,
            "no bundle declares a resolvable apex theorem — this check is UNVERIFIED, "
            "not passing. The field is `apex_theorems` in bundle_metadata.json"))
        return CheckResult(passed=False, measured=False, details=details)

    for r in placeholders:
        details.append(Detail("claim_placeholder", False, r))
    for r in restatements:
        details.append(Detail("claim_restates_name", False, r))

    numerals_ok = len(numeral_gaps) <= APEX_CLAIM_NUMERAL_CEILING
    for code, short, missing in numeral_gaps[:20]:
        details.append(Detail(
            "claim_numeral_absent", True,
            f"{code}: `{short}` claims {', '.join(missing)}, which appears neither in "
            f"its statement nor in the statement of anything its statement references "
            f"— check the claim against the type (it may still be correct: a numeral "
            f"inside a `def`'s VALUE is invisible to lean_deps.json)", warning=True))
    if len(numeral_gaps) > 20:
        details.append(Detail(
            "claim_numeral_absent", True,
            f"… and {len(numeral_gaps) - 20} more", warning=True))

    population_ok = scored >= APEX_CLAIMS_SCORED_FLOOR
    if not population_ok:
        details.insert(0, Detail(
            "population_floor", False,
            f"only {scored} apex claim(s) were scored, below the floor of "
            f"{APEX_CLAIMS_SCORED_FLOOR} — the population has SHRUNK, so the three legs "
            f"below are holding over fewer rows than they were written for. Find what "
            f"stopped resolving (see `bundle_apex_resolves`) before reading this "
            f"check's verdict.", measured=False))

    ok = not placeholders and not restatements and numerals_ok and population_ok
    details.insert(0, Detail(
        "summary", ok,
        f"{scored} declared apex claim(s) scored (floor {APEX_CLAIMS_SCORED_FLOOR}) — "
        f"{len(placeholders)} placeholder, "
        f"{len(restatements)} name-restatement (both gating, both zero by design), "
        f"{len(numeral_gaps)} with a numeral absent from the statement "
        f"(ceiling {APEX_CLAIM_NUMERAL_CEILING})"
        + ("" if numerals_ok else
           " — MORE PUBLISHED CLAIMS NOW ASSERT A QUANTITY NO STATEMENT IN THEIR CHAIN "
           "CARRIES. Restate the claim over what the theorem proves, or prove the "
           "quantity; do not widen the numeral-noise list"),
        warning=bool(numeral_gaps) and numerals_ok))
    return CheckResult(passed=ok, measured=population_ok, details=details)


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
    codes, _roster_err = _H.bundle_codes_or_unmeasured()
    if codes is None:
        return CheckResult(passed=False, measured=False, details=[Detail(
            "roster", False, _roster_err)])

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
    codes, _roster_err = _H.bundle_codes_or_unmeasured()
    if codes is None:
        return CheckResult(passed=False, measured=False, details=[Detail(
            "roster", False, _roster_err)])

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
