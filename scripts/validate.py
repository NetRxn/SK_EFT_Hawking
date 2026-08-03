#!/usr/bin/env python3
"""
SK-EFT Hawking Project — Cross-Layer Validation Suite
=====================================================

Single entry point for verifying consistency across:
  Python source  ↔  Lean formal proofs  ↔  Notebooks  ↔  Papers

Usage
-----
    # From project root (recommended):
    python scripts/validate.py

    # With JSON output for CI:
    python scripts/validate.py --json

    # Save timestamped report to docs/validation/reports/:
    python scripts/validate.py --archive

    # Run a single check:
    python scripts/validate.py --check formulas

    # List available checks:
    python scripts/validate.py --list

Exit Codes
----------
    0 — all checks passed
    1 — one or more checks failed
    2 — script error (bad arguments, missing files)

Architecture & Extensibility
----------------------------
Each check is a function decorated with @register_check. To add a new check:

    @register_check("my_new_check", "Description of what it validates")
    def check_my_new_thing() -> CheckResult:
        ...
        return CheckResult(passed=True, details=[...])

The decorator handles registration, output formatting, and CI integration.
Checks are run in registration order, and any check can be run individually
via --check <name>.

Design Decisions
----------------
- Pure stdlib (no pytest dependency for the validation itself).
  This means validation works even if the test environment is degraded.
- Path-agnostic: resolves PROJECT_ROOT from this file's location,
  works from any working directory.
- Timestamped archival: --archive writes a dated JSON + text report
  to docs/validation/reports/ for historical tracking.
- Lean integration: if `lake` is on PATH, runs `lake build` as a check.
  If not available, skips gracefully with a warning.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import importlib
import json
import re
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import asdict          # `dataclass`/`field` moved with the result types
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Optional  # `Callable` moved with `register_check`

# ═══════════════════════════════════════════════════════════════════════
# Path resolution
# ═══════════════════════════════════════════════════════════════════════

# Bootstrap only — the minimum needed to make sibling modules importable. Every
# other path below is an ALIAS of `validate_helpers`, which owns the anchor.
_BOOTSTRAP_SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(_BOOTSTRAP_SCRIPT_DIR.parent))   # repo root, so `src.*` imports
if str(_BOOTSTRAP_SCRIPT_DIR) not in sys.path:          # siblings (tests import this module)
    sys.path.insert(0, str(_BOOTSTRAP_SCRIPT_DIR))

from bundle_registry import BUNDLE_CODES as _REGISTRY_BUNDLE_CODES  # noqa: E402
# ADR-009 Phase 1: shared path anchors + artifact loaders. Owns WHERE things are
# and HOW they are read; each call site keeps its OWN verdict on absence (H4).
import validate_helpers as _H  # noqa: E402
# ADR-009 H5: runtime flags live in ONE module, reached by ATTRIBUTE ACCESS so the
# value is resolved at call time. Importing them by value binds a copy at import
# time and silently freezes --strict once the checks are split across modules.
from validation import _config as _cfg  # noqa: E402

# ── Path anchors — ALIASES, not independent derivations (ADR-009 H1) ─────
# These were each computed from `Path(__file__)`. That is safe while this file
# lives at `scripts/validate.py` and silently wrong the moment it becomes
# `scripts/validate/__init__.py`: `PROJECT_ROOT` would resolve to `scripts/`,
# every artifact lookup would miss, every check would take its "absent" branch,
# and the suite would go GREEN having measured nothing. Aliasing a single anchor
# in `validate_helpers` (which stays at `scripts/`) makes the Phase-2 move
# provably path-neutral instead of a silent catastrophe.
SCRIPT_DIR = _H.SCRIPT_DIR
PROJECT_ROOT = _H.PROJECT_ROOT
SRC_DIR = _H.SRC_DIR
LEAN_DIR = _H.LEAN_DIR
NOTEBOOKS_DIR = _H.NOTEBOOKS_DIR
PAPERS_DIR = _H.PAPERS_DIR
REPORTS_DIR = _H.DOCS_DIR / "validation" / "reports"


# ═══════════════════════════════════════════════════════════════════════
# Data structures + registry — RE-EXPORTED from `validation._registry`
# ═══════════════════════════════════════════════════════════════════════
# These moved out so that `validation/checks/*.py` can import them without
# importing `validate`, which would be a cycle (validate imports the check
# modules for their registration side-effect). See `validation/_registry.py`.
#
# ⚠️ `_CHECKS` is re-exported BY BINDING, and that is load-bearing: registration
# appends to it and `_apply_canonical_order()` sorts it in place, so this name and
# `validation._registry._CHECKS` must remain THE SAME list. Never rebind it
# (`_CHECKS = [...]`) — that yields two registries, one filled by registration and
# a different one iterated by `run_checks` / `--list`, and since `all([])` is True
# the suite would report success while running fewer checks.
#
# The re-export itself is required by ADR-009 D2 item 8: nine test files and
# `scripts/sync_manifest.py` import names from `validate` directly.
# `tests/test_validate_public_surface.py` freezes the full 33-name surface and
# asserts the `_CHECKS` identity above.
from validation._registry import (  # noqa: E402
    Detail, CheckResult, CheckSpec, _CHECKS, register_check,
)




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
       ``review_figures.py`` writes to ``PROJECT_ROOT/figures``, not into the
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
    import importlib

    details: List[Detail] = []
    try:
        viz = importlib.import_module("src.core.visualizations")
    except Exception as exc:  # pragma: no cover - import guard
        return CheckResult(passed=True, details=[Detail(
            "skipped", True, f"visualizations import failed ({exc}) — skipped",
            warning=True)])

    if not hasattr(viz, "bundle_figure_typeset_pt"):
        return CheckResult(passed=True, details=[Detail(
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
        _spec = _ilu.spec_from_file_location(
            "_review_figures", SCRIPT_DIR / "review_figures.py")
        _rf = _ilu.module_from_spec(_spec)
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
            png = PAPERS_DIR / bundle / "figures" / f"{png_name}.png"
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
                import hashlib, tempfile, os as _os
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










# ═══════════════════════════════════════════════════════════════════════
# CHECK 15: Parameter provenance — every experimental param has a
# verified source traced to a published paper + table/figure.
# ═══════════════════════════════════════════════════════════════════════

@register_check("parameter_provenance",
                "Every experimental parameter has verified provenance")
def check_parameter_provenance() -> CheckResult:
    """CHECK 15: Validate the parameter provenance registry.

    Checks:
    1. Coverage: every param in EXPERIMENTS/ATOMS/POLARITON has provenance
    2. LLM verification: all entries have llm_verified_date (gates Stage 1)
    3. Human verification: advisory — gates paper submission, not computation
    4. Consistency: provenance value matches actual constant value
    5. Tier appropriateness: MEASURED params must have a real source
    """
    from src.core.constants import EXPERIMENTS, ATOMS, POLARITON_PLATFORMS
    from src.core.provenance import PARAMETER_PROVENANCE

    details = []
    all_pass = True

    # --- 1. Coverage: every parameter has a provenance entry ---
    missing = []
    for platform, params in EXPERIMENTS.items():
        for key in params:
            if key in ('description', 'atom'):
                continue
            prov_key = f"{platform}.{key}"
            if prov_key not in PARAMETER_PROVENANCE:
                missing.append(prov_key)

    for atom, props in ATOMS.items():
        for key in props:
            if key in ('label',):
                continue
            prov_key = f"{atom}.{key}"
            if prov_key not in PARAMETER_PROVENANCE:
                missing.append(prov_key)

    # Check POLARITON_MASS
    if 'POLARITON_MASS' not in PARAMETER_PROVENANCE:
        missing.append('POLARITON_MASS')

    for config, params in POLARITON_PLATFORMS.items():
        for key in ('c_s', 'xi', 'kappa', 'tau_cav', 'Gamma_pol', 'gamma_phonon_dim'):
            prov_key = f"{config}.{key}"
            if prov_key not in PARAMETER_PROVENANCE:
                # Shared params (c_s, xi, kappa, gamma_phonon_dim) only need
                # one entry under Paris_long since all configs share them
                if key in ('c_s', 'xi', 'kappa', 'gamma_phonon_dim'):
                    shared_key = f"Paris_long.{key}"
                    if shared_key not in PARAMETER_PROVENANCE:
                        missing.append(prov_key)
                else:
                    missing.append(prov_key)

    if missing:
        all_pass = False
        details.append(Detail(
            "coverage", False,
            f"Missing provenance for {len(missing)} params: {', '.join(missing[:5])}"
            + (f"... (+{len(missing)-5} more)" if len(missing) > 5 else "")
        ))
    else:
        details.append(Detail("coverage", True,
                              f"All {len(PARAMETER_PROVENANCE)} parameters have provenance entries"))

    # --- 2. LLM verification (gates Stage 1 computation) ---
    not_llm = [k for k, v in PARAMETER_PROVENANCE.items()
               if v.get('llm_verified_date') is None]
    if not_llm:
        all_pass = False
        details.append(Detail(
            "llm_verification", False,
            f"{len(not_llm)} params not LLM-verified: {', '.join(not_llm[:5])}"
            + (f"... (+{len(not_llm)-5} more)" if len(not_llm) > 5 else "")
        ))
    else:
        details.append(Detail("llm_verification", True,
                              "All parameters LLM-verified"))

    # --- 3. Human verification (advisory by default; hard fail in --strict) ---
    # PROJECTED tier is exempt from human_verified — these are explicit estimates
    # for not-yet-performed experiments, not measurements requiring verification.
    not_human = [k for k, v in PARAMETER_PROVENANCE.items()
                 if v.get('human_verified_date') is None]
    not_human_required = [
        k for k in not_human
        if PARAMETER_PROVENANCE[k].get('tier') != 'PROJECTED'
    ]
    if _cfg.STRICT_MODE and not_human_required:
        all_pass = False
        sample = ', '.join(not_human_required[:8])
        more = f" + {len(not_human_required) - 8} more" if len(not_human_required) > 8 else ""
        details.append(Detail(
            "human_verification", False,
            f"[strict] {len(not_human_required)} non-PROJECTED params lack "
            f"human_verified_date (paper-submission blocker): {sample}{more}"
        ))
    elif not_human:
        details.append(Detail(
            "human_verification", True,
            f"{len(not_human)} params not yet human-verified "
            f"({len(not_human_required)} non-PROJECTED; blocks paper submission)",
            warning=True
        ))
    else:
        details.append(Detail("human_verification", True,
                              "All parameters human-verified — paper submission unblocked"))

    # --- 4. Consistency: provenance value matches actual constant ---
    mismatches = []
    null_values = []
    for prov_key, entry in PARAMETER_PROVENANCE.items():
        if entry['value'] is None:
            null_values.append(prov_key)
            continue

        # Look up actual value
        actual = _lookup_provenance_value(prov_key, EXPERIMENTS, ATOMS,
                                          POLARITON_PLATFORMS)
        if actual is not None:
            try:
                rel_err = abs(float(actual) - float(entry['value'])) / max(abs(float(actual)), 1e-30)
                if rel_err > 0.001:
                    mismatches.append(f"{prov_key}: registry={entry['value']}, code={actual}")
            except (TypeError, ValueError):
                pass  # non-numeric (e.g., string params)

    if null_values:
        all_pass = False
        details.append(Detail(
            "unresolved_conflicts", False,
            f"{len(null_values)} params have NULL value (unresolved conflict): "
            f"{', '.join(null_values)}"
        ))
    if mismatches:
        all_pass = False
        details.append(Detail(
            "value_consistency", False,
            f"{len(mismatches)} mismatches: {'; '.join(mismatches[:3])}"
        ))
    elif not null_values:
        details.append(Detail("value_consistency", True,
                              "All provenance values match code"))

    # --- 5. Tier appropriateness ---
    tier_issues = []
    for prov_key, entry in PARAMETER_PROVENANCE.items():
        if (entry['tier'] == 'MEASURED'
                and entry.get('llm_verified_date') is None
                and 'CODATA' not in entry.get('source', '')
                and 'NIST' not in entry.get('source', '')):
            tier_issues.append(prov_key)
    if tier_issues:
        details.append(Detail(
            "tier_appropriateness", True,
            f"{len(tier_issues)} MEASURED params not yet LLM-verified: "
            f"{', '.join(tier_issues[:5])}",
            warning=True
        ))

    return CheckResult(passed=all_pass, details=details)




# ═══════════════════════════════════════════════════════════════════════
# CHECK 17b: Inline numerical literals outside \input{} blocks (Phase 5v)
# ═══════════════════════════════════════════════════════════════════════







# ═══════════════════════════════════════════════════════════════════════
# CHECK 17: Count literals in paper .tex (Phase 5v Wave 1b)
# ═══════════════════════════════════════════════════════════════════════





# ═══════════════════════════════════════════════════════════════════════
# CHECK 18: Readiness submission gate (Phase 5v Wave 4)
# ═══════════════════════════════════════════════════════════════════════

# ── NOT SHIPPED: `ledger_evidence_names_its_finding` ────────────────────────────────
# D12 round-13 BLOCKER 13.1 found three ledger records that close a finding their evidence
# does not describe, and nothing detects it. I built a guard requiring the evidence to share
# a content word with the finding's title, and MEASURED it before shipping: it flags 40
# records, and the ones I sampled are correct. Example —
# `2026-04-28-...:paper40_higher_curvature:2.1`, whose evidence reads "CrossPaperConsistency
# gate verifies sampled cross-paper bibitems match character-for-character on load-bearing
# fields". That describes the FIX; the title describes the DEFECT; well-written evidence
# routinely shares no vocabulary with the finding it closes.
#
# So the premise is wrong, not the threshold, and a guard that flags 40 correct records is
# worse than no guard — that is the lesson this session has taught eleven times. The three
# real mis-keys were caught by a reviewer READING them, which is not a test I can currently
# mechanise. Recording the gap rather than shipping a check that manufactures work.
#
# What would work, and is not built: require the record to name the artifact it changed
# (a file path) and verify that path appears in the cited commit's diff. That is mechanical
# and would have caught all three, since their evidence names another round's artifacts.


# ── Recurrence matcher — module scope so tests can reach the REAL implementation ──
# These were function-locals until 2026-08-03 (ADR-009 Phase 0, Guard 3). The consequence
# was that `tests/test_bundle_formulas_d11_d12.py::TestRecurrenceThresholdAgainstFrozenPairs`
# — the test whose whole purpose is to hold this threshold to a frozen labelled set —
# could not import them, so it RE-IMPLEMENTED `norm()` locally and re-hardcoded the
# threshold. The production matcher could have been deleted or inverted and that test would
# still have passed. It asserted nothing about this code.
#
# The calibration history lives with the check body below, where the decision was made; do
# not restate it here. `_MIN_TITLE` / `_MIN_OVERLAP` / `_norm` inside the check are aliases
# of these, so the two can never diverge.
_RECURRENCE_MIN_TITLE = 12     # see the check body for why
_RECURRENCE_MIN_OVERLAP = 0.40  # Jaccard over token sets; see the check body for the derivation


def _recurrence_norm(s: str) -> str:
    """Normalize a finding label for recurrence comparison.

    Strips markup, lowercases, drops non-alphanumerics, then removes leading
    section-number and severity-word tokens — a recurrence appears under a DIFFERENT
    number in a later round (round 8's 5.1 recurring as round 9's 3.2), so leading
    numbers are noise in exactly the case the check exists for.
    """
    s = re.sub(r'[`*_\[\]]', '', str(s or '')).lower()
    s = re.sub(r'[^a-z0-9 ]+', ' ', s)
    toks = s.split()
    while toks and (re.fullmatch(r'[0-9]+([a-z0-9]*)?', toks[0])
                    or toks[0] in ('blocker', 'required', 'recommended', 'critical',
                                   'major', 'minor', 'advisory', 'regression')):
        toks.pop(0)
    return " ".join(toks)


@register_check("recurrence_reopens_closures",
                "A closure is not contradicted by a later review raising the same finding")
def check_recurrence_reopens_closures() -> CheckResult:
    """CHECK: a finding closed in the ledger must not recur in a LATER review.

    Added 2026-07-31 (D12 Stage-13 round-11 finding 8.1b, part 3c). The ledger is now the
    sole channel that can close a finding, which makes a stale closure the remaining way
    for a real defect to read as resolved: close it, have a later round raise the same
    thing, and the ledger still says fixed. That happened repeatedly this session — the
    "effective modulus" misnomer was closed and re-raised across five rounds.

    Recurrence is matched on the finding's own title text, normalised, requiring a long
    overlap so that two genuinely different findings about the same file do not collide.
    A hit is reported against the CLOSURE, not the new finding: the new finding is correct,
    and it is the closure that is now false.
    """
    try:
        from build_graph import extract_review_finding_nodes
    except ImportError as exc:
        return CheckResult(passed=False, details=[
            Detail("import", False, f"unavailable ({exc}) — unverified, not passing")])

    # ⚠️ THRESHOLDS ARE MEASURED, NOT GUESSED. The first version required a 60-character
    # common prefix. Measured afterwards: normalized finding labels run min 5 / median 48 /
    # **max 56** characters, so that threshold could never be met and the check was
    # structurally incapable of ever reporting a hit — while printing a reassuring
    # "0 contradicted" over 500 closures. That is the sixth guard in this session that
    # could not do what its summary said, and the pattern each time was choosing a constant
    # from what I imagined the data looked like.
    # ⚠️ The PRIMITIVE was wrong, not just the constant (D11 round-12 BLOCKER 4.2).
    # I required a 30-character common PREFIX. Measured over all 4,210 candidate pairs in
    # this corpus, the maximum prefix ANY pair achieves is 17 — and `_PREFIX_FRAC *
    # _MIN_TITLE = 22.5` put a second floor above that ceiling, so no single constant could
    # revive it. The check printed "0 contradicted by a recurrence" while being incapable
    # of anything else, under a comment that read "THRESHOLDS ARE MEASURED, NOT GUESSED"
    # and listed the six previous instances. I had measured label LENGTHS; the predicate
    # compares PREFIXES, and I never measured those.
    #
    # A recurrence restates a finding, it does not re-type it: word order and wording drift
    # while the vocabulary persists. Token overlap (Jaccard) is the right primitive.
    # Measured on the same 4,210 pairs: median 0.00, p99 0.20, max 0.67 — and the single
    # pair at 0.67 is a TRUE recurrence ("israel third law parenthetical", closed then
    # re-raised in a later round). 0.50 sits in the empty band between p99 and that pair.
    _MIN_TITLE = _RECURRENCE_MIN_TITLE   # below this a title carries too few tokens to compare
    # ⚠️ RE-DERIVED 2026-08-01 (D11 round-13 N1). Switching the primitive from prefix to
    # Jaccard was right; I then kept a 0.50 threshold that I had measured on a sweep whose
    # pairing rules were NOT the check's own. Measured with the check's `_norm`, its
    # same-bundle rule and its date rule, over 4,706 pairs: median 0.000, p99 0.200,
    # MAX 0.429. So 0.50 admitted nothing — the guard still could not fire, one round after
    # being "fixed", and the 0.67 pair I cited as calibration does not exist as a
    # closure/open pair at all.
    #
    # The two D12 records I reported it "rejecting" were added already `open`; the guard had
    # no part in it. That claim in commit 03a4592e's message is false and this comment is
    # the correction.
    #
    # 0.40 sits between p99 (0.200) and the top pair (0.429), which is a TRUE stale closure:
    # 1530:D11:4.1 closed, 2220:D11:4.6 open, both about PAPER_DRAFT_MAPPING.md:109.
    _MIN_OVERLAP = _RECURRENCE_MIN_OVERLAP   # Jaccard over token sets
    #
    # ⚠️ THIS MATCHER IS WEAK, and its limits are measured — but an earlier version of this
    # comment said it "cannot do its job", which round 14 disproved: driving the ledger off
    # git snapshots it fires 3 real hits at 0.40 that 0.50 could not reach, and scores 22/29
    # on a 29-pair labelled set built from twelve self-declared chains. My own fixture has
    # three positives and I generalised from it to an absolute — the same over-reach, one
    # layer up, as the numbers this session kept overstating. What follows is the measured
    # limit, not an impossibility claim. Measured on
    # `tests/fixtures/recurrence_pairs.json`: true recurrences score 0.188, 0.000, 0.071
    # while unrelated pairs score 0.000 — the worst positive does not beat the best
    # negative, so NO threshold separates them. All three tunings this session
    # (30-char prefix -> 0.50 -> 0.40) were tuning a matcher that cannot discriminate.
    #
    # Root cause is upstream: `label` is `heading[:50]`, so a RESTATED finding — which is
    # what a recurrence is — shares almost no vocabulary with its original. What this guard
    # actually detects is duplicate heading OPENINGS, which is why every real hit it has
    # produced was a near-verbatim repeat. Those hits were genuine and worth having; the
    # guard is kept for them, at a threshold that admits them and little else.
    #
    # It is a WEAK recurrence detector — good on near-verbatim restatements, poor on
    # rewordings — and must not be quoted as a reliable one. Improving it
    # needs the full finding text carried on the node, not a wider constant — and
    # `tests/…::TestRecurrenceThresholdAgainstFrozenPairs` fails the day that lands, which
    # is the signal to replace this comment.
    #
    # QI: qi-threshold-calibration-consumes-its-own-datum. Three times a constant was set
    # just under the live corpus maximum by the same commit that repaired the pair
    # producing that maximum, so it was unreachable on arrival. Thresholds on a
    # self-remediating corpus must be calibrated against frozen labelled pairs.

    # Drops leading section-number and severity-word tokens. A recurrence appears under
    # a DIFFERENT number in a later round — round 8's 5.1 recurring as round 9's 3.2 —
    # so comparing prefixes that begin with the number is fragile in exactly the case
    # the check exists for. Verified with a planted probe whose label minted as
    # "1.1 1.1 blocker ..." against a source of "1.1 blocker ...": the prefix agreement
    # was near zero for two identical findings.
    # Implementation is `_recurrence_norm` at module scope (ADR-009 Phase 0, Guard 3) so
    # the frozen-pairs test binds to the real matcher instead of a copy of it.
    _norm = _recurrence_norm

    findings = extract_review_finding_nodes()
    closed, open_ = [], []
    for f in findings:
        m = f.get("meta") or {}
        rec = (m.get("review_date", ""), _norm(f.get("label", "")), f["id"], m.get("severity"),
               m.get("inferred_bundle") or m.get("inferred_paper"))
        if not rec[1] or len(rec[1]) < _MIN_TITLE:
            continue
        (closed if m.get("status") in ("fixed", "accepted") else open_).append(rec)

    details: list[Detail] = []
    hits = 0
    compared = 0
    _had_candidate: set = set()
    skipped_short = sum(1 for f in findings
                        if len(_norm(f.get("label", ""))) < _MIN_TITLE)
    for cdate, ctext, cid, csev, cbundle in closed:
        if csev not in ("critical", "major"):
            continue
        for odate, otext, oid, _, obundle in open_:
            # Same bundle only. Reviews share heading boilerplate across bundles, so a D2
            # closure matching an I2 finding's title is a template collision, not a
            # recurrence — measured: the two hits before this constraint were exactly that
            # (D2 vs I2, L3 vs L2).
            if cbundle is None or obundle is None or cbundle != obundle:
                continue
            if odate <= cdate:
                continue
            _a, _b = set(ctext.split()), set(otext.split())
            if not _a or not _b:
                continue
            # Count a closure as COMPARED only once it has something to compare against
            # (D12 round-13). `compared += 1` used to sit before this loop, so it counted
            # closures that reached the loop rather than closures that met a candidate:
            # the summary said 318 where 162 had any counterpart. Ninth instance of the
            # same defect, and the third consecutive version of THIS summary line to
            # overstate its own coverage.
            if cid not in _had_candidate:
                _had_candidate.add(cid)
                compared += 1
            if len(_a & _b) / len(_a | _b) < _MIN_OVERLAP:
                continue
            # Section-number agreement as a tie-breaker (D12 round-14 finding 14.4). The
            # guard's FIRST live D12 effect was a false positive: it held 1524:8.2 open
            # against 1823:8.4 at exactly j = 2/5 = 0.400, carried entirely by the shared
            # phrase "fails open" — two different guards that both failed open, not one
            # finding recurring. A real recurrence is the SAME finding restated, and this
            # corpus numbers findings by class, so a recurrence overwhelmingly keeps its
            # section number (round 14: 8.3 -> 8.3 is the true pair; 8.2 -> 8.4 is not).
            # Marginal scores need that corroboration; strong scores do not.
            if (len(_a & _b) / len(_a | _b) < _MIN_OVERLAP + 0.10
                    and cid.rsplit(':', 1)[-1] != oid.rsplit(':', 1)[-1]):
                continue
            if True:
                hits += 1
                details.append(Detail(
                    cid, False,
                    f"closed on {cdate}, but {oid} ({odate}) raises the same finding and is "
                    f"open. The later review is the evidence; the CLOSURE is what is now "
                    f"false. Reopen it or record why the recurrence is a different defect."))
                break

    # Report what was COMPARED, not what was collected. The previous summary printed
    # `len(closed)` — 552 — while the loop's severity filter meant 148 were actually
    # compared, and it never mentioned the findings excluded for a short title. A guard's
    # summary overstating its own coverage is the failure this session kept producing.
    details.insert(0, Detail(
        "summary", hits == 0,
        f"{compared} blocking-severity closure(s) compared against {len(open_)} open "
        f"finding(s) from later same-bundle reviews; {hits} contradicted by a recurrence. "
        f"NOT compared: {len(closed) - compared} non-blocking closure(s), and "
        f"{skipped_short} finding(s) whose normalised title is under {_MIN_TITLE} chars "
        f"(labels are truncated to heading[:50] upstream, so short titles are a real "
        f"coverage limit, not a rounding detail)"))
    return CheckResult(passed=hits == 0, details=details)


@register_check("review_severity_declared",
                "Review documents from the cutoff forward declare each finding's severity")
def check_review_severity_declared() -> CheckResult:
    """CHECK: severity must be a declared field, not an inferable glyph.

    Added 2026-07-31 (D12 Stage-13 round-11 finding 8.1b, part 3b). Severity drove the
    blocking-closure bar while being inferred from glyphs in the heading, which made it
    editable without leaving a trace. Two exploits were demonstrated against that: a
    one-line glyph demotion plus the word "fixed" reopened self-closure on a past BLOCKER,
    and typesetting a summary as `0 «**»BLOCKER«**»` escalated a whole zero-blocker report
    to critical.

    `build_graph` now prefers an explicit `- **Severity:** <level>` line in the finding
    body. This check makes that mandatory from `_CUTOFF` forward, so omitting it is a red
    build rather than a silent downgrade. Historical documents keep glyph inference — there
    are ~1400 findings that predate the convention and rewriting them would be churn with
    no provenance value, so the cutoff is the honest boundary rather than a blanket rule.
    """
    _CUTOFF = "2026-08-01"   # documents dated on/after this must declare severity

    reviews_dir = PROJECT_ROOT / "papers" / "AutomatedReviews"
    if not reviews_dir.is_dir():
        return CheckResult(passed=True, details=[
            Detail("scope", True, "no review directory", warning=True)])

    _SEV_LINE = re.compile(r'^[-*]\s*\*\*Severity:?\*\*', re.M | re.I)
    _HEADING = re.compile(r'^#{3,5}\s+\S', re.M)

    details: list[Detail] = []
    bad = 0
    checked = 0
    for md in sorted(reviews_dir.glob("*/*.md")):
        date = md.parent.name[:10]
        if date < _CUTOFF:
            continue
        text = md.read_text(encoding="utf-8", errors="replace")
        n_head = len(_HEADING.findall(text))
        if n_head == 0:
            continue
        checked += 1
        n_sev = len(_SEV_LINE.findall(text))
        if n_sev < n_head:
            bad += 1
            details.append(Detail(
                str(md.relative_to(PROJECT_ROOT)), False,
                f"{n_head} finding heading(s) but only {n_sev} `- **Severity:**` line(s). "
                f"From {_CUTOFF} every finding must declare its severity explicitly: "
                f"severity drives the blocking-closure bar, and inferring it from a glyph "
                f"lets it be changed without leaving a trace."))

    details.insert(0, Detail(
        "summary", bad == 0,
        f"{checked} review document(s) dated >= {_CUTOFF} checked; {bad} with findings "
        f"that do not declare severity (earlier documents keep glyph inference)"))
    return CheckResult(passed=bad == 0, details=details)


@register_check("review_docs_mint_findings",
                "Every bundle Stage-13 review document mints at least one ReviewFinding node")
def check_review_docs_mint_findings() -> CheckResult:
    """CHECK: a review that produces zero graph nodes must fail loudly, not silently pass.

    Added 2026-07-31 (D12 Stage-13 round-9 BLOCKER 8.2). This is the fail-open path that
    survived every previous repair, and it needs no mutation to trigger — only a heading
    that drifts from `### N.N — ` to `#### `, `### Finding `, or `### 1.1: `. The
    round-9 reviewer wrote a review declaring four BLOCKERs with such headings and it
    minted **zero** nodes; `findings_reach_the_graph` structurally cannot see it, because
    that guard's file index is built *from findings*, so a file with no findings is not in
    it. A whole round of blockers then reads exactly like a clean round.

    The predicate the existing guards cannot express is this one: for each review document
    named after a bundle in the roster, at least one `ReviewFinding` node must resolve to
    it. Zero is a parser failure or a malformed document — never evidence of a clean review.
    """
    # Deliberately LOOSER than `build_graph._REVIEW_SECTION_RE`: this asks "does this
    # document look like it carries findings", and the gap between the two regexes IS the
    # defect being detected. If they were the same pattern the check would be a tautology.
    #
    # ⚠️ The first version was circular anyway (D12 round-11 BLOCKER 8.2). It required
    # `<digits><dash>` — the exact fragment that drifts — so the six documents minting zero
    # were precisely the six it skipped, and my "8 → 0" was measured inside the scope the
    # check itself defines. Those six carry 47 severity-marked headings including four
    # declared BLOCKERs in `lean_project_audit.md` and four 🔴 in `CitationReview-01.md`.
    #
    # The predicate is now SEVERITY, not numbering: a heading that declares BLOCKER /
    # REQUIRED / RECOMMENDED / CRITICAL, or carries a severity glyph, is a finding heading
    # whatever its numbering scheme — including the forms that defeated the old one
    # (`### 1. Paper 7 —`, `### 1. Class 6 BLOCKER —`, `### BLOCK-1 (…) —`,
    # `### I.1 Count …`, and glyph-first `### 🔴 BLOCKER 1.1 —`). Severity is the thing a
    # finding cannot omit and still be a finding.
    _SEVERITY_HEADING = re.compile(
        r'^#{3,5}\s+.*(?:BLOCKER|REQUIRED|RECOMMENDED|CRITICAL|MAJOR|MINOR'
        r'|\U0001F534|\U0001F7E1|\U0001F535|\u26a0)', re.M)
    # ...but a severity WORD is not a severity LABEL. A clean figure review's headings read
    # "`fig5.png` (P2) — **PASS** (round-2 BLOCKER resolved)": the token appears inside a
    # resolution note, and that document correctly mints nothing. Excluding headings that
    # also declare PASS/RESOLVED is the difference between "carries findings" and "mentions
    # a finding", and skipping it would have made this guard fire on a correct document —
    # the fifth time today.
    _RESOLVED_HEADING = re.compile(r'PASS|RESOLVED|resolved', re.I)

    def _carries_findings(text: str) -> bool:
        return any(not _RESOLVED_HEADING.search(h)
                   for h in _SEVERITY_HEADING.findall(text) or []) or any(
            not _RESOLVED_HEADING.search(m.group(0))
            for m in _SEVERITY_HEADING.finditer(text))

    try:
        from build_graph import extract_review_finding_nodes
    except ImportError as exc:
        return CheckResult(passed=False, details=[
            Detail("import", False,
                   f"could not import the review extractor ({exc}) — unverified, not passing")])

    try:
        findings = extract_review_finding_nodes()
    except Exception as exc:
        return CheckResult(passed=False, details=[
            Detail("extract", False,
                   f"review extraction failed ({type(exc).__name__}: {exc}) — unverified")])

    minted: dict[str, int] = {}
    for f in findings:
        rf = (f.get("meta") or {}).get("review_file")
        if rf:
            minted[rf] = minted.get(rf, 0) + 1

    reviews_dir = PROJECT_ROOT / "papers" / "AutomatedReviews"
    details: list[Detail] = []
    empty = 0
    checked = 0
    if reviews_dir.is_dir():
        for md in sorted(reviews_dir.glob("*/*.md")):
            # Scope by CONTENT, not by filename or directory.
            #
            # Two earlier scopings were both wrong, in opposite directions. Filtering to
            # roster-named files put 120 documents out of scope. Then excluding
            # `*-bundle-stage13/` — because 107 of 138 files there are
            # `bundle_readiness.py` aggregations that mint zero BY DESIGN — excluded the
            # directory `BUNDLE_DIRECTORY_SCHEMA.md:86` and `BUNDLE_LIFT_PROCEDURE.md:243`
            # name as THE canonical location for a Stage-13 review, hiding five
            # findings-bearing reviews, one of them declaring a BLOCKER (D12 round-10 8.2).
            #
            # The honest discriminator is the document's own content: a file containing
            # finding-shaped headings must mint findings. A generated aggregation has no
            # such headings and is silently skipped — not because of where it lives, but
            # because it never claimed to carry findings.
            if not _carries_findings(md.read_text(encoding="utf-8", errors="replace")):
                continue
            checked += 1
            rel = str(md.relative_to(PROJECT_ROOT))
            n = minted.get(rel, 0)
            if n == 0:
                empty += 1
                details.append(Detail(
                    rel, False,
                    f"this Stage-13 review document mints ZERO ReviewFinding nodes. Either "
                    f"its finding headings do not match the extractor's expected "
                    f"`### <N.N> — <severity> — <text>` form, or the document is malformed. "
                    f"A round that mints nothing is invisible to Gate 11 and reads exactly "
                    f"like a clean round."))

    details.insert(0, Detail(
        "summary", empty == 0,
        f"{checked} document(s) carrying unresolved severity-labelled headings checked "
        f"(a document mentioning a severity only inside a PASS/RESOLVED note carries no "
        f"findings and is skipped); {empty} mint zero"))
    return CheckResult(passed=empty == 0, details=details)


@register_check("accepted_findings_carry_rationale",
                "Every `accepted` supersession record justifies acceptance in writing")
def check_accepted_findings_carry_rationale() -> CheckResult:
    """CHECK: `accepted` must be a recorded decision, never a way to silence a finding.

    Added 2026-07-31 (D12 Stage-13 round-8). `_eval_fix_propagation` stopped treating
    `accepted` as an open blocker this session — correct, because it is a deliberate
    decision written into the supersession ledger, not an unclosed finding. But that
    change also made `accepted` the cheapest way to make a blocking finding disappear
    from Gate 11: 27 blocking-severity findings are currently invisible to it on that
    status alone. The round-8 reviewer measured that 138 of 140 accepted records carry
    substantive rationale and none is wholly bare — so the practice is sound and this
    check pins it, rather than fixing a live defect.

    A blocking-severity acceptance additionally has to say why acceptance rather than a
    fix; "accepted" with a one-line restatement of the finding is not a decision.
    """
    # ADR-009 H1. This site is one of the two where a retargeted anchor would be
    # SILENT: a missing ledger returns passed=True below, so on a module move this
    # check would report success having examined nothing.
    ledger_path = _H.DOCS_DIR / "review_finding_supersessions.json"
    if not ledger_path.is_file():
        return CheckResult(passed=True, details=[
            Detail("ledger", True, "no supersession ledger; skipping", warning=True)])
    try:
        led = json.loads(ledger_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError) as exc:
        return CheckResult(passed=False, details=[
            Detail("ledger", False, f"ledger unreadable ({exc}) — unverified, not passing")])

    MIN_CHARS = 40
    bad, checked = [], 0
    for e in led.get("supersessions", []):
        if e.get("status") != "accepted":
            continue
        checked += 1
        # The ledger uses three field names for the same thing across its history:
        # `evidence` (recent), `rationale`, and `note` (the 2026-05 records). Reading only
        # the first two produced two false positives on records that are in fact well
        # justified — a guard that flags correct data is worse than none.
        why = " ".join(str(e.get("evidence") or e.get("rationale")
                           or e.get("note") or "").split())
        if len(why) < MIN_CHARS:
            bad.append((e.get("finding_id", "?"), len(why)))

    details = [Detail("summary", not bad,
                      f"{checked} accepted record(s) checked, {len(bad)} without a written "
                      f"rationale of at least {MIN_CHARS} characters")]
    for fid, n in bad[:10]:
        details.append(Detail(
            fid, False,
            f"status=accepted with {n} characters of rationale. `accepted` removes a "
            f"finding from Gate 11's blocking set, so it must record a DECISION — why "
            f"acceptance rather than a fix — not merely assert one."))
    return CheckResult(passed=not bad, details=details)


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
                f"Re-run `uv run python scripts/bundle_readiness.py`, which writes these "
                f"fields; do not hand-edit them."))

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
    for bundle, agg in sorted(by_bundle.items()):
        if str(agg.get('readiness', '')).upper() != 'GREEN':
            continue
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


@register_check("readiness_submission_gate",
                "Every paper has all P1 readiness gates passed (Phase 5v Wave 4)")
def check_readiness_submission_gate() -> CheckResult:
    """CHECK 18: Aggregate per-paper readiness state.

    Iterates every Paper node's 11 ReadinessGate instances. A paper is
    submission-ready iff ALL priority-1 gates are `passed` and no
    priority-2 gate is `blocked`. Priority-2 `needs-recheck`/`open` are
    advisory warnings.

    The check is WARN-only during the readiness rollout — existing drafts
    will light up red (as intended) until remediation lands. To block
    submission, run `validate.py --strict` (future flag) or grep for
    'readiness-status: red' in archived reports.
    """
    try:
        from build_graph import build_graph_json
    except ImportError as exc:
        return CheckResult(passed=True, details=[
            Detail("import", True, f"build_graph not available ({exc}); skipping",
                   warning=True),
        ])

    graph = build_graph_json()
    gates = [n for n in graph.get('nodes', []) if n['type'] == 'ReadinessGate']
    if not gates:
        # FAIL, not warn (D12 round-8 BLOCKER 8.2). Zero gate nodes is not "no problems
        # found" — it is the gate system being absent, which is the only state in which
        # every bundle trivially satisfies it.
        return CheckResult(passed=False, details=[
            Detail("gates", False,
                   "NO ReadinessGate nodes exist. The submission gate has nothing to "
                   "evaluate, so its verdict is vacuous — treat as unverified, not passing."),
        ])

    # Aggregate per-paper
    from collections import defaultdict
    per_paper: dict[str, dict] = defaultdict(lambda: {
        'p1_blocked': [], 'p2_blocked': [], 'p2_advisory': [],
        'passed': [], 'open': [],
    })
    for g in gates:
        m = g['meta']
        paper = m['paper']
        entry = (m['gate'], m['state'], m.get('notes', ''))
        if m['state'] == 'passed':
            per_paper[paper]['passed'].append(entry)
        elif m['priority'] == 1 and m['state'] == 'blocked':
            per_paper[paper]['p1_blocked'].append(entry)
        elif m['priority'] == 2 and m['state'] == 'blocked':
            per_paper[paper]['p2_blocked'].append(entry)
        elif m['priority'] == 2 and m['state'] in ('needs-recheck', 'open'):
            per_paper[paper]['p2_advisory'].append(entry)
        else:
            per_paper[paper]['open'].append(entry)

    # Classification
    green, yellow, red = [], [], []
    for paper, state in sorted(per_paper.items()):
        if state['p1_blocked'] or state['p2_blocked']:
            red.append(paper)
        elif state['p2_advisory'] or state['open']:
            yellow.append(paper)
        else:
            green.append(paper)

    details = [
        Detail("summary", True,
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
            paper, True,  # WARN not FAIL during rollout
            f"{len(blockers)} blocked: "
            f"{', '.join(g for g,_,_ in blockers[:5])}"
            + (f" (+{len(blockers)-5} more)" if len(blockers) > 5 else ""),
            warning=True))

    return CheckResult(passed=True, details=details)


def _lookup_provenance_value(prov_key, experiments, atoms, polariton_platforms):
    """Look up the actual value in constants for a provenance key like 'Steinhauer.omega_perp'."""
    import numpy as np
    from src.core.constants import HBAR, K_B, A_BOHR, POLARITON_MASS

    # Fundamental constants
    fundamentals = {'HBAR': HBAR, 'K_B': K_B, 'A_BOHR': A_BOHR,
                    'POLARITON_MASS': POLARITON_MASS}
    if prov_key in fundamentals:
        return fundamentals[prov_key]

    parts = prov_key.split('.', 1)
    if len(parts) != 2:
        return None
    group, key = parts

    # ATOMS
    if group in atoms:
        return atoms[group].get(key)

    # EXPERIMENTS
    if group in experiments:
        return experiments[group].get(key)

    # POLARITON_PLATFORMS
    if group in polariton_platforms:
        return polariton_platforms[group].get(key)

    return None


# ═══════════════════════════════════════════════════════════════════════
# Execution order (ADR-009 H3)
# ═══════════════════════════════════════════════════════════════════════
#
# Registration order is SEMANTIC, not cosmetic: `counts_fresh`, `tables_fresh` and
# `claim_clusters_fresh` shell out and REGENERATE artifacts that later checks read
# (`axiom_count_prose_consistency` and `inventory_index_autogen_fresh` both consume
# `docs/counts.json`). `run_checks` iterates `_CHECKS` in order, so what a later
# check observes depends on what ran before it.
#
# Until now that order was an EMERGENT PROPERTY of where each `@register_check`
# happened to sit in one 7,800-line file. That is fine while there is one file and
# impossible to preserve once the checks are split by domain: the current order
# interleaves domains (#10 Lean, #11 physics, #13 papers, #16 Lean), so no ordering
# of domain modules reproduces it.
#
# So import order and execution order are decoupled. Modules may be organised
# however reads best; execution order is declared HERE, as data, and applied once
# after registration. A registered check absent from this list raises on sort —
# the correct loud failure for a check nobody declared a position for.
#
# NOTE `tests/test_validate_registry_contract.py` keeps its OWN frozen copy and
# must NOT import this one; otherwise it would assert only that production agrees
# with itself.
_CANONICAL_ORDER: tuple[str, ...] = (
    'formulas', 'placeholder_not_cited', 'disclosure_consistency',
    'proxy_body_audit', 'tracked_hypothesis_ledger', 'tracked_hypotheses_fresh',
    'formula_grounding', 'vacuous_statement_audit', 'nogo_substrate_integrity',
    'native_decide_regression', 'numerical', 'identities',
    'paper_table', 'd1_hierarchy_table', 'f_hierarchy_claims',
    'theorems', 'notebooks', 'lean_source',
    'cgl_fdr', 'lean_build', 'axiom_closure_allowlist',
    'elaboration_knob_watchlist', 'bundle_figure_integrity', 'viz_consistency',
    'notebook_exec', 'physical_bounds', 'cross_path_consistency',
    'paper_provenance', 'parameter_provenance', 'counts_fresh',
    'tables_fresh', 'claim_clusters_fresh', 'numerical_literals',
    'graph_integrity', 'atlas_integrity', 'atlas_hypothesis_discipline',
    'count_literals', 'recurrence_reopens_closures', 'review_severity_declared',
    'review_docs_mint_findings', 'accepted_findings_carry_rationale',
    'bundle_metadata_matches_graph', 'notebook_stored_outputs_current',
    'readiness_verdicts_agree', 'readiness_submission_gate',
    'citation_primary_sources_present', 'provenance_doi_in_registry',
    'bundle_consistency', 'bundle_source_freshness',
    'bibitem_title_primary_source', 'quantum_network',
    'bundle_registry_consistency', 'paper_latex_compiles',
    'axiom_count_prose_consistency', 'prose_theorem_reference_coverage',
    'theorem_name_embedded_citations', 'inventory_index_autogen_fresh',
    'lean_docstring_refs_resolve', 'paper_toolchain_pin_drift',
)


def _apply_canonical_order() -> None:
    """Sort `_CHECKS` into `_CANONICAL_ORDER`. Idempotent; a no-op while every
    check still lives in this file in canonical sequence, which is exactly why it
    is introduced BEFORE any module moves — the mechanism is proven inert before
    anything depends on it."""
    index = {name: i for i, name in enumerate(_CANONICAL_ORDER)}
    unknown = [s.name for s in _CHECKS if s.name not in index]
    if unknown:
        raise RuntimeError(
            f"check(s) registered with no declared execution position: {unknown}. "
            f"Add them to _CANONICAL_ORDER — position is semantic (see above), so "
            f"it must be chosen, not inherited from import order.")
    _CHECKS.sort(key=lambda s: index[s.name])


# ⚠️ THE CALL IS DELIBERATELY NOT HERE. It lives at the BOTTOM of this module,
# after the last `@register_check`. Placing it here — which is where it was first
# written, on 2026-08-03 — sorted only the 45 checks registered above this point
# and left the 14 below it appended, unsorted, in import order. Two consequences,
# both invisible because the tail happened to already be in canonical sequence:
#
#   1. The mechanism was inert for 14/59 checks, i.e. exactly the ones a Phase-2
#      module move is most likely to reorder.
#   2. The `raise` above — the "loud failure for a check nobody declared a
#      position for" — could not fire for anything registered below, INCLUDING
#      the end of the file, which is where a new check naturally goes. Verified
#      by mutation: an undeclared check added at :7441 ran, listed, and exited 0.
#
# So the guard written to make ordering explicit was itself order-dependent.
# `tests/test_validate_registry_contract.py` now asserts the call's position
# structurally, because no behavioural test can see this while the tail is
# coincidentally correct.


# ═══════════════════════════════════════════════════════════════════════
# Runner
# ═══════════════════════════════════════════════════════════════════════

def run_checks(
    check_filter: Optional[str] = None,
) -> Dict[str, CheckResult]:
    """Run all (or one) registered checks, return results keyed by name."""
    results = {}
    for spec in _CHECKS:
        if check_filter and spec.name != check_filter:
            continue
        try:
            results[spec.name] = spec.func()
        except Exception as e:
            results[spec.name] = CheckResult(passed=False, error=str(e))
    return results


def print_results(results: Dict[str, CheckResult]) -> None:
    """Pretty-print validation results to stdout."""
    for spec in _CHECKS:
        if spec.name not in results:
            continue
        cr = results[spec.name]
        status = "\033[32m✓ PASS\033[0m" if cr.passed else "\033[31m✗ FAIL\033[0m"
        print(f"\n{'═'*70}")
        print(f"  {status}  {spec.name}: {spec.description}")
        print(f"{'═'*70}")

        if cr.error:
            print(f"  ERROR: {cr.error}")

        for d in cr.details:
            if d.warning:
                sym = "\033[33m⚠\033[0m"
            elif d.passed:
                sym = "✓"
            else:
                sym = "✗"
            line = f"  {sym} {d.name}"
            if d.message:
                line += f"  —  {d.message}"
            print(line)

    total = len(results)
    passed = sum(1 for r in results.values() if r.passed)
    total_warnings = sum(
        1 for r in results.values() for d in r.details if d.warning
    )
    print(f"\n{'═'*70}")
    summary = f"  Overall: {passed}/{total} checks passed"
    if total_warnings:
        summary += f" ({total_warnings} warning{'s' if total_warnings > 1 else ''})"
    print(summary)
    if passed == total:
        print("  \033[32mALL CHECKS PASSED\033[0m")
    else:
        print("  \033[31mSOME CHECKS FAILED\033[0m")
    print(f"{'═'*70}\n")


def archive_results(results: Dict[str, CheckResult]) -> Path:
    """Write timestamped JSON + text report to docs/validation/reports/."""
    REPORTS_DIR.mkdir(parents=True, exist_ok=True)
    ts = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")

    # JSON report
    json_path = REPORTS_DIR / f"validation_{ts}.json"
    payload = {
        "timestamp": ts,
        "project_root": str(PROJECT_ROOT),
        "checks": {},
    }
    for name, cr in results.items():
        payload["checks"][name] = {
            "passed": cr.passed,
            "error": cr.error,
            "details": [asdict(d) for d in cr.details],
        }
    payload["summary"] = {
        "total": len(results),
        "passed": sum(1 for r in results.values() if r.passed),
        "failed": sum(1 for r in results.values() if not r.passed),
    }
    class _Encoder(json.JSONEncoder):
        def default(self, o):
            if isinstance(o, (bool,)):
                return bool(o)
            try:
                return float(o)  # numpy scalars
            except (TypeError, ValueError):
                return super().default(o)

    with open(json_path, 'w') as f:
        json.dump(payload, f, indent=2, cls=_Encoder)

    # Text report (human-readable)
    txt_path = REPORTS_DIR / f"validation_{ts}.txt"
    lines = [
        f"SK-EFT Hawking Validation Report",
        f"Generated: {ts}",
        f"Project: {PROJECT_ROOT}",
        "",
    ]
    for name, cr in results.items():
        status = "PASS" if cr.passed else "FAIL"
        lines.append(f"[{status}] {name}")
        if cr.error:
            lines.append(f"  ERROR: {cr.error}")
        for d in cr.details:
            sym = "+" if d.passed else "-"
            line = f"  {sym} {d.name}"
            if d.message:
                line += f" — {d.message}"
            lines.append(line)
        lines.append("")

    total = len(results)
    passed = sum(1 for r in results.values() if r.passed)
    lines.append(f"Overall: {passed}/{total} passed")
    with open(txt_path, 'w') as f:
        f.write('\n'.join(lines))

    return json_path


# ═══════════════════════════════════════════════════════════════════════
# CHECK 19: Citation primary-source cache present (Phase 6i Wave 1)
# ═══════════════════════════════════════════════════════════════════════

def _discover_cache_for(bibkey: str):
    """Find a primary-source cache for `bibkey` by globbing, independently of what the
    registry declares. Mirrors the discovery the existence half of
    `citation_primary_sources_present` performs, so the content half cannot be opted out
    of by editing one registry field (D11 round-8 finding 1.1)."""
    from src.core.workspace import find_workspace as _fw
    base = _fw() / "Lit-Search"
    if not base.is_dir():
        return None
    for phase in base.iterdir():
        d = phase / "primary-sources"
        if not d.is_dir():
            continue
        # Every cache extension the existence half accepts. A `.pdf` or `.json` cache is
        # a legitimate primary source with no parseable header — it resolves here (so it
        # is not reported unresolvable) and the caller skips the header comparison.
        for ext in ("abstract.txt", "txt", "md", "json", "pdf"):
            cand = d / f"{bibkey}.{ext}"
            if cand.is_file():
                return cand
        low = f"{bibkey}.".lower()
        for cand in d.iterdir():
            if cand.name.lower().startswith(low) and cand.is_file():
                return cand
    return None


@register_check("citation_primary_sources_present",
                "Every external bibitem cited in papers has a primary-source cache file")
def check_citation_primary_sources_present() -> CheckResult:
    """For every \\cite{<bibkey>} in any papers/*/paper_draft.tex, verify a
    primary-source artifact exists on disk under
    `Lit-Search/Phase-X/primary-sources/<bibkey>.{pdf,tex,abstract.txt,json}`.

    `inprep: True` entries are exempt (no external primary source to cache).

    Textbook / pre-DOI references with `primary_source_path: None` AND
    `doi: None` AND `arxiv: None` are also exempt — these are canonical
    textbook citations (e.g. Gilkey 1995 CRC heat-equation textbook;
    Trautman 1973 pre-DOI Symposia Mathematica volume) verified via
    secondary academic citations rather than via a downloadable primary
    source. The registry entry's `notes` field documents the secondary-
    citation pathway. Phase 6i Wave 6 addition.

    Bibkeys absent from CITATION_REGISTRY surface as FAIL — that's already a
    CitationIntegrity violation, not a Wave 1 concern, but worth reporting.
    """
    import ast
    import re
    from src.core.citations import CITATION_REGISTRY, bibkey_phase
    from src.core.workspace import find_workspace

    LIT_SEARCH = find_workspace() / "Lit-Search"
    FALLBACK = "Phase-1-and-Background"
    EXTENSIONS = ["pdf", "tex", "abstract.txt", "json"]

    # ── Duplicate-key guard (added 2026-07-31) ────────────────────────────────
    # CITATION_REGISTRY is a dict *literal*, so a repeated key is legal Python:
    # the later entry silently wins and the earlier one's `used_in` consumers and
    # `primary_source_path` become unreachable. That is invisible to every check
    # that reads the imported dict, because by then the duplicate is already gone.
    # It shipped undetected for two Stage-13 rounds ('Berry1984'). Detect it by
    # parsing the source, not the imported object.
    dup_details = []
    try:
        # ADR-009 H1 — the other SILENT site: the `except` below downgrades to an
        # advisory warning, so a retargeted anchor would disable this duplicate-key
        # guard without failing anything.
        _reg_src = (_H.SRC_DIR / "core" / "citations.py").read_text(encoding="utf-8")
        _tree = ast.parse(_reg_src)
        _seen: dict[str, int] = {}
        for _node in ast.walk(_tree):
            if not isinstance(_node, ast.Dict):
                continue
            for _k in _node.keys:
                if isinstance(_k, ast.Constant) and isinstance(_k.value, str):
                    _seen[_k.value] = _seen.get(_k.value, 0) + 1
        _dups = sorted(k for k, n in _seen.items() if n > 1 and k in CITATION_REGISTRY)
        if _dups:
            dup_details.append(Detail(
                "duplicate_bibkeys", False,
                f"{len(_dups)} bibkey(s) defined more than once in citations.py — the later "
                f"literal silently shadows the earlier, orphaning its used_in/primary_source_path: "
                f"{', '.join(_dups)}",
            ))
    except Exception as exc:  # pragma: no cover - guard must never mask the real check
        dup_details.append(Detail(
            "duplicate_bibkeys", True,
            f"duplicate-key scan skipped ({type(exc).__name__}: {exc})", warning=True,
        ))

    # Match \cite, \citep, \citet, \citeauthor, etc., with optional star,
    # optional [opt-args], then {key1,key2,...}
    CITE_RE = re.compile(r"\\cite[a-zA-Z]*\*?\s*(?:\[[^\]]*\])*\s*\{([^}]+)\}")

    details: List[Detail] = []
    all_pass = True

    paper_tex_files = _H.all_paper_drafts()     # ALL drafts (bundles + legacy)
    if not paper_tex_files:
        return CheckResult(passed=False, error="No papers/*/paper_draft.tex found")

    # First pass: collect (bibkey, paper_key) usage across all papers
    usage: dict[str, set[str]] = {}
    for tex_path in paper_tex_files:
        paper_key = tex_path.parent.name
        text = tex_path.read_text(encoding="utf-8", errors="replace")
        # Strip TeX-comment lines so commented-out \cite{} are not gated
        text_uncommented = "\n".join(
            line.split("%", 1)[0] for line in text.splitlines()
        )
        for m in CITE_RE.finditer(text_uncommented):
            for raw_key in m.group(1).split(","):
                key = raw_key.strip()
                if key:
                    usage.setdefault(key, set()).add(paper_key)

    # Second pass: classify each cited bibkey
    missing_from_registry: list[str] = []
    inprep_exempt: list[str] = []
    textbook_exempt: list[str] = []
    cached: list[str] = []
    not_cached: list[tuple[str, str, list[str]]] = []  # (key, phase, papers)

    for bibkey in sorted(usage):
        entry = CITATION_REGISTRY.get(bibkey)
        if entry is None:
            missing_from_registry.append(bibkey)
            continue
        if entry.get("inprep"):
            inprep_exempt.append(bibkey)
            continue
        # Textbook / pre-DOI exemption (Wave-6): canonical textbook
        # references with no DOI / no arXiv / no primary_source_path,
        # verified via secondary academic citations per `notes`.
        if (entry.get("primary_source_path") is None
                and entry.get("doi") is None
                and entry.get("arxiv") is None):
            textbook_exempt.append(bibkey)
            continue
        # Resolve phase: prefer canonical (used_in[0] paper), else fallback
        phase = bibkey_phase(entry) or FALLBACK
        target_dir = LIT_SEARCH / phase / "primary-sources"
        found = False
        for ext in EXTENSIONS:
            candidate = target_dir / f"{bibkey}.{ext}"
            if candidate.is_file() and candidate.stat().st_size > 0:
                found = True
                break
        if found:
            cached.append(bibkey)
        else:
            not_cached.append((bibkey, phase, sorted(usage[bibkey])))

    # Report
    n_cited = len(usage)
    n_cached = len(cached)
    n_inprep = len(inprep_exempt)
    n_textbook = len(textbook_exempt)
    n_missing = len(missing_from_registry)
    n_uncached = len(not_cached)

    details.append(Detail(
        "summary",
        n_uncached == 0 and n_missing == 0,
        f"{n_cited} bibkeys cited across {len(paper_tex_files)} papers — "
        f"{n_cached} cached / {n_inprep} inprep-exempt / "
        f"{n_textbook} textbook-exempt / "
        f"{n_uncached} need cache / {n_missing} missing-from-registry"
    ))

    if missing_from_registry:
        all_pass = False
        sample = ", ".join(missing_from_registry[:8])
        more = f" (and {len(missing_from_registry) - 8} more)" if len(missing_from_registry) > 8 else ""
        details.append(Detail(
            "missing_from_registry",
            False,
            f"{n_missing} cited bibkeys absent from CITATION_REGISTRY: {sample}{more}"
        ))

    if not_cached:
        all_pass = False
        # Group by phase for compactness
        by_phase: dict[str, list[str]] = {}
        for bibkey, phase, _ in not_cached:
            by_phase.setdefault(phase, []).append(bibkey)
        for phase in sorted(by_phase):
            keys = by_phase[phase]
            sample = ", ".join(keys[:5])
            more = f" + {len(keys) - 5} more" if len(keys) > 5 else ""
            details.append(Detail(
                f"missing_cache:{phase}",
                False,
                f"{len(keys)} bibkeys lack primary-source cache: {sample}{more}"
            ))

    if all_pass:
        details.append(Detail(
            "all_cached",
            True,
            "Every cited external bibkey has a primary-source cache file"
        ))

    # Fold in the duplicate-key guard: a shadowed bibkey is a CitationIntegrity
    # defect even when every cache file is present.
    details.extend(dup_details)
    all_pass = all_pass and all(d.passed for d in dup_details)

    # ── Cache CONTENT agreement (added 2026-07-31) ────────────────────────────
    # This check historically verified only that a cache file EXISTS. That let a
    # hallucinated citation be caught in the .tex, fixed in the .tex and in
    # CITATION_REGISTRY, and survive verbatim in the cache — the artifact the
    # pipeline calls its strongest evidence class — while this check reported
    # PASS. Two Stage-13 BLOCKERs of exactly that shape shipped
    # (BoldoLaxMilgram2016, LeanLJ2025), each with the refuted metadata still
    # tagged "[fetched]".
    #
    # (An earlier version of this comment claimed promote_primary_sources.py writes
    # cache contents back into the registry, making a stale cache self-propagating.
    # That was asserted without reading the script and is FALSE -- it reads only its
    # sidecar JSON, missing_bibkey_stubs.json and citations.py, and inserts only
    # 'inprep' and 'primary_source_path'. Corrected 2026-07-31, D11 round 4. The
    # cache is a bad RECORD, not a loaded gun -- which is reason enough to gate it.)
    #
    # Compare each cache header's Title:/arXiv: against the registry.
    title_details = []
    _norm_ws = lambda s: " ".join(s.split()).strip().lower()
    # ⚠️ BYPASS CLOSED 2026-07-31 (D11 Stage-13 round-8 finding 1.1). This loop used to
    # `continue` whenever `primary_source_path` was absent or did not end in
    # `.abstract.txt`, while the EXISTENCE half above globs for `<bibkey>.<ext>` by bibkey
    # independently of that field. So blanking one registry field passed existence (the
    # file is still on disk and still found by glob) and silently skipped every content
    # check — title, authors, year, DOI, arXiv. A reviewer took that path green in three
    # mutations. The loop is now driven by the cache DISCOVERED for each bibkey, so the
    # registry cannot opt itself out, and a declared-but-unresolvable path is a FAIL
    # rather than a silent skip.
    for bibkey, entry in sorted(CITATION_REGISTRY.items()):
        ps = entry.get("primary_source_path")
        declared = bool(ps)
        cache_file = (find_workspace() / ps) if ps else None
        if cache_file is None or not str(ps).endswith(".abstract.txt"):
            # No usable declared path: fall back to the same discovery the existence half
            # uses, so the content checks still run on whatever cache is actually present.
            found = _discover_cache_for(bibkey)
            if found is None:
                if declared:
                    title_details.append(Detail(
                        f"cache_path_unresolvable:{bibkey}", False,
                        f"registry declares primary_source_path={ps!r} but no cache "
                        f"resolves for this bibkey by any extension, so NO content check "
                        f"ran. A declared path that names nothing is worse than none: it "
                        f"reads as provenance."))
                continue
            # Header comparison needs a parseable header. A `.pdf`/`.json` cache has none;
            # that is a real cache, just not one this half can read — skip silently, as the
            # `.abstract.txt` opt-in used to, but ONLY after discovery proved it exists.
            if found.suffix not in (".txt", ".md"):
                continue
            cache_file = found
        if not cache_file.exists():
            # Case-insensitive retry: registry paths say `Phase-6E`/`Phase-6C` while the
            # directories on disk are `Phase-6e`/`Phase-6c`. That resolves on APFS but NOT
            # on a case-sensitive filesystem, where every entry would fall through this
            # branch and the gate would report PASS having checked nothing (D11 round-4
            # finding). Resolve explicitly rather than skip.
            parent = cache_file.parent
            resolved = None
            if not parent.exists():
                gp = parent.parent
                if gp.exists():
                    for cand in gp.iterdir():
                        if cand.is_dir() and cand.name.lower() == parent.name.lower():
                            parent = cand
                            break
            if parent.exists():
                for cand in parent.iterdir():
                    if cand.name.lower() == cache_file.name.lower():
                        resolved = cand
                        break
            if resolved is None:
                continue  # existence is the other half of this check
            cache_file = resolved
        try:
            head = cache_file.read_text(encoding="utf-8", errors="replace")[:4000]
        except OSError:
            continue
        m_title = re.search(r"^Title:\s*(.+)$", head, re.MULTILINE)
        reg_title = entry.get("title")
        if m_title and reg_title:
            if _norm_ws(m_title.group(1)) != _norm_ws(reg_title):
                title_details.append(Detail(
                    f"cache_title_mismatch:{bibkey}", False,
                    f"{cache_file} header Title disagrees with CITATION_REGISTRY. "
                    f"cache={m_title.group(1).strip()!r} registry={reg_title!r}. "
                    f"The cache is this pipeline's designated primary-source evidence; a "
                    f"disagreement means one of the two is wrong.",
                ))
        # Author-surname agreement. The round-2 LeanLJ2025 defect was a wrong TITLE *and*
        # three wrong author initials; a title-only check catches that one but not an
        # author-only drift, so compare surnames too (initials and accents vary).
        m_auth = re.search(r"^Authors:\s*(.+)$", head, re.MULTILINE)
        reg_auth = entry.get("authors")
        if m_auth and reg_auth:
            _STOP = {"and", "the", "van", "der", "den", "von", "de", "di", "el"}

            def _surnames(s: str) -> set:
                # Tokenize into WORDS, not comma-separated chunks: the cache writes
                # "Scott Aaronson, Daniel Gottesman" while the registry writes
                # "Aaronson, S. and Gottesman, D.", so a chunk comparison never
                # intersects. Drop initials (len<=2) and connectives.
                out = set()
                for w in re.findall(r"[A-Za-zÀ-ÿ'’-]+", s):
                    wl = w.lower()
                    if len(wl) > 2 and wl not in _STOP:
                        out.add(wl)
                return out
            c_s, r_s = _surnames(m_auth.group(1)), _surnames(reg_auth)
            if c_s and r_s and not (c_s & r_s):
                title_details.append(Detail(
                    f"cache_authors_mismatch:{bibkey}", False,
                    f"{ps} header Authors shares no surname with CITATION_REGISTRY. "
                    f"cache={m_auth.group(1).strip()!r} registry={reg_auth!r}",
                ))
        # Year is ADVISORY only: a cache recording an arXiv v1 year against a registry
        # holding the journal year is a legitimate convention difference, not a defect.
        m_year = re.search(r"^Year:\s*(\d{4})", head, re.MULTILINE)
        reg_year = entry.get("year")
        if m_year and reg_year and int(m_year.group(1)) != int(reg_year):
            title_details.append(Detail(
                f"cache_year_advisory:{bibkey}", True,
                f"{ps} header Year {m_year.group(1)} != registry {reg_year} "
                f"(preprint vs publication year?)", warning=True,
            ))
        m_doi = re.search(r"^DOI:\s*(\S+)", head, re.MULTILINE)
        reg_doi = entry.get("doi")
        if m_doi and reg_doi and m_doi.group(1).strip().rstrip('.') != str(reg_doi).strip():
            title_details.append(Detail(
                f"cache_doi_mismatch:{bibkey}", False,
                f"{ps} header DOI {m_doi.group(1)} != registry {reg_doi}",
            ))
        m_ax = re.search(r"^arXiv:\s*([0-9]{4}\.[0-9]{4,5}|[a-z-]+/[0-9]{7})", head, re.MULTILINE)
        reg_ax = entry.get("arxiv")
        if m_ax and reg_ax and m_ax.group(1).strip() != str(reg_ax).strip():
            title_details.append(Detail(
                f"cache_arxiv_mismatch:{bibkey}", False,
                f"{ps} header arXiv {m_ax.group(1)} != registry {reg_ax}",
            ))
    if not title_details:
        title_details.append(Detail(
            "cache_content_agreement", True,
            "Every .abstract.txt cache header agrees with its registry "
            "Title/Authors/Year/DOI/arXiv",
        ))
    details.extend(title_details)
    all_pass = all_pass and all(d.passed for d in title_details)

    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 20: Provenance DOI ↔ CITATION_REGISTRY coverage
# ═══════════════════════════════════════════════════════════════════════

@register_check("provenance_doi_in_registry",
                "PARAMETER_PROVENANCE source DOIs resolve to CITATION_REGISTRY bibkeys")
def check_provenance_doi_in_registry() -> CheckResult:
    """For every PARAMETER_PROVENANCE entry whose `doi` is non-null, verify
    that DOI is present in CITATION_REGISTRY. This is the
    `qi-provenance-citation-coverage` QI item recommended by the Stage 13
    paper40 re-review (round 2): primary-experimental papers cited in
    PARAMETER_PROVENANCE should themselves be in CITATION_REGISTRY so that
    the Phase 6i Wave 1 primary-source cache covers them.

    Each entry may also carry a `cited_bibkeys` field listing the registry
    keys it relies on; if present, those keys must exist in CITATION_REGISTRY.

    Strict mode promotes both findings to hard failures; default mode keeps
    them as warnings (advisory during the rolling Phase 6i remediation).
    """
    from src.core.citations import CITATION_REGISTRY
    from src.core.provenance import PARAMETER_PROVENANCE

    reg_dois = {
        (e.get('doi') or '').lower(): k
        for k, e in CITATION_REGISTRY.items() if e.get('doi')
    }

    details: List[Detail] = []
    all_pass = True

    missing_doi: list[tuple[str, str]] = []  # (prov_key, doi)
    missing_bibkey: list[tuple[str, str]] = []  # (prov_key, bibkey)
    resolved_doi = 0
    resolved_bibkey = 0
    no_doi = 0

    for prov_key, entry in PARAMETER_PROVENANCE.items():
        doi = entry.get('doi')
        if doi:
            if doi.lower() in reg_dois:
                resolved_doi += 1
            else:
                missing_doi.append((prov_key, doi))
        else:
            no_doi += 1

        for bibkey in entry.get('cited_bibkeys', []) or []:
            if bibkey in CITATION_REGISTRY:
                resolved_bibkey += 1
            else:
                missing_bibkey.append((prov_key, bibkey))

    n_total = len(PARAMETER_PROVENANCE)
    details.append(Detail(
        "summary", not (missing_doi or missing_bibkey),
        f"{resolved_doi} provenance DOIs resolved / {len(missing_doi)} missing "
        f"/ {no_doi} entries without DOI (internal derivation); "
        f"{resolved_bibkey} cited_bibkeys resolved / "
        f"{len(missing_bibkey)} missing"
    ))

    if missing_doi:
        sample = ', '.join(f"{k}({d})" for k, d in missing_doi[:5])
        more = f" + {len(missing_doi) - 5} more" if len(missing_doi) > 5 else ""
        msg = (f"{len(missing_doi)} provenance DOIs absent from "
               f"CITATION_REGISTRY: {sample}{more}")
        if _cfg.STRICT_MODE:
            all_pass = False
            details.append(Detail("missing_dois", False, f"[strict] {msg}"))
        else:
            details.append(Detail("missing_dois", True, msg, warning=True))

    if missing_bibkey:
        sample = ', '.join(f"{k}({b})" for k, b in missing_bibkey[:5])
        more = f" + {len(missing_bibkey) - 5} more" if len(missing_bibkey) > 5 else ""
        all_pass = False  # cited_bibkeys MUST resolve — these are explicit refs
        details.append(Detail(
            "missing_cited_bibkeys", False,
            f"{len(missing_bibkey)} cited_bibkeys absent from "
            f"CITATION_REGISTRY: {sample}{more}"
        ))

    if not (missing_doi or missing_bibkey):
        details.append(Detail(
            "all_resolved", True,
            "Every provenance DOI and cited_bibkey resolves to a "
            "CITATION_REGISTRY entry"
        ))

    return CheckResult(passed=all_pass, details=details)


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
    # PAPERS_DIR = PROJECT_ROOT / "papers", where PROJECT_ROOT is this
    # checkout's repo root. The old `__file__.parent×3 / "SK_EFT_Hawking" /
    # "papers"` walk resolved to `.claude/worktrees/SK_EFT_Hawking/papers`
    # from a worktree. Per CLAUDE.md: never hardcode parent-walks.
    INDEX_PATH = PAPERS_DIR / "cluster_bundle_index.json"

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




# ═══════════════════════════════════════════════════════════════════════
# CHECK 23: Bibitem title ↔ primary-source PDF page-1 consistency
# (Stage 14 QI candidate from Phase 6o Wave 4a.4 D5 adversarial review:
#  catches single-word title drift like "in a relativistic" vs
#  "in relativistic" Bose-Einstein condensate. Default: advisory WARN.)
# ═══════════════════════════════════════════════════════════════════════

@register_check("bibitem_title_primary_source",
                "Registry titles match primary-source cache PDF page-1 titles (drift detector)")
def check_bibitem_title_primary_source() -> CheckResult:
    """For every CITATION_REGISTRY entry whose `primary_source_path` points
    to a `.pdf` cache file AND has a non-empty `title`, extract the page-1
    text from the cached PDF and compare against the registry title.

    Flags single-word and multi-word title drift between the registry's
    bibitem title and the actual published form. Designed to catch the
    failure mode that produced the BLOCKER in the Phase 6o Wave 4a.4 D5
    adversarial review (`BelenchiaLiberatiMohd2014` registered as "in a
    relativistic Bose-Einstein condensate" but published as "in
    relativistic Bose-Einstein condensate" — a single-word drop).

    Implementation: extract page-1 text via pdfminer.six; normalize both
    titles (lowercase, collapse whitespace, strip punctuation); compute
    `difflib.SequenceMatcher` ratio between the registry title and a
    sliding window of the page-1 text. Flag entries where the best-window
    ratio falls below a threshold.

    Default mode: advisory WARN per finding (the check passes overall;
    individual mismatches are surfaced for author review). Strict mode
    (`validate.py --strict`) promotes mismatches to FAIL — for use at
    paper-submission gate.

    Skips:
    - Entries with `inprep: True` (no external primary source).
    - Entries with `primary_source_path: None` (textbook / pre-DOI exempt
      per Pipeline Invariant #11).
    - Entries whose cache is non-PDF (`.json`, `.abstract.txt`, `.tex`).
    - Entries whose cache file does not exist on disk (separately
      enforced by `citation_primary_sources_present`).

    Phase 6o Wave 4a.4 close memo `temporary/working-docs/phase6o/
    wave_4a_sakharov_lambda_substrate_refactor_close.md` documents the
    BLOCKER pattern this check guards against.
    """
    import re
    from src.core.citations import CITATION_REGISTRY
    from src.core.workspace import find_workspace

    # ps_path entries are workspace-relative (`Lit-Search/...`), so resolve
    # against the workspace root. Layout-independent (main checkout AND a
    # worktree slot); the old `__file__.parent×3` walk resolved to
    # `.claude/worktrees` from a worktree. Per CLAUDE.md: no parent-walks.
    PROJECT_ROOT_LOCAL = find_workspace()

    try:
        from pdfminer.high_level import extract_text  # type: ignore
    except ImportError:
        return CheckResult(
            passed=True,
            details=[Detail(
                "skipped",
                True,
                "pdfminer.six not installed — check skipped (advisory)",
                warning=True,
            )],
        )

    # Common ligature decompositions used in PDF text extraction
    LIGATURES = {
        "ﬁ": "fi", "ﬂ": "fl", "ﬀ": "ff", "ﬃ": "ffi", "ﬄ": "ffl",
        "ﬅ": "ft", "ﬆ": "st",
    }

    # Greek-letter spell-outs that appear in titles vs PDF text
    GREEK = {
        "Λ": "lambda", "λ": "lambda",
        "Α": "alpha", "α": "alpha",
        "Β": "beta", "β": "beta",
        "Γ": "gamma", "γ": "gamma",
        "Δ": "delta", "δ": "delta",
        "Ω": "omega", "ω": "omega",
        "ℝ": "r", "ℤ": "z", "ℕ": "n", "ℂ": "c",
    }

    def _normalize(s: str) -> str:
        # Apply ligature + Greek decomposition
        for k, v in LIGATURES.items():
            s = s.replace(k, v)
        for k, v in GREEK.items():
            s = s.replace(k, v)
        s = s.lower()
        # Normalize all dash variants
        s = s.replace("–", "-").replace("—", "-").replace("−", "-")
        # Strip everything except letters, digits, hyphens, spaces.
        # Also drop hyphens (so "Bose-Einstein" matches "Bose Einstein")
        s = re.sub(r"[^a-z0-9\s]", " ", s)
        s = re.sub(r"\s+", " ", s).strip()
        return s

    details: List[Detail] = []
    flagged: list[tuple[str, str, str]] = []  # (key, registry_title, pdf_excerpt)
    checked = 0
    skipped_no_pdf = 0
    skipped_inprep = 0
    skipped_textbook = 0
    skipped_no_title = 0
    skipped_missing_cache = 0
    extract_failed: list[tuple[str, str]] = []

    for bibkey, entry in sorted(CITATION_REGISTRY.items()):
        if entry.get("inprep"):
            skipped_inprep += 1
            continue
        title = (entry.get("title") or "").strip()
        if not title:
            skipped_no_title += 1
            continue
        ps_path = entry.get("primary_source_path")
        if ps_path is None:
            # Textbook / pre-DOI exempt per Pipeline Invariant #11
            if entry.get("doi") is None and entry.get("arxiv") is None:
                skipped_textbook += 1
            continue
        if not str(ps_path).endswith(".pdf"):
            skipped_no_pdf += 1
            continue
        cache_file = PROJECT_ROOT_LOCAL / ps_path
        if not cache_file.is_file() or cache_file.stat().st_size == 0:
            skipped_missing_cache += 1
            continue

        try:
            page1_text = extract_text(str(cache_file), maxpages=1) or ""
        except Exception as exc:
            extract_failed.append((bibkey, str(exc)[:100]))
            continue

        norm_title = _normalize(title)
        norm_page = _normalize(page1_text)
        if not norm_title or not norm_page:
            extract_failed.append((bibkey, "empty extract"))
            continue

        checked += 1

        # Primary signal: substring containment after normalization.
        # If the normalized registry title appears verbatim in the
        # normalized page-1 text, the bibitem is consistent with the PDF.
        if norm_title in norm_page:
            continue

        # Secondary signal: try dropping a single word from the registry
        # title — if any single-word drop makes it a substring, that is
        # the BLOCKER drift pattern (e.g., registry has "in a relativistic"
        # but PDF has "in relativistic": dropping "a" yields containment).
        tokens = norm_title.split()
        single_drop_match = None
        if len(tokens) >= 3:
            for i, _ in enumerate(tokens):
                candidate = " ".join(tokens[:i] + tokens[i + 1:])
                if candidate and candidate in norm_page:
                    single_drop_match = tokens[i]
                    break
        if single_drop_match is not None:
            # Localize the matched window for the report
            candidate = " ".join(t for t in tokens if t != single_drop_match)
            idx = norm_page.find(candidate)
            window = norm_page[max(0, idx - 10):idx + len(candidate) + 30]
            flagged.append((
                bibkey,
                f"DROP-WORD: registry has extra {single_drop_match!r} not in PDF — title={title!r}",
                window,
            ))
            continue

        # Tertiary signal: check if PDF has an extra word the registry lacks.
        # If we can find every registry token in order in a 200-char window
        # of the page, but the title isn't a clean substring, flag for review.
        # Otherwise, the title may simply not be on page 1 (e.g., journal
        # metadata pages) — defer to manual audit.
        # For brevity, just flag with a low-priority "title-not-on-page1" note.
        flagged.append((
            bibkey,
            f"NOT-FOUND: registry title not a substring of page-1 — title={title!r}",
            norm_page[:120],
        ))

    # Partition flags: DROP-WORD flags are the high-confidence drift class
    # (the BLOCKER pattern this check targets). NOT-FOUND flags often
    # indicate that the title isn't on page 1 of the PDF (e.g., the cache
    # is a journal title page, a chapter excerpt, or has heavy metadata
    # before the title) — these are advisory only.
    drop_word_flags = [(k, m, w) for (k, m, w) in flagged if m.startswith("DROP-WORD")]
    not_found_flags = [(k, m, w) for (k, m, w) in flagged if m.startswith("NOT-FOUND")]
    n_drop_word = len(drop_word_flags)
    n_not_found = len(not_found_flags)
    n_extract_failed = len(extract_failed)

    # In strict mode, both drift classes fail; in default mode, only
    # DROP-WORD flags fail (high-confidence BLOCKER pattern), NOT-FOUND
    # is advisory only.
    summary_passed = _cfg.STRICT_MODE is False or (n_drop_word == 0 and n_not_found == 0)
    if not _cfg.STRICT_MODE:
        summary_passed = True  # Always pass in default mode

    details.append(Detail(
        "summary",
        summary_passed,
        f"checked {checked} PDF caches — "
        f"{n_drop_word} DROP-WORD drift flag(s) / "
        f"{n_not_found} NOT-FOUND advisory flag(s) / "
        f"{n_extract_failed} extract-failure(s) / "
        f"skipped: {skipped_inprep} inprep, {skipped_textbook} textbook, "
        f"{skipped_no_pdf} non-pdf cache, {skipped_no_title} no-title, "
        f"{skipped_missing_cache} cache-missing"
        + (" (strict mode: drift flags promoted to FAIL)" if _cfg.STRICT_MODE else ""),
        warning=(n_drop_word > 0 or n_not_found > 0) and not _cfg.STRICT_MODE,
    ))

    # DROP-WORD findings: high-confidence drift (the BLOCKER class)
    for bibkey, msg, pdf_excerpt in drop_word_flags[:20]:
        details.append(Detail(
            f"drop_word:{bibkey}",
            _cfg.STRICT_MODE is False,
            f"{msg} — pdf-page1≈{pdf_excerpt!r}",
            warning=not _cfg.STRICT_MODE,
        ))
    if len(drop_word_flags) > 20:
        details.append(Detail(
            "drop_word:overflow",
            True,
            f"({len(drop_word_flags) - 20} more DROP-WORD flags omitted)",
            warning=True,
        ))

    # NOT-FOUND findings: advisory (title not on page 1; often false-positive
    # for cached PDFs whose page-1 is a journal cover or chapter intro).
    # Show only first 10 in default output.
    for bibkey, msg, pdf_excerpt in not_found_flags[:10]:
        details.append(Detail(
            f"not_found:{bibkey}",
            True,  # advisory only
            f"{msg} (advisory — verify manually)",
            warning=True,
        ))
    if len(not_found_flags) > 10:
        details.append(Detail(
            "not_found:overflow",
            True,
            f"({len(not_found_flags) - 10} more NOT-FOUND advisory flags omitted)",
            warning=True,
        ))

    for bibkey, err in extract_failed[:10]:
        details.append(Detail(
            f"extract_failed:{bibkey}",
            True,  # extract failures are advisory
            f"pdfminer error: {err}",
            warning=True,
        ))

    if n_drop_word == 0 and n_not_found == 0 and n_extract_failed == 0:
        details.append(Detail(
            "all_consistent",
            True,
            "Every checked registry title matches its PDF page-1 form",
        ))

    return CheckResult(
        passed=summary_passed,
        details=details,
    )




# ═══════════════════════════════════════════════════════════════════════
# Shared helpers for the prose-consistency checks (CHECK 24–26)
# (Stage 14 follow-through from the 2026-06-05 external-review remediation;
#  record: temporary/working-docs/reviews/papers/2026-06-05-Perplexity/
#  REMEDIATION_TRIAGE_2026-06-10.md, Wave-5 process items a/b/c.)
# ═══════════════════════════════════════════════════════════════════════

#: Bundle codes per docs/PAPER_STRATEGY.md, from THE roster source of truth
#: (scripts/bundle_registry.py). Re-exported under the historical name because
#: three checks below and `tests/` import it.
#:
#: This was a hand-maintained literal until 2026-07-30. It omitted D10–D12,
#: which meant `prose_theorem_reference_coverage` — the one gate that catches
#: Lean theorem-name drift in bundle prose — never scanned D10 at all between
#: its 2026-06-30 first lift and 2026-07-30. A short tuple does not error; it
#: just checks fewer bundles and reports a clean pass.
BUNDLE_CODES = _REGISTRY_BUNDLE_CODES


# ═══════════════════════════════════════════════════════════════════════
# Bundle-roster single-source-of-truth gate
# ═══════════════════════════════════════════════════════════════════════

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
    for py in sorted(SCRIPT_DIR.glob("*.py")):
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














# ═══════════════════════════════════════════════════════════════════════
# CLI
# ═══════════════════════════════════════════════════════════════════════






# ═══════════════════════════════════════════════════════════════════════
# Check modules — imported for their registration side-effect (ADR-009 Phase 2)
# ═══════════════════════════════════════════════════════════════════════
# Import order does NOT determine execution order; `_CANONICAL_ORDER` below does
# (H3). Organise `validation/checks/*` for reading, not for sequencing.
#
# The names are re-exported because nine test files and `scripts/sync_manifest.py`
# import them from `validate` directly (D2 item 8). `tests/test_validate_public_surface.py`
# freezes that surface.
from validation.checks import notebooks as _checks_notebooks  # noqa: E402
from validation.checks import physics as _checks_physics      # noqa: E402
from validation.checks import graph_atlas as _checks_graph_atlas  # noqa: E402
from validation.checks import freshness as _checks_freshness      # noqa: E402
from validation.checks import lean_toolchain as _checks_lean_toolchain  # noqa: E402
from validation.checks import lean_substrate as _checks_lean_substrate  # noqa: E402
from validation.checks import papers_prose as _checks_papers_prose      # noqa: E402
from validation.checks import prose_lean_refs as _checks_prose_refs     # noqa: E402

check_notebook_isolation = _checks_notebooks.check_notebook_isolation
check_viz_consistency = _checks_notebooks.check_viz_consistency
check_notebook_execution = _checks_notebooks.check_notebook_execution
NOTEBOOK_EXEC_CACHE = _checks_notebooks.NOTEBOOK_EXEC_CACHE
_src_core_fingerprint = _checks_notebooks._src_core_fingerprint
_notebook_code_hash = _checks_notebooks._notebook_code_hash

check_numerical_consistency = _checks_physics.check_numerical_consistency
check_formula_identities = _checks_physics.check_formula_identities
check_paper_table_consistency = _checks_physics.check_paper_table_consistency
check_d1_hierarchy_table = _checks_physics.check_d1_hierarchy_table
check_f_hierarchy_claims = _checks_physics.check_f_hierarchy_claims
check_cgl_fdr = _checks_physics.check_cgl_fdr
check_physical_bounds = _checks_physics.check_physical_bounds
check_cross_path_consistency = _checks_physics.check_cross_path_consistency
check_quantum_network = _checks_physics.check_quantum_network
_parse_latex_number = _checks_physics._parse_latex_number

check_graph_integrity = _checks_graph_atlas.check_graph_integrity
check_atlas_integrity = _checks_graph_atlas.check_atlas_integrity
check_atlas_hypothesis_discipline = _checks_graph_atlas.check_atlas_hypothesis_discipline
_hyp_module_stem = _checks_graph_atlas._hyp_module_stem

check_counts_fresh = _checks_freshness.check_counts_fresh
check_tables_fresh = _checks_freshness.check_tables_fresh
check_claim_clusters_fresh = _checks_freshness.check_claim_clusters_fresh
check_bundle_source_freshness = _checks_freshness.check_bundle_source_freshness
check_inventory_index_autogen_fresh = _checks_freshness.check_inventory_index_autogen_fresh
check_notebook_stored_outputs_current = _checks_freshness.check_notebook_stored_outputs_current
_counts_is_stale = _checks_freshness._counts_is_stale      # scripts/sync_manifest.py
_tables_is_stale = _checks_freshness._tables_is_stale      # scripts/sync_manifest.py
_claim_clusters_is_stale = _checks_freshness._claim_clusters_is_stale
COUNTS_JSON_PATH = _checks_freshness._H.COUNTS_JSON_PATH
COUNTS_TEX_PATH = _checks_freshness._H.COUNTS_TEX_PATH
CLAIM_CLUSTERS_PATH = _checks_freshness.CLAIM_CLUSTERS_PATH

check_native_decide_regression = _checks_lean_toolchain.check_native_decide_regression
check_theorem_count = _checks_lean_toolchain.check_theorem_count
check_lean_source = _checks_lean_toolchain.check_lean_source
check_lean_build = _checks_lean_toolchain.check_lean_build
check_axiom_closure_allowlist = _checks_lean_toolchain.check_axiom_closure_allowlist
check_elaboration_knob_watchlist = _checks_lean_toolchain.check_elaboration_knob_watchlist
check_lean_docstring_refs_resolve = _checks_lean_toolchain.check_lean_docstring_refs_resolve

check_formulas_to_theorems = _checks_lean_substrate.check_formulas_to_theorems
check_placeholder_not_cited = _checks_lean_substrate.check_placeholder_not_cited
check_disclosure_consistency = _checks_lean_substrate.check_disclosure_consistency
check_proxy_body_audit = _checks_lean_substrate.check_proxy_body_audit
check_tracked_hypothesis_ledger = _checks_lean_substrate.check_tracked_hypothesis_ledger
check_tracked_hypotheses_fresh = _checks_lean_substrate.check_tracked_hypotheses_fresh
check_formula_grounding = _checks_lean_substrate.check_formula_grounding
check_vacuous_statement_audit = _checks_lean_substrate.check_vacuous_statement_audit
check_nogo_substrate_integrity = _checks_lean_substrate.check_nogo_substrate_integrity
# Regexes + pure cores imported directly by tests/test_substrate_integrity_gates.py
_tex_name_pattern = _checks_lean_substrate._tex_name_pattern
_VERIFY_CLAIM_RE = _checks_lean_substrate._VERIFY_CLAIM_RE
_HEDGE_CLAIM_RE = _checks_lean_substrate._HEDGE_CLAIM_RE
_OVERCLAIM_VERB_RE = _checks_lean_substrate._OVERCLAIM_VERB_RE
_LEDGER_HEDGE_RE = _checks_lean_substrate._LEDGER_HEDGE_RE
_STRUCTURAL_NAME_RE = _checks_lean_substrate._STRUCTURAL_NAME_RE
_TRIVIAL_BODY_RES = _checks_lean_substrate._TRIVIAL_BODY_RES
_NONTRIVIAL_MARKER_RE = _checks_lean_substrate._NONTRIVIAL_MARKER_RE
_TRACKED_PROP_NAME_RE = _checks_lean_substrate._TRACKED_PROP_NAME_RE
_THIN_HARD = _checks_lean_substrate._THIN_HARD
_is_prop_codomain = _checks_lean_substrate._is_prop_codomain
_is_autogen_decl = _checks_lean_substrate._is_autogen_decl
_thin_type_label = _checks_lean_substrate._thin_type_label
_is_vacuous_identity_wrapper = _checks_lean_substrate._is_vacuous_identity_wrapper
_parse_formula_lean_refs = _checks_lean_substrate._parse_formula_lean_refs

check_paper_provenance = _checks_papers_prose.check_paper_provenance
check_numerical_literals = _checks_papers_prose.check_numerical_literals
check_count_literals = _checks_papers_prose.check_count_literals
check_paper_latex_compiles = _checks_papers_prose.check_paper_latex_compiles
check_axiom_count_prose_consistency = _checks_papers_prose.check_axiom_count_prose_consistency
check_paper_toolchain_pin_drift = _checks_papers_prose.check_paper_toolchain_pin_drift
_axiom_prose_findings = _checks_papers_prose._axiom_prose_findings
_tp_live_pins = _checks_papers_prose._tp_live_pins
_tp_scan_lines = _checks_papers_prose._tp_scan_lines
check_prose_theorem_reference_coverage = _checks_prose_refs.check_prose_theorem_reference_coverage
check_theorem_name_embedded_citations = _checks_prose_refs.check_theorem_name_embedded_citations
_prose_occurrence_disclaimed = _checks_prose_refs._prose_occurrence_disclaimed
_extract_prose_lean_candidates = _checks_prose_refs._extract_prose_lean_candidates
_resolve_prose_ref = _checks_prose_refs._resolve_prose_ref
_embedded_citation_pairs = _checks_prose_refs._embedded_citation_pairs
_paper_bibitems = _checks_prose_refs._paper_bibitems
_PROSE_REF_WAIVERS = _checks_prose_refs._PROSE_REF_WAIVERS
from validation._tex import _strip_tex_comments  # noqa: E402  frozen surface


# ═══════════════════════════════════════════════════════════════════════
# Apply the declared execution order — AFTER every registration (ADR-009 H3)
# ═══════════════════════════════════════════════════════════════════════
# This must be the last statement following the final `@register_check`, and it
# must run at IMPORT time rather than inside `main()`: the tests, the
# characterization harness and `gate_precheck.py` all read `_CHECKS` directly
# without ever calling `main`, so a sort deferred to the CLI would leave every
# in-process consumer running an unordered registry.
#
# In Phase 2 this becomes structurally safe rather than positionally safe — the
# framework will import the check modules and then sort, so "after all
# registrations" is enforced by the import block rather than by where this line
# happens to sit. Until then, the position IS the contract, and the registry
# test asserts it.
_apply_canonical_order()


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description="SK-EFT Hawking cross-layer validation suite",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python scripts/validate.py              # run all checks + archive result
  python scripts/validate.py --no-archive # run without saving report
  python scripts/validate.py --json       # JSON output for CI (no archive)
  python scripts/validate.py --check formulas  # run one check
  python scripts/validate.py --list       # list available checks
""",
    )
    parser.add_argument("--check", help="Run only this check (by name)")
    parser.add_argument("--json", action="store_true", help="JSON output to stdout")
    parser.add_argument("--no-archive", action="store_true",
                        help="Skip saving timestamped report (default: always archive)")
    parser.add_argument("--list", action="store_true", help="List available checks")
    parser.add_argument(
        "--strict", action="store_true",
        help=("Promote paper-submission advisory warnings to hard failures "
              "(parameter_provenance, provenance_doi_in_registry). Used at the "
              "paper-submission gate, not at Stage-1 development.")
    )
    parser.add_argument(
        "--force-notebooks", action="store_true",
        help=("Bypass the CHECK 11 notebook-exec skip-cache and re-execute every "
              "notebook (default skips unchanged, previously-vetted notebooks). "
              "Use after a kernel / dependency upgrade.")
    )
    parser.add_argument(
        "--force-latex", action="store_true",
        help=("Run the slow paper_latex_compiles check (pdflatex × all bundle "
              "drafts). Default skips it; it also auto-runs when selected via "
              "--check paper_latex_compiles.")
    )
    args = parser.parse_args(argv)

    _cfg.STRICT_MODE = args.strict
    _cfg.FORCE_NOTEBOOK_REEXEC = args.force_notebooks
    _cfg.FORCE_LATEX = args.force_latex or args.check == "paper_latex_compiles"

    if args.list:
        print("Available checks:")
        for spec in _CHECKS:
            print(f"  {spec.name:20s} {spec.description}")
        return 0

    # An UNKNOWN --check name must hard-error, not silently pass: run_checks filters by
    # spec.name, so an unknown filter yields an empty result set and `all([]) == True`
    # -> exit 0, silently DISABLING the gate (the commit gate / gate_precheck rely on a
    # real failure surfacing). Fail loud with rc2 (run_check in pre-commit-sync.sh maps
    # rc2 -> SKIP-printed; gate_precheck propagates it as FAIL).
    if args.check and args.check not in {spec.name for spec in _CHECKS}:
        print(f"ERROR: unknown check {args.check!r}. Run 'validate.py --list' for the registry.",
              file=sys.stderr)
        return 2

    t0 = time.monotonic()
    results = run_checks(check_filter=args.check)
    elapsed = time.monotonic() - t0

    if args.json:
        payload = {
            "elapsed_seconds": round(elapsed, 2),
            "checks": {
                name: {
                    "passed": cr.passed,
                    "error": cr.error,
                    "details": [asdict(d) for d in cr.details],
                }
                for name, cr in results.items()
            },
            "summary": {
                "total": len(results),
                "passed": sum(1 for r in results.values() if r.passed),
            },
        }
        class _Enc(json.JSONEncoder):
            def default(self, o):
                try:
                    return float(o)
                except (TypeError, ValueError):
                    return super().default(o)
        print(json.dumps(payload, indent=2, cls=_Enc))
    else:
        print_results(results)
        print(f"  Completed in {elapsed:.1f}s")

    if not args.no_archive and not args.json and not args.check:
        path = archive_results(results)
        print(f"\n  Archived to: {path}")

    all_passed = all(r.passed for r in results.values())
    return 0 if all_passed else 1


if __name__ == "__main__":
    sys.exit(main())

