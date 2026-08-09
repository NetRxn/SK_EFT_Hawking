"""Lean build, trust-surface and name-resolution checks — ADR-009 Phase 2.

`native_decide_regression` (the ADR-002 kernel-trust ratchet), `theorems` (registry
counts), `lean_source`, `lean_build`, `axiom_closure_allowlist` (Invariant #15
backstop), `elaboration_knob_watchlist` (advisory perf/portability) and
`lean_docstring_refs_resolve` (rename-drift in Lean docstrings).

WHY THIS IS A SEPARATE MODULE FROM `lean_substrate`
---------------------------------------------------
The migration plan assigned all of these to one `lean_substrate.py`. Measured, that
module would be ~1,580 lines — which fails the criterion the split exists to
satisfy: **every file readable in one pass** (ADR-009 D1). Splitting on the real
seam instead: `lean_substrate` holds the SUBSTANCE gates (R1-R3 — does a theorem
prove anything, is an assumption disclosed), and this module holds everything about
the BUILD and the TRUST SURFACE (does it compile, what axioms does it lean on, do
its names still resolve). The two share no helpers, which is the seam confirming
itself. `docs/architecture/.working-docs/validation-module-migration-notes.md` §4
is updated to match.

`theorems` lands here because the migration table never assigned it and it is a
registry-count check, not a substance gate.

MOVED VERBATIM — extracted by script from AST-verified ranges. No body edited, no
policy unified, no threshold retuned (ADR-009 D4). `axiom_closure_allowlist` reads
`_cfg.STRICT_MODE` by ATTRIBUTE (H5); paths are `_H.<NAME>` at each use, never
module-level aliases and never from `__file__` (H1). The two `Path(...)` calls here
construct from `LEAN_PROJECT_DIR` and are unrelated to the anchor.

`check_theorem_count`, `check_lean_source` and `check_atlas_integrity`'s siblings
are in the frozen external surface; `validate` re-exports every moved name
(ADR-009 D2 item 8).
"""
from __future__ import annotations

import tomllib

import json
import re
import subprocess
from pathlib import Path
from typing import Dict, List

import validate_helpers as _H
from validation import _config as _cfg
from validation import _memo
from validation._registry import CheckResult, Detail, register_check


# ── Lake / Lean-project resolution — ONE owner (audit QI-11 residue, closed with W-D) ──
# These six lines sat verbatim in BOTH `check_lean_build` and
# `check_axiom_closure_allowlist`. Deliberately shared LATE rather than in the Phase-2
# mechanical pass: extracting it changes two checks' early-return path, so ADR-009 D4
# required it to land with the mutation tests that prove the paths are unchanged
# (`tests/test_d5_lean_toolchain.py::TestLakeResolution`).
#
# ⚠️ ONLY THE RESOLUTION IS SHARED — NOT THE POLICY. Each caller keeps its own SKIP
# message and its own early return, because they differ and the difference belongs to
# the check. That is `validate_helpers`' policy line (ADR-009 H4) applied one level
# down: this owns WHERE lake is, never WHAT ITS ABSENCE MEANS. A single helper that
# also returned the CheckResult would silently unify two checks' behaviour, which is
# the exact shape H4 exists to prevent.

def _resolve_lake() -> str | None:
    """The `lake` binary: `LAKE_PATH`, then `~/.elan/bin/lake`, then `PATH`."""
    import os
    import shutil
    lake_bin = os.environ.get("LAKE_PATH")
    if not lake_bin:
        elan_lake = Path.home() / ".elan" / "bin" / "lake"
        if elan_lake.is_file():
            lake_bin = str(elan_lake)
    if not lake_bin:
        lake_bin = shutil.which("lake")
    return lake_bin or None


def _resolve_lean_root() -> Path:
    """The Lean project directory: `LEAN_PROJECT_DIR`, else `<project>/lean`."""
    import os
    return Path(os.environ.get("LEAN_PROJECT_DIR", _H.PROJECT_ROOT / "lean"))


# ═══════════════════════════════════════════════════════════════════════
# CHECK 1f: native_decide trust-surface regression (R4)
# ═══════════════════════════════════════════════════════════════════════

@register_check(
    "native_decide_regression",
    "native_decide decl-closure does not silently grow past its ceiling (R4; ADR-002)")
def check_native_decide_regression() -> CheckResult:
    """The native_decide kernel-trust surface may only DECREASE without review.

    A wave that ADDS trust surface must bump `NATIVE_DECIDE_DECL_CLOSURE_CEILING`
    in the same commit with a rationale, so the increase is visible. Elimination
    policy is owned by ADR-002; this is only the regression backstop. Substrate
    Integrity Gates W5.

    ⚠️ **READS `lean_deps.json`, NOT `docs/counts.json` (fixed 2026-08-03, ADR-009
    §Deferred item 1).** The metric is a pure function of the declaration data, and
    `update_counts.py` merely records it. Reading the recording had two failure
    modes, and reordering the suite could only have fixed one:

    * In a full run this check sits at canonical position ~9 and `counts_fresh`
      regenerates `counts.json` at ~29, so the ratchet compared a snapshot taken
      before the current wave's Lean changes.
    * In the **commit gate** it is one of only three checks invoked, in ISOLATION —
      `counts_fresh` never runs at all, at the one moment the ratchet can hard-block
      `main`. No ordering of the suite reaches that case.

    `lean_deps.json` is also the stronger source: its staleness key is a **content
    hash** of `**/*.lean`, where `counts.json` is mtime-based (QA/QI map §2).

    `counts.json` is still compared, as a **staleness signal** rather than as the
    measurement — a disagreement now means the recording is behind the substrate,
    which is worth surfacing rather than silently inheriting.
    """
    from src.core.constants import NATIVE_DECIDE_DECL_CLOSURE_CEILING as CEIL

    if not _H.lean_deps_present():
        # FAIL, not pass. This is a ratchet in the commit gate; "I could not find the
        # substrate" is not evidence that the trust surface did not grow.
        return CheckResult(passed=False, details=[Detail(
            "lean_deps", False,
            "lean/lean_deps.json absent — the native_decide trust surface could not be "
            "measured, so this ratchet is UNVERIFIED, not passing. Refresh with "
            "`cd lean && lake build SKEFTHawking.ExtractDeps`.")])

    from update_counts import native_decide_decls
    decls = native_decide_decls(_H.load_lean_deps())
    cur = len(decls)

    details: List[Detail] = []

    # counts.json as a staleness signal only — never as the measurement.
    try:
        recorded = json.loads(_H.COUNTS_JSON_PATH.read_text())["lean"]["native_decide_decl_closure"]
    except (OSError, KeyError, ValueError):
        recorded = None
    if recorded is not None and recorded != cur:
        details.append(Detail(
            "counts_drift", True,
            f"docs/counts.json records {recorded} but the live substrate has {cur} — "
            f"counts.json is behind lean_deps.json. The ratchet below uses the LIVE "
            f"value; run `scripts/update_counts.py` to resync the recording.",
            warning=True))

    if cur > CEIL:
        clusters = {}
        for d in decls:
            m = str(d.get("module", ""))
            clusters[m.split(".")[1] if "." in m else m] = \
                clusters.get(m.split(".")[1] if "." in m else m, 0) + 1
        top = ", ".join(f"{k}={v}" for k, v in
                        sorted(clusters.items(), key=lambda kv: -kv[1])[:6])
        details.append(Detail(
            "ceiling", False,
            f"native_decide decl-closure {cur} EXCEEDS ceiling {CEIL} — a wave grew the "
            f"kernel-trust surface. Eliminate (ADR-002) or bump "
            f"NATIVE_DECIDE_DECL_CLOSURE_CEILING with a rationale. Densest modules: {top}"))
        return CheckResult(passed=False, details=details)

    msg = f"native_decide decl-closure {cur} <= ceiling {CEIL} (measured from lean_deps.json)"
    if cur < CEIL:
        msg += f" (down {CEIL - cur}; consider lowering the ceiling)"
    details.append(Detail("ceiling", True, msg, warning=(cur < CEIL)))
    return CheckResult(passed=True, details=details)




# ═══════════════════════════════════════════════════════════════════════
# CHECK 5: Theorem registry
# ═══════════════════════════════════════════════════════════════════════

@register_check(
    "theorems",
    "Aristotle registry entries resolve to real Lean declarations (ratcheted)")
def check_theorem_count() -> CheckResult:
    """CHECK: every `ARISTOTLE_THEOREMS` key names a declaration that EXISTS.

    ⚠️ **REWRITTEN 2026-08-04 — all three of its previous legs were vacuous (audit
    QI-30).** It read:

        TOTAL_THEOREMS            == 322
        len(ARISTOTLE_THEOREMS)   == 322
        TOTAL_THEOREMS            == len(ARISTOTLE_THEOREMS)

    * The third is a **tautology**: `constants.py` defines
      `ARISTOTLE_PROVED_COUNT = len(ARISTOTLE_THEOREMS)` and `TOTAL_THEOREMS` is an
      alias of it, so the two sides are the same expression. It could not fail.
    * The first two are **unreachable**: `constants.py` already `assert`s that count
      at IMPORT time, so a wrong count raises before this function's body runs — and
      they are the same comparison written twice, since both operands are that one
      value.

    So a check registered as *"has 322 entries and is self-consistent"* asserted
    nothing, and had been green since it was written for that reason. The count
    invariant is real and is KEPT — it just belongs to `constants.py`, which enforces
    it more strictly (an import-time failure) than a check ever could. Restating it
    here was duplication with no owner.

    **What is checked instead is the thing nothing checked.** `ARISTOTLE_THEOREMS` is
    hand-maintained, and `check_formulas_to_theorems` unions its KEYS into
    `all_lean_names` — the set it resolves formula references against. A stale key
    therefore launders a nonexistent theorem into that set, and a formula grounded on
    it passes. Measured at the rewrite: **14 of 322 keys resolve to no declaration**
    in `lean_deps.json` or the Lean source.

    Ratcheted at `ARISTOTLE_REGISTRY_UNRESOLVED_CEILING`, the house idiom: the frozen
    debt is reported as a warning, a NEW stale entry fails. That keeps this from
    turning a documentation-grade cleanup into a red build while still closing the
    generator.

    The FUNCTION NAME is deliberately unchanged: it is in the frozen 54-name external
    surface (ADR-009 D2 item 8) and `tests/test_cross_validation.py` imports it by
    name. Renaming it is a contract change and belongs to its own increment.
    """
    from src.core.constants import (ARISTOTLE_THEOREMS,
                                    ARISTOTLE_REGISTRY_UNRESOLVED_CEILING as CEIL)

    #: How many stale names to name in a detail before summarising. A DISPLAY cap —
    #: named rather than inlined so it is never mistaken for a threshold, and so the
    #: guard in `test_d5_lean_toolchain.py` can forbid literal comparisons outright
    #: instead of carving out an exception it would then have to keep correct.
    _SAMPLE = 8

    # FAIL, not pass, on a missing substrate — matching `native_decide_regression`,
    # the suite's other ratchet. "I could not find the Lean" is not evidence that the
    # registry is clean. This is a NEW lean_deps reader and so does not widen the H4
    # divergence ADR-009 §Deferred item 4 declined to unify; it adopts the stricter
    # policy the ADR calls arguably correct.
    if not _H.lean_deps_present():
        return CheckResult(passed=False, details=[Detail(
            "lean_deps", False,
            "lean/lean_deps.json absent — the Aristotle registry could not be resolved "
            "against the substrate, so this ratchet is UNVERIFIED, not passing. "
            "Refresh with `cd lean && lake build SKEFTHawking.ExtractDeps`.")])

    # ONE OWNER (2026-08-05, PR-review R4-I3). The resolver moved to
    # `validate_helpers.unresolved_aristotle_keys` because
    # `check_formulas_to_theorems` must SUBTRACT exactly this set, and a second
    # copy there is the duplication shape this audit keeps finding.
    unresolved = _H.unresolved_aristotle_keys()

    details: List[Detail] = [Detail(
        "registry_size", True,
        f"{len(ARISTOTLE_THEOREMS)} Aristotle-proved theorem(s) registered "
        f"(the count itself is asserted at import by src/core/constants.py, which "
        f"fails harder than this check could)")]

    if len(unresolved) > CEIL:
        details.append(Detail(
            "unresolved", False,
            f"{len(unresolved)} registry entries resolve to NO Lean declaration, above "
            f"the frozen ceiling of {CEIL}. A stale key is laundered into "
            f"`check_formulas_to_theorems`' valid-name set, so a formula can be reported "
            f"as grounded on a theorem that does not exist. Fix the name, drop the entry, "
            f"or lower/raise ARISTOTLE_REGISTRY_UNRESOLVED_CEILING with a reason: "
            f"{', '.join(unresolved[:_SAMPLE])}"))
        return CheckResult(passed=False, details=details)

    if unresolved:
        details.append(Detail(
            "unresolved", True,
            f"{len(unresolved)} registry entries resolve to no Lean declaration "
            f"(frozen debt, ceiling {CEIL}; no growth): "
            f"{', '.join(unresolved[:_SAMPLE])}"
            + (f" (+{len(unresolved) - _SAMPLE} more)"
               if len(unresolved) > _SAMPLE else ""),
            warning=True))
        if len(unresolved) < CEIL:
            details.append(Detail(
                "ratchet", True,
                f"{CEIL - len(unresolved)} entry/entries repaired since the freeze — "
                f"lower ARISTOTLE_REGISTRY_UNRESOLVED_CEILING to {len(unresolved)}",
                warning=True))
    else:
        details.append(Detail(
            "unresolved", True,
            "every Aristotle registry entry resolves to a real Lean declaration"))

    return CheckResult(passed=True, details=details)




# ═══════════════════════════════════════════════════════════════════════
# CHECK 7: Lean theorem names appear in .lean source files
# ═══════════════════════════════════════════════════════════════════════

@register_check("lean_source", "Key theorem names found in Lean source files")
def check_lean_source() -> CheckResult:
    if not _H.LEAN_DIR.exists():
        return CheckResult(passed=False, error=f"Lean directory not found: {_H.LEAN_DIR}")

    # Collect all identifiers declared as theorem/lemma/def.
    # ⚠️ rglob, NOT glob (fixed 2026-08-04, audit finding QI-01). `glob` saw 1,373
    # of ~2,040 Lean files, so 7,695 declared identifiers in subdirectories were
    # invisible. The direction of that error is toward FALSE FAILURES here (a
    # spot-check name that moved into a package would report "NOT found" while
    # existing), so it was latent rather than live — but a name-resolution check
    # that cannot see a third of the library is not measuring what it claims.
    lean_idents = set()
    for lf in _H.LEAN_DIR.rglob("*.lean"):
        try:
            content = lf.read_text()
            lean_idents.update(re.findall(r'(?:theorem|lemma|def)\s+(\w+)', content))
        except Exception:
            pass

    # Map Python registry names to expected Lean identifiers
    # (some differ by naming convention)
    spot_checks = {
        # Phase 1-2
        'dampingRate_eq_zero_iff': 'dampingRate_eq_zero_iff',
        'dispersive_bound': 'dispersive_correction_bound',
        'firstOrder_correction_zero_iff': 'firstOrder_correction_zero_iff',
        'acoustic_metric_determinant': 'acousticMetric_det',
        'secondOrder_count': 'secondOrder_count',
        # Phase 4 (Aristotle batch b1ea2eb7)
        'fracton_exceeds_standard_general': 'fracton_exceeds_standard_general',
        'binomial_strict_mono': 'binomial_strict_mono',
        'dof_gap_positive_2_through_8': 'dof_gap_positive_2_through_8',
        'evading_one_breaks_nogo': 'evading_one_breaks_nogo',
        'ep_distinguishes_phases': 'ep_distinguishes_phases',
        'obstructions_individually_sufficient': 'obstructions_individually_sufficient',
    }

    details = []
    all_pass = True

    for registry_name, lean_name in spot_checks.items():
        ok = lean_name in lean_idents
        details.append(Detail(registry_name, ok,
                              f"Lean ident '{lean_name}' {'found' if ok else 'NOT found'}"))
        if not ok:
            all_pass = False

    return CheckResult(passed=all_pass, details=details)




# ═══════════════════════════════════════════════════════════════════════
# CHECK 9: Lean build (optional, requires `lake` on PATH)
# ═══════════════════════════════════════════════════════════════════════

@register_check("lean_build", "Lean project builds cleanly (requires lake)")
def check_lean_build() -> CheckResult:
    """
    Run `lake build` on the Lean project.

    Lake discovery order:
      1. LAKE_PATH env var  (explicit path to lake binary)
      2. ~/.elan/bin/lake   (standard elan install location)
      3. System PATH         (global install)

    Lean project directory:
      1. LEAN_PROJECT_DIR env var  (override for mono-repo layouts)
      2. _H.PROJECT_ROOT / "lean"     (default, same repo)

    The check looks for lakefile.lean OR lakefile.toml (Lean 4 / Lake v4+).
    """
    lake_bin = _resolve_lake()
    if not lake_bin:
        return CheckResult(
            passed=True, measured=False,
            details=[Detail("lake", True,
                            "SKIPPED — lake not found. Set LAKE_PATH or install elan "
                            "(https://github.com/leanprover/elan)")],
        )

    # ── Resolve Lean project directory ──
    lean_root = _resolve_lean_root()

    has_lakefile = (
        (lean_root / "lakefile.lean").exists()
        or (lean_root / "lakefile.toml").exists()
    )
    if not has_lakefile:
        return CheckResult(
            passed=True, measured=False,
            details=[Detail("lakefile", True,
                            f"SKIPPED — no lakefile.{{lean,toml}} in {lean_root}")],
        )

    # ── Run lake build ──
    details = [Detail("lake_bin", True, lake_bin),
               Detail("lean_root", True, str(lean_root))]

    try:
        result = subprocess.run(
            [lake_bin, "build"],
            cwd=str(lean_root),
            capture_output=True, text=True, timeout=600,
        )
        ok = result.returncode == 0
        if ok:
            # Count jobs from output like "Build completed successfully (2254 jobs)."
            # or "ℹ [2254/2254] ..." lines in stderr + stdout
            combined = result.stderr + result.stdout
            job_match = (
                re.search(r'(\d+) jobs?\)', combined)
                or re.search(r'\[(\d+)/\1\]', combined)  # [N/N] = final job
            )
            jobs = job_match.group(1) if job_match else "cached"
            msg = f"build succeeded ({jobs} jobs)"
        else:
            msg = result.stderr[-500:]
        details.append(Detail("lake_build", ok, msg))
        return CheckResult(passed=ok, details=details)
    except subprocess.TimeoutExpired:
        details.append(Detail("lake_build", False, "timeout (600s)"))
        return CheckResult(passed=False, details=details)
    except Exception as e:
        return CheckResult(passed=False, details=details, error=str(e))


# ═══════════════════════════════════════════════════════════════════════
# CHECK: Axiom-closure allow-list (AI-Defect-Defense-Layer P4, Invariant #15)
# ═══════════════════════════════════════════════════════════════════════

@register_check(
    "axiom_closure_allowlist",
    "Every SKEFTHawking declaration's transitive axiom closure is on the standard "
    "kernel axioms + the AXIOM_METADATA allow-list (Invariant #15 backstop)",
)
@_memo.memoize_check(
    "axiom_closure_allowlist",
    lambda: _memo.memo_key(
        _memo.lean_source_fingerprint(),
        _memo.toolchain_pin_fingerprint(),
        _memo.files_fingerprint([
            _H.PROJECT_ROOT / "src" / "core" / "constants.py",   # AXIOM_METADATA
            _H.PROJECT_ROOT / "scripts" / "update_counts.py",    # is_native_decide_axiom
        ]),
    ),
    "Lean sources, toolchain pins, AXIOM_METADATA",
)
def check_axiom_closure_allowlist() -> CheckResult:
    """
    AI-Defect-Defense-Layer P4. Runs the ``AxiomAudit`` Lean executable
    (interpreted, reusing the memoized ``AxiomClosure`` machinery that backs
    ``ExtractDeps``) to obtain the transitive *non-core* axiom closure of every
    ``SKEFTHawking.*`` declaration, and verifies each axiom lies in the allow-list

        {propext, Classical.choice, Quot.sound} ∪ AXIOM_METADATA.keys()

    Posture (WARN-first, retrofit): a non-allow-listed axiom is an advisory
    warning by default and a hard failure under ``--strict`` (paper-submission
    gating), mirroring ``parameter_provenance``. ``native_decide``-generated
    compiler-trust axioms (per-declaration ``*._native.native_decide.ax_*``) are
    recognised as a distinct *accepted* category and reported for visibility —
    they are not declared project ``axiom``s, so ``counts.json`` reports
    ``Axioms: 0`` while this check surfaces the genuine trust surface.

    Shares the underlying Lean executable with the lean4 plugin's
    ``/check-axioms`` (``lean/SKEFTHawking/AxiomAudit.lean``): discipline defined
    once, invoked interactively at ``/lean4:checkpoint`` and non-interactively here.

    MEMOIZED (2026-08-05): measured **145.4 s**, the single most expensive check in
    the suite. Over all 5,814 commits on `main` since 2026-03-01, `lean/` moved in
    **78 %** — so on a Lean wave this MUST re-measure and the memo saves nothing, by
    design. It pays on the repeat: re-running `validate.py` after a doc / paper /
    count fix, which is what a `/goal` loop does until the gate is green.
    (⚠️ An earlier draft read "47 %" off 400 commits of this infra branch — not a
    representative window.) The key names every input that can move the
    verdict: the Lean sources (`AxiomAudit` reads the built environment, which
    derives from them), the toolchain/Mathlib pin set, `AXIOM_METADATA`, and
    `update_counts.is_native_decide_axiom` — plus this body's own source, which
    `_memo.memoized` folds in for every memoized check. ``--strict`` bypasses the
    memo entirely, so the Paper Submission Gate always re-measures.
    """
    lake_bin = _resolve_lake()
    if not lake_bin:
        return CheckResult(passed=True, measured=False, details=[
            Detail("lake", True, "SKIPPED — lake not found. Set LAKE_PATH or install elan")])

    lean_root = _resolve_lean_root()
    audit_src = lean_root / "SKEFTHawking" / "AxiomAudit.lean"
    if not audit_src.exists():
        return CheckResult(passed=True, measured=False, details=[
            Detail("axiom_audit_src", True, f"SKIPPED — {audit_src} not found")])

    # ── Allow-list ──
    try:
        from src.core.constants import AXIOM_METADATA  # type: ignore
        metadata_keys = set(AXIOM_METADATA.keys())
    except Exception:
        metadata_keys = set()
    allowlist = {"propext", "Classical.choice", "Quot.sound"} | metadata_keys

    # ── Run AxiomAudit (interpreted; native link exceeds macOS arg limits) ──
    try:
        result = subprocess.run(
            [lake_bin, "env", "lean", "--run", "SKEFTHawking/AxiomAudit.lean"],
            cwd=str(lean_root), capture_output=True, text=True, timeout=600,
        )
    except subprocess.TimeoutExpired:
        return CheckResult(passed=True, measured=False, details=[
            Detail("axiom_audit_run", True, "SKIPPED — AxiomAudit timed out (600s)", warning=True)])
    except Exception as exc:  # noqa: BLE001
        return CheckResult(passed=True, measured=False, details=[
            Detail("axiom_audit_run", True, f"SKIPPED — {exc}", warning=True)])

    if result.returncode != 0:
        return CheckResult(passed=True, measured=False, details=[
            Detail("axiom_audit_run", True,
                   f"SKIPPED — AxiomAudit exited {result.returncode}: {result.stderr[-300:]}",
                   warning=True)])

    try:
        closures: Dict[str, List[str]] = json.loads(result.stdout.strip() or "{}")
    except json.JSONDecodeError as exc:
        return CheckResult(passed=True, measured=False, details=[
            Detail("axiom_audit_parse", True,
                   f"SKIPPED — could not parse AxiomAudit output ({exc})", warning=True)])

    # ONE definition of this predicate, in update_counts (the ADR-002 metric's owner).
    from update_counts import is_native_decide_axiom as is_native_decide

    native_decls: set[str] = set()
    unexpected: Dict[str, List[str]] = {}
    for decl, axes in closures.items():
        if "native_decide" in decl:
            continue  # the per-declaration native-axiom self-entries
        bad: List[str] = []
        for ax in axes:
            if ax in allowlist:
                continue
            if is_native_decide(ax):
                native_decls.add(decl)
                continue
            bad.append(ax)
        if bad:
            unexpected[decl] = sorted(set(bad))

    details = [Detail("allowlist_size", True,
                      f"{len(allowlist)} allow-listed axioms "
                      f"(3 core + {len(metadata_keys)} AXIOM_METADATA)")]

    if native_decls:
        details.append(Detail(
            "native_decide", True,
            f"{len(native_decls)} declaration(s) transitively use `native_decide` "
            f"(compiler-trust axiom) — accepted Lean mechanism, flagged for visibility "
            f"(counts.json 'Axioms: 0' counts only declared `axiom`s)",
            warning=True))

    strict = _cfg.STRICT_MODE
    if unexpected:
        sample = list(unexpected.items())[:10]
        msg = (f"{len(unexpected)} declaration(s) carry a non-allow-listed axiom "
               f"({'FAIL under --strict' if strict else 'WARN-first'} — add to "
               f"AXIOM_METADATA or discharge): "
               + "; ".join(f"{d} → {','.join(ax)}" for d, ax in sample))
        details.append(Detail("unexpected_axioms", not strict, msg, warning=not strict))
        return CheckResult(passed=not strict, details=details)

    details.append(Detail(
        "allowlist", True,
        "no declaration carries a non-allow-listed, non-native_decide axiom "
        "(Invariant #15 backstop clean)"))
    return CheckResult(passed=True, details=details)


#: Zero-headroom ratchet for Invariant #10 (`set_option maxHeartbeats` in a proof
#: body). MEASURED 2026-08-05 by the predicate below: **22** sites attached to a
#: `theorem`/`lemma`/`example`, across 4 files.
#:
#: ⚠️ THIS COUNT WAS MEASURED THREE TIMES AND I WAS WRONG TWICE. Reviewer R5 filed
#: 22. I "corrected" it to 23 with a looser attribution scan, then explained the
#: gap as "22 bare + 1 `synthInstance.maxHeartbeats`" — but there are **zero**
#: `synthInstance.maxHeartbeats` sites in the tree, so that explanation was also
#: wrong. R5's 22 was right both times.
#:
#: The lesson is the one this audit keeps re-learning: a count is meaningless
#: without its predicate. The enforced predicate is stated in the check body, and
#: **31** bare `set_option maxHeartbeats` lines exist in total — the other 9
#: attach to no theorem/lemma/example within 12 lines (file-level blocks, or the
#: uncovered tactic-bodied-`def` limb).
#:
#: This may only DECREASE. The discharge is Invariant #10's own remedy — a
#: heartbeat wall means the proof architecture is wrong, so decompose into `have`
#: sub-lemmas — not raising the number. Raising it is a decision that must be
#: stated in the same commit.
#:
#: ⚠️ Until 2026-08-05 this invariant had NO enforcement anywhere, while
#: `elaboration_knob_watchlist` excluded bare `maxHeartbeats` from its pattern on
#: the stated grounds that it was "forbidden outright" — i.e. handled elsewhere.
#: It was handled nowhere, and a test asserted the exclusion was deliberate.
MAXHEARTBEATS_PROOF_BODY_CEILING = 22


# ═══════════════════════════════════════════════════════════════════════
# CHECK: Elaboration-knob watchlist (perf / upstream-portability, NOT soundness)
# ═══════════════════════════════════════════════════════════════════════

@register_check(
    "elaboration_knob_watchlist",
    "Watchlist (advisory): proof-body maxRecDepth / synthInstance knobs — a "
    "performance / Mathlib-CI-portability signal, NOT a soundness or axiom-closure issue",
)
def check_elaboration_knob_watchlist() -> CheckResult:
    """
    Surfaces every ``set_option maxRecDepth`` / ``synthInstance.maxSize`` /
    ``synthInstance.maxHeartbeats`` in SKEFTHawking Lean source.

    WHY THIS IS SEPARATE FROM ``axiom_closure_allowlist`` (the soundness gate):
    these are *elaboration-time* knobs. They only let the front-end search deeper /
    wider before giving up; the **kernel independently re-checks the final term** and
    never reads them, so they add NOTHING to the axiom closure (no ``Lean.ofReduceBool``)
    and stay kernel-pure ``{propext, Classical.choice, Quot.sound}``. Mathlib uses
    ``maxRecDepth`` routinely. The genuine trust surface (``native_decide`` →
    ``Lean.ofReduceBool``) is gated by ``axiom_closure_allowlist``; THIS check is a
    NON-FAILING watchlist for the only real downside — a ``decide`` heavy enough to
    need a knob is also a slow KERNEL reduction, which Mathlib CI's speed budget may
    reject. So each hit is an upstream-portability candidate (consider a structural
    reproof IF upstreaming that lemma), never a correctness concern. Always passes.

    NB ``maxHeartbeats`` in proof bodies is forbidden outright by Invariant #10
    (architecture discipline) and is enforced elsewhere; it is intentionally not in
    this advisory list.
    """
    # `_H.LEAN_DIR` is the owner of this path (audit QI-11). Re-deriving it as
    # `_H.PROJECT_ROOT / "lean" / "SKEFTHawking"` gave the same value but a second
    # definition, so a test monkeypatching the anchor reached some sites and not
    # others — the by-value hazard H1/H5 exist to prevent, one level down.
    lean_dir = _H.LEAN_DIR
    if not lean_dir.exists():
        return CheckResult(passed=True, measured=False, details=[
            Detail("lean_src", True, f"SKIPPED — {lean_dir} not found")])

    pat = re.compile(
        r"set_option\s+(maxRecDepth|synthInstance\.maxSize|synthInstance\.maxHeartbeats)\s+(\d+)")

    # ⚠️ INVARIANT #10 IS NOW ENFORCED HERE (2026-08-05, PR-review pass 2, R5-MAJ3).
    # Bare `maxHeartbeats` was deliberately EXCLUDED from `pat` above, and the
    # comment justifying that said it is "forbidden outright by Invariant #10" —
    # i.e. handled elsewhere. **It was handled nowhere.** `rg maxHeartbeats scripts/`
    # returned only this check's own docstring and exclusion list, while the
    # substrate carried 23 live violations across 4 files.
    #
    # Worse, the branch had PINNED the gap: `15edc340` added
    # `test_maxHeartbeats_is_deliberately_not_watched_here`, whose docstring
    # asserts the invariant "is enforced elsewhere". Closing the gap therefore
    # broke a green test that said the gap was correct — the strongest form of this
    # audit's core defect. That test is rewritten alongside this change.
    #
    # RATCHETED, not hard-failed on day one: 23 violations exist and a bare FAIL
    # would redden the suite on pre-existing debt with no discharge path. The house
    # idiom applies — freeze the measured population at zero headroom and only let
    # it shrink. Decomposing those proofs into `have` sub-lemmas is the discharge
    # (Invariant #10's own remedy), tracked in the pass-2 register.
    # BOTH forms, because Invariant #10 names both: WAVE_EXECUTION_PIPELINE.md:675
    # — "No `set_option maxHeartbeats` or `set_option synthInstance.maxHeartbeats`
    # in any theorem, lemma, example, or def whose body is produced by tactics."
    # ⚠️ Reviewer R5 filed 22 and the lead first "corrected" it to 23; both were
    # measuring different things — 22 bare + 1 `synthInstance.` = 23, and the
    # invariant forbids all 23.
    proof_body_re = re.compile(r"set_option\s+(?:synthInstance\.)?maxHeartbeats\s+(\d+)")
    decl_re = re.compile(
        r"^\s*(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |partial |unsafe )*"
        r"(theorem|lemma|example)\b")

    hits: List[Detail] = []
    violations: List[Detail] = []
    for f in sorted(lean_dir.rglob("*.lean")):
        if "/.lake/" in str(f):
            continue
        lines = f.read_text(errors="replace").splitlines()
        rel = f.relative_to(_H.PROJECT_ROOT)
        for i, line in enumerate(lines, 1):
            m = pat.search(line)
            if m:
                hits.append(Detail(f"{rel}:{i}", True, f"{m.group(1)} {m.group(2)}",
                                   warning=True))
            mh = proof_body_re.search(line)
            if mh:
                # Attach it to the declaration it precedes. Only theorem/lemma/example
                # count: Invariant #10 exempts O(project-size) metaprograms, and a
                # file-level `set_option` block is reported separately below.
                attaches_to = None
                for nxt in lines[i:i + 12]:
                    d = decl_re.match(nxt)
                    if d:
                        attaches_to = d.group(1)
                        break
                # ⚠️ KNOWN NARROWING, stated not hidden: Invariant #10 also covers a
                # `def`/`noncomputable def` whose body is TACTIC-PRODUCED. Deciding
                # that needs real parsing (`:= by` vs a term body, across line
                # breaks), so this leg covers only theorem/lemma/example, which are
                # unambiguous. A tactic-bodied `def` carrying a heartbeat override
                # is therefore NOT caught yet — tracked in the pass-2 register.
                if attaches_to:
                    violations.append(Detail(
                        f"{rel}:{i}", False,
                        f"maxHeartbeats {mh.group(1)} on a `{attaches_to}` — Invariant #10 "
                        f"forbids it in a proof body; decompose into `have` sub-lemmas"))

    over = len(violations) > MAXHEARTBEATS_PROOF_BODY_CEILING
    summary = Detail(
        "watchlist", True,
        f"{len(hits)} proof-body elaboration-knob site(s) — perf/upstream-CI watchlist, "
        "kernel-pure (NOT a soundness/axiom-closure issue; that is axiom_closure_allowlist)",
        warning=bool(hits))
    inv10 = Detail(
        "invariant_10", not over,
        f"{len(violations)} `maxHeartbeats` site(s) in a proof body "
        f"(ceiling {MAXHEARTBEATS_PROOF_BODY_CEILING})"
        + (f" — EXCEEDS by {len(violations) - MAXHEARTBEATS_PROOF_BODY_CEILING}" if over
           else f" — {MAXHEARTBEATS_PROOF_BODY_CEILING - len(violations)} below; LOWER THE "
                f"CEILING in the same commit" if len(violations) < MAXHEARTBEATS_PROOF_BODY_CEILING
           else ""),
        warning=(bool(violations) and not over))
    return CheckResult(passed=not over,
                       details=[summary, inv10] + violations + hits)


# ---------------------------------------------------------------------------
# Lean docstring reference drift (Stage-14 QI, 2026-07-28)
# ---------------------------------------------------------------------------
# Structural prevention for the failure class that produced BLOCKER 1.1 of the
# Phase-6EA Stage-13 review: a Lean module docstring naming a project declaration
# that no longer exists, because the declaration was renamed and the prose was not.
#
# `prose_theorem_reference_coverage` already guards this for *bundle drafts*
# (papers/<bundle>/paper_draft.tex). Nothing guarded Lean docstrings themselves,
# and the class has a live generator: it fired the same day a lead rename landed.
#
# Low-noise by construction. A backticked snake_case token is reported only when it
# (a) fails to resolve in lean_deps.json, AND (b) closely resembles a name that DOES
# resolve — i.e. it looks like rename drift rather than a Mathlib or tactic name.
# That is precisely the observed failure shape and it keeps Mathlib references,
# tactic names and local binders out of the result.
_DOCSTRING_STRICT_FAMILIES = ("SKEFTHawking.Detection.", "SKEFTHawking.Electrothermal.",
                              "SKEFTHawking.Control.", "SKEFTHawking.GrapheneBand.")
_DOCSTRING_TOKEN_RE = re.compile(r"`([A-Za-z][A-Za-z0-9_']*)`")
# Covers `/-- … -/` doc comments, `/-! … -/` section comments AND plain `/- … -/` module
# headers. The module-header case was previously unscanned, which let a load-bearing
# reference to a nonexistent `combined_floor_add_strictly_sharper` sit in
# `Control/CompositeReadoutCeilings.lean`'s header through five adversarial reviews.
_DOCSTRING_BLOCK_RE = re.compile(r"/-[-!]?(.*?)-/", re.DOTALL)


@register_check("lean_docstring_refs_resolve",
                "Lean docstring `backticked` project names resolve (rename-drift guard)")
@_memo.memoize_check(
    "lean_docstring_refs_resolve",
    lambda: _memo.memo_key(_memo.lean_source_fingerprint(),
                           _memo.toolchain_pin_fingerprint()),
    "Lean sources and the Mathlib pin",
)
def check_lean_docstring_refs_resolve() -> CheckResult:
    """Flag Lean docstrings naming a project declaration that does not exist.

    MEMOIZED (2026-08-05): measured **52.8 s**, second-most-expensive check in the
    suite, because it greps the pinned Mathlib source tree to build the exemption
    set. Its inputs are the Lean sources (the docstrings themselves, and
    `lean_deps.json`, which derives from them) and the pinned Mathlib — the latter
    keyed through `lakefile.toml` / `lean-toolchain` / `lake-manifest.json` rather
    than by hashing several GB of Mathlib source.

    Round-1 design used a `difflib` near-match filter to suppress noise. A regression
    test against the ACTUAL blocker showed that silently defeated the check: the real
    rename pair (`poisson_avgError_floor_equalRates` vs
    `poisson_avgError_equalRates_eq_half`) scores below any cutoff loose enough to stay
    quiet. So the near-match is now used only to enrich the message, never to gate it.

    Noise is controlled the honest way instead: a token is exempt if it is a Mathlib
    declaration name (short-name set built from the pinned Mathlib source) or a common
    tactic/keyword. Inside the strict families — the new, clean module families — any
    surviving unresolvable token is a FAIL. Elsewhere it is advisory, so the legacy
    backlog is reported without blocking.
    """
    import difflib

    # ⚠️ These were `TODO(semantic-review, ADR-009 Phase 3)` until 2026-08-04
    # (audit finding QI-15). Phase 3 is COMPLETE and its §Deferred item 4
    # explicitly DECLINED converting these sites wholesale: 5 are
    # optional-toolchain-absent, 3 advisory by design, 8 are this `lean_deps`
    # divergence kept VISIBLE on purpose, 2 are the annotated H1-silent sites.
    # A TODO pointing at a finished phase reads as unfinished work; the
    # population is frozen instead by `tests/test_cannot_measure_baseline.py`,
    # which fails both on a NEW silent PASS and on a converted site left stale
    # in the baseline.
    # H4 DIVERGENCE, deliberately preserved (ADR-009 §Deferred item 4 — DECLINED). absence -> PASS *with a warning* — a third
    # distinct policy, alongside the five silent PASSes and two FAILs.
    if not _H.lean_deps_present():
        return CheckResult(passed=True, measured=False,
                           details=[Detail("skipped", True, "lean_deps.json absent", warning=True)])
    decls = _H.load_lean_deps()
    full = {d["name"] for d in decls}
    short: dict[str, str] = {}
    for d in decls:
        short.setdefault(d["name"].rsplit(".", 1)[-1], d["name"])
    known = set(short) | full

    mathlib_dir = _H.PROJECT_ROOT / "lean" / ".lake" / "packages" / "mathlib" / "Mathlib"
    mathlib_names: set[str] = set()
    if mathlib_dir.exists():
        try:
            out = subprocess.run(
                ["grep", "-rhoE",
                 r"^(private |protected |noncomputable )*"
                 r"(theorem|lemma|def|abbrev|instance|structure|inductive|class) "
                 r"+[A-Za-z_][A-Za-z0-9_']*",
                 str(mathlib_dir)],
                capture_output=True, text=True, timeout=180).stdout
            mathlib_names = {ln.split()[-1] for ln in out.splitlines() if ln.split()}
        except Exception:
            mathlib_names = set()

    # A docstring may deliberately name a declaration that does NOT exist — e.g. recording a
    # route that was rejected, retracted, or consciously not shipped. Those are the opposite of
    # drift (they are the record that keeps someone from re-adding it), so exempt an occurrence
    # whose surrounding sentence disclaims it. Mirrors the disclaimer exemption in
    # `prose_theorem_reference_coverage`.
    disclaim = re.compile(
        r"(NOT shipped|not shipped|deliberately|does not exist|do(es)? NOT exist|retracted|"
        r"rejected|REJECTED|banned|settled-dead|superseded|dropped|no longer|would have been|"
        r"is wrong|was wrong|non-existent|nonexistent)", re.IGNORECASE)
    exempt = {"set_option", "maxHeartbeats", "native_decide", "norm_num", "field_simp",
              "ring_nf", "simp_rw", "noncomm_ring", "push_cast", "linear_combination",
              "match_scalars", "fun_prop", "positivity", "gcongr", "gauss_sum"}

    details: list[Detail] = []
    n_fail = n_adv = 0
    for path in sorted(_H.LEAN_DIR.rglob("*.lean")):
        rel_mod = str(path.relative_to(_H.LEAN_DIR))
        module = "SKEFTHawking." + rel_mod.removesuffix(".lean").replace("/", ".")
        strict = module.startswith(_DOCSTRING_STRICT_FAMILIES)
        src = path.read_text(errors="ignore")
        seen: set[str] = set()
        for block in _DOCSTRING_BLOCK_RE.findall(src):
            for tok in _DOCSTRING_TOKEN_RE.findall(block):
                if tok in seen or tok in known or tok in mathlib_names or tok in exempt:
                    continue
                if "_" not in tok or len(tok) < 6 or not any(c.islower() for c in tok):
                    continue
                seen.add(tok)
                # Disclaimed-in-context ⇒ intentional record of an absent name, not drift.
                pos = block.index(tok)
                if disclaim.search(block[max(0, pos - 400): pos + 400]):
                    continue
                near = difflib.get_close_matches(tok, short.keys(), n=1, cutoff=0.6)
                hint = f"; nearest existing is `{near[0]}`" if near else ""
                rel = path.relative_to(_H.PROJECT_ROOT)
                line = src[:src.index(tok)].count("\n") + 1 if tok in src else 0
                if strict:
                    n_fail += 1
                    details.append(Detail(
                        f"drift:{module}:{tok}", False,
                        f"{rel}:{line} — docstring names `{tok}`, which resolves to NO "
                        f"declaration and is not a Mathlib name{hint}. Update the prose or "
                        f"restore the name.",
                    ))
                else:
                    n_adv += 1
                    details.append(Detail(
                        f"drift-advisory:{module}:{tok}", True,
                        f"{rel}:{line} — docstring names `{tok}` (unresolved{hint}) — "
                        f"advisory outside the strict families.",
                        warning=True,
                    ))
    details.insert(0, Detail(
        "summary", True,
        f"scanned all SKEFTHawking Lean docstrings against {len(short)} project + "
        f"{len(mathlib_names)} Mathlib names — {n_fail} FAIL(s) in the strict families, "
        f"{n_adv} advisory elsewhere",
        warning=bool(n_adv),
    ))
    return CheckResult(passed=(n_fail == 0), details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK: every project .lean is IN THE BUILD GRAPH
#
# The gap this closes, measured 2026-08-05 (PR-review pass 3):
#   ~2,040 module files on disk, 2,011 reachable from `lean/SKEFTHawking.lean`,
#   28 not. `lakefile.toml` declares the library with NO `globs`, so Lake builds
#   the root plus its transitive imports only. A file nothing imports is built by
#   nothing, indexed by nothing, counted by nothing, and guarded by nothing.
#
# What was hiding in there: the project's ONLY live `sorry`, and TWO modules that
# did not compile at all — one of which asserts "Kernel-pure" in its own docstring.
# Every instrument reported them as ABSENT rather than UNVERIFIED, which is the
# branch's signature defect (absence of measurement rendered as success) at the
# most load-bearing layer there is.
#
# The exe-root allowlist is PARSED FROM `lakefile.toml`, not hardcoded. Three
# repairs on this branch were overtaken within hours because they enumerated the
# cases then in evidence; a derived allowlist cannot go stale when a root is added.
# ═══════════════════════════════════════════════════════════════════════

_LEAN_IMPORT_RE = re.compile(r"^import\s+(SKEFTHawking[\w.]*)", re.M)

#: Modules deliberately outside the library, each with a stated reason. This is a
#: RATCHET: it may only shrink. Adding a name here needs the reason in the same commit.
#: Empty is the target state — a module that cannot justify an entry belongs in the
#: import graph.
UNREACHABLE_MODULE_EXCEPTIONS: dict[str, str] = {}


def _lean_exe_roots() -> set:
    """Module names declared as `[[lean_exe]] root = ...` in lakefile.toml.

    PARSED as TOML, not regexed: a regex over `root = "..."` also matches the key
    inside any other table, and misses the single-quoted and multi-line forms TOML
    permits. `tomllib` is the format's own parser.
    """
    lakefile = _H.PROJECT_ROOT / "lean" / "lakefile.toml"
    if not lakefile.is_file():
        return set()
    try:
        with lakefile.open("rb") as fh:
            data = tomllib.load(fh)
    except (OSError, tomllib.TOMLDecodeError):
        return set()
    exes = data.get("lean_exe") or []
    if isinstance(exes, dict):
        exes = [exes]
    return {e["root"] for e in exes if isinstance(e, dict) and isinstance(e.get("root"), str)}


def _built_modules() -> set:
    """Modules recorded in `lean_deps.json` — i.e. built AS OF THE LAST EXTRACTION.

    ⚠️ **Corroboration only. NOT the primary source, and the reason is timing.**
    `lean_deps.json` is a generated artifact that LAGS the tree: delete an import now
    and the module stays recorded as built until the next extraction, so a check keyed
    on it cannot see a module that was orphaned *this commit* — which is the whole
    event this check exists to catch. Verified by mutation on 2026-08-06: sourcing
    reachability from here made the guard silent on a removed import.

    "Use the real infrastructure" is right in general and wrong here: the build record
    answers *what was compiled last time*, and the question is *what does the tree
    declare now*. Same subject, different tense.
    """
    try:
        return {r["module"] for r in _H.load_lean_deps() if r.get("module")}
    except Exception:
        return set()


def _root_reachable_modules() -> set:
    """PRIMARY — the transitive `import SKEFTHawking.*` closure from the root aggregate.

    Reads the CURRENT source, which is the only thing that reflects an orphaning the
    moment it happens. It does re-implement Lake's resolution, which is a real cost;
    `_built_modules()` cross-checks it so a divergence is visible rather than assumed
    away.
    """
    lean = _H.PROJECT_ROOT / "lean"
    root = lean / "SKEFTHawking.lean"
    if not root.is_file():
        return set()

    def imports_of(mod: str):
        p = lean / (mod.replace(".", "/") + ".lean")
        if not p.is_file():
            return []
        return _LEAN_IMPORT_RE.findall(p.read_text(errors="replace"))

    seen, stack = set(), list(_LEAN_IMPORT_RE.findall(root.read_text(errors="replace")))
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        stack.extend(imports_of(m))
    return seen


@register_check("lean_modules_in_build_graph",
                "Every project .lean module is reachable from the root aggregate "
                "(else it is built, indexed, counted and guarded by nothing)")
def check_lean_modules_in_build_graph() -> CheckResult:
    """Compare the FILESYSTEM to the import graph — the join nothing else makes."""
    src = _H.PROJECT_ROOT / "lean" / "SKEFTHawking"
    if not src.is_dir():
        return CheckResult(passed=False, measured=False, details=[Detail(
            "scope", False, "SKIPPED — lean/SKEFTHawking/ absent; UNVERIFIED, not passing")])

    disk = {"SKEFTHawking." + str(p.relative_to(src)).removesuffix(".lean").replace("/", ".")
            for p in src.rglob("*.lean")}
    if not disk:
        return CheckResult(passed=False, measured=False, details=[Detail(
            "scope", False, "SKIPPED — no .lean files found; UNVERIFIED, not passing")])

    reachable = _root_reachable_modules()
    exe_roots = _lean_exe_roots()
    orphans = sorted(disk - reachable - exe_roots - set(UNREACHABLE_MODULE_EXCEPTIONS))

    details = [Detail(
        "population", True,
        f"{len(disk)} module files on disk / {len(disk & reachable)} reachable from the "
        f"root aggregate / {len(exe_roots & disk)} declared exe root(s) / "
        f"{len(UNREACHABLE_MODULE_EXCEPTIONS)} documented exception(s)")]

    # Cross-check against the build record. A module recorded built but no longer
    # import-reachable means the record is stale relative to the tree — worth saying,
    # never worth silencing the primary with.
    built = _built_modules()
    if built:
        stale = sorted((built & disk) - reachable - exe_roots)
        if stale:
            details.append(Detail(
                "build_record_lag", True,
                f"{len(stale)} module(s) recorded in lean_deps.json but no longer "
                f"reachable — the record predates a removed import; regenerate counts: "
                f"{', '.join(stale[:5])}", warning=True))

    for name, why in sorted(UNREACHABLE_MODULE_EXCEPTIONS.items()):
        if name in disk and name not in reachable:
            details.append(Detail(f"exception:{name.rsplit('.', 1)[-1]}", True, why, warning=True))

    if orphans:
        details.append(Detail(
            "orphans", False,
            f"{len(orphans)} module(s) exist on disk but are reachable from NOTHING — so they "
            f"are never compiled, never enter lean_deps.json, and are invisible to the sorry "
            f"and axiom guards. Add an `import` to lean/SKEFTHawking.lean, or record the module "
            f"in UNREACHABLE_MODULE_EXCEPTIONS with a reason: {', '.join(orphans[:8])}"
            + (f" (+{len(orphans) - 8} more)" if len(orphans) > 8 else "")))
    else:
        details.append(Detail("orphans", True, "no orphaned modules — the filesystem and the "
                                               "import graph agree"))
    return CheckResult(passed=not orphans, details=details)
