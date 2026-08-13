"""Generated-artifact freshness checks — ADR-009 Phase 2.

The checks that REGENERATE artifacts other checks read (`counts_fresh`,
`tables_fresh`, `claim_clusters_fresh`), plus the freshness comparisons that do
not regenerate (`bundle_source_freshness`, `inventory_index_autogen_fresh`,
`notebook_stored_outputs_current`).

⚠️ **THIS MODULE IS WHY EXECUTION ORDER IS DATA.** `counts_fresh` shells out to
`update_counts.py`, which can rewrite `docs/counts.json` *and* `lean/lean_deps.json`
mid-run; `tables_fresh` rewrites `papers/*/tables/*.tex`; `claim_clusters_fresh`
rewrites `papers/claim_clusters.json`. Later checks read all three. Their position
relative to their consumers is SEMANTIC, and it is declared in
`validate._CANONICAL_ORDER` — never inferred from where this module sits in an
import list (ADR-009 H3). Moving a check out of this module does not change when it
runs; changing `_CANONICAL_ORDER` does.

Three of these are QUARANTINED from the characterization harness for exactly that
reason: they mutate the tree, so run N+1 legitimately differs from run N.

MOVED VERBATIM from `scripts/validate.py`, extracted by script from AST-verified
ranges. The only edits are the import rewrites: paths are reached as `_H.<NAME>` at
each use rather than through module-level aliases (a local alias is an import-time
copy that defeats any test monkeypatching the owner — see `checks/physics.py`), and
`COUNTS_JSON_PATH` / `COUNTS_TEX_PATH` now come from `validate_helpers`, which
already owned them, instead of being re-derived here.

`_counts_is_stale` and `_tables_is_stale` are in the frozen external surface and
are consumed by **`scripts/sync_manifest.py` — a production script, not a test** —
so `validate` re-exports them (ADR-009 D2 item 8).

`bundle_source_freshness` reads `_cfg.STRICT_MODE` by ATTRIBUTE; importing the flag
by value would freeze it at import time and silently make `--strict` a no-op (H5).
"""
from __future__ import annotations

import json
import re
import subprocess
from pathlib import Path
from typing import Dict, List

import validate_helpers as _H
from validation import _config as _cfg
from validation._registry import CheckResult, Detail, register_check


# ═══════════════════════════════════════════════════════════════════════
# CHECK 15b: Counts freshness (Phase 5v Wave 1b)
# ═══════════════════════════════════════════════════════════════════════

_COUNTS_SOURCES = [
    _H.LEAN_DEPS_PATH,
    _H.SRC_DIR / "core" / "constants.py",
    _H.SRC_DIR / "core" / "visualizations.py",
]


#: Which artifacts each regenerator owns. Used ONLY by `_verify_regeneration`'s
#: mtime-ordering repair — never to decide staleness.
_GENERATOR_ARTIFACTS = {
    "update_counts.py": ("docs/counts.json", "docs/counts.tex"),
    "render_paper_tables.py": (),      # many; ordering repair not applicable
    "cluster_detect.py": ("papers/claim_clusters.json",),
}


def _artifacts_of(generator: str):
    """Paths a generator writes, anchored through `_H` at each use (H1)."""
    return [_H.PROJECT_ROOT / rel for rel in _GENERATOR_ARTIFACTS.get(generator, ())]


def _verify_regeneration(is_stale, generator: str, details: list) -> bool:
    """RE-TEST staleness after a regenerator claimed success. Returns False if the
    artifact is still stale, appending the failing Detail.

    ⚠️ ADDED 2026-08-05 (PR-review R4-I7). All three regenerators measured staleness
    ONCE — before shelling out — and then never asked again. Their only `passed=False`
    paths were subprocess failures (non-zero rc, `FileNotFoundError`, timeout). So the
    one outcome they could not report is the one worth reporting: **a generator that
    exits 0 having written nothing, or having written something still stale.**

    Live proof from the review's own run, unchanged at HEAD before this fix:

        counts_fresh  detail 1: "stale: constants.py newer than counts.json"
                      detail 2: "update_counts.py succeeded"
                      verdict : PASS

    These were self-healing scripts wearing the interface of gates. Re-testing costs
    one mtime comparison and changes nothing on the happy path — a generator that did
    its job leaves the artifact fresh.

    Deliberately ONE helper for all three: the same defect in three copies is what
    this audit keeps finding, and a fourth regenerator should inherit the fix rather
    than re-earn it.
    """
    still_stale, why = is_stale()

    # ⚠️ WEDGE REPAIR 2026-08-05 (PR-review R4-MAJ7). The re-test above is
    # MTIME-based, and the generators skip byte-identical writes — so an artifact
    # that is CORRECT but merely older than its source could never satisfy it, and
    # this leg pinned the check permanently red. Measured live on 2026-08-05:
    # `counts.json` content byte-identical after regeneration, `constants.py` mtime
    # 1785947998.849 > `counts.json` 1785947429.469 → "STILL STALE" forever. No
    # content change could heal it; a `git checkout`, a merge, or a test that writes
    # and restores a source file all trigger it. (The trigger that day was
    # `tests/test_validation_memo.py` restoring content but not mtimes.)
    #
    # So: if the generator exited 0 and staleness persists, TOUCH the artifact and
    # re-test ONCE. The generators are deterministic and idempotent, so "exited 0
    # and declined to rewrite" means the content is already what it would have
    # written — mtime ordering is then a checkout artifact, not evidence.
    #
    # ⚠️ RESIDUAL RISK, stated rather than hidden: this cannot distinguish a
    # generator that correctly wrote nothing from one that is broken and writes
    # nothing when it should. The R4-I7 guarantee survives only for the case where
    # staleness OUTLIVES a touch. Closing that properly needs a content-derived
    # staleness predicate (as `inventory_index_autogen_fresh` already uses); filed,
    # not done here.
    if still_stale:
        touched = False
        for art in _artifacts_of(generator):
            if art.exists():
                art.touch()
                touched = True
        if touched:
            still_stale, why = is_stale()
            if not still_stale:
                details.append(Detail(
                    "post_regenerate", True,
                    f"{generator} exited 0 and declined to rewrite (content already "
                    f"current); artifact mtime restored. Ordering was a checkout "
                    f"artifact, not staleness.", warning=True))
                return True

    if still_stale:
        details.append(Detail(
            "post_regenerate", False,
            f"{generator} exited 0 but the artifact is STILL STALE ({why}). A "
            f"generator reporting success while writing nothing usable is the failure "
            f"this leg exists for — the pre-regeneration staleness measurement cannot "
            f"see it."))
        return False
    details.append(Detail("post_regenerate", True,
                          f"{generator} output verified fresh"))
    return True


def _counts_is_stale() -> tuple[bool, str]:
    """Return (stale, reason). Stale if counts.json is missing or older
    than any of _COUNTS_SOURCES, or if counts.tex is missing."""
    if not _H.COUNTS_JSON_PATH.exists():
        return True, "counts.json missing"
    if not _H.COUNTS_TEX_PATH.exists():
        return True, "counts.tex missing"
    counts_mtime = _H.COUNTS_JSON_PATH.stat().st_mtime
    for src in _COUNTS_SOURCES:
        if src.exists() and src.stat().st_mtime > counts_mtime:
            return True, f"{src.name} newer than counts.json"
    # Also regenerate if any .lean file in SKEFTHawking is newer (catches
    # cases where lean_deps.json isn't regenerated but sources changed).
    # rglob (recursive) — a *.lean in a subdirectory (FKLW/, SymTFT/,
    # QuantumNetwork/, …) must also mark counts stale, else a native_decide
    # added in a subdir kept the decl-closure metric stale (ADR-004 W7
    # adversarial finding M2, 2026-06-13).
    lean_src = _H.LEAN_DIR.rglob("*.lean")
    newest_lean = max((f.stat().st_mtime for f in lean_src), default=0)
    if newest_lean > counts_mtime:
        return True, "SKEFTHawking/**/*.lean newer than counts.json"

    # ⚠️ THE OTHER COUNT-BEARING TREES. `counts.json` publishes `pytest_cases`,
    # `test_files`, `notebooks` and `papers`, and NONE of those directories was a
    # staleness input — only lean_deps, constants.py and visualizations.py were. So
    # `\totaltests`, `\testfiles`, `\notebookcount` and `\papercount` could drift
    # silently while this check reported `fresh`. Measured 2026-08-10: two commits
    # added 8 tests after the last regeneration and `counts.json` still said 6,163
    # against a live 6,171, with the check green — a violation of the repo's
    # "update before you ship, in the same commit" rule BY the mechanism meant to
    # enforce it.
    #
    # Same rglob-newest shape as the Lean leg above, deliberately: one staleness
    # mechanism, applied to every tree whose contents this artifact publishes.
    for label, root, pat in (
            ("src/**/*.py", _H.SRC_DIR, "*.py"),      # publishes python_modules
            ("tests/**/*.py", _H.TESTS_DIR, "*.py"),
            ("notebooks/**/*.ipynb", _H.NOTEBOOKS_DIR, "*.ipynb"),
            ("papers/**/paper_draft.tex", _H.PAPERS_DIR, "paper_draft.tex")):
        if not root.exists():
            continue
        newest = max((f.stat().st_mtime for f in root.rglob(pat)), default=0)
        if newest > counts_mtime:
            return True, f"{label} newer than counts.json"
    return False, "fresh"


@register_check("counts_fresh",
                "counts.json / counts.tex are up-to-date vs. sources")
def check_counts_fresh() -> CheckResult:
    """CHECK 15b: Regenerate counts.json + counts.tex if stale.

    Papers reference counts via \\input{counts.tex} macros; this check
    ensures the macro values reflect the current codebase. Regeneration
    is automatic when sources are newer; check passes as long as both
    artifacts exist after the regeneration attempt.
    """
    stale, reason = _counts_is_stale()
    details = []

    if stale:
        details.append(Detail("staleness", True, f"stale: {reason}",
                              warning=True))
        # Run update_counts.py
        try:
            # Timeout 1800s = 30 min (Phase 7a sub-wave 7a.0.4 bump from 600s).
            # update_counts.py invokes ExtractDeps.lean which walks ~5000+ decls
            # and runs collectAxioms on each — exceeds 600s on current project size.
            result = subprocess.run(
                ["uv", "run", "python",
                 str(_H.SCRIPT_DIR / "update_counts.py")],
                cwd=str(_H.PROJECT_ROOT),
                capture_output=True, text=True, timeout=1800,
            )
            if result.returncode != 0:
                details.append(Detail(
                    "regenerate", False,
                    f"update_counts.py failed (rc={result.returncode}): "
                    f"{result.stderr[-200:].strip()}",
                ))
                return CheckResult(passed=False, details=details)
            details.append(Detail("regenerate", True,
                                  "update_counts.py succeeded"))
            if not _verify_regeneration(_counts_is_stale, "update_counts.py", details):
                return CheckResult(passed=False, details=details)
        except (FileNotFoundError, subprocess.TimeoutExpired) as exc:
            details.append(Detail("regenerate", False,
                                  f"update_counts.py not runnable: {exc}"))
            return CheckResult(passed=False, details=details)
    else:
        details.append(Detail("staleness", True, "fresh"))

    # Both artifacts must now exist
    passed = _H.COUNTS_JSON_PATH.exists() and _H.COUNTS_TEX_PATH.exists()
    if passed:
        # Summary of current counts
        try:
            counts = json.loads(_H.COUNTS_JSON_PATH.read_text())
            lean = counts.get("lean", {})
            python = counts.get("python", {})
            aristotle = counts.get("aristotle", {})
            summary = (
                f"theorems={lean.get('theorems_total','?')} "
                f"(substantive={lean.get('theorems_substantive','?')}, "
                f"placeholder={lean.get('theorems_placeholder','?')}) | "
                f"modules={lean.get('modules','?')} | "
                f"sorry={lean.get('sorry_declarations','?')} | "
                f"papers={python.get('papers','?')} | "
                f"aristotle_proved={aristotle.get('aristotle_proved','?')}"
            )
            details.append(Detail("summary", True, summary))
        except (json.JSONDecodeError, OSError) as exc:
            details.append(Detail("summary", False,
                                  f"counts.json unreadable: {exc}"))
            passed = False

    return CheckResult(passed=passed, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 15c: Paper tables freshness (Phase 5v)
# ═══════════════════════════════════════════════════════════════════════

_TABLES_SOURCES = [
    _H.SRC_DIR / "core" / "formulas.py",
    _H.SRC_DIR / "core" / "constants.py",
    _H.SRC_DIR / "core" / "transonic_background.py",
    _H.SRC_DIR / "core" / "provenance.py",
    _H.LEAN_DEPS_PATH,
    _H.PROJECT_ROOT / "docs" / "WAVE_EXECUTION_PIPELINE.md",
    _H.PROJECT_ROOT / "scripts" / "paper_tables" / "__init__.py",
    _H.PROJECT_ROOT / "scripts" / "paper_tables" / "sources.py",
    _H.PROJECT_ROOT / "scripts" / "render_paper_tables.py",
]


def _tables_specs() -> list[Path]:
    """Every papers/<key>/tables.py that exists."""
    if not _H.PAPERS_DIR.exists():
        return []
    return list(_H.PAPERS_DIR.glob("paper*_*/tables.py"))


def _tables_outputs() -> list[Path]:
    """Every papers/<key>/tables/*.tex that has been generated."""
    if not _H.PAPERS_DIR.exists():
        return []
    return list(_H.PAPERS_DIR.glob("paper*_*/tables/*.tex"))


def _tables_is_stale() -> tuple[bool, str]:
    """Stale if any source / spec mtime is newer than the newest output,
    or if a spec exists but has no output file."""
    specs = _tables_specs()
    outputs = _tables_outputs()
    if not specs:
        return False, "no tables.py specs"
    if not outputs:
        return True, f"{len(specs)} spec(s) but no output .tex files"
    output_mtime = min(p.stat().st_mtime for p in outputs)
    for src in _TABLES_SOURCES + specs:
        if src.exists() and src.stat().st_mtime > output_mtime:
            return True, f"{src.name} newer than oldest output"
    return False, f"fresh ({len(outputs)} output files across {len(specs)} papers)"


@register_check("tables_fresh",
                "Paper tables (tables/*.tex) are up-to-date vs. pipeline sources")
def check_tables_fresh() -> CheckResult:
    """CHECK 15c: Regenerate papers/*/tables/*.tex if stale.

    Papers `\\input{}` their numerical tables from this autogenerated
    directory; this check keeps the cells fresh when any pipeline source
    changes (formulas, constants, transonic background, the paper's
    spec). Mirror of CHECK 15b counts_fresh for numerical tables.
    """
    stale, reason = _tables_is_stale()
    details = []
    if stale:
        details.append(Detail("staleness", True, f"stale: {reason}", warning=True))
        try:
            result = subprocess.run(
                ["uv", "run", "python",
                 str(_H.SCRIPT_DIR / "render_paper_tables.py")],
                cwd=str(_H.PROJECT_ROOT),
                capture_output=True, text=True, timeout=300,
            )
            if result.returncode != 0:
                details.append(Detail(
                    "regenerate", False,
                    f"render_paper_tables.py failed (rc={result.returncode}): "
                    f"{result.stderr[-200:].strip()}",
                ))
                return CheckResult(passed=False, details=details)
            tables_written = result.stdout.strip().splitlines()[-1] if result.stdout.strip() else '0 tables'
            details.append(Detail("regenerate", True,
                                  f"render_paper_tables.py succeeded: {tables_written}"))
            if not _verify_regeneration(_tables_is_stale, "render_paper_tables.py", details):
                return CheckResult(passed=False, details=details)
        except (FileNotFoundError, subprocess.TimeoutExpired) as exc:
            details.append(Detail("regenerate", False,
                                  f"render_paper_tables.py not runnable: {exc}"))
            return CheckResult(passed=False, details=details)
    else:
        details.append(Detail("staleness", True, reason))
    return CheckResult(passed=True, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 15d: Cross-paper ClaimCluster freshness (Phase 5v Wave 10f)
# ═══════════════════════════════════════════════════════════════════════

def claim_clusters_path():
    # ⚠️ H1: resolved AT EACH USE, not bound at import. A module-level
    # `X = _H.ANCHOR / "..."` is an import-time COPY: a test monkeypatching the
    # anchor does not reach it, so the check silently reads the PRODUCTION tree
    # while the test believes it is reading a fixture. Converted 2026-08-05
    # (PR-review pass 2, R3-I5 / R1).
    return _H.PAPERS_DIR / "claim_clusters.json"


def _claim_clusters_is_stale() -> tuple[bool, str]:
    """Stale if any v2 ``claims_review.json`` mtime is newer than
    ``claim_clusters.json``, or if any v2 file exists but no cluster
    file does.

    A v2 ``claims_review.json`` carries a top-level ``sentences`` list;
    files without that key are v1 and don't participate in cross-paper
    clustering.
    """
    if not _H.PAPERS_DIR.exists():
        return False, "no papers/ dir"
    # ⚠️ REUSE THE GENERATOR'S OWN POPULATION — never re-implement the predicate here.
    # A freshness guard that computes its own population can share a blind spot with the
    # generator it watches, and then reports "fresh" over the very files both are missing.
    # Importing the iterator keeps the population definable in exactly one place.
    from cluster_detect import iter_v2_paper_dirs
    v2_files: list[Path] = [
        d / 'claims_review.json'
        for _pid, d in iter_v2_paper_dirs(_H.PAPERS_DIR)   # H1: anchor at each use
    ]
    if not v2_files:
        return False, "no v2 claims_review.json files"
    if not claim_clusters_path().exists():
        return True, f"{len(v2_files)} v2 paper(s), no claim_clusters.json"
    cluster_mtime = claim_clusters_path().stat().st_mtime
    for f in v2_files:
        if f.stat().st_mtime > cluster_mtime:
            return True, f"{f.parent.name}/claims_review.json newer than claim_clusters.json"
    return False, f"fresh ({len(v2_files)} v2 paper(s) tracked)"


@register_check("claim_clusters_fresh",
                "papers/claim_clusters.json is up-to-date vs. v2 claims_review.json files")
def check_claim_clusters_fresh() -> CheckResult:
    """CHECK 15d: Regenerate ``papers/claim_clusters.json`` if any v2
    ``claims_review.json`` is newer.

    Wave 10f. The cross-paper ClaimCluster + MEMBER_OF graph extractors
    consume this file; out-of-date data means the dashboard misses
    propagation prompts and ``graph_integrity.claim_cluster_inconsistency``
    runs against stale member sets. Auto-regenerates via ``cluster_detect.py``.
    Idempotent + safe on machines with zero v2 papers.
    """
    stale, reason = _claim_clusters_is_stale()
    details = []
    if stale:
        details.append(Detail("staleness", True, f"stale: {reason}", warning=True))
        try:
            result = subprocess.run(
                ["uv", "run", "python",
                 str(_H.SCRIPT_DIR / "cluster_detect.py")],
                cwd=str(_H.PROJECT_ROOT),
                capture_output=True, text=True, timeout=120,
            )
            if result.returncode != 0:
                details.append(Detail(
                    "regenerate", False,
                    f"cluster_detect.py failed (rc={result.returncode}): "
                    f"{result.stderr[-200:].strip()}",
                ))
                return CheckResult(passed=False, details=details)
            # cluster_detect prints summary on stderr (one-line)
            tail = (result.stderr or '').strip().splitlines()
            details.append(Detail("regenerate", True,
                                  tail[-1] if tail else "cluster_detect.py succeeded"))
            if not _verify_regeneration(_claim_clusters_is_stale,
                                        "cluster_detect.py", details):
                return CheckResult(passed=False, details=details)
        except (FileNotFoundError, subprocess.TimeoutExpired) as exc:
            details.append(Detail("regenerate", False,
                                  f"cluster_detect.py not runnable: {exc}"))
            return CheckResult(passed=False, details=details)
    else:
        details.append(Detail("staleness", True, reason))

    # Summarize current cluster state when present
    if claim_clusters_path().exists():
        try:
            data = json.loads(claim_clusters_path().read_text())
            n_clusters = data.get('cluster_count', 0)
            n_papers = len(data.get('paper_coverage') or [])
            details.append(Detail(
                "summary", True,
                f"{n_clusters} cluster(s) across {n_papers} paper(s)",
            ))
        except (json.JSONDecodeError, OSError) as exc:
            details.append(Detail("summary", False,
                                  f"claim_clusters.json unreadable: {exc}"))
            return CheckResult(passed=False, details=details)
    return CheckResult(passed=True, details=details)


@register_check("notebook_stored_outputs_current",
                "Bundle companion notebooks' STORED outputs equal what their code produces")
def check_notebook_stored_outputs_current() -> CheckResult:
    """CHECK: stored notebook output must be what the notebook actually produces.

    Added 2026-07-31 (D11 Stage-13 round-7 BLOCKER 5.1). `notebook_exec` executes
    each notebook with `NotebookClient` into an in-memory `nb` and **never writes it
    back** (`scripts/validate.py`, no `nbformat.write` in that path). So it proves a
    notebook *runs*; it has no opinion about what is stored in it. Stored outputs can
    therefore drift arbitrarily from what the code produces, and the check stays green
    the whole time.

    That is exactly what happened: D11's companion notebook shipped as a bundle
    artifact with stored figure output rendering `Voigt-Reuss elastic bounds` and
    `effective modulus M` — the two namings the paper's Section 5 and the Lean module
    header explicitly retract — plus a 3.3177 annotation missing the
    `(numerical, not certified)` qualifier the paper claims the figure carries. A
    reader opening the shipped notebook saw the retracted claims.

    NOTE on the diagnosed cause: the round-7 reviewer attributed this to the skip-cache
    key being "the notebook's own state, not visualizations.py". That is not the
    mechanism — `_src_core_fingerprint()` hashes all of `src/core/*.py`, visualizations
    included, and does invalidate the cache. The real cause is narrower and worse: the
    check never compares or refreshes stored output at all, so no cache key could have
    saved it.

    Scoped to the bundle companion notebooks (the ones that ship as artifacts) because
    executing all ~91 costs ~10 minutes; the rest stay covered by `notebook_exec`'s
    runs-clean guarantee. The scope limit is stated in the summary line rather than
    left implicit.
    """
    try:
        import nbformat
        from nbclient import NotebookClient
    except ImportError as exc:
        # ⚠️ `measured=False`. This branch executes NO notebook, and it defaulted to
        # reporting a measurement — so with nbclient absent it counted toward the
        # `--ci` zero-headroom coverage floor as evidence, and `_memo` could cache
        # it. `notebooks.py:317` handles the IDENTICAL nbclient ImportError with
        # `measured=False`; this was the site that did not.
        #
        # ⚠️ An earlier version of this comment also cited "the sibling at :783 in
        # this same file". That line is a DOCSTRING, and the nearby return guards a
        # different import in a different check. Naming a line without opening it is
        # how this branch produced most of its wrong claims — including this one.
        return CheckResult(passed=True, measured=False, details=[
            Detail("import", True, f"nbclient/nbformat unavailable ({exc}); skipping",
                   warning=True, measured=False)])

    targets = sorted(_H.NOTEBOOKS_DIR.glob("D1[12]_*.ipynb"))
    if not targets:
        # FAIL, not pass (D11 round-12). The glob is the whole scope, so renaming a
        # notebook out of the pattern silently emptied it and the check reported success
        # having examined nothing — the same fail-open shape as the readiness guards.
        return CheckResult(passed=False, details=[
            Detail("scope", False,
                   "NO bundle companion notebook matches D1[12]_*.ipynb. The bundles ship "
                   "executed notebooks, so an empty scope means the glob no longer finds "
                   "them — unverified, not passing.")])

    # Arrays longer than this are summarised by a rounded-value digest rather than
    # compared element-by-element. Applies identically to base64 numpy arrays and lists.
    _BULK_ARRAY_MIN = 8
    # Significant figures kept in the digest. 1e-15 relative jitter (library/BLAS
    # version noise) rounds away; a curve computed from a different formula does not.
    _DIGEST_SIGFIGS = 9

    def _decode_bdata(obj) -> list:
        """Decode a Plotly `{"dtype": ..., "bdata": <base64>}` array to a Python list."""
        import base64 as _b64, struct as _st
        fmt = {"f8": "<d", "f4": "<f", "i8": "<q", "i4": "<i", "i2": "<h", "i1": "<b",
               "u8": "<Q", "u4": "<I", "u2": "<H", "u1": "<B"}.get(str(obj.get("dtype")))
        if fmt is None:
            return []
        try:
            raw = _b64.b64decode(obj["bdata"])
        except Exception:
            return []
        w = _st.calcsize(fmt)
        return [_st.unpack_from(fmt, raw, i * w)[0] for i in range(len(raw) // w)]

    def _array_digest(values: list) -> str:
        """Length + a digest of the VALUES rounded to `_DIGEST_SIGFIGS`.

        ⚠️ This replaced a length-only summary on 2026-07-31 (D11 Stage-13 round-9
        finding 5.1). Length-only meant the *values* of any array longer than
        `_BULK_ARRAY_MIN` were invisible: the round-9 reviewer demonstrated end-to-end
        that the shipped notebook could plot `ε = 1 + 3f` instead of Maxwell–Garnett,
        under an annotation reading "(certified)", and this check still reported
        "stored output matches a fresh run". A structural exclusion cannot distinguish
        a claim from noise; a rounded digest can, which is what the reviewer proposed.
        """
        import hashlib as _h
        h = _h.sha256()
        n = 0
        for v in values:
            if not isinstance(v, (int, float)) or v != v or v in (float("inf"), float("-inf")):
                h.update(repr(v).encode())
            else:
                h.update(f"{float(v):.{_DIGEST_SIGFIGS}g}".encode())
            h.update(b"\x00")
            n += 1
        return f"len={n},sha={h.hexdigest()[:16]}"

    def _strings_in(obj, _path: str = "") -> list[str]:
        """Every claim-bearing leaf of a JSON payload, in document order.

        String leaves are the reader-visible text surface — subplot titles, axis titles,
        legend names, annotation text. Numeric leaves matter too, but only in the places
        where a number IS a claim.

        ⚠️ The numeric half was added 2026-07-31 after a round-8 reviewer defeated the
        string-only version: moving the *certified* Maxwell–Garnett marker from
        `f = 1/2` to `f = 0.55`, while its label still read
        `f = 1/2 ⟹ ε_eff = 2 (certified)`, left this check green. Scalar coordinates
        serialize as JSON numbers, not string leaves, so a text-only comparison cannot
        see a certified point that has silently moved off the value it certifies.

        Bulk trace arrays are deliberately EXCLUDED: `x`/`y`/`z` lists are hundreds of
        floats whose low-order digits move with library versions, and comparing them
        would make the check fire on non-claims. Scalar positions do not have that
        problem — an annotation anchor, a vline abscissa, a single-point marker — and
        those are exactly where a figure asserts "this value is certified".
        """
        out: list[str] = []
        if isinstance(obj, str):
            out.append(obj)
        elif isinstance(obj, bool):
            out.append(f"{_path}={obj}")
        elif isinstance(obj, (int, float)):
            out.append(f"{_path}={obj!r}")
        elif isinstance(obj, dict):
            # Plotly serializes a numpy array as {"dtype": "f8", "bdata": "<base64>"}.
            # `bdata` is a STRING, so without this branch it took the string arm above and
            # was compared byte-for-byte — the exact opposite of the bulk-array rule below,
            # which only ever saw arrays that happened to be Python lists at the call site.
            # Measured 2026-07-31 (D11 round-8 finding 5.1): D11 has 24 base64 arrays and 0
            # plain lists reaching the rule; D12 has 32 and 2. So the discriminator was
            # "numpy or list at the call site", not "claim or not", and 56 bulk curves were
            # being compared to the last bit — a 1e-15 jitter would have failed the check.
            # Both encodings now route through the SAME length-only rule.
            if isinstance(obj.get("bdata"), str) and "dtype" in obj:
                out.append(f"{_path}[bdata:{obj['dtype']}]="
                           + _array_digest(_decode_bdata(obj)))
                return out
            for k in sorted(obj):
                out.extend(_strings_in(obj[k], f"{_path}.{k}" if _path else str(k)))
        elif isinstance(obj, list):
            # A long all-numeric list is plotted data, not a claim: keep only its length,
            # so a trace losing points still shows up while float jitter does not.
            nums = sum(1 for v in obj if isinstance(v, (int, float)))
            if nums > _BULK_ARRAY_MIN and nums == len(obj):
                out.append(f"{_path}[nums]=" + _array_digest(list(obj)))
                return out
            for i, v in enumerate(obj):
                out.extend(_strings_in(v, f"{_path}[{i}]"))
        return out

    def _texts(nb) -> list[str]:
        """Every text-bearing output payload, in order.

        ⚠️ Figure output is the point (D11 round-7 BLOCKER 5.1 was a stale *figure*,
        not stale stdout). In this repo figures serialize as
        `application/vnd.plotly.v1+json`, so an implementation that collected only
        `text/plain` / `text/html` / `application/json` — as the first version of this
        function did — would ignore all four D11 figures and pass green on precisely the
        defect it exists to catch. Any `*json*` MIME key is descended into for its string
        leaves. Raster image payloads are still ignored: bit-level PNG churn is not a
        claim.
        """
        out = []
        for cell in nb.cells:
            if cell.cell_type != "code":
                continue
            for o in cell.get("outputs", []) or []:
                if "text" in o:
                    out.append("".join(o["text"]))
                d = (o.get("data") or {})
                for key in sorted(d):
                    # `text/markdown` added 2026-07-31 (D11 round-10 5.1). The digest
                    # closed the numeric hole, but the MIME allow-list one level up was
                    # still narrow: the reviewer injected a `text/markdown` output
                    # asserting C = +1 beside the name of the theorem certifying C = −1,
                    # and this check reported "stored output matches a fresh run". Any
                    # rendered text a reader sees is a claim surface.
                    # `image/svg+xml` added 2026-07-31 (D11 round-12). SVG was in neither
                    # the allow-list nor the `json` branch, so the reviewer appended an SVG
                    # cell, executed it, then edited ONLY the stored SVG to read "C = +1"
                    # and "3.3177 (certified)" — the exact two claims this guard exists to
                    # protect — and it reported "stored output matches a fresh run". SVG is
                    # the realistic attack because GitHub does not render Plotly JSON, so a
                    # static renderer is what an author reaches for.
                    if key in ("text/plain", "text/html", "text/markdown",
                               "text/latex", "application/x-latex", "image/svg+xml"):
                        v = d[key]
                        out.append(v if isinstance(v, str) else "".join(v))
                    elif "json" in key:
                        out.extend(_strings_in(d[key]))
        return out

    details: list[Detail] = []
    all_pass = True
    for nb_path in targets:
        try:
            stored = nbformat.read(nb_path.open(), as_version=4)
            fresh = nbformat.read(nb_path.open(), as_version=4)
            NotebookClient(fresh, timeout=180, kernel_name="python3",
                           resources={"metadata": {"path": str(_H.NOTEBOOKS_DIR)}}).execute()
        except Exception as exc:
            all_pass = False
            details.append(Detail(nb_path.name, False,
                                  f"could not re-execute for comparison: "
                                  f"{type(exc).__name__}: {exc}"))
            continue

        a, b = _texts(stored), _texts(fresh)
        if a == b:
            details.append(Detail(nb_path.name, True,
                                  f"stored output matches a fresh run "
                                  f"({len(a)} text payloads)"))
            continue
        all_pass = False
        diff = next((f"stored={x[:160]!r} fresh={y[:160]!r}"
                     for x, y in zip(a, b) if x != y),
                    f"payload count differs: stored={len(a)} fresh={len(b)}")
        details.append(Detail(
            nb_path.name, False,
            f"STORED OUTPUT IS STALE — a fresh run produces different text. "
            f"This notebook ships as a bundle artifact, so the stored output is what a "
            f"reader sees. Re-execute in place: "
            f"`uv run jupyter nbconvert --to notebook --execute --inplace "
            f"notebooks/{nb_path.name}`. First divergence: {diff}"))

    details.insert(0, Detail(
        "summary", all_pass,
        f"{len(targets)} bundle companion notebook(s) compared against a fresh run; "
        f"non-bundle notebooks are NOT covered here (cost) and rely on notebook_exec"))
    return CheckResult(passed=all_pass, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 22: bundle source freshness (Phase 7a sub-wave 7a.1.4)
# ═══════════════════════════════════════════════════════════════════════

@register_check(
    "bundle_source_freshness",
    "Bundle source-paper mtime ≤ bundle last_lift; flag stale bundles",
)
def check_bundle_source_freshness() -> CheckResult:
    """For each bundle (per `papers/<bundle>/bundle_metadata.json`),
    detect whether any of its source papers (per
    `docs/PAPER_DRAFT_MAPPING.md`) has been modified since the bundle's
    last lift. Stale bundles need Stage-13 re-invocation per
    `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md`.

    Default mode: advisory (every detail.warning=True passes the check).
    Strict mode (`validate.py --strict`): freshness-stale bundles fail.

    Phase 7a sub-wave 7a.1.4 deliverable. Schema reference:
    `docs/BUNDLE_DIRECTORY_SCHEMA.md`.
    """
    try:
        from check_bundle_source_freshness import check as _run_check
    except ImportError as exc:
        # An unimportable module is the strongest possible non-measurement.
        return CheckResult(
            passed=False,
            measured=False,
            error=f"check_bundle_source_freshness module unavailable: {exc}",
        )

    findings = _run_check()
    if not findings:
        # ⚠️ ZERO bundles measured, and this reported a MEASUREMENT for five rounds.
        # It is the ADR-009 H1 anchor-retarget scenario applied to the whole bundle
        # corpus: move `papers/` and CHECK 22 returns green over nothing.
        #
        # Both guards were blind to it, which is why five rounds missed it. The AST
        # scanner only sees `except` handlers and `if`s whose test calls a presence
        # function — the test here is `not findings`. The keyword scanner does not
        # match "no bundle directories initialized yet". Neither instrument could
        # see the site, so nothing contradicted `_registry.py`'s citing THIS check
        # as the example of a population-unreachable non-measurement.
        return CheckResult(
            passed=True,
            measured=False,
            details=[Detail(
                "scope",
                True,
                "no bundle directories initialized yet (pre-Phase-7-execution state)",
                measured=False,
            )],
        )

    details: List[Detail] = []
    n_warn = 0
    n_fail = 0
    for f in findings:
        bundle = f["bundle"]
        msg = f["message"]
        passed = f["passed"]
        warning = f.get("warning", False)
        # In strict mode, WARN bundles fail
        if _cfg.STRICT_MODE and warning:
            passed = False
        details.append(Detail(
            f"bundle:{bundle}",
            passed,
            msg,
            warning=warning,
            measured=f.get("measured", True),
        ))
        if not passed:
            n_fail += 1
        elif warning:
            n_warn += 1

    summary_msg = (
        f"{len(findings)} sub-findings: {n_fail} FAIL / {n_warn} WARN / "
        f"{len(findings) - n_fail - n_warn} PASS"
    )
    if _cfg.STRICT_MODE:
        summary_msg += " (strict mode: WARN promoted to FAIL)"

    # ⚠️ FAIL-CLOSED, and deliberately so. If ANY bundle's freshness could not be
    # established, this check did not measure its population — and the `--ci`
    # floor is exactly the instrument meant to see that. In a healthy tree no
    # detail is unmeasured and this is True; with `lean/.lake` absent all 21 go
    # dark and the floor catches it instead of counting a full measurement.
    # Count BEFORE inserting, so the summary is never in its own population.
    n_unmeasured = sum(1 for d in details if not d.measured)
    if n_unmeasured:
        summary_msg += f" — {n_unmeasured} UNMEASURED"
    details.insert(0, Detail("summary", n_fail == 0, summary_msg,
                             measured=(n_unmeasured == 0)))

    return CheckResult(
        passed=(n_fail == 0),
        measured=(n_unmeasured == 0),
        details=details,
    )


# ═══════════════════════════════════════════════════════════════════════
# CHECK: Inventory-Index autogen freshness (advisory)
# ═══════════════════════════════════════════════════════════════════════

# The Index declares its own contract in its own header — "pointers only, no
# embedded content", and a size ceiling justified by a single `Read` call. Both
# legs below read that contract FROM the file rather than hardcoding it, so the
# guard and the sentence a human reads cannot diverge into two rules.
#
# Down-only, per CHECK_AUTHORING_GUIDE §2.3. Lower either with a stated reason.
_INDEX_NARRATIVE_COUNT_CEILING: int = 19
"""Hand-written counts in the Index's narrative, outside the AUTOGEN blocks.

Measured 2026-08-13 at 19, after pruning a ~10 KB nested changelog from the
header. Every one of these is a second census beside `docs/counts.json`, and the
population is the reason the leg exists: the pruned header stated a theorem count
roughly ten thousand below the AUTOGEN table a few lines down, in the same file,
green throughout — `inventory_index_autogen_fresh` gated the generated blocks and
nothing at all outside them.

⚠️ The pattern matches adjacency and takes false positives (a year beside the word
"Theorem", the `0 axiom` / `0 sorry` invariant restated). That is deliberate: they
sit in the baseline, and the ratchet is down-only, so imprecision costs a slightly
high ceiling and never a missed regression.
"""


# Same shape as `architecture_inventory_fresh`'s narrative-count pattern, over the
# nouns the Index actually publishes. Adjacency-matched and deliberately imprecise
# — see the ceiling's docstring for why that is the right trade here.
_INDEX_COUNT_RE = re.compile(
    r"(?<![-#\w])\d[\d,]*[\s*_`]*"
    r"(?:theorems?|thm|modules?|mod|declarations?|axioms?|sorr(?:y|ies)|definitions?"
    r"|bundles?|papers?|notebooks?|figures?|pytest cases|checks?|gates?)\b",
    re.IGNORECASE)


def _index_narrative_lines(text: str) -> tuple[list[str | None], int, list[str]]:
    """Mask the AUTOGEN regions; return (masked lines, block count, seam errors).

    ⚠️ **The masking IS the seam** (guide §2.5). An unmatched `BEGIN` masks every
    line after it, so the scan quietly walks a shrinking population and reports a
    clean bill — the same shape as the defect this check exists to catch. An
    unmatched marker is therefore an error, not a parse convenience.
    """
    masked: list[str | None] = []
    errors: list[str] = []
    blocks = 0
    inside = False
    for i, ln in enumerate(text.splitlines(), 1):
        if "<!-- AUTOGEN:" in ln and "BEGIN" in ln:
            if inside:
                errors.append(f"L{i}: AUTOGEN BEGIN inside an unclosed block")
            inside = True
        masked.append(None if inside else ln)
        if "<!-- AUTOGEN:" in ln and "END" in ln:
            if not inside:
                errors.append(f"L{i}: AUTOGEN END with no matching BEGIN")
            else:
                blocks += 1
            inside = False
    if inside:
        errors.append("AUTOGEN BEGIN never closed — every line after it was masked")
    return masked, blocks, errors


@register_check("inventory_index_autogen_fresh",
                "SK_EFT_Hawking_Inventory_Index.md: autogen blocks fresh, and its "
                "narrative honours the pointers-only contract it declares")
def check_inventory_index_autogen_fresh() -> CheckResult:
    """The Inventory Index is the pointer layer CLAUDE.md routes a reader to for
    "what is this module", and it owns two halves with different guarantees.

    The ``<!-- AUTOGEN:... -->`` blocks (the §1 counts table, the §3 per-family
    sentence, the §3.1 family->count table) are written by
    ``scripts/update_inventory_index.py`` from ``docs/counts.json``; their
    freshness leg stays ADVISORY, because a stale generated table is a hygiene
    signal and running the generator fixes it.

    ⚠️ **Everything OUTSIDE those markers had no guard at all, and that is where
    the damage was.** Measured 2026-08-13: the narrative was two months stale, over
    the size ceiling it declares for itself, stating a theorem count roughly ten
    thousand below the AUTOGEN table in the same file, and asserting that this repo
    has no ``CLAUDE.md`` — which it does, at 21 KB, as the primary bootstrap. A
    reader who believes that sentence skips the bootstrap and never learns what
    they do not know. Every gate was green.

    The two legs added here BLOCK, and both read the Index's own declared contract
    rather than a constant chosen here:

    * **size** — the header states a ceiling, justified by a single ``Read`` call.
    * **counts** — "pointers only, no embedded content"; a count in the narrative
      is a second census beside ``docs/counts.json``, which is the rule
      ``architecture_inventory_fresh`` already enforces for ``docs/architecture/``.
      This is that mechanism extended to the document that needed it, not a second
      one built beside it.
    """
    details: list[Detail] = []
    all_pass = True

    # ── Leg 1: AUTOGEN freshness (advisory, unchanged) ────────────────────────
    try:
        from update_inventory_index import compute_stale
        stale, summary = compute_stale()
        details.append(Detail(
            "freshness", True,
            f"{summary} — run `uv run python scripts/update_inventory_index.py` "
            f"to refresh" if stale else summary,
            warning=bool(stale)))
    except ImportError as exc:
        details.append(Detail("freshness", True,
                              f"SKIPPED — update_inventory_index not importable: {exc}",
                              warning=True))
    except Exception as exc:  # defensive: an advisory leg never fails the suite
        details.append(Detail("freshness", True,
                              f"SKIPPED — compute_stale raised: {exc}", warning=True))

    # ── Legs 2+3: the narrative half ──────────────────────────────────────────
    idx = _H.PROJECT_ROOT / "SK_EFT_Hawking_Inventory_Index.md"
    if not idx.is_file():
        return CheckResult(passed=False, measured=False, details=details + [Detail(
            "index", False,
            f"SKIPPED — {idx.name} absent; UNVERIFIED, not passing")])
    text = idx.read_text(encoding="utf-8", errors="ignore")

    declared = re.search(r"Keep under\s+(\d+)\s*KB", text)
    if not declared:
        all_pass = False
        details.append(Detail(
            "size_ceiling", False,
            "the Index no longer declares a size ceiling — this leg asserts the "
            "file against its OWN stated rule, so a deleted rule is an unmeasurable "
            "leg, not a passing one. Restore the `Keep under N KB` sentence."))
    else:
        ceiling_kb = int(declared.group(1))
        actual_kb = len(text.encode("utf-8")) / 1024
        ok = actual_kb <= ceiling_kb
        details.append(Detail(
            "size_ceiling", ok,
            f"{actual_kb:.0f} KB, within the {ceiling_kb} KB ceiling the file declares"
            if ok else
            f"{actual_kb:.0f} KB EXCEEDS the {ceiling_kb} KB ceiling the file declares "
            f"for itself. The stated reason is that a bootstrap must read it in one "
            f"call. Prune narrative into SK_EFT_Hawking_Inventory.md — the file's own "
            f"Size-discipline rule says exactly that, and says not to inline wave "
            f"history or per-commit detail here."))
        if not ok:
            all_pass = False

    masked, blocks, seam_errors = _index_narrative_lines(text)
    scanned = sum(1 for m in masked if m is not None)
    if seam_errors or blocks == 0 or scanned == 0:
        all_pass = False
        details.append(Detail(
            "narrative_seam", False,
            f"the AUTOGEN masking is unsound, so the counts leg below walked a "
            f"population it cannot vouch for — blocks={blocks}, narrative "
            f"lines={scanned}, errors={seam_errors or 'none'}"))
    else:
        offenders = [
            f"L{i}: {m.group(0).strip()!r}"
            for i, ln in enumerate(masked, 1) if ln
            for m in [_INDEX_COUNT_RE.search(ln)] if m
        ]
        n = len(offenders)
        ok = n <= _INDEX_NARRATIVE_COUNT_CEILING
        details.append(Detail(
            "no_counts_outside_autogen", ok,
            f"{n} hand-written count(s) in {scanned} narrative line(s), at or below "
            f"the down-only ceiling of {_INDEX_NARRATIVE_COUNT_CEILING} "
            f"({blocks} AUTOGEN block(s) masked)"
            if ok else
            f"{n} hand-written count(s) in the Index narrative EXCEEDS the down-only "
            f"ceiling of {_INDEX_NARRATIVE_COUNT_CEILING}. The Index declares itself "
            f"'pointers only — no embedded content'; a count here is a second census "
            f"beside docs/counts.json and the AUTOGEN blocks, and it drifts. Name the "
            f"artifact that owns the number instead: {offenders[:8]}"))
        if not ok:
            all_pass = False
        elif n < _INDEX_NARRATIVE_COUNT_CEILING:
            details.append(Detail(
                "ratchet_slack", True,
                f"ceiling {_INDEX_NARRATIVE_COUNT_CEILING} now has {_INDEX_NARRATIVE_COUNT_CEILING - n} "
                f"of headroom — lower it to {n} in this commit; a ratchet with slack "
                f"cannot fire (guide §2.3)", warning=True))

    return CheckResult(passed=all_pass, details=details)


@register_check(
    "architecture_inventory_fresh",
    "docs/architecture/SURFACE_INVENTORY.md matches a fresh derivation from the code")
def check_architecture_inventory_fresh() -> CheckResult:
    """The end-to-end architecture map is split into a NARRATIVE and a CENSUS, and this
    gates the census.

    `docs/architecture/END_TO_END_MAP.md` explains how work moves from a roadmap to a
    signed-off publication; `SURFACE_INVENTORY.md` lists *what exists* — every check, gate,
    hook, agent, command, graph type, registry and bundle — derived by
    `scripts/architecture_inventory.py` from the artifact that owns each population.

    The split exists because narrative counts rot, provably and repeatedly here.
    `WAVE_EXECUTION_PIPELINE.md` once opened on a stage count shorter than its own live
    stage list, quoted a check total from an earlier era, and froze the roster at a bundle
    count predating the bundles authorized since. Each was true when written; all three
    have since been repaired, which is the point rather than a reason to relax the rule —
    they were repaired by hand, one at a time, after a reader had already been misled.
    A map nobody can trust is worse than no map, because it is quoted.

    So the census is regenerated, never hand-edited, and this check fails when the tracked
    file no longer matches a fresh run. Regenerate with:

        uv run python scripts/architecture_inventory.py --write

    ⚠️ Deliberately NOT auto-regenerating, unlike its neighbours in this module. A change in
    the inventory means the SYSTEM changed shape — a check appeared, a gate moved, an agent
    was added — and that should be seen and committed by a person, not silently absorbed
    into a passing run. `counts_fresh` auto-regenerates because a count moving is routine;
    the surface moving is not.
    """
    inv = _H.SCRIPT_DIR / "architecture_inventory.py"
    doc = _H.DOCS_DIR / "architecture" / "SURFACE_INVENTORY.md"
    if not inv.exists():
        return CheckResult(passed=True, measured=False, details=[Detail(
            "generator_present", True, f"{inv} absent — nothing to measure", warning=True)])
    if not doc.exists():
        return CheckResult(passed=False, details=[Detail(
            "doc_present", False,
            f"{doc} is missing — run `uv run python scripts/architecture_inventory.py "
            f"--write`. An absent census is not a fresh one.")])

    import importlib.util
    import sys as _sys
    spec = importlib.util.spec_from_file_location("_arch_inventory", inv)
    mod = importlib.util.module_from_spec(spec)
    _sys.modules[spec.name] = mod   # register BEFORE exec — dataclasses probe sys.modules
    try:
        spec.loader.exec_module(mod)
        fresh = mod.render(mod.collect())
    except Exception as exc:  # noqa: BLE001
        return CheckResult(passed=False, details=[Detail(
            "derivation_runs", False,
            f"architecture_inventory.py failed to derive the surface ({exc}) — the census "
            f"cannot be confirmed, which is a failure, not a skip")])

    details: List[Detail] = []
    all_pass = True

    # ── Leg 2: no narrative in docs/architecture/ may state a census count ──────
    #
    # Regenerating the census fixes the census. It does NOTHING about a count written
    # into a narrative, and that is where every contradiction this directory has
    # produced actually lived: one map said 61 checks, another 59, the registry had 65,
    # and one sentence in one file managed to say 61 and 59 at once.
    #
    # Re-syncing them by hand is the lowest-value work in the repository and it recurs
    # on every addition. The fix is not to chase them — it is to make a count OUTSIDE
    # the derived file a hard failure, so there is nothing to chase. A narrative that
    # needs a magnitude links to SURFACE_INVENTORY.md instead.
    #
    # The noun set is deliberately narrow: ONLY populations SURFACE_INVENTORY owns. A
    # doc may still write "the four hazards" or "two caches" — those are stable
    # structural facts nothing else derives, and banning them would make this gate fire
    # on correct work, which per VALIDATION_GATE_TOPOLOGY §3 is how a gate gets
    # switched off.
    arch_dir = doc.parent
    census_nouns = (r"checks?|gates?|hooks?|agents?|commands?|bundles?|"
                    r"node types?|edge types?|validation modules?|"
                    # theorems/declarations added 2026-08-11: a corpus count sat in
                    # VALIDATION_ARCHITECTURE for three rounds, outside every mechanical
                    # guard, while the same file declared such figures forbidden. It moves
                    # on every Lean wave, so prose restating it is a census nobody
                    # reconciles. The live values are derived in counts.json and gated by
                    # `theorem_census_agrees`.
                    r"theorems?|declarations?")
    # (?<![-#\w]) — a digit preceded by a hyphen or a hash is part of a NAME or an
    # ORDINAL, never a count. "Tier-2 checks" is the tier's name; "Invariant #4 gate"
    # is the invariant's number. Both were false positives on correct prose, and per
    # VALIDATION_GATE_TOPOLOGY §3 a gate that fires on correct work gets switched off.
    # `registries` is deliberately absent from the nouns: "rebinding creates two
    # registries" describes a bug mechanism, not the census's registry table.
    # ⚠️ THIS MATCHES ADJACENCY, NOT THE CLASS — a stated limit, not an oversight.
    # `22,669 machine-checked theorems` passes: one adjective separates the number from
    # the noun, and that is this project's own house phrasing (`papers/I1` writes exactly
    # it). Widening to a bounded adjective gap was tried and REVERTED: it caught no live
    # violation and produced three false positives on correct prose — a quoted historical
    # tally, "gate" used as a verb, and `checks` inside the identifier `run_checks`. Per
    # VALIDATION_GATE_TOPOLOGY §3 a gate that fires on correct work gets switched off, so
    # precision wins here and the residue is covered by review, not by this pattern.
    count_re = re.compile(
        r"(?<![-#\w])(?:\d[\d,]*|one|two|three|four|five|six|seven|eight|nine|ten|eleven|twelve)\b"
        r"[\s*_`]*(?:" + census_nouns + r")\b",
        re.IGNORECASE)
    offenders: list[str] = []
    scanned = 0
    for md in sorted(arch_dir.glob("*.md")):
        if md.name == doc.name:      # the census is where counts BELONG
            continue
        scanned += 1
        for i, line in enumerate(md.read_text().splitlines(), 1):
            if line.lstrip().startswith(">") and "SURFACE_INVENTORY" in line:
                continue             # a pointer AT the census may name what it holds
            m = count_re.search(line)
            if m:
                offenders.append(f"{md.name}:{i} {m.group(0).strip()!r}")

    # ── Leg 3: no narrative may enumerate a registry AS IF COMPLETE ────────────
    #
    # Leg 2 guards a count; it does not guard a LIST. Every doc defect the
    # post-ADR-011 reconciliation found was an enumerated roster in prose
    # (ledger V59): two maps naming three reviewers when there were four, and
    # `_VALID_BUNDLE_TARGETS`' members transcribed into schema prose.
    # `END_TO_END_MAP` §9 already states the rule — "an enumerated roster in prose
    # goes stale exactly as an enumerated roster in code does, but nothing fails
    # when it happens" — and that document's own diagram then went stale by it.
    #
    # ⚠️ THE OBVIOUS PREDICATE IS WRONG AND WAS MEASURED BEFORE BEING BUILT.
    # TODO-D30 proposed flagging any narrative line naming >=3 registry members.
    # Measured against the live corpus that fires on **7 lines, all of them
    # correct prose** — "D1, D2 and D3 all cite the same Stage-13 sweep",
    # "D6+D9 share zero declarations" — and on **0 defects**. A gate that fires
    # on correct work gets switched off (VALIDATION_GATE_TOPOLOGY §3).
    #
    # The distinguishing feature is not the enumeration, it is the TOTALISING
    # claim wrapped around it: "the three reviewers are ...", "the existing
    # bundles are ...". Discussing several members is not asserting the set.
    # Measured with the totalising requirement: 0 live offenders, and both
    # reconstructed historical defects fire.
    from bundle_registry import BUNDLE_CODES as _BC
    _agent_dir = _H.PROJECT_ROOT / ".claude/plugins/skeft-qa/agents"
    _registries = {
        "bundles": sorted(_BC),
        "reviewers": sorted(p.stem for p in _agent_dir.glob("*.md")),
    }
    _roster_link_re = re.compile(
        r"bundle_registry|SURFACE_INVENTORY|BUNDLE_CODES|plugins/skeft-qa|registry",
        re.IGNORECASE)
    _totalising_re = re.compile(
        r"\b(?:the|all|every|each|only|consists? of|comprises?|namely)\b"
        r"[^.]{0,60}\b(?:bundles?|targets?|reviewers?|agents?|codes?)\b",
        re.IGNORECASE)
    roster_offenders: list[str] = []
    for _rname, _members in _registries.items():
        if len(_members) < 3:
            continue
        _mem_re = re.compile(r"(?<![\w/-])("
                             + "|".join(map(re.escape, _members)) + r")(?![\w-])")
        for md in sorted(arch_dir.glob("*.md")):
            if md.name == doc.name:
                continue
            for i, line in enumerate(md.read_text().splitlines(), 1):
                if (len(set(_mem_re.findall(line))) >= 3
                        and _totalising_re.search(line)
                        and not _roster_link_re.search(line)):
                    roster_offenders.append(f"{md.name}:{i} [{_rname}]")
    details.append(Detail(
        "no_rosters_in_narratives", not roster_offenders,
        f"{scanned} narrative doc(s) enumerate no registry as if complete"
        if not roster_offenders else
        f"registry roster enumerated as complete in a narrative — name the "
        f"mechanism and link its registry instead of transcribing members: "
        f"{roster_offenders[:6]}"))
    if roster_offenders:
        all_pass = False

    # ── Leg 4: every owned document answers the question README assigns it ────
    #
    # TODO-D8. Assertion-granularity verification is a SOUNDNESS check: it asks
    # whether every sentence present is true. It cannot ask whether a REQUIRED
    # sentence is absent. `README.md:14` assigned "how does work get from a
    # roadmap to a signed-off publication?" to `END_TO_END_MAP.md`, which
    # contained no promotion path at all until 2026-08-07 — while both documents
    # were verified 100 % accurate at assertion granularity, and the suite, the
    # ledger and this very check were all green.
    #
    # The contract is a DECLARED BIDIRECTIONAL LINK, compared verbatim, not a
    # keyword proxy: README says document X answers question Q, and X must carry
    # `> **Answers:** Q`. A keyword heuristic would pass on a document that
    # merely mentions the topic, which is the failure mode being closed.
    #
    # ⚠️ This is a completeness FLOOR, not proof of adequacy. It catches an
    # assignment that drifted away from its answer; it cannot judge whether the
    # answer is good. Stated so nobody reads a green here as more than it is.
    import re as _re
    readme_path = arch_dir / "README.md"
    contract_bad: list[str] = []
    n_owned = 0
    try:
        readme_txt = readme_path.read_text(encoding="utf-8")
    except OSError:
        readme_txt = ""
    for q, dname in _re.findall(
            r"^\|\s*(.+?)\s*\|\s*\[`([^`]+)`\]\([^)]+\)\s*\|\s*$", readme_txt, _re.M):
        if q.lower() == "your question":
            continue
        n_owned += 1
        target = arch_dir / dname
        if not target.is_file():
            contract_bad.append(f"{dname} (assigned but absent)")
            continue
        body = target.read_text(encoding="utf-8", errors="ignore")
        if f"**Answers:** {q}" not in body:
            contract_bad.append(f"{dname} (no verbatim Answers line)")
    if n_owned == 0:
        all_pass = False
        details.append(Detail(
            "owned_questions", False,
            "README.md's ownership table parsed to zero rows — the completeness "
            "leg walked an empty population, which is not evidence that it holds"))
    else:
        details.append(Detail(
            "documents_answer_their_question", not contract_bad,
            f"{n_owned} owned document(s) each declare the question README assigns them"
            if not contract_bad else
            f"ownership assignment without a matching answer: {contract_bad}. Add "
            f"`> **Answers:** <question>` verbatim, or fix README's table."))
        if contract_bad:
            all_pass = False

    # A scan that matched nothing because it walked nothing passes vacuously (D5 §2.5).
    if scanned == 0:
        all_pass = False
        details.append(Detail(
            "narratives_scanned", False,
            f"no narrative .md found beside {doc.name} — the no-counts leg walked an "
            f"empty population, which is not evidence that it holds"))
    else:
        details.append(Detail(
            "no_counts_in_narratives", not offenders,
            f"{scanned} narrative doc(s) in {arch_dir.name}/ state no census count"
            if not offenders else
            f"census count(s) written into a narrative — name the MECHANISM instead "
            f"of the magnitude, and link to whichever artifact OWNS the number: "
            f"{doc.name} for surfaces (checks, gates, hooks, agents, commands, "
            f"bundles, node/edge types, validation modules); docs/counts.json for "
            f"theorem and declaration counts. A corpus count does NOT belong in "
            f"{doc.name} — that file is compared verbatim against a fresh render, so "
            f"a hand-written number there fails leg 1 instead: {offenders[:6]}"))
        if offenders:
            all_pass = False

    # ── Leg 3: every path-like reference in a narrative must RESOLVE ──────────
    #
    # The rot path for these documents is a rename or a deletion: the prose keeps
    # naming `scripts/foo.py` long after it became `scripts/bar.py`, and nothing
    # notices because prose is not compiled. This is the cheapest mechanical guard on
    # doc ACCURACY that exists — it cannot check whether a description is true, but it
    # can check that everything the description names is still there.
    #
    # Deliberate absences are real and must not be forced out of the prose: the maps
    # name `scripts/pre_commit_hook.sh` precisely to say it does NOT exist, and name
    # runtime artifacts that a clean tree has never created. Those live in an explicit
    # exception set with a reason each, ratcheted — the set may SHRINK (when the thing
    # gets built, or the reference is dropped) and a new entry is a deliberate decision.
    deliberately_absent = {
        # AI-Defense Tier 1 names these as its implementation; both are absent, and
        # saying so is the finding. See ARCHITECTURE_TODOs A2.
        "scripts/pre_commit_hook.sh",
        "scripts/install_pre_commit.sh",
        # ⚠️ REASON CORRECTED 2026-08-12. This read "never created", which was true of the
        # tree and false of the mechanism: the P9a browser test clicked Confirm once and
        # the change bus wrote its first event immediately. It is a RUNTIME artifact —
        # absent in a clean checkout, present after anyone confirms a parameter — and is
        # now gitignored alongside the harness's other per-run logs. The exemption stands
        # either way; the reason had to stop being wrong.
        "docs/verification_log.jsonl",
        # Declared as a Bundles-tab input by DASHBOARD.md and named there precisely to say
        # it does NOT exist (ADR-012 C10/D22). Not gitignored either, so its absence is a
        # gap rather than a local-artifact convention. Drop this entry when the submission
        # event log acquires a store.
        "docs/submission_state.json",
        # Runtime artifacts: written during a /goal loop, absent in a clean tree.
        "active_issues.json",
        "blocked_questions.jsonl",
    }
    pathish = re.compile(r"^[A-Za-z_][\w./-]*\.(?:py|sh|md|json|lean|tex|jsonl|toml|yml)$")
    # ⚠️ `docker` added 2026-08-12 (ADR-012 P8d). `docker/docker-compose.graph.yml` EXISTS
    # and was reported dangling the moment DASHBOARD.md moved under `docs/architecture/` —
    # the scanner simply never walked that directory. A root missing from this tuple makes
    # a live file indistinguishable from a deleted one, which is the opposite of what this
    # leg is for, so the fix is the root and never an exception entry.
    roots = ("scripts", "docs", "tests", "src", "papers", "lean", "figures",
             "temporary", "notebooks", "docker", ".claude/plugins/skeft-qa")
    # `.lake` holds the whole Mathlib build tree — tens of thousands of files that no
    # architecture document references. Walking it turns a sub-second scan into minutes.
    skip_parts = {".lake", ".git", "__pycache__", "node_modules", ".pytest_cache"}
    known: set[str] = set()
    bases: set[str] = set()
    for r in roots:
        base = _H.PROJECT_ROOT / r
        if not base.is_dir():
            continue
        for f in base.rglob("*"):
            if not f.is_file() or skip_parts & set(f.parts):
                continue
            try:
                rel = f.relative_to(_H.PROJECT_ROOT).as_posix()
            except ValueError:
                continue
            known.add(rel)
            bases.add(f.name)
    for f in _H.PROJECT_ROOT.glob("*"):
        if f.is_file():
            known.add(f.name)
            bases.add(f.name)

    dangling: list[str] = []
    n_refs = 0
    for md in sorted(arch_dir.glob("*.md")):
        for tok in sorted(set(re.findall(r"`([^`\n]+)`", md.read_text()))):
            tok = tok.strip()
            if not pathish.match(tok) or tok in deliberately_absent:
                continue
            n_refs += 1
            if tok in known or tok in bases:
                continue
            if any(k.endswith("/" + tok) for k in known):
                continue
            dangling.append(f"{md.name}: {tok}")

    if n_refs == 0:
        all_pass = False
        details.append(Detail(
            "doc_refs_resolve", False,
            "no path-like reference found in any narrative — the scan matched nothing, "
            "which is not evidence that every reference resolves"))
    else:
        details.append(Detail(
            "doc_refs_resolve", not dangling,
            f"{n_refs} path-like reference(s) across {arch_dir.name}/ all resolve "
            f"({len(deliberately_absent)} documented-absent refs exempt)"
            if not dangling else
            f"reference(s) naming a file that does not exist — a rename or deletion "
            f"the prose did not follow: {dangling[:6]}"))
        if dangling:
            all_pass = False

    current = doc.read_text()
    if current == fresh:
        details.insert(0, Detail(
            "inventory_fresh", True,
            f"{doc.name} matches a fresh derivation ({len(fresh.splitlines())} lines)"))
        return CheckResult(passed=all_pass, details=details)

    cur_lines, new_lines = current.splitlines(), fresh.splitlines()
    first = next((i for i, (a, b) in enumerate(zip(cur_lines, new_lines)) if a != b),
                 min(len(cur_lines), len(new_lines)))
    details.insert(0, Detail(
        "inventory_fresh", False,
        f"{doc.name} is STALE — the system's surface changed and the census did not. "
        f"First divergence at line {first + 1}: tracked "
        f"{cur_lines[first][:90] if first < len(cur_lines) else '<eof>'!r} vs derived "
        f"{new_lines[first][:90] if first < len(new_lines) else '<eof>'!r}. "
        f"Run `uv run python scripts/architecture_inventory.py --write`."))
    return CheckResult(passed=False, details=details)


@register_check(
    "bundle_counts_fresh",
    "papers/<CODE>/bundle_counts.tex matches a fresh derivation from the bundle's apex closure")
def check_bundle_counts_fresh() -> CheckResult:
    """CHECK: a paper's own substrate figures cannot drift from its substrate.

    `\\bundleTheorems` / `\\bundleDecls` / `\\bundleModules` are generated per bundle by
    `scripts/render_bundle_counts.py` from that bundle's declared-apex closure. They
    exist because the **project-wide** `\\substantivetheorems` was being used for
    **paper-scoped** claims: measured 2026-08-09, E2's verification-chain parenthetical
    stated 26 329 against a verified chain of **6** theorems, and E1's stated the same
    against **11** (TODO-D9).

    ⚠️ **A generated macro is only as honest as its regeneration.** `\\substantivetheorems`
    was itself introduced to stop hand-maintained counts, and it produced the portfolio's
    largest numerical overclaim *because it grew with the library while the sentence
    around it stayed still*. A per-bundle macro fails the same way if nothing re-derives
    it after the apex list changes, so this check is part of the fix rather than a
    nicety.

    Delegates wholly to `render_bundle_counts.build()` — no second derivation lives here.
    The `chain_backing_targets_resolve` precedent is the reason: a check that carried its
    own resolver beside a working one disagreed with it and reported a third more
    failures than the truth.

    ⚠️ **A bundle with no declared apexes emits no file, and that is not a failure** — its
    substrate is UNKNOWN, and a `0` in a manuscript would be a confident wrong number.
    It is reported, and the missing `\\input` fails that draft's compile, which is the
    loud path.
    """
    try:
        import render_bundle_counts as rbc
    except Exception as exc:  # noqa: BLE001
        return CheckResult(passed=False, measured=False, details=[Detail(
            "import", False,
            f"could not import render_bundle_counts ({exc}) — per-bundle counts are "
            f"UNVERIFIED, not fresh")])

    try:
        rendered = rbc.build()
    except Exception as exc:  # noqa: BLE001
        return CheckResult(passed=False, measured=False, details=[Detail(
            "derive", False,
            f"could not derive per-bundle counts ({exc}) — UNVERIFIED, not fresh")])

    details: List[Detail] = []
    stale, missing, undeclared, ok = [], [], [], 0
    for code, body in rendered.items():
        target = _H.PAPERS_DIR / code / "bundle_counts.tex"
        if body is None:
            undeclared.append(code)
            continue
        if not target.is_file():
            missing.append(code)
            continue
        if target.read_text() != body:
            stale.append(code)
        else:
            ok += 1

    if undeclared:
        details.append(Detail(
            "undeclared", True,
            f"{len(undeclared)} bundle(s) declare no apexes, so no counts file is emitted "
            f"(substrate UNKNOWN, not zero): {', '.join(sorted(undeclared))}", warning=True))
    if not ok and not stale and not missing:
        return CheckResult(passed=False, measured=False, details=details + [Detail(
            "seam", False,
            "no bundle produced a counts file — an empty population cannot evidence "
            "freshness; UNVERIFIED, not passing")])
    for code in sorted(missing):
        details.append(Detail(
            f"missing:{code}", False,
            f"{code}: bundle_counts.tex is absent while its apexes are declared — run "
            f"scripts/render_bundle_counts.py (its draft's \\input will also fail)"))
    for code in sorted(stale):
        details.append(Detail(
            f"stale:{code}", False,
            f"{code}: bundle_counts.tex disagrees with a fresh derivation from its apex "
            f"closure — the paper is quoting a substrate figure it no longer has. Run "
            f"scripts/render_bundle_counts.py"))
    details.append(Detail(
        "summary", not (stale or missing),
        f"{ok}/{ok + len(stale) + len(missing)} declared bundle(s) carry a current "
        f"bundle_counts.tex"))
    return CheckResult(passed=not (stale or missing), details=details)
