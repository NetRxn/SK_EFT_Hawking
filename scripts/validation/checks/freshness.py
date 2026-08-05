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

CLAIM_CLUSTERS_PATH = _H.PAPERS_DIR / "claim_clusters.json"


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
    v2_files: list[Path] = []
    for p in _H.PAPERS_DIR.iterdir():
        if not p.is_dir() or not p.name.startswith('paper'):
            continue
        cr = p / 'claims_review.json'
        if not cr.exists():
            continue
        try:
            data = json.loads(cr.read_text())
        except json.JSONDecodeError:
            continue
        if isinstance(data.get('sentences'), list):
            v2_files.append(cr)
    if not v2_files:
        return False, "no v2 claims_review.json files"
    if not CLAIM_CLUSTERS_PATH.exists():
        return True, f"{len(v2_files)} v2 paper(s), no claim_clusters.json"
    cluster_mtime = CLAIM_CLUSTERS_PATH.stat().st_mtime
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
    if CLAIM_CLUSTERS_PATH.exists():
        try:
            data = json.loads(CLAIM_CLUSTERS_PATH.read_text())
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
        return CheckResult(passed=True, details=[
            Detail("import", True, f"nbclient/nbformat unavailable ({exc}); skipping",
                   warning=True)])

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
        return CheckResult(
            passed=False,
            error=f"check_bundle_source_freshness module unavailable: {exc}",
        )

    findings = _run_check()
    if not findings:
        return CheckResult(
            passed=True,
            details=[Detail(
                "scope",
                True,
                "no bundle directories initialized yet (pre-Phase-7-execution state)",
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
    details.insert(0, Detail("summary", n_fail == 0, summary_msg))

    return CheckResult(
        passed=(n_fail == 0),
        details=details,
    )


# ═══════════════════════════════════════════════════════════════════════
# CHECK: Inventory-Index autogen freshness (advisory)
# ═══════════════════════════════════════════════════════════════════════

@register_check("inventory_index_autogen_fresh",
                "Advisory: SK_EFT_Hawking_Inventory_Index.md autogen blocks match docs/counts.json")
def check_inventory_index_autogen_fresh() -> CheckResult:
    """Advisory watchlist: the auto-generated blocks in the Inventory Index
    (the §1 counts table, the §3 per-family-counts sentence, and the §3.1
    generated family->count table) must reflect ``docs/counts.json``.

    These blocks are owned by ``scripts/update_inventory_index.py`` and
    bracketed by ``<!-- AUTOGEN:... -->`` markers. They drift between manual
    syncs whenever ``update_counts.py`` regenerates ``counts.json`` without a
    follow-up index refresh. This check is ADVISORY (always passes, warns on
    staleness) — mirroring ``elaboration_knob_watchlist`` semantics — because a
    stale doc-index is a documentation-hygiene signal, not a soundness or
    pipeline-invariant failure. Fix: run
    ``uv run python scripts/update_inventory_index.py``.

    Runs the generator's ``compute_stale`` logic in-process (no shelling out).
    """
    try:
        from update_inventory_index import compute_stale
    except ImportError as exc:
        return CheckResult(passed=True, measured=False, details=[
            Detail("import", True,
                   f"SKIPPED — update_inventory_index not importable: {exc}",
                   warning=True)])

    try:
        stale, summary = compute_stale()
    except Exception as exc:  # defensive: never fail the suite on an advisory
        return CheckResult(passed=True, measured=False, details=[
            Detail("compute", True,
                   f"SKIPPED — compute_stale raised: {exc}", warning=True)])

    if stale:
        return CheckResult(passed=True, details=[
            Detail("freshness", True,
                   f"{summary} — run `uv run python "
                   "scripts/update_inventory_index.py` to refresh",
                   warning=True)])
    return CheckResult(passed=True, details=[
        Detail("freshness", True, summary)])
