"""Input-fingerprint memoization for the few genuinely expensive checks.

WHY THIS EXISTS
---------------
Measured on this branch (2026-08-05), the 55-check suite costs **332.6 s**, and
**43 of those checks finish in under one second**. The cost is three checks:

    axiom_closure_allowlist    145.4 s   (shells `lake env lean --run AxiomAudit`)
    lean_docstring_refs_resolve 52.8 s   (greps the pinned Mathlib source tree)
    paper_latex_compiles        16.6 s   (pdflatex × 21 bundle drafts)

Measured over all 5,814 commits on `main` since 2026-03-01, `lean/` is touched in
**78 %** of them — so on a Lean wave these checks MUST re-measure and this module
saves nothing, by design. What it saves is the repeat: a `/goal` loop runs
`validate.py`, fixes a doc / paper / count issue, and runs it again, and every
such re-run after a non-Lean edit drops 198 s to 0.1 s. Paper- and doc-side waves
get the same.

⚠️ Do NOT re-derive this from the branch you are on. An earlier draft measured 400
commits of the ADR-009 infra branch and read "`lean/` moves in 47 %", concluding
half of every run was wasted. Core-infrastructure branches are not how this repo
normally works — normal work is Lean, or paper/notebook.

The house already solves this twice — `extract_lean_deps.py`'s source-hash skip
and `NOTEBOOK_EXEC_CACHE`'s per-notebook content hash. This module is that idiom
made shared, so the third and fourth users do not each reinvent it.

THE HAZARD, STATED PLAINLY
--------------------------
A memoized check reports PASS **without measuring anything**. That is precisely
"absence of measurement rendered as success" — the defect class this entire audit
exists to close — and it is sound *only* if the key covers every input. A key that
misses an input is strictly worse than no cache: it manufactures a green tick that
survives the very change it should have caught.

Four structural guards, in order of how much they carry:

1. **The key includes the check function's own source** (`source_fingerprint`).
   Editing the check — including editing what it reads — invalidates every entry.
   This is the guard that makes the others recoverable rather than permanent.
2. **`tests/test_validation_memo.py` seeds a real change into each declared input,
   in the production tree, and asserts the key moves.** Per QI-30: a mutation
   caught against a patched fixture proves nothing about production.
3. **Only PASS is cached.** A failing check re-runs every time, so a red check can
   never be memoized away, and a fix is never masked by a stale failure.
4. **The skip is VISIBLE, and the whole report is replayed** — a memo hit emits a
   `Detail` saying so (like `notebook_exec`'s `skip_cache` line) *and* re-emits
   every detail of the cached run. Caching only the verdict would have deleted
   `axiom_closure_allowlist`'s ⚠ "N declaration(s) carry a non-allow-listed axiom"
   from every run after the first — real trust-surface signal, silently narrowed.

Plus two blunt escapes: `--no-memo`, and `--strict` implying it (see `memoized`).

FAIL-SAFE DIRECTION
-------------------
Every error path here computes rather than skips. Unreadable cache, unparseable
JSON, unhashable input, schema mismatch — all fall through to the real check. The
cache can only ever make a run *slower* when it is broken, never greener.
"""
from __future__ import annotations

import hashlib
import inspect
import json
import os
from pathlib import Path
from typing import Callable, Iterable

import validate_helpers as _H
from validation import _config as _cfg
from validation._registry import CheckResult, Detail

#: Bump to invalidate every stored entry at once — the escape hatch for a change
#: that alters check semantics without altering any file a key names (a dependency
#: upgrade, a Lean toolchain bump whose pin files are unchanged). Cheap: the next
#: run pays full price once.
MEMO_SCHEMA = 1

#: Machine-local, git-ignored (`.gitignore`, alongside the notebook skip-cache and
#: the four `lean/.lean_*_cache.json` ExtractDeps caches). Never tracked: a shared
#: cache would let one workstation's vetted state answer for another's tree.
MEMO_CACHE = "docs/validation/.check_memo.json"


def _cache_path() -> Path:
    """H1: anchor through `_H` at each use, never a module-level constant."""
    return _H.PROJECT_ROOT / MEMO_CACHE


# ══════════════════════════════════════════════════════════════════════════
# Fingerprint builders — each returns a short hex digest, or a distinct
# sentinel for "absent". Absence must hash DIFFERENTLY from empty, so that
# creating a missing input invalidates the entry.
# ══════════════════════════════════════════════════════════════════════════

def files_fingerprint(paths: Iterable[Path]) -> str:
    """Digest of the named files' contents, order-independent of the caller.

    A missing file contributes the literal ``\\0MISSING`` rather than nothing, so
    "the file does not exist" and "the file is empty" are different keys.
    """
    hasher = hashlib.sha256()
    for fp in sorted(set(paths), key=str):
        hasher.update(str(fp).encode("utf-8"))
        try:
            hasher.update(fp.read_bytes())
        except OSError:
            hasher.update(b"\0MISSING")
    return hasher.hexdigest()[:16]


def tree_fingerprint(root: Path, pattern: str = "**/*") -> str:
    """Digest of every file under ``root`` matching ``pattern``.

    Names are hashed alongside contents so a pure rename moves the key. Measured:
    2,039 `lean/SKEFTHawking/**/*.lean` files in **0.42 s**, against the 198 s of
    Lean checks it gates.
    """
    hasher = hashlib.sha256()
    if not root.is_dir():
        return "\0ABSENT"
    for fp in sorted(root.glob(pattern)):
        if not fp.is_file():
            continue
        hasher.update(str(fp.relative_to(root)).encode("utf-8"))
        try:
            hasher.update(fp.read_bytes())
        except OSError:
            hasher.update(b"\0UNREADABLE")
    return hasher.hexdigest()[:16]


def source_fingerprint(fn: Callable) -> str:
    """Digest of a function's own source text — guard 1 above. Applied
    automatically to every memoized body by :func:`memoized`; callers do not
    (and must not need to) add it themselves.

    `inspect.getsource` can raise for a function with no retrievable source (a
    C-level or exec'd callable). That returns a sentinel that varies per call, so
    the key never matches and the check always runs: fail-safe, not fail-quiet.
    """
    try:
        return hashlib.sha256(inspect.getsource(fn).encode("utf-8")).hexdigest()[:16]
    except (OSError, TypeError):
        return f"\0NOSOURCE:{id(fn)}"


def lean_source_fingerprint() -> str:
    """The Lean substrate's content key.

    ⚠️ Deliberately hashes the **sources**, not `lean/lean_deps.json.hash`, even
    though that file already holds an equivalent digest. That file is written by
    `extract_lean_deps.py` when it regenerates — so after a `.lean` edit and
    before the next extract, it holds the digest of the PREVIOUS tree. Keying on
    it would skip exactly the run that should have caught the edit. Recomputing
    costs 0.42 s and cannot be stale.
    """
    return tree_fingerprint(_H.PROJECT_ROOT / "lean" / "SKEFTHawking", "**/*.lean")


def toolchain_pin_fingerprint() -> str:
    """Mathlib / PhysLib / toolchain pins — one matched set, per the project's
    coupled-bump rule. Any check that reads the pinned Mathlib source tree must
    include this, or a pin bump leaves its verdict frozen at the old Mathlib.

    ``lake-manifest.json`` is in here alongside the declared pins because it
    records the exact resolved revision of every dependency. The declared pins
    alone would miss a `lake update` that re-resolves a transitive dep without
    anyone editing `lakefile.toml` — which is precisely the case the private
    repo's bump-pairing note documents as having happened.

    Hashing the ~5 GB `.lake/packages/mathlib` source tree itself is the
    alternative and is not worth it: the manifest is the same information at
    four orders of magnitude less cost.
    """
    lean = _H.PROJECT_ROOT / "lean"
    return files_fingerprint([lean / "lakefile.toml", lean / "lean-toolchain",
                              lean / "lake-manifest.json"])


# ══════════════════════════════════════════════════════════════════════════
# The memo itself
# ══════════════════════════════════════════════════════════════════════════

def _load() -> dict:
    try:
        loaded = json.loads(_cache_path().read_text())
    except (OSError, json.JSONDecodeError):
        return {}
    if not isinstance(loaded, dict) or loaded.get("schema") != MEMO_SCHEMA:
        return {}
    entries = loaded.get("entries")
    return entries if isinstance(entries, dict) else {}


def _store(entries: dict) -> None:
    try:
        path = _cache_path()
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(
            {"schema": MEMO_SCHEMA, "entries": entries}, indent=2, sort_keys=True))
    except OSError:
        pass  # a cache that cannot be written is a slow run, never a wrong one


def memo_key(*parts: str) -> str:
    """Combine fingerprint contributors into one key."""
    return hashlib.sha256("|".join(parts).encode("utf-8")).hexdigest()[:24]


def memoized(name: str, key: str, compute: Callable[[], CheckResult],
             what: str) -> CheckResult:
    """Run ``compute``, or return a PASS if ``key`` matches its last passing run.

    ``what`` names the inputs in the visible skip message, so a reader of the
    report can tell what the cached verdict is conditional on without opening this
    module.

    BYPASSES
    --------
    ``--no-memo`` bypasses unconditionally. ``--strict`` implies it, and that is a
    deliberate asymmetry rather than belt-and-braces: `--strict` is the Paper
    Submission Gate (Invariant #12), the one irreversible consumer, and the one
    place where paying 200 s to re-measure from scratch is obviously worth more
    than the cache is. Everywhere else the key is trusted, because if it cannot be
    trusted there it should not be trusted at submission either — and then the
    right fix is the key, not a second opinion.

    ``SKEFT_VALIDATION_NO_MEMO=1`` bypasses too, and `tests/conftest.py` sets it
    for the whole suite. Without it a test that monkeypatches a check's internals
    and calls it would write a cache entry keyed on the REAL inputs but holding a
    verdict reached under the patch — poisoning the developer's next real run.
    That is the fixture-vs-production confusion of QI-30, pointed at the cache.
    """
    bypass = (_cfg.NO_MEMO or _cfg.STRICT_MODE
              or os.environ.get("SKEFT_VALIDATION_NO_MEMO") == "1")
    entries = {} if bypass else _load()

    # Guard 1, folded in HERE rather than left to each caller's `key_fn`: the body's
    # own source is part of every key, unconditionally. A caller that forgot it would
    # get a cache surviving an edit to the very check it caches — and a guard you can
    # forget to apply is the parallel-list failure this codebase keeps re-finding.
    key = memo_key(key, source_fingerprint(compute))

    # ONE entry per check, keyed on the LAST passing state — not a keyed history.
    # Consequence, deliberate: reverting a file to a previously-vetted state MISSES
    # and re-runs, because the stored key moved on. That is the safe direction and
    # a multi-entry history would only trade it for unbounded cache growth
    # (`lean_docstring_refs_resolve` alone replays 844 details).
    hit = entries.get(name)
    if isinstance(hit, dict) and hit.get("key") == key:
        # REPLAY THE WHOLE REPORT, not just the verdict. `axiom_closure_allowlist`
        # passes non-strict while emitting ⚠ "N declaration(s) carry a
        # non-allow-listed axiom" — real trust-surface signal the reader is meant to
        # see. A cached bare PASS would delete that warning from every run after the
        # first, which is a silent narrowing of what the suite reports: the same
        # defect class as the cache itself, one field over.
        return CheckResult(
            passed=True,
            details=[Detail("memo", True,
                            f"SKIPPED (cached) — {what} unchanged since the last "
                            f"PASS; --no-memo (or --strict) re-measures")]
                    + [Detail(*d) for d in hit.get("details", [])])

    result = compute()

    # Only PASS is recorded, and a FAIL actively evicts: a check that starts
    # failing must not leave a stale green key behind for the next run to find.
    if not bypass:
        entries = _load()
        if result.passed:
            entries[name] = {
                "key": key,
                "details": [[d.name, d.passed, d.message, d.warning]
                            for d in result.details],
            }
        else:
            entries.pop(name, None)
        _store(entries)

    return result


def memoize_check(name: str, key_fn: Callable[[], str], what: str):
    """Decorator form: wrap a check body so it is memoized on ``key_fn()``.

    ``key_fn`` is deferred (a callable, not a value) because keys must be computed
    at RUN time. Evaluated at import time they would freeze the tree's state as of
    process start — the same import-time-copy hazard `_config`'s docstring exists
    to warn about, one layer over.

    The wrapper carries ``__memo_body__``, and that is not a convenience: several
    guards in `tests/` resolve a check by registry name and then INSPECT it — the
    flag-propagation test reads `co_names` for `_cfg`, the cannot-measure baseline
    scans the source for early-return sites. Against a bare wrapper each of those
    silently inspects the wrong function and passes vacuously. They unwrap through
    this attribute instead. A memo whose side effect is to blind three
    introspecting guards would cost more than the 198 s it saves.
    """
    def deco(body: Callable[[], CheckResult]) -> Callable[[], CheckResult]:
        def wrapper() -> CheckResult:
            return memoized(name, key_fn(), body, what)
        wrapper.__name__ = body.__name__
        wrapper.__qualname__ = body.__qualname__
        wrapper.__doc__ = body.__doc__
        wrapper.__memo_body__ = body            # type: ignore[attr-defined]
        return wrapper
    return deco


def unwrap(fn: Callable) -> Callable:
    """The real check body behind a `memoize_check` wrapper (or `fn` itself).

    Every test that resolves a check by registry name and then inspects its code,
    source or flag usage must go through this.
    """
    return getattr(fn, "__memo_body__", fn)
