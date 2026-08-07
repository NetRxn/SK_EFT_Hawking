#!/usr/bin/env python3
"""Lean Declaration Extraction Wrapper

Manages staleness checking and invocation of the Lean meta script
`ExtractDeps.lean`. Provides `load_lean_deps()` for use by
`build_graph.py` and other consumers.

The JSON is cached at `lean/lean_deps.json` with a hash file at
`lean/lean_deps.json.hash`. Re-extraction only happens when .lean
files change.
"""

from __future__ import annotations

import hashlib
import json
import logging
import subprocess
import sys
from pathlib import Path

logger = logging.getLogger(__name__)

PROJECT_ROOT = Path(__file__).resolve().parent.parent
LEAN_DIR = PROJECT_ROOT / "lean" / "SKEFTHawking"
LEAN_ROOT = PROJECT_ROOT / "lean"
JSON_PATH = LEAN_ROOT / "lean_deps.json"
HASH_PATH = LEAN_ROOT / "lean_deps.json.hash"


def serialize_deps(data: list) -> str:
    """Serialize the declaration list as a JSON array with ONE RECORD PER LINE.

    Still ordinary JSON — ``json.loads`` round-trips it — but line-oriented, which matters a
    great deal for a 68 MB artifact that is committed on every counts sync.

    ExtractDeps emits its array on a **single line**, and we used to persist that stdout
    verbatim. A 68 MB single line is pathological for every line-oriented tool in the chain:

    * ``git diff --cached`` over it cost **~25 s** (measured 2026-07-28) — by itself the single
      largest cost in the pre-commit hook, larger than the incremental ``lake build``.
    * git stores a whole new 68 MB blob per sync instead of a delta, because there are no line
      boundaries to delta against.
    * ``grep``/``sed``/review tooling either chokes or silently drops the line (macOS ugrep
      drops it outright in inverted-match mode, exit 0 — a guard that reads as passing).

    One record per line fixes all three at a cost of ~1 byte per declaration. Keys are sorted so
    the serialization is deterministic: two runs over the same declarations produce byte-identical
    output, so a no-op re-extraction shows an EMPTY diff rather than a reordered 68 MB one.

    NOTE this is a pure formatting change — the parsed value is unchanged, so nothing that reads
    the file through ``json.load`` is affected, and it does NOT invalidate
    ``lean_deps.json.hash`` (that hashes the .lean SOURCES, not this file).
    """
    if not data:
        return "[]\n"
    rows = (json.dumps(rec, sort_keys=True, separators=(",", ":")) for rec in data)
    return "[\n" + ",\n".join(rows) + "\n]\n"


def compute_lean_hash() -> str:
    """SHA-256 hash (16 hex chars) of all .lean source files (recursive).

    Uses ``rglob("*.lean")`` to walk every subdirectory under ``SKEFTHawking/``
    so that changes inside namespace folders (e.g. ``GloriosoLiu/``,
    ``CrooksAnalogHawking/``, ``QuantumCrooks/``, ``SymTFTAudit/``,
    ``Resurgence/``) trigger re-extraction. The earlier non-recursive
    ``glob`` missed sub-directory edits and let ``lean_deps.json`` go stale
    silently — observed during Phase 6n session 7 when the new
    ``CrooksAnalogHawking/SKEFTHorizonBridge.lean`` and modified
    ``GloriosoLiu/{EntropyCurrent,OnsagerReciprocity}.lean`` did not refresh
    counts because no top-level file changed.

    ⚠️ **The root aggregate is hashed too, and it is the load-bearing one.**
    ``lean/SKEFTHawking.lean`` sits ONE LEVEL ABOVE ``LEAN_DIR`` and is what
    ``ExtractDeps.lean`` imports, so it alone decides **which modules are in scope
    for extraction**. Adding or removing an import there changes the extracted
    population without touching any file under ``SKEFTHawking/`` — so hashing only
    the subtree left the one edit that changes scope invisible to the cache.

    That is the same defect the paragraph above records fixing, one level up: the
    earlier repair widened the walk from ``glob`` to ``rglob`` — it went *deeper*
    and never went *up*. Added 2026-08-06 after the end-to-end architecture map
    measured it (`docs/architecture/END_TO_END_MAP.md` §4).
    """
    hasher = hashlib.sha256()
    if LEAN_DIR.is_dir():
        for fp in sorted(LEAN_DIR.rglob("*.lean")):
            hasher.update(fp.read_bytes())
    # The aggregate LAST and unconditionally — a missing aggregate must change the
    # hash too, or its deletion would read as "nothing changed".
    aggregate = LEAN_ROOT / "SKEFTHawking.lean"
    hasher.update(aggregate.read_bytes() if aggregate.is_file() else b"<absent>")
    return hasher.hexdigest()[:16]


def _needs_refresh() -> bool:
    """Check if lean_deps.json is stale or missing."""
    if not JSON_PATH.exists():
        return True
    if not HASH_PATH.exists():
        return True
    stored_hash = HASH_PATH.read_text().strip()
    return stored_hash != compute_lean_hash()


def _run_extraction() -> None:
    """Run the Lean extraction script and write the JSON output.

    Serialized at the extraction CHOKEPOINT by the shared ``regen_lock("lean_deps")``
    (ADR-005 D-G.1). The regen lock was previously applied only at the ``/sync``
    orchestration layer, so direct ``load_lean_deps()`` callers (``validate.py``
    ``graph_integrity``, ``build_graph.py``, the dashboard, a swarm lead) bypassed it and
    could launch competing ~5-min extractions — the multi-agent stampede. Wrapping it here
    means EVERY entry point inherits single-writer serialization: if another process holds
    the lock, SKIP and let the caller proceed on the existing cache rather than racing.
    """
    # Local import + path guard: harness_lock lives alongside this script.
    import sys as _sys
    _sys.path.insert(0, str(Path(__file__).resolve().parent))
    import harness_lock  # noqa: E402

    with harness_lock.regen_lock("lean_deps") as got:
        if not got:
            logger.info(
                "lean_deps regen already in progress (lock held by another process) — "
                "using existing cache"
            )
            return
        _run_extraction_locked()


def _run_extraction_locked() -> None:
    """The actual extraction body (runs only while holding the lean_deps regen lock)."""
    logger.info("Lean deps stale — running ExtractDeps.lean...")
    try:
        # Timeout: 1800s = 30 min. ExtractDeps walks every declaration in
        # the SKEFTHawking namespace (~5000+ decls post-Phase-6m) and runs
        # `collectAxioms` on each. Phase 7a sub-wave 7a.0.4 bump from 600s.
        result = subprocess.run(
            ["lake", "env", "lean", "--run", "SKEFTHawking/ExtractDeps.lean"],
            capture_output=True,
            text=True,
            cwd=str(LEAN_ROOT),
            timeout=1800,
        )
        if result.returncode != 0:
            # Lean reports import/elaboration errors on STDOUT (stderr is often
            # empty) — surface both, or failures look blank (2026-07-13 lesson:
            # a missing-olean error hid on stdout through repeated sync failures).
            err = (result.stderr or "").strip() or (result.stdout or "").strip()
            logger.error("ExtractDeps.lean failed:\n%s", err[:500])
            raise RuntimeError(f"ExtractDeps failed: {err[:500]}")

        # Phase 5v Wave 9e: Lean sometimes prints compile warnings
        # (e.g. "String.trim has been deprecated") to stdout before the
        # JSON array. Strip any non-JSON prefix before parsing. The
        # JSON output always begins with `[{` (array of objects).
        stdout = result.stdout
        array_start = stdout.find('[{')
        if array_start > 0:
            prefix = stdout[:array_start].strip()
            if prefix:
                logger.warning("ExtractDeps emitted non-JSON prefix (stripped): %s",
                               prefix[:300])
            stdout = stdout[array_start:]

        # Validate JSON before writing
        data = json.loads(stdout)
        assert isinstance(data, list), "ExtractDeps output must be a JSON array"

        # Persist LINE-ORIENTED, not ExtractDeps' single-line stdout — see serialize_deps().
        JSON_PATH.write_text(serialize_deps(data))
        HASH_PATH.write_text(compute_lean_hash())
        logger.info("Wrote %d declarations to %s", len(data), JSON_PATH)

        # Stage EXTRACT_NAME_DEPS diagnostics from stderr to user visibility.
        if result.stderr:
            # Lean stderr includes our `[name_deps]` status lines — surface
            # them so users know whether proof-dep data is populated.
            for line in result.stderr.splitlines():
                if line.startswith('[name_deps]'):
                    logger.info(line)

    except FileNotFoundError:
        logger.warning("lake not found — cannot run ExtractDeps. Using cached data if available.")
        if not JSON_PATH.exists():
            raise RuntimeError("No cached lean_deps.json and lake not available")
    except subprocess.TimeoutExpired:
        logger.error("ExtractDeps timed out after 600s")
        raise


def load_lean_deps() -> list[dict]:
    """Load Lean declaration data, refreshing if stale.

    Returns a list of declaration dicts with keys:
        name, kind, module, type, axiom_deps_project, axiom_deps_core, structure_fields
    """
    if _needs_refresh():
        _run_extraction()

    if not JSON_PATH.exists():
        logger.warning("lean_deps.json not found — returning empty list")
        return []

    with open(JSON_PATH) as f:
        return json.load(f)


def main() -> int:
    """CLI entry point: refresh `lean_deps.json` if stale (hash-guarded, regen-locked).

    Historically this module was library-only — running it as a script was a SILENT
    no-op (arm-2 friction, 2026-07-12). This entry point makes the script form honest:
    it configures logging (the library's `logger.info` lines are invisible without a
    handler), runs the same guarded `load_lean_deps()` every consumer uses, and reports
    what happened. `--check` reports staleness without extracting (exit 1 if stale).
    """
    import argparse

    logging.basicConfig(level=logging.INFO, format="%(message)s")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true",
                        help="report staleness only; do not extract (exit 1 if stale)")
    args = parser.parse_args()

    if args.check:
        stale = _needs_refresh()
        print(f"lean_deps.json: {'STALE (extraction needed)' if stale else 'fresh'}")
        return 1 if stale else 0

    stale_before = _needs_refresh()
    decls = load_lean_deps()
    print(f"lean_deps.json: {len(decls)} declarations "
          f"({'refreshed' if stale_before else 'already fresh — no extraction run'})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
