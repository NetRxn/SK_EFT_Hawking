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


def compute_lean_hash() -> str:
    """SHA-256 hash (16 hex chars) of all .lean source files."""
    hasher = hashlib.sha256()
    if LEAN_DIR.is_dir():
        for fp in sorted(LEAN_DIR.glob("*.lean")):
            hasher.update(fp.read_bytes())
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
    """Run the Lean extraction script and write the JSON output."""
    logger.info("Lean deps stale — running ExtractDeps.lean...")
    try:
        result = subprocess.run(
            ["lake", "env", "lean", "--run", "SKEFTHawking/ExtractDeps.lean"],
            capture_output=True,
            text=True,
            cwd=str(LEAN_ROOT),
            timeout=600,
        )
        if result.returncode != 0:
            logger.error("ExtractDeps.lean failed:\n%s", result.stderr[:500])
            raise RuntimeError(f"ExtractDeps failed: {result.stderr[:500]}")

        # Validate JSON before writing
        data = json.loads(result.stdout)
        assert isinstance(data, list), "ExtractDeps output must be a JSON array"

        JSON_PATH.write_text(result.stdout)
        HASH_PATH.write_text(compute_lean_hash())
        logger.info("Wrote %d declarations to %s", len(data), JSON_PATH)

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
