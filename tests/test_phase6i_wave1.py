"""Wave 1 of Phase 6i — primary-sources cache infrastructure tests.

Network-free unit tests for:
    - src.core.citations.PAPER_TO_PHASE / paper_phase / bibkey_phase
    - scripts/extract_missing_bibkeys.py output shape
    - scripts/back_fill_primary_sources.py status reporting
    - scripts/validate.py citation_primary_sources_present check

Bulk-fetch and promotion are exercised by ad-hoc invocation; their effects
are verified in CITATION_REGISTRY shape + a few spot bibkeys.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent
SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))

from src.core.citations import (
    CITATION_REGISTRY,
    PAPER_TO_PHASE,
    bibkey_phase,
    paper_phase,
)


# ────────────────────────────────────────────────────────────────────────
# Schema invariants
# ────────────────────────────────────────────────────────────────────────

def test_paper_to_phase_keys_exist_on_disk():
    """Every key in PAPER_TO_PHASE matches a real papers/<key>/ directory.

    Exemption: underscore-prefixed keys (e.g. `_phase6w_W1_lean_only`) are
    the deliberate lean-only-wave convention introduced by Phase 6w Wave 1
    (cbc5fe52) — synthetic `used_in` handles that phase-route primary-source
    caching for waves that shipped Lean modules without a per-wave paper
    draft (see the "D.4 sourceless-lift handle" note in CITATION_REGISTRY).
    They intentionally have no papers/<key>/ directory; registry entries
    whose first `used_in` points at them route their cache files to the
    mapped Lit-Search/Phase-X/ dir instead of the Phase-1-and-Background
    fallback. Real (non-underscore) keys must still exist on disk.
    """
    papers_dir = SK_ROOT / "papers"
    missing = [
        k for k in PAPER_TO_PHASE
        if not k.startswith("_") and not (papers_dir / k).is_dir()
    ]
    assert not missing, f"PAPER_TO_PHASE has keys without paper directories: {missing}"


def test_paper_to_phase_values_exist_on_disk():
    """Every PAPER_TO_PHASE value matches a real Lit-Search/Phase-X/ dir."""
    lit = PROJECT_ROOT / "Lit-Search"
    missing = sorted({v for v in PAPER_TO_PHASE.values() if not (lit / v).is_dir()})
    assert not missing, f"PAPER_TO_PHASE values without Lit-Search dirs: {missing}"


def test_paper_phase_resolves_paper_paths():
    assert paper_phase("papers/paper1_first_order/paper_draft.tex") == "Phase-1-and-Background"
    assert paper_phase("papers/paper39_heat_kernel_expansion/paper_draft.tex") == "Phase-6e"
    assert paper_phase("papers/note_rt_ch_bounds/paper_draft.tex") == "Phase-6c"


def test_paper_phase_returns_none_for_non_paper_paths():
    assert paper_phase("src/core/constants.py") is None
    assert paper_phase("docs/CLAUDE.md") is None


def test_bibkey_phase_routes_to_first_paper():
    """A registry entry should route to the first paper in `used_in`."""
    e = CITATION_REGISTRY["Steinhauer2016"]
    assert bibkey_phase(e) == "Phase-1-and-Background"


def test_bibkey_phase_returns_none_for_inprep():
    """In-prep self-cites have no external primary source."""
    e = CITATION_REGISTRY["Roehm2026Wave1"]
    assert e.get("inprep") is True
    assert bibkey_phase(e) is None


# ────────────────────────────────────────────────────────────────────────
# Wave 1 deliverables — shape and population
# ────────────────────────────────────────────────────────────────────────

def test_every_external_entry_has_inprep_field():
    """After Wave 1 promotion, every registry entry carries `inprep`."""
    missing = [k for k, e in CITATION_REGISTRY.items() if "inprep" not in e]
    assert not missing, f"Entries missing 'inprep' field: {missing[:10]}"


def test_every_entry_has_primary_source_path_field():
    """After Wave 1 promotion, every registry entry carries `primary_source_path`."""
    missing = [k for k, e in CITATION_REGISTRY.items() if "primary_source_path" not in e]
    assert not missing, f"Entries missing 'primary_source_path' field: {missing[:10]}"


def test_inprep_entries_have_null_primary_source_path():
    """In-prep self-cites must not point to an external cache file."""
    bad = [
        k for k, e in CITATION_REGISTRY.items()
        if e.get("inprep") and e.get("primary_source_path") is not None
    ]
    assert not bad, f"inprep entries with non-null primary_source_path: {bad}"


def test_external_cache_paths_resolve_when_set():
    """If `primary_source_path` is set, the file exists and is non-empty.

    Tolerated exception: an entry whose file is missing locally BUT is
    recorded in `docs/primary_sources_state.json` with verdict='success'
    is treated as cross-machine sync drift — the central state file says
    the file was successfully fetched (presumably on another workstation)
    but it hasn't been synced to this one. This is a separate concern
    from registry hygiene; the test surfaces it via the `sync_drift`
    list (visible in the failure-on-genuine-bug message) but doesn't
    fail on it.

    Hard failure remains for entries with `primary_source_path` set but
    NO state-file record at all — those are genuine registry bugs (path
    declared but never successfully fetched anywhere).
    """
    import json
    # State file lives in SK_ROOT/docs/, not workspace-level PROJECT_ROOT/docs/.
    state_path = SK_ROOT / "docs" / "primary_sources_state.json"
    state_entries = {}
    if state_path.is_file():
        try:
            state_entries = json.loads(state_path.read_text()).get("entries", {})
        except json.JSONDecodeError:
            state_entries = {}

    bad = []
    sync_drift = []
    for k, e in CITATION_REGISTRY.items():
        path = e.get("primary_source_path")
        if path is None:
            continue
        full = PROJECT_ROOT / path
        if full.is_file() and full.stat().st_size > 0:
            continue
        # Distinguish sync drift (state recorded success) from genuine bug.
        state_entry = state_entries.get(k)
        if state_entry and state_entry.get("verdict") == "success":
            sync_drift.append((k, path))
        else:
            bad.append((k, path))

    assert not bad, (
        f"Cached paths missing on disk WITHOUT a state-file success record "
        f"(genuine registry bugs): {bad[:10]}"
        + (f"\n(Also {len(sync_drift)} entries are sync-drift — recorded as "
           f"fetched in state file but missing locally; those are tolerated.)"
           if sync_drift else "")
    )


# ────────────────────────────────────────────────────────────────────────
# Validate check exercise (deterministic, no network)
# ────────────────────────────────────────────────────────────────────────

def test_validate_citation_primary_sources_present_runs():
    """The new validate.py check runs and produces a summary detail."""
    from validate import check_citation_primary_sources_present  # noqa
    result = check_citation_primary_sources_present()
    summary = next((d for d in result.details if d.name == "summary"), None)
    assert summary is not None
    # Summary message has the expected shape
    assert "cited across" in summary.message
    assert "missing-from-registry" in summary.message


def test_no_missing_from_registry():
    """After Wave 1 promotion, every cited bibkey is registered."""
    from validate import check_citation_primary_sources_present  # noqa
    result = check_citation_primary_sources_present()
    missing_detail = next((d for d in result.details if d.name == "missing_from_registry"), None)
    assert missing_detail is None, (
        "After Wave 1 promotion every \\cite{} target should resolve. "
        "If this fails, run scripts/extract_missing_bibkeys.py and "
        "scripts/promote_primary_sources.py to backfill."
    )


# ────────────────────────────────────────────────────────────────────────
# Stub extractor smoke (idempotent re-run)
# ────────────────────────────────────────────────────────────────────────

@pytest.mark.slow
def test_extract_missing_bibkeys_emits_no_orphans():
    """Re-run the extractor; after promotion all citations resolve so 0 stubs."""
    import extract_missing_bibkeys as ext  # noqa
    rc = ext.main(["--out", str(SK_ROOT / "docs" / ".test_missing_stubs.json")])
    assert rc == 0
    payload = json.loads(
        (SK_ROOT / "docs" / ".test_missing_stubs.json").read_text(encoding="utf-8")
    )
    assert payload["n_stubs"] == 0, (
        f"Post-promotion extractor still finds {payload['n_stubs']} unregistered "
        f"bibkeys: {[s['bibkey'] for s in payload['stubs'][:8]]}"
    )
    assert payload["n_orphans"] == 0
    # Tidy up
    (SK_ROOT / "docs" / ".test_missing_stubs.json").unlink(missing_ok=True)
