# SK_EFT_Hawking/tests/test_sync_manifest.py
"""Tests for the L0 sync manifest (deterministic mechanical-artifact edges).
Run: cd SK_EFT_Hawking && uv run python -m pytest tests/test_sync_manifest.py -q
NOTE: scripts/ is not on sys.path by default — load sync_manifest via the helper below;
do NOT `import sync_manifest` at module level (that fails at COLLECTION, masking the
real signal)."""
import importlib.util
import sys
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent.parent / "scripts"


def _load(mod):
    spec = importlib.util.spec_from_file_location(mod, SCRIPTS / f"{mod}.py")
    m = importlib.util.module_from_spec(spec)
    sys.modules[mod] = m            # register BEFORE exec: the canonical importlib pattern.
    # Required because sync_manifest uses `from __future__ import annotations`, so
    # @dataclass resolves its string field annotations via sys.modules[cls.__module__]
    # at class-creation; an unregistered module makes that None -> AttributeError.
    spec.loader.exec_module(m)
    return m


def test_manifest_enumerates_known_edges():
    m = _load("sync_manifest")
    keys = {e.output for e in m.EDGES}
    # The canonical mechanical artifacts must all be covered:
    assert any("counts.json" in k for k in keys)
    assert any("counts.tex" in k for k in keys)
    assert any("lean_deps.json" in k for k in keys)
    assert any("Inventory_Index.md" in k for k in keys)  # autogen blocks
    assert any("tables" in k for k in keys)


def test_each_edge_has_regen_and_staleness():
    m = _load("sync_manifest")
    for e in m.EDGES:
        assert e.regen_cmd, f"{e.output} missing regen_cmd"
        assert callable(e.is_stale), f"{e.output} missing is_stale"
        assert e.cost in ("cheap", "heavy"), f"{e.output} bad cost {e.cost}"


def test_stale_artifacts_is_subset_of_outputs():
    m = _load("sync_manifest")
    outs = {e.output for e in m.EDGES}
    assert all(s in outs for s in m.stale_artifacts())


def test_cheap_only_excludes_heavy_edges(monkeypatch):
    """Falsifiable: force EVERY edge stale, then --cheap-only must return exactly the
    cheap-edge outputs and NEVER a heavy one — the cost gating the commit gate relies on."""
    m = _load("sync_manifest")
    monkeypatch.setattr(m, "EDGES",
                        [m.Edge(e.output, e.inputs_glob, e.regen_cmd, lambda: True, e.cost)
                         for e in m.EDGES])
    cheap = set(m.stale_artifacts(cheap_only=True))
    heavy_outs = {e.output for e in m.EDGES if e.cost == "heavy"}
    cheap_outs = {e.output for e in m.EDGES if e.cost == "cheap"}
    assert cheap == cheap_outs and not (cheap & heavy_outs)
