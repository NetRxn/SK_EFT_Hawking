"""Dependency-free regression guards for the Knowledge Graph tab fix (the
dangling-edge crash + hidden load error). Always run — no browser needed.
Complements the browser test tests/e2e/test_graph_tab.py.
"""
from __future__ import annotations

from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
GRAPH_TPL = (PROJECT_ROOT / "scripts" / "templates" / "partials" / "graph_tab.html").read_text()


def test_graph_drops_dangling_edges_before_forcelink():
    # d3.forceLink throws "node not found" on the first edge referencing an absent
    # node, blanking the whole graph. initGraph must filter such edges first.
    assert "links = links.filter" in GRAPH_TPL
    assert "dangling edge" in GRAPH_TPL.lower()


def test_graph_load_error_is_made_visible():
    # The fetch .catch writes into #kg-loading, which the success path set to
    # display:none — it must restore display so the error isn't silently hidden.
    assert "el.style.display = ''" in GRAPH_TPL
