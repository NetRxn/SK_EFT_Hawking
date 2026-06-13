"""Phase 3 — Knowledge Graph (D3) tab.

Regression guard for the bug where one of 478 dangling edges made d3.forceLink
throw "node not found", aborting the whole render so the tab showed "0/0 nodes".
"""
from __future__ import annotations

import pytest
from playwright.sync_api import expect


@pytest.mark.e2e
def test_api_graph_returns_rich_graph(page, dashboard_url):
    resp = page.request.get(f"{dashboard_url}/api/graph")
    assert resp.status == 200
    data = resp.json()
    assert len(data["nodes"]) > 1000
    assert len(data["links"]) > 100


@pytest.mark.e2e
def test_knowledge_graph_renders_nodes_not_blank(page, console_errors, dashboard_url):
    page.goto(f"{dashboard_url}/?tab=graph", wait_until="load")
    # D3 fetches /api/graph then appends one <g.kg-node> per node. A dangling-edge
    # regression would make forceLink throw and zero nodes would render.
    page.wait_for_function(
        "() => document.querySelectorAll('#kg-graph g.kg-node').length > 500",
        timeout=30000,
    )
    total = int(page.locator("#kg-stat-nodes").inner_text().replace(",", ""))
    assert total > 1000, total
    # The load/error element must not be showing an error.
    assert "Error loading graph" not in page.locator("#kg-loading").inner_text()
    # The dropped-dangling-edges message is a console.warn, not an error.
    assert console_errors == [], console_errors


@pytest.mark.e2e
def test_graph_mode_and_layout_controls(page, dashboard_url):
    page.goto(f"{dashboard_url}/?tab=graph", wait_until="load")
    for label in ("Explore", "Trace", "Impact", "Force", "Radial", "Hierarchy", "Circle"):
        expect(page.locator(f"#kg-topbar button:has-text('{label}')").first).to_be_visible()
