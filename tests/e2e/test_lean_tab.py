"""Phase 3 — Proof Architecture (lean) tab: axiom command panel, declaration
browser, and the cross-link into the Knowledge Graph."""
from __future__ import annotations

import pytest
from playwright.sync_api import expect


@pytest.mark.e2e
def test_summary_bar_and_axiom_cards(page, dashboard_url):
    page.goto(f"{dashboard_url}/?tab=lean", wait_until="load")
    expect(page.locator(".summary-item:has-text('Axioms')").first).to_be_visible()
    # The axiom command panel renders at least one axiom card.
    expect(page.locator(".axiom-card").first).to_be_visible()
    assert page.locator(".axiom-card").count() >= 1


@pytest.mark.e2e
def test_declaration_browser_and_kg_crosslink(page, dashboard_url):
    page.goto(f"{dashboard_url}/?tab=lean", wait_until="load")
    expect(page.locator("#decl-browser-table")).to_be_visible()
    assert page.locator("#decl-browser-table tbody tr").count() > 10
    # "View in KG" jumps to the graph tab.
    expect(page.locator("a.btn-kg[href='?tab=graph']").first).to_be_visible()
