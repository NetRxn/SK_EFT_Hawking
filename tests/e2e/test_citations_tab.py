"""Phase 3 — Citation Registry tab: the CITATION_REGISTRY table with outbound
DOI / arXiv links."""
from __future__ import annotations

import pytest
from playwright.sync_api import expect


@pytest.mark.e2e
def test_citation_table_renders_with_columns(page, dashboard_url):
    page.goto(f"{dashboard_url}/?tab=citations", wait_until="load")
    for col in ("Key", "Authors", "Reference", "DOI", "arXiv"):
        expect(page.locator(f"th:has-text('{col}')").first).to_be_visible()
    assert page.locator("table tbody tr").count() > 20


@pytest.mark.e2e
def test_outbound_links_are_safe(page, dashboard_url):
    page.goto(f"{dashboard_url}/?tab=citations", wait_until="load")
    # a.doi-link also appears on the (hidden) Parameters cards, so scope to visible.
    link = page.locator("a.doi-link:visible").first
    expect(link).to_be_visible()
    # External links open in a new tab and carry rel=noopener.
    assert link.get_attribute("target") == "_blank"
    assert "noopener" in (link.get_attribute("rel") or "")
