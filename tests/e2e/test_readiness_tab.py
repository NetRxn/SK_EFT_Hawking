"""Phase 3 — Paper Readiness tab: the 11-gate × N-paper matrix (Datastar SSE)."""
from __future__ import annotations

import pytest
from playwright.sync_api import expect


@pytest.mark.e2e
def test_readiness_heatmap_populates(page, console_errors, dashboard_url):
    page.goto(f"{dashboard_url}/?tab=readiness", wait_until="load")
    # The heatmap fills in via the /api/readiness SSE morph.
    page.wait_for_selector("#readiness-heatmap td", timeout=20000)
    assert page.locator("#readiness-heatmap td").count() > 50
    expect(page.locator("#readiness-summary-row")).to_contain_text("papers")
    assert console_errors == [], console_errors


@pytest.mark.e2e
def test_readiness_h2_has_no_stale_paper_count(page, dashboard_url):
    page.goto(f"{dashboard_url}/?tab=readiness", wait_until="load")
    h2 = page.locator("#readiness-root h2").inner_text()
    # Was hard-coded "11 gates × 15 papers" while the live count is ~42.
    assert "15 papers" not in h2, h2
