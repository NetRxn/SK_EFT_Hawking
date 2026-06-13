"""Phase 3 — Process Health (QI) tab: the Stage-14 Quality-Improvement register
(Datastar SSE). An empty register (0 open items) is a valid clean state."""
from __future__ import annotations

import pytest
from playwright.sync_api import expect


@pytest.mark.e2e
def test_qi_register_populates(page, console_errors, dashboard_url):
    page.goto(f"{dashboard_url}/?tab=qi", wait_until="load")
    expect(page.locator("#qi-root h2")).to_contain_text("Process Health")
    # Summary morphs in via SSE; "QI items" appears whether the count is 0 or N.
    page.wait_for_function(
        "() => /QI items/i.test(document.getElementById('qi-summary')?.textContent || '')",
        timeout=20000,
    )
    assert console_errors == [], console_errors
