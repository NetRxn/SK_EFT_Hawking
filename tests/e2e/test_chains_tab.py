"""Phase 3 — Research Status (Chains) tab: named provenance chains with
theorem/axiom/milestone counts (Datastar SSE)."""
from __future__ import annotations

import pytest
from playwright.sync_api import expect


@pytest.mark.e2e
def test_chains_list_populates(page, console_errors, dashboard_url):
    page.goto(f"{dashboard_url}/?tab=chains", wait_until="load")
    page.wait_for_function(
        "() => (document.getElementById('rs-chains-list')?.children.length || 0) > 0",
        timeout=20000,
    )
    # At least one named chain renders with a theorem count.
    expect(page.locator("#rs-chains-list")).to_contain_text("thms")
    assert console_errors == [], console_errors
