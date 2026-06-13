"""Phase 0 harness sanity: proves the subprocess boot + readiness poll +
chromium driving all work end-to-end before the rest of the suite builds on them."""
from __future__ import annotations

import pytest


@pytest.mark.e2e
def test_dashboard_boots_and_serves(page, dashboard_url):
    page.goto(f"{dashboard_url}/", wait_until="load")
    assert "Provenance Command Center" in page.title()
    # The header H1 renders on every tab.
    assert page.locator("h1").first.inner_text().strip() != ""
