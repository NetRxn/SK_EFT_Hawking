"""Phase 3 — Paper Provenance tab: the sentence-level chain-of-backing inspector
(Datastar SSE). Read-only: selecting a paper loads its prose; we deliberately do
NOT click the per-link verify / cluster-propagate buttons (those mutate
prose_state.json / audit_log.jsonl via the sole-writer CLI)."""
from __future__ import annotations

import pytest
from playwright.sync_api import expect


@pytest.mark.e2e
def test_paper_selector_present(page, dashboard_url):
    page.goto(f"{dashboard_url}/?tab=paper", wait_until="load")
    sel = page.locator("#pp-wrap select").first
    expect(sel).to_be_visible()
    assert sel.locator("option").count() > 10


@pytest.mark.e2e
def test_selecting_paper_loads_prose(page, console_errors, dashboard_url):
    page.goto(f"{dashboard_url}/?tab=paper", wait_until="load")
    page.locator("#pp-wrap select").first.select_option("D1")
    # Banner + prose body morph in via /api/papers/D1/provenance SSE.
    page.wait_for_function(
        "() => (document.getElementById('pp-banner-title-block')?.textContent || '').trim().length > 5",
        timeout=20000,
    )
    expect(page.locator("#pp-banner-title-block")).to_contain_text("Hawking")
    assert len(page.locator("#pp-paper-body").inner_text().strip()) > 100
    assert console_errors == [], console_errors
