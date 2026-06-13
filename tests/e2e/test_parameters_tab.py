"""Phase 3 — Parameters tab journey: cards, query-param filters, the
immediate-save verify action (button + keyboard), and the now-honest save bar
(the old no-op "Save All" is gone and the bar no longer bleeds onto other tabs).
"""
from __future__ import annotations

from pathlib import Path

import pytest
from playwright.sync_api import expect

PROJECT_ROOT = Path(__file__).resolve().parents[2]
VERIFICATION_LOG = PROJECT_ROOT / "docs" / "verification_log.jsonl"


@pytest.fixture
def verification_log_guard():
    """Restore docs/verification_log.jsonl around tests that record verify events
    (the /verify change-bus appends to it)."""
    existed = VERIFICATION_LOG.exists()
    backup = VERIFICATION_LOG.read_bytes() if existed else None
    try:
        yield
    finally:
        if backup is not None:
            VERIFICATION_LOG.write_bytes(backup)
        elif VERIFICATION_LOG.exists():
            VERIFICATION_LOG.unlink()


@pytest.mark.e2e
def test_parameter_cards_render(page, dashboard_url):
    page.goto(f"{dashboard_url}/?tab=parameters", wait_until="load")
    expect(page.locator(".param-card").first).to_be_visible()
    assert page.locator(".param-card").count() > 10


@pytest.mark.e2e
def test_status_filter_narrows_cards(page, dashboard_url):
    page.goto(f"{dashboard_url}/?tab=parameters&status=all", wait_until="load")
    all_count = page.locator(".param-card").count()
    page.goto(f"{dashboard_url}/?tab=parameters&status=human_verified", wait_until="load")
    hv_count = page.locator(".param-card").count()
    # Filter genuinely narrows the set (128/205 human-verified at baseline).
    assert 0 < hv_count < all_count, (hv_count, all_count)
    # The status select reflects the active filter.
    assert page.locator("select").first.input_value() == "human_verified"


@pytest.mark.e2e
def test_save_bar_is_honest_and_scoped(page, dashboard_url):
    page.goto(f"{dashboard_url}/?tab=parameters", wait_until="load")
    body = page.locator("body").inner_text()
    assert "Save All" not in body, "the no-op Save All button must be gone"
    assert "accumulate in browser session" not in body, "stale 'accumulate/persist' copy must be gone"
    expect(page.locator(".save-bar")).to_contain_text("save immediately to the audit log")
    # The bar is Parameters-only — it must not bleed onto e.g. the Bundles tab.
    page.goto(f"{dashboard_url}/?tab=bundles", wait_until="load")
    assert page.locator(".save-bar").count() == 0


@pytest.mark.e2e
def test_confirm_button_marks_human_verified(page, dashboard_url, verification_log_guard):
    page.goto(f"{dashboard_url}/?tab=parameters&status=llm_verified", wait_until="load")
    card = page.locator(".param-card").first
    expect(card).to_be_visible()
    card.locator(".btn-confirm").click()
    expect(card).to_contain_text("HUMAN VERIFIED")


@pytest.mark.e2e
def test_keyboard_confirm_shortcut(page, dashboard_url, verification_log_guard):
    page.goto(f"{dashboard_url}/?tab=parameters&status=llm_verified", wait_until="load")
    # currentCard defaults to 0, so `y` confirms the first card (no focus needed).
    page.locator("body").press("y")
    expect(page.locator(".param-card").first).to_contain_text("HUMAN VERIFIED")
