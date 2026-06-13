"""Phase 1 — smoke every dashboard tab: it routes to the right tab, renders a
content landmark (not a blank/broken tab), and throws no Flask traceback or JS
console error. Deep per-tab journeys live in the test_<tab>_tab.py files.
"""
from __future__ import annotations

import pytest
from playwright.sync_api import expect

# (tab slug, a landmark selector that is unique-and-visible on that tab)
TABS = [
    ("parameters", ".param-card"),
    ("formulas", "th:has-text('Function')"),
    ("lean", ".summary-item:has-text('Axioms')"),
    ("citations", "th:has-text('Authors')"),
    ("graph", "#kg-wrap"),
    ("readiness", "#readiness-root"),
    ("qi", "#qi-root"),
    ("chains", "#rs-root"),
    ("paper", "#pp-wrap"),
    ("bundles", "h2:has-text('Publication Bundles')"),
]


def _non_favicon(errors):
    """Drop favicon 404s — that's handled by its own fix/test in Phase 2."""
    return [e for e in errors if "favicon" not in e.lower()]


@pytest.mark.e2e
@pytest.mark.parametrize("slug,landmark", TABS, ids=[t[0] for t in TABS])
def test_tab_renders_without_errors(page, console_errors, dashboard_url, slug, landmark):
    page.goto(f"{dashboard_url}/?tab={slug}", wait_until="load")

    # 1. Server routed to exactly the requested tab.
    active = page.locator("a.tab.active")
    expect(active).to_have_count(1)
    assert f"tab={slug}" in (active.get_attribute("href") or ""), \
        f"active nav tab does not target {slug!r}"

    # 2. The tab's content landmark is actually visible.
    expect(page.locator(landmark).first).to_be_visible()

    # 3. No Flask error page leaked into the body.
    body = page.locator("body").inner_text()
    assert "Traceback (most recent call last)" not in body
    assert "Internal Server Error" not in body

    # 4. No JS console errors beyond the (separately-fixed) favicon 404.
    leftover = _non_favicon(console_errors)
    assert leftover == [], f"console errors on {slug}: {leftover}"
