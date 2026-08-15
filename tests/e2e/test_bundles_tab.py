"""Phase 2 — the publication-bundle walkthrough: the spine of the reviewer
journey (every scaffolded bundle, review docs, cross-bundle clusters, and the
submission-event round-trip). Also locks the bug fixes (companion link, favicon,
loader-error surfacing) with fail-before / pass-after browser assertions.

The roster assertions are DERIVED from the loader, not pinned to a literal.
This file previously hardcoded 18 while tests/test_bundles_dashboard.py
asserted 19 — the two drifted apart when D10 was scaffolded, and the e2e failure
sat red long enough to stop being read as a signal.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest
from playwright.sync_api import expect

PROJECT_ROOT = Path(__file__).resolve().parents[2]
SUBMISSION_STATE = PROJECT_ROOT / "docs" / "submission_state.json"
sys.path.insert(0, str(PROJECT_ROOT / "scripts"))


def _expected_roster() -> list[str]:
    """Bundle codes in the order the tab is expected to render them."""
    from datastar_bundles import load_bundles_summary

    return [b["code"] for b in load_bundles_summary()["bundles"]]


@pytest.fixture
def submission_state_guard():
    """Back up docs/submission_state.json around a test that records an event,
    then restore (delete if it didn't exist) so the repo file isn't polluted.

    Journalled since 2026-08-15: a killed e2e run used to leave a recorded submission
    event in a tracked file, which is a claim about the project's state that nothing
    downstream distinguishes from a real one.
    """
    import sys
    sys.path.insert(0, str(SUBMISSION_STATE.parent.parent / "scripts"))
    from seed_journal import journalled
    with journalled(SUBMISSION_STATE, allow_absent=True,
                    reason="an e2e test records a real submission event here"):
        yield SUBMISSION_STATE


@pytest.mark.e2e
def test_all_bundles_render(page, dashboard_url):
    roster = _expected_roster()
    page.goto(f"{dashboard_url}/?tab=bundles", wait_until="load")
    expect(page.locator(
        f"h2:has-text('Publication Bundles ({len(roster)})')")).to_be_visible()
    bundle_table = page.locator("table.bundles-table").first
    expect(bundle_table.locator("tbody tr")).to_have_count(len(roster))
    # Tier spot-checks across the architecture.
    expect(page.locator("tr:has(td strong:text-is('F'))")).to_contain_text("Tier 0")
    expect(page.locator("tr:has(td strong:text-is('D9'))")).to_contain_text("Tier 1")
    expect(page.locator("tr:has(td strong:text-is('L1'))")).to_contain_text("Tier 2")
    expect(page.locator("tr:has(td strong:text-is('I3'))")).to_contain_text("Tier 3")
    expect(page.locator("tr:has(td strong:text-is('E2'))")).to_contain_text("Tier 4")


@pytest.mark.e2e
def test_bundle_rows_render_in_roster_order(page, dashboard_url):
    """Codes appear in the loader's order — D10 after D9, not between D1 and D2."""
    page.goto(f"{dashboard_url}/?tab=bundles", wait_until="load")
    rendered = page.locator("table.bundles-table").first.locator(
        "tbody tr td:first-child strong").all_text_contents()
    assert [c.strip() for c in rendered] == _expected_roster()


@pytest.mark.e2e
def test_no_bundle_renders_a_blank_title(page, dashboard_url):
    """D10 rendered an empty title cell because _BUNDLE_TITLES was never updated
    when it was scaffolded; the `.get` default made it silent."""
    page.goto(f"{dashboard_url}/?tab=bundles", wait_until="load")
    rows = page.locator("table.bundles-table").first.locator("tbody tr")
    blank = []
    for i in range(rows.count()):
        row = rows.nth(i)
        code = row.locator("td:first-child strong").inner_text().strip()
        title = row.locator("td").nth(2).inner_text().strip()
        if not title:
            blank.append(code)
    assert blank == [], f"bundles rendered with a blank title cell: {blank}"


@pytest.mark.e2e
def test_review_doc_links_open_markdown(page, dashboard_url):
    page.goto(f"{dashboard_url}/?tab=bundles", wait_until="load")
    link = page.locator("a[href='/api/bundles/F/review']")
    expect(link).to_have_count(1)
    assert link.get_attribute("target") == "_blank", "review docs should open in a new tab"
    # The endpoint actually serves the markdown (not a 404 / empty).
    resp = page.request.get(f"{dashboard_url}/api/bundles/F/review")
    assert resp.status == 200, resp.status
    assert len(resp.text()) > 50


@pytest.mark.e2e
def test_cross_bundle_clusters_render(page, dashboard_url):
    page.goto(f"{dashboard_url}/?tab=bundles", wait_until="load")
    expect(page.locator("h3:has-text('Cross-bundle clusters (2)')")).to_be_visible()
    cluster_table = page.locator("table.bundles-table").nth(1)
    expect(cluster_table.locator("tbody tr")).to_have_count(2)
    expect(cluster_table).to_contain_text("D2, D4, L2")


@pytest.mark.e2e
def test_companion_strategy_link_not_wrong_repo(page, dashboard_url):
    """Issue #2: the PAPER_STRATEGY.md companion reference hard-coded a link to
    github.com/anthropics/claude-code (a copy-paste bug)."""
    page.goto(f"{dashboard_url}/?tab=bundles", wait_until="load")
    expect(page.locator("a[href*='github.com/anthropics/claude-code']")).to_have_count(0)


@pytest.mark.e2e
def test_favicon_declared_no_404(page, console_errors, dashboard_url):
    """Issue #3: declare a favicon so the browser doesn't 404 on /favicon.ico every
    load. Headless chromium doesn't fetch favicon.ico, so the real guard is that the
    icon link is declared; the console check is belt-and-braces."""
    page.goto(f"{dashboard_url}/?tab=bundles", wait_until="load")
    page.wait_for_timeout(200)
    assert page.locator("link[rel='icon']").count() >= 1, "no <link rel=icon> declared in <head>"
    assert [e for e in console_errors if "favicon" in e.lower()] == []


@pytest.mark.e2e
def test_submission_event_recorded_from_ui(page, dashboard_url, submission_state_guard):
    """Issue #1 (BUILD): the submission-event POST endpoint must have a real UI
    caller — an inline form to record drafted/submitted/accepted/... events."""
    marker = "E2E-TEST-EVIDENCE-marker-7f3a"
    page.goto(f"{dashboard_url}/?tab=bundles", wait_until="load")

    form = page.locator("form.submission-form")
    expect(form).to_be_visible()
    form.locator("select[name=bundle]").select_option("L1")
    form.locator("select[name=action]").select_option("submitted")
    form.locator("input[name=evidence]").fill(marker)
    form.locator("button[type=submit]").click()
    page.wait_for_load_state("load")

    # The new event appears in the submission log after the round-trip.
    expect(page.locator(f"text={marker}")).to_be_visible()

    # And it persisted to disk with the right bundle/action.
    data = json.loads(submission_state_guard.read_text())
    assert any(
        e["bundle"] == "L1" and e["action"] == "submitted" and e["evidence"] == marker
        for e in data["events"]
    ), data["events"]
