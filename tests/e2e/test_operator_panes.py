"""ADR-012 P9b/P9c — the three operator panes, driven in a real browser.

⚠️ **THIS FILE IS THE SECOND HALF OF WHY THESE PANES EXIST AT ALL.** They shipped as
2,360 lines that nothing imported: no route, no template, no reachable surface, and every
gate green — because an unreferenced module is not a broken reference, a template-contract
test needs a template, and a browser test needs a route
(`papers/AutomatedReviews/2026-08-13-p9-panes-unwired/infra.md`). A server-side
`test_client` could not have caught it either; only fetching the page can.

Each test asserts the pane rendered its OWN content, never merely that the page returned
200. A 200 with an empty panel is the exact failure mode D2's dashboard exception was
written for, and it is what the unwired state would have produced if the tab link had
existed without the include.
"""
from __future__ import annotations

import pytest
from playwright.sync_api import expect


@pytest.mark.e2e
def test_flow_board_renders_the_roster_and_its_caveats(page, console_errors, dashboard_url):
    """The board must show rows AND the sentences saying what it cannot see.

    `flow_board()` raises rather than returning an empty board, so a rendered board with
    zero rows would mean the template dropped them — which is why the row assertion is a
    count, not a truthiness check.
    """
    page.goto(f"{dashboard_url}/?tab=flow", wait_until="load")
    expect(page.locator(".flow-board h2")).to_contain_text("Flow")
    assert page.locator(".flow-board .flow-table tbody tr").count() >= 21, (
        "the Flow board rendered fewer rows than the bundle roster — an empty or "
        "truncated board is not a clean portfolio")
    # The coverage block is the partition assertion; a board without it looks complete
    # over a population it never reached.
    expect(page.locator(".flow-board .flow-coverage")).to_be_visible()
    assert page.locator(".flow-board .flow-caveats li").count() >= 1, (
        "the board rendered no caveats — §7.5 alone always produces one")
    assert console_errors == [], console_errors


@pytest.mark.e2e
def test_a_non_verdict_cell_is_not_painted_as_a_verdict(page, dashboard_url):
    """⚠️ THE RENDER-LAYER HALF OF THE MODULE'S REFUSAL.

    `dashboard_flow` refuses to call an unmeasured stage passed or failed. A template that
    styled `not-tracked` with the green rule would put that defect back one layer up,
    where no test of the module could see it. §7.5 is `not-tracked` for every bundle by
    design (ADR-012 C3), so this is guaranteed to have a subject.
    """
    page.goto(f"{dashboard_url}/?tab=flow", wait_until="load")
    cell = page.locator(".flow-board .flow-not-tracked").first
    expect(cell).to_be_visible()
    bg = cell.evaluate("el => getComputedStyle(el).backgroundImage")
    assert "gradient" in bg, (
        f"a not-tracked cell renders with backgroundImage={bg!r} — it must be visibly "
        "distinct from pass and fail, not a flat verdict colour")


@pytest.mark.e2e
def test_attention_renders_four_feeds_and_leads_with_its_caveats(page, console_errors,
                                                                dashboard_url):
    """`attention()` returns the feeds and the caveats from ONE call so a template cannot
    render the lists and drop the sentences. This asserts the template honoured that."""
    page.goto(f"{dashboard_url}/?tab=attention", wait_until="load")
    expect(page.locator(".attention-pane h2")).to_contain_text("Attention")
    headings = page.locator(".attention-pane h3").all_inner_texts()
    for feed in ("Publication", "Process", "Decisions", "Parked"):
        assert any(feed in h for h in headings), f"{feed} feed missing: {headings}"
    assert page.locator(".attention-pane .flow-caveats li").count() >= 1, (
        "Attention rendered its feeds without its caveats — the one thing the module's "
        "single-return-value design exists to prevent")
    assert console_errors == [], console_errors


@pytest.mark.e2e
def test_loops_states_its_attribution_limit_on_its_face(page, console_errors, dashboard_url):
    """ADR-012's narrowed risk, asserted where a reader sees it.

    Activity is keyed by timestamp and carries no goal id, so it is harness-wide and NOT
    attributable to a loop. A pane implying otherwise would be absence-rendered-as-success
    in a new location, so the limit ships on the face of the pane.
    """
    page.goto(f"{dashboard_url}/?tab=loops", wait_until="load")
    expect(page.locator(".loops-pane h2")).to_contain_text("Loops")
    # ⚠️ Keyed on the limit's OWN class, not on "the first note on the pane". The first
    # draft used `.loops-note` and matched the armed-state sentence instead — it would
    # have gone green with the attribution limit missing entirely.
    note = page.locator(".loops-pane .loops-attribution-limit")
    expect(note).to_be_visible()
    assert "attribut" in note.inner_text().lower(), (
        "the Loops pane does not state its attribution limit where a reader sees it")
    assert console_errors == [], console_errors


@pytest.mark.e2e
@pytest.mark.parametrize("tab", ["flow", "attention", "loops"])
def test_each_pane_is_reachable_from_the_tab_bar(page, dashboard_url, tab):
    """SEAM GUARD. Every assertion above navigates by URL, so all four would still pass if
    the tab links were never added and the panes were reachable only by typing a query
    string. Clicking is what proves an operator can get there."""
    page.goto(dashboard_url, wait_until="load")
    page.locator(f".tabs a[href='?tab={tab}']").click()
    page.wait_for_load_state("load")
    expect(page.locator(f"[data-partial='{tab}_tab']")).to_be_visible()
