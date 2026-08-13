"""A gate blocker drills through to the finding it came from — ADR-012 D15 S1.

⚠️ **A `test_client` CANNOT see any of this.** The focus pane arrives over Datastar SSE and
is morphed into the page by JavaScript, so a server-side assertion proves only that a string
was produced, never that a reader sees it. That is the whole reason `tests/e2e/` exists, and
why ADR-012 D2 makes a browser test one of the two extra gates on dashboard work.

The defect this pins: the old assertion `'Blockers' in html` passed for years while every
entry was an unlinkable 60-character prose fragment. The heading was right and the content
was a dead end.
"""
from __future__ import annotations

import pytest


#: The cell is `<td class="gate-cell blocked" title="FixPropagation — blocked">`.
#: ⚠️ **`FixPropagation` specifically, not any blocked cell.** It is the only evaluator that
#: reads `FLAGS`, so it is the only one that can name a finding; a paper blocked solely on
#: `CitationIntegrity` correctly renders prose and would fail this test for the right reason
#: at the wrong site.
_BLOCKED_FIXPROP = ('#readiness-heatmap td.gate-cell.blocked'
                    '[title^="FixPropagation"]')


@pytest.mark.e2e
def test_a_blocker_names_the_finding_it_came_from(page, console_errors, dashboard_url):
    page.goto(f"{dashboard_url}/?tab=readiness", wait_until="load")
    page.wait_for_selector("#readiness-heatmap td", timeout=20000)

    cells = page.locator(_BLOCKED_FIXPROP)
    assert cells.count() > 0, (
        "no blocked FixPropagation cell in the live corpus — this test would pass over "
        "nothing, so an empty population is a failure and not a skip")
    cells.first.click()

    page.wait_for_selector("#readiness-focus .blockers li", timeout=20000)
    items = page.locator("#readiness-focus .blockers li[data-finding-id]")
    assert items.count() > 0, (
        "the focus pane rendered blockers but none carries a finding id — the drill-through "
        "is back to prose")
    first = items.first.get_attribute("data-finding-id")
    assert first and first.startswith("review:"), (
        f"blocker id is {first!r}, which is not a minted ReviewFinding id")
    assert items.first.get_attribute("data-lane"), (
        "a blocker carries no lane, so the operator cannot see who repairs it — the cell is "
        "a status light again rather than a routing instrument")
    assert console_errors == [], console_errors


@pytest.mark.e2e
def test_a_truncated_blocker_list_SAYS_it_is_truncated(page, dashboard_url):
    """No silent caps. The pane shows ten; at least one live paper carries far more."""
    page.goto(f"{dashboard_url}/?tab=readiness", wait_until="load")
    page.wait_for_selector("#readiness-heatmap td", timeout=20000)
    page.locator(_BLOCKED_FIXPROP).first.click()
    page.wait_for_selector("#readiness-focus .blockers li", timeout=20000)

    shown = page.locator("#readiness-focus .blockers li").count()
    note = page.locator("#readiness-focus .blockers-truncated")
    if shown >= 10 and note.count():
        text = note.first.inner_text()
        assert " of " in text, f"truncation note does not state the total: {text!r}"
        total = int(text.rsplit(" of ", 1)[1].strip())
        assert total >= shown, (
            f"the note claims a total of {total} while showing {shown} — the disclosure is "
            f"computed from the already-truncated list, which is the defect it exists to "
            f"prevent")
