"""Phase 3 — Paper Provenance tab: the sentence-level chain-of-backing inspector
(Datastar SSE). All journeys use the independent disposable dummy-paper server."""
from __future__ import annotations

import pytest
import json
from playwright.sync_api import expect


@pytest.mark.e2e
def test_paper_selector_present(page, dummy_paper_dashboard, dummy_paper_network):
    dashboard_url = dummy_paper_dashboard["url"]
    page.goto(f"{dashboard_url}/?tab=paper", wait_until="load")
    sel = page.locator("#pp-wrap select").first
    expect(sel).to_be_visible()
    assert sel.locator("option").count() > 10


@pytest.mark.e2e
def test_selecting_paper_loads_prose(page, console_errors, dummy_paper_dashboard, dummy_paper_network):
    dashboard_url = dummy_paper_dashboard["url"]
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


@pytest.mark.e2e
def test_sentence_controls_persist_only_to_dummy_papers(
        page, console_errors, dummy_paper_dashboard, dummy_paper_network):
    fixture = dummy_paper_dashboard
    url, root = fixture["url"], fixture["root"]
    sid = fixture["sentences"]["paper_a"]
    other_sid = fixture["sentences"]["paper_b"]
    a, b = root / "papers" / "paper_a", root / "papers" / "paper_b"
    original_b = (b / "prose_state.json").read_bytes()
    outside = root / "outside_claims.json"
    outside_before = outside.read_bytes()
    page.goto(url + "/?tab=paper&paper=paper_a", wait_until="load")
    expect(page.locator("#pp-paper-body .pp-sentence")).to_have_count(1)
    page.locator("#pp-paper-body .pp-sentence").click()
    expect(page.locator("#pp-sentence-inspector .pp-state-btn")).to_have_count(4)

    writes = 0

    def verify(action, state):
        nonlocal writes
        with page.expect_response(lambda response: response.request.method == "POST"
                                  and response.url.endswith("/verify")) as pending:
            action()
        response = pending.value
        assert response.status == 200
        assert response.request.post_data_json == {"state": state, "actor": "user:dashboard"}
        assert response.json()["ok"] is True
        expect(page.locator(f"#pp-paper-body .pp-sentence--{state}")).to_be_visible()
        saved = json.loads((a / "prose_state.json").read_text())
        assert saved["sentences"][sid]["human_state"] == "human_" + state
        assert not (a / "prose_state.json").is_symlink()
        assert (b / "prose_state.json").read_bytes() == original_b
        writes += 1
        audit = [json.loads(line) for line in (a / "audit_log.jsonl").read_text().splitlines()]
        assert len(audit) == writes
        assert audit[-1]["meta"]["target_id"] == sid
        assert audit[-1]["meta"]["new_state"] == "human_" + state

    for state in ("verified", "interpretive", "needs_fix", "needs_recheck"):
        verify(lambda state=state: page.locator(f".pp-state-btn--{state}").click(), state)
    for key, state in (("v", "verified"), ("i", "interpretive"), ("r", "needs_recheck")):
        expect(page.locator("#pp-paper-body .pp-sentence--active")).to_be_visible()
        verify(lambda key=key: page.keyboard.press(key), state)

    page.once("dialog", lambda dialog: dialog.accept("verified"))
    with page.expect_response(lambda response: response.request.method == "POST"
                              and response.url.endswith("/propagate")) as pending:
        page.locator(".pp-cluster-banner__btn").click()
    propagated = pending.value
    assert propagated.status == 200
    assert propagated.request.post_data_json == {
        "state": "verified", "source_sentence": sid, "actor": "user:dashboard"}
    assert propagated.json()["propagated_count"] == 1
    assert propagated.json()["failed_count"] == 0
    other = json.loads((b / "prose_state.json").read_text())
    assert other["sentences"][other_sid]["human_state"] == "human_verified"
    assert len((b / "audit_log.jsonl").read_text().splitlines()) == 1
    assert len((a / "audit_log.jsonl").read_text().splitlines()) == 7
    page.reload(wait_until="load")
    expect(page.locator("#pp-paper-body .pp-sentence--needs_recheck")).to_be_visible()

    unsafe = page.request.get(url + "/api/papers/paper_unsafe/provenance")
    assert unsafe.status == 404 and "OUTSIDE_DUMMY_MARKER" not in unsafe.text()
    escaped_sid = fixture["sentences"]["paper_escape"]
    refused = page.request.post(url + f"/api/papers/paper_escape/sentences/{escaped_sid}/verify",
                                data={"state": "verified", "actor": "user:dummy_browser"})
    assert refused.status == 400
    assert "prerequisite" in refused.json()["stderr"]
    assert outside.read_bytes() == outside_before
    escaped = root / "papers" / "paper_escape"
    assert (escaped / "audit_log.jsonl").read_bytes() == b""
    assert not list(escaped.glob("*.lock"))
    assert console_errors == [], console_errors
