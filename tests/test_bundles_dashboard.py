"""Dependency-free contract guards for the Bundles tab.

These run in the DEFAULT pytest suite (no browser, no live server), so a
regression is caught even where chromium is unavailable. They complement the
real-browser journey in tests/e2e/test_bundles_tab.py. Pairing a JS/template
feature with an always-on guard is the lesson of workspace memory
`feedback-test-client-never-runs-js`.
"""
from __future__ import annotations

import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "scripts"))

BUNDLES_TPL = (PROJECT_ROOT / "scripts" / "templates" / "partials" / "bundles_tab.html").read_text()
DASHBOARD_TPL = (PROJECT_ROOT / "scripts" / "templates" / "dashboard.html").read_text()


def test_companion_strategy_link_not_claude_code_repo():
    # Was hard-coded to github.com/anthropics/claude-code (copy-paste bug).
    assert "github.com/anthropics/claude-code" not in BUNDLES_TPL


def test_favicon_declared_in_head():
    # Declaring an icon stops the browser 404-ing on /favicon.ico every load.
    assert 'rel="icon"' in DASHBOARD_TPL


def test_bundle_comment_count_current():
    assert "13 publication targets" not in BUNDLES_TPL
    assert "18 publication targets" in BUNDLES_TPL


def test_submission_form_present_and_posts_to_form_route():
    assert 'class="submission-form"' in BUNDLES_TPL
    assert 'action="/bundles/submission_event"' in BUNDLES_TPL
    assert 'method="post"' in BUNDLES_TPL


def test_submission_inputs_are_not_two_way_bound():
    # Footgun from `feedback-test-client-never-runs-js`: two-way Datastar
    # data-bind on plain inputs collapses signals / coerces values. The form
    # must use plain inputs + a classic POST.
    assert "data-bind" not in BUNDLES_TPL


def test_loader_error_is_surfaced_not_silent():
    # The zeroed-fallback dict carries an `error` key; the template must render it.
    assert "bundles_summary.error" in BUNDLES_TPL


def test_readiness_display_surfaced():
    assert "b.readiness_display" in BUNDLES_TPL


def test_load_bundles_summary_has_18_bundles_with_display():
    from datastar_bundles import load_bundles_summary

    summary = load_bundles_summary()
    assert summary["total_bundles"] == 18
    codes = {b["code"] for b in summary["bundles"]}
    assert {"F", "D1", "D9", "L1", "L3", "I1", "I3", "E1", "E2"} <= codes
    for b in summary["bundles"]:
        assert "readiness_display" in b, b["code"]
