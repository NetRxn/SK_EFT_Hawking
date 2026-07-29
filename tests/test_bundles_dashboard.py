"""Dependency-free contract guards for the Bundles tab.

These run in the DEFAULT pytest suite (no browser, no live server), so a
regression is caught even where chromium is unavailable. They complement the
real-browser journey in tests/e2e/test_bundles_tab.py. Pairing a JS/template
feature with an always-on guard is the lesson of workspace memory
`feedback-test-client-never-runs-js`.
"""
from __future__ import annotations

import re
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


def test_template_hardcodes_no_roster_count():
    """The template must not bake a roster count into its prose.

    It has gone stale three times (13 -> 18 -> 19) because two different numbers
    get conflated: the AUTHORIZED roster in PAPER_STRATEGY.md (21 as of the
    2026-07-27 D12 authorization) and the SCAFFOLDED bundles that
    PAPER_DRAFT_MAPPING.md yields (19 — D11/D12 scaffolding is deferred to first
    content-lift). The heading renders the live count from the loader instead.
    """
    stale = re.findall(r"\b\d+\s+publication targets\b", BUNDLES_TPL)
    assert stale == [], f"template hardcodes a roster count: {stale}"


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


def test_load_bundles_summary_matches_mapping_doc():
    """The rendered roster is exactly what PAPER_DRAFT_MAPPING.md assigns.

    Derived rather than pinned to a literal: authorizing or lifting a bundle
    should not fail an unrelated count assertion (which is how the e2e test
    ended up asserting 18 while this file asserted 19).
    """
    from bundle_migration import parse_mapping
    from bundle_readiness import aggregate_by_bundle, load_findings_by_paper
    from datastar_bundles import MAPPING_DOC, load_bundles_summary

    expected = set(aggregate_by_bundle(
        parse_mapping(MAPPING_DOC.read_text()), load_findings_by_paper()))

    summary = load_bundles_summary()
    codes = {b["code"] for b in summary["bundles"]}
    assert codes == expected
    assert summary["total_bundles"] == len(expected)
    for b in summary["bundles"]:
        assert "readiness_display" in b, b["code"]


def test_every_rendered_bundle_has_a_title():
    """D10 shipped into the mapping and _TIER_OF but never into _BUNDLE_TITLES,
    so it rendered with a BLANK title cell for weeks. The lookup is a `.get`
    default, so nothing failed loudly."""
    from datastar_bundles import load_bundles_summary

    blank = [b["code"] for b in load_bundles_summary()["bundles"] if not b["title"]]
    assert blank == [], f"bundles rendering with an empty title: {blank}"


def test_authorized_roster_is_registered_even_before_scaffolding():
    """Every bundle authorized in PAPER_STRATEGY.md must carry tier + title
    metadata BEFORE its papers/<code>/ directory is scaffolded — otherwise the
    tab breaks (or renders blank) on the day of first content-lift."""
    from datastar_bundles import _BUNDLE_TITLES, _TIER_OF

    strategy = (PROJECT_ROOT / "docs" / "PAPER_STRATEGY.md").read_text()
    # Authorized deep papers are announced as "**Paper D<n>: <title>**".
    authorized = set(re.findall(r"\*\*Paper (D\d+):", strategy))
    assert authorized, "no authorized deep papers parsed from PAPER_STRATEGY.md"

    missing_tier = sorted(authorized - set(_TIER_OF))
    missing_title = sorted(authorized - set(_BUNDLE_TITLES))
    assert missing_tier == [], f"authorized but no tier: {missing_tier}"
    assert missing_title == [], f"authorized but no title: {missing_title}"


def test_deep_papers_sort_numerically_not_lexicographically():
    """D10 sorted between D1 and D2 under the old plain-string key."""
    from datastar_bundles import _bundle_sort_key

    codes = ["D1", "D10", "D2", "D9", "D11", "D12"]
    assert sorted(codes, key=_bundle_sort_key) == [
        "D1", "D2", "D9", "D10", "D11", "D12"]
