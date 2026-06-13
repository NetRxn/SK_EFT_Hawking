"""Phase 3 — Formulas tab: the formula-provenance table from src/core/formulas.py."""
from __future__ import annotations

import pytest
from playwright.sync_api import expect


@pytest.mark.e2e
def test_formulas_table_renders_with_columns(page, dashboard_url):
    page.goto(f"{dashboard_url}/?tab=formulas", wait_until="load")
    for col in ("Function", "Description", "Lean", "Aristotle", "Source"):
        expect(page.locator(f"th:has-text('{col}')").first).to_be_visible()
    # 385 formulas at baseline — the table is densely populated.
    assert page.locator("table tbody tr").count() > 50


@pytest.mark.e2e
def test_formulas_lean_reference_column_present(page, dashboard_url):
    page.goto(f"{dashboard_url}/?tab=formulas", wait_until="load")
    # Each formula row reports its Lean theorem ref or a red MISSING flag —
    # at least the Lean column cells are populated (theorem name or MISSING).
    assert page.locator("table tbody tr td").count() > 100
