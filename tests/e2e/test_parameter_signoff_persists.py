"""The confirmed parameter is still confirmed after a reload — ADR-012 P9a Task 5.

⚠️ **THE DEFECT, STATED AS A TEST.** The green badge and the *persisted* green badge are
the same markup. Nothing rendered on the page distinguishes them, and no `test_client`
assertion can either — a server-side check sees the fragment the route returned, which was
always green. **Reloading is the only way to tell them apart**, which is why this case is
here and not in `tests/test_provenance_writer.py`.

⚠️ **THIS TEST WRITES TO A TRACKED FILE**, because that is the thing under test:
`src/core/provenance.py` is the registry the writer edits in place. It therefore refuses to
run if that file already has uncommitted changes — it must never be the thing that
clobbers work in progress — and restores the original in a `finally`, asserting the restore
succeeded rather than assuming it.
"""
from __future__ import annotations

import re
import time
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent.parent
PROV = ROOT / "src" / "core" / "provenance.py"


def _first_unverified(src: str) -> str | None:
    for m in re.finditer(r"(?m)^    '([A-Za-z0-9_.+-]+)': \{", src):
        start = m.end()
        end = src.find("\n    },", start)
        if end != -1 and "'human_verified_date': None," in src[start:end]:
            return m.group(1)
    return None


@pytest.mark.e2e
def test_a_confirmed_parameter_is_still_confirmed_after_reload(page, dashboard_url):
    # ⚠️ THE DIRTY-CHECK MOVED TO AN AUTOUSE FIXTURE, AND IT NOW FAILS RATHER THAN SKIPS.
    # This test used to skip on a dirty registry — and `test_parameters_tab.py` reliably
    # dirtied it a moment later, so the branch's flagship persistence proof silently
    # disabled itself on every run after the first. `tests/e2e/conftest.py` guards every
    # e2e test now, because ANY of them can reach `/verify`.
    #
    # ⚠️ THE CRASH-SAFE RESTORE IS THE AUTOUSE FIXTURE'S, NOT THIS `finally`'s. The
    # conftest guard journals `src/core/provenance.py` to `.seed-journal/` before this
    # test starts, so a kill here is repaired by the next pytest run. The local
    # `try/finally` is kept as the in-process fast path and for its assertion message;
    # it is no longer the only copy of the information needed to undo the write.
    original = PROV.read_text(encoding="utf-8")
    key = _first_unverified(original)
    assert key, ("every parameter is already human-verified — this test would pass over "
                 "nothing, so it is a failure and not a skip")

    try:
        page.goto(f"{dashboard_url}/?tab=parameters", wait_until="load")
        page.wait_for_selector(".param-card", timeout=20000)

        # Confirm through the real UI path, not by calling the route.
        card = page.locator(f'.param-card:has-text("{key}")').first
        card.scroll_into_view_if_needed()
        card.locator('button:has-text("Confirm")').first.click()

        # ⚠️ POLL, DO NOT SLEEP. The dashboard is a SEPARATE SUBPROCESS, so the write is
        # asynchronous to this test. A fixed `wait_for_timeout(1500)` raced it two ways on a
        # loaded machine: the assertion could fire before `os.replace` landed, AND the
        # `finally` could then restore while the server was still writing — leaving the tree
        # dirty by the very path written to prevent that.
        after = original
        deadline = time.monotonic() + 30
        while time.monotonic() < deadline:
            after = PROV.read_text(encoding="utf-8")
            if after != original:
                break
            time.sleep(0.25)

        # ⚠️ THE ASSERTION THAT MATTERS: the FILE changed. Reading the page here would
        # pass against the old in-memory-only behaviour.
        assert after != original, (
            "the confirm button rendered its badge and wrote nothing within 30s — the "
            "in-memory-only path is back, and the badge is indistinguishable from a "
            "persisted one")
        # Let any in-flight replace settle before the `finally` restores over it.
        time.sleep(0.5)
        assert f"'{key}'" in after
        start = after.index(f"    '{key}': {{")
        entry = after[start:after.index("\n    },", start)]
        assert "'human_verified_date': None," not in entry, (
            f"{key}'s date is still None after a confirm that reported success")

        # …and it survives a reload, which is what a human would do to check.
        page.reload(wait_until="load")
        page.wait_for_selector(".param-card", timeout=20000)
        assert PROV.read_text(encoding="utf-8") == after
    finally:
        PROV.write_text(original, encoding="utf-8")
        assert PROV.read_text(encoding="utf-8") == original, (
            "FAILED TO RESTORE src/core/provenance.py — restore it from git before "
            "continuing")
