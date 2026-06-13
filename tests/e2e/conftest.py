"""Live-server + chromium fixtures for the provenance-dashboard e2e suite.

These tests boot the REAL Flask dashboard as a subprocess on an ephemeral port
(the same code path `uv run python scripts/provenance_dashboard.py` runs, including
the startup graph prewarm) and drive it in a real chromium browser via Playwright's
sync API. A server-side `test_client` can never catch Datastar / SSE / data-on JS
regressions — only a real browser can. See workspace memory
`feedback-test-client-never-runs-js`.

Skips LOUDLY when Playwright or chromium are unavailable:
    uv run playwright install chromium

All tests here are marked `e2e` (registered in pyproject.toml) and are excluded
from the default `uv run pytest` run; invoke them with `-m e2e`.
"""
from __future__ import annotations

import socket
import subprocess
import sys
import tempfile
import time
import urllib.request
from pathlib import Path

import pytest

sync_api = pytest.importorskip("playwright.sync_api")

# tests/e2e/conftest.py -> parents[2] == SK_EFT_Hawking/
PROJECT_ROOT = Path(__file__).resolve().parents[2]
DASHBOARD = PROJECT_ROOT / "scripts" / "provenance_dashboard.py"


def _free_port() -> int:
    """Bind :0 to let the OS hand us an unused localhost port, then release it."""
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


def _wait_until_up(url: str, proc: "subprocess.Popen", log_path: Path,
                   timeout: float = 180.0) -> None:
    """Poll ``url`` until it answers 200. The first GET blocks on the ~15-20s
    graph build, so the per-request timeout is generous. Raises with the server
    log tail if the process dies during boot."""
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        if proc.poll() is not None:
            tail = "\n".join(
                log_path.read_text(errors="replace").splitlines()[-30:]
            )
            raise RuntimeError(
                f"dashboard exited early (code {proc.returncode}).\n"
                f"--- server log tail ---\n{tail}"
            )
        try:
            with urllib.request.urlopen(url, timeout=30) as resp:
                if resp.status == 200:
                    return
        except Exception:
            time.sleep(0.5)
    raise TimeoutError(f"dashboard not up at {url} within {timeout}s")


@pytest.fixture(scope="session")
def dashboard_url():
    """Session-scoped live public dashboard on an ephemeral port.

    Boots once per test session (the graph build is expensive). Uses
    ``--no-browser`` (don't pop a real browser tab) and ``--no-pg-sync``
    (don't mutate the Postgres mirror during tests).
    """
    port = _free_port()
    log_path = Path(tempfile.gettempdir()) / f"dash_e2e_{port}.log"
    log = log_path.open("w")
    proc = subprocess.Popen(
        [sys.executable, str(DASHBOARD), "--port", str(port),
         "--no-browser", "--no-pg-sync"],
        cwd=str(PROJECT_ROOT),
        stdout=log,
        stderr=subprocess.STDOUT,
    )
    url = f"http://127.0.0.1:{port}"
    try:
        _wait_until_up(url + "/", proc, log_path)
        yield url
    finally:
        proc.terminate()
        try:
            proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            proc.kill()
        log.close()


@pytest.fixture(scope="session")
def _browser():
    """Session-scoped headless chromium. Skips the whole suite (loudly) if the
    browser build is missing rather than erroring per-test."""
    with sync_api.sync_playwright() as p:
        try:
            browser = p.chromium.launch()
        except Exception as exc:  # chromium build not installed
            pytest.skip(
                f"chromium unavailable ({exc}); run "
                f"`uv run playwright install chromium`."
            )
        try:
            yield browser
        finally:
            browser.close()


@pytest.fixture
def page(_browser):
    """Per-test isolated browser context + page (fresh cookies/storage)."""
    context = _browser.new_context()
    pg = context.new_page()
    try:
        yield pg
    finally:
        context.close()


@pytest.fixture
def console_errors(page):
    """Collects console-error + uncaught-pageerror strings for the test's page.

    Depends on ``page`` so the listeners attach before the test navigates.
    Returns a live list the test can assert on after driving the page.
    """
    errors: list[str] = []
    page.on(
        "console",
        lambda m: errors.append(f"{m.type}: {m.text}") if m.type == "error" else None,
    )
    page.on("pageerror", lambda e: errors.append(f"pageerror: {e}"))
    return errors
