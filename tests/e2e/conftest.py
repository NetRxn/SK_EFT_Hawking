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
import os
import json
import hashlib
import uuid
import shutil
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
        env={**os.environ, 'SK_EFT_GRAPH_SOURCE': 'json'},
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
def dummy_paper_evidence(request):
    """Capture evidence outside pytest retention, before fixture cleanup."""
    archive = (PROJECT_ROOT / "outputs" / "continuity" /
               "round54-dashboard-four-sse-guarded-fixtures-r1" / "browser-runs" / uuid.uuid4().hex)
    archive.mkdir(parents=True, exist_ok=False)
    sources = ["tests/e2e/conftest.py", "tests/e2e/dummy_paper_server.py",
               "tests/e2e/test_paper_provenance_tab.py", "scripts/datastar_helpers.py",
               "scripts/provenance_dashboard.py", "scripts/templates/partials/paper_provenance_tab.html"]
    source_hashes = {name: hashlib.sha256((PROJECT_ROOT / name).read_bytes()).hexdigest()
                     for name in sources}
    try:
        yield archive
    finally:
        files = {path.name: {"sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                             "bytes": path.stat().st_size}
                 for path in archive.iterdir() if path.is_file()}
        with (archive / "manifest.json").open("x") as out:
            json.dump({"test": request.node.nodeid, "source": source_hashes, "files": files}, out, indent=2)
            out.write("\n")
        print("Durable dummy evidence archive:", archive)


@pytest.fixture
def dummy_paper_network(page, dummy_paper_evidence):
    """Preserve actual dummy-browser request/response/finish evidence."""
    pg = page
    network = []
    journal = dummy_paper_evidence / "browser-network.jsonl"
    journal.touch(exist_ok=False)
    started = time.monotonic()
    def observe(kind, value):
        network.append({"at": time.monotonic() - started, "kind": kind,
                        "url": value.url,
                        "method": value.method if kind != "response" else value.request.method,
                        "headers": value.headers,
                        "status": value.status if kind == "response" else None})
        with journal.open("a") as out:
            out.write(json.dumps(network[-1]) + "\n")
    subscriptions = []
    for kind in ("request", "response", "requestfinished", "requestfailed"):
        handler = lambda value, kind=kind: observe(kind, value)
        pg.on(kind, handler)
        subscriptions.append((kind, handler))
    try:
        yield network
    finally:
        for kind, handler in subscriptions:
            pg.remove_listener(kind, handler)
        with (dummy_paper_evidence / "browser-network.json").open("x") as out:
            json.dump(network, out, indent=2)
            out.write("\n")
        print("Browser network evidence:", dummy_paper_evidence / "browser-network.json")


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


@pytest.fixture
def dummy_paper_dashboard(tmp_path, monkeypatch, dummy_paper_evidence):
    """Real CLI/server with disposable papers; no production corpus or database."""
    monkeypatch.syspath_prepend(str(PROJECT_ROOT / "scripts"))
    from test_helpers import make_v2_review, make_v2_sentence

    root = tmp_path.resolve()
    papers = root / "papers"
    papers.mkdir()
    (root / "docs").mkdir()
    (root / "lean" / "SKEFTHawking").mkdir(parents=True)
    shutil.copytree(PROJECT_ROOT / "src", root / "src",
                    ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
    (root / "scripts").mkdir()
    shutil.copy2(PROJECT_ROOT / "scripts" / "review_figures.py",
                 root / "scripts" / "review_figures.py")
    quote = "This disposable sentence tests verification controls without claiming a scientific result."
    sentences = {}
    # More than ten real selector entries and a full >50-cell readiness matrix
    # are supplied as disposable data, rather than lowering the browser assertions.
    names = ("paper_a", "paper_b", "paper_escape", "D1") + tuple(
        f"fixture_{i}" for i in range(9))
    for name in names:
        paper = papers / name
        paper.mkdir()
        sentence = make_v2_sentence(name, quote=quote)
        sentences[name] = sentence["id"]
        (paper / "paper_draft.tex").write_text(
            "\\title{Dummy Hawking browser fixture " + name + "}\n\\begin{abstract}\n" + quote
            + "\nA second disposable sentence provides sufficient abstract content.\n\\end{abstract}\n")
        (paper / "claims_review.json").write_text(json.dumps(make_v2_review(name, [sentence])))
        (paper / "prose_state.json").write_text(json.dumps({"paper": name, "sentences": {}}))
        (paper / "audit_log.jsonl").write_text("")
    # The actual graph extractor reads this dummy metadata. It is never a
    # compiled declaration or evidence about the scientific source tree.
    (root / "lean" / "lean_deps.json").write_text(json.dumps([{
        "name": "SKEFTHawking.AcousticMetric.browser_fixture_only",
        "module": "SKEFTHawking.AcousticMetric", "kind": "theorem",
        "type": "True", "axiom_deps_project": [], "axiom_deps_core": [],
        "name_deps_project": [], "name_deps_extracted": True,
        "name_deps_timed_out": False,
    }]))
    reviews = papers / "AutomatedReviews" / "dummy-browser"
    reviews.mkdir(parents=True)
    (reviews / "fixture.md").write_text(
        "---\npaper: D1\nbundle_target: D1\nreview_date: 2026-01-01\n---\n"
        "### 1.1 — Disposable browser finding\n\n"
        "- **Severity:** minor\n- **Lane:** infra\n- **Gate:** FixPropagation\n"
        "- **Location:** papers/D1/paper_draft.tex\n"
        "- **Observed:** Synthetic fixture exercises the actual QI reader.\n")
    (papers / "paper_a" / "prose_state.json").unlink()
    (papers / "paper_a" / "prose_state.json").symlink_to(papers / "paper_b" / "prose_state.json")
    outside_claims = root / "outside_claims.json"
    (papers / "paper_escape" / "claims_review.json").rename(outside_claims)
    (papers / "paper_escape" / "claims_review.json").symlink_to(outside_claims)
    unsafe = papers / "paper_unsafe"
    unsafe.mkdir()
    (root / "outside.tex").write_text("OUTSIDE_DUMMY_MARKER")
    (unsafe / "paper_draft.tex").symlink_to(root / "outside.tex")
    (papers / "claim_clusters.json").write_text(json.dumps({"clusters": [{
        "id": "cluster:dummy-papers", "match_kind": "exact", "confidence": 1.0,
        "members": [sentences["paper_a"], sentences["paper_b"]],
        "member_papers": ["paper_a", "paper_b"], "label": "Disposable matching sentences",
    }]}))
    port = _free_port()
    log_path = root / "dashboard.log"
    with log_path.open("w") as log:
        proc = subprocess.Popen(
            [sys.executable, "-B", str(Path(__file__).with_name("dummy_paper_server.py")),
             str(root), str(port)], cwd=PROJECT_ROOT,
            env={**os.environ, "SK_EFT_GRAPH_SOURCE": "json", "PYTHONDONTWRITEBYTECODE": "1"},
            stdout=log, stderr=subprocess.STDOUT)
        url = f"http://localhost:{port}"
        try:
            _wait_until_up(url + "/api/papers/list", proc, log_path)
            yield {"url": url, "root": root, "sentences": sentences}
        finally:
            proc.terminate()
            try:
                proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)
            # Preserve actual bytes immediately after owned-child join, before
            # tmp_path teardown or any pytest retention cleanup can run.
            log.flush()
            for name in ("server-observations.json", "server-stacks.log", "dashboard.log"):
                if (root / name).exists():
                    with (root / name).open("rb") as src, (dummy_paper_evidence / name).open("xb") as dst:
                        shutil.copyfileobj(src, dst)
            observations = json.loads((root / "server-observations.json").read_text())
            (dummy_paper_evidence / "cleanup.json").write_text(json.dumps({
                "pid": proc.pid, "returncode": proc.returncode,
                "joined": proc.poll() is not None}, indent=2) + "\n")
            print("Dummy paper server root:", root)
            print("Dummy paper server observations:", json.dumps(observations, sort_keys=True))
            print("Dummy paper server stacks:", (root / "server-stacks.log").read_text())
            assert observations["db_connect_attempts"] == 0
            assert observations["violations"] == []
            assert observations["PG_SYNC_ENABLED"] is False
            assert observations["graph_source"] == "json"
            assert observations["server_exit"] is True
            assert proc.returncode == 0


# ═══════════════════════════════════════════════════════════════════════════════════════
# Registry guard — autouse, because a browser test can now WRITE the parameter registry
# ═══════════════════════════════════════════════════════════════════════════════════════

PROVENANCE_PATH = (Path(__file__).resolve().parent.parent.parent
                   / "src" / "core" / "provenance.py")


@pytest.fixture(autouse=True)
def _provenance_registry_guard(request):
    """Restore `src/core/provenance.py` after every e2e test. **Autouse, deliberately.**

    ⚠️ **THIS BECAME NECESSARY THE MOMENT `/verify` STARTED PERSISTING.** `test_parameters_tab
    .py::test_confirm_button_marks_human_verified` has clicked Confirm since Phase 3, guarded
    only by a fixture that restored `docs/verification_log.jsonl`. Once ADR-012 P9a wired
    `set_human_verified` into that route, a green test run began **writing a real
    `human_verified_date` into a tracked file** — manufacturing exactly the evidence the P1
    `ParameterProvenance` gate exists to demand, one `git add` away from being believed.

    ⚠️ **AND IT COMPOUNDED.** `test_parameter_signoff_persists.py` skips when the registry is
    dirty. Collection is alphabetical, so it ran first, restored correctly, and then
    `test_parameters_tab.py` left the file modified — silently disabling the branch's
    flagship persistence proof on every subsequent run. A guard that skips is a guard that
    switches itself off.

    Entering dirty is therefore a **FAILURE**, not a skip: it means a previous run leaked,
    and continuing would let this fixture restore someone else's uncommitted work.

    ⚠️ THE WRITER HERE IS A BROWSER, which is why this uses `journalled` rather than
    `seeded_mutation`: no content is known up front — a Playwright click reaches `/verify`,
    which persists a real `human_verified_date` into this tracked file. Journalling it
    means a killed e2e run leaves a repairable record instead of manufactured provenance
    evidence, one `git add` away from being believed by the P1 `ParameterProvenance` gate.
    """
    if "dummy_paper_dashboard" in request.fixturenames:
        # Guarded journeys cannot reach the real parameter writer. Assert
        # immutability without journalling/restoring an unowned tracked file.
        original = PROVENANCE_PATH.read_bytes()
        yield
        assert PROVENANCE_PATH.read_bytes() == original
        return
    import subprocess
    import sys
    root = PROVENANCE_PATH.parent.parent.parent
    sys.path.insert(0, str(root / "scripts"))
    from seed_journal import journalled
    dirty = subprocess.run(["git", "status", "--porcelain", str(PROVENANCE_PATH)],
                           cwd=root, capture_output=True, text=True).stdout.strip()
    assert not dirty, (
        f"{PROVENANCE_PATH.name} is already modified before this test ran. Either a previous "
        f"e2e run leaked a write, or you have uncommitted work here — restoring it "
        f"afterwards would destroy the latter. Resolve it, then re-run.")
    original = PROVENANCE_PATH.read_text(encoding="utf-8")
    with journalled(PROVENANCE_PATH,
                    reason="an e2e test can reach /verify, which persists a real "
                           "human_verified_date into this tracked registry"):
        yield
    assert PROVENANCE_PATH.read_text(encoding="utf-8") == original
