"""Tests for the web-egress guard (scripts/harness_web_egress_guard.py).

Covers: domain whitelist (allow primaries, allow subdomains, block look-alikes,
block off-whitelist), denylist scan (absolute paths from the committed baseline,
operator/private literals from a monkeypatched local file), non-web passthrough,
and the fail-closed exception path.
"""
import importlib.util
import pathlib

_SCRIPTS = pathlib.Path(__file__).resolve().parent.parent / "scripts"


def _load():
    spec = importlib.util.spec_from_file_location(
        "web_egress_guard", _SCRIPTS / "harness_web_egress_guard.py"
    )
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


guard = _load()


# --- domain whitelist ---

def test_allows_primary_fetch():
    ev = {"tool_name": "WebFetch",
          "tool_input": {"url": "https://arxiv.org/abs/1234.5678", "prompt": "summarize"}}
    assert guard.evaluate(ev) is None


def test_allows_subdomain_of_whitelist():
    assert guard._host_allowed("export.arxiv.org")
    assert guard._host_allowed("arxiv.org")
    assert guard._host_allowed("ARXIV.ORG")


def test_blocks_lookalike_domains():
    assert not guard._host_allowed("arxiv.org.evil.com")
    assert not guard._host_allowed("notarxiv.org")
    assert not guard._host_allowed("")


def test_blocks_offwhitelist_fetch():
    ev = {"tool_name": "WebFetch", "tool_input": {"url": "https://evil.example.com/x"}}
    r = guard.evaluate(ev)
    assert r is not None and "non-whitelisted domain" in r


# --- denylist scan ---

def test_blocks_absolute_path_in_search():
    ev = {"tool_name": "WebSearch",
          "tool_input": {"query": "why does /Users/someone/proj/file.lean fail to build"}}
    r = guard.evaluate(ev)
    assert r is not None and "absolute local path" in r


def test_allows_clean_search():
    ev = {"tool_name": "WebSearch",
          "tool_input": {"query": "Kato L3 Navier-Stokes local well-posedness"}}
    assert guard.evaluate(ev) is None


def test_local_literal_is_denied(tmp_path, monkeypatch):
    # A fixture local denylist with a fake sensitive literal — no real secret committed.
    local = tmp_path / "research_egress_denylist.txt"
    local.write_text("# --- firewall identifier ---\nFAKESECRETCODENAME\n", encoding="utf-8")
    monkeypatch.setattr(guard, "_LOCAL", str(local))
    ev = {"tool_name": "WebSearch",
          "tool_input": {"query": "specs of the FAKESECRETCODENAME module"}}
    r = guard.evaluate(ev)
    assert r is not None and "firewall identifier" in r


# --- passthrough + fail-closed ---

def test_ignores_non_web_tools():
    # The guard only governs web tools; a /Users/ path in a Read is none of its business.
    assert guard.evaluate({"tool_name": "Read",
                           "tool_input": {"file_path": "/Users/x/y.txt"}}) is None


def test_main_fails_closed_on_bad_stdin(monkeypatch, capsys):
    import io
    monkeypatch.setattr("sys.stdin", io.StringIO("{ this is not json"))
    rc = guard.main()
    out = capsys.readouterr().out
    assert rc == 0
    assert '"permissionDecision": "deny"' in out
    assert "failing closed" in out
