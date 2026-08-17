"""The plugin bind/refresh lifecycle — `scripts/plugin_lifecycle.py`.

The defect these guard against: a session binds its plugin at process start, so guidance
committed afterwards is inert until a sync AND a restart. The predecessor keyed its
uncommitted-source check on ONE file (the egress guard), which passes for every edit outside it
and then silently skips that edit during the refresh it was meant to block.
"""

import importlib.util
import subprocess
from pathlib import Path

import pytest

SCRIPTS = Path(__file__).resolve().parent.parent / "scripts"


def _load():
    spec = importlib.util.spec_from_file_location("plugin_lifecycle", SCRIPTS / "plugin_lifecycle.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


@pytest.fixture
def pl():
    return _load()


def _git(repo, *args):
    subprocess.run(["git", *args], cwd=repo, check=True, capture_output=True)


@pytest.fixture
def fake_repo(tmp_path, pl, monkeypatch):
    """A repo with a plugin tree, so 'uncommitted' is a real git state and not a mock."""
    repo = tmp_path / "repo"
    plugin = repo / ".claude" / "plugins" / "skeft-qa" / "agents"
    plugin.mkdir(parents=True)
    (plugin / "lean-worker.md").write_text("v1\n")
    # the file the egress-scoped predecessor keyed its check on — present, so a narrowed
    # decider is WELL-DEFINED here and reports clean, which is the defect being guarded.
    guard = repo / ".claude" / "plugins" / "skeft-qa" / "scripts"
    guard.mkdir(parents=True)
    (guard / "harness_web_egress_guard.py").write_text("_WHITELIST = {}\n")
    (repo / "unrelated.py").write_text("x = 1\n")
    _git(repo, "init", "-q")
    _git(repo, "config", "user.email", "t@t")
    _git(repo, "config", "user.name", "t")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "initial")
    monkeypatch.setattr(pl, "REPO", repo)
    monkeypatch.setattr(pl, "PLUGIN_SRC", repo / ".claude" / "plugins" / "skeft-qa")
    monkeypatch.setattr(pl, "DELTA_DOC", repo / "docs" / "dev-loops" / "PLUGIN_DELTA.md")
    return repo


def test_sync_refuses_when_ANY_plugin_file_is_uncommitted(fake_repo, pl, monkeypatch, capsys):
    """The decider is the whole plugin tree — not one chosen file.

    An edit to an agent definition must block the refresh. Keyed on a single guard file, this
    passes and the edit is then skipped by the very refresh that reported success.
    """
    (fake_repo / ".claude/plugins/skeft-qa/agents/lean-worker.md").write_text("v2 — uncommitted\n")
    called = []
    monkeypatch.setattr(pl, "_install_records", lambda: called.append("records") or [fake_repo])

    rc = pl.cmd_sync(None)

    assert rc == 1, "an uncommitted agent edit must block the refresh"
    assert "REFUSING" in capsys.readouterr().out
    assert not called, "sync must not touch install records after refusing"


def test_sync_is_not_blocked_by_an_unrelated_uncommitted_file(fake_repo, pl, monkeypatch):
    """Non-vacuity: the guard must be scoped to the plugin, not to 'the repo is dirty'."""
    (fake_repo / "unrelated.py").write_text("x = 2\n")
    monkeypatch.setattr(pl, "_install_records", lambda: [])

    assert pl.cmd_sync(None) == 0, "a dirty file outside the plugin must not block a refresh"


def test_delta_is_empty_when_the_bound_cache_is_current(fake_repo, pl, monkeypatch, capsys):
    head = pl._plugin_head()
    monkeypatch.setattr(pl, "_bound_shas", lambda: {"/p": head[:12]})
    pl.DELTA_DOC.parent.mkdir(parents=True, exist_ok=True)
    pl.DELTA_DOC.write_text("stale content from an earlier run\n")

    rc = pl.cmd_delta(None)

    assert rc == 0
    assert "No delta" in capsys.readouterr().out
    assert not pl.DELTA_DOC.exists(), "a current cache must clear the doc, not leave it stale"


def test_delta_separates_amendable_components_from_bind_at_start_files(fake_repo, pl, monkeypatch):
    """A citation can amend an agent's prompt. It cannot reach a script the plugin executes."""
    bound = pl._plugin_head()
    (fake_repo / ".claude/plugins/skeft-qa/agents/lean-worker.md").write_text("v2 — the new rule\n")
    scripts_dir = fake_repo / ".claude/plugins/skeft-qa/scripts"
    scripts_dir.mkdir(parents=True, exist_ok=True)
    (scripts_dir / "notebook_lib.py").write_text("# fixed resolver\n")
    _git(fake_repo, "add", "-A")
    _git(fake_repo, "commit", "-qm", "plugin changes")
    monkeypatch.setattr(pl, "_bound_shas", lambda: {"/p": bound[:12]})

    rc = pl.cmd_delta(None)

    assert rc == 1, "a real delta must report non-zero so a caller can branch on it"
    body = pl.DELTA_DOC.read_text()
    assert "v2 — the new rule" in body, "an amendable agent's CURRENT TEXT must be rendered"
    assert "Not amendable" in body and "notebook_lib.py" in body, (
        "a script that binds at process start must be named as unreachable by citation, "
        "not silently rendered as if a brief could deliver it"
    )
    assert "# fixed resolver" not in body, "a bind-at-start file's body must not be rendered"
