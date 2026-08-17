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
    # No live session by default — otherwise `_running_shas` reports the REAL session running
    # these tests, whose cache SHA is meaningless inside this fixture. Tests about the running
    # session set it explicitly.
    monkeypatch.setattr(pl, "_running_shas", lambda: [])
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


def test_a_repo_commit_that_leaves_the_plugin_alone_is_NOT_stale(fake_repo, pl, monkeypatch, capsys):
    """`claude plugin update` stamps the record with REPO HEAD, not the last plugin commit.

    So after a sync, any commit that advances the repo without touching the plugin makes the two
    SHAs differ while the plugin is byte-identical. Keyed on SHA equality, status reports STALE
    forever and advises a sync that changes nothing — a detector that cries stale always.
    """
    # A sync happens HERE, at a commit that touches nothing under the plugin. `claude plugin update`
    # stamps the record with THIS sha — which is not the last plugin-touching commit, and that gap
    # is the whole defect. Binding to the last plugin commit instead would make both predicates
    # agree and prove nothing.
    (fake_repo / "unrelated.py").write_text("x = 99\n")
    _git(fake_repo, "add", "-A")
    _git(fake_repo, "commit", "-qm", "unrelated repo work")
    bound = pl._run(["git", "rev-parse", "HEAD"], fake_repo)[1]
    monkeypatch.setattr(pl, "_bound_shas", lambda: {"/p": bound[:12]})

    assert bound[:12] != pl._plugin_head()[:12], "fixture must seed the divergence it tests"
    assert pl._is_stale(bound[:12]) is False, (
        "no plugin file differs, so the bound cache is current — the SHAs differing is a fact "
        "about the repo, not about the plugin")
    assert pl.cmd_status(None) == 0
    assert "STALE" not in capsys.readouterr().out


def test_a_plugin_commit_IS_stale(fake_repo, pl):
    """Non-vacuity for the test above: the predicate must still fire when the plugin moves."""
    bound = pl._run(["git", "rev-parse", "HEAD"], fake_repo)[1]
    (fake_repo / ".claude/plugins/skeft-qa/agents/lean-worker.md").write_text("v2\n")
    _git(fake_repo, "add", "-A")
    _git(fake_repo, "commit", "-qm", "plugin work")

    assert pl._is_stale(bound[:12]) is True


def test_delta_clears_a_prior_document_when_no_plugin_file_differs(fake_repo, pl, monkeypatch):
    """The path the SHA-keyed version left uncovered: bound != HEAD, but nothing plugin differs.

    A brief cites this document by ABSOLUTE PATH, so a survivor from an earlier run is delivered to
    a subagent as current guidance. Clearing must happen on every no-delta path, not just one.
    """
    (fake_repo / "unrelated.py").write_text("x = 7\n")
    _git(fake_repo, "add", "-A")
    _git(fake_repo, "commit", "-qm", "unrelated")
    bound = pl._run(["git", "rev-parse", "HEAD"], fake_repo)[1]   # a non-plugin commit, as synced
    assert bound[:12] != pl._plugin_head()[:12], "fixture must seed the divergence it tests"
    monkeypatch.setattr(pl, "_running_shas", lambda: [bound[:12]])
    pl.DELTA_DOC.parent.mkdir(parents=True, exist_ok=True)
    pl.DELTA_DOC.write_text("# STALE DELTA FROM A PREVIOUS RUN — an agent will cite this\n")

    rc = pl.cmd_delta(None)

    assert rc == 0
    assert not pl.DELTA_DOC.exists(), (
        "a no-delta run must delete the document; leaving it makes a brief hand a subagent "
        "guidance that no longer reflects HEAD")


def test_delta_follows_the_running_session_not_the_refreshed_record(fake_repo, pl, monkeypatch,
                                                                    capsys):
    """The state after a sync: the record names HEAD, a live session still executes the old cache.

    This is the ordinary order of operations — commit, sync, and the session that authored the
    commit keeps running. Keyed on the install record, delta reports "no delta" and unlinks its
    own document at exactly the moment a dispatch brief needs to cite it.
    """
    bound = pl._plugin_head()
    (fake_repo / ".claude/plugins/skeft-qa/agents/lean-worker.md").write_text("v2 — the new rule\n")
    _git(fake_repo, "add", "-A")
    _git(fake_repo, "commit", "-qm", "plugin change")
    head = pl._plugin_head()
    monkeypatch.setattr(pl, "_bound_shas", lambda: {"/p": head[:12]})   # record: already synced
    monkeypatch.setattr(pl, "_running_shas", lambda: [bound[:12]])      # session: still on the old

    rc = pl.cmd_delta(None)

    assert rc == 1, "a session executing a stale cache is a delta, whatever the record says"
    assert "v2 — the new rule" in pl.DELTA_DOC.read_text()
    assert "No delta" not in capsys.readouterr().out


def test_delta_prefers_the_oldest_session_by_ancestry_not_by_hex_order(fake_repo, pl, monkeypatch):
    """Two live sessions, two caches. The delta must cover the one further behind.

    Ordering SHAs as strings is not an age ordering. The commit below is amended until the
    NEWER sha sorts first, so a lexicographic `sorted(...)[0]` deterministically picks the
    wrong one — otherwise this trap would spring only on the ~half of runs where the random
    hex happens to fall that way, and a flaky detector is not a detector.
    """
    older = pl._plugin_head()
    (fake_repo / ".claude/plugins/skeft-qa/agents/lean-worker.md").write_text("v2\n")
    _git(fake_repo, "add", "-A")
    _git(fake_repo, "commit", "-qm", "first change")
    for n in range(200):
        newer = pl._plugin_head()
        if newer[:12] < older[:12]:
            break
        _git(fake_repo, "commit", "--amend", "-qm", f"first change {n}")
    else:
        pytest.skip("could not seed a hex ordering that traps a lexicographic sort")

    skills = fake_repo / ".claude/plugins/skeft-qa/skills"
    skills.mkdir(parents=True, exist_ok=True)
    (skills / "paper.md").write_text("both sessions lack this\n")
    _git(fake_repo, "add", "-A")
    _git(fake_repo, "commit", "-qm", "second change")
    monkeypatch.setattr(pl, "_running_shas", lambda: [older[:12], newer[:12]])

    assert pl.cmd_delta(None) == 1
    body = pl.DELTA_DOC.read_text()
    assert "skills/paper.md" in body, "the change both sessions lack must always render"
    assert "agents/lean-worker.md" in body, (
        "the render must span back to the OLDEST live session; a string sort picks whichever "
        "hex sorts first and drops everything only the oldest session is missing"
    )


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
