"""Production-adapter mutations against disposable Git input repositories."""
import importlib.util
import json
from pathlib import Path
import subprocess

import pytest

SPEC = importlib.util.spec_from_file_location("codex_continuity", Path(__file__).resolve().parents[1] / "scripts/codex_continuity.py")
c = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(c)


def run(root, *args):
    return subprocess.run(["git", "-C", str(root), *args], check=True, capture_output=True).stdout


@pytest.fixture
def repo(tmp_path):
    root = tmp_path / "primary"
    root.mkdir()
    run(root, "init", "-q")
    run(root, "config", "user.name", "Fixture")
    run(root, "config", "user.email", "fixture@example.invalid")
    (root / ".gitignore").write_text(".local/\nLAB_NOTEBOOK_INDEX.md\n")
    for name in ("source.py", "ROADMAP.md", "AUTHORITY.md", "AGENTS.md", "CLAUDE.md"):
        (root / name).write_text("initial\n")
    run(root, "add", ".")
    run(root, "commit", "-qm", "fixture")
    (root / "LAB_NOTEBOOK_INDEX.md").write_text("settled decision\n")
    return root


def make(root, **overrides):
    repo = root
    values = dict(repo=repo, output=repo / ".local/assignment.json", task="proof-a", parent="program",
                  role="leaf", owner="worker", writer="lead", objective="inspect target",
                  reviewer="independent-review", evidence="report actual checks", roadmap=repo / "ROADMAP.md",
                  notebook=repo / "LAB_NOTEBOOK_INDEX.md", owned=["source.py"], authorities=[repo / "AUTHORITY.md"])
    values.update(overrides)
    c.make_packet(**values)
    return values["output"]


def test_fresh_and_read_only(repo):
    p = make(repo)
    before = {x: x.read_bytes() for x in repo.iterdir() if x.is_file()}
    assert c.check_packet(p)["fresh"]
    assert before == {x: x.read_bytes() for x in repo.iterdir() if x.is_file()}
    assert "no execution" in c.check_packet(p)["meaning"]


def test_same_porcelain_different_bytes(repo):
    source = repo / "source.py"
    source.write_text("dirty one\n")
    p = make(repo)
    before = run(repo, "status", "--porcelain")
    source.write_text("dirty two\n")
    assert run(repo, "status", "--porcelain") == before
    assert "source" in c.check_packet(p)["changed"]


@pytest.mark.parametrize("filename,label", [("ROADMAP.md", "roadmap"), ("AUTHORITY.md", "authority[2]"),
                                             ("LAB_NOTEBOOK_INDEX.md", "notebook")])
def test_referenced_input_changes(repo, filename, label):
    p = make(repo)
    (repo / filename).write_text("different\n")
    assert label in c.check_packet(p)["changed"]


def test_missing_notebook(repo):
    p = make(repo)
    (repo / "LAB_NOTEBOOK_INDEX.md").unlink()
    assert not c.check_packet(p)["fresh"]
    with pytest.raises(c.ContinuityError):
        make(repo, output=repo / ".local/new.json")


def test_commit_and_index_changes(repo):
    p = make(repo)
    (repo / "source.py").write_text("staged\n")
    run(repo, "add", "source.py")
    assert not c.check_packet(p)["fresh"]
    p2 = make(repo, output=repo / ".local/second.json")
    run(repo, "commit", "-qm", "changed")
    assert not c.check_packet(p2)["fresh"]


def test_untracked_contents_and_ignored_exclusion(repo):
    untracked = repo / "new.py"
    untracked.write_text("one\n")
    p = make(repo)
    (repo / ".local/cache").write_text("irrelevant\n")
    assert c.check_packet(p)["fresh"]
    untracked.write_text("two\n")
    assert not c.check_packet(p)["fresh"]


def test_worktree_primary_resolution(repo, tmp_path):
    wt = tmp_path / "worker"
    run(repo, "worktree", "add", "-qb", "worker", str(wt))
    p = make(repo, repo=wt)
    data = json.loads(p.read_text())
    assert data["primary"] == str(repo)
    assert data["checkout"] == str(wt)
    assert data["references"]["notebook"]["path"] == str(repo / "LAB_NOTEBOOK_INDEX.md")
    assert c.check_packet(p)["fresh"]
    (wt / "source.py").write_text("worker edit\n")
    assert not c.check_packet(p)["fresh"]


@pytest.mark.parametrize("output", ["tracked.json", "ROADMAP.md", "LAB_NOTEBOOK_INDEX.md", ".git/packet.json"])
def test_output_safety(repo, output):
    before = (repo / "ROADMAP.md").read_bytes()
    with pytest.raises(c.ContinuityError):
        make(repo, output=repo / output)
    assert (repo / "ROADMAP.md").read_bytes() == before


def test_no_overwrite(repo):
    p = make(repo)
    original = p.read_bytes()
    with pytest.raises(c.ContinuityError):
        make(repo)
    assert p.read_bytes() == original


def test_scope_and_symlink_escape(repo, tmp_path):
    foreign = tmp_path / "outside"
    foreign.write_text("not owned")
    (repo / "escape").symlink_to(foreign)
    for owned in (["../outside"], [str(foreign)], ["escape"], [".git/config"]):
        with pytest.raises(c.ContinuityError):
            make(repo, owned=owned)


def test_invalid_packet_and_role(repo):
    p = make(repo)
    packet = json.loads(p.read_text())
    packet["role"] = "unrestricted"
    p.write_text(json.dumps(packet))
    assert not c.check_packet(p)["fresh"]
    p.write_text("{")
    assert not c.check_packet(p)["fresh"]
    assert not c.check_packet(repo / ".local/missing")["fresh"]


def test_leaf_notebook_writer_rejected(repo):
    with pytest.raises(c.ContinuityError):
        make(repo, writer="worker")


def test_cli_failure_exit(repo):
    p = make(repo)
    result = subprocess.run(["python3", c.__file__, "check", str(p)], capture_output=True)
    assert result.returncode == 0
    (repo / "source.py").write_text("changed")
    result = subprocess.run(["python3", c.__file__, "check", str(p)], capture_output=True)
    assert result.returncode == 1
    assert not json.loads(result.stdout)["fresh"]


def test_ignored_owned_file_is_fingerprinted(repo):
    target = repo / ".local/owned.py"
    target.parent.mkdir()
    target.write_text("one")
    p = make(repo, owned=[".local/owned.py"])
    assert c.check_packet(p)["fresh"]
    target.write_text("two")
    assert "owned-files" in c.check_packet(p)["changed"]


def test_owned_notebook_rejected(repo):
    with pytest.raises(c.ContinuityError):
        make(repo, owned=["LAB_NOTEBOOK_INDEX.md"])


def test_reference_symlink_retarget_detected(repo):
    alternate = repo / ".local/alternate.md"
    alternate.parent.mkdir()
    alternate.write_text("initial\n")
    link = repo / ".local/authority-link"
    link.symlink_to(repo / "AUTHORITY.md")
    p = make(repo, authorities=[link])
    assert c.check_packet(p)["fresh"]
    link.unlink()
    link.symlink_to(alternate)
    assert "authority[2]" in c.check_packet(p)["changed"]


def test_packet_cannot_be_own_output(repo):
    with pytest.raises(c.ContinuityError):
        make(repo, owned=[".local/assignment.json"])


def test_external_authority_additive_and_required_bootstrap(repo, tmp_path):
    external = tmp_path / "external-governance.md"
    external.write_text("rule one")
    p = make(repo, authorities=[external])
    data = json.loads(p.read_text())
    paths = {r["path"] for r in data["references"]["authorities"]}
    assert str(repo / "AGENTS.md") in paths
    assert str(repo / "CLAUDE.md") in paths
    assert str(external) in paths
    assert c.check_packet(p)["fresh"]
    external.write_text("rule two")
    assert not c.check_packet(p)["fresh"]
    (repo / "AGENTS.md").unlink()
    with pytest.raises(c.ContinuityError):
        make(repo, output=repo / ".local/new.json", authorities=[external])
